#![doc = include_str!("../README.md")]
//!
//!
//! If you to change the alignment requirements of your DST (for example, your type may need to be
//! aligned to a 32-byte boundary), see [`DstBase`], which is also where most of the documentation
//! lives.

#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![feature(ptr_metadata, unsize, pin_deref_mut)]
#![warn(missing_docs)]

mod assert;
mod trait_impls;

use core::{
    any::Any,
    marker::{PhantomData, Unsize},
    mem::{size_of, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::{copy_nonoverlapping, drop_in_place, from_raw_parts, from_raw_parts_mut, Pointee},
};

use aligned::Aligned;

pub use aligned::{Alignment, A1, A16, A2, A32, A4, A64, A8};

/// Given multiple type names, return the size of the biggest type.
///
/// This can be used in const context. It is intended for computing the required size for [`Dst`].
///
/// ```
/// # use core::fmt::Display;
/// # use core::mem::{size_of, size_of_val};
/// # use sized_dst::{max_size, Dst};
/// // Dst data will be the size of f64
/// let dst = Dst::<dyn Display, { max_size!(u32, f64, bool) }>::new(12.0);
/// assert!(size_of_val(&dst) > size_of::<f64>());
/// ```
#[macro_export]
macro_rules! max_size {
    ($first:ty $(, $other:ty)* $(,)?) => {{
        #[allow(unused_mut)]
        let mut max = core::mem::size_of::<$first>();
        $(
            let next = core::mem::size_of::<$other>();
            if next > max {
                max = next;
            }
        )*
        max
    }};
}

/// Sized object that stores a DST object, such as a trait object, on the stack.
///
/// The layout of `DstBase` consists of the DST metadata (for trait objects, this is the vtable
/// pointer) and a fixed block of memory storing the actual object.
///
/// `DstBase` implements `Deref` and `DerefMut` for the DST, so it can be used in place of the DST
/// in most use-cases.
///
/// ```
/// # use sized_dst::Dst;
/// let dst = Dst::<dyn ToString, 8>::new(12u32);
/// assert_eq!(dst.to_string(), "12");
/// ```
///
/// Rather than using `DstBase` directly, use [`Dst`], which is aligned to the target word boundary.
/// This is almost always what you want.
///
/// # Alignment and Capacity
///
/// The alignment and capacity of the backing storage are specified via the generic parameters `A`
/// and `N` respectively. Since DST objects can have any size and alignment, the object being
/// stored must fit and be well-aligned within the backing storage. These checks are done at
/// **compile-time**, resulting in a compile-time error if the size or alignment requirements are
/// not met.
///
/// For example, the following will work:
/// ```
/// # use sized_dst::{DstBase, A4};
/// // u32 fits within 8 bytes and an alignment of 4
/// let dst = DstBase::<dyn std::fmt::Debug, A4, 8>::new(12u32);
/// ```
/// however, this will fail to compile due to insufficient capacity:
/// ```compile_fail
/// # use sized_dst::{DstBase, A4};
/// // [u32; 3] does not fit within 8 bytes
/// let dst = DstBase::<dyn std::fmt::Debug, A4, 8>::new([1u32, 23u32, 0u32]);
/// ```
/// and this will also fail to compile due to insufficient alignment:
/// ```compile_fail
/// # use sized_dst::{DstBase, A4};
/// // f64 does not fit the alignment requirement of 4 bytes
/// let dst = DstBase::<dyn std::fmt::Debug, A4, 8>::new(12.0f64);
/// ```
pub struct DstBase<D: ?Sized + Pointee, A: Alignment, const N: usize> {
    metadata: <D as Pointee>::Metadata,
    obj_bytes: Aligned<A, [MaybeUninit<u8>; N]>,
    // Technically we own an instance of D, so we need this for autotraits to be propagated
    // correctly
    _phantom: PhantomData<D>,
}

impl<D: ?Sized, A: Alignment, const N: usize> DstBase<D, A, N> {
    /// Create a new `DstBase` from a sized `value`.
    ///
    /// `value` is coerced from its original type into the type D and stored into the `DstBase`.
    /// The size and alignment of `value` are checked against the `DstBase` parameters at
    /// **compile-time**, resulting in a compile error if `value` doesn't fit.
    pub fn new<T: Unsize<D>>(value: T) -> Self {
        assert::const_assert::<T, A, N>();

        // SAFETY:
        // - `val_size` is the size of `value`, as expected by the function.
        // - Our assertions made sure that `value` fits in `self.obj_bytes`, and its alignment
        //   requirement does not extracted that of `self.obj_bytes`.
        // - We call `mem::forget` immediately after to prevent double-free.
        let out = unsafe { Self::from_dyn(&value, size_of::<T>()) };
        core::mem::forget(value);
        out
    }

    /// SAFETY:
    /// - `val_size` must be the size of the object `value` points to.
    /// - `self.obj_bytes` must be at least `val_size` bytes long.
    /// - `value`'s alignment requirements must not be more strict than `self.obj_bytes`.
    /// - `mem::forget` must be called on the `value` object after this call.
    unsafe fn from_dyn(value: &D, val_size: usize) -> Self {
        // The metadata comes from a fat D pointer pointing to `value`. We can use the metadata
        // to reconstruct the fat D pointer in the future.
        let metadata = core::ptr::metadata(value as *const D);

        let mut obj_bytes = Aligned([MaybeUninit::uninit(); N]);
        // Move `value` into `obj_bytes`
        //
        // SAFETY:
        // - `value` and `self.obj_bytes` are at least `val_size` bytes, so the copy is valid.
        // - `value`'s alignment is not more strict than `self.obj_bytes`, so the copied `value`
        //   will always be well-aligned.
        // - `value` and `obj_bytes` are separate variables, so they can't overlap.
        unsafe {
            copy_nonoverlapping(
                value as *const D as *const MaybeUninit<u8>,
                obj_bytes.as_mut_ptr(),
                val_size,
            )
        };

        DstBase {
            metadata,
            obj_bytes,
            _phantom: PhantomData,
        }
    }

    /// Get a dereferenceable, well-aligned pointer to the stored DST object
    fn as_ptr(&self) -> *const D {
        // A value that coerces into `D` was written into `obj_bytes` in the constructor, so the
        // pointer to `obj_bytes` always points to a valid, well-aligned instance of `D`.
        // Additionally, `metadata` was extracted from a fat D pointer in the constructor . As a
        // result, the reconstructed D pointer is guaranteed to be dereferenceable.
        from_raw_parts(self.obj_bytes.as_ptr(), self.metadata)
    }

    /// Get a dereferenceable, well-aligned mutable pointer to the stored DST object
    fn as_mut_ptr(&mut self) -> *mut D {
        // See `as_ptr` for how the API guarantees are upholded
        from_raw_parts_mut(self.obj_bytes.as_mut_ptr(), self.metadata)
    }
}

macro_rules! downcast_impl {
    ($dst:ty) => {
        impl<A: Alignment, const N: usize> DstBase<$dst, A, N> {
            /// Attempt to downcast to a concrete type
            pub fn downcast<T: Any>(self) -> Option<T> {
                if let Some(val_ref) = self.deref().downcast_ref() {
                    // SAFETY:
                    // - val_ref is a valid reference to T, so we're reading a valid value of T for sure.
                    // - Call mem::forget on self so we don't drop T twice.
                    let val = unsafe { core::ptr::read(val_ref as *const T) };
                    core::mem::forget(self);
                    Some(val)
                } else {
                    None
                }
            }
        }
    };
}
downcast_impl!(dyn Any);
downcast_impl!(dyn Any + Send);
downcast_impl!(dyn Any + Send + Sync);

impl<D: ?Sized, A: Alignment, const N: usize> Drop for DstBase<D, A, N> {
    fn drop(&mut self) {
        // SAFETY:
        // - `as_mut_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - The stored value has not been dropped previously, since `forget` was called in the
        //   constructor.
        unsafe { drop_in_place(self.as_mut_ptr()) }
    }
}

impl<D: ?Sized, A: Alignment, const N: usize> Deref for DstBase<D, A, N> {
    type Target = D;

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // - `as_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - Lifetime of the return reference is constrained by the lifetime of `self`, so the
        //   reference will never dangle.
        unsafe { &*self.as_ptr() }
    }
}

impl<D: ?Sized, A: Alignment, const N: usize> DerefMut for DstBase<D, A, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // - `as_mut_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - Lifetime of the return reference is constrained by the lifetime of `self`, so the
        //   reference will never dangle.
        unsafe { &mut *self.as_mut_ptr() }
    }
}

/// [`DstBase`] storing an object with alignment of 1 byte
pub type DstA1<D, const N: usize> = DstBase<D, A1, N>;
/// [`DstBase`] storing an object with alignment of 2 bytes
pub type DstA2<D, const N: usize> = DstBase<D, A2, N>;
/// [`DstBase`] storing an object with alignment of 4 bytes
pub type DstA4<D, const N: usize> = DstBase<D, A4, N>;
/// [`DstBase`] storing an object with alignment of 8 bytes
pub type DstA8<D, const N: usize> = DstBase<D, A8, N>;
/// [`DstBase`] storing an object with alignment of 16 bytes
pub type DstA16<D, const N: usize> = DstBase<D, A16, N>;
/// [`DstBase`] storing an object with alignment of 32 bytes
pub type DstA32<D, const N: usize> = DstBase<D, A32, N>;
/// [`DstBase`] storing an object with alignment of 64 bytes
pub type DstA64<D, const N: usize> = DstBase<D, A64, N>;

#[cfg(target_pointer_width = "16")]
/// [`DstBase`] aligned to the target word boundary. This is almost always what you want to use.
pub type Dst<D, const N: usize> = DstA2<D, N>;
#[cfg(target_pointer_width = "32")]
/// [`DstBase`] aligned to the target word boundary. This is almost always what you want to use.
pub type Dst<D, const N: usize> = DstA4<D, N>;
#[cfg(target_pointer_width = "64")]
/// [`DstBase`] aligned to the target word boundary. This is almost always what you want to use.
pub type Dst<D, const N: usize> = DstA8<D, N>;

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(clippy::needless_borrows_for_generic_args)]
    #[test]
    fn to_string() {
        let n = 123;
        let mut obj = DstA8::<dyn std::fmt::Display, 8>::new(4);
        assert_eq!(obj.to_string(), "4");

        obj = DstA8::new('a');
        assert_eq!(obj.to_string(), "a");

        obj = DstA8::new(123u64);
        assert_eq!(obj.to_string(), "123");

        // This is safe, because n outlives obj
        obj = DstA8::new(&n);
        assert_eq!(obj.to_string(), "123");

        assert_eq!(align_of_val(&obj.obj_bytes), 8);
        assert!(size_of_val(&obj.obj_bytes) >= 8);
    }

    #[test]
    fn small() {
        let mut obj = DstA1::<dyn std::fmt::Debug, 2>::new(3u8);
        assert_eq!(align_of_val(&obj.obj_bytes), 1);
        assert!(size_of_val(&obj.obj_bytes) >= 2);

        obj = DstA1::new([1u8, 2u8]);
        assert_eq!(align_of_val(&obj.obj_bytes), 1);
        assert!(size_of_val(&obj.obj_bytes) >= 2);
    }

    #[allow(clippy::needless_borrows_for_generic_args)]
    #[test]
    fn native() {
        let mut obj = Dst::<dyn std::fmt::Debug, 16>::new(0usize);
        assert_eq!(align_of_val(&obj.obj_bytes), size_of::<usize>());
        assert!(size_of_val(&obj.obj_bytes) >= 16);

        obj = Dst::new(std::ptr::null::<*const String>());
        assert_eq!(align_of_val(&obj.obj_bytes), size_of::<usize>());
        assert!(size_of_val(&obj.obj_bytes) >= 16);

        obj = Dst::new(Box::new(32));
        assert_eq!(align_of_val(&obj.obj_bytes), size_of::<usize>());
        assert!(size_of_val(&obj.obj_bytes) >= 16);

        obj = Dst::new(&0);
        assert_eq!(align_of_val(&obj.obj_bytes), size_of::<usize>());
        assert!(size_of_val(&obj.obj_bytes) >= 16);
    }

    #[test]
    fn custom_trait_obj() {
        struct Test<'a> {
            bop_count: &'a mut u32,
            drop_count: &'a mut u32,
        }
        trait Bop {
            fn bop(&mut self);
        }
        impl<'a> Bop for Test<'a> {
            fn bop(&mut self) {
                *self.bop_count += 1;
            }
        }
        impl<'a> Drop for Test<'a> {
            fn drop(&mut self) {
                *self.drop_count += 1;
            }
        }

        let mut bop_count = 0;
        let mut drop_count = 0;
        let test = Test {
            bop_count: &mut bop_count,
            drop_count: &mut drop_count,
        };
        let mut obj = Dst::<dyn Bop, 20>::new(test);
        obj.bop();
        obj.bop();
        drop(obj);

        // We bopped twice
        assert_eq!(bop_count, 2);
        // Should have only dropped once
        assert_eq!(drop_count, 1);
    }

    #[test]
    fn slice() {
        let mut obj = DstA1::<[u8], 4>::new([b'a', b'b']);
        assert_eq!(obj.deref(), b"ab");

        obj = DstA1::<[u8], 4>::new([b'a', b'b', b'c', b'd']);
        assert_eq!(obj.deref(), b"abcd");

        obj = DstA1::<[u8], 4>::new([]);
        assert_eq!(obj.deref(), b"");
    }

    #[test]
    fn align32() {
        let obj = DstA32::<dyn std::fmt::Debug, 32>::new(aligned::Aligned::<A32, _>(0));
        assert_eq!(align_of_val(&obj.obj_bytes), 32);
    }

    #[test]
    fn any_replace() {
        let mut obj = Dst::<dyn Any, 32>::new(String::from("xyz"));
        let ref_mut = obj.downcast_mut::<String>().unwrap();
        assert_eq!(ref_mut, "xyz");

        // Use a downcasted reference to replace the inner object without changing the metadata.
        // The metadata should still be valid because the concrete type of the replacement object
        // is the exact same as the original object, so future from_raw_parts calls are still sound.
        *ref_mut = String::from("abc");
        assert_eq!(obj.downcast_ref::<String>().unwrap(), "abc");
    }

    #[test]
    fn downcast() {
        let obj = Dst::<dyn Any, 32>::new(Box::new(2u32));
        let val: Box<u32> = obj.downcast::<Box<u32>>().unwrap();
        assert_eq!(*val, 2);

        let obj = Dst::<dyn Any, 32>::new(Box::new(2u32));
        assert!(obj.downcast::<String>().is_none());
    }

    #[test]
    fn max_size() {
        assert_eq!(size_of::<[u8; max_size!(String)]>(), size_of::<String>());
        assert_eq!(size_of::<[u8; max_size!(u8, u32, u64)]>(), size_of::<u64>());
    }
}

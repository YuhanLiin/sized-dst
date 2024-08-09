//! Placeholder

#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![feature(ptr_metadata, unsize, pin_deref_mut)]
#![warn(missing_docs)]

mod trait_impls;

use core::{
    any::Any,
    marker::{PhantomData, Unsize},
    mem::{size_of, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::{copy_nonoverlapping, drop_in_place, from_raw_parts, from_raw_parts_mut, Pointee},
};

use aligned::{Aligned, Alignment};

pub use aligned::{A1, A16, A2, A32, A4, A64, A8};

/// Sized object that stores a DST object, such as a trait object, on the stack.
///
/// The layout of `SizedDst` consists of the DST metadata (in the case of trait objects, this is
/// the vtable pointer)  followed a fixed block of memory for storing the actual object.
///
/// `SizeDst` implements `Deref` and `DerefMut` for the DST, so it can be used in place of the DST
/// in most use-cases.
///
/// ```
/// # use sized_dst::SizedDstNative;
/// let dst = SizedDstNative::<dyn ToString, 8>::new(12u32);
/// assert_eq!(dst.to_string(), "12");
/// ```
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
/// # use sized_dst::{SizedDst, A4};
/// // u32 fits within 8 bytes and an alignment of 4
/// let dst = SizedDst::<dyn std::fmt::Debug, A4, 8>::new(12u32);
/// ```
/// however, this will fail to compile due to insufficient capacity:
/// ```compile_fail
/// # use sized_dst::{SizedDst, A4};
/// // [u32; 3] does not fit within 8 bytes
/// let dst = SizedDst::<dyn std::fmt::Debug, A4, 8>::new([1u32, 23u32, 0u32]);
/// ```
/// and this will also fail to compile due to insufficient alignment:
/// ```compile_fail
/// # use sized_dst::{SizedDst, A4};
/// // f64 does not fit the alignment requirement of 4 bytes
/// let dst = SizedDst::<dyn std::fmt::Debug, A4, 8>::new(12.0f64);
/// ```
///
/// For a `SizedDst` that's aligned to the target word boundary, see [`SizedDstNative`]. This will
/// almost always be what you want.
#[repr(C)]
pub struct SizedDst<DST: ?Sized + Pointee, A: Alignment, const N: usize> {
    metadata: <DST as Pointee>::Metadata,
    obj_bytes: Aligned<A, [MaybeUninit<u8>; N]>,
    // Technically we own an instance of DST, so we need this for autotraits to be propagated
    // correctly
    _phantom: PhantomData<DST>,
}

impl<DST: ?Sized, A: Alignment, const N: usize> SizedDst<DST, A, N> {
    /// Create a new `SizedDst` from a sized `value`.
    ///
    /// `value` is coerced from its original type into the DST and stored into the `SizedDst`.
    /// The size and alignment of `value` are checked against the `SizedDst` parameters at
    /// **compile-time**, resulting in a compile error if `value` doesn't fit.
    pub fn new<T: Unsize<DST>>(value: T) -> Self {
        const {
            assert!(
                size_of::<T>() <= N,
                "Value must fit within the stack object"
            );
        }
        const {
            assert!(
                align_of::<T>() <= align_of::<A>(),
                "Value alignment requirements must not exceed that of the stack object"
            );
        }

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
    unsafe fn from_dyn(value: &DST, val_size: usize) -> Self {
        // The metadata comes from a fat DST pointer pointing to `value`. We can use the metadata
        // to reconstruct the fat DST pointer in the future.
        let metadata = core::ptr::metadata(value as *const DST);

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
                value as *const DST as *const MaybeUninit<u8>,
                obj_bytes.as_mut_ptr(),
                val_size,
            )
        };

        SizedDst {
            metadata,
            obj_bytes,
            _phantom: PhantomData,
        }
    }

    /// Get a dereferenceable, well-aligned pointer to the stored DST object
    fn as_ptr(&self) -> *const DST {
        // A value that coerces into `DST` was written into `obj_bytes` in the constructor, so the
        // pointer to `obj_bytes` always points to a valid, well-aligned instance of `DST`.
        // Additionally, `metadata` was extracted from a fat DST pointer in the constructor . As a
        // result, the reconstructed DST pointer is guaranteed to be dereferenceable.
        from_raw_parts(self.obj_bytes.as_ptr(), self.metadata)
    }

    /// Get a dereferenceable, well-aligned mutable pointer to the stored DST object
    fn as_mut_ptr(&mut self) -> *mut DST {
        // See `as_ptr` for how the API guarantees are upholded
        from_raw_parts_mut(self.obj_bytes.as_mut_ptr(), self.metadata)
    }
}

impl<A: Alignment, const N: usize> SizedDst<dyn Any, A, N> {
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

impl<DST: ?Sized, A: Alignment, const N: usize> Drop for SizedDst<DST, A, N> {
    fn drop(&mut self) {
        // SAFETY:
        // - `as_mut_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - The stored value has not been dropped previously, since `forget` was called in the
        //   constructor.
        unsafe { drop_in_place(self.as_mut_ptr()) }
    }
}

impl<DST: ?Sized, A: Alignment, const N: usize> Deref for SizedDst<DST, A, N> {
    type Target = DST;

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // - `as_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - Lifetime of the return reference is constrained by the lifetime of `self`, so the
        //   reference will never dangle.
        unsafe { &*self.as_ptr() }
    }
}

impl<DST: ?Sized, A: Alignment, const N: usize> DerefMut for SizedDst<DST, A, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // - `as_mut_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - Lifetime of the return reference is constrained by the lifetime of `self`, so the
        //   reference will never dangle.
        unsafe { &mut *self.as_mut_ptr() }
    }
}

/// [`SizedDst`] storing an object with alignment of 1 byte
pub type SizedDstA1<DST, const N: usize> = SizedDst<DST, A1, N>;
/// [`SizedDst`] storing an object with alignment of 2 bytes
pub type SizedDstA2<DST, const N: usize> = SizedDst<DST, A2, N>;
/// [`SizedDst`] storing an object with alignment of 4 bytes
pub type SizedDstA4<DST, const N: usize> = SizedDst<DST, A4, N>;
/// [`SizedDst`] storing an object with alignment of 8 bytes
pub type SizedDstA8<DST, const N: usize> = SizedDst<DST, A8, N>;
/// [`SizedDst`] storing an object with alignment of 16 bytes
pub type SizedDstA16<DST, const N: usize> = SizedDst<DST, A16, N>;
/// [`SizedDst`] storing an object with alignment of 32 bytes
pub type SizedDstA32<DST, const N: usize> = SizedDst<DST, A32, N>;
/// [`SizedDst`] storing an object with alignment of 64 bytes
pub type SizedDstA64<DST, const N: usize> = SizedDst<DST, A64, N>;

#[cfg(target_pointer_width = "16")]
/// [`SizedDst`] aligned to the target word boundary. This is almost always the alignment that you
/// want to use
pub type SizedDstNative<DST, const N: usize> = SizedDstA2<DST, N>;
#[cfg(target_pointer_width = "32")]
/// [`SizedDst`] aligned to the target word boundary. This is almost always the alignment that you
/// want to use
pub type SizedDstNative<DST, const N: usize> = SizedDstA4<DST, N>;
#[cfg(target_pointer_width = "64")]
/// [`SizedDst`] aligned to the target word boundary. This is almost always the alignment that you
/// want to use
pub type SizedDstNative<DST, const N: usize> = SizedDstA8<DST, N>;

#[cfg(test)]
mod tests {
    use static_assertions::{assert_impl_all, assert_not_impl_any};

    use super::*;

    assert_not_impl_any!(SizedDstA8::<dyn ToString, 8>: Send, Sync);

    assert_impl_all!(SizedDstA8::<dyn ToString + Send, 8>: Send);
    assert_not_impl_any!(SizedDstA8::<dyn ToString + Send, 8>: Sync);

    assert_impl_all!(SizedDstA8::<dyn ToString + Send + Sync, 8>: Send, Sync);

    #[allow(clippy::needless_borrows_for_generic_args)]
    #[test]
    fn to_string() {
        let n = 123;
        let mut obj = SizedDstA8::<dyn ToString, 8>::new(4);
        assert_eq!(obj.to_string(), "4");

        obj = SizedDstA8::new('a');
        assert_eq!(obj.to_string(), "a");

        obj = SizedDstA8::new(123u64);
        assert_eq!(obj.to_string(), "123");

        // This is safe, because n outlives obj
        obj = SizedDstA8::new(&n);
        assert_eq!(obj.to_string(), "123");

        assert_eq!(align_of_val(&obj.obj_bytes), 8);
        assert!(size_of_val(&obj.obj_bytes) >= 8);
    }

    #[test]
    fn small() {
        let mut obj = SizedDstA1::<dyn std::fmt::Debug, 2>::new(3u8);
        assert_eq!(align_of_val(&obj.obj_bytes), 1);
        assert!(size_of_val(&obj.obj_bytes) >= 2);

        obj = SizedDstA1::new([1u8, 2u8]);
        assert_eq!(align_of_val(&obj.obj_bytes), 1);
        assert!(size_of_val(&obj.obj_bytes) >= 2);
    }

    #[allow(clippy::needless_borrows_for_generic_args)]
    #[test]
    fn native() {
        let mut obj = SizedDstNative::<dyn std::fmt::Debug, 16>::new(0usize);
        assert_eq!(align_of_val(&obj.obj_bytes), size_of::<usize>());
        assert!(size_of_val(&obj.obj_bytes) >= 16);

        obj = SizedDstNative::new(std::ptr::null::<*const String>());
        assert_eq!(align_of_val(&obj.obj_bytes), size_of::<usize>());
        assert!(size_of_val(&obj.obj_bytes) >= 16);

        obj = SizedDstNative::new(Box::new(32));
        assert_eq!(align_of_val(&obj.obj_bytes), size_of::<usize>());
        assert!(size_of_val(&obj.obj_bytes) >= 16);

        obj = SizedDstNative::new(&0);
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
        let mut obj = SizedDstNative::<dyn Bop, 20>::new(test);
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
        let mut obj = SizedDstA1::<[u8], 4>::new([b'a', b'b']);
        assert_eq!(obj.deref(), b"ab");

        obj = SizedDstA1::<[u8], 4>::new([b'a', b'b', b'c', b'd']);
        assert_eq!(obj.deref(), b"abcd");

        obj = SizedDstA1::<[u8], 4>::new([]);
        assert_eq!(obj.deref(), b"");
    }

    #[test]
    fn align32() {
        let obj = SizedDstA32::<dyn std::fmt::Debug, 32>::new(aligned::Aligned::<A32, _>(0));
        assert_eq!(align_of_val(&obj.obj_bytes), 32);
    }

    #[test]
    fn any_replace() {
        let mut obj = SizedDstNative::<dyn Any, 32>::new(String::from("xyz"));
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
        let obj = SizedDstNative::<dyn Any, 32>::new(Box::new(2u32));
        let val: Box<u32> = obj.downcast::<Box<u32>>().unwrap();
        assert_eq!(*val, 2);

        let obj = SizedDstNative::<dyn Any, 32>::new(Box::new(2u32));
        assert!(obj.downcast::<String>().is_none());
    }
}

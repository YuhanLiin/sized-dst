#![cfg_attr(not(test), no_std)]
#![feature(ptr_metadata, unsize)]

use core::{
    marker::PhantomData,
    marker::Unsize,
    mem::{size_of, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::{copy_nonoverlapping, drop_in_place, from_raw_parts, from_raw_parts_mut, Pointee},
};

use aligned::{Aligned, Alignment};

#[repr(C)]
struct StackObjectAlign<Dyn: ?Sized + Pointee, A: Alignment, const N: usize> {
    metadata: <Dyn as Pointee>::Metadata,
    obj_bytes: Aligned<A, [MaybeUninit<u8>; N]>,
    // Technically we own an instance of Dyn, so we need this for `Send` and `Sync` to be
    // propagated correctly
    _phantom: PhantomData<Dyn>,
}

impl<Dyn: ?Sized, A: Alignment, const N: usize> StackObjectAlign<Dyn, A, N> {
    pub fn new<T: Unsize<Dyn>>(value: T) -> Self {
        const {
            assert!(
                size_of::<T>() <= N,
                "Value must fit within the stack object"
            );
            assert!(
                align_of::<T>() <= align_of::<A>(),
                "Value alignment requirements must not exceed that of the stack object"
            );
        }

        // The metadata comes from a fat Dyn pointer pointing to `value`. We can use the metadata
        // to reconstruct the fat Dyn pointer in the future.
        let metadata = core::ptr::metadata(&value as &Dyn as *const Dyn);

        let mut obj_bytes = Aligned([MaybeUninit::uninit(); N]);
        // Move `value` into `obj_bytes`
        //
        // SAFETY:
        // - `value` is of type T, so it must be valid for reads of size_of::<T>.
        // - We asserted that `obj_bytes` is at least size_of::<T> bytes, and since its type is
        //   MaybeUninit<u8>, any bit pattern is valid.
        // - We asserted that the alignment of `obj_bytes` is at least as strict as the alignment
        //   of T, so the newly written instance of T must be properly aligned.
        // - `value` and `obj_bytes` are separate variables, so they can't overlap.
        unsafe {
            copy_nonoverlapping(
                &value as *const T as *const MaybeUninit<u8>,
                obj_bytes.as_mut_ptr(),
                size_of::<T>(),
            )
        };
        // The value is now owned by the object, so we shouldn't drop it
        core::mem::forget(value);

        StackObjectAlign {
            metadata,
            obj_bytes,
            _phantom: PhantomData,
        }
    }

    /// Get a dereferenceable, well-aligned pointer to the stored DST object
    fn as_ptr(&self) -> *const Dyn {
        // A value that coerces into `Dyn` was written into `obj_bytes` in the constructor, so the
        // pointer to `obj_bytes` always points to a valid, well-aligned instance of `Dyn`.
        // Additionally, `metadata` was extracted from a fat Dyn pointer in the constructor . As a
        // result, the reconstructed Dyn pointer is guaranteed to be dereferenceable.
        from_raw_parts(self.obj_bytes.as_ptr(), self.metadata)
    }

    /// Get a dereferenceable, well-aligned mutable pointer to the stored DST object
    fn as_mut_ptr(&mut self) -> *mut Dyn {
        // See `as_ptr` for how the API guarantees are upholded
        from_raw_parts_mut(self.obj_bytes.as_mut_ptr(), self.metadata)
    }
}

impl<Dyn: ?Sized, A: Alignment, const N: usize> Drop for StackObjectAlign<Dyn, A, N> {
    fn drop(&mut self) {
        // SAFETY:
        // - `as_mut_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - The stored value has not been dropped previously, since `forget` was called in the
        //   constructor.
        unsafe { drop_in_place(self.as_mut_ptr()) }
    }
}

impl<Dyn: ?Sized, A: Alignment, const N: usize> Deref for StackObjectAlign<Dyn, A, N> {
    type Target = Dyn;

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // - `as_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - Lifetime of the return reference is constrained by the lifetime of `self`, so the
        //   reference will never dangle.
        unsafe { &*self.as_ptr() }
    }
}

impl<Dyn: ?Sized, A: Alignment, const N: usize> DerefMut for StackObjectAlign<Dyn, A, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // - `as_mut_ptr` is guaranteed to return a dereferenceable, well-aligned pointer.
        // - Lifetime of the return reference is constrained by the lifetime of `self`, so the
        //   reference will never dangle.
        unsafe { &mut *self.as_mut_ptr() }
    }
}

pub type StackObjectA1<Dyn, const N: usize> = StackObjectAlign<Dyn, aligned::A1, N>;
pub type StackObjectA2<Dyn, const N: usize> = StackObjectAlign<Dyn, aligned::A2, N>;
pub type StackObjectA4<Dyn, const N: usize> = StackObjectAlign<Dyn, aligned::A4, N>;
pub type StackObjectA8<Dyn, const N: usize> = StackObjectAlign<Dyn, aligned::A8, N>;

#[cfg(test)]
mod tests {
    use std::any::Any;

    use static_assertions::{assert_impl_all, assert_not_impl_any};

    use super::*;

    assert_not_impl_any!(StackObjectA8::<dyn ToString, 8>: Send, Sync);

    assert_impl_all!(StackObjectA8::<dyn ToString + Send, 8>: Send);
    assert_not_impl_any!(StackObjectA8::<dyn ToString + Send, 8>: Sync);

    assert_impl_all!(StackObjectA8::<dyn ToString + Send + Sync, 8>: Send, Sync);

    #[allow(clippy::needless_borrows_for_generic_args)]
    #[test]
    fn to_string() {
        let n = 123;
        let mut obj = StackObjectA8::<dyn ToString, 8>::new(4);
        assert_eq!(obj.to_string(), "4");

        obj = StackObjectA8::new('a');
        assert_eq!(obj.to_string(), "a");

        obj = StackObjectA8::new(123u64);
        assert_eq!(obj.to_string(), "123");

        // This is safe, because n outlives obj
        obj = StackObjectA8::new(&n);
        assert_eq!(obj.to_string(), "123");

        assert_eq!(align_of_val(&obj.obj_bytes), 8);
        assert!(size_of_val(&obj.obj_bytes) >= 8);
    }

    #[test]
    fn small() {
        let mut obj = StackObjectA1::<dyn std::fmt::Debug, 2>::new(3u8);
        assert_eq!(align_of_val(&obj.obj_bytes), 1);
        assert!(size_of_val(&obj.obj_bytes) >= 2);

        obj = StackObjectA1::new([1u8, 2u8]);
        assert_eq!(align_of_val(&obj.obj_bytes), 1);
        assert!(size_of_val(&obj.obj_bytes) >= 2);
    }

    #[derive(Default)]
    struct Test {
        bop_count: u32,
        drop_count: u32,
    }

    trait Bop: Any {
        fn bop(&mut self);
        fn as_any(&self) -> &dyn Any;
    }

    impl Bop for Test {
        fn bop(&mut self) {
            self.bop_count += 1;
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    impl Drop for Test {
        fn drop(&mut self) {
            self.drop_count += 1;
        }
    }

    #[test]
    fn custom_trait_obj() {
        let test = Test::default();
        let mut obj = StackObjectA4::<dyn Bop, 10>::new(test);
        obj.bop();
        obj.bop();

        let test_ref = obj.as_any().downcast_ref::<Test>().unwrap();
        // We bopped twice
        assert_eq!(test_ref.bop_count, 2);
        // Since the object is still live, we should not have called `drop` at all
        assert_eq!(test_ref.drop_count, 0);
    }
}

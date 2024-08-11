// Put const asserts into separate file so that line numbers in error messages are consistent.
// Otherwise trybuild tests will fail every time lib.rs is changed.
pub(crate) const fn const_assert<T, A, const N: usize>() {
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
}

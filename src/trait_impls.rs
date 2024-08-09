use core::{
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    fmt::{Binary, Debug, Display, LowerExp, LowerHex, Octal, Pointer, UpperExp, UpperHex},
    future::Future,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    ops::{
        AddAssign, BitAndAssign, BitOrAssign, BitXorAssign, Deref, DerefMut, DivAssign, Index,
        IndexMut, MulAssign, RemAssign, ShlAssign, ShrAssign, SubAssign,
    },
    pin::Pin,
};

use aligned::Alignment;

use crate::SizedDst;

macro_rules! impl_fmt_trait {
    ($trait:ident) => {
        impl<DST: ?Sized + $trait, A: Alignment, const N: usize> $trait for SizedDst<DST, A, N> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                self.deref().fmt(f)
            }
        }
    };
}

impl_fmt_trait!(Debug);
impl_fmt_trait!(Display);
impl_fmt_trait!(Binary);
impl_fmt_trait!(Octal);
impl_fmt_trait!(LowerHex);
impl_fmt_trait!(UpperHex);
impl_fmt_trait!(LowerExp);
impl_fmt_trait!(UpperExp);
impl_fmt_trait!(Pointer);

impl<T: ?Sized, DST: ?Sized + AsRef<T>, A: Alignment, const N: usize> AsRef<T>
    for SizedDst<DST, A, N>
{
    fn as_ref(&self) -> &T {
        self.deref().as_ref()
    }
}

impl<T: ?Sized, DST: ?Sized + AsMut<T>, A: Alignment, const N: usize> AsMut<T>
    for SizedDst<DST, A, N>
{
    fn as_mut(&mut self) -> &mut T {
        self.deref_mut().as_mut()
    }
}

impl<DST: ?Sized, A: Alignment, const N: usize> Borrow<DST> for SizedDst<DST, A, N> {
    fn borrow(&self) -> &DST {
        self.deref()
    }
}

impl<DST: ?Sized, A: Alignment, const N: usize> BorrowMut<DST> for SizedDst<DST, A, N> {
    fn borrow_mut(&mut self) -> &mut DST {
        self.deref_mut()
    }
}

impl<Idx, DST: ?Sized + Index<Idx>, A: Alignment, const N: usize> Index<Idx>
    for SizedDst<DST, A, N>
{
    type Output = DST::Output;
    fn index(&self, index: Idx) -> &<Self as Index<Idx>>::Output {
        self.deref().index(index)
    }
}

impl<Idx, DST: ?Sized + IndexMut<Idx>, A: Alignment, const N: usize> IndexMut<Idx>
    for SizedDst<DST, A, N>
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.deref_mut().index_mut(index)
    }
}

macro_rules! impl_assign_trait {
    ($trait:ident, $method:ident) => {
        impl<Rhs, DST: ?Sized + $trait<Rhs>, A: Alignment, const N: usize> $trait<Rhs>
            for SizedDst<DST, A, N>
        {
            fn $method(&mut self, rhs: Rhs) {
                self.deref_mut().$method(rhs)
            }
        }
    };
}

impl_assign_trait!(AddAssign, add_assign);
impl_assign_trait!(SubAssign, sub_assign);
impl_assign_trait!(BitOrAssign, bitor_assign);
impl_assign_trait!(BitAndAssign, bitand_assign);
impl_assign_trait!(BitXorAssign, bitxor_assign);
impl_assign_trait!(MulAssign, mul_assign);
impl_assign_trait!(DivAssign, div_assign);
impl_assign_trait!(RemAssign, rem_assign);
impl_assign_trait!(ShrAssign, shr_assign);
impl_assign_trait!(ShlAssign, shl_assign);

impl<DST: ?Sized + Iterator, A: Alignment, const N: usize> Iterator for SizedDst<DST, A, N> {
    type Item = DST::Item;
    fn next(&mut self) -> Option<Self::Item> {
        self.deref_mut().next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.deref().size_hint()
    }
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.deref_mut().nth(n)
    }
}

impl<DST: ?Sized + DoubleEndedIterator, A: Alignment, const N: usize> DoubleEndedIterator
    for SizedDst<DST, A, N>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.deref_mut().next_back()
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.deref_mut().nth_back(n)
    }
}

impl<DST: ?Sized + ExactSizeIterator, A: Alignment, const N: usize> ExactSizeIterator
    for SizedDst<DST, A, N>
{
    fn len(&self) -> usize {
        self.deref().len()
    }
}

impl<DST: ?Sized + FusedIterator, A: Alignment, const N: usize> FusedIterator
    for SizedDst<DST, A, N>
{
}

macro_rules! cmp_method {
    ($method:ident -> $ret:ty) => {
        fn $method(&self, other: &Self) -> $ret {
            self.deref().$method(other)
        }
    };
}

impl<DST: ?Sized + PartialEq, A: Alignment, const N: usize> PartialEq for SizedDst<DST, A, N> {
    cmp_method!(eq -> bool);
}

impl<DST: ?Sized + PartialOrd, A: Alignment, const N: usize> PartialOrd for SizedDst<DST, A, N> {
    cmp_method!(partial_cmp -> Option<Ordering>);
    cmp_method!(lt -> bool);
    cmp_method!(le -> bool);
    cmp_method!(gt -> bool);
    cmp_method!(ge -> bool);
}

impl<DST: ?Sized + Eq, A: Alignment, const N: usize> Eq for SizedDst<DST, A, N> {}

impl<DST: ?Sized + Ord, A: Alignment, const N: usize> Ord for SizedDst<DST, A, N> {
    cmp_method!(cmp -> Ordering);
}

impl<DST: ?Sized + Hasher, A: Alignment, const N: usize> Hasher for SizedDst<DST, A, N> {
    fn finish(&self) -> u64 {
        self.deref().finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        self.deref_mut().write(bytes)
    }
    fn write_u8(&mut self, i: u8) {
        self.deref_mut().write_u8(i)
    }
    fn write_u16(&mut self, i: u16) {
        self.deref_mut().write_u16(i)
    }
    fn write_u32(&mut self, i: u32) {
        self.deref_mut().write_u32(i)
    }
    fn write_u64(&mut self, i: u64) {
        self.deref_mut().write_u64(i)
    }
    fn write_u128(&mut self, i: u128) {
        self.deref_mut().write_u128(i)
    }
    fn write_usize(&mut self, i: usize) {
        self.deref_mut().write_usize(i)
    }
    fn write_i8(&mut self, i: i8) {
        self.deref_mut().write_i8(i)
    }
    fn write_i16(&mut self, i: i16) {
        self.deref_mut().write_i16(i)
    }
    fn write_i32(&mut self, i: i32) {
        self.deref_mut().write_i32(i)
    }
    fn write_i64(&mut self, i: i64) {
        self.deref_mut().write_i64(i)
    }
    fn write_i128(&mut self, i: i128) {
        self.deref_mut().write_i128(i)
    }
    fn write_isize(&mut self, i: isize) {
        self.deref_mut().write_isize(i)
    }
}

impl<DST: ?Sized + Hash, A: Alignment, const N: usize> Hash for SizedDst<DST, A, N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<DST: ?Sized + Future, A: Alignment, const N: usize> Future for SizedDst<DST, A, N> {
    type Output = DST::Output;
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        // SAFETY:
        // This is basically a pin projection into Pin<&mut DST>, so the pin projection rules apply
        // - SizedDst is Unpin only if DST is Unpin, because it has a PhantomData<DST> field.
        // - The destructor of SizedDst only calls drop_in_place on the DST pointer. DST's
        //   destructor can only move DST if it implements Unpin, which also means SizedDst is
        //   Unpin. Thus, SizedDst's destructor can only move its DST field if SizedDst is Unpin.
        // - The only way to get a mutable reference to DST is via deref_mut, which can't be called
        //   while SizedDst is pinned, so it's impossible to re-use the memory used for the DST
        //   with safe code after SizedDst has been pinned.
        // - Likewise, since there's no way to obtain a mutable DST reference while SizedDst is
        //   pinned, data can't be moved out of the DST after it's pinned.
        unsafe { self.map_unchecked_mut(|p| &mut **p).poll(cx) }
    }
}

#[cfg(test)]
mod tests {
    use static_assertions::{assert_impl_all, assert_not_impl_all};

    use super::*;
    use crate::*;

    assert_not_impl_all!(SizedDstNative<dyn Future<Output = i32>, 12>: Unpin);
    assert_impl_all!(SizedDstNative<dyn Future<Output = i32> + Unpin, 12>: Unpin);

    #[test]
    fn future() {
        let fut = async { 5 };
        let dst = SizedDstNative::<dyn Future<Output = i32>, 12>::new(fut);

        let n = futures_executor::block_on(dst);
        assert_eq!(n, 5);
    }
}

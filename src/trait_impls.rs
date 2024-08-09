use core::{
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    error::Error,
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
#[cfg(feature = "std")]
use std::{
    io::{BufRead, Read, Seek, Write},
    os::fd::{AsFd, AsRawFd},
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

impl<DST: ?Sized + core::fmt::Write, A: Alignment, const N: usize> core::fmt::Write
    for SizedDst<DST, A, N>
{
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.deref_mut().write_str(s)
    }
    fn write_char(&mut self, c: char) -> core::fmt::Result {
        self.deref_mut().write_char(c)
    }
    fn write_fmt(&mut self, args: core::fmt::Arguments<'_>) -> core::fmt::Result {
        self.deref_mut().write_fmt(args)
    }
}

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

impl<DST: ?Sized + Error, A: Alignment, const N: usize> Error for SizedDst<DST, A, N> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.deref().source()
    }
}

#[cfg(feature = "std")]
impl<DST: ?Sized + Read, A: Alignment, const N: usize> Read for SizedDst<DST, A, N> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.deref_mut().read(buf)
    }
    fn read_vectored(&mut self, bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize> {
        self.deref_mut().read_vectored(bufs)
    }
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize> {
        self.deref_mut().read_to_end(buf)
    }
    fn read_to_string(&mut self, buf: &mut String) -> std::io::Result<usize> {
        self.deref_mut().read_to_string(buf)
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        self.deref_mut().read_exact(buf)
    }
}

#[cfg(feature = "std")]
impl<DST: ?Sized + Write, A: Alignment, const N: usize> Write for SizedDst<DST, A, N> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.deref_mut().write(buf)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.deref_mut().flush()
    }
    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize> {
        self.deref_mut().write_vectored(bufs)
    }
    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()> {
        self.deref_mut().write_all(buf)
    }
    fn write_fmt(&mut self, fmt: std::fmt::Arguments<'_>) -> std::io::Result<()> {
        self.deref_mut().write_all(fmt)
    }
}

#[cfg(feature = "std")]
impl<DST: ?Sized + BufRead, A: Alignment, const N: usize> BufRead for SizedDst<DST, A, N> {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        self.deref_mut().fill_buf()
    }
    fn consume(&mut self, amt: usize) {
        self.deref_mut().consume(amt)
    }
    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> std::io::Result<usize> {
        self.deref_mut().read_until(byte, buf)
    }
    fn read_line(&mut self, buf: &mut String) -> std::io::Result<usize> {
        self.deref_mut().read_line(buf)
    }
}

#[cfg(feature = "std")]
impl<DST: ?Sized + Seek, A: Alignment, const N: usize> Seek for SizedDst<DST, A, N> {
    fn seek(&mut self, pos: std::io::SeekFrom) -> std::io::Result<u64> {
        self.deref_mut().seek(pos)
    }
    fn rewind(&mut self) -> std::io::Result<()> {
        self.deref_mut().rewind()
    }
    fn stream_position(&mut self) -> std::io::Result<u64> {
        self.deref_mut().stream_position()
    }
    fn seek_relative(&mut self, offset: i64) -> std::io::Result<()> {
        self.deref_mut().seek_relative(offset)
    }
}

#[cfg(feature = "std")]
impl<DST: ?Sized + AsFd, A: Alignment, const N: usize> AsFd for SizedDst<DST, A, N> {
    fn as_fd(&self) -> std::os::unix::prelude::BorrowedFd<'_> {
        self.deref().as_fd()
    }
}

#[cfg(feature = "std")]
impl<DST: ?Sized + AsRawFd, A: Alignment, const N: usize> AsRawFd for SizedDst<DST, A, N> {
    fn as_raw_fd(&self) -> std::os::unix::prelude::RawFd {
        self.deref().as_raw_fd()
    }
}

#[cfg(test)]
mod tests {
    use static_assertions::{assert_impl_all, assert_not_impl_all};

    use super::*;
    use crate::*;

    // Ensure Unpin is only implemented if DST is Unpin
    assert_not_impl_all!(SizedDstNative<dyn Future<Output = i32>, 12>: Unpin);
    assert_impl_all!(SizedDstNative<dyn Future<Output = i32>, 12>: Future<Output = i32>);
    assert_impl_all!(SizedDstNative<dyn Future<Output = i32> + Unpin, 12>: Unpin, Future<Output = i32>);

    #[test]
    fn future() {
        let fut = async { 5 };
        let dst = SizedDstNative::<dyn Future<Output = i32>, 12>::new(fut);

        let n = futures_executor::block_on(dst);
        assert_eq!(n, 5);
    }

    assert_impl_all!(SizedDstNative<dyn AsRef<[u8]>, 12>: AsRef<[u8]>, BorrowMut<dyn AsRef<[u8]>>);
    assert_impl_all!(SizedDstNative<dyn AsMut<[u8]>, 12>: AsMut<[u8]>, BorrowMut<dyn AsMut<[u8]>>);

    #[test]
    fn as_ref() {
        let dst = SizedDstNative::<dyn AsRef<[u8]>, 32>::new(String::from("xyz"));
        assert_eq!(dst.as_ref(), b"xyz");
    }

    #[test]
    fn as_mut() {
        let mut dst = SizedDstNative::<dyn AsMut<[u32]>, 32>::new(vec![0, 1, 2]);
        assert_eq!(dst.as_mut(), &[0, 1, 2]);
        dst.as_mut()[0] = 3;
        assert_eq!(dst.as_mut(), &[3, 1, 2]);
    }

    assert_impl_all!(SizedDstNative<dyn IndexMut<usize, Output = u8>, 32>: IndexMut<usize>, Index<usize>);

    #[test]
    fn index() {
        let mut dst = SizedDstNative::<dyn IndexMut<usize, Output = u8>, 32>::new(vec![0, 3]);
        assert_eq!(dst[0], 0);
        assert_eq!(dst[1], 3);
        dst[0] = 4;
        assert_eq!(dst[0], 4);
    }

    assert_impl_all!(SizedDstNative<dyn DoubleEndedIterator<Item = u8>, 32>: DoubleEndedIterator, Iterator);
    assert_impl_all!(SizedDstNative<dyn FusedIterator<Item = u8>, 32>: FusedIterator, Iterator);
    assert_impl_all!(SizedDstNative<dyn ExactSizeIterator<Item = u8>, 32>: ExactSizeIterator, Iterator);

    #[test]
    fn iterator() {
        let mut dst = SizedDstNative::<dyn DoubleEndedIterator<Item = u8>, 32>::new(
            [2, 3, 4, 5, 6].into_iter(),
        );
        assert_eq!(dst.next(), Some(2));
        assert_eq!(dst.nth(1), Some(4));
        assert_eq!(dst.next_back(), Some(6));
        assert_eq!(dst.nth_back(0), Some(5));
        assert_eq!(dst.next(), None);
    }
}

use core::{
    any::Any,
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

use crate::DstBase;

macro_rules! impl_fmt_trait {
    ($trait:ident) => {
        impl<D: ?Sized + $trait, A: Alignment, const N: usize> $trait for DstBase<D, A, N> {
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

impl<D: ?Sized + core::fmt::Write, A: Alignment, const N: usize> core::fmt::Write
    for DstBase<D, A, N>
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

impl<T: ?Sized, D: ?Sized + AsRef<T>, A: Alignment, const N: usize> AsRef<T> for DstBase<D, A, N> {
    fn as_ref(&self) -> &T {
        self.deref().as_ref()
    }
}

impl<T: ?Sized, D: ?Sized + AsMut<T>, A: Alignment, const N: usize> AsMut<T> for DstBase<D, A, N> {
    fn as_mut(&mut self) -> &mut T {
        self.deref_mut().as_mut()
    }
}

impl<D: ?Sized, A: Alignment, const N: usize> Borrow<D> for DstBase<D, A, N> {
    fn borrow(&self) -> &D {
        self.deref()
    }
}

impl<D: ?Sized, A: Alignment, const N: usize> BorrowMut<D> for DstBase<D, A, N> {
    fn borrow_mut(&mut self) -> &mut D {
        self.deref_mut()
    }
}

impl<Idx, D: ?Sized + Index<Idx>, A: Alignment, const N: usize> Index<Idx> for DstBase<D, A, N> {
    type Output = D::Output;
    fn index(&self, index: Idx) -> &<Self as Index<Idx>>::Output {
        self.deref().index(index)
    }
}

impl<Idx, D: ?Sized + IndexMut<Idx>, A: Alignment, const N: usize> IndexMut<Idx>
    for DstBase<D, A, N>
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.deref_mut().index_mut(index)
    }
}

macro_rules! impl_assign_trait {
    ($trait:ident, $method:ident) => {
        impl<Rhs, D: ?Sized + $trait<Rhs>, A: Alignment, const N: usize> $trait<Rhs>
            for DstBase<D, A, N>
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

impl<D: ?Sized + Iterator, A: Alignment, const N: usize> Iterator for DstBase<D, A, N> {
    type Item = D::Item;
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

impl<D: ?Sized + DoubleEndedIterator, A: Alignment, const N: usize> DoubleEndedIterator
    for DstBase<D, A, N>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.deref_mut().next_back()
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.deref_mut().nth_back(n)
    }
}

impl<D: ?Sized + ExactSizeIterator, A: Alignment, const N: usize> ExactSizeIterator
    for DstBase<D, A, N>
{
    fn len(&self) -> usize {
        self.deref().len()
    }
}

impl<D: ?Sized + FusedIterator, A: Alignment, const N: usize> FusedIterator for DstBase<D, A, N> {}

macro_rules! cmp_method {
    ($method:ident -> $ret:ty) => {
        fn $method(&self, other: &Self) -> $ret {
            self.deref().$method(other)
        }
    };
}

impl<D: ?Sized + PartialEq, A: Alignment, const N: usize> PartialEq for DstBase<D, A, N> {
    cmp_method!(eq -> bool);
}

impl<D: ?Sized + PartialOrd, A: Alignment, const N: usize> PartialOrd for DstBase<D, A, N> {
    cmp_method!(partial_cmp -> Option<Ordering>);
    cmp_method!(lt -> bool);
    cmp_method!(le -> bool);
    cmp_method!(gt -> bool);
    cmp_method!(ge -> bool);
}

impl<D: ?Sized + Eq, A: Alignment, const N: usize> Eq for DstBase<D, A, N> {}

impl<D: ?Sized + Ord, A: Alignment, const N: usize> Ord for DstBase<D, A, N> {
    cmp_method!(cmp -> Ordering);
}

impl<D: ?Sized + Hasher, A: Alignment, const N: usize> Hasher for DstBase<D, A, N> {
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

impl<D: ?Sized + Hash, A: Alignment, const N: usize> Hash for DstBase<D, A, N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<D: ?Sized + Future, A: Alignment, const N: usize> Future for DstBase<D, A, N> {
    type Output = D::Output;
    fn poll(
        self: Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        // SAFETY:
        // This is basically a pin projection into Pin<&mut D>, so the pin projection rules apply
        // - DstBase is Unpin only if D is Unpin, because it has a PhantomData<D> field.
        // - The destructor of DstBase only calls drop_in_place on the D pointer. D's
        //   destructor can only move D if it implements Unpin, which also means DstBase is
        //   Unpin. Thus, DstBase's destructor can only move its D field if DstBase is Unpin.
        // - The only way to get a mutable reference to D is via deref_mut, which can't be called
        //   while DstBase is pinned, so it's impossible to re-use the memory used for the D
        //   with safe code after DstBase has been pinned.
        // - Likewise, since there's no way to obtain a mutable D reference while DstBase is
        //   pinned, data can't be moved out of the D after it's pinned.
        unsafe { self.map_unchecked_mut(|p| &mut **p).poll(cx) }
    }
}

impl<D: ?Sized + Error, A: Alignment, const N: usize> Error for DstBase<D, A, N> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.deref().source()
    }
}

macro_rules! downcast_impl {
    ($trait:ident $(+ $marker:ident)*) => {
        impl<A: Alignment, const N: usize> DstBase<dyn $trait $(+ $marker)*, A, N> {
            /// Attempt to downcast to a concrete type
            pub fn downcast<T: $trait + 'static>(self) -> Option<T> {
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
downcast_impl!(Any);
downcast_impl!(Any + Send);
downcast_impl!(Any + Send + Sync);
downcast_impl!(Error);
downcast_impl!(Error + Send);
downcast_impl!(Error + Send + Sync);

#[cfg(feature = "std")]
impl<D: ?Sized + Read, A: Alignment, const N: usize> Read for DstBase<D, A, N> {
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
impl<D: ?Sized + Write, A: Alignment, const N: usize> Write for DstBase<D, A, N> {
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
        self.deref_mut().write_fmt(fmt)
    }
}

#[cfg(feature = "std")]
impl<D: ?Sized + BufRead, A: Alignment, const N: usize> BufRead for DstBase<D, A, N> {
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
impl<D: ?Sized + Seek, A: Alignment, const N: usize> Seek for DstBase<D, A, N> {
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
impl<D: ?Sized + AsFd, A: Alignment, const N: usize> AsFd for DstBase<D, A, N> {
    fn as_fd(&self) -> std::os::unix::prelude::BorrowedFd<'_> {
        self.deref().as_fd()
    }
}

#[cfg(feature = "std")]
impl<D: ?Sized + AsRawFd, A: Alignment, const N: usize> AsRawFd for DstBase<D, A, N> {
    fn as_raw_fd(&self) -> std::os::unix::prelude::RawFd {
        self.deref().as_raw_fd()
    }
}

#[cfg(test)]
mod tests {
    use static_assertions::{assert_impl_all, assert_not_impl_any};

    use super::*;
    use crate::*;

    // Ensure Send and Sync propagate properly
    assert_not_impl_any!(DstA8::<dyn ToString, 8>: Send, Sync);
    assert_impl_all!(DstA8::<dyn ToString + Send, 8>: Send);
    assert_not_impl_any!(DstA8::<dyn ToString + Send, 8>: Sync);
    assert_impl_all!(DstA8::<dyn ToString + Send + Sync, 8>: Send, Sync);

    // Ensure Unpin is only implemented if D is Unpin
    assert_not_impl_any!(Dst<dyn Future<Output = i32>, 12>: Unpin);
    assert_impl_all!(Dst<dyn Future<Output = i32>, 12>: Future<Output = i32>);
    assert_impl_all!(Dst<dyn Future<Output = i32> + Unpin, 12>: Unpin, Future<Output = i32>);

    #[test]
    fn future() {
        let fut = async { 5 };
        let dst = Dst::<dyn Future<Output = i32>, 12>::new(fut);

        let n = futures_executor::block_on(dst);
        assert_eq!(n, 5);
    }

    assert_impl_all!(Dst<dyn AsRef<[u8]>, 12>: AsRef<[u8]>, BorrowMut<dyn AsRef<[u8]>>);
    assert_impl_all!(Dst<dyn AsMut<[u8]>, 12>: AsMut<[u8]>, BorrowMut<dyn AsMut<[u8]>>);

    #[test]
    fn as_ref() {
        let dst = Dst::<dyn AsRef<[u8]>, 32>::new(String::from("xyz"));
        assert_eq!(dst.as_ref(), b"xyz");
    }

    #[test]
    fn as_mut() {
        let mut dst = Dst::<dyn AsMut<[u32]>, 32>::new(vec![0, 1, 2]);
        assert_eq!(dst.as_mut(), &[0, 1, 2]);
        dst.as_mut()[0] = 3;
        assert_eq!(dst.as_mut(), &[3, 1, 2]);
    }

    assert_impl_all!(Dst<dyn IndexMut<usize, Output = u8>, 32>: IndexMut<usize>, Index<usize>);

    #[test]
    fn index() {
        let mut dst = Dst::<dyn IndexMut<usize, Output = u8>, 32>::new(vec![0, 3]);
        assert_eq!(dst[0], 0);
        assert_eq!(dst[1], 3);
        dst[0] = 4;
        assert_eq!(dst[0], 4);
    }

    assert_impl_all!(Dst<dyn DoubleEndedIterator<Item = u8>, 32>: DoubleEndedIterator, Iterator);
    assert_impl_all!(Dst<dyn FusedIterator<Item = u8>, 32>: FusedIterator, Iterator);
    assert_impl_all!(Dst<dyn ExactSizeIterator<Item = u8>, 32>: ExactSizeIterator, Iterator);

    #[test]
    fn iterator() {
        let mut dst =
            Dst::<dyn DoubleEndedIterator<Item = u8>, 32>::new([2, 3, 4, 5, 6].into_iter());
        assert_eq!(dst.next(), Some(2));
        assert_eq!(dst.nth(1), Some(4));
        assert_eq!(dst.next_back(), Some(6));
        assert_eq!(dst.nth_back(0), Some(5));
        assert_eq!(dst.next(), None);
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
        let val = obj.downcast::<Box<u32>>().unwrap();
        assert_eq!(*val, 2);

        let obj = Dst::<dyn Any, 32>::new(Box::new(2u32));
        assert!(obj.downcast::<String>().is_none());

        let obj = Dst::<dyn Error, 32>::new(std::io::Error::from(std::io::ErrorKind::NotFound));
        let val = obj.downcast::<std::io::Error>().unwrap();
        assert_eq!(val.kind(), std::io::ErrorKind::NotFound);
    }
}

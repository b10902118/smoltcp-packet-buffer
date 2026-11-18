use core::ops::{Deref, DerefMut};
use core::fmt;

#[cfg(feature = "std")]
use std::boxed::Box;
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::boxed::Box;
#[cfg(feature = "std")]
use std::vec::Vec;
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;

use vstd::prelude::*;

verus! {

/// A managed slice.
///
/// This enum can be used to represent exclusive access to slices of objects.
/// In Rust, exclusive access to an object is obtained by either owning the object,
/// or owning a mutable pointer to the object; hence, "managed".
///
/// The purpose of this enum is providing good ergonomics with `std` present while making
/// it possible to avoid having a heap at all (which of course means that `std` is not present).
/// To achieve this, the variants other than `Borrowed` are only available when the corresponding
/// feature is opted in.
///
/// A function that requires a managed object should be generic over an `Into<ManagedSlice<'a, T>>`
/// argument; then, it will be possible to pass either a `Vec<T>`, or a `&'a mut [T]`
/// without any conversion at the call site.
///
/// See also [Managed](enum.Managed.html).
pub enum ManagedSlice<'a, T: 'a> {
    /// Borrowed variant for no heap implementations
    Borrowed(&'a mut [T]),
    /// Owned variant, only available with the `std` or `alloc` feature enabled.
    #[cfg(any(feature = "std", feature = "alloc"))]
    Owned(Vec<T>)
}

/// Abstract view: the sequence of elements, regardless of which variant holds them.
impl<'a, T: 'a> View for ManagedSlice<'a, T> {
    type V = Seq<T>;

    open spec fn view(&self) -> Seq<T> {
        match self {
            ManagedSlice::Borrowed(s) => (**s)@,
            #[cfg(any(feature = "std", feature = "alloc"))]
            ManagedSlice::Owned(v) => v@,
        }
    }
}

impl<'a, T: 'a> ManagedSlice<'a, T> {
    /// Verified body of `Deref::deref`.
    pub fn as_slice(&self) -> (ret: &[T])
        ensures
            ret@ == self@,
    {
        match self {
            ManagedSlice::Borrowed(value) => &**value, //returns the unmutable shared refernce to [T]
            #[cfg(any(feature = "std", feature = "alloc"))]
            ManagedSlice::Owned(value) => value.as_slice(), //call std as_slice on &Vec<T>
        }
    }

    /// Verified body of `DerefMut::deref_mut`.
    ///
    /// The returned slice starts out equal to the managed slice's contents, and
    /// whatever the caller leaves in it when the borrow ends becomes the managed
    /// slice's new contents.
    pub fn as_mut_slice(&mut self) -> (ret: &mut [T])
        ensures
            (*ret)@ == old(self)@, //on this fuct's return the slices match
            final(self)@ == (*final(ret))@, //when the caller updates the slice with this mutable reference ret, that slice is updated in memory wherever that slice is owned. This is checked on when the borrow of ret ends in the caller.
    {
        match self {
            ManagedSlice::Borrowed(value) => &mut **value,
            #[cfg(any(feature = "std", feature = "alloc"))]
            ManagedSlice::Owned(value) => value.as_mut_slice(),
        }
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Not verified: plain Rust outside `verus!`.
// ---------------------------------------------------------------------------

impl<'a, T: 'a> fmt::Debug for ManagedSlice<'a, T>
        where T: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ManagedSlice::Borrowed(x) => write!(f, "Borrowed({:?})", x),
            #[cfg(any(feature = "std", feature = "alloc"))]
            ManagedSlice::Owned(x)    => write!(f, "Owned({:?})", x)
        }
    }
}

impl<'a, T: 'a> From<&'a mut [T]> for ManagedSlice<'a, T> {
    fn from(value: &'a mut [T]) -> Self {
        ManagedSlice::Borrowed(value)
    }
}

macro_rules! from_unboxed_slice {
    ($n:expr) => (
        impl<'a, T> From<[T; $n]> for ManagedSlice<'a, T> {
            #[inline]
            fn from(value: [T; $n]) -> Self {
                ManagedSlice::Owned((Box::new(value) as Box<[T]>).into_vec())
            }
        }
    );
    ($n:expr, $( $r:expr ),*) => (
        from_unboxed_slice!($n);
        from_unboxed_slice!($( $r ),*);
    )
}

#[cfg(any(feature = "std", feature = "alloc"))]
from_unboxed_slice!(0,  1,   2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
                    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31);

#[cfg(any(feature = "std", feature = "alloc"))]
impl<'a, T: 'a> From<Vec<T>> for ManagedSlice<'a, T> {
    fn from(value: Vec<T>) -> Self {
        ManagedSlice::Owned(value)
    }
}

// The trait impls just forward to the verified methods above, so their
// behaviour is exactly what `as_slice` / `as_mut_slice` prove.
impl<'a, T: 'a> Deref for ManagedSlice<'a, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<'a, T: 'a> DerefMut for ManagedSlice<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

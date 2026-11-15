// Flux specifications for external items used by the storage containers.
//
// These are trusted and not verified, they describe the behaviour of code that
// lives outside this crate (`managed`, `core`).

use core::ops::{Deref, DerefMut};

use flux_core as _;

use flux_rs::attrs::*;
use managed::ManagedSlice;

#[extern_spec(managed)]
#[refined_by(len: int)]
#[invariant(0 <= len)]
struct ManagedSlice<'a, T>;

#[extern_spec(managed)]
#[assoc(fn as_deref(v: Self, target: int) -> bool { v.len == target })]
impl<'a, T> Deref for ManagedSlice<'a, T> {
    #[spec(fn(self: &Self[@n]) -> &<ManagedSlice<T> as Deref>::Target[n])]
    fn deref<'s>(&'s self) -> &'s <ManagedSlice<'a, T> as Deref>::Target;
}

#[extern_spec(managed)]
impl<'a, T> DerefMut for ManagedSlice<'a, T> {
    #[spec(fn(self: &mut Self[@n]) -> &mut <ManagedSlice<T> as Deref>::Target[n])]
    fn deref_mut<'s>(&'s mut self) -> &'s mut <ManagedSlice<'a, T> as Deref>::Target;
}

#[extern_spec(core::cmp)]
#[spec(fn(T[@a], T[@b]) -> T{v: <T as core::cmp::Ord>::min_res(a, b, v)})]
fn min<T: Ord>(v1: T, v2: T) -> T;

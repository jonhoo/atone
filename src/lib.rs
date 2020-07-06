//! A `VecDeque` (and `Vec`) variant that spreads resize load across pushes.
//!
//! Most vector-like implementations, such as `Vec` and `VecDeque`, must occasionally "resize" the
//! backing memory for the vector as the number of elements grows. This means allocating a new
//! vector (usually of twice the size), and moving all the elements from the old vector to the new
//! one. As your vector gets larger, this process takes longer and longer.
//!
//! For most applications, this behavior is fine — if some very small number of pushes take longer
//! than others, the application won't even notice. And if the vector is relatively small anyway,
//! even those "slow" pushes are quite fast. Similarly, if your vector grow for a while, and then
//! _stops_ growing, the "steady state" of your application won't see any resizing pauses at all.
//!
//! Where resizing becomes a problem is in applications that use vectors to keep ever-growing state
//! where tail latency is important. At large scale, it is simply not okay for one push to take 30
//! milliseconds when most take double-digit **nano**seconds. Worse yet, these resize pauses can
//! compound to create [significant spikes] in tail latency.
//!
//! This crate implements a technique referred to as "incremental resizing", in contrast to the
//! common "all-at-once" approached outlined above. At its core, the idea is pretty simple: instead
//! of moving all the elements to the resized vector immediately, move a couple each time a push
//! happens. This spreads the cost of moving the elements so that _each_ push becomes a little
//! slower until the resize has finished, instead of _one_ push becoming a _lot_ slower.
//!
//! This approach isn't free, however. While the resize is going on, the old vector must be
//! kept around (so memory isn't reclaimed immediately), and iterators and other vector-wide
//! operations must access both vectors, which makes them slower. Only once the resize completes is
//! the old vector reclaimed and full performance restored.
//!
//! To help you decide whether this implementation is right for you, here's a handy reference for
//! how this implementation compares to the standard library vectors:
//!
//!  - Pushes all take approximately the same time.
//!    After a resize, they will be slower for a while, but only by a relatively small factor.
//!  - Memory is not reclaimed immediately upon resize.
//!  - Access operations are marginally slower as they must check two vectors.
//!  - The incremental vector is slightly larger on the stack.
//!  - The "efficiency" of the resize is slightly lower as the all-at-once resize moves the items
//!    from the small vector to the large one in batch, whereas the incremental does a series of
//!    pushes.
//!
//! Also, since this crate must keep two vectors, it cannot guarantee that the elements are stored
//! in one contiguous chunk of memory. Since it must move elements between then without losing
//! their order, it is backed by `VecDeque`s, which means that this is the case even after the
//! resize has completed. For this reason, this crate presents an interface that resembles
//! `VecDeque` more so than `Vec`. If you need contiguous memory, there's no good way to do
//! incremental resizing without low-level memory mapping magic that I'm aware of.
//!
//! # Why "atone"?
//!
//! We make the vector atone with more expensive pushes for the sin it committed by resizing..?
//!
//! [significant spikes]: https://twitter.com/jonhoo/status/1277618908355313670

#![no_std]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(rustdoc)]
#![cfg_attr(is_nightly, feature(deque_make_contiguous))]

#[cfg(any(test, miri))]
pub(crate) const R: usize = 4;
#[cfg(not(any(test, miri)))]
const R: usize = 8;

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg_attr(test, macro_use)]
extern crate alloc;

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::{repeat_with, FromIterator};
use core::mem;
use core::ops::Bound::{Excluded, Included, Unbounded};
use core::ops::{Index, IndexMut, RangeBounds};

use alloc::collections::VecDeque;
use alloc::vec::Vec;

mod external_trait_impls;
mod iter;

/// A `VecDeque` (and `Vec`) variant that spreads resize load across pushes.
pub mod vc {
    pub use super::iter::*;
}

/// A `VecDeque` (and `Vec`) variant that spreads resize load across pushes.
///
/// See the [crate-level documentation] for details.
///
/// [crate-level documentation]: index.html
pub struct Vc<T> {
    // Logically, the arrangement here is that `head` is the leftovers from the previous resize.
    // All of which preceede the `tail`, which is where new pushes go.
    new_tail: VecDeque<T>,
    old_head: Option<VecDeque<T>>,
}

impl<T: Clone> Clone for Vc<T> {
    fn clone(&self) -> Vc<T> {
        self.iter().cloned().collect()
    }

    fn clone_from(&mut self, other: &Self) {
        self.clear();
        self.new_tail.reserve(other.len());
        self.new_tail.extend(other.iter().cloned());
    }
}

impl<T> Default for Vc<T> {
    /// Creates an empty `Vc<T>`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Vc<T> {
    /// Creates an empty `Vc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let vector: Vc<u32> = Vc::new();
    /// ```
    pub fn new() -> Self {
        Self {
            new_tail: VecDeque::new(),
            old_head: None,
        }
    }

    /// Creates an empty `Vc` with space for at least `capacity` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let vector: Vc<u32> = Vc::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            new_tail: VecDeque::with_capacity(capacity),
            old_head: None,
        }
    }

    /// Provides a reference to the element at the given index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// assert_eq!(buf.get(1), Some(&4));
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        let old_len = self.old_len();
        if index < old_len {
            // index < old_len implies old_len > 0 and index in-bounds
            Some(
                unsafe { self.old_ref() }
                    .get(index)
                    .unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() }),
            )
        } else {
            self.new_tail.get(index - old_len)
        }
    }

    /// Provides a mutable reference to the element at the given index.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// if let Some(elem) = buf.get_mut(1) {
    ///     *elem = 7;
    /// }
    ///
    /// assert_eq!(buf[1], 7);
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        let old_len = self.old_len();
        if index < old_len {
            // index < old_len implies old_len > 0 and index in-bounds
            Some(
                unsafe { self.old_mut() }
                    .get_mut(index)
                    .unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() }),
            )
        } else {
            self.new_tail.get_mut(index - old_len)
        }
    }

    /// Swaps elements at indices `i` and `j`.
    ///
    /// `i` and `j` may be equal.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if either index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// buf.push_back(5);
    /// assert_eq!(buf, vec![3, 4, 5]);
    /// buf.swap(0, 2);
    /// assert_eq!(buf, vec![5, 4, 3]);
    /// ```
    pub fn swap(&mut self, i: usize, j: usize) {
        let old_len = self.old_len();
        let i_in_old = i < old_len;
        if i_in_old == (j < old_len) {
            // same "part"
            if i_in_old {
                unsafe { self.old_mut() }.swap(i, j);
            } else {
                self.new_tail.swap(i - old_len, j - old_len);
            }
        } else if i_in_old {
            // NOTE: cannot use old_mut() here because of split borrows
            debug_assert!(self.old_head.is_some());
            let old_mut = self
                .old_head
                .as_mut()
                .unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
            mem::swap(&mut old_mut[i], &mut self.new_tail[j - old_len])
        } else {
            // j must be in old, so old must be non-empty
            debug_assert!(self.old_head.is_some());
            let old_mut = self
                .old_head
                .as_mut()
                .unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
            mem::swap(&mut old_mut[j], &mut self.new_tail[i - old_len])
        }
    }

    /// Reverses the order of elements in the `Vc`, in place.
    ///
    /// This method is only available on nightly compilers at the moment.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    /// use std::iter::FromIterator;
    ///
    /// let mut v: Vc<_> = (1..=3).collect();
    /// v.reverse();
    /// assert_eq!(v, vec![3, 2, 1]);
    /// ```
    #[inline]
    #[cfg(is_nightly)]
    pub fn reverse(&mut self) {
        // first, we reverse the tail in place
        self.new_tail.make_contiguous().reverse();
        // then, we push_back (instead of push_front) the head in reverse order
        if let Some(ref mut old_head) = self.old_head {
            while let Some(e) = old_head.pop_back() {
                self.new_tail.push_back(e);
            }
            let _ = self.take_old();
        }
    }

    /// Returns the number of elements the `Vc` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let buf: Vc<i32> = Vc::with_capacity(10);
    /// assert!(buf.capacity() >= 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.new_tail.capacity()
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to be inserted in the
    /// given `Vc`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore
    /// capacity can not be relied upon to be precisely minimal. Prefer [`reserve`] if future
    /// insertions are expected.
    ///
    /// While we try to make this incremental where possible, it may require all-at-once resizing.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf: Vc<i32> = vec![1].into_iter().collect();
    /// buf.reserve_exact(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        // See comments in reserve
        let need = self.old_len() + additional;
        if self.new_tail.capacity() - self.new_tail.len() > need {
            if cfg!(debug_assertions) {
                let buckets = self.new_tail.capacity();
                self.new_tail.reserve_exact(need);
                assert_eq!(
                    buckets,
                    self.new_tail.capacity(),
                    "resize despite sufficient capacity"
                );
            } else {
                self.new_tail.reserve_exact(need);
            }
        } else if self.old_len() != 0 {
            self.carry_all();
            self.grow(additional, true);
        } else {
            self.grow(additional, true);
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `Vc`. The collection may reserve more space to avoid frequent reallocations.
    ///
    /// While we try to make this incremental where possible, it may require all-at-once resizing.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf: Vc<i32> = vec![1].into_iter().collect();
    /// buf.reserve(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let need = self.old_len() + additional;
        if self.new_tail.capacity() - self.new_tail.len() > need {
            // We can accommodate the additional items without resizing, so all is well.
            if cfg!(debug_assertions) {
                let buckets = self.new_tail.capacity();
                self.new_tail.reserve(need);
                assert_eq!(
                    buckets,
                    self.new_tail.capacity(),
                    "resize despite sufficient capacity"
                );
            } else {
                self.new_tail.reserve(need);
            }
        } else if self.old_len() != 0 {
            // We probably have to resize, but we already have leftovers!
            //
            // Here, we're sort of stuck — we can't do this fully incrementally, because we'd need
            // to keep _three_ VecDeques: the current old_head, the current new_tail (which would
            // become the new old_head), _and_ the new, resized VecDeque.
            //
            // We do the best we can, which is to carry over all the current leftovers, and _then_
            // do an incremental resize. This at least moves only the current leftovers, rather
            // than the current full set of elements.
            self.carry_all();
            self.grow(additional, false);
        } else {
            // We probably have to resize, but since we don't have any leftovers, we can do it
            // incrementally.
            self.grow(additional, false);
        }
    }

    /// Shrinks the capacity of the `Vc` as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// `Vc` that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::with_capacity(15);
    /// buf.extend(0..4);
    /// assert_eq!(buf.capacity(), 15);
    /// buf.shrink_to_fit();
    /// assert!(buf.capacity() >= 4);
    /// assert!(buf.capacity() < 15);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }

    /// Shrinks the capacity of the `Vc` with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// Panics if the current capacity is smaller than the supplied
    /// minimum capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::with_capacity(15);
    /// buf.extend(0..4);
    /// assert_eq!(buf.capacity(), 15);
    /// // buf.shrink_to(6);
    /// assert!(buf.capacity() >= 6);
    /// // buf.shrink_to(0);
    /// assert!(buf.capacity() >= 4);
    /// ```
    fn shrink_to(&mut self, min_capacity: usize) {
        // Calculate the minimal number of elements that we need to reserve
        // space for.
        let mut need = self.new_tail.len();
        // We need to make sure that we never have to resize while there
        // are still leftovers.
        if self.old_head.is_some() {
            let old_len = self.old_len();
            // We need to move another lo.table.len() items.
            need += old_len;
            // We move R items on each insert.
            // That means we need to accomodate another
            // lo.table.len() / R (rounded up) inserts to move them all.
            need += (old_len + R - 1) / R;
        } else if min_capacity <= need {
            self.new_tail.shrink_to_fit();
        }
        let _min_size = usize::max(need, min_capacity);

        // FIXME: for now, this is a no-op
        // TODO: use VecDeque::shrink_to once available
        //       then, uncomment relevant code in doctest
        // self.new_tail.shrink_to(min_size);
    }

    /// Shortens the `Vc`, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than the `Vc`'s current length, this has no
    /// effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, vec![5, 10, 15]);
    /// buf.truncate(1);
    /// assert_eq!(buf, vec![5]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        let old_len = self.old_len();
        if old_len == 0 {
            self.new_tail.truncate(len);
        } else if len < old_len {
            self.new_tail.clear();
            for v in unsafe { self.take_old_unchecked() }.into_iter().take(len) {
                self.new_tail.push_back(v);
            }
        } else {
            self.new_tail.truncate(len - old_len);
            for v in unsafe { self.take_old_unchecked() }.into_iter().rev() {
                self.new_tail.push_front(v);
            }
        }
    }

    /// Returns a front-to-back iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(5);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// let b: &[_] = &[&5, &3, &4];
    /// let c: Vec<&i32> = buf.iter().collect();
    /// assert_eq!(&c[..], b);
    /// ```
    pub fn iter(&self) -> iter::Iter<'_, T> {
        iter::Iter {
            head: self.old_head.as_ref().map(|v| v.iter()),
            tail: self.new_tail.iter(),
        }
    }

    /// Returns a front-to-back iterator that returns mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(5);
    /// buf.push_back(3);
    /// buf.push_back(4);
    /// for num in buf.iter_mut() {
    ///     *num = *num - 2;
    /// }
    /// let b: &[_] = &[&mut 3, &mut 1, &mut 2];
    /// assert_eq!(&buf.iter_mut().collect::<Vec<&mut i32>>()[..], b);
    /// ```
    pub fn iter_mut(&mut self) -> iter::IterMut<'_, T> {
        iter::IterMut {
            head: self.old_head.as_mut().map(|v| v.iter_mut()),
            tail: self.new_tail.iter_mut(),
        }
    }

    /// Returns the single slice which contains, in order, the contents of the `Vc`, if possible.
    ///
    /// You will likely want to call [`make_contiguous`](#method.make_contiguous) before calling
    /// this method to ensure that this method returns `Some`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    /// let mut vector = Vc::new();
    ///
    /// vector.push(0);
    /// vector.push(1);
    /// vector.push(2);
    ///
    /// assert_eq!(vector.as_single_slice(), Some(&[0, 1, 2][..]));
    ///
    /// // Push enough items, and the memory is no longer
    /// // contiguous due to incremental resizing.
    /// for i in 3..16 {
    ///     vector.push(i);
    /// }
    ///
    /// assert_eq!(vector.as_single_slice(), None);
    ///
    /// // TODO:
    /// // With make_contiguous, we can bring it back.
    /// // vector.make_contiguous();
    /// // assert_eq!(vector.as_single_slice(), Some(&(0..16).collect::<Vec<_>>()[..]));
    /// ```
    #[inline]
    pub fn as_single_slice(&self) -> Option<&[T]> {
        if self.old_len() != 0 {
            None
        } else if let (tail, []) = self.new_tail.as_slices() {
            Some(tail)
        } else {
            None
        }
    }

    /// Returns the number of elements in the `Vc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut v = Vc::new();
    /// assert_eq!(v.len(), 0);
    /// v.push_back(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.new_tail.len() + self.old_len()
    }

    /// Returns `true` if the `Vc` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut v = Vc::new();
    /// assert!(v.is_empty());
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.new_tail.is_empty() && self.old_len() == 0
    }

    fn range_start_end<R>(&self, range: R) -> (usize, usize)
    where
        R: RangeBounds<usize>,
    {
        let len = self.len();
        let start = match range.start_bound() {
            Included(&n) => n,
            Excluded(&n) => n + 1,
            Unbounded => 0,
        };
        let end = match range.end_bound() {
            Included(&n) => n + 1,
            Excluded(&n) => n,
            Unbounded => len,
        };
        assert!(start <= end, "lower bound was too large");
        assert!(end <= len, "upper bound was too large");
        (start, end)
    }

    /// Creates an iterator that covers the specified range in the `VecDeque`.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let v: Vc<_> = vec![1, 2, 3].into_iter().collect();
    /// let range = v.range(2..).copied().collect::<Vc<_>>();
    /// assert_eq!(range, vec![3]);
    ///
    /// // A full range covers all contents
    /// let all = v.range(..);
    /// assert_eq!(all.len(), 3);
    /// ```
    #[inline]
    // TODO: with https://github.com/rust-lang/rust/pull/74099, this can become iter::Iter<'_, T>,
    // which would also give us DoubleEndedIterator + FusedIterator.
    pub fn range<R>(&self, range: R) -> impl ExactSizeIterator<Item = &'_ T>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = self.range_start_end(range);
        self.iter().skip(start).take(end - start)
    }

    /// Creates an iterator that covers the specified mutable range in the `VecDeque`.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut v: Vc<_> = vec![1, 2, 3].into_iter().collect();
    /// for v in v.range_mut(2..) {
    ///   *v *= 2;
    /// }
    /// assert_eq!(v, vec![1, 2, 6]);
    ///
    /// // A full range covers all contents
    /// for v in v.range_mut(..) {
    ///   *v *= 2;
    /// }
    /// assert_eq!(v, vec![2, 4, 12]);
    /// ```
    // TODO: with https://github.com/rust-lang/rust/pull/74099, this can become iter::IterMut<'_,
    // T>, which would also give us DoubleEndedIterator + FusedIterator.
    #[inline]
    pub fn range_mut<R>(&mut self, range: R) -> impl ExactSizeIterator<Item = &'_ mut T>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = self.range_start_end(range);
        self.iter_mut().skip(start).take(end - start)
    }

    /// Creates a draining iterator that removes the specified range in the
    /// `Vc` and yields the removed items.
    ///
    /// Note 1: The element range is removed even if the iterator is not
    /// consumed until the end.
    ///
    /// Note 2: It is unspecified how many elements are removed from the deque,
    /// if the `Drain` value is not dropped, but the borrow it holds expires
    /// (e.g., due to `mem::forget`).
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut v: Vc<_> = vec![1, 2, 3].into_iter().collect();
    /// let drained = v.drain(2..).collect::<Vc<_>>();
    /// assert_eq!(drained, vec![3]);
    /// assert_eq!(v, vec![1, 2]);
    ///
    /// // A full range clears all contents
    /// v.drain(..);
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> iter::Drain<'_, T>
    where
        R: RangeBounds<usize>,
    {
        let old_len = self.old_len();
        if old_len == 0 {
            return iter::Drain {
                head: None,
                tail: self.new_tail.drain(range),
            };
        }

        let (start_incl, end_excl) = self.range_start_end(range);
        debug_assert!(start_incl <= end_excl);
        let head = if start_incl < old_len {
            // TODO: take_old when drained if start_incl == 0 && end_excl >= old_len
            // NOTE: cannot use old_mut() here because of split borrows
            debug_assert!(self.old_head.is_some());
            let old_mut = self
                .old_head
                .as_mut()
                .unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
            Some(old_mut.drain(start_incl..end_excl.min(old_len)))
        } else {
            None
        };
        let tail = if end_excl > old_len {
            if start_incl > old_len {
                self.new_tail
                    .drain((start_incl - old_len)..(end_excl - old_len))
            } else {
                self.new_tail.drain(..(end_excl - old_len))
            }
        } else {
            self.new_tail.drain(..0)
        };

        iter::Drain { head, tail }
    }

    /// Clears the `Vc`, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut v = Vc::new();
    /// v.push_back(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        let _ = self.take_old();
        self.new_tail.clear();
    }

    /// Returns `true` if the `Vc` contains an element equal to the
    /// given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut vector: Vc<u32> = Vc::new();
    ///
    /// vector.push_back(0);
    /// vector.push_back(1);
    ///
    /// assert_eq!(vector.contains(&1), true);
    /// assert_eq!(vector.contains(&10), false);
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.new_tail.contains(x) || self.old_head.as_ref().map_or(false, |v| v.contains(x))
    }

    /// Provides a reference to the front element, or `None` if the `Vc` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut d = Vc::new();
    /// assert_eq!(d.front(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        self.old_head
            .as_ref()
            .and_then(|v| v.front())
            .or_else(|| self.new_tail.front())
    }

    /// Provides a mutable reference to the front element, or `None` if the
    /// `Vc` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut d = Vc::new();
    /// assert_eq!(d.front_mut(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.front_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.front(), Some(&9));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if let Some(e) = self.old_head.as_mut().and_then(|v| v.front_mut()) {
            Some(e)
        } else {
            self.new_tail.front_mut()
        }
    }

    /// Provides a reference to the back element, or `None` if the `Vc` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut d = Vc::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// assert_eq!(d.back(), Some(&2));
    /// ```
    pub fn back(&self) -> Option<&T> {
        self.new_tail
            .back()
            .or_else(|| self.old_head.as_ref().and_then(|v| v.back()))
    }

    /// Provides a mutable reference to the back element, or `None` if the
    /// `Vc` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut d = Vc::new();
    /// assert_eq!(d.back(), None);
    ///
    /// d.push_back(1);
    /// d.push_back(2);
    /// match d.back_mut() {
    ///     Some(x) => *x = 9,
    ///     None => (),
    /// }
    /// assert_eq!(d.back(), Some(&9));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        if let Some(e) = self.new_tail.back_mut() {
            Some(e)
        } else {
            self.old_head.as_mut().and_then(|v| v.back_mut())
        }
    }

    /// Removes the first element and returns it, or `None` if the `Vc` is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut d = Vc::new();
    /// d.push_back(1);
    /// d.push_back(2);
    ///
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        let new_tail = &mut self.new_tail;
        self.old_head
            .as_mut()
            .and_then(|v| v.pop_front())
            .or_else(|| new_tail.pop_front())
    }

    /// Removes the last element from the `Vc` and returns it, or `None` if
    /// it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// assert_eq!(buf.pop_back(), None);
    /// buf.push_back(1);
    /// buf.push_back(3);
    /// assert_eq!(buf.pop_back(), Some(3));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        let old_head = &mut self.old_head;
        self.new_tail
            .pop_back()
            .or_else(|| old_head.as_mut().and_then(|v| v.pop_back()))
    }

    /// Removes the last element from the `Vc` and returns it, or [`None`] if
    /// it is empty.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec, [1, 2]);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.pop_back()
    }

    /// Appends an element to the back of the `Vc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(1);
    /// buf.push_back(3);
    /// assert_eq!(3, *buf.back().unwrap());
    /// ```
    pub fn push_back(&mut self, value: T) {
        if self.new_tail.capacity() == self.new_tail.len() {
            debug_assert_eq!(self.old_len(), 0);
            self.grow(1 /* the value we're about to push */, false);
            return self.push_back(value);
        }

        if cfg!(debug_assertions) {
            let cap = self.new_tail.capacity();
            self.new_tail.push_back(value);

            // make sure VecDeque didn't resize
            assert_eq!(
                cap,
                self.new_tail.capacity(),
                "resize while elements are still left over"
            );
        } else {
            self.new_tail.push_back(value);
        }

        if self.old_len() != 0 {
            // Also carry some items over.
            self.carry();
        }
    }

    /// Appends an element to the back of the `Vc`.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[inline]
    pub fn push(&mut self, value: T) {
        self.push_back(value)
    }

    #[inline]
    unsafe fn old_ref(&self) -> &VecDeque<T> {
        debug_assert!(self.old_head.is_some());
        self.old_head
            .as_ref()
            .unwrap_or_else(|| core::hint::unreachable_unchecked())
    }

    #[inline]
    unsafe fn old_mut(&mut self) -> &mut VecDeque<T> {
        debug_assert!(self.old_head.is_some());
        self.old_head
            .as_mut()
            .unwrap_or_else(|| core::hint::unreachable_unchecked())
    }

    #[inline]
    fn old_len(&self) -> usize {
        self.old_head.as_ref().map_or(0, |v| v.len())
    }

    #[inline]
    #[doc(hidden)]
    #[allow(dead_code)]
    pub fn is_atoning(&self) -> bool {
        self.old_head.is_some()
    }

    /// Removes an element from anywhere in the `Vc` and returns it,
    /// replacing it with the first element.
    ///
    /// This does not preserve ordering, but is `O(1)`.
    ///
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// assert_eq!(buf.swap_remove_front(0), None);
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, vec![1, 2, 3]);
    ///
    /// assert_eq!(buf.swap_remove_front(2), Some(3));
    /// assert_eq!(buf, vec![2, 1]);
    /// ```
    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        let length = self.len();
        if length > 0 && index < length && index != 0 {
            self.swap(index, 0);
        } else if index >= length {
            return None;
        }
        self.pop_front()
    }

    /// Removes an element from anywhere in the `Vc` and returns it, replacing it with the
    /// last element.
    ///
    /// This does not preserve ordering, but is `O(1)`.
    ///
    /// Returns `None` if `index` is out of bounds.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// assert_eq!(buf.swap_remove_back(0), None);
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, vec![1, 2, 3]);
    ///
    /// assert_eq!(buf.swap_remove_back(0), Some(1));
    /// assert_eq!(buf, vec![3, 2]);
    /// ```
    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        let length = self.len();
        if length > 0 && index < length - 1 {
            self.swap(index, length - 1);
        } else if index >= length {
            return None;
        }
        self.pop_back()
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec!["foo", "bar", "baz", "qux"];
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v, ["baz", "qux"]);
    /// ```
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        self.swap_remove_back(index).expect("index out of bounds")
    }

    /// Inserts an element at `index` within the `Vc`, shifting all elements with indices
    /// greater than or equal to `index` towards the back.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than `Vc`'s length
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut vec_deque = Vc::new();
    /// vec_deque.push_back('a');
    /// vec_deque.push_back('b');
    /// vec_deque.push_back('c');
    /// assert_eq!(vec_deque, vec!['a', 'b', 'c']);
    ///
    /// vec_deque.insert(1, 'd');
    /// assert_eq!(vec_deque, vec!['a', 'd', 'b', 'c']);
    /// ```
    pub fn insert(&mut self, index: usize, value: T) {
        let do_the_thing = |this: &mut Self, value: T| {
            let old_len = this.old_len();
            if index < old_len {
                // index < old_len implies old_len > 0 and index in-bounds
                let shift = unsafe { this.old_mut() }
                    .pop_back()
                    .unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
                this.new_tail.push_front(shift);
                unsafe { this.old_mut() }.insert(index, value);
            } else {
                this.new_tail.insert(index - old_len, value);
            }
        };

        if self.old_len() != 0 {
            if cfg!(debug_assertions) {
                let cap = self.new_tail.capacity();
                do_the_thing(self, value);

                // make sure VecDeque didn't resize
                assert_eq!(
                    cap,
                    self.new_tail.capacity(),
                    "resize while elements are still left over"
                );
            } else {
                do_the_thing(self, value);
            }

            // Also carry some items over.
            self.carry();
        } else if self.new_tail.capacity() == self.new_tail.len() {
            self.grow(1 /* the value we're about to insert */, false);
            self.insert(index, value)
        } else {
            do_the_thing(self, value);
        }
    }

    /// Removes and returns the element at `index` from the `Vc`.
    /// Whichever end is closer to the removal point will be moved to make
    /// room, and all the affected elements will be moved to new positions.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(1);
    /// buf.push_back(2);
    /// buf.push_back(3);
    /// assert_eq!(buf, vec![1, 2, 3]);
    ///
    /// assert_eq!(buf.remove(1), 2);
    /// assert_eq!(buf, vec![1, 3]);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("removal index (is {}) should be < len (is {})", index, len);
        }

        let old_len = self.old_len();
        if index < old_len {
            // index < old_len implies old_len > 0 and index in-bounds
            unsafe {
                let v = self.old_mut().remove(index);
                if self.old_ref().is_empty() {
                    let _ = self.take_old_unchecked();
                }
                v.unwrap_or_else(|| assert_failed(index, self.len()))
            }
        } else {
            self.new_tail
                .remove(index - old_len)
                .unwrap_or_else(|| assert_failed(index, self.len()))
        }
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new number of elements in self overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf: Vc<_> = vec![1, 2].into_iter().collect();
    /// let mut buf2: Vc<_> = vec![3, 4].into_iter().collect();
    /// buf.append(&mut buf2);
    /// assert_eq!(buf, vec![1, 2, 3, 4]);
    /// assert_eq!(buf2, vec![]);
    /// ```
    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        self.reserve(other.len());
        while let Some(e) = other.pop_front() {
            self.push_back(e);
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.extend(1..5);
    /// buf.retain(|&x| x % 2 == 0);
    /// assert_eq!(buf, vec![2, 4]);
    /// ```
    ///
    /// The exact order may be useful for tracking external state, like an index.
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.extend(1..6);
    ///
    /// let keep = [false, true, true, false, true];
    /// let mut i = 0;
    /// buf.retain(|_| (keep[i], i += 1).0);
    /// assert_eq!(buf, vec![2, 3, 5]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        if let Some(ref mut v) = self.old_head {
            v.retain(&mut f);
        }
        self.new_tail.retain(&mut f);
    }

    fn take_old(&mut self) -> Option<VecDeque<T>> {
        self.old_head.take()
    }

    unsafe fn take_old_unchecked(&mut self) -> VecDeque<T> {
        self.old_head
            .take()
            .unwrap_or_else(|| core::hint::unreachable_unchecked())
    }

    // This may panic or abort
    #[inline(never)]
    fn grow(&mut self, extra: usize, exact: bool) {
        debug_assert_eq!(self.old_len(), 0);

        // We need to grow the Vec by at least a factor of (R + 1)/R to ensure that
        // the new Vec won't _also_ grow while we're still moving items from the old
        // one.
        //
        // Here's how we get to len * (R + 1)/R:
        //  - We need to move another len items
        let need = self.new_tail.len();
        //  - We move R items on each push, so to move len items takes
        //    len / R pushes (rounded up!)
        //  - Since we want to round up, we pull the old +R-1 trick
        let pushes = (self.new_tail.len() + R - 1) / R;
        //  - That's len + len/R
        //    Which is == R*len/R + len/R
        //    Which is == ((R+1)*len)/R
        //    Which is == len * (R+1)/R
        //  - We don't actually use that formula because of integer division.
        //
        // We also need to make sure we can fit the additional capacity required for `extra`.
        // Normally, that'll be handled by `pushes`, but not always!
        let add = usize::max(extra, pushes);
        let new_tail = if exact {
            let mut v = VecDeque::with_capacity(0);
            v.reserve_exact(need + pushes + add);
            v
        } else {
            VecDeque::with_capacity(need + pushes + add)
        };
        self.old_head = Some(mem::replace(&mut self.new_tail, new_tail));
    }

    /// Modifies the `Vc` in-place so that `len()` is equal to `new_len`,
    /// either by removing excess elements from the back or by appending
    /// elements generated by calling `generator` to the back.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, vec![5, 10, 15]);
    ///
    /// buf.resize_with(5, Default::default);
    /// assert_eq!(buf, vec![5, 10, 15, 0, 0]);
    ///
    /// buf.resize_with(2, || unreachable!());
    /// assert_eq!(buf, vec![5, 10]);
    ///
    /// let mut state = 100;
    /// buf.resize_with(5, || { state += 1; state });
    /// assert_eq!(buf, vec![5, 10, 101, 102, 103]);
    /// ```
    pub fn resize_with(&mut self, new_len: usize, generator: impl FnMut() -> T) {
        let len = self.len();

        if new_len > len {
            self.extend(repeat_with(generator).take(new_len - len))
        } else {
            self.truncate(new_len);
        }
    }

    /// Rearranges the internal storage so that all elements are in one contiguous slice,
    /// which is then returned.
    ///
    /// This method does not allocate and does not change the order of the inserted elements.
    /// As it returns a mutable slice, this can be used to sort or binary search a deque.
    ///
    /// This method will also move over leftover items from the last resize, if any.
    ///
    /// This method is only available on nightly compilers at the moment.
    ///
    /// # Examples
    ///
    /// Sorting the content of a deque.
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::with_capacity(3);
    /// for i in 1..=16 {
    ///     buf.push(16 - i);
    /// }
    ///
    /// // The backing memory of buf is now split,
    /// // since some items are left over after the resize.
    /// // To sort the list, we make it contiguous, and then sort.
    /// buf.make_contiguous().sort();
    /// assert_eq!(buf, (0..16).collect::<Vec<_>>());
    ///
    /// // Similarly, we can sort it in reverse order.
    /// buf.make_contiguous().sort_by(|a, b| b.cmp(a));
    /// assert_eq!(buf, (1..=16).map(|i| 16 - i).collect::<Vec<_>>());
    /// ```
    ///
    /// Getting immutable access to the contiguous slice.
    ///
    /// ```rust
    /// use atone::Vc;
    /// let mut buf = Vc::new();
    /// for i in 1..=3 {
    ///     buf.push(i);
    /// }
    ///
    /// buf.make_contiguous();
    /// if let Some(slice) = buf.as_single_slice() {
    ///     // we can now be sure that `slice` contains all elements of the deque,
    ///     // while still having immutable access to `buf`.
    ///     assert_eq!(buf.len(), slice.len());
    ///     assert_eq!(slice, &[1, 2, 3] as &[_]);
    /// }
    /// ```
    #[cfg(is_nightly)]
    pub fn make_contiguous(&mut self) -> &mut [T] {
        if self.old_len() != 0 {
            self.carry_all();
        }
        self.new_tail.make_contiguous()
    }
}

impl<T: Clone> Vc<T> {
    /// Modifies the `Vc` in-place so that `len()` is equal to new_len,
    /// either by removing excess elements from the back or by appending clones of `value`
    /// to the back.
    ///
    /// # Examples
    ///
    /// ```
    /// use atone::Vc;
    ///
    /// let mut buf = Vc::new();
    /// buf.push_back(5);
    /// buf.push_back(10);
    /// buf.push_back(15);
    /// assert_eq!(buf, vec![5, 10, 15]);
    ///
    /// buf.resize(2, 0);
    /// assert_eq!(buf, vec![5, 10]);
    ///
    /// buf.resize(5, 20);
    /// assert_eq!(buf, vec![5, 10, 20, 20, 20]);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T) {
        self.resize_with(new_len, || value.clone());
    }
}

impl<A: PartialEq> PartialEq for Vc<A> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        match (self.old_len(), other.old_len()) {
            (0, 0) => self.new_tail == other.new_tail,
            (self_old_len, other_old_len) => {
                if self_old_len == other_old_len {
                    return self.old_head == other.old_head && self.new_tail == other.new_tail;
                }

                // TODO: optimize
                self.old_head
                    .iter()
                    .flatten()
                    .chain(self.new_tail.iter())
                    .eq(other.old_head.iter().flatten().chain(other.new_tail.iter()))
            }
        }
    }
}

impl<A: Eq> Eq for Vc<A> {}

macro_rules! __impl_slice_eq1 {
    ($lhs:ty, $rhs:ty, $($constraints:tt)*) => {
        impl<A, B> PartialEq<$rhs> for $lhs
        where
            A: PartialEq<B>,
            $($constraints)*
        {
            fn eq(&self, other: &$rhs) -> bool {
                    self.old_head
                        .iter()
                        .flatten()
                        .chain(self.new_tail.iter())
                        .eq(other.iter())
            }
        }
    }
}

__impl_slice_eq1! { Vc<A>, Vec<B>, }
__impl_slice_eq1! { Vc<A>, &[B], }
__impl_slice_eq1! { Vc<A>, &mut [B], }

// For symmetry:

macro_rules! __impl_slice_eq2 {
    ($lhs:ty, $rhs:ty, $($constraints:tt)*) => {
        impl<A, B> PartialEq<$lhs> for $rhs
        where
            A: PartialEq<B>,
            $($constraints)*
        {
            fn eq(&self, other: &$lhs) -> bool {
                    other.old_head
                        .iter()
                        .flatten()
                        .chain(other.new_tail.iter())
                        .eq(self.iter())
            }
        }
    }
}

__impl_slice_eq2! { Vc<A>, Vec<B>, }
__impl_slice_eq2! { Vc<A>, &[B], }
__impl_slice_eq2! { Vc<A>, &mut [B], }

impl<A: PartialOrd> PartialOrd for Vc<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.old_len(), other.old_len()) {
            (0, 0) => self.new_tail.partial_cmp(&other.new_tail),
            (self_old_len, other_old_len) => {
                if self_old_len == other_old_len {
                    return self.old_head.partial_cmp(&other.old_head).and_then(|o| {
                        if let Ordering::Equal = o {
                            self.new_tail.partial_cmp(&other.new_tail)
                        } else {
                            Some(o)
                        }
                    });
                }

                // TODO: optimize
                self.old_head
                    .iter()
                    .flatten()
                    .chain(self.new_tail.iter())
                    .partial_cmp(other.old_head.iter().flatten().chain(other.new_tail.iter()))
            }
        }
    }
}

impl<A: Ord> Ord for Vc<A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.old_len(), other.old_len()) {
            (0, 0) => self.new_tail.cmp(&other.new_tail),
            (self_old_len, other_old_len) => {
                if self_old_len == other_old_len {
                    return self
                        .old_head
                        .cmp(&other.old_head)
                        .then_with(|| self.new_tail.cmp(&other.new_tail));
                }

                // TODO: optimize
                self.old_head
                    .iter()
                    .flatten()
                    .chain(self.new_tail.iter())
                    .cmp(other.old_head.iter().flatten().chain(other.new_tail.iter()))
            }
        }
    }
}

impl<A: Hash> Hash for Vc<A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);

        // NOTE: this _seems_ wrong, since it would make Vcs hash differently depending on whether
        // the _same_ elements were in old_head or new_tail. But it's what VecDeque does, so..?
        self.old_head.hash(state);
        self.new_tail.hash(state);
    }
}

impl<A> Index<usize> for Vc<A> {
    type Output = A;

    #[inline]
    fn index(&self, index: usize) -> &A {
        self.get(index).expect("Out of bounds access")
    }
}

impl<A> IndexMut<usize> for Vc<A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut A {
        self.get_mut(index).expect("Out of bounds access")
    }
}

impl<A> FromIterator<A> for Vc<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let iterator = iter.into_iter();
        let (lower, _) = iterator.size_hint();
        let mut deq = Self::with_capacity(lower);
        deq.extend(iterator);
        deq
    }
}

impl<T> IntoIterator for Vc<T> {
    type Item = T;
    type IntoIter = iter::IntoIter<T>;

    fn into_iter(self) -> iter::IntoIter<T> {
        iter::IntoIter {
            head: self.old_head.map(|v| v.into_iter()),
            tail: self.new_tail.into_iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a Vc<T> {
    type Item = &'a T;
    type IntoIter = iter::Iter<'a, T>;

    fn into_iter(self) -> iter::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Vc<T> {
    type Item = &'a mut T;
    type IntoIter = iter::IterMut<'a, T>;

    fn into_iter(self) -> iter::IterMut<'a, T> {
        self.iter_mut()
    }
}
impl<A> Extend<A> for Vc<A> {
    fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T) {
        // Reserve the entire hint lower bound if the Vc is empty.
        // Otherwise reserve half the hint (rounded up), so the Vc
        // will only resize twice in the worst case.
        let iter = iter.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        iter.for_each(move |v| {
            // TODO: optimize bounds checking
            self.push_back(v);
        });
    }
}

impl<'a, T: 'a + Copy> Extend<&'a T> for Vc<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

impl<T: fmt::Debug> fmt::Debug for Vc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T> From<Vec<T>> for Vc<T> {
    fn from(other: Vec<T>) -> Self {
        Self::from(VecDeque::from(other))
    }
}

impl<T> From<VecDeque<T>> for Vc<T> {
    fn from(other: VecDeque<T>) -> Self {
        Self {
            new_tail: other,
            old_head: None,
        }
    }
}

impl<T> From<Vc<T>> for Vec<T> {
    fn from(other: Vc<T>) -> Self {
        VecDeque::from(other).into()
    }
}

impl<T> From<Vc<T>> for VecDeque<T> {
    fn from(mut other: Vc<T>) -> Self {
        if other.old_len() != 0 {
            other.carry_all();
        }
        other.new_tail
    }
}

////////////////////////////////////////////////////////////////////////////////
// Amortization methods
////////////////////////////////////////////////////////////////////////////////

impl<T> Vc<T> {
    #[cold]
    #[inline(never)]
    pub(crate) fn carry_all(&mut self) {
        debug_assert_ne!(self.old_len(), 0);
        while let Some(e) = unsafe { self.old_mut() }.pop_back() {
            self.new_tail.push_front(e);
        }
        // The resize is finally fully complete.
        self.old_head = None;
    }

    #[cold]
    #[inline(never)]
    pub(crate) fn carry(&mut self) {
        if !unsafe { self.old_ref() }.is_empty() {
            for _ in 0..R {
                if let Some(e) = unsafe { self.old_mut() }.pop_back() {
                    self.new_tail.push_front(e);
                } else {
                    // The resize is finally fully complete.
                    self.old_head = None;
                    return;
                }
            }

            if unsafe { self.old_ref() }.is_empty() {
                // The resize is finally fully complete.
                self.old_head = None;
            }
        }
    }
}

#[cfg(test)]
#[cfg(not(tarpaulin_include))] // don't count for coverage
mod tests {
    use super::Vc;
    use std::cell::RefCell;
    use std::collections::VecDeque;
    use std::usize;
    use std::vec::Vec;

    #[test]
    fn test_zero_capacities() {
        assert_eq!(VecDeque::<i32>::with_capacity(0).capacity(), 1);
        assert_eq!(Vc::<i32>::with_capacity(0).capacity(), 1);
    }

    #[test]
    fn test_create_capacity_zero() {
        let mut m = Vc::with_capacity(0);

        m.push(1);
        m.push(2);

        assert_eq!(m.front(), Some(&1));
        assert_eq!(m.back(), Some(&2));
        assert!(m.contains(&1));
        assert!(m.contains(&2));
        assert!(!m.contains(&0));
    }

    #[test]
    fn test_push() {
        let mut m = Vc::new();
        assert_eq!(m.len(), 0);
        m.push(1);
        assert_eq!(m.len(), 1);
        m.push(2);
        assert_eq!(m.len(), 2);
        assert_eq!(*m.front().unwrap(), 1);
        assert_eq!(*m.back().unwrap(), 2);
    }

    #[test]
    fn test_split_push() {
        // the code below assumes that R is 4
        assert_eq!(crate::R, 4);

        let mut m = Vc::with_capacity(3);
        assert_eq!(m.capacity(), 3);
        assert_eq!(m.len(), 0);
        // three pushes won't split
        for i in 1..=3 {
            m.push(i);
            assert!(m.contains(&i));
            assert_eq!(m.capacity(), 3);
        }
        assert!(m.iter().copied().eq(1..=3));
        // fourth push will split and migrate all elements
        assert!(!m.is_atoning());
        m.push(4);
        // capacity should now be doubled
        assert_eq!(m.capacity(), 7);
        // and there should be no leftovers
        assert!(!m.is_atoning());
        assert_eq!(m.old_head, None);
        assert_eq!(m.new_tail.len(), 4);
        for i in 1..=4 {
            assert!(m.contains(&i));
        }
        assert!(m.iter().copied().eq(1..=4));

        // move to next split point
        for i in 5..=7 {
            m.push(i);
            assert!(m.contains(&i));
            assert_eq!(m.capacity(), 7);
        }
        assert!(m.iter().copied().eq(1..=7));

        // next push will split, and move some, but not all (since R < old.len())
        m.push(8);
        // capacity should now be doubled
        assert_eq!(m.capacity(), 15);
        // and there should be leftovers
        assert!(m.is_atoning());
        assert_eq!(m.new_tail.len(), 1 + crate::R);
        assert_eq!(m.old_len(), 8 - (1 + crate::R));
        for i in 1..=8 {
            assert!(m.contains(&i));
        }
        // check that the iterators do the right thing when split:
        assert_eq!(m.iter().count(), 8);
        for i in 1..=8 {
            assert!(m.iter().any(|&e| e == i));
        }
        assert_eq!(m.iter_mut().count(), 8);
        for i in 1..=8 {
            assert!(m.iter_mut().any(|&mut e| e == i));
        }

        // if we do another push, it will move the rest of the items from old_head
        m.push(9);
        assert!(!m.is_atoning());
        assert_eq!(m.new_tail.len(), 9);
        assert_eq!(m.old_head, None);
        // it should not have changed capacity
        assert_eq!(m.capacity(), 15);
        for i in 1..=9 {
            assert!(m.contains(&i));
        }
        assert!(m.iter().copied().eq(1..=9));
    }

    #[test]
    fn test_clone() {
        let mut m = Vc::new();
        for i in 1..=8 {
            assert_eq!(m.len(), i - 1);
            m.push(i);
        }
        assert_eq!(m.len(), 8);
        let m2 = m.clone();
        assert!(m2.iter().copied().eq(1..=8));
    }

    #[test]
    fn test_clone_from() {
        let mut m = Vc::new();
        let mut m2 = Vc::new();
        for i in 1..=8 {
            assert_eq!(m.len(), i - 1);
            m.push(i);
        }
        assert_eq!(m.len(), 8);
        m2.clone_from(&m);
        assert!(m2.iter().copied().eq(1..=8));
    }

    thread_local! { static DROP_VECTOR: RefCell<Vec<i32>> = RefCell::new(Vec::new()) }

    #[derive(Hash, PartialEq, Eq)]
    struct Droppable {
        k: usize,
    }

    impl Droppable {
        fn new(k: usize) -> Droppable {
            DROP_VECTOR.with(|slot| {
                slot.borrow_mut()[k] += 1;
            });

            Droppable { k }
        }
    }

    impl Drop for Droppable {
        fn drop(&mut self) {
            DROP_VECTOR.with(|slot| {
                slot.borrow_mut()[self.k] -= 1;
            });
        }
    }

    impl Clone for Droppable {
        fn clone(&self) -> Self {
            Droppable::new(self.k)
        }
    }

    #[test]
    fn test_drops() {
        DROP_VECTOR.with(|slot| {
            *slot.borrow_mut() = vec![0; 100];
        });

        {
            let mut vs = Vc::new();

            DROP_VECTOR.with(|v| {
                for i in 0..100 {
                    assert_eq!(v.borrow()[i], 0);
                }
            });

            for i in 0..100 {
                let d = Droppable::new(i);
                vs.push(d);
            }

            DROP_VECTOR.with(|v| {
                for i in 0..100 {
                    assert_eq!(v.borrow()[i], 1);
                }
            });

            for i in 0..50 {
                let v = vs.remove(0);

                assert_eq!(v.k, i);

                DROP_VECTOR.with(|v| {
                    assert_eq!(v.borrow()[i], 1);
                });
            }

            DROP_VECTOR.with(|v| {
                for i in 0..50 {
                    assert_eq!(v.borrow()[i], 0);
                }

                for i in 50..100 {
                    assert_eq!(v.borrow()[i], 1);
                }
            });
        }

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 0);
            }
        });
    }

    #[test]
    fn test_into_iter_drops() {
        DROP_VECTOR.with(|v| {
            *v.borrow_mut() = vec![0; 100];
        });

        let vs = {
            let mut vs = Vc::new();

            DROP_VECTOR.with(|v| {
                for i in 0..100 {
                    assert_eq!(v.borrow()[i], 0);
                }
            });

            for i in 0..100 {
                let d = Droppable::new(i);
                vs.push(d);
            }

            DROP_VECTOR.with(|v| {
                for i in 0..100 {
                    assert_eq!(v.borrow()[i], 1);
                }
            });

            vs
        };

        // By the way, ensure that cloning doesn't screw up the dropping.
        drop(vs.clone());

        {
            let mut half = vs.into_iter().take(50);

            DROP_VECTOR.with(|v| {
                for i in 0..100 {
                    assert_eq!(v.borrow()[i], 1);
                }
            });

            for _ in half.by_ref() {}

            DROP_VECTOR.with(|v| {
                let n = (0..100).filter(|&i| v.borrow()[i] == 1).count();

                assert_eq!(n, 50);
            });
        };

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 0);
            }
        });
    }

    #[test]
    #[should_panic]
    fn test_empty_remove() {
        let mut vs: Vc<i32> = Vc::new();
        vs.remove(0);
    }

    #[test]
    fn test_empty_iter() {
        let mut vs: Vc<i32> = Vc::new();
        assert_eq!(vs.drain(..).next(), None);
        assert_eq!(vs.iter().next(), None);
        assert_eq!(vs.iter_mut().next(), None);
        assert_eq!(vs.len(), 0);
        assert!(vs.is_empty());
        assert_eq!(vs.into_iter().next(), None);
    }

    #[test]
    #[should_panic]
    fn test_empty_swap_remove() {
        let mut vs: Vc<i32> = Vc::new();
        vs.swap_remove(0);
    }

    #[test]
    fn test_lots_of_pushes() {
        let mut vs = Vc::new();

        #[cfg(not(any(tarpaulin, miri)))]
        const M: usize = 101;
        #[cfg(tarpaulin)]
        const M: usize = 33;
        #[cfg(miri)]
        const M: usize = 17;

        for i in 1..M {
            vs.push(i);

            for j in 1..=i {
                let r = vs.get(j - 1);
                assert_eq!(r, Some(&j));
            }

            for j in i + 1..M {
                let r = vs.get(j - 1);
                assert_eq!(r, None);
            }
        }

        for i in M..(M * 2 - 1) {
            assert!(!vs.contains(&i));
        }

        // remove forwards
        for i in 1..M {
            assert_eq!(vs.remove(0), i);

            for j in 1..=i {
                assert!(!vs.contains(&j));
            }

            for j in i + 1..M {
                assert!(vs.contains(&j));
            }
        }

        for i in 1..M {
            assert!(!vs.contains(&i));
        }

        for i in 1..M {
            vs.push(i);
        }

        // remove backwards
        for i in (1..M).rev() {
            assert_eq!(vs.pop(), Some(i));

            for j in i..M {
                assert!(!vs.contains(&j));
            }

            for j in 1..i {
                assert!(vs.contains(&j));
            }
        }
        assert!(vs.is_empty());
    }

    #[test]
    fn test_is_empty() {
        let mut vs = Vc::with_capacity(4);
        vs.push(1);
        assert!(!vs.is_empty());
        vs.remove(0);
        assert!(vs.is_empty());
    }

    #[test]
    fn test_iterate() {
        let mut vs = Vc::with_capacity(4);
        for i in 0..32 {
            vs.push(i * 2);
        }
        assert!(vs.is_atoning());
        assert_eq!(vs.len(), 32);

        assert!(vs.iter().copied().eq((0..32).map(|v| v * 2)));
    }

    #[test]
    fn test_eq() {
        let mut vs1 = Vc::new();
        for v in (1..).take(8) {
            vs1.push(v);
        }

        let mut vs2 = Vc::new();
        for v in (1..).take(7) {
            vs2.push(v);
        }

        assert!(vs1 != vs2);

        vs2.push(8);

        assert_eq!(vs1, vs2);
    }

    #[test]
    fn test_show() {
        let mut vs = Vc::new();
        let empty: Vc<i32> = Vc::new();

        vs.push(1);
        vs.push(2);

        assert_eq!(format!("{:?}", vs), "[1, 2]");
        assert_eq!(format!("{:?}", empty), "[]");
    }

    #[test]
    fn test_from_iter() {
        let xs = 0..8;

        let vs: Vc<_> = xs.clone().collect();
        assert!(vs.iter().copied().eq(xs));
    }

    #[test]
    fn test_size_hint() {
        let xs = 0..8;

        let vs: Vc<_> = xs.clone().collect();

        let mut iter = vs.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (8 - 3, Some(8 - 3)));
    }

    #[test]
    fn test_iter_len() {
        let xs = 0..8;

        let vs: Vc<_> = xs.clone().collect();

        let mut iter = vs.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.len(), 8 - 3);
    }

    #[test]
    fn test_mut_size_hint() {
        let xs = 0..8;

        let mut vs: Vc<_> = xs.clone().collect();

        let mut iter = vs.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (8 - 3, Some(8 - 3)));
    }

    #[test]
    fn test_iter_mut_len() {
        let xs = 0..8;

        let mut vs: Vc<_> = xs.clone().collect();

        let mut iter = vs.iter_mut();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.len(), 8 - 3);
    }

    #[test]
    fn test_index() {
        let mut vs = Vc::new();

        for i in 1..=8 {
            vs.push(i);
        }
        assert!(vs.is_atoning());

        assert_eq!(vs[2 - 1], 2);
    }

    #[test]
    #[should_panic]
    fn test_index_nonexistent() {
        let mut vs = Vc::new();

        for i in 1..=8 {
            vs.push(i);
        }
        assert!(vs.is_atoning());

        vs[9];
    }

    #[test]
    fn test_extend_ref() {
        let mut a = Vc::new();
        a.push("one");
        let mut b = Vc::new();
        b.push("two");
        b.push("three");

        a.extend(&b);

        assert_eq!(a.len(), 3);
        assert_eq!(a[0], "one");
        assert_eq!(a[1], "two");
        assert_eq!(a[2], "three");
    }

    #[test]
    fn test_capacity_not_less_than_len() {
        let mut a = Vc::new();
        let mut item = 0;

        for _ in 0..116 {
            a.push(item);
            item += 1;
        }

        assert!(a.capacity() > a.len());

        let free = a.capacity() - a.len();
        for _ in 0..free {
            a.push(item);
            item += 1;
        }

        assert_eq!(a.len(), a.capacity());

        // Insert at capacity should cause allocation.
        a.insert(item, 0);
        assert!(a.capacity() > a.len());
    }

    #[test]
    fn test_retain() {
        let mut vs: Vc<i32> = Vc::new();
        for x in 0..130 {
            vs.push(x);
        }
        assert!(vs.is_atoning());

        vs.retain(|&e| e % 2 == 0);
        assert_eq!(vs.len(), 65);
        assert_eq!(vs[2], 4);
        assert_eq!(vs[4], 8);
        assert_eq!(vs[6], 12);
    }
}

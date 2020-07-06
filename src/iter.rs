use core::iter::FusedIterator;

use alloc::collections::vec_deque;

fn size_hint(
    head: Option<(usize, Option<usize>)>,
    tail: (usize, Option<usize>),
) -> (usize, Option<usize>) {
    debug_assert_ne!(tail.1, None);
    if let Some(head) = head {
        debug_assert_ne!(head.1, None);
        let (lo1, hi1) = head;
        let (lo2, hi2) = tail;

        // all vec_deque iterators are ExactSizeIterator
        let hi1 = hi1.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
        let hi2 = hi2.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });

        (lo1 + lo2, Some(hi1 + hi2))
    } else {
        tail
    }
}

/// An iterator over the elements of a `Vc`.
///
/// This `struct` is created by the [`iter`] method on [`Vc`]. See its
/// documentation for more.
///
/// [`iter`]: struct.Vc.html#method.iter
/// [`Vc`]: struct.Vc.html
#[derive(Debug)]
pub struct Iter<'a, T> {
    pub(super) head: Option<vec_deque::Iter<'a, T>>,
    pub(super) tail: vec_deque::Iter<'a, T>,
}

impl<'a, T> Clone for Iter<'a, T> {
    fn clone(&self) -> Self {
        Self {
            head: self.head.clone(),
            tail: self.tail.clone(),
        }
    }
}

macro_rules! _impl {
    (fw) => {
        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let tail = &mut self.tail;
            self.head
                .as_mut()
                .and_then(|it| it.next())
                .or_else(|| tail.next())
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            size_hint(
                self.head.as_ref().map(|it| it.size_hint()),
                self.tail.size_hint(),
            )
        }

        fn fold<Acc, F>(self, accum: Acc, mut f: F) -> Acc
        where
            F: FnMut(Acc, Self::Item) -> Acc,
        {
            if let Some(head) = self.head {
                self.tail.fold(head.fold(accum, &mut f), f)
            } else {
                self.tail.fold(accum, f)
            }
        }

        fn nth(&mut self, n: usize) -> Option<Self::Item> {
            if let Some(ref mut head) = self.head {
                let head_ln = head.len();
                if let Some(e) = head.nth(n) {
                    Some(e)
                } else {
                    self.tail.nth(n - head_ln)
                }
            } else {
                self.tail.nth(n)
            }
        }

        #[inline]
        fn last(mut self) -> Option<Self::Item> {
            self.next_back()
        }
    };

    (bw) => {
        #[inline]
        fn next_back(&mut self) -> Option<Self::Item> {
            if let Some(ref mut head) = self.head {
                if let Some(e) = self.tail.next_back() {
                    Some(e)
                } else if let Some(e) = head.next_back() {
                    Some(e)
                } else {
                    let _ = self.head.take();
                    None
                }
            } else {
                self.tail.next_back()
            }
        }

        fn rfold<Acc, F>(self, accum: Acc, mut f: F) -> Acc
        where
            F: FnMut(Acc, Self::Item) -> Acc,
        {
            if let Some(head) = self.head {
                head.rfold(self.tail.rfold(accum, &mut f), f)
            } else {
                self.tail.rfold(accum, f)
            }
        }
    };
}

impl<'a, T> Iterator for Iter<'a, T>
where
    vec_deque::Iter<'a, T>: Iterator<Item = &'a T> + FusedIterator + ExactSizeIterator,
{
    type Item = &'a T;

    _impl!(fw);
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    _impl!(bw);
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> where
    vec_deque::Iter<'a, T>: ExactSizeIterator<Item = &'a T>
{
}

impl<T> FusedIterator for Iter<'_, T> {}

/// A mutable iterator over the elements of a `Vc`.
///
/// This `struct` is created by the [`iter_mut`] method on [`Vc`]. See its
/// documentation for more.
///
/// [`iter_mut`]: struct.Vc.html#method.iter_mut
/// [`Vc`]: struct.Vc.html
#[derive(Debug)]
pub struct IterMut<'a, T> {
    pub(super) head: Option<vec_deque::IterMut<'a, T>>,
    pub(super) tail: vec_deque::IterMut<'a, T>,
}

impl<'a, T> Iterator for IterMut<'a, T>
where
    vec_deque::IterMut<'a, T>: Iterator<Item = &'a mut T> + FusedIterator + ExactSizeIterator,
{
    type Item = &'a mut T;

    _impl!(fw);
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    _impl!(bw);
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> where
    vec_deque::IterMut<'a, T>: ExactSizeIterator<Item = &'a mut T>
{
}

impl<T> FusedIterator for IterMut<'_, T> {}

/// An owning iterator over the elements of a `Vc`.
///
/// This `struct` is created by the [`into_iter`] method on [`Vc`]
/// (provided by the `IntoIterator` trait). See its documentation for more.
///
/// [`into_iter`]: struct.Vc.html#method.into_iter
/// [`Vc`]: struct.Vc.html
#[derive(Clone, Debug)]
pub struct IntoIter<T> {
    pub(super) head: Option<vec_deque::IntoIter<T>>,
    pub(super) tail: vec_deque::IntoIter<T>,
}

impl<T> Iterator for IntoIter<T>
where
    vec_deque::IntoIter<T>: Iterator<Item = T> + FusedIterator + ExactSizeIterator,
{
    type Item = T;

    _impl!(fw);
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    _impl!(bw);
}

impl<T> ExactSizeIterator for IntoIter<T> where vec_deque::IntoIter<T>: ExactSizeIterator<Item = T> {}

impl<T> FusedIterator for IntoIter<T> {}

/// A draining iterator over the elements of a `Vc`.
///
/// This `struct` is created by the [`drain`] method on [`Vc`]. See its
/// documentation for more.
///
/// [`drain`]: struct.Vc.html#method.drain
/// [`Vc`]: struct.Vc.html
#[derive(Debug)]
pub struct Drain<'a, T> {
    pub(super) head: Option<vec_deque::Drain<'a, T>>,
    pub(super) tail: vec_deque::Drain<'a, T>,
}

impl<'a, T> Iterator for Drain<'a, T>
where
    vec_deque::Drain<'a, T>: Iterator<Item = T> + FusedIterator + ExactSizeIterator,
{
    type Item = T;

    _impl!(fw);
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    _impl!(bw);
}

impl<'a, T> ExactSizeIterator for Drain<'a, T> where
    vec_deque::Drain<'a, T>: ExactSizeIterator<Item = T>
{
}

impl<'a, T> FusedIterator for Drain<'a, T> {}

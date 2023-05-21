//! This module contains the parallel iterator types for double `Vc<T>`.
//! You will rarely need to interact with it directly
//! unless you have need to name one of the iterator types.

use crate::Vc;

use alloc::collections::LinkedList;
use rayon_::collections::vec_deque;
use rayon_::iter::plumbing::*;
use rayon_::iter::*;

// NOTE: the following macros are lifted from
// https://github.com/rayon-rs/rayon/blob/44b641e7a8b664c47c35109195441a1e54f1c1b9/src/delegate.rs

/// Creates a parallel iterator implementation which simply wraps an inner type
/// and delegates all methods inward.  The actual struct must already be
/// declared with an `inner` field.
///
/// The implementation of `IntoParallelIterator` should be added separately.
macro_rules! delegate_iterator {
    ($iter:ty => $item:ty ,
     impl $( $args:tt )*
     ) => {
        impl $( $args )* ParallelIterator for $iter {
            type Item = $item;

            fn drive_unindexed<C>(self, consumer: C) -> C::Result
                where C: UnindexedConsumer<Self::Item>
            {
                self.inner.drive_unindexed(consumer)
            }

            fn opt_len(&self) -> Option<usize> {
                self.inner.opt_len()
            }
        }
    }
}

/// Creates an indexed parallel iterator implementation which simply wraps an
/// inner type and delegates all methods inward.  The actual struct must already
/// be declared with an `inner` field.
macro_rules! delegate_indexed_iterator {
    ($iter:ty => $item:ty ,
     impl $( $args:tt )*
     ) => {
        delegate_iterator!{
            $iter => $item ,
            impl $( $args )*
        }

        impl $( $args )* IndexedParallelIterator for $iter {
            fn drive<C>(self, consumer: C) -> C::Result
                where C: Consumer<Self::Item>
            {
                self.inner.drive(consumer)
            }

            fn len(&self) -> usize {
                self.inner.len()
            }

            fn with_producer<CB>(self, callback: CB) -> CB::Output
                where CB: ProducerCallback<Self::Item>
            {
                self.inner.with_producer(callback)
            }
        }
    }
}

/// Parallel iterator over a `Vc`
#[derive(Debug, Clone)]
pub struct IntoIter<T: Send> {
    inner: Chain<Maybe<vec_deque::IntoIter<T>>, vec_deque::IntoIter<T>>,
}

impl<T: Send> IntoParallelIterator for Vc<T> {
    type Item = T;
    type Iter = IntoIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter {
            inner: Maybe(self.old_head.map(|h| h.into_par_iter()))
                .chain(self.new_tail.into_par_iter()),
        }
    }
}

delegate_indexed_iterator! {
    IntoIter<T> => T,
    impl<T: Send>
}

/// Parallel iterator over an immutable reference to a `Vc`
#[derive(Debug)]
pub struct Iter<'a, T: Sync> {
    inner: Chain<Maybe<vec_deque::Iter<'a, T>>, vec_deque::Iter<'a, T>>,
}

impl<'a, T: Sync> Clone for Iter<'a, T> {
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, T: Sync> IntoParallelIterator for &'a Vc<T> {
    type Item = &'a T;
    type Iter = Iter<'a, T>;

    fn into_par_iter(self) -> Self::Iter {
        Iter {
            inner: Maybe(self.old_head.as_ref().map(|h| h.into_par_iter()))
                .chain((&self.new_tail).into_par_iter()),
        }
    }
}

delegate_indexed_iterator! {
    Iter<'a, T> => &'a T,
    impl<'a, T: Sync + 'a>
}

/// Parallel iterator over a mutable reference to a double-ended queue
#[derive(Debug)]
pub struct IterMut<'a, T: Send> {
    inner: Chain<Maybe<vec_deque::IterMut<'a, T>>, vec_deque::IterMut<'a, T>>,
}

impl<'a, T: Send> IntoParallelIterator for &'a mut Vc<T> {
    type Item = &'a mut T;
    type Iter = IterMut<'a, T>;

    fn into_par_iter(self) -> Self::Iter {
        IterMut {
            inner: Maybe(self.old_head.as_mut().map(|h| h.into_par_iter()))
                .chain((&mut self.new_tail).into_par_iter()),
        }
    }
}

delegate_indexed_iterator! {
    IterMut<'a, T> => &'a mut T,
    impl<'a, T: Send + 'a>
}

impl<T> FromParallelIterator<T> for Vc<T>
where
    T: Send,
{
    fn from_par_iter<I>(par_iter: I) -> Self
    where
        I: IntoParallelIterator<Item = T>,
    {
        alloc::vec::Vec::from_par_iter(par_iter).into()
    }
}

// The ParallelExtend impl is basically
// https://github.com/rayon-rs/rayon/blob/f0d2e708216edae7386e5343a27efc3948ee9001/src/iter/extend.rs

impl<T> ParallelExtend<T> for Vc<T>
where
    T: Send,
{
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = T>,
    {
        let list = par_iter
            .into_par_iter()
            .fold(alloc::vec::Vec::new, |mut v, i| {
                v.push(i);
                v
            })
            .map(|item| {
                let mut list = LinkedList::new();
                list.push_back(item);
                list
            })
            .reduce(LinkedList::new, |mut list1, mut list2| {
                list1.append(&mut list2);
                list1
            });
        self.reserve(list.iter().map(alloc::vec::Vec::len).sum());
        for vec in list {
            self.extend(vec);
        }
    }
}

impl<'a, T> ParallelExtend<&'a T> for Vc<T>
where
    T: 'a + Copy + Send + Sync,
{
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = &'a T>,
    {
        self.par_extend(par_iter.into_par_iter().copied())
    }
}

#[derive(Debug, Clone)]
struct Maybe<T>(Option<T>);

impl<T: Send> ParallelIterator for Maybe<T>
where
    T: IndexedParallelIterator,
{
    type Item = <T as ParallelIterator>::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.drive(consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.len())
    }
}

impl<T: Send> IndexedParallelIterator for Maybe<T>
where
    T: IndexedParallelIterator,
{
    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        if let Some(iter) = self.0 {
            iter.drive(consumer)
        } else {
            consumer.into_folder().complete()
        }
    }

    fn len(&self) -> usize {
        match self.0 {
            Some(ref iter) => iter.len(),
            None => 0,
        }
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        if let Some(iter) = self.0 {
            iter.with_producer(callback)
        } else {
            None.into_par_iter().with_producer(callback)
        }
    }
}

#![cfg(not(miri))]

#[macro_use]
extern crate quickcheck;

use atone::Vc;

use quickcheck::Arbitrary;
use quickcheck::Gen;

use std::cmp::min;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Deref;

fn set<'a, T, I>(iter: I) -> HashSet<T>
where
    I: IntoIterator<Item = &'a T>,
    T: Copy + Hash + Eq + 'a,
{
    iter.into_iter().cloned().collect()
}

quickcheck! {
    fn iter(push: Vec<u32>) -> bool {
        let mut vs = Vc::new();
        for &v in &push {
            vs.push(v);
        }
        push.iter().eq(vs.iter())
    }

    fn front_back(push: Vec<u32>) -> bool {
        let mut vs1 = Vc::new();
        let mut vs2 = VecDeque::new();
        for &v in &push {
            vs1.push_back(v);
            vs2.push_back(v);
        }
        assert_eq!(vs1.front(), vs2.front());
        assert_eq!(vs1.front_mut(), vs2.front_mut());
        assert_eq!(vs1.back(), vs2.back());
        assert_eq!(vs1.back_mut(), vs2.back_mut());
        true
    }

    fn contains(push: Vec<u32>) -> bool {
        let mut vs = Vc::new();
        for &v in &push {
            vs.push(v);
        }
        push.iter().all(|&v| vs.contains(&v))
    }

    fn push_remove(push: Vec<u8>, remove: Vec<u8>) -> bool {
        let mut vs = Vc::new();
        for &v in &push {
            vs.push(v);
        }
        for &rm in &remove {
            while let Some(i) = vs.iter().position(|&v| v == rm) {
                vs.remove(i);
            }
        }
        let elements = &set(&push) - &set(&remove);
        elements.iter().all(|v| vs.contains(v)) && vs.iter().all(|v| elements.contains(v))
    }

    fn push_retain(push: Vec<u8>, retain: Vec<u8>) -> bool {
        let mut vs = Vc::new();
        for &v in &push {
            vs.push(v);
        }
        vs.retain(|v| retain.contains(v));
        let push = set(&push);
        let retain = set(&retain);
        let elements: Vec<_> = push.intersection(&retain).collect();
        elements.iter().all(|v| vs.contains(v)) && vs.iter().all(|v| elements.contains(&v))
    }

    fn with_cap(cap: u8) -> bool {
        let cap = cap as usize;
        let vs: Vc<u8> = Vc::with_capacity(cap);
        println!("wish: {}, got: {} (diff: {})", cap, vs.capacity(), vs.capacity() as isize - cap as isize);
        vs.capacity() >= cap
    }
}

use Op::*;
#[derive(Copy, Clone, Debug)]
enum Op<T> {
    Push(T),
    Insert(u16, T),
    Pop,
    PopFront,
    CheckEnds,
    SwapRemove(u16),
    Truncate(u8),
    Reserve(u8),
}

impl<T> Arbitrary for Op<T>
where
    T: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        match u32::arbitrary(g) % 9 {
            0 | 1 => Push(T::arbitrary(g)),
            2 => Pop,
            3 => PopFront,
            4 => SwapRemove(u16::arbitrary(g)),
            5 => Insert(u16::arbitrary(g), T::arbitrary(g)),
            6 => Truncate(u8::arbitrary(g)),
            7 => Reserve(u8::arbitrary(g)),
            8 => CheckEnds,
            _ => unreachable!(),
        }
    }
}

fn do_ops<T>(ops: &[Op<T>], a: &mut Vc<T>, b: &mut VecDeque<T>)
where
    T: Eq + Clone + std::fmt::Debug,
{
    for op in ops {
        match *op {
            Push(ref v) => {
                a.push(v.clone());
                b.push_back(v.clone());
            }
            Insert(i, ref v) => {
                let ln = a.len();
                let i = if ln == 0 { 0 } else { i as usize % ln };
                a.insert(i, v.clone());
                b.insert(i, v.clone());
            }
            Pop => {
                assert_eq!(a.pop(), b.pop_back());
            }
            PopFront => {
                assert_eq!(a.pop_front(), b.pop_front());
            }
            SwapRemove(i) => {
                let ln = a.len();
                if ln != 0 {
                    assert_eq!(
                        a.swap_remove_back(i as usize % ln),
                        b.swap_remove_back(i as usize % ln)
                    );
                }
            }
            Truncate(n) => {
                a.truncate(n as usize);
                b.truncate(n as usize);
            }
            Reserve(n) => {
                a.reserve(n as usize);
                b.reserve(n as usize);
            }
            CheckEnds => {
                assert_eq!(a.front(), b.front());
                assert_eq!(a.front_mut(), b.front_mut());
                assert_eq!(a.back(), b.back());
                assert_eq!(a.back_mut(), b.back_mut());
            }
        }
        //println!("{:?}", a);
    }
}

fn assert_equivalent<T>(a: &Vc<T>, b: &VecDeque<T>) -> bool
where
    T: Eq + Debug,
{
    assert_eq!(a.len(), b.len());
    assert_eq!(a.iter().next().is_some(), b.iter().next().is_some());
    for v in a.iter() {
        assert!(b.contains(v), "b does not contain {:?}", v);
    }
    for v in b.iter() {
        assert!(a.contains(v), "a does not contain {:?}", v);
    }
    for (av, bv) in a.iter().zip(b.iter()) {
        assert_eq!(av, bv, "a and b order differs");
    }
    for (av, bv) in a.iter().rev().zip(b.iter().rev()) {
        assert_eq!(av, bv, "a and b reverse iterator order differs");
    }
    true
}

quickcheck! {
    fn operations_i8(ops: Large<Vec<Op<i8>>>) -> bool {
        let mut vs = Vc::new();
        let mut reference = VecDeque::new();
        do_ops(&ops, &mut vs, &mut reference);
        assert_equivalent(&vs, &reference)
    }

    fn operations_string(ops: Vec<Op<Alpha>>) -> bool {
        let mut vs = Vc::new();
        let mut reference = VecDeque::new();
        do_ops(&ops, &mut vs, &mut reference);
        assert_equivalent(&vs, &reference)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Alpha(String);

impl Deref for Alpha {
    type Target = String;
    fn deref(&self) -> &String {
        &self.0
    }
}

const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyz";

impl Arbitrary for Alpha {
    fn arbitrary(g: &mut Gen) -> Self {
        let len = u32::arbitrary(g) % g.size() as u32;
        let len = min(len, 16);
        Alpha(
            (0..len)
                .map(|_| ALPHABET[u32::arbitrary(g) as usize % ALPHABET.len()] as char)
                .collect(),
        )
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new((**self).shrink().map(Alpha))
    }
}

/// quickcheck Arbitrary adaptor -- make a larger vec
#[derive(Clone, Debug)]
struct Large<T>(T);

impl<T> Deref for Large<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> Arbitrary for Large<Vec<T>>
where
    T: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let len = u32::arbitrary(g) % (g.size() * 10) as u32;
        Large((0..len).map(|_| T::arbitrary(g)).collect())
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new((**self).shrink().map(Large))
    }
}

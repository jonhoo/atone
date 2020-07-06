#![cfg(feature = "rayon")]

#[macro_use]
extern crate lazy_static;

use atone::Vc;
use rayon_::iter::{
    IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelExtend,
    ParallelIterator,
};

macro_rules! assert_eq3 {
    ($e1:expr, $e2:expr, $e3:expr) => {{
        assert_eq!($e1, $e2);
        assert_eq!($e1, $e3);
        assert_eq!($e2, $e3);
    }};
}

lazy_static! {
    static ref VC_EMPTY: Vc<u32> = Vc::new();
    static ref VC: Vc<u32> = {
        let mut vc = Vc::new();
        vc.push(20);
        vc.push(10);
        vc.push(30);
        vc.push(50);
        vc.push(60);
        vc.push(40);
        vc
    };
}

#[test]
fn vc_seq_par_equivalence_iter_empty() {
    let vec_seq = VC_EMPTY.iter().collect::<Vec<_>>();
    let vec_par = VC_EMPTY.par_iter().collect::<Vec<_>>();

    assert_eq3!(vec_seq, vec_par, &[] as &[&u32]);
}

#[test]
fn vc_seq_par_equivalence_iter() {
    let mut vec_seq = VC.iter().collect::<Vec<_>>();
    let mut vec_par = VC.par_iter().collect::<Vec<_>>();

    assert_eq!(vec_seq, vec_par);

    let expected_sorted = [&10, &20, &30, &40, &50, &60];

    vec_seq.sort_unstable();
    vec_par.sort_unstable();

    assert_eq3!(vec_seq, vec_par, expected_sorted);
}

#[test]
fn vc_seq_par_equivalence_iter_mut_empty() {
    let mut map1 = VC_EMPTY.clone();
    let mut map2 = VC_EMPTY.clone();

    let vec_seq = map1.iter_mut().collect::<Vec<_>>();
    let vec_par = map2.par_iter_mut().collect::<Vec<_>>();

    assert_eq3!(vec_seq, vec_par, &[] as &[&u32]);
}

#[test]
fn vc_seq_par_equivalence_iter_mut() {
    let mut map1 = VC.clone();
    let mut map2 = VC.clone();

    let mut vec_seq = map1.iter_mut().collect::<Vec<_>>();
    let mut vec_par = map2.par_iter_mut().collect::<Vec<_>>();

    assert_eq!(vec_seq, vec_par);

    let expected_sorted = [&mut 10, &mut 20, &mut 30, &mut 40, &mut 50, &mut 60];

    vec_seq.sort_unstable();
    vec_par.sort_unstable();

    assert_eq3!(vec_seq, vec_par, expected_sorted);
}

#[test]
fn vc_seq_par_equivalence_into_iter_empty() {
    let vec_seq = VC_EMPTY.clone().into_iter().collect::<Vec<_>>();
    let vec_par = VC_EMPTY.clone().into_par_iter().collect::<Vec<_>>();

    assert_eq3!(vec_seq, vec_par, []);
}

#[test]
fn vc_seq_par_equivalence_into_iter() {
    let mut vec_seq = VC.clone().into_iter().collect::<Vec<_>>();
    let mut vec_par = VC.clone().into_par_iter().collect::<Vec<_>>();

    assert_eq!(vec_seq, vec_par);

    let expected_sorted = [10, 20, 30, 40, 50, 60];

    vec_seq.sort_unstable();
    vec_par.sort_unstable();

    assert_eq3!(vec_seq, vec_par, expected_sorted);
}

lazy_static! {
    static ref VC_VEC_EMPTY: Vec<u32> = vec![];
    static ref VC_VEC: Vec<u32> = vec![20, 10, 30, 50, 60, 40,];
}

#[test]
fn vc_seq_par_equivalence_collect_empty() {
    let vc_expected = VC_EMPTY.clone();
    let vc_seq = VC_VEC_EMPTY.clone().into_iter().collect::<Vc<_>>();
    let vc_par = VC_VEC_EMPTY.clone().into_par_iter().collect::<Vc<_>>();

    assert_eq!(vc_seq, vc_par);
    assert_eq!(vc_seq, vc_expected);
    assert_eq!(vc_par, vc_expected);
}

#[test]
fn vc_seq_par_equivalence_collect() {
    let vc_expected = VC.clone();
    let vc_seq = VC_VEC.clone().into_iter().collect::<Vc<_>>();
    let vc_par = VC_VEC.clone().into_par_iter().collect::<Vc<_>>();

    assert_eq!(vc_seq, vc_par);
    assert_eq!(vc_seq, vc_expected);
    assert_eq!(vc_par, vc_expected);
}

lazy_static! {
    static ref VC_EXISTING_EMPTY: Vc<u32> = Vc::new();
    static ref VC_EXISTING: Vc<u32> = {
        let mut vc = Vc::new();
        vc.push(20);
        vc.push(10);
        vc
    };
    static ref VC_EXTENSION_EMPTY: Vec<u32> = vec![];
    static ref VC_EXTENSION: Vec<u32> = vec![30, 50, 60, 40];
}

#[test]
fn vc_seq_par_equivalence_existing_empty_extend_empty() {
    let expected = Vc::new();
    let mut vc_seq = VC_EXISTING_EMPTY.clone();
    let mut vc_par = VC_EXISTING_EMPTY.clone();

    vc_seq.extend(VC_EXTENSION_EMPTY.iter().cloned());
    vc_par.par_extend(VC_EXTENSION_EMPTY.par_iter().cloned());

    assert_eq3!(vc_seq, vc_par, expected);
}

#[test]
fn vc_seq_par_equivalence_existing_empty_extend() {
    let expected = VC_EXTENSION.iter().cloned().collect::<Vc<_>>();
    let mut vc_seq = VC_EXISTING_EMPTY.clone();
    let mut vc_par = VC_EXISTING_EMPTY.clone();

    vc_seq.extend(VC_EXTENSION.iter().cloned());
    vc_par.par_extend(VC_EXTENSION.par_iter().cloned());

    assert_eq3!(vc_seq, vc_par, expected);
}

#[test]
fn vc_seq_par_equivalence_existing_extend_empty() {
    let expected = VC_EXISTING.clone();
    let mut vc_seq = VC_EXISTING.clone();
    let mut vc_par = VC_EXISTING.clone();

    vc_seq.extend(VC_EXTENSION_EMPTY.iter().cloned());
    vc_par.par_extend(VC_EXTENSION_EMPTY.par_iter().cloned());

    assert_eq3!(vc_seq, vc_par, expected);
}

#[test]
fn vc_seq_par_equivalence_existing_extend() {
    let expected = VC.clone();
    let mut vc_seq = VC_EXISTING.clone();
    let mut vc_par = VC_EXISTING.clone();

    vc_seq.extend(VC_EXTENSION.iter().cloned());
    vc_par.par_extend(VC_EXTENSION.par_iter().cloned());

    assert_eq3!(vc_seq, vc_par, expected);
}

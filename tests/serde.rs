#![cfg(feature = "serde")]

use atone::Vc;
use serde_test::{assert_tokens, Token};

#[test]
fn test_serde_empty_vc() {
    let my_vec: Vc<u32> = Vc::default();
    assert_tokens(&my_vec, &[Token::Seq { len: Some(0) }, Token::SeqEnd])
}

#[test]
fn test_serde_non_empty() {
    let mut my_vec: Vc<u32> = Vc::default();
    my_vec.push(1);
    my_vec.push(2);
    my_vec.push(3);
    assert_tokens(
        &my_vec,
        &[
            Token::Seq { len: Some(3) },
            Token::U32(1),
            Token::U32(2),
            Token::U32(3),
            Token::SeqEnd,
        ],
    )
}

#[test]
fn test_serde_while_atoning() {
    let mut my_vec: Vc<u32> = Vc::with_capacity(15);
    for i in 1..=16 {
        my_vec.push(i);
    }
    assert!(my_vec.is_atoning());
    assert_tokens(
        &my_vec,
        &[
            Token::Seq { len: Some(16) },
            Token::U32(1),
            Token::U32(2),
            Token::U32(3),
            Token::U32(4),
            Token::U32(5),
            Token::U32(6),
            Token::U32(7),
            Token::U32(8),
            Token::U32(9),
            Token::U32(10),
            Token::U32(11),
            Token::U32(12),
            Token::U32(13),
            Token::U32(14),
            Token::U32(15),
            Token::U32(16),
            Token::SeqEnd,
        ],
    );
}

#[test]
fn test_vec_to_vc_serde() {
    let sinful: Vec<u32> = vec![1, 2, 3, 4];
    let json = serde_json::to_string(&sinful).unwrap();
    let atoner: Vc<u32> = serde_json::from_str(&json).unwrap();
    assert_eq!(
        sinful, atoner,
        "Deserialized Vc is not identical to the original Vec"
    );
}

#[test]
fn test_vc_to_vec_serde() {
    let mut atoner: Vc<u32> = Vc::new();
    atoner.push(1);
    atoner.push(2);
    atoner.push(3);
    atoner.push(4);
    let json = serde_json::to_string(&atoner).unwrap();
    let baptized: Vec<u32> = serde_json::from_str(&json).unwrap();
    assert_eq!(
        atoner, baptized,
        "Deserialized Vec is not identical to the original Vc"
    );
}

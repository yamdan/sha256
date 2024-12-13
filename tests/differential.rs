use std::collections::BTreeMap;
use std::path::PathBuf;

use noir_runner::{InputValue, NoirRunner};
use sha2::{Digest, Sha256};

#[test]
fn test_vibe_check() {
    let runner = NoirRunner::try_new(PathBuf::new()).unwrap();

    let result = runner
        .run("test_keccak256_0", BTreeMap::new())
        .unwrap()
        .unwrap();

    let expected: [u8; 32] = Sha256::digest([]).try_into().unwrap();

    let expected = expected.into_iter()
        .map(|byte| byte as u32)
        .map(|byte| InputValue::Field(byte.into()))
        .collect();

    println!("{:?}", result);
    println!("{:?}", expected);

    assert_eq!(result, InputValue::Vec(expected));
}

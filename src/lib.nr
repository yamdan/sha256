use std::runtime::is_unconstrained;
use std::hash::sha256_compression;

/// Block size
global BLOCK_SIZE: u32 = 64;

/// First index in the block where the 8-byte message will be written.
global MSG_LEN_PTR: u32 = 56;

/// Size of message block when packed as 4-byte integer array.
global INT_BLOCK_SIZE: u32 = 16;

/// Size of unsigned 32 bit integer in bytes.
global INT_SIZE: u32 = 4;

/// Index of the integer in `INT_BLOCK` where the length is writen.
global INT_SIZE_PTR: u32 = MSG_LEN_PTR / INT_SIZE;

global TWO_POW_8: u32 = 256;
global TWO_POW_16: u32 = TWO_POW_8 * 256;
global TWO_POW_24: u32 = TWO_POW_16 * 256;
global TWO_POW_32: u64 = TWO_POW_24 as u64 * 256;

/// Index of abyte in 64 byte block;
type BlockBytePtr = u32;

/// Foreign function interface type
type IntBlock = [u32; INT_BLOCK_SIZE];

type MsgBlock = IntBlock;

type Hash = [u8; 32];

type State = [u32; 8];

#[no_predicates]
pub fn digest<let N: u32>(msg: [u8; N]) -> Hash {
    sha256_var(msg, N as u64)
}

/// SHA256 hash function
pub fn sha256_var<let N: u32>(msg: [u8; N], msg_len: u64) -> Hash {
    let msg_len = msg_len as u32;

    let num_blocks = N / BLOCK_SIZE;

    let mut msg_block: MsgBlock = [0; INT_BLOCK_SIZE];

    let mut state: State = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    let mut msg_byte_ptr = 0;

    for i in 0..num_blocks {
        let msg_start = BLOCK_SIZE * i;

        let (new_msg_block, new_msg_byte_ptr) = unsafe { build_msg_block(msg, msg_len, msg_start) };

        if msg_start < msg_len {
            msg_block = new_msg_block;
        }

        if !is_unconstrained() {
            let new_msg_byte_ptr = verify_msg_block(msg, msg_len, msg_block, msg_start);

            if msg_start < msg_len {
                msg_byte_ptr = new_msg_byte_ptr;
            }
        } else if msg_start < msg_len {
            msg_byte_ptr = new_msg_byte_ptr;
        }

        if (msg_start < msg_len) & (msg_byte_ptr == BLOCK_SIZE) {
            state = sha256_compression(msg_block, state);
        }
    }

    let modulus = N % BLOCK_SIZE;

    if modulus != 0 {
        let msg_start = BLOCK_SIZE * num_blocks;

        let (new_msg_block, new_msg_byte_ptr) = unsafe { build_msg_block(msg, msg_len, msg_start) };

        if msg_start < msg_len {
            msg_block = new_msg_block;
        }

        if !is_unconstrained() {
            let new_msg_byte_ptr = verify_msg_block(msg, msg_len, msg_block, msg_start);

            if msg_start < msg_len {
                msg_byte_ptr = new_msg_byte_ptr;

                verify_msg_block_padding(msg_block, msg_byte_ptr);
            }
        } else if msg_start < msg_len {
            msg_byte_ptr = new_msg_byte_ptr;
        }
    }

    if msg_byte_ptr == BLOCK_SIZE {
        msg_byte_ptr = 0;
    }

    msg_block = update_block_item(
        msg_block,
        msg_byte_ptr,
        |msg_item| set_item_byte_then_zeros(msg_item, msg_byte_ptr, 1 << 7),
    );

    msg_byte_ptr += 1;

    let last_block = msg_block;

    if msg_byte_ptr > MSG_LEN_PTR {
        state = sha256_compression(msg_block, state);

        msg_byte_ptr = 0;
    }

    msg_block = unsafe { attach_len_to_msg_block(msg_block, msg_byte_ptr, msg_len) };

    if !is_unconstrained() {
        verify_msg_len(msg_block, last_block, msg_byte_ptr, msg_len);
    }

    hash_final_block(msg_block, state)
}

unconstrained fn build_msg_block<let N: u32>(
    msg: [u8; N],
    msg_len: u32,
    msg_start: u32,
) -> (MsgBlock, BlockBytePtr) {
    let mut msg_block: MsgBlock = [0; INT_BLOCK_SIZE];

    let block_input = if msg_start + BLOCK_SIZE > msg_len {
        if msg_len < msg_start {
            0
        } else {
            msg_len - msg_start
        }
    } else {
        BLOCK_SIZE
    };

    let mut int_input = block_input / INT_SIZE;

    if block_input % INT_SIZE != 0 {
        int_input += 1;
    }

    for i in 0..int_input {
        let mut msg_item: u32 = 0;

        for j in 0..INT_SIZE {
            let k = i * INT_SIZE + j;

            let msg_byte = if k < block_input {
                msg[msg_start + k]
            } else {
                0
            };

            msg_item = shl8(msg_item, 1) + msg_byte as u32;
        }

        msg_block[i] = msg_item;
    }

    (msg_block, block_input)
}

fn verify_msg_block<let N: u32>(
    msg: [u8; N],
    msg_len: u32,
    msg_block: MsgBlock,
    msg_start: u32,
) -> BlockBytePtr {
    let mut msg_byte_ptr = 0;

    let mut msg_end = msg_start + BLOCK_SIZE;

    if msg_end > N {
        msg_end = N;
    }

    if msg_end % INT_SIZE != 0 {
        msg_end += INT_SIZE - msg_end % INT_SIZE;
    }

    let mut msg_item: u32 = 0;

    let mut i: u32 = 0;

    for k in msg_start..=msg_end {
        if k % INT_SIZE == 0 {
            if (msg_start < msg_len) & (k > msg_start) {
                assert_eq(msg_block[i], msg_item as u32);

                i += 1;

                msg_item = 0;
            }
        }

        msg_item = shl8(msg_item, 1);

        if k < msg_len & k < msg_end {
            msg_item += msg[k] as u32;

            msg_byte_ptr += 1;
        }
    }

    msg_byte_ptr
}

fn verify_msg_block_padding(msg_block: MsgBlock, msg_byte_ptr: BlockBytePtr) {
    verify_msg_block_zeros(msg_block, msg_byte_ptr, INT_BLOCK_SIZE);
}

fn verify_msg_block_zeros(
    msg_block: MsgBlock,
    mut msg_byte_ptr: BlockBytePtr,
    max_int_byte_ptr: u32,
) {
    let zero = msg_block[0] - msg_block[0];

    let mut int_byte_ptr = msg_byte_ptr / INT_SIZE;

    let modulus = msg_byte_ptr % INT_SIZE;

    if modulus != 0 {
        let zeros = INT_SIZE - modulus;

        let mask = if zeros == 3 {
            TWO_POW_24
        } else if zeros == 2 {
            TWO_POW_16
        } else {
            TWO_POW_8
        };

        assert_eq(msg_block[int_byte_ptr] % mask, zero);

        int_byte_ptr += 1;
    }

    for i in 0..max_int_byte_ptr {
        if i >= int_byte_ptr {
            assert_eq(msg_block[i], zero);
        }
    }
}

fn verify_msg_block_equals_last(
    msg_block: MsgBlock,
    last_block: MsgBlock,
    mut msg_byte_ptr: BlockBytePtr,
) {
    let mut int_byte_ptr = msg_byte_ptr / INT_SIZE;

    let modulus = msg_byte_ptr % INT_SIZE;

    if modulus != 0 {
        let last_field = last_block[int_byte_ptr];

        let mut msg_item: u32 = 0;

        msg_byte_ptr -= modulus;

        for i in 0..INT_SIZE {
            msg_item = shl8(msg_item, 1);

            if i < modulus {
                msg_item += get_item_byte(last_field, msg_byte_ptr) as u32;

                msg_byte_ptr += 1;
            }
        }

        assert_eq(msg_block[int_byte_ptr], msg_item);
    }

    for i in 0..INT_SIZE_PTR {
        if i < int_byte_ptr {
            assert_eq(msg_block[i], last_block[i]);
        }
    }
}

fn update_block_item<Env>(
    mut msg_block: MsgBlock,
    msg_byte_ptr: BlockBytePtr,
    f: fn[Env](u32) -> u32,
) -> MsgBlock {
    let i = msg_byte_ptr / INT_SIZE;

    msg_block[i] = f(msg_block[i]);

    msg_block
}

fn set_item_byte_then_zeros(msg_item: u32, msg_byte_ptr: BlockBytePtr, msg_byte: u8) -> u32 {
    let zeros = (INT_SIZE - msg_byte_ptr % INT_SIZE) as u8;

    let zeroed_item = shl8(shr8(msg_item, zeros), zeros);

    let new_item = byte_into_item(msg_byte, msg_byte_ptr);

    zeroed_item + new_item
}

fn get_item_byte(mut msg_item: u32, msg_byte_ptr: BlockBytePtr) -> u8 {
    let max_shifts = INT_SIZE - 1;

    let shifts = (max_shifts - msg_byte_ptr % INT_SIZE) as u8;

    msg_item = shr8(msg_item, shifts);

    msg_item as u8
}

fn byte_into_item(msg_byte: u8, msg_byte_ptr: BlockBytePtr) -> u32 {
    let mut msg_item = msg_byte as u32;

    let max_shifts = INT_SIZE - 1;

    let shifts = (max_shifts - msg_byte_ptr % INT_SIZE) as u8;

    shl8(msg_item, shifts)
}

fn make_item(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    let mut item = b0 as u32;
    item = shl8(item, 1) + b1 as u32;
    item = shl8(item, 1) + b2 as u32;
    item = shl8(item, 1) + b3 as u32;

    item
}

fn shl8(item: u32, shifts: u8) -> u32 {
    if is_unconstrained() {
        if item == 0 {
            0
        } else {
            item << (8 * shifts)
        }
    } else {
        if shifts == 0 {
            item
        } else if shifts == 1 {
            item * TWO_POW_8
        } else if shifts == 2 {
            item * TWO_POW_16
        } else if shifts == 3 {
            item * TWO_POW_24
        } else {
            0
        }
    }
}

fn shr8(item: u32, shifts: u8) -> u32 {
    if is_unconstrained() {
        item >> (8 * shifts)
    } else {
        if shifts == 0 {
            item
        } else if shifts == 1 {
            item / TWO_POW_8
        } else if shifts == 2 {
            item / TWO_POW_16
        } else if shifts == 3 {
            item / TWO_POW_24
        } else {
            0
        }
    }
}

unconstrained fn attach_len_to_msg_block(
    mut msg_block: MsgBlock,
    mut msg_byte_ptr: BlockBytePtr,
    msg_len: u32,
) -> MsgBlock {
    let modulus = msg_byte_ptr % INT_SIZE;

    if modulus != 0 {
        let i = msg_byte_ptr / INT_SIZE;

        let zeros = (INT_SIZE - modulus) as u8;

        msg_block[i] = shl8(shr8(msg_block[i], zeros), zeros);

        msg_byte_ptr += zeros as u32;
    }

    for i in (msg_byte_ptr / INT_SIZE)..INT_SIZE_PTR {
        msg_block[i] = 0;
    }

    let len = 8 * msg_len;

    let len_bytes: [u8; 8] = (len as Field).to_be_bytes();

    for i in 0..=1 {
        let shift = i * 4;

        msg_block[INT_SIZE_PTR + i] = make_item(
            len_bytes[shift],
            len_bytes[shift + 1],
            len_bytes[shift + 2],
            len_bytes[shift + 3],
        );
    }

    msg_block
}

fn verify_msg_len(
    msg_block: MsgBlock,
    last_block: MsgBlock,
    msg_byte_ptr: BlockBytePtr,
    msg_len: u32,
) {
    verify_msg_block_zeros(msg_block, msg_byte_ptr, INT_SIZE_PTR);

    verify_msg_block_equals_last(msg_block, last_block, msg_byte_ptr);

    let mut reconstructed_len: u64 = 0;

    for i in INT_SIZE_PTR..INT_BLOCK_SIZE {
        reconstructed_len *= TWO_POW_32;

        reconstructed_len += msg_block[i] as u64;
    }

    let len = 8 * msg_len as u64;

    assert_eq(reconstructed_len, len);
}

fn hash_final_block(msg_block: MsgBlock, mut state: State) -> Hash {
    let mut out_state: Hash = [0; 32];

    state = sha256_compression(msg_block, state);

    for j in 0..8 {
        let state_bytes: [u8; 4] = (state[j] as Field).to_be_bytes();

        for k in 0..4 {
            out_state[4 * j + k] = state_bytes[k];
        }
    }

    out_state
}

mod tests {
    use super::{
        attach_len_to_msg_block, build_msg_block, byte_into_item, get_item_byte, make_item,
        set_item_byte_then_zeros, sha256_var, IntBlock, shl8, shr8,
    };

    #[test]
    fn test_smoke() {
        let input = [0xbd];

        let result = [
            0x68, 0x32, 0x57, 0x20, 0xaa, 0xbd, 0x7c, 0x82, 0xf3, 0x0f, 0x55, 0x4b, 0x31, 0x3d,
            0x05, 0x70, 0xc9, 0x5a, 0xcc, 0xbb, 0x7d, 0xc4, 0xb5, 0xaa, 0xe1, 0x12, 0x04, 0xc0,
            0x8f, 0xfe, 0x73, 0x2b,
        ];

        assert_eq(sha256_var(input, input.len() as u64), result);
    }

    #[test]
    fn msg_just_over_block() {
        let input = [
            102, 114, 111, 109, 58, 114, 117, 110, 110, 105, 101, 114, 46, 108, 101, 97, 103, 117,
            101, 115, 46, 48, 106, 64, 105, 99, 108, 111, 117, 100, 46, 99, 111, 109, 13, 10, 99,
            111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 116, 101, 120, 116, 47, 112,
            108, 97, 105, 110, 59, 32, 99, 104, 97, 114, 115, 101, 116,
        ];
        let result = [
            91, 122, 146, 93, 52, 109, 133, 148, 171, 61, 156, 70, 189, 238, 153, 7, 222, 184, 94,
            24, 65, 114, 192, 244, 207, 199, 87, 232, 192, 224, 171, 207,
        ];
        assert_eq(sha256_var(input, input.len() as u64), result);
    }

    #[test]
    fn msg_multiple_over_block() {
        let input = [
            102, 114, 111, 109, 58, 114, 117, 110, 110, 105, 101, 114, 46, 108, 101, 97, 103, 117,
            101, 115, 46, 48, 106, 64, 105, 99, 108, 111, 117, 100, 46, 99, 111, 109, 13, 10, 99,
            111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 116, 101, 120, 116, 47, 112,
            108, 97, 105, 110, 59, 32, 99, 104, 97, 114, 115, 101, 116, 61, 117, 115, 45, 97, 115,
            99, 105, 105, 13, 10, 109, 105, 109, 101, 45, 118, 101, 114, 115, 105, 111, 110, 58, 49,
            46, 48, 32, 40, 77, 97, 99, 32, 79, 83, 32, 88, 32, 77, 97, 105, 108, 32, 49, 54, 46,
            48, 32, 92, 40, 51, 55, 51, 49, 46, 53, 48, 48, 46, 50, 51, 49, 92, 41, 41, 13, 10, 115,
            117, 98, 106, 101, 99, 116, 58, 72, 101, 108, 108, 111, 13, 10, 109, 101, 115, 115, 97,
            103, 101, 45, 105, 100, 58, 60, 56, 70, 56, 49, 57, 68, 51, 50, 45, 66, 54, 65, 67, 45,
            52, 56, 57, 68, 45, 57, 55, 55, 70, 45, 52, 51, 56, 66, 66, 67, 52, 67, 65, 66, 50, 55,
            64, 109, 101, 46, 99, 111, 109, 62, 13, 10, 100, 97, 116, 101, 58, 83, 97, 116, 44, 32,
            50, 54, 32, 65, 117, 103, 32, 50, 48, 50, 51, 32, 49, 50, 58, 50, 53, 58, 50, 50, 32,
            43, 48, 52, 48, 48, 13, 10, 116, 111, 58, 122, 107, 101, 119, 116, 101, 115, 116, 64,
            103, 109, 97, 105, 108, 46, 99, 111, 109, 13, 10, 100, 107, 105, 109, 45, 115, 105, 103,
            110, 97, 116, 117, 114, 101, 58, 118, 61, 49, 59, 32, 97, 61, 114, 115, 97, 45, 115,
            104, 97, 50, 53, 54, 59, 32, 99, 61, 114, 101, 108, 97, 120, 101, 100, 47, 114, 101,
            108, 97, 120, 101, 100, 59, 32, 100, 61, 105, 99, 108, 111, 117, 100, 46, 99, 111, 109,
            59, 32, 115, 61, 49, 97, 49, 104, 97, 105, 59, 32, 116, 61, 49, 54, 57, 51, 48, 51, 56,
            51, 51, 55, 59, 32, 98, 104, 61, 55, 120, 81, 77, 68, 117, 111, 86, 86, 85, 52, 109, 48,
            87, 48, 87, 82, 86, 83, 114, 86, 88, 77, 101, 71, 83, 73, 65, 83, 115, 110, 117, 99, 75,
            57, 100, 74, 115, 114, 99, 43, 118, 85, 61, 59, 32, 104, 61, 102, 114, 111, 109, 58, 67,
            111, 110, 116, 101, 110, 116, 45, 84, 121, 112, 101, 58, 77, 105, 109, 101, 45, 86, 101,
            114, 115, 105, 111, 110, 58, 83, 117, 98, 106, 101, 99,
        ];
        let result = [
            116, 90, 151, 31, 78, 22, 138, 180, 211, 189, 69, 76, 227, 200, 155, 29, 59, 123, 154,
            60, 47, 153, 203, 129, 157, 251, 48, 2, 79, 11, 65, 47,
        ];
        assert_eq(sha256_var(input, input.len() as u64), result);
    }

    #[test]
    fn msg_just_under_block() {
        let input = [
            102, 114, 111, 109, 58, 114, 117, 110, 110, 105, 101, 114, 46, 108, 101, 97, 103, 117,
            101, 115, 46, 48, 106, 64, 105, 99, 108, 111, 117, 100, 46, 99, 111, 109, 13, 10, 99,
            111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 116, 101, 120, 116, 47, 112,
            108, 97, 105, 110, 59,
        ];
        let result = [
            143, 140, 76, 173, 222, 123, 102, 68, 70, 149, 207, 43, 39, 61, 34, 79, 216, 252, 213,
            165, 74, 16, 110, 74, 29, 64, 138, 167, 30, 1, 9, 119,
        ];
        assert_eq(sha256_var(input, input.len() as u64), result);
    }

    #[test]
    fn msg_big_not_block_multiple() {
        let input = [
            102, 114, 111, 109, 58, 114, 117, 110, 110, 105, 101, 114, 46, 108, 101, 97, 103, 117,
            101, 115, 46, 48, 106, 64, 105, 99, 108, 111, 117, 100, 46, 99, 111, 109, 13, 10, 99,
            111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 116, 101, 120, 116, 47, 112,
            108, 97, 105, 110, 59, 32, 99, 104, 97, 114, 115, 101, 116, 61, 117, 115, 45, 97, 115,
            99, 105, 105, 13, 10, 109, 105, 109, 101, 45, 118, 101, 114, 115, 105, 111, 110, 58, 49,
            46, 48, 32, 40, 77, 97, 99, 32, 79, 83, 32, 88, 32, 77, 97, 105, 108, 32, 49, 54, 46,
            48, 32, 92, 40, 51, 55, 51, 49, 46, 53, 48, 48, 46, 50, 51, 49, 92, 41, 41, 13, 10, 115,
            117, 98, 106, 101, 99, 116, 58, 72, 101, 108, 108, 111, 13, 10, 109, 101, 115, 115, 97,
            103, 101, 45, 105, 100, 58, 60, 56, 70, 56, 49, 57, 68, 51, 50, 45, 66, 54, 65, 67, 45,
            52, 56, 57, 68, 45, 57, 55, 55, 70, 45, 52, 51, 56, 66, 66, 67, 52, 67, 65, 66, 50, 55,
            64, 109, 101, 46, 99, 111, 109, 62, 13, 10, 100, 97, 116, 101, 58, 83, 97, 116, 44, 32,
            50, 54, 32, 65, 117, 103, 32, 50, 48, 50, 51, 32, 49, 50, 58, 50, 53, 58, 50, 50, 32,
            43, 48, 52, 48, 48, 13, 10, 116, 111, 58, 122, 107, 101, 119, 116, 101, 115, 116, 64,
            103, 109, 97, 105, 108, 46, 99, 111, 109, 13, 10, 100, 107, 105, 109, 45, 115, 105, 103,
            110, 97, 116, 117, 114, 101, 58, 118, 61, 49, 59, 32, 97, 61, 114, 115, 97, 45, 115,
            104, 97, 50, 53, 54, 59, 32, 99, 61, 114, 101, 108, 97, 120, 101, 100, 47, 114, 101,
            108, 97, 120, 101, 100, 59, 32, 100, 61, 105, 99, 108, 111, 117, 100, 46, 99, 111, 109,
            59, 32, 115, 61, 49, 97, 49, 104, 97, 105, 59, 32, 116, 61, 49, 54, 57, 51, 48, 51, 56,
            51, 51, 55, 59, 32, 98, 104, 61, 55, 120, 81, 77, 68, 117, 111, 86, 86, 85, 52, 109, 48,
            87, 48, 87, 82, 86, 83, 114, 86, 88, 77, 101, 71, 83, 73, 65, 83, 115, 110, 117, 99, 75,
            57, 100, 74, 115, 114, 99, 43, 118, 85, 61, 59, 32, 104, 61, 102, 114, 111, 109, 58, 67,
            111, 110, 116, 101, 110, 116, 45, 84, 121, 112, 101, 58, 77, 105, 109, 101, 45, 86, 101,
            114, 115, 105, 111, 110, 58, 83, 117, 98, 106, 101, 99, 116, 58, 77, 101, 115, 115, 97,
            103, 101, 45, 73, 100, 58, 68, 97, 116, 101, 58, 116, 111, 59, 32, 98, 61,
        ];
        let result = [
            112, 144, 73, 182, 208, 98, 9, 238, 54, 229, 61, 145, 222, 17, 72, 62, 148, 222, 186,
            55, 192, 82, 220, 35, 66, 47, 193, 200, 22, 38, 26, 186,
        ];
        assert_eq(sha256_var(input, input.len() as u64), result);
    }

    #[test]
    fn msg_big_with_padding() {
        let input = [
            48, 130, 1, 37, 2, 1, 0, 48, 11, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 1, 48, 130, 1, 17,
            48, 37, 2, 1, 1, 4, 32, 176, 223, 31, 133, 108, 84, 158, 102, 70, 11, 165, 175, 196, 12,
            201, 130, 25, 131, 46, 125, 156, 194, 28, 23, 55, 133, 157, 164, 135, 136, 220, 78, 48,
            37, 2, 1, 2, 4, 32, 190, 82, 180, 235, 222, 33, 79, 50, 152, 136, 142, 35, 116, 224, 6,
            242, 156, 141, 128, 248, 10, 61, 98, 86, 248, 45, 207, 210, 90, 232, 175, 38, 48, 37, 2,
            1, 3, 4, 32, 0, 194, 104, 108, 237, 246, 97, 230, 116, 198, 69, 110, 26, 87, 17, 89,
            110, 199, 108, 250, 36, 21, 39, 87, 110, 102, 250, 213, 174, 131, 171, 174, 48, 37, 2,
            1, 11, 4, 32, 136, 155, 87, 144, 111, 15, 152, 127, 85, 25, 154, 81, 20, 58, 51, 75,
            193, 116, 234, 0, 60, 30, 29, 30, 183, 141, 72, 247, 255, 203, 100, 124, 48, 37, 2, 1,
            12, 4, 32, 41, 234, 106, 78, 31, 11, 114, 137, 237, 17, 92, 71, 134, 47, 62, 78, 189,
            233, 201, 214, 53, 4, 47, 189, 201, 133, 6, 121, 34, 131, 64, 142, 48, 37, 2, 1, 13, 4,
            32, 91, 222, 210, 193, 62, 222, 104, 82, 36, 41, 138, 253, 70, 15, 148, 208, 156, 45,
            105, 171, 241, 195, 185, 43, 217, 162, 146, 201, 222, 89, 238, 38, 48, 37, 2, 1, 14, 4,
            32, 76, 123, 216, 13, 51, 227, 72, 245, 59, 193, 238, 166, 103, 49, 23, 164, 171, 188,
            194, 197, 156, 187, 249, 28, 198, 95, 69, 15, 182, 56, 54, 38, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let result = [
            32, 85, 108, 174, 127, 112, 178, 182, 8, 43, 134, 123, 192, 211, 131, 66, 184, 240, 212,
            181, 240, 180, 106, 195, 24, 117, 54, 129, 19, 10, 250, 53,
        ];
        let message_size = 297;
        assert_eq(sha256_var(input, message_size), result);
    }

    #[test]
    fn msg_big_no_padding() {
        let input = [
            48, 130, 1, 37, 2, 1, 0, 48, 11, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 1, 48, 130, 1, 17,
            48, 37, 2, 1, 1, 4, 32, 176, 223, 31, 133, 108, 84, 158, 102, 70, 11, 165, 175, 196, 12,
            201, 130, 25, 131, 46, 125, 156, 194, 28, 23, 55, 133, 157, 164, 135, 136, 220, 78, 48,
            37, 2, 1, 2, 4, 32, 190, 82, 180, 235, 222, 33, 79, 50, 152, 136, 142, 35, 116, 224, 6,
            242, 156, 141, 128, 248, 10, 61, 98, 86, 248, 45, 207, 210, 90, 232, 175, 38, 48, 37, 2,
            1, 3, 4, 32, 0, 194, 104, 108, 237, 246, 97, 230, 116, 198, 69, 110, 26, 87, 17, 89,
            110, 199, 108, 250, 36, 21, 39, 87, 110, 102, 250, 213, 174, 131, 171, 174, 48, 37, 2,
            1, 11, 4, 32, 136, 155, 87, 144, 111, 15, 152, 127, 85, 25, 154, 81, 20, 58, 51, 75,
            193, 116, 234, 0, 60, 30, 29, 30, 183, 141, 72, 247, 255, 203, 100, 124, 48, 37, 2, 1,
            12, 4, 32, 41, 234, 106, 78, 31, 11, 114, 137, 237, 17, 92, 71, 134, 47, 62, 78, 189,
            233, 201, 214, 53, 4, 47, 189, 201, 133, 6, 121, 34, 131, 64, 142, 48, 37, 2, 1, 13, 4,
            32, 91, 222, 210, 193, 62, 222, 104, 82, 36, 41, 138, 253, 70, 15, 148, 208, 156, 45,
            105, 171, 241, 195, 185, 43, 217, 162, 146, 201, 222, 89, 238, 38, 48, 37, 2, 1, 14, 4,
            32, 76, 123, 216, 13, 51, 227, 72, 245, 59, 193, 238, 166, 103, 49, 23, 164, 171, 188,
            194, 197, 156, 187, 249, 28, 198, 95, 69, 15, 182, 56, 54, 38,
        ];
        let result = [
            32, 85, 108, 174, 127, 112, 178, 182, 8, 43, 134, 123, 192, 211, 131, 66, 184, 240, 212,
            181, 240, 180, 106, 195, 24, 117, 54, 129, 19, 10, 250, 53,
        ];
        assert_eq(sha256_var(input, input.len() as u64), result);
    }

    #[test]
    fn test_get_item_byte() {
        let fld = make_item(10, 20, 30, 40);
        assert_eq(fld, 0x0a141e28);
        assert_eq(get_item_byte(fld, 0), 10);
        assert_eq(get_item_byte(fld, 4), 10);
        assert_eq(get_item_byte(fld, 6), 30);
    }

    #[test]
    fn test_byte_into_item() {
        let fld = make_item(0, 20, 0, 0);
        assert_eq(byte_into_item(20, 1), fld);
        assert_eq(byte_into_item(20, 5), fld);
    }

    #[test]
    fn test_set_item_zeros() {
        let fld0 = make_item(10, 20, 30, 40);
        let fld1 = make_item(10, 0, 0, 0);
        assert_eq(shl8(shr8(fld0, 3), 3), fld1);
        assert_eq(shl8(shr8(fld0, 4), 4), 0);
        assert_eq(shl8(shr8(0, 4), 4), 0);
    }

    #[test]
    fn test_set_item_byte_then_zeros() {
        let fld0 = make_item(10, 20, 30, 40);
        let fld1 = make_item(10, 50, 0, 0);
        assert_eq(set_item_byte_then_zeros(fld0, 1, 50), fld1);
    }

    #[test]
    fn test_build_msg_block_start_0() {
        let input = [
            102, 114, 111, 109, 58, 114, 117, 110, 110, 105, 101, 114, 46, 108, 101, 97, 103, 117,
            101, 115, 46, 48,
        ];
        assert_eq(input.len(), 22);
        let (msg_block, msg_byte_ptr) = unsafe { build_msg_block(input, input.len(), 0) };
        assert_eq(msg_byte_ptr, input.len());
        assert_eq(msg_block[0], make_item(input[0], input[1], input[2], input[3]));
        assert_eq(msg_block[1], make_item(input[4], input[5], input[6], input[7]));
        assert_eq(msg_block[5], make_item(input[20], input[21], 0, 0));
        assert_eq(msg_block[6], 0);
    }

    #[test]
    fn test_build_msg_block_start_1() {
        let input = [
            102, 114, 111, 109, 58, 114, 117, 110, 110, 105, 101, 114, 46, 108, 101, 97, 103, 117,
            101, 115, 46, 48, 106, 64, 105, 99, 108, 111, 117, 100, 46, 99, 111, 109, 13, 10, 99,
            111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 58, 116, 101, 120, 116, 47, 112,
            108, 97, 105, 110, 59, 32, 99, 104, 97, 114, 115, 101, 116,
        ];
        assert_eq(input.len(), 68);
        let (msg_block, msg_byte_ptr) = unsafe { build_msg_block(input, input.len(), 64) };
        assert_eq(msg_byte_ptr, 4);
        assert_eq(msg_block[0], make_item(input[64], input[65], input[66], input[67]));
        assert_eq(msg_block[1], 0);
    }

    #[test]
    fn test_attach_len_to_msg_block() {
        let input: IntBlock = [
            2152555847, 1397309779, 1936618851, 1262052426, 1936876331, 1985297723, 543702374,
            1919905082, 1131376244, 1701737517, 1417244773, 978151789, 1697470053, 1920166255,
            1849316213, 1651139939,
        ];
        let msg_block = unsafe { attach_len_to_msg_block(input, 1, 448) };
        assert_eq(msg_block[0], ((1 << 7) as u32) * 256 * 256 * 256);
        assert_eq(msg_block[1], 0);
        assert_eq(msg_block[15], 3584);
    }
}

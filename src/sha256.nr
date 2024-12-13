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
pub(crate) type IntBlock = [u32; INT_BLOCK_SIZE];

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

unconstrained pub(crate) fn build_msg_block<let N: u32>(
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

pub(crate) fn verify_msg_block<let N: u32>(
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

pub(crate) fn verify_msg_block_padding(msg_block: MsgBlock, msg_byte_ptr: BlockBytePtr) {
    verify_msg_block_zeros(msg_block, msg_byte_ptr, INT_BLOCK_SIZE);
}

pub(crate) fn verify_msg_block_zeros(
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

pub(crate) fn verify_msg_block_equals_last(
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

pub(crate) fn update_block_item<Env>(
    mut msg_block: MsgBlock,
    msg_byte_ptr: BlockBytePtr,
    f: fn[Env](u32) -> u32,
) -> MsgBlock {
    let i = msg_byte_ptr / INT_SIZE;

    msg_block[i] = f(msg_block[i]);

    msg_block
}

pub(crate) fn set_item_byte_then_zeros(msg_item: u32, msg_byte_ptr: BlockBytePtr, msg_byte: u8) -> u32 {
    let zeros = (INT_SIZE - msg_byte_ptr % INT_SIZE) as u8;

    let zeroed_item = shl8(shr8(msg_item, zeros), zeros);

    let new_item = byte_into_item(msg_byte, msg_byte_ptr);

    zeroed_item + new_item
}

pub(crate) fn get_item_byte(mut msg_item: u32, msg_byte_ptr: BlockBytePtr) -> u8 {
    let max_shifts = INT_SIZE - 1;

    let shifts = (max_shifts - msg_byte_ptr % INT_SIZE) as u8;

    msg_item = shr8(msg_item, shifts);

    msg_item as u8
}

pub(crate) fn byte_into_item(msg_byte: u8, msg_byte_ptr: BlockBytePtr) -> u32 {
    let mut msg_item = msg_byte as u32;

    let max_shifts = INT_SIZE - 1;

    let shifts = (max_shifts - msg_byte_ptr % INT_SIZE) as u8;

    shl8(msg_item, shifts)
}

pub(crate) fn make_item(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    let mut item = b0 as u32;
    item = shl8(item, 1) + b1 as u32;
    item = shl8(item, 1) + b2 as u32;
    item = shl8(item, 1) + b3 as u32;

    item
}

pub(crate) fn shl8(item: u32, shifts: u8) -> u32 {
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

pub(crate) fn shr8(item: u32, shifts: u8) -> u32 {
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

unconstrained pub(crate) fn attach_len_to_msg_block(
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

pub(crate) fn verify_msg_len(
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

pub(crate) fn hash_final_block(msg_block: MsgBlock, mut state: State) -> Hash {
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

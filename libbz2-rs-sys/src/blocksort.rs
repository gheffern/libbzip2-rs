#![forbid(unsafe_code)]

use core::cmp::Ordering;

use crate::assert_h;
use crate::bzlib::{EState, BZ_N_OVERSHOOT};

/// Compare two cyclic rotations of `block` of length `n`.
#[inline]
fn compare_cyclic_suffixes(block: &[u8], n: usize, a: usize, b: usize) -> Ordering {
    if a == b {
        return Ordering::Equal;
    }

    let mut cur_a = a;
    let mut cur_b = b;

    for _ in 0..n {
        let ca = block[cur_a];
        let cb = block[cur_b];
        if ca != cb {
            return ca.cmp(&cb);
        }
        cur_a = if cur_a + 1 == n { 0 } else { cur_a + 1 };
        cur_b = if cur_b + 1 == n { 0 } else { cur_b + 1 };
    }

    Ordering::Equal
}

/// Classify cyclic suffixes into S-type (1) and L-type (0).
/// Returns true if all characters in block are identical.
fn classify_cyclic_suffixes(block: &[u8], n: usize, is_s_type: &mut [u64]) -> bool {
    let words = n.div_ceil(64);
    is_s_type[..words].fill(0);

    let mut p = usize::MAX;
    for i in 0..n {
        let next_i = if i + 1 == n { 0 } else { i + 1 };
        if block[i] != block[next_i] {
            p = i;
            break;
        }
    }

    if p == usize::MAX {
        return true;
    }

    let next_p = if p + 1 == n { 0 } else { p + 1 };
    let mut curr_is_s = block[p] < block[next_p];
    if curr_is_s {
        is_s_type[p >> 6] |= 1 << (p & 63);
    }

    let mut i = if p == 0 { n - 1 } else { p - 1 };
    while i != p {
        let next_i = if i + 1 == n { 0 } else { i + 1 };
        let c = block[i];
        let next_c = block[next_i];
        if c < next_c {
            curr_is_s = true;
        } else if c > next_c {
            curr_is_s = false;
        }
        if curr_is_s {
            is_s_type[i >> 6] |= 1 << (i & 63);
        }
        i = if i == 0 { n - 1 } else { i - 1 };
    }

    false
}

#[inline(always)]
fn is_s(bitset: &[u64], i: usize) -> bool {
    ((bitset[i >> 6] >> (i & 63)) & 1) != 0
}

/// Base Two-Stage Induced Suffix Sorting (DivSufSort for BWT).
///
/// Based on Yuta Mori's DivSufSort (2005):
/// 1. Classify all cyclic suffixes into S-type (smaller than suffix i+1) and
///    L-type (larger than suffix i+1).
/// 2. Extract Type B* suffixes (S-type suffixes immediately preceded by an L-type suffix).
/// 3. Sort the B* suffixes.
/// 4. Induce sorted order for all L-type suffixes in a left-to-right pass.
/// 5. Induce sorted order for all S-type suffixes in a right-to-left pass.
fn divsufsort_bwt(ptr: &mut [u32], block: &mut [u8], quadrant: &mut [u16], nblock: usize) -> i32 {
    if nblock == 0 {
        return 0;
    }
    if nblock == 1 {
        ptr[0] = 0;
        return 0;
    }

    // Overshoot padding copy
    for i in 0..BZ_N_OVERSHOOT {
        block[nblock + i] = block[i];
    }

    // Allocate bitset for S-type/L-type flags (112.5 KB on stack for max 900,000 block)
    let words_needed = nblock.div_ceil(64);
    let mut bitset = [0u64; 14063];
    let is_all_equal =
        classify_cyclic_suffixes(&block[..nblock], nblock, &mut bitset[..words_needed]);

    if is_all_equal {
        for (i, p) in ptr[..nblock].iter_mut().enumerate() {
            *p = i as u32;
        }
        return 0;
    }

    // Collect Type B* suffixes: S-type suffixes whose cyclic predecessor is L-type
    let mut num_bstar = 0;
    for i in 0..nblock {
        let prev_i = if i == 0 { nblock - 1 } else { i - 1 };
        if is_s(&bitset, i) && !is_s(&bitset, prev_i) {
            ptr[num_bstar] = i as u32;
            num_bstar += 1;
        }
    }

    // Sort B* suffixes
    if num_bstar > 0 {
        ptr[..num_bstar].sort_unstable_by(|&a, &b| {
            compare_cyclic_suffixes(block, nblock, a as usize, b as usize)
        });
    }

    // Count 1-byte frequencies for bucket boundaries
    let mut count = [0usize; 256];
    for &b in &block[..nblock] {
        count[b as usize] += 1;
    }

    let mut bucket_start = [0usize; 256];
    let mut bucket_end = [0usize; 256];
    let mut total = 0;
    for c in 0..256 {
        bucket_start[c] = total;
        total += count[c];
        bucket_end[c] = total;
    }

    // Copy sorted B* suffixes into quadrant buffer before clearing ptr
    for i in 0..num_bstar {
        let val = ptr[i];
        quadrant[i * 2] = (val & 0xFFFF) as u16;
        quadrant[i * 2 + 1] = (val >> 16) as u16;
    }

    // Clear ptr to unassigned sentinel (u32::MAX)
    ptr.fill(u32::MAX);

    // Place sorted B* suffixes at bucket ends
    let mut tail = bucket_end;
    for i in (0..num_bstar).rev() {
        let low = quadrant[i * 2] as u32;
        let high = quadrant[i * 2 + 1] as u32;
        let s = low | (high << 16);
        let c = block[s as usize] as usize;
        tail[c] -= 1;
        ptr[tail[c]] = s;
    }

    // Phase 1: Induce L-type suffixes from left to right
    let mut head = bucket_start;
    for k in 0..nblock {
        let p = ptr[k];
        if p != u32::MAX {
            let j = if p == 0 { nblock - 1 } else { (p - 1) as usize };
            if !is_s(&bitset, j) {
                let c = block[j] as usize;
                ptr[head[c]] = j as u32;
                head[c] += 1;
            }
        }
    }

    // Phase 2: Induce S-type suffixes from right to left
    let mut tail = bucket_end;
    for k in (0..nblock).rev() {
        let p = ptr[k];
        if p != u32::MAX {
            let j = if p == 0 { nblock - 1 } else { (p - 1) as usize };
            if is_s(&bitset, j) {
                let c = block[j] as usize;
                tail[c] -= 1;
                ptr[tail[c]] = j as u32;
            }
        }
    }

    // Locate origPtr (index where ptr[k] == 0)
    let mut orig_ptr = -1;
    for (i, &p) in ptr[..nblock].iter().enumerate() {
        if p == 0 {
            orig_ptr = i as i32;
            break;
        }
    }

    orig_ptr
}

/// Main entry point called from `compress.rs`.
pub(crate) fn block_sort(s: &mut EState) {
    let nblock = usize::try_from(s.nblock).unwrap();
    if nblock == 0 {
        s.origPtr = 0;
        return;
    }

    let ptr = s.arr1.ptr();
    let (block, quadrant) = s.arr2.block_and_quadrant(nblock);

    s.origPtr = divsufsort_bwt(ptr, block, quadrant, nblock);

    assert_h!(s.origPtr != -1, 1003);
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Untrusted Symbol Index Re-exports and Prologue Frame-Size Inference (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (provides `*Index.json` sidecar types for host tools and
//!   prologue stack-frame inference mirroring `inferPrologueFrameBytes?` in
//!   `ProofLib/PrologueFrame.lean`).
//! - **Purpose:** Infers downward prologue stack frame sizes (`sub sp, sp, #n`, pre-indexed
//!   `stp`/`str ..., [sp, #-n]!`) from raw AArch64 function code bytes and re-exports the
//!   `*Index.json` schema and discovery helpers from [`super::index_schema`].
//!
//! # Key Types & Functions
//! - [`TargetSymbolIndex`], [`FunctionIndexEntry`], [`CalleeInfo`], [`StubIndexEntry`],
//!   [`GENERATED_DIR`], [`default_repo_root`], [`symbol_index_paths`], [`load_symbol_indices`]:
//!   JSON schema and discovery helpers (re-exported from [`super::index_schema`]).
//! - [`SpEffect`], [`classify_sp_word`], [`trimmed_word_count`], [`trim_trailing_zero_bytes_len`],
//!   [`infer_prologue_frame`]: Prologue stack frame analysis.
//!
//! # When to Read This File
//! - Read this file when modifying prologue stack frame inference (keep in sync with
//!   `inferPrologueFrameBytes?` in `ProofLib/PrologueFrame.lean`).

// ---------------------------------------------------------------------------
// 1. Prologue Stack Frame Inference
// ---------------------------------------------------------------------------

/// Effect of a single 32-bit AArch64 instruction on `SP`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpEffect {
    /// Does not modify `SP`.
    None,
    /// Subtracts a positive constant `delta` bytes from `SP` (`sub sp, sp, #delta`,
    /// pre-indexed `stp ..., [sp, #-delta]!`, or pre-indexed `str ..., [sp, #-delta]!`).
    Alloc(u64),
    /// Adds a constant `delta` bytes to `SP` (`add sp, sp, #delta`, post-indexed
    /// `ldp ..., [sp], #delta`, post-indexed `ldr ..., [sp], #delta`, or `mov sp, x29`).
    Dealloc(u64),
    /// Modifies `SP` in a dynamic or unrecognized way (`sub sp, sp, xN`, `and sp, ...`, etc.).
    Unknown,
}

/// Control-flow classification of an instruction for prologue boundary detection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlowKind {
    /// Ordinary straight-line instruction.
    Normal,
    /// Call (`bl`, `blr`), return (`ret`), unconditional branch (`b`, `br`), or backward
    /// conditional branch.
    EndPrologue,
    /// Forward conditional branch (`b.cond`, `cbz`, `cbnz`, `tbz`, `tbnz`) targeting word
    /// index `target_idx > idx`.
    FwdCond(usize),
}

/// Classify how a 32-bit AArch64 instruction word `w` modifies `SP`.
///
/// Mirrors `Arm64.classifySpWord` in `ProofLib/PrologueFrame.lean`.
pub fn classify_sp_word(w: u32) -> SpEffect {
    // 1. `sub sp, sp, #imm12[, lsl #12]`: sf=1, op=1, S=0, 100010, sh, imm12, Rn=31, Rd=31
    if (w & 0xff80_03ff) == 0xd100_03ff {
        let sh = (w >> 22) & 1;
        let imm12 = ((w >> 10) & 0xfff) as u64;
        let delta = if sh == 1 { imm12 << 12 } else { imm12 };
        return if delta > 0 {
            SpEffect::Alloc(delta)
        } else {
            SpEffect::None
        };
    }
    // 2. `add sp, sp, #imm12[, lsl #12]`: sf=1, op=0, S=0, 100010, sh, imm12, Rn=31, Rd=31
    if (w & 0xff80_03ff) == 0x9100_03ff {
        let sh = (w >> 22) & 1;
        let imm12 = ((w >> 10) & 0xfff) as u64;
        let delta = if sh == 1 { imm12 << 12 } else { imm12 };
        return if delta > 0 {
            SpEffect::Dealloc(delta)
        } else {
            SpEffect::None
        };
    }
    // 3. Load/Store Pair (`stp` / `ldp`) with base `Rn = 31` (`sp`):
    //    bits 29..27 = 101, bit 25 = 0, bits 9..5 = 31.
    if (w & 0x3a00_03e0) == 0x2800_03e0 {
        let idx_mode = (w >> 23) & 3;
        if idx_mode != 0b011 && idx_mode != 0b001 {
            // Signed-offset (`0b010`) or no-allocate (`0b000`): does not write back to `sp`.
            // (`Rt`/`Rt2` = 31 in `ldp` is `xzr`/`wzr`, never `sp`.)
            return SpEffect::None;
        }
        let opc = (w >> 30) & 3;
        let v = (w >> 26) & 1;
        let l = (w >> 22) & 1;
        let imm7 = ((w >> 15) & 0x7f) as u64;
        let scale = if v == 0 {
            match opc {
                0 => Some(2u32),
                2 => Some(3u32),
                _ => None,
            }
        } else {
            match opc {
                0 => Some(2u32),
                1 => Some(3u32),
                2 => Some(4u32),
                _ => None,
            }
        };
        let Some(scale) = scale else {
            return SpEffect::Unknown;
        };
        if idx_mode == 0b011 && l == 0 && imm7 >= 64 {
            return SpEffect::Alloc((128 - imm7) << scale);
        }
        if idx_mode == 0b001 && l == 1 && imm7 > 0 && imm7 < 64 {
            return SpEffect::Dealloc(imm7 << scale);
        }
        return SpEffect::Unknown;
    }
    // 4. Load/Store Register immediate (`str` / `ldr`) with base `Rn = 31` (`sp`):
    //    bits 29..27 = 111, bits 25..24 = 00, bit 21 = 0, bits 9..5 = 31.
    if (w & 0x3b20_03e0) == 0x3800_03e0 {
        let idx_mode = (w >> 10) & 3;
        if idx_mode != 0b11 && idx_mode != 0b01 {
            return SpEffect::None;
        }
        let opc = (w >> 22) & 3;
        let imm9 = ((w >> 12) & 0x1ff) as u64;
        if idx_mode == 0b11 && opc == 0 && imm9 >= 256 {
            return SpEffect::Alloc(512 - imm9);
        }
        if idx_mode == 0b01 && opc != 0 && imm9 > 0 && imm9 < 256 {
            return SpEffect::Dealloc(imm9);
        }
        return SpEffect::Unknown;
    }
    // 5. `mov sp, x29` (`add sp, x29, #0`, encoding `0x910003bf`) in epilogues:
    if w == 0x9100_03bf {
        return SpEffect::Dealloc(0);
    }
    // 6. Other instructions writing `Rd = 31` where `Rd` denotes `SP`:
    //    - Add/Sub immediate with `S = 0` and `Rd = 31` (`Rn != 31` since `Rn = 31` was handled above)
    if (w & 0x3f00_001f) == 0x1100_001f {
        return SpEffect::Unknown;
    }
    //    - Add/Sub extended register with `S = 0` and `Rd = 31` (e.g. `sub sp, sp, x8`)
    if (w & 0x3f20_001f) == 0x0b20_001f {
        return SpEffect::Unknown;
    }
    //    - Logical immediate with `opc != 3` (`ands` writes `xzr`) and `Rd = 31` (e.g. `and sp, x9, #-16`)
    if (w & 0x1f80_001f) == 0x1200_001f && ((w >> 29) & 3) != 3 {
        return SpEffect::Unknown;
    }
    SpEffect::None
}

/// Classify the control-flow behavior of instruction word `w` at word index `idx`.
fn classify_flow_word(w: u32, idx: usize) -> FlowKind {
    // `bl` or `b`
    if (w & 0xfc00_0000) == 0x9400_0000 || (w & 0xfc00_0000) == 0x1400_0000 {
        return FlowKind::EndPrologue;
    }
    // `blr`, `br`, or `ret`
    if (w & 0xffff_fc1f) == 0xd63f_0000
        || (w & 0xffff_fc1f) == 0xd61f_0000
        || (w & 0xffff_fc1f) == 0xd65f_0000
    {
        return FlowKind::EndPrologue;
    }
    // `b.cond` or `cbz`/`cbnz` (19-bit signed word displacement in bits 23..5)
    if (w & 0xff00_0010) == 0x5400_0000 || (w & 0x7e00_0000) == 0x3400_0000 {
        let imm19 = ((w >> 5) & 0x7ffff) as usize;
        if imm19 == 0 || imm19 >= 0x40000 {
            return FlowKind::EndPrologue;
        }
        return FlowKind::FwdCond(idx + imm19);
    }
    // `tbz`/`tbnz` (14-bit signed word displacement in bits 18..5)
    if (w & 0x7e00_0000) == 0x3600_0000 {
        let imm14 = ((w >> 5) & 0x3fff) as usize;
        if imm14 == 0 || imm14 >= 0x2000 {
            return FlowKind::EndPrologue;
        }
        return FlowKind::FwdCond(idx + imm14);
    }
    FlowKind::Normal
}

#[derive(Clone, Copy, Debug)]
enum PrologueState {
    Before(Option<usize>),
    InPrologue(u64, Option<usize>),
    After(u64),
}

fn past_min_fwd(idx: usize, min_fwd: Option<usize>) -> bool {
    min_fwd.is_some_and(|t| idx >= t)
}

/// Number of 32-bit words in `code_bytes` after stripping trailing `0x0000_0000`
/// alignment padding words (keeping at least 1 word if `code_bytes` is non-empty).
/// Mirrors `trimTrailingZeroWords` in `Arm64/Trusted/Spec/SepLogic.lean`.
pub fn trimmed_word_count(code_bytes: &[u8]) -> Option<usize> {
    if code_bytes.len() % 4 != 0 {
        return None;
    }
    let mut total_words = code_bytes.len() / 4;
    while total_words > 1 {
        let i = total_words - 1;
        let w = u32::from_le_bytes(code_bytes[4 * i..4 * i + 4].try_into().unwrap());
        if w == 0 {
            total_words -= 1;
        } else {
            break;
        }
    }
    Some(total_words)
}

/// Byte length of `code_bytes` after stripping trailing 4-byte `0x0000_0000` padding words
/// (keeping at least 4 bytes when non-empty).
/// Mirrors `trimTrailingZeroBytesLen` in `Arm64/Trusted/Spec/SepLogic.lean`.
pub fn trim_trailing_zero_bytes_len(code_bytes: &[u8]) -> u64 {
    match trimmed_word_count(code_bytes) {
        Some(words) => (words * 4) as u64,
        None => code_bytes.len() as u64,
    }
}

/// Infer the downward stack frame size in bytes allocated by a function's prologue from its
/// raw code bytes (`Some(0)` for leaf functions that do not allocate a frame; `None` if the
/// function uses dynamic/non-standard `SP` adjustments or has a misaligned frame).
///
/// Mirrors `Arm64.inferPrologueFrameBytes?` in `ProofLib/PrologueFrame.lean`.
pub fn infer_prologue_frame(code_bytes: &[u8]) -> Option<u64> {
    let total_words = trimmed_word_count(code_bytes)?;
    let mut state = PrologueState::Before(None);
    for idx in 0..total_words {
        if let PrologueState::InPrologue(acc, min_fwd) = state
            && past_min_fwd(idx, min_fwd)
        {
            state = PrologueState::After(acc);
        }
        let w = u32::from_le_bytes(code_bytes[4 * idx..4 * idx + 4].try_into().unwrap());
        match (state, classify_sp_word(w)) {
            (_, SpEffect::Unknown) => return None,
            (PrologueState::Before(min_fwd), SpEffect::Alloc(d)) => {
                if past_min_fwd(idx, min_fwd) {
                    return None;
                }
                state = PrologueState::InPrologue(d, min_fwd);
            }
            (PrologueState::InPrologue(acc, min_fwd), SpEffect::Alloc(d)) => {
                state = PrologueState::InPrologue(acc + d, min_fwd);
            }
            (PrologueState::After(_), SpEffect::Alloc(_)) => return None,
            (PrologueState::Before(_), SpEffect::Dealloc(_)) => return None,
            (PrologueState::InPrologue(acc, _), SpEffect::Dealloc(_)) => {
                state = PrologueState::After(acc);
            }
            (PrologueState::After(acc), SpEffect::Dealloc(_)) => {
                state = PrologueState::After(acc);
            }
            (PrologueState::Before(min_fwd), SpEffect::None) => match classify_flow_word(w, idx) {
                FlowKind::Normal => {}
                FlowKind::EndPrologue => {
                    state = PrologueState::After(0);
                }
                FlowKind::FwdCond(target_idx) => {
                    let next_min = Some(min_fwd.map_or(target_idx, |t| t.min(target_idx)));
                    state = PrologueState::Before(next_min);
                }
            },
            (PrologueState::InPrologue(acc, min_fwd), SpEffect::None) => {
                match classify_flow_word(w, idx) {
                    FlowKind::Normal => {
                        state = PrologueState::InPrologue(acc, min_fwd);
                    }
                    FlowKind::EndPrologue | FlowKind::FwdCond(_) => {
                        state = PrologueState::After(acc);
                    }
                }
            }
            (PrologueState::After(acc), SpEffect::None) => {
                state = PrologueState::After(acc);
            }
        }
    }
    let total = match state {
        PrologueState::Before(_) => 0,
        PrologueState::InPrologue(acc, min_fwd) => {
            if past_min_fwd(total_words, min_fwd) {
                return None;
            }
            acc
        }
        PrologueState::After(acc) => acc,
    };
    if total % 16 == 0 { Some(total) } else { None }
}

// ---------------------------------------------------------------------------
// 2. Symbol Index Schema Re-exports
// ---------------------------------------------------------------------------

pub use super::index_schema::{
    CalleeInfo, FunctionIndexEntry, GENERATED_DIR, StubIndexEntry, TargetSymbolIndex,
    default_repo_root, load_symbol_indices, symbol_index_paths,
};

#[cfg(test)]
mod tests {
    use super::*;

    fn words(ws: &[u32]) -> Vec<u8> {
        ws.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    #[test]
    fn prologue_frame_inference_leaf_and_standard_prologues() {
        // 1. Leaf function: `add x0, x0, #1; ret` -> Some(0)
        let leaf = words(&[0x9100_0400, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&leaf), Some(0));

        // 2. Pre-indexed `stp x29, x30, [sp, #-16]!; mov x29, sp; ldp x29, x30, [sp], #16; ret` -> Some(16)
        let stp16 = words(&[0xa9bf_7bfd, 0x9100_03fd, 0xa8c1_7bfd, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&stp16), Some(16));

        // 3. `sub sp, sp, #48; stp x29, x30, [sp, #32]; add sp, sp, #48; ret` -> Some(48)
        let sub48 = words(&[0xd100_c3ff, 0xa902_7bfd, 0x9100_c3ff, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&sub48), Some(48));

        // 4. Two-step allocation: `stp x29, x30, [sp, #-32]!; sub sp, sp, #16; add sp, sp, #16; ldp x29, x30, [sp], #32; ret` -> Some(48)
        let two_step = words(&[
            0xa9be_7bfd, // stp x29, x30, [sp, #-32]!
            0xd100_43ff, // sub sp, sp, #16
            0x9100_43ff, // add sp, sp, #16
            0xa8c2_7bfd, // ldp x29, x30, [sp], #32
            0xd65f_03c0, // ret
        ]);
        assert_eq!(infer_prologue_frame(&two_step), Some(48));

        // 5. Pre-indexed single register `str x30, [sp, #-16]!; ldr x30, [sp], #16; ret` -> Some(16)
        let str16 = words(&[0xf81f_0ffe, 0xf841_07fe, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&str16), Some(16));

        // 6. Shrink-wrapped early return guard:
        //    `cbz x0, +4 words (.Lret); stp x29, x30, [sp, #-32]!; bl 0; ldp x29, x30, [sp], #32; .Lret: ret`
        let shrink_wrapped = words(&[
            0xb400_0080, // cbz x0, +16 (to word 4)
            0xa9be_7bfd, // stp x29, x30, [sp, #-32]!
            0x9400_0000, // bl ...
            0xa8c2_7bfd, // ldp x29, x30, [sp], #32
            0xd65f_03c0, // ret
        ]);
        assert_eq!(infer_prologue_frame(&shrink_wrapped), Some(32));
    }

    #[test]
    fn prologue_frame_inference_rejects_dynamic_or_malformed_sp() {
        // 1. Dynamic stack allocation `sub sp, sp, x8` (`0xcb2863ff`) -> None
        let dyn_sub = words(&[0xcb28_63ff, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&dyn_sub), None);

        // 2. Misaligned frame size `sub sp, sp, #8` (`0xd10023ff`) -> None
        let misaligned = words(&[0xd100_23ff, 0x9100_23ff, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&misaligned), None);

        // 3. Allocation after a `bl` call -> None
        let alloc_after_call = words(&[
            0xa9bf_7bfd, // stp x29, x30, [sp, #-16]!
            0x9400_0000, // bl ...
            0xd100_43ff, // sub sp, sp, #16 (after call!)
            0xd65f_03c0, // ret
        ]);
        assert_eq!(infer_prologue_frame(&alloc_after_call), None);
    }
}

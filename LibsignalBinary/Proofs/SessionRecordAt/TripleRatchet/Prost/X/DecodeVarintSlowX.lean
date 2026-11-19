/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesW -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Slow -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.TryFromDefsX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.From
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::varint::decode_varint_slow`

Verifies `decode_varint_slow` (`0x4db38`, block `293`) on `contractProg img.base ext` and under
`[LibsignalPlacement]` from `DecodeError::from`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.WireX
export CryptoVerification.LibsignalTripleRatchet.WireX (decodeVarintSlowSpecX)
export CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow
  (vAcc1 vAcc2 vAcc3 vAcc4 vAcc5 vAcc6 vAcc7 vAcc8 vAcc9 vAcc10 vAcc1_eq)
open CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_DecodeVarintSlowX : True := trivial

/-! ## Stack helpers -/

theorem stackAt_varintSlowX (sp : BitVec 64) :
    stackAt sp varintSlowStackX =
      stackAt (sp - 64#64) decodeErrorHookStackW ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v8) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := ProofLib.stackAt_split_cells sp decodeErrorHookStackW 8 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 8)) 8 (by decide)] at h0
  change stackAt sp varintSlowStackX =
    stackAt (sp - 64#64) decodeErrorHookStackW ∗ memRegion (sp - 64#64) 64 at h0
  have s1 := ProofLib.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [bv_sub_add_lit sp 56 40] at s2
  have s3 := ProofLib.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s3
  rw [h0, s1, s2, s3,
    ProofLib.memRegion_eight (sp - 64#64), ProofLib.memRegion_eight (sp - 16#64), ProofLib.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

@[expose] def StateAt (s0 s : State) (pc : BitVec 64) : Prop :=
  s.pc = pc ∧ s.status = .Running ∧ s.sp = s0.sp - 64#64 ∧
    s.trace = s0.trace ∧ CalleeSaved19_28 s0 s

/-! ## Caller-relative callee -/

section Placed

open CryptoVerification

/-- Relocatable `prost::encoding::varint::decode_varint_slow` (Block `293`) meets
`DecodeVarintSlowPlacedOkW A H` given `DecodeErrorFromPlacedOkW A H`. -/
theorem decodeVarintSlow_placed_okW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hFrom : DecodeErrorFromPlacedOkW A H) :
    DecodeVarintSlowPlacedOkW A H :=
  CryptoVerification.LibsignalTripleRatchet.Prost.decode_varint_slow_placed_ok_with_stack
    (errStack := decodeErrorHookStackW) (by decide)
    (WireX.decodeErrorFrom_placed_ok_cl (callerProg := (blkPC_293).rebase (blkPl_293).base H) hFrom)

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X

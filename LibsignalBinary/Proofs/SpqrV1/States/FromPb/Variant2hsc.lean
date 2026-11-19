/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part C

**Checked by Lean.**

Error exit tails (`+9224`, `+9228`), inline `ProtoPolynomialDecoder` deallocation
(`+4428..+4512`), and `+9152 -> +9228` vector cleanup chain.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsc_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

theorem v2hsc_fnAddr_eq_sub_of_rel {P : Program} {n1 n2 : String} {k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (hrel : (P.rebase b X).fnAddr n2 = (P.rebase b X).fnAddr n1 + BitVec.ofNat 64 k) :
    (P.rebase b X).fnAddr n1 = (P.rebase b X).fnAddr n2 - BitVec.ofNat 64 k := by
  rw [hrel, BitVec.add_sub_cancel]

theorem v2hsc_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v2hsc_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v2hsc_ptsCap_add_one_ne_zero {ptsCap : BitVec 64} (h : ptsCap.toNat * 24 < 2 ^ 63) :
    ¬((ptsCap + 1#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  bv_omega

@[expose] def v2hsc_optProtoPolyDecoderWordsAt (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗ ((a + 32#64) ↦₆₄ w32)

@[expose] def v2hsc_optProtoPolyDecoderHeap (A : RustAlloc) :
    Option ProtoPolynomialDecoder → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 32 → BitVec 32 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some pb, w0, w8, w16, d24, d28, w32 =>
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 w32)⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w8 (w0.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
       memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))

/-! ## Error Exit Tails (`+9228 -> s0.x30` and `+9224 -> s0.x30`) -/

theorem v2hsc_bfm_loByte_eq (x23 x26 : BitVec 64) :
    ((x23 &&& 255#64 ||| (x26 &&& 72057594037927935#64) <<< 8).extractLsb' 0 8) =
      x23.extractLsb' 0 8 := by
  bv_kernel

@[expose, reducible]
def v2hsc_Saved4436Preserved (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = ptsPtr ∧
  s.readReg64 .x22 = ptsCap ∧
  s.readReg64 .x23 = x23_val ∧
  TraceCalleeSaved s s0

/-- Extract the `some pb` case of `v2hsc_optProtoPolyDecoderWordsAt` + `v2hsc_optProtoPolyDecoderHeap`
at `fsp + 1032#64` into the precondition shape of `v2hsc_dealloc_some_proto_decoder_4428`. -/
theorem v2hsc_optProtoDecoder_some_pre (A : RustAlloc) (fsp : BitVec 64)
    (pb : ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 w232 : BitVec 64)
    (Frame : SepProp) :
    v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
      v2hsc_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame ⊢
    ⌜d16 = BitVec.ofNat 64 pb.pts.length ∧
      pb.pts.length ≤ d0.toNat ∧ d0.toNat * 24 < 2 ^ 63⌝ ∗
    (((fsp + 232#64) ↦₆₄ w232) ∗
     ((fsp + 1040#64) ↦₆₄ d8) ∗
     ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
     (if d0 = 0#64 then emp
      else A.live d8 (d0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 pb.pts ∗
        memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
     A.pool ∗ stackAt fsp allocHookStack ∗
     (((fsp + 1032#64) ↦₆₄ d0) ∗
      ((fsp + 1056#64) ↦₃₂ d24) ∗
      ((fsp + 1060#64) ↦₃₂ d28) ∗
      ((fsp + 1064#64) ↦₆₄ d32) ∗ Frame)) := by
  dsimp only [v2hsc_optProtoPolyDecoderWordsAt, v2hsc_optProtoPolyDecoderHeap]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜d16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ d0.toNat ∧ d0.toNat * 24 < 2 ^ 63 ∧
      d8 ≠ 0#64 ∧
      (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 d32)⌝ ∗
    (((fsp + 232#64) ↦₆₄ w232) ∗
     ((fsp + 1040#64) ↦₆₄ d8) ∗
     ((fsp + 1048#64) ↦₆₄ d16) ∗
     (if d0 = 0#64 then emp
      else A.live d8 (d0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 pb.pts ∗
        memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
     A.pool ∗ stackAt fsp allocHookStack ∗
     (((fsp + 1032#64) ↦₆₄ d0) ∗
      ((fsp + 1056#64) ↦₃₂ d24) ∗
      ((fsp + 1060#64) ↦₃₂ d28) ∗
      ((fsp + 1064#64) ↦₆₄ d32) ∗ Frame)) by ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨hd16, _, _, hle, hcap, _, _⟩
  subst hd16
  exact Entails.pure_right ⟨rfl, hle, hcap⟩ (Entails.refl _)

end CryptoVerification.SpqrV1.States.FromPb

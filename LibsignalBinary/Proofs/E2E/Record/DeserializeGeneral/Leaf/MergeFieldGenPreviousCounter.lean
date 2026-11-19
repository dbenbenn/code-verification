/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import

/-!
# Tag-5 Leaf (`mergeFieldGenPreviousCounter_ok`) for `SessionStructure::merge_field`

Proves `mergeFieldGenPreviousCounter_ok` for `previous_counter` (tag `5`, `int32::merge` into
`ss + 0x14c`).
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem genField_tag_eq_5_iff (fl : GenField) :
    fl.tag = 5 ↔ ∃ v, fl = .prevCounter v := by
  cases fl <;> simp [GenField.tag]

private theorem mergeUint32_prevCounter_previousCounter (v : BitVec 32) (tail : List (BitVec 8)) :
    mergeUint32 .varint ((GenField.prevCounter v).payload ++ tail) = some (v, tail) := by
  exact mergeUint32_encode v tail

local elab "mf5_code_fetches_from " codeId:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter s!"previousCounter_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

private theorem drop_left_sepWPp_previousCounter {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

private def prostSSGRest_previousCounter (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

private theorem prostSSGAt_eq_prevCounter_sep_rest_previousCounter (A : RustAlloc) (ss : BitVec 64) (v : SSG) :
    prostSSGAt A ss v = ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗ prostSSGRest_previousCounter A ss v := by
  unfold prostSSGAt prostSSGRest_previousCounter
  ac_rfl

private theorem stackAt_mergeField_split_previousCounter (sp : BitVec 64) :
    stackAt sp mergeFieldStack =
      memRegion (sp - 16384#64) 7792 ∗
        stackAt (sp - 240#64) Prost.int32MergeStack ∗
        memRegion (sp - 240#64) 160 ∗
        memRegion (sp - 56#64) 8 ∗
        (∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
         ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64,
         ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
          ((sp - 80#64) ↦₆₄ w29) ∗ ((sp - 72#64) ↦₆₄ w30) ∗
          ((sp - 64#64) ↦₆₄ w25) ∗
          ((sp - 48#64) ↦₆₄ w24) ∗ ((sp - 40#64) ↦₆₄ w23) ∗
          ((sp - 32#64) ↦₆₄ w22) ∗ ((sp - 24#64) ↦₆₄ w21) ∗
          ((sp - 16#64) ↦₆₄ w20) ∗ ((sp - 8#64) ↦₆₄ w19)) := by
  have h0 := LibsignalTripleRatchet.stackAt_split_cells sp 16144 30 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 30)) 30 (by decide)] at h0
  change stackAt sp mergeFieldStack = stackAt (sp - 240#64) 16144 ∗ memRegion (sp - 240#64) 240 at h0
  have hsub := ProofLib.stackAt_split_bottom (sp - 240#64) Prost.int32MergeStack 7792 (by decide)
  change stackAt (sp - 240#64) 16144 =
    memRegion (sp - 240#64 - 16144#64) 7792 ∗ stackAt (sp - 240#64) Prost.int32MergeStack at hsub
  have hsub_addr : sp - 240#64 - 16144#64 = sp - 16384#64 := by bv_omega
  rw [hsub_addr] at hsub
  have s1 := Prost.memRegion_split (sp - 240#64) 160 80 (by decide)
  rw [bv_sub_add_lit sp 240 160] at s1
  have s2 := Prost.memRegion_split (sp - 80#64) 8 72 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s2
  have s3 := Prost.memRegion_split (sp - 72#64) 8 64 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s3
  have s4 := Prost.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s4
  have s5 := Prost.memRegion_split (sp - 56#64) 8 48 (by decide)
  rw [bv_sub_add_lit sp 56 8] at s5
  have s6 := Prost.memRegion_split (sp - 48#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 48 8] at s6
  have s7 := Prost.memRegion_split (sp - 40#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 40 8] at s7
  have s8 := Prost.memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s8
  have s9 := Prost.memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s9
  have s10 := Prost.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s10
  rw [h0, hsub, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    Prost.memRegion_eight (sp - 80#64), Prost.memRegion_eight (sp - 72#64),
    Prost.memRegion_eight (sp - 64#64),
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

private theorem setWidth8_zext64_trunc32_previousCounter (v : BitVec 64) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)) = BitVec.setWidth 8 v := by
  change BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = BitVec.setWidth 8 v
  rw [BitVec.setWidth_setWidth_of_le (BitVec.setWidth 32 v) (by decide),
    BitVec.setWidth_setWidth_of_le v (by decide)]

private theorem int64_raw_toBitVec_previousCounter (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % 18446744073709551616
  exact (Nat.mod_eq_of_lt h).symm

private theorem allowPanic_call_previousCounter {s_call s0 sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  have h1 : allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    unfold allocFailedIn
    rw [htr]
    exact id
  exact allowPanic_frame h1 hm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero int64_raw_toBitVec_previousCounter

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter


/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Previous-Session Version-Skip Tail Proof (`+0x1fd4 → +0x2cfc`)

Proves `overPrevErr_cli_4k_ok` and `overPrevErr_cli_ok` on `tripleRatchetProgAtExt`: compares
`w8 = 4` against `msgVer ≠ 4`, invokes `pqxdh_log_closure`, appends the second
`UnrecognizedMessageVersion` entry at `errsPtr + 48..96` (`errs.len = 2`), drops the decoded
`SessionStructure` at `sp + 0x930`, and exits the 1-element loop to `+0x2cfc`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cond_ne_subs32_4_of_ne {v : BitVec 32} (h : v ≠ 4#32) :
    ConditionHolds CondCode.NE (subsPState32 4#32 v) = true := by
  unfold subsPState32
  rw [conditionHolds_ne_subs32, bne_iff_ne]
  exact Ne.symm h

private theorem spA90_344_ver_split_eq (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 344 = (∃∗ e5 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e3 : BitVec 64,
      ∃∗ e2 : BitVec 64, ∃∗ ua9c : BitVec 32, ∃∗ ua98 : BitVec 32, ∃∗ ua90 : BitVec 64,
      ((sp + 0xa90#64) ↦₆₄ ua90) ∗ ((sp + 0xa98#64) ↦₃₂ ua98) ∗ ((sp + 0xa9c#64) ↦₃₂ ua9c) ∗
      ((sp + 0xaa0#64) ↦₆₄ e2) ∗ ((sp + 0xaa8#64) ↦₆₄ e3) ∗
      ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
      memRegion (sp + 0xac0#64) 296) := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 4) (k := 332) (b' := sp + 0xa9c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa9c#64) (n := 4) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0xa90#64), ProofLib.memRegion_four (sp + 0xa98#64),
      ProofLib.memRegion_four (sp + 0xa9c#64), ProofLib.memRegion_eight (sp + 0xaa0#64),
      ProofLib.memRegion_eight (sp + 0xaa8#64), ProofLib.memRegion_eight (sp + 0xab0#64),
      ProofLib.memRegion_eight (sp + 0xab8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem pointsTo32_pair_spA98 (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0xa98#64) ↦₃₂ lo) ∗ ((sp + 0xa9c#64) ↦₃₂ hi)) = ((sp + 0xa98#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0xa9c#64 = (sp + 0xa98#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

private theorem spA90_344_fold (sp w0 w1 e2 e3 e4 e5 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ w0) ∗ ((sp + 0xa98#64) ↦₆₄ w1) ∗ ((sp + 0xaa0#64) ↦₆₄ e2) ∗
    ((sp + 0xaa8#64) ↦₆₄ e3) ∗ ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
    memRegion (sp + 0xac0#64) 296 ⊢
    memRegion (sp + 0xa90#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 8) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))))

private theorem errs144_split_eq_at48 (errsPtr : BitVec 64) :
    memRegion (errsPtr + 48#64) 144 = (∃∗ u_e5 : BitVec 64, ∃∗ u_e4 : BitVec 64, ∃∗ u_e3 : BitVec 64,
      ∃∗ u_e2 : BitVec 64, ∃∗ u_e1 : BitVec 64, ∃∗ u_e0 : BitVec 64,
      ((errsPtr + 48#64) ↦₆₄ u_e0) ∗ ((errsPtr + 56#64) ↦₆₄ u_e1) ∗
      ((errsPtr + 64#64) ↦₆₄ u_e2) ∗ ((errsPtr + 72#64) ↦₆₄ u_e3) ∗
      ((errsPtr + 80#64) ↦₆₄ u_e4) ∗ ((errsPtr + 88#64) ↦₆₄ u_e5) ∗
      memRegion (errsPtr + 96#64) 96) := by
  rw [ProofLib.memRegion_split' (b := errsPtr + 48#64) (n := 8) (k := 136) (b' := errsPtr + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 56#64) (n := 8) (k := 128) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 120) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 112) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 104) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 88#64) (n := 8) (k := 96) (b' := errsPtr + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (errsPtr + 48#64), ProofLib.memRegion_eight (errsPtr + 56#64),
      ProofLib.memRegion_eight (errsPtr + 64#64), ProofLib.memRegion_eight (errsPtr + 72#64),
      ProofLib.memRegion_eight (errsPtr + 80#64), ProofLib.memRegion_eight (errsPtr + 88#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem errs48_fold_ver_at48 (errsPtr e2 e3 e4 e5 : BitVec 64) (msgVer ua9c : BitVec 32) :
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) ∗
    ((errsPtr + 64#64) ↦₆₄ e2) ∗ ((errsPtr + 72#64) ↦₆₄ e3) ∗ ((errsPtr + 80#64) ↦₆₄ e4) ∗
    ((errsPtr + 88#64) ↦₆₄ e5) ⊢
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
    memRegion (errsPtr + 60#64) 36 := by
  have hpair : ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) =
      ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ ((errsPtr + 60#64) ↦₃₂ ua9c) := by
    have h60 : errsPtr + 60#64 = (errsPtr + 56#64) + 4#64 := by bv_omega
    rw [h60, ← pointsTo32_pair]
  rw [hpair, sepConj_assoc,
      ProofLib.memRegion_split' (b := errsPtr + 60#64) (n := 4) (k := 32) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 24) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 16) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 8) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

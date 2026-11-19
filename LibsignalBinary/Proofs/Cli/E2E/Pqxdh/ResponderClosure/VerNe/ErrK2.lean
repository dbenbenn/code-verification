/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PrevBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp

/-!
# Version-Mismatch Epilogue over One Archived Session

Proves `overK2Seg_cli_4k_ok` and `overK2Seg_cli_ok` (`+0x359c → retAddr` on
`tripleRatchetProgAtExt`), freeing the inner `Vec<u8>` buffer (when `c ≠ 0`) and outer
`Vec<Vec<u8>>` buffer at `prevPtr`, writing the 48-byte `Result::Err` payload to `outPtr`, and
restoring all callee-saved GPRs and `calleeSavedVRegs`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem entails_replace_sub_k2 {P A A' F Q : SepProp}
    (hA : A ⊢ A') (hP : P = A ∗ F) (hQ : Q = A' ∗ F) : P ⊢ Q := by
  rw [hP, hQ]; exact sepConj_mono_left hA

private theorem prevVecAt_one_drop_split_k2 (A : RustAlloc) (r cap q : BitVec 64)
    (enc : List (BitVec 8)) (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64,
        ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗
        HdrP r cap q 1#64 ∗
        A.live q (cap.toNat * 24) 8 ∗
        (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat) ∗
        memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
  have h0 : prevVecAt A r cap q [enc] ⊢
      HdrP r cap q 1#64 ∗ ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
      A.live q (cap.toNat * 24) 8 ∗
      (∃∗ c : BitVec 64, ∃∗ p : BitVec 64, (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗ (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat)) ∗
      memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
    rw [prevVecAt_one_eq A r cap q enc hcap]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
    unfold vecU8
    refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
    refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
    refine Entails.trans (vecU8At_entails_dealloc A q c p enc) ?_
    unfold vecHeader
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    refine sepConj_mono (pointsTo64_entails_memRegion (q + 16#64) _) ?_
    exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.refl _)
  refine Entails.trans h0 ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
  refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
  exact Entails.of_eq (by ac_rfl)

private theorem prevVec1_outer_merge_k2 (q c p : BitVec 64) (cap : Nat)
    (h : 1 ≤ cap ∧ cap * 24 < 2 ^ 63) :
    (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗ memRegion (q + 24#64) ((cap - 1) * 24) ⊢
      memRegion q (cap * 24) := by
  have h24 : (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
      memRegion (q + 24#64) ((cap - 1) * 24) ⊢
      memRegion q 24 ∗ memRegion (q + 24#64) ((cap - 1) * 24) := by
    rw [ProofLib.memRegion_split' (b := q) (b' := q + 8#64) (N := 24) (n := 8) (k := 16)
          rfl rfl (by decide),
        ProofLib.memRegion_split' (b := q + 8#64) (b' := q + 16#64) (N := 16) (n := 8) (k := 8)
          rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
    exact sepConj_mono (pointsTo64_entails_memRegion q c)
      (sepConj_mono (pointsTo64_entails_memRegion (q + 8#64) p) (Entails.refl _))
  refine Entails.trans h24 ?_
  rw [ProofLib.memRegion_split' (b := q) (b' := q + 24#64) (N := cap * 24) (n := 24)
        (k := (cap - 1) * 24) (by omega) rfl (by omega)]
  exact Entails.refl _

private theorem prevVecAt_one_cap0_false_k2 (A : RustAlloc) (r q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A r 0#64 q [enc] ⊢ ⌜False⌝ := by
  rw [prevVecAt_eq]
  unfold RustHeap.vecBuf
  rw [sepConj_left_comm]
  refine Entails.pure_left fun ⟨hlen, _, _⟩ => ?_
  nomatch hlen

private theorem sepWP_exists_elim_k2 {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

private theorem sepWP_pure_elim_k2 {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s P post) :
    SepWP prog pc s (⌜φ⌝ ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

/-! ## Case split (`c = 0` vs `c ≠ 0`) and main theorems -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Tail
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Glue

/-!
# Stage P2 Matched-Session `Some ik` Check and Remote-Identity Match Branch

Proves `stageP2_matched_ok_10cc_to_1778` (`+0x10cc → +0x1778` on equal remote identity keys),
`stageP2_matched_094c_some_to_10cc` (`+0x094c → +0x10cc`), and `stageP2_matched_094c_match`
(`+0x094c → +0x1778` when `recSt.remoteIdentity = some remIdKey`), plus `PublicKeyEqOkExt32` lifts.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Glue
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem coro_298_split_two (coroPtr w : BitVec 64) :
    ((coroPtr + 0x298#64) ↦₆₄ (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32))) ⊢
      ∃∗ hi : BitVec 32,
        ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
        ((coroPtr + 0x29c#64) ↦₃₂ hi) := by
  let packed := (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32))
  refine Entails.sepExists_right (packed.extractLsb' 32 32) ?_
  rw [pointsTo64_split32 (coroPtr + 0x298#64) packed, opkPacked_two_lo32 w]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

private theorem cap_add_one_ne_zero {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    c + 1#64 ≠ 0#64 := by
  bv_omega

private theorem sepExists_pull_left {α : Type} (P : α → SepProp) {R : SepProp}
    {R' : α → SepProp} (h : ∀ a, P a ∗ R = R' a) :
    (∃∗ a, P a) ∗ R = ∃∗ a, R' a := by
  rw [sepExists_sepConj_left]
  exact congrArg sepExists (funext h)

private theorem sepExists_push_right {α : Type} (L : SepProp) {Q Q' : α → SepProp}
    (h : ∀ a, L ∗ Q a = Q' a) :
    L ∗ (∃∗ a, Q a) = ∃∗ a, Q' a := by
  rw [sepExists_sepConj_right]
  exact congrArg sepExists (funext h)

private theorem sepExists_pull2 {α₁ α₂ : Type} (P₁ : α₁ → SepProp) (P₂ : α₂ → SepProp) :
    (∃∗ a₁, P₁ a₁) ∗ (∃∗ a₂, P₂ a₂) = ∃∗ a₁, ∃∗ a₂, P₁ a₁ ∗ P₂ a₂ :=
  sepExists_pull_left P₁ fun a₁ => sepExists_push_right (P₁ a₁) fun _ => rfl

private theorem sepExists_pull3 {α₁ α₂ α₃ : Type}
    (P₁ : α₁ → SepProp) (P₂ : α₂ → SepProp) (P₃ : α₃ → SepProp) :
    (∃∗ a₁, P₁ a₁) ∗ (∃∗ a₂, P₂ a₂) ∗ (∃∗ a₃, P₃ a₃) =
      ∃∗ a₁, ∃∗ a₂, ∃∗ a₃, P₁ a₁ ∗ P₂ a₂ ∗ P₃ a₃ := by
  rw [sepExists_pull2 P₂ P₃]
  exact sepExists_pull_left P₁ fun a₁ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ => rfl

private theorem sepExists_pull4 {α₁ α₂ α₃ α₄ : Type}
    (P₁ : α₁ → SepProp) (P₂ : α₂ → SepProp) (P₃ : α₃ → SepProp) (P₄ : α₄ → SepProp) :
    (∃∗ a₁, P₁ a₁) ∗ (∃∗ a₂, P₂ a₂) ∗ (∃∗ a₃, P₃ a₃) ∗ (∃∗ a₄, P₄ a₄) =
      ∃∗ a₁, ∃∗ a₂, ∃∗ a₃, ∃∗ a₄, P₁ a₁ ∗ P₂ a₂ ∗ P₃ a₃ ∗ P₄ a₄ := by
  rw [sepExists_pull3 P₂ P₃ P₄]
  exact sepExists_pull_left P₁ fun a₁ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ => rfl

private theorem sepExists_pull5 {α₁ α₂ α₃ α₄ α₅ : Type}
    (P₁ : α₁ → SepProp) (P₂ : α₂ → SepProp) (P₃ : α₃ → SepProp)
    (P₄ : α₄ → SepProp) (P₅ : α₅ → SepProp) :
    (∃∗ a₁, P₁ a₁) ∗ (∃∗ a₂, P₂ a₂) ∗ (∃∗ a₃, P₃ a₃) ∗
    (∃∗ a₄, P₄ a₄) ∗ (∃∗ a₅, P₅ a₅) =
      ∃∗ a₁, ∃∗ a₂, ∃∗ a₃, ∃∗ a₄, ∃∗ a₅,
        P₁ a₁ ∗ P₂ a₂ ∗ P₃ a₃ ∗ P₄ a₄ ∗ P₅ a₅ := by
  rw [sepExists_pull4 P₂ P₃ P₄ P₅]
  exact sepExists_pull_left P₁ fun a₁ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ => rfl

private theorem sepExists_pull6 {α₁ α₂ α₃ α₄ α₅ α₆ : Type}
    (P₁ : α₁ → SepProp) (P₂ : α₂ → SepProp) (P₃ : α₃ → SepProp)
    (P₄ : α₄ → SepProp) (P₅ : α₅ → SepProp) (P₆ : α₆ → SepProp) :
    (∃∗ a₁, P₁ a₁) ∗ (∃∗ a₂, P₂ a₂) ∗ (∃∗ a₃, P₃ a₃) ∗
    (∃∗ a₄, P₄ a₄) ∗ (∃∗ a₅, P₅ a₅) ∗ (∃∗ a₆, P₆ a₆) =
    ∃∗ a₁, ∃∗ a₂, ∃∗ a₃, ∃∗ a₄, ∃∗ a₅, ∃∗ a₆,
      P₁ a₁ ∗ P₂ a₂ ∗ P₃ a₃ ∗ P₄ a₄ ∗ P₅ a₅ ∗ P₆ a₆ := by
  rw [sepExists_pull5 P₂ P₃ P₄ P₅ P₆]
  exact sepExists_pull_left P₁ fun a₁ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ =>
    sepExists_push_right (P₁ a₁) fun _ => rfl

theorem memRegion_32_eq_chunks32 (base : BitVec 64) :
    memRegion base 32 =
      ∃∗ w0 : BitVec 32, ∃∗ h1 : BitVec 16,
      ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64, ∃∗ q4 : BitVec 64, ∃∗ h5 : BitVec 16,
        chunks32At base w0 h1 q2 q3 q4 h5 := by
  unfold chunks32At
  rw [ProofLib.memRegion_split base 4 28 (by decide),
      ProofLib.memRegion_split (base + 4#64) 2 26 (by decide),
      ProofLib.memRegion_split (base + 4#64 + 2#64) 8 18 (by decide),
      ProofLib.memRegion_split (base + 4#64 + 2#64 + 8#64) 8 10 (by decide),
      ProofLib.memRegion_split (base + 4#64 + 2#64 + 8#64 + 8#64) 8 2 (by decide),
      ProofLib.memRegion_four, ProofLib.memRegion_two,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_two]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepExists_pull6 _ _ _ _ _ _

theorem chunks32_entails_memRegion_32 (base : BitVec 64)
    (w0 : BitVec 32) (h1 : BitVec 16) (q2 q3 q4 : BitVec 64) (h5 : BitVec 16) :
    chunks32At base w0 h1 q2 q3 q4 h5 ⊢ memRegion base 32 := by
  rw [memRegion_32_eq_chunks32 base]
  exact Entails.sepExists_right w0 (Entails.sepExists_right h1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right h5 (Entails.refl _))))))

theorem rem34_bytes_entails_memRegion34 (sp : BitVec 64) (b0 b1 : BitVec 8)
    (w0 : BitVec 32) (h1 : BitVec 16) (q2 q3 q4 : BitVec 64) (h5 : BitVec 16) :
    ((sp + 0x3e0#64) ↦₈ b0) ∗ ((sp + 0x3e1#64) ↦₈ b1) ∗
      chunks32At (sp + 0x3e2#64) w0 h1 q2 q3 q4 h5 ⊢
      memRegion (sp + 0x3e0#64) 34 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 1 33 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 1#64) 1 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepConj_mono (pointsTo8_entails_memRegion _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion _ b1)
      (chunks32_entails_memRegion_32 _ w0 h1 q2 q3 q4 h5))

theorem memRegion_34_split_32_2 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 34 =
      memRegion (sp + 0x3e0#64) 32 ∗ memRegion (sp + 0x400#64) 2 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 32 2 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_34_split_24_10 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 34 =
      memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 24 10 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_920_6_split (sp : BitVec 64) :
    memRegion (sp + 0x920#64) 6 =
      ∃∗ u_920 : BitVec 32, ∃∗ u_924 : BitVec 16,
        ((sp + 0x920#64) ↦₃₂ u_920) ∗ ((sp + 0x924#64) ↦₁₆ u_924) := by
  rw [ProofLib.memRegion_split (sp + 0x920#64) 4 2 (by decide),
      ProofLib.memRegion_four, ProofLib.memRegion_two]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepExists_pull2 _ _

theorem memRegion_920_6_join (sp : BitVec 64) (u_920 : BitVec 32) (u_924 : BitVec 16) :
    ((sp + 0x920#64) ↦₃₂ u_920) ∗ ((sp + 0x924#64) ↦₁₆ u_924) ⊢
      memRegion (sp + 0x920#64) 6 := by
  rw [memRegion_920_6_split sp]
  exact Entails.sepExists_right u_920 (Entails.sepExists_right u_924 (Entails.refl _))

theorem memRegion_a90_48_split_10_38 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 48 =
      (∃∗ u_a90 : BitVec 64, ∃∗ u_a98 : BitVec 16,
        ((sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((sp + 0xa98#64) ↦₁₆ u_a98)) ∗
      memRegion (sp + 0xa9a#64) 38 := by
  rw [ProofLib.memRegion_split (sp + 0xa90#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64) 2 38 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_two]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
  rw [sepExists_pull2]

theorem memRegion_a90_48_join_10_38 (sp : BitVec 64) (u_a90 : BitVec 64) (u_a98 : BitVec 16) :
    ((sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((sp + 0xa98#64) ↦₁₆ u_a98) ∗
      memRegion (sp + 0xa9a#64) 38 ⊢
      memRegion (sp + 0xa90#64) 48 := by
  rw [memRegion_a90_48_split_10_38 sp, ← sepConj_assoc]
  exact sepConj_mono_left
    (Entails.sepExists_right u_a90 (Entails.sepExists_right u_a98 (Entails.refl _)))

theorem remoteIdentityOkAt_none_eq (sp : BitVec 64) :
    Getters.remoteIdentityOkAt (sp + 0x3e0#64) none =
      ((sp + 0x3e0#64) ↦₈ 0#8) ∗ ((sp + 0x3e1#64) ↦₈ 0#8) ∗
      memRegion (sp + 0x3e2#64) 32 := by
  dsimp only [Getters.remoteIdentityOkAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem remoteIdentityOkAt_some_eq (sp : BitVec 64) (ik : IdentityKey) :
    Getters.remoteIdentityOkAt (sp + 0x3e0#64) (some ik) =
      ((sp + 0x3e0#64) ↦₈ 0#8) ∗ ((sp + 0x3e1#64) ↦₈ 1#8) ∗
      ((sp + 0x3e2#64) ↦ₛ ik.publicKey.bytes.toList) := by
  dsimp only [Getters.remoteIdentityOkAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem stack_root_to_pkEq_ext32 (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - Getters.publicKeyEqStackExt) ∗
      stackAt sp Getters.publicKeyEqStackExt :=
  stackAt_split_of_le sp rootStack Getters.publicKeyEqStackExt (by decide) hn

theorem blackBoxSat_withPanics_m2 {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    HookSat (Rust.withPanics ext) "subtle::black_box::<u8>"
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec32 := by
  obtain ⟨fn, hfn, hok⟩ := h_bb
  have hnp : Rust.isPanicSymbol "subtle::black_box::<u8>" = false := by simp [Rust.isPanicSymbol]
  refine ⟨fn, ?_, hok⟩
  simpa [Rust.withPanics, hnp] using hfn

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

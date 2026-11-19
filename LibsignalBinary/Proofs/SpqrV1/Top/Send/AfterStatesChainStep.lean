/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.States1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: `send_key` Error Cleanup & `Chain::into_pb` Steps

Symbolic execution of `<Chain>::send_key` error cleanup (`0x31600 -> 0x31a3c`), `ChainPB` 9-word
relocation bridges, and `<Chain>::into_pb` pre/post steps (`0x316dc..0x317fc`) in
`spqr::send::<HookRng>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem stackAt_spqrSendCallee_eq_dropStack32 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack32) ∗
        stackAt sp dropStack32 :=
  ProofLib.stackAt_split_bottom sp dropStack32
    (spqrSendCalleeStack - dropStack32) (by decide)

theorem stackAt_spqrSendCallee_eq_allocHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  ProofLib.stackAt_split_bottom sp allocHookStack
    (spqrSendCalleeStack - allocHookStack) (by decide)

theorem stackAt_spqrSendCallee_eq_dropStackPoly64 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStackPoly64) ∗
        stackAt sp dropStackPoly64 :=
  ProofLib.stackAt_split_bottom sp dropStackPoly64
    (spqrSendCalleeStack - dropStackPoly64) (by decide)

theorem sendKeyErrAt_entails_words (out : BitVec 64) (err : Error) :
    sendKeyErrAt out err ⊢
      (out ↦₆₄ 1#64) ∗
      (∃∗ d0 : BitVec 32, (out + 0x08#64) ↦₃₂ d0) ∗
      (∃∗ d1 : BitVec 32, (out + 0x0c#64) ↦₃₂ d1) ∗
      (∃∗ w2 : BitVec 64, (out + 0x10#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (out + 0x18#64) ↦₆₄ w3) ∗
      memRegion (out + 0x20#64) 8 := by
  unfold sendKeyErrAt
  have h24 :
      (match err with
       | .sendKeyEpochDecreased s e =>
         ((out + 16#64) ↦₆₄ s) ∗ ((out + 24#64) ↦₆₄ e) ∗ memRegion (out + 32#64) 8
       | .epochOutOfRange e =>
         ((out + 16#64) ↦₆₄ e) ∗ memRegion (out + 24#64) 16
       | _ => memRegion (out + 16#64) 24) ⊢
      (∃∗ w2 : BitVec 64, (out + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (out + 24#64) ↦₆₄ w3) ∗
      memRegion (out + 32#64) 8 := by
    rw [← ProofLib.memRegion_eight (out + 16#64), ← ProofLib.memRegion_eight (out + 24#64),
        ← ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8)
            (b' := out + 32#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16)
            (b' := out + 24#64) rfl (by bv_omega) (by decide)]
    cases err <;> try exact Entails.refl _
    · rw [ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16)
            (b' := out + 24#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
    · rw [ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16)
            (b' := out + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8)
            (b' := out + 32#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  have h8 :
      ((out + 8#64) ↦₈ spqrErrorTag err) ∗ memRegion (out + 9#64) 7 ⊢
        (∃∗ d0 : BitVec 32, (out + 8#64) ↦₃₂ d0) ∗
        (∃∗ d1 : BitVec 32, (out + 12#64) ↦₃₂ d1) := by
    rw [← ProofLib.memRegion_four (out + 8#64), ← ProofLib.memRegion_four (out + 12#64),
        ← ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 4)
            (b' := out + 12#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 7)
            (b' := out + 9#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)
  rw [← sepConj_assoc ((out + 8#64) ↦₈ spqrErrorTag err),
      ← sepConj_assoc (∃∗ d0 : BitVec 32, (out + 8#64) ↦₃₂ d0)]
  exact sepConj_mono_right (sepConj_mono h8 h24)

theorem sendKeyErrSlot_entails_memRegion_40 (out : BitVec 64)
    (w0 : BitVec 64) (d0 d1 : BitVec 32) (w2 w3 : BitVec 64) :
    (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₃₂ d0) ∗ ((out + 12#64) ↦₃₂ d1) ∗
      ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ memRegion (out + 32#64) 8 ⊢
      memRegion out 40 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 32) (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 28) (b' := out + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 24) (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 16) (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 8) (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))))

theorem add_emp_arrayAt_nil (A : RustAlloc) (P : SepProp) (ptr : BitVec 64) :
    P ⊢ arrayAt (chainEpoch A) 112 ptr [] ∗ P := by
  dsimp only [arrayAt]
  exact Entails.of_eq (emp_sepConj P).symm

theorem links_len_or_grow_ok {len cap : Nat}
    (hle : len ≤ cap) (hbnd : len ≤ 2 ^ 54) :
    len < cap ∨ max (2 * cap) 4 * chainEpochSize < 2 ^ 63 := by
  by_cases hlt : len < cap
  · exact Or.inl hlt
  · right
    change max (2 * cap) 4 * 112 < 2 ^ 63
    omega

theorem list_length_le_sum_map_add {α : Type} (f : α → Nat) (c : Nat) (hc : 1 ≤ c) :
    ∀ l : List α, l.length ≤ (l.map (fun x => f x + c)).sum
  | [] => by simp
  | x :: xs => by
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := list_length_le_sum_map_add f c hc xs
    omega

theorem chain_links_length_le_rawChain (c : Chain) :
    c.links.length ≤ StateSize.rawChain c.intoPb := by
  have h1 := list_length_le_sum_map_add StateSize.rawChainEpoch 200 (by decide)
    c.intoPb.links
  have hlen : c.intoPb.links.length = c.links.length := by
    unfold Chain.intoPb
    simp
  rw [hlen] at h1
  unfold StateSize.rawChain
  omega

theorem memRegion_80_words10 (a : BitVec 64) :
    memRegion a 80 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (a + 48#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (a + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (a + 64#64) ↦₆₄ w8) ∗
      (∃∗ w9 : BitVec 64, (a + 72#64) ↦₆₄ w9) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 64) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 56) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 48) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 40) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 32) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 24) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 16) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 8) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
      ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 56#64),
      ProofLib.memRegion_eight (a + 64#64), ProofLib.memRegion_eight (a + 72#64)]

theorem words10_to_memRegion_80 (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
    ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
    ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
    ((a + 72#64) ↦₆₄ w9) ⊢ memRegion a 80 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 64) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 56) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 48) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 40) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 32) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 24) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 16) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 8) (b' := a + 72#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _)))))))))

/-- Pure relation characterizing the last two 64-bit words (`+0x40` and `+0x48`) of `ChainPB`:
    `params : Option ChainParamsPB` (`12` bytes at `+0x40..+0x4c`) and `direction : BitVec 32`
    (`4` bytes at `+0x4c..+0x50`). -/
@[expose] def chainPBParamsDirWords (pb : ChainPB) (w8 w9 : BitVec 64) : Prop :=
  match pb.params with
  | none => ∃ p0 p1 : BitVec 32, w8 = p0 ++ 0#32 ∧ w9 = pb.direction ++ p1
  | some cp => w8 = cp.maxJump ++ 1#32 ∧ w9 = pb.direction ++ cp.maxOooKeys

/-- Address-independent heap part of `Top.ChainFrom.chainPBAt A g a pb`. -/
@[expose] def chainPBHeapAt (A : RustAlloc) (g : ChainPBGhost) (pb : ChainPB) : SepProp :=
  ⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
      g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
    DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot

theorem optChainParamsDir_entails_words2 (a : BitVec 64) (pb : ChainPB) :
    optChainParamsPBAt (a + 0x40#64) pb.params ∗ ((a + 0x4c#64) ↦₃₂ pb.direction) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
        ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
        ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) := by
  have ha64 : a + 0x40#64 = a + 64#64 := rfl
  have ha68 : a + 64#64 + 4#64 = a + 68#64 := by bv_omega
  have ha72 : a + 64#64 + 8#64 = a + 72#64 := by bv_omega
  have ha76 : a + 0x4c#64 = a + 72#64 + 4#64 := by bv_omega
  cases hparams : pb.params with
  | none =>
    unfold chainPBParamsDirWords
    rw [hparams]
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha76,
        ProofLib.memRegion_split' (b := a + 68#64) (n := 4) (k := 4)
          (b' := a + 72#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_four (a + 68#64),
        ProofLib.memRegion_four (a + 72#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro p1
    apply Entails.sepExists_elim; intro p0
    refine Entails.sepExists_right (p0 ++ 0#32) (Entails.sepExists_right (pb.direction ++ p1) ?_)
    refine Entails.pure_right ⟨p0, p1, rfl, rfl⟩ ?_
    have h1 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 0#32 p0
    rw [ha68] at h1
    have h2 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) p1 pb.direction
    rw [← h1, ← h2]
    exact Entails.of_eq (by ac_rfl)
  | some cp =>
    unfold chainPBParamsDirWords
    rw [hparams]
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha72, ha76]
    refine Entails.sepExists_right (cp.maxJump ++ 1#32)
      (Entails.sepExists_right (pb.direction ++ cp.maxOooKeys) ?_)
    refine Entails.pure_right ⟨rfl, rfl⟩ ?_
    have h1 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 1#32 cp.maxJump
    rw [ha68] at h1
    have h2 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) cp.maxOooKeys pb.direction
    rw [← h1, ← h2]
    exact Entails.of_eq (by ac_rfl)

theorem words2_entails_optChainParamsDir (a : BitVec 64) (pb : ChainPB) (w8 w9 : BitVec 64)
    (hw : chainPBParamsDirWords pb w8 w9) :
    ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ⊢
      optChainParamsPBAt (a + 0x40#64) pb.params ∗ ((a + 0x4c#64) ↦₃₂ pb.direction) := by
  have ha64 : a + 0x40#64 = a + 64#64 := rfl
  have ha68 : a + 64#64 + 4#64 = a + 68#64 := by bv_omega
  have ha72 : a + 64#64 + 8#64 = a + 72#64 := by bv_omega
  have ha76 : a + 0x4c#64 = a + 72#64 + 4#64 := by bv_omega
  unfold chainPBParamsDirWords at hw
  cases hparams : pb.params with
  | none =>
    rw [hparams] at hw
    rcases hw with ⟨p0, p1, rfl, rfl⟩
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha76,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 0#32 p0,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) p1 pb.direction,
        ha68,
        ProofLib.memRegion_split' (b := a + 68#64) (n := 4) (k := 4)
          (b' := a + 72#64) rfl (by bv_omega) (by decide)]
    have hp0 := ProofLib.pointsTo32_entails_memRegion (a + 68#64) p0
    have hp1 := ProofLib.pointsTo32_entails_memRegion (a + 72#64) p1
    refine Entails.trans (Entails.of_eq (show
      (((a + 64#64) ↦₃₂ 0#32) ∗ ((a + 68#64) ↦₃₂ p0)) ∗
        (((a + 72#64) ↦₃₂ p1) ∗ ((a + 72#64 + 4#64) ↦₃₂ pb.direction)) =
      (((a + 64#64) ↦₃₂ 0#32) ∗ (((a + 68#64) ↦₃₂ p0) ∗ ((a + 72#64) ↦₃₂ p1))) ∗
        ((a + 72#64 + 4#64) ↦₃₂ pb.direction) by ac_rfl)) ?_
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono hp0 hp1))
  | some cp =>
    rw [hparams] at hw
    rcases hw with ⟨rfl, rfl⟩
    dsimp only [optChainParamsPBAt]
    rw [ha64, ha68, ha72, ha76,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 64#64) 1#32 cp.maxJump,
        ← ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 72#64) cp.maxOooKeys pb.direction,
        ha68]
    exact Entails.of_eq (by ac_rfl)

/-- Unpack `ChainFromNorm.chainPBRestAt A g a pb` into 9 64-bit words at `a + 8..a + 72` plus
    `chainPBHeapAt A g pb`. -/
theorem chainPBRestAt_entails_words9 (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB) :
    ChainFromNorm.chainPBRestAt A g a pb ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
        ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
        ((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
        ((a + 64#64) ↦₆₄ w8) ∗
        ((a + 72#64) ↦₆₄ w9) ∗
        chainPBHeapAt A g pb := by
  have hvec : vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot =
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot := by
    unfold vecU8At vecHeader DecodeState.vecU8Heap
    have ha32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 0x18#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    ac_rfl
  unfold ChainFromNorm.chainPBRestAt chainPBHeapAt
  rw [hvec]
  apply Entails.pure_left; intro hlen
  have h1 := ChainFromNorm.vecBuf_linksCap_ne_noneCap A g.linksCap g.linksPtr (g.epochs.zip pb.links)
  have h2 := optChainParamsDir_entails_words2 a pb
  refine Entails.trans (Entails.of_eq (show
    ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      (((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) ∗
      ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
      optChainParamsPBAt (a + 0x40#64) pb.params ∗
      ((a + 0x4c#64) ↦₃₂ pb.direction) =
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      (optChainParamsPBAt (a + 0x40#64) pb.params ∗ ((a + 0x4c#64) ↦₃₂ pb.direction)) ∗
      (((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w9
  apply Entails.pure_left; intro hcap_ne
  refine Entails.trans (Entails.of_eq (show
    vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
      ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
      DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot =
    ⌜chainPBParamsDirWords pb w8 w9⌝ ∗
      vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
      (((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
        ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
        ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) by ac_rfl)) ?_
  apply Entails.pure_left; intro hw
  refine Entails.sepExists_right w8 (Entails.sepExists_right w9 ?_)
  refine Entails.pure_right hw ?_
  have hpure :
      vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) ⊢
        ⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
          vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A) g.linksCap g.linksPtr (g.epochs.zip pb.links) :=
    Entails.pure_right ⟨hlen, hcap_ne⟩ (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hpure) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Repack 9 64-bit words at `a + 8..a + 72` plus `chainPBHeapAt A g pb` into
    `ChainFromNorm.chainPBRestAt A g a pb`. -/
theorem words9_entails_chainPBRestAt (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB)
    (w8 w9 : BitVec 64) (hw : chainPBParamsDirWords pb w8 w9) :
    ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
      ((a + 64#64) ↦₆₄ w8) ∗
      ((a + 72#64) ↦₆₄ w9) ∗
      chainPBHeapAt A g pb ⊢
      ChainFromNorm.chainPBRestAt A g a pb := by
  have hvec : vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot =
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot := by
    unfold vecU8At vecHeader DecodeState.vecU8Heap
    have ha32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 0x18#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    ac_rfl
  unfold ChainFromNorm.chainPBRestAt chainPBHeapAt
  rw [hvec]
  have h2 := words2_entails_optChainParamsDir a pb w8 w9 hw
  refine Entails.trans (Entails.of_eq (show
    ((a + 8#64) ↦₆₄ g.linksPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
      ((a + 48#64) ↦₆₄ pb.currentEpoch) ∗
      ((a + 56#64) ↦₆₄ pb.sendEpoch) ∗
      ((a + 64#64) ↦₆₄ w8) ∗
      ((a + 72#64) ↦₆₄ w9) ∗
      (⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
        vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
          g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
        DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) =
    ⌜g.epochs.length = pb.links.length ∧ g.linksCap ≠ noneCap⌝ ∗
      (((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
      (((a + 8#64) ↦₆₄ g.linksPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        vecBuf A chainEpochSize chainEpochAlign (chainEpochPBAt A)
          g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
        (((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗
          ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
          DecodeState.vecU8Heap A g.nextRoot.cap g.nextRoot.ptr pb.nextRoot) ∗
        ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
        ((a + 0x38#64) ↦₆₄ pb.sendEpoch)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  refine Entails.pure_right hlen ?_
  refine Entails.trans (sepConj_mono_left h2) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_72_words9 (a : BitVec 64) :
    memRegion a 72 =
      (∃∗ w1 : BitVec 64, a ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 8#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 16#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 24#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 32#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (a + 40#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (a + 48#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (a + 56#64) ↦₆₄ w8) ∗
      (∃∗ w9 : BitVec 64, (a + 64#64) ↦₆₄ w9) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 64) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 56) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 48) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 40) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 32) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 24) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 16) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 8) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
      ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 56#64),
      ProofLib.memRegion_eight (a + 64#64)]

theorem words9_to_memRegion_72 (a w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗
    ((a + 24#64) ↦₆₄ w4) ∗ ((a + 32#64) ↦₆₄ w5) ∗ ((a + 40#64) ↦₆₄ w6) ∗
    ((a + 48#64) ↦₆₄ w7) ∗ ((a + 56#64) ↦₆₄ w8) ∗ ((a + 64#64) ↦₆₄ w9) ⊢ memRegion a 72 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 64) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 56) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 48) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 40) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 32) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 24) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 16) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 8) (b' := a + 64#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _))))))))

/-- Representation of `chainPb : Option ChainPB` at `0x317fc`, split between register `x25`
    (holding the first 8-byte word `links.cap` / `noneCap`) and the 72-byte stack slot at `a_slot`
    (`sp + 0xd90#64`):
    * `none`: `⌜x25 = noneCap⌝ ∗ memRegion a_slot 72`
    * `some ch`: `∃∗ g : ChainPBGhost, ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap⌝ ∗ ChainFromNorm.chainPBRestAt A g (a_slot - 8#64) ch` -/
@[expose] def optChainPBRegSlotAt (A : RustAlloc) (a_slot : BitVec 64) (x25 : BitVec 64) :
    Option ChainPB → SepProp
  | none => ⌜x25 = noneCap⌝ ∗ memRegion a_slot 72
  | some ch =>
    ∃∗ g : ChainPBGhost,
      ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap⌝ ∗
        ChainFromNorm.chainPBRestAt A g (a_slot - 8#64) ch

theorem sendKeyOkSlot_entails_words11 (A : RustAlloc) (a : BitVec 64) (idx : BitVec 32) (msgKey : Bytes) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4 ∗
      vecU8 A (a + 16#64) msgKey) ∗ memRegion (a + 40#64) 48 ⊢
      ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
      ∃∗ d1 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64,
      ∃∗ d7 : BitVec 64, ∃∗ d8 : BitVec 64, ∃∗ d9 : BitVec 64, ∃∗ d10 : BitVec 64,
        (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ d1) ∗
        ((a + 16#64) ↦₆₄ mkCap) ∗ ((a + 24#64) ↦₆₄ mkPtr) ∗
        ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗
        ((a + 56#64) ↦₆₄ d7) ∗ ((a + 64#64) ↦₆₄ d8) ∗
        ((a + 72#64) ↦₆₄ d9) ∗ ((a + 80#64) ↦₆₄ d10) ∗
        DecodeState.vecU8Heap A mkCap mkPtr msgKey := by
  have hd1 : ((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4 ⊢
      ∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1 := by
    rw [← ProofLib.memRegion_eight (a + 8#64),
        ProofLib.memRegion_split' (b := a + 8#64) (n := 4) (k := 4)
          (b' := a + 12#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)
  have hvec : ∀ c p : BitVec 64,
      vecU8At A (a + 16#64) c p msgKey =
        ((a + 16#64) ↦₆₄ c) ∗ ((a + 24#64) ↦₆₄ p) ∗
        ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        DecodeState.vecU8Heap A c p msgKey := by
    intro c p
    unfold vecU8At vecHeader DecodeState.vecU8Heap
    have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
    have ha32 : a + 16#64 + 16#64 = a + 32#64 := by bv_omega
    rw [ha24, ha32]
    ac_rfl
  rw [ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 40) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 32) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 24) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 16) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 8) (k := 8) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 40#64), ProofLib.memRegion_eight (a + 48#64),
      ProofLib.memRegion_eight (a + 56#64), ProofLib.memRegion_eight (a + 64#64),
      ProofLib.memRegion_eight (a + 72#64), ProofLib.memRegion_eight (a + 80#64)]
  unfold vecU8
  simp only [hvec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d10
  apply Entails.sepExists_elim; intro d9
  apply Entails.sepExists_elim; intro d8
  apply Entails.sepExists_elim; intro d7
  apply Entails.sepExists_elim; intro d6
  apply Entails.sepExists_elim; intro d5
  apply Entails.sepExists_elim; intro mkCap
  apply Entails.sepExists_elim; intro mkPtr
  refine Entails.trans (Entails.of_eq (show
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4 ∗
      ((a + 16#64) ↦₆₄ mkCap) ∗ ((a + 24#64) ↦₆₄ mkPtr) ∗
      ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
      DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
      ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗
      ((a + 56#64) ↦₆₄ d7) ∗ ((a + 64#64) ↦₆₄ d8) ∗
      ((a + 72#64) ↦₆₄ d9) ∗ ((a + 80#64) ↦₆₄ d10) =
    (((a + 8#64) ↦₃₂ idx) ∗ memRegion (a + 12#64) 4) ∗
      ((a ↦₆₄ 0#64) ∗
        ((a + 16#64) ↦₆₄ mkCap) ∗ ((a + 24#64) ↦₆₄ mkPtr) ∗
        ((a + 32#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗
        ((a + 56#64) ↦₆₄ d7) ∗ ((a + 64#64) ↦₆₄ d8) ∗
        ((a + 72#64) ↦₆₄ d9) ∗ ((a + 80#64) ↦₆₄ d10) ∗
        DecodeState.vecU8Heap A mkCap mkPtr msgKey) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hd1) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro d1
  refine Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr
    (Entails.sepExists_right d1 (Entails.sepExists_right d5
    (Entails.sepExists_right d6 (Entails.sepExists_right d7
    (Entails.sepExists_right d8 (Entails.sepExists_right d9
    (Entails.sepExists_right d10 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send

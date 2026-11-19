/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.RelocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Relocatable Epilogue and Panic Tails for `Chain::clone [local#3]` (Block `468`)

Program-generic `protoChainCloneSpec` lifts (`chainClone_of_protoChainClone_gen`,
`senderChainClone_of_chainClone_gen`) and Block `468` epilogue (`+736..+796`) / allocation-failure
panic-tail (`+800..+860`) lemmas under `[LibsignalPlacement]`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.ChainClone3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  BS5.sp_setPC_pre BS5.sp_setMem_setPC_pre
  BS5.readReg64_setPC_pre BS5.readReg64_setMem_setPC_pre
  BS5.readReg32_setPC_pre BS5.readReg32_setMem_setPC_pre
  BS5.readReg_setPC_pre BS5.readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## 1. Program-Generic `protoChainCloneSpec` -> `chainCloneSpec` / `senderChainCloneSpec` Bridges -/

theorem chainClone_of_protoChainClone_gen {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec A)) :
    subroutine_ok prog entry (chainCloneSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [chainCloneSpec, chainAt_eq_protoChainAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  set P_rc : Prop := x.gc.1.srk.bytes.length = 33 ∧ x.gc.1.priv.bytes = []
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec A).pre x s0 ∗ (⌜P_rc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome x (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hoom⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hpure_front :
        sf.mem ⊨
          ⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_rc⌝ ∗ R) =
          (⌜P_rc⌝ ∗
            (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hsrk33, hpriv_nil⟩, hrest_f⟩
    simp only [chainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv', hkeys'⟩, ?_⟩
    rw [chainAt_eq_protoChainAt A (g', x.gc.2) x.dst, chainAt_eq_protoChainAt A x.gc x.src]
    have hsrk33' : g'.srk.bytes.length = 33 := by rw [hsrk', hsrk33]
    have hpriv_nil' : g'.priv.bytes = [] := hpriv'.trans hpriv_nil
    set P_rc' : Prop := g'.srk.bytes.length = 33 ∧ g'.priv.bytes = []
    change sf.mem ⊨
      (⌜P_rc'⌝ ∗ protoChainAt A (g', x.gc.2) x.dst) ∗
      (⌜P_rc⌝ ∗ protoChainAt A x.gc x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_rc'⌝ ∗ protoChainAt A (g', x.gc.2) x.dst) ∗
          (⌜P_rc⌝ ∗ protoChainAt A x.gc x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_rc'⌝ ∗ (⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [protoChainCloneSpec, chainCloneSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · right; right; left
    exact ⟨code, hexit, by
      simp only [protoChainCloneSpec] at hpost
      exact False.elim (not_satisfies_false_sepConj hpost)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem senderChainClone_of_chainClone_gen {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hbridge : ∀ A a g sc, optSenderChainAt A a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
      protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a)
    (hclone : subroutine_ok prog entry (protoChainCloneSpec A)) :
    subroutine_ok prog entry (senderChainCloneSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [senderChainCloneSpec, hbridge, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  let P_sc : Prop :=
    x.g.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
      x.g.srk.bytes.length = 33
  let gc_init : ChainGhost × ReceiverChain :=
    (⟨x.g.srk, x.g.priv, x.g.mkCap, x.g.mkPtr, [], x.g.ck⟩,
      ⟨x.sc.ratchetKey.publicKey, some x.sc.chainKey, []⟩)
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc_init x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A gc_init x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc_init x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A gc_init x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec A).pre ⟨x.dst, x.src, gc_init⟩ s0 ∗ (⌜P_sc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome ⟨x.dst, x.src, gc_init⟩ (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hoom⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hkeys_nil : g'.keys = [] := List.eq_nil_of_length_eq_zero hkeys'
    have hpure_front :
        sf.mem ⊨
          ⌜P_sc⌝ ∗
          (protoChainAt A (g', gc_init.2) x.dst ∗ protoChainAt A gc_init x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A (g', gc_init.2) x.dst ∗ protoChainAt A gc_init x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_sc⌝ ∗ R) =
          (⌜P_sc⌝ ∗
            (protoChainAt A (g', gc_init.2) x.dst ∗ protoChainAt A gc_init x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
    let sg' : SenderChainGhost := ⟨g'.srk, g'.priv, g'.mkCap, g'.mkPtr, g'.ck⟩
    have hg'_eq : g' = ⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩ := by
      cases g'; dsimp [sg'] at hkeys_nil ⊢; subst hkeys_nil; rfl
    rw [hg'_eq] at hrest_f
    simp only [senderChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sg', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv'⟩, ?_⟩
    rw [hbridge A x.dst sg' x.sc, hbridge A x.src x.g x.sc]
    have hpriv'_eq : sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList :=
      hpriv'.trans hpriv_eq
    have hsrk33' : sg'.srk.bytes.length = 33 := by
      change g'.srk.bytes.length = 33
      rw [hsrk', hsrk33]
    let P_sc' : Prop :=
      sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
        sg'.srk.bytes.length = 33
    let gc' : ChainGhost × ReceiverChain :=
      (⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩, gc_init.2)
    change sf.mem ⊨
      (⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
      (⌜P_sc⌝ ∗ protoChainAt A gc_init x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
          (⌜P_sc⌝ ∗ protoChainAt A gc_init x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_sc'⌝ ∗ (⌜P_sc⌝ ∗
          (protoChainAt A gc' x.dst ∗ protoChainAt A gc_init x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [protoChainCloneSpec, senderChainCloneSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · right; right; left
    exact ⟨code, hexit, by
      simp only [protoChainCloneSpec] at hpost
      exact False.elim (not_satisfies_false_sepConj hpost)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Epilogue & Panic Tail Lemmas on Block `468` -/

end CryptoVerification.LibsignalTripleRatchet.ChainClone3

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.DagCertCheckC

/-!
# Verified 158-Node Concrete Evaluation DAG Certificate (`dag_nodes_ok`)
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

section Step1DagSafeMemo

open DY.Libsignal.Refinement (canonicalVariation sha256CompressFunction)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain TRSignalMsg trHonestWireMsg messageVersion spqrA2B spqrB2A lit litByte
   hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys kdfCk computeMac)
open DY.Libsignal.Composed.Refinement
  (TrialCtx trialTerms trWireBytes litOf clamp ofByteArray node opaqueNode spqrKeyNode
   concretizeLit concretizeConcat concretizeDhPk concretizeDh concretizeKdf
   concretizeSym concretizeTrunc concretizeTrWire concretizeKemEncap concretizeKemSS
   concretizeKemPk concretizeVk concretizeSign
   concretizeSpqrInit concretizeSpqrChainKey concretizeSpqrSendState
   concretizeSpqrSendKey concretizeSpqrSendMsg concretizeSpqrRecvState concretizeSpqrRecvKey
   sigFuns spqrFuns allFuns)
open ByteSpecs (hmacWith)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (compLookupPub compLookupDh compAesPerm compKyberEncaps bytesToNat)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compI0_publicKey compI0_agreement compI0_aesEncrypt compI0_kyberEncaps compLookupDh_comm)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots serialize_localTR_memo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)


private theorem all_range'_get {p : Nat → Bool} :
    ∀ {s n x : Nat}, (List.range' s n).all p = true → s ≤ x → x < s + n → p x = true
  | _, 0, _, _, _, h2 => absurd h2 (by omega)
  | s, n + 1, x, hall, h1, h2 => by
    simp only [List.range', List.all_cons, Bool.and_eq_true] at hall
    by_cases hx : x = s
    · subst hx; exact hall.1
    · exact all_range'_get hall.2 (by omega) (by omega)

theorem dag_nodes_ok : ∀ id < dagSize, compDagNodeOk dagOp dagBytes id = true := by
  intro id hid
  change id < 199 at hid
  by_cases h25 : id < 25
  · exact all_range'_get dag_nodes_ok_0_25 (Nat.zero_le _) h25
  · by_cases he25 : id = 25
    · subst he25; exact dag_nodes_ok_25
    · by_cases h70 : id < 70
      · exact all_range'_get dag_nodes_ok_26_44 (by omega) (by omega)
      · by_cases he70 : id = 70
        · subst he70; exact dag_nodes_ok_70
        · by_cases he71 : id = 71
          · subst he71; exact dag_nodes_ok_71
          · by_cases h86 : id < 86
            · exact all_range'_get dag_nodes_ok_72_14 (by omega) (by omega)
            · by_cases h100 : id < 100
              · exact all_range'_get dag_nodes_ok_86_14 (by omega) (by omega)
              · by_cases h116 : id < 116
                · exact all_range'_get dag_nodes_ok_100_16 (by omega) (by omega)
                · by_cases h132 : id < 132
                  · exact all_range'_get dag_nodes_ok_116_16 (by omega) (by omega)
                  · by_cases h148 : id < 148
                    · exact all_range'_get dag_nodes_ok_132_16 (by omega) (by omega)
                    · by_cases h165 : id < 165
                      · exact all_range'_get dag_nodes_ok_148_17 (by omega) (by omega)
                      · by_cases h182 : id < 182
                        · exact all_range'_get dag_nodes_ok_165_17 (by omega) (by omega)
                        · exact all_range'_get dag_nodes_ok_182_17 (by omega) (by omega)

private theorem dagBucketMemOk_all : ∀ i < dagSize, dagBucketMemOk i = true := by
  intro i hi
  change i < 199 at hi
  by_cases h25 : i < 25
  · exact all_range'_get dag_buckets_mem_0_25 (Nat.zero_le _) h25
  · by_cases he25 : i = 25
    · subst he25; exact dag_buckets_mem_25
    · by_cases h70 : i < 70
      · exact all_range'_get dag_buckets_mem_26_44 (by omega) (by omega)
      · by_cases he70 : i = 70
        · subst he70; exact dag_buckets_mem_70
        · by_cases h100 : i < 100
          · exact all_range'_get dag_buckets_mem_71_29 (by omega) (by omega)
          · by_cases h133 : i < 133
            · exact all_range'_get dag_buckets_mem_100_33 (by omega) (by omega)
            · by_cases h166 : i < 166
              · exact all_range'_get dag_buckets_mem_133_33 (by omega) (by omega)
              · exact all_range'_get dag_buckets_mem_166_33 (by omega) (by omega)

theorem dag_buckets_mem : ∀ i < dagSize,
    (i, (dagOp i).isAI, packBytesKey (dagBytes i)) ∈ dagBucket (bytesBucketIdx (dagBytes i)) := by
  intro i hi
  have h := dagBucketMemOk_all i hi
  unfold dagBucketMemOk at h
  obtain ⟨e, he, hd⟩ := List.any_eq_true.mp h
  rw [of_decide_eq_true hd] at he
  exact he

theorem dag_buckets_ok : ∀ b < 256, bucketNoCollision (dagBucket b) = true := by
  intro b hb
  by_cases h128 : b < 128
  · exact all_range'_get dag_buckets_ok_0_128 (Nat.zero_le _) h128
  · exact all_range'_get dag_buckets_ok_128_128 (by omega) (by omega)

theorem dag_no_collision : ∀ id₁ < dagSize, ∀ id₂ < dagSize,
    ((dagOp id₁).isAI = true ∨ (dagOp id₂).isAI = true) →
    dagBytes id₁ = dagBytes id₂ → id₁ = id₂ := by
  intro id₁ h₁ id₂ h₂ hai hbs
  have hm₁ := dag_buckets_mem id₁ h₁
  have hm₂ := dag_buckets_mem id₂ h₂
  rw [← hbs] at hm₂
  have hb_lt : bytesBucketIdx (dagBytes id₁) < 256 := BitVec.isLt _
  exact bucketNoCollision_sound (dag_buckets_ok _ hb_lt) hm₁ hm₂ hai

theorem dag_no_ai_0100 {id : Nat} (hid : id < dagSize) (hai : (dagOp id).isAI = true) :
    ¬ ([0x01#8, 0x00#8] <:+ dagBytes id) := by
  have hok := List.all_eq_true.mp dag_no_ai_0100_bool id (List.mem_range.mpr hid)
  rw [hai, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hok
  rintro ⟨pfx, heq⟩
  have h2 : 2 ≤ (dagBytes id).length := by rw [← heq, List.length_append]; simp
  have hd : (dagBytes id).drop ((dagBytes id).length - 2) = [0x01#8, 0x00#8] := by
    rw [← heq]
    have hsub : (pfx ++ [0x01#8, 0x00#8]).length - 2 = pfx.length := by
      rw [List.length_append]; simp
    rw [hsub, List.drop_append, List.drop_eq_nil_of_le (Nat.le_refl pfx.length),
      List.nil_append, Nat.sub_self, List.drop_zero]
  unfold endsWith0100 at hok
  simp [h2, hd] at hok

def SafeEntry (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (pts : List DY.Bytes) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ x.2.2.length < 8) ∨
  (assumedInjective x.1 = false ∧
    (x.2.2.length < 8 ∨
     (38 ≤ x.2.2.length ∧ x.2.2.drop (x.2.2.length - 2) = [0x01#8, 0x00#8]))) ∨
  (∃ id < dagSize, x.2.1 = dagShape opOf dagSize id ∧ x.2.2 = bytesOf id ∧
    (assumedInjective x.1 = true → (opOf id).isAI = true))

def SafeMemo (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List DY.Bytes) (b : DY.Bytes) : Prop :=
  ∀ x ∈ (gamma' compI0 S g b).memo, SafeEntry dagSize opOf bytesOf pts x

def TermAt (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List DY.Bytes) (b : DY.Bytes) (id : Nat) : Prop :=
  id < dagSize ∧
  (gamma' compI0 S g b).bytes = bytesOf id ∧
  (gamma' compI0 S g b).shape = dagShape opOf dagSize id ∧
  SafeMemo dagSize opOf bytesOf S g pts b

theorem TermAt.safeMemo {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {b : DY.Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    SafeMemo dagSize opOf bytesOf S g pts b :=
  h.2.2.2

theorem TermAt.gamma_eq {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {b : DY.Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    gamma compI0 S g b = bytesOf id :=
  h.2.1

def SafeEntry2 (pts : List DY.Bytes) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ x.2.2.length < 8) ∨
  (assumedInjective x.1 = false ∧
    (x.2.2.length < 8 ∨ [0x01#8, 0x00#8] <:+ x.2.2)) ∨
  (∃ id < dagSize, x.2.1 = dagShape dagOp dagSize id ∧ x.2.2 = dagBytes id ∧
    (assumedInjective x.1 = true → (dagOp id).isAI = true))

def SafeMemo2 (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List DY.Bytes) (b : DY.Bytes) : Prop :=
  ∀ x ∈ (gamma' compI0 S g b).memo, SafeEntry2 pts x

abbrev DagSafeMemo := SafeMemo dagSize dagOp dagBytes
abbrev DagTermAt := TermAt dagSize dagOp dagBytes

theorem safeMemo_toSafeMemo2 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {b : DY.Bytes}
    (h : DagSafeMemo S g pts b) : SafeMemo2 S g pts b := by
  intro x hx
  rcases h x hx with hpt | ⟨hnai, hlt | ⟨_, hd⟩⟩ | hdag
  · exact Or.inl hpt
  · exact Or.inr (Or.inl ⟨hnai, Or.inl hlt⟩)
  · refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨x.2.2.take (x.2.2.length - 2), ?_⟩⟩)
    rw [← hd, List.take_append_drop]
  · exact Or.inr (Or.inr hdag)

theorem safeMemo2_mono_pts {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts₁ pts₂ : List DY.Bytes} {b : DY.Bytes}
    (hsub : ∀ p ∈ pts₁, p ∈ pts₂) (h : SafeMemo2 S g pts₁ b) : SafeMemo2 S g pts₂ b := by
  intro x hx
  rcases h x hx with ⟨hm, hl⟩ | hsp | hdag
  · exact Or.inl ⟨hsub _ hm, hl⟩
  · exact Or.inr (Or.inl hsp)
  · exact Or.inr (Or.inr hdag)

theorem not_memoCollisionOn_of_safeMemo2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop}
    {tr : ExecTrace} {vis : List VisEntry} {newTerms newPts : List DY.Bytes}
    (hPref : ∀ t ∈ prefixTerms r tr vis,
      SafeMemo2 S g (plaintextTerms vis ++ newPts) t)
    (hNew : ∀ t ∈ newTerms,
      SafeMemo2 S g (plaintextTerms vis ++ newPts) t) :
    ¬ MemoCollisionOn compI0 r S g known tr vis newTerms newPts := by
  rintro ⟨x₁, hx₁_raw, x₂, hx₂_raw, hsh, hinj, hpt₁, hpt₂, hbytes⟩
  set pts := plaintextTerms vis ++ newPts
  have hs₁ : SafeEntry2 pts x₁ := by
    obtain ⟨t₁, ht₁, hmx₁⟩ := List.mem_flatMap.mp hx₁_raw
    exact hNew t₁ ht₁ x₁ hmx₁
  have hs₂ : SafeEntry2 pts x₂ := by
    rcases List.mem_append.mp hx₂_raw with hx₂_p | hx₂_n
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_p
      exact hPref t₂ ht₂ x₂ hmx₂
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_n
      exact hNew t₂ ht₂ x₂ hmx₂
  have hAi8 : ∀ {id : Nat}, id < dagSize → (dagOp id).isAI = true → 8 ≤ (dagBytes id).length := by
    intro id hid hai
    have hn := dag_nodes_ok id hid
    unfold compDagNodeOk at hn
    simp only [hai, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact hn.2.1
  rcases hs₁ with ⟨hm₁, hlen₁⟩ | ⟨hnai₁, hni₁⟩ | ⟨id₁, hid₁, hsh₁, hb₁, hai₁⟩
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · exact (hpt₁ hm₁).1 hm₂
    · have := (hpt₁ hm₁).2.1; rw [hnai₂] at this; cases this
    · have h8 := hAi8 hid₂ (hai₂ (hpt₁ hm₁).2.1)
      rw [hbytes, hb₂] at hlen₁; omega
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · have := (hpt₂ hm₂).2.1; rw [hnai₁] at this; cases this
    · rcases hinj with h | h <;> simp_all
    · have hai₂' : (dagOp id₂).isAI = true := by
        rcases hinj with h | h
        · rw [hnai₁] at h; cases h
        · exact hai₂ h
      rcases hni₁ with hlt₁ | hsfx₁
      · have h8 := hAi8 hid₂ hai₂'; rw [hbytes, hb₂] at hlt₁; omega
      · rw [hbytes, hb₂] at hsfx₁; exact dag_no_ai_0100 hid₂ hai₂' hsfx₁
  · rcases hs₂ with ⟨hm₂, hlen₂⟩ | ⟨hnai₂, hni₂⟩ | ⟨id₂, hid₂, hsh₂, hb₂, hai₂⟩
    · have h8 := hAi8 hid₁ (hai₁ (hpt₂ hm₂).2.1)
      rw [← hbytes, hb₁] at hlen₂; omega
    · have hai₁' : (dagOp id₁).isAI = true := by
        rcases hinj with h | h
        · exact hai₁ h
        · rw [hnai₂] at h; cases h
      rcases hni₂ with hlt₂ | hsfx₂
      · have h8 := hAi8 hid₁ hai₁'; rw [← hbytes, hb₁] at hlt₂; omega
      · rw [← hbytes, hb₁] at hsfx₂; exact dag_no_ai_0100 hid₁ hai₁' hsfx₂
    · have hor : (dagOp id₁).isAI = true ∨ (dagOp id₂).isAI = true := by
        rcases hinj with h | h
        · exact Or.inl (hai₁ h)
        · exact Or.inr (hai₂ h)
      have hideq := dag_no_collision id₁ hid₁ id₂ hid₂ hor (hb₁.symm.trans (hbytes.trans hb₂))
      subst hideq
      exact hsh (hsh₁.trans hsh₂.symm)


end Step1DagSafeMemo

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

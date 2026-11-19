/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.ReductionsQueries
import Computational.Proofs.Fig8SchemeBridge

public section

set_option autoImplicit false

open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (OptSkippedLenLe SkippedLenLe fsFullImpl_skippedLenLe fsReveal_ext_skippedLenLe hooksFS_vrInv_skippedLenLe implE_hooksFS_ext_skippedLenLe initFSRaw_skippedLenLe skippedLenLe_init vRecv_hooksFS_fsClamp_fsAtomicB_eq vSend_hooksFS_fsClamp_fsAtomicB_eq)
open CryptoGames (AEADScheme CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.SM.Construction (FSState FSVROkStep Header Mode PartyState SchemeAdversary corrE_fsClamp_eq fsClamp fsFullImpl fsReveal_ext_snd_fromAEADPRG fst_mem_support_of_mem_support_simulateQ_run hooksFS hooksFS_vrInv_fromAEADPRG implE_ext_snd_fromAEADPRG implE_fsClamp_eq initFS initFSRaw initFSRaw_inv initFSRaw_vrInv_fromAEADPRG isQueryBoundP_initFSRaw_dec polUni12 receiverState_reach_of_isDecQuery_bound redFSPrivUni redFSPrivUniCoin runFSUni vSend_ext_snd vSend_fsClamp_eq)
open CryptoGames.SM.Construction.ReductionsQueries (QB qb_abortE qb_bind0 qb_deliverE_one qb_get qb_injectE_one qb_liftH qb_modify qb_mono qb_pure qb_reveal_zero qb_vSend_zero)
open CryptoGames.SM.Engine (EState Policy RSReach SMEngineInv SMVRInv VP abortE challE coinsE commitE corrE deliverE engRun implE implE_inv implE_vrInv injectE run_liftH_bind transmitE)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (AllPartiesInv badSendMsg_chall_false badSendMsg_query_bind_step badSendMsg_transmit_false hooksFS_localCKAAgree localPartyInv_mkParties mode_cfg_challMsg simulateQ_implE_localCKA_eq)

namespace Computational.Proofs.SessionCostedFig8.Stage2Swap

open OracleComp OracleSpec
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)

theorem runFSUni_dhSchemeFb_eq {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (lam : Pt) (Δcka qep t : ℕ) (b : Bool)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    runFSUni (dhSchemeFb Dh) prng fs lam Δcka qep t b A =
      runFSUni (dhScheme Dh) prng fs lam Δcka qep t b A := by
  unfold runFSUni engRun
  have hInit : initFS (dhSchemeFb Dh) prng fs lam ⟨false, none, t⟩ 0 =
      initFS (dhScheme Dh) prng fs lam ⟨false, none, t⟩ 0 := rfl
  rw [hInit]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · have hAll : AllPartiesInv (M := M) (E := Header Pt × E)
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := b }, h := h } := by
      unfold initFS at hmem
      simp only [StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨kr, _, kc, _, ⟨⟨σ, k, sid⟩, _⟩, _, ⟨ext, _⟩, _, hmem⟩ := hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some.injEq] at hmem
      rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
      exact localPartyInv_mkParties Dh kc σ
        (if ext then none else some (fs.initSender k))
        (if ext then none else some (fs.initReceiver k))
    dsimp only
    exact congrArg (· >>= fun res => pure (some res))
      (simulateQ_implE_localCKA_eq (hooksFS_localCKAAgree Dh prng fs Δcka ⟨false, none, t⟩ 0)
        (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Config.priv t) (polUni12 Δcka t) A _ hAll)

private lemma implE_hooksFS_pol_fsClamp_fsAtomicB_eq
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 B_q q' Δcka qep : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSState Pt RSt (BitVec 256) I (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (ℕ × LibsignalCiphertextWithSalt32)))
    (t : (CryptoGames.SM.spec (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
      (St := PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) (.inr t) = false)
    (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q (q' + 1) es.g)
    (hLen : SMVRInv (fun _ => OptSkippedLenLe) B_q (q' + 1) es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - (q' + 1)) (es.h.ext.map Prod.snd))
    (hExtLen : OptSkippedLenLe (es.h.ext.map Prod.snd)) :
    (implE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg π (.inr t)).run es =
      (implE (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        Δcka mo j) (2 + Δcka) qep maxForwardJumps mo.cfg π (.inr t)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · by_cases hdoom : π.leakDoom es.g s₁ = true
        · simp [hdoom]
        · have hm : atomicShortPubB m.1 = true :=
            badSendMsg_transmit_false
              (ok := fun (x : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB x.1) hBad
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
          exact congrArg (· >>= _)
            (vSend_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 Δcka mo j
              s₁ P (s₁.st P) m none r hm es.h)
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es = (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    obtain ⟨hm₀, hm₁⟩ := badSendMsg_chall_false hBad
    have hm : atomicShortPubB (if es.g.b then m₁ else m₀).1 = true := by
      cases es.g.b <;> simp [hm₀, hm₁]
    unfold challE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · by_cases hch : (!(s₁.safeCh (2 + Δcka) P) ||
            !((mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch P))) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : π.leakDoom es.g s₁ = true
          · simp [hdoom]
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, mode_cfg_challMsg, Option.getD_none,
              run_liftH_bind,
              vSend_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 Δcka mo j
                s₁ P (s₁.st P) (if es.g.b then m₁ else m₀) (some (m₀, m₁)) r hm es.h]
  · change (deliverE _ maxForwardJumps mo.cfg (P, c)).run es =
      (deliverE _ maxForwardJumps mo.cfg (P, c)).run es
    have hCommit :
        commitE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j) =
          commitE (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j) := by
      unfold commitE hooksFS; rfl
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind,
          vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 (B_q - (q' + 1))
            Δcka mo j hkB es.g P (es.g.st P) c (some r) es.h (hVR P) (hLen P) hExt hExtLen, hCommit]
  · change (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es
    have hCommit :
        commitE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j) =
          commitE (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j) := by
      unfold commitE hooksFS; rfl
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
        !(es.g.safeInj (2 + Δcka))) = true
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 (B_q - (q' + 1))
          Δcka mo j hkB es.g P (es.g.st P) c none es.h (hVR P) (hLen P) hExt hExtLen, hCommit]
  · change (corrE _ π P).run es = (corrE _ π P).run es
    unfold corrE hooksFS; rfl

private lemma implE_pol_fsClamp_eq
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
        (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (t : (CryptoGames.SM.spec (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q (q + 1) es.g)
    (hExt : FSVROkStep maxSkip (B_q - (q + 1)) (es.h.ext.map Prod.snd)) :
    (implE (hooksFS cka prng (fsClamp B (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg π (.inr t)).run es =
      (implE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg π (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE; rw [vSend_fsClamp_eq]
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es = (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    unfold challE; rw [vSend_fsClamp_eq]
  · change (deliverE _ maxSkip mo.cfg (P, c)).run es = (deliverE _ maxSkip mo.cfg (P, c)).run es
    exact implE_fsClamp_eq cka prng ae G maxSkip B B_q q Δcka qep mo j hB es
      (.inl (.inl (.inr (P, c)))) hVR hExt
  · change (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es
    exact implE_fsClamp_eq cka prng ae G maxSkip B B_q q Δcka qep mo j hB es
      (.inl (.inr (P, c))) hVR hExt
  · change (corrE _ π P).run es = (corrE _ π P).run es
    rw [corrE_fsClamp_eq]

private lemma implE_pol_ext_snd_fromAEADPRG
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
        (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (CryptoGames.SM.spec (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
        ((implE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip mo.cfg π (.inr q)).run es)).run st),
      FSVROkStep maxSkip (k + 1) (z.1.2.h.ext.map Prod.snd) := by
  have hExt1 : FSVROkStep maxSkip (k + 1) (es.h.ext.map Prod.snd) := hExt.mono (Nat.le_succ k)
  intro z hz
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((transmitE _ _ _ _ (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hep] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt1
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka mo j s₁ P (s₁.st P) m none r es.h (vsRes, h') hvs
          rcases vsRes with _ | ⟨st', ct⟩ <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt1)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((challE _ _ _ _ _ (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((CryptoGames.SM.Construction.Mode.cfg (M := M) mo).challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt1
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : π.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt1
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h (vsRes, h') hvs
            rcases vsRes with _ | ⟨st', ct⟩ <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt1)
  · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((deliverE _ maxSkip mo.cfg (P, c)).run es)).run st) at hz
    exact implE_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka qep mo j es
      (.inl (.inl (.inr (P, c)))) st hVR hExt hSt z hz
  · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es)).run st) at hz
    exact implE_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka qep mo j es
      (.inl (.inr (P, c))) st hVR hExt hSt z hz
  · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((corrE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j) π P).run es)).run st) at hz
    unfold corrE abortE at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt1
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hExt1
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
        have hExt' := fsReveal_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
        rcases revRes with _ | stP <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz;
           subst hz; exact hExt'.mono (Nat.le_succ k))

private lemma implE_pol_hooksFS_ext_skippedLenLe
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
        (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (CryptoGames.SM.spec (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : OptSkippedLenLe (es.h.ext.map Prod.snd))
    (hSt : SkippedLenLe st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
        ((implE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip mo.cfg π (.inr q)).run es)).run st),
      OptSkippedLenLe (z.1.2.h.ext.map Prod.snd) := by
  intro z hz
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((transmitE _ _ _ _ (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [hep] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka mo j s₁ P (s₁.st P) m none r es.h (vsRes, h') hvs
          rcases vsRes with _ | ⟨stP, ct⟩ <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((challE _ _ _ _ _ (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((CryptoGames.SM.Construction.Mode.cfg (M := M) mo).challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : π.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h (vsRes, h') hvs
            rcases vsRes with _ | ⟨stP, ct⟩ <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt)
  · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((deliverE _ maxSkip mo.cfg (P, c)).run es)).run st) at hz
    exact implE_hooksFS_ext_skippedLenLe cka prng ae G maxSkip k Δcka qep mo j es
      (.inl (.inl (.inr (P, c)))) st hVR hExt hSt z hz
  · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es)).run st) at hz
    exact implE_hooksFS_ext_skippedLenLe cka prng ae G maxSkip k Δcka qep mo j es
      (.inl (.inr (P, c))) st hVR hExt hSt z hz
  · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((corrE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        π P).run es)).run st) at hz
    unfold corrE abortE at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hExt
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
        have hExt' := fsReveal_ext_skippedLenLe cka prng ae G maxSkip Δcka mo j
          es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
        rcases revRes with _ | stP <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz;
           subst hz; exact hExt')

private lemma qb_implE_pol_inr_one
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    {Q : (unifSpec + CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain → Prop}
    [DecidablePred Q]
    (hQu : ∀ n, ¬ Q (.inl n))
    (hQt : ∀ a m, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))))
    (hQch : ∀ a m₀ m₁, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))))
    (hQcs : ¬ Q (.inr (.inl (.inl (.inl (.inr ()))))))
    (hQcr : ¬ Q (.inr (.inl (.inl (.inr ())))))
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (t : (CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain) :
    CryptoGames.SM.Construction.ReductionsQueries.QB Q
      (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg π (.inr t)) 1 := by
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | q) | q) | P
  · refine qb_mono ?_ (Nat.zero_le 1)
    change QB Q (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep π (P, m, r)) 0
    unfold transmitE
    refine qb_bind0 qb_get fun es => ?_
    by_cases h1 : (es.abort || es.g.win) = true
    · simp only [h1, ↓reduceIte]; exact qb_pure none 0
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => exact qb_pure none 0
      | some s₁ =>
        by_cases h2 : π.leakDoom es.g s₁ = true
        · simp only [h2, ↓reduceIte]; exact qb_bind0 qb_abortE fun _ => qb_pure none 0
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          refine qb_bind0
            (qb_liftH (qb_vSend_zero hQu hQt hQch hQcs cka prng fs Δcka mo j s₁ P (s₁.st P) m none r))
            fun res => ?_
          cases res with
          | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
          | some sc => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some sc.2) 0
  · refine qb_mono ?_ (Nat.zero_le 1)
    change QB Q (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg π (P, m₀, m₁, r)) 0
    unfold challE
    refine qb_bind0 qb_get fun es => ?_
    by_cases h1 : (es.abort || es.g.win) = true
    · simp only [h1, ↓reduceIte]; exact qb_pure none 0
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => exact qb_pure none 0
      | some s₁ =>
        by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !(mo.cfg (M := M)).challAllowedIn (s₁.epoch P)) = true
        · simp only [h2, ↓reduceIte]; exact qb_pure none 0
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : π.leakDoom es.g s₁ = true
          · simp only [h3, ↓reduceIte]; exact qb_bind0 qb_abortE fun _ => qb_pure none 0
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            refine qb_bind0
              (qb_liftH (qb_vSend_zero hQu hQt hQch hQcs cka prng fs Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r))
              fun res => ?_
            cases res with
            | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
            | some sc => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some sc.2) 0
  · exact qb_deliverE_one hQu cka prng fs Δcka mo j q
  · exact qb_injectE_one hQu cka prng fs Δcka qep mo j q
  · refine qb_mono ?_ (Nat.zero_le 1)
    change QB Q (corrE (hooksFS cka prng fs Δcka mo j) π P) 0
    unfold corrE
    refine qb_bind0 qb_get fun es => ?_
    by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowed P) = true
    · simp only [h1, ↓reduceIte]; exact qb_pure none 0
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) = true
      · simp only [h2, ↓reduceIte]; exact qb_bind0 qb_abortE fun _ => qb_pure none 0
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine qb_bind0 (qb_liftH (qb_reveal_zero hQcs hQcr cka prng fs Δcka mo j es.g P (es.g.st P)))
          fun res => ?_
        cases res with
        | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
        | some st => exact qb_bind0 (qb_modify _) fun _ => qb_pure (some st) 0

private lemma simulateQ_implE_pol_fsClamp_fsAtomicB_eq
    {KC Γ CCoins Pt I KR RSt α : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L B B0 B_q q Δcka qep : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) α}
    (hoa : oa.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q)
    (hSendOk : oa.IsQueryBoundP
      (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
        (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSState Pt RSt (BitVec 256) I (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (ℕ × LibsignalCiphertextWithSalt32)))
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q q es.g)
    (hLen : SMVRInv (fun _ => OptSkippedLenLe) B_q q es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - q) (es.h.ext.map Prod.snd))
    (hExtLen : OptSkippedLenLe (es.h.ext.map Prod.snd))
    (hSt : RSReach maxForwardJumps (B_q - q) st.receiverState)
    (hStLen : SkippedLenLe st.receiverState) :
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (implE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg π) oa).run es)).run st =
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (implE (hooksFS cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg π) oa).run es)).run st := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  induction oa using OracleComp.inductionOn generalizing q es st with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ := badSendMsg_query_bind_step (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hInl1 :
          (implE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg π (.inl n)).run es =
            (coinsE n).run es := rfl
      have hInl2 :
          (implE (hooksFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg π (.inl n)).run es =
            (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      obtain ⟨_, _, _, rfl⟩ := hmem1
      have hQbCoins := CryptoGames.SM.Construction.ReductionsQueries.qb_coinsE
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) n es'
      have hSt' : RSReach maxForwardJumps (B_q - q) st'.receiverState := by
        simpa using receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps
          hQbCoins st hSt ((u, es'), st') hmem
      have hStLen' : SkippedLenLe st'.receiverState :=
        fsFullImpl_skippedLenLe ae G maxForwardJumps ((coinsE n).run es') st hStLen
          ((u, es'), st') hmem
      exact ih u q (hmx u) (hSendMx u) es' st' hInv hVR hLen hExt hExtLen hSt' hStLen'
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < q := hq0.resolve_left (by decide)
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hStep1 := implE_hooksFS_pol_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf
        B B0 B_q q' Δcka qep mo π j hB0 es t_sm hBad hVR hLen hExt hExtLen
      have hStep2 :
          (implE (hooksFS cka prng
              (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg π (.inr t_sm)).run es =
            (implE (hooksFS cka prng
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg π (.inr t_sm)).run es :=
        implE_pol_fsClamp_eq cka prng ae G maxForwardJumps B B_q q' Δcka qep mo π j hB es t_sm hVR hExt
      rw [hStep1, hStep2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      have hInv' := implE_inv
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        mo.cfg π es t_sm hInv (u, es') hmem1
      have hVR' := implE_vrInv
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        (hooksFS_vrInv_fromAEADPRG cka prng ae G maxForwardJumps Δcka mo j)
        mo.cfg π es t_sm hInv hVR (u, es') hmem1
      have hLen' := implE_vrInv
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        (hooksFS_vrInv_skippedLenLe cka prng ae G maxForwardJumps Δcka mo j)
        mo.cfg π es t_sm hInv hLen (u, es') hmem1
      have hBq : B_q - (q' + 1) + 1 ≤ B_q - q' := by have := hInv.1; omega
      have hExt' := (implE_pol_ext_snd_fromAEADPRG cka prng ae G maxForwardJumps (B_q - (q' + 1))
        Δcka qep mo π j es t_sm st (fun P _ _ hv => hVR P _ _ hv) hExt hSt
        ((u, es'), st') hmem).mono hBq
      have hExtLen' := implE_pol_hooksFS_ext_skippedLenLe cka prng ae G maxForwardJumps
        (B_q - (q' + 1)) Δcka qep mo π j es t_sm st (fun P _ _ hv => hVR P _ _ hv)
        hExtLen hStLen ((u, es'), st') hmem
      have hQbStep := qb_implE_pol_inr_one
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (CryptoGames.SM.Construction.ReductionsQueries.hQt_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQch_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQcs_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQcr_QFSDec _ _ Pt _ _)
        cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka qep mo π j t_sm es
      have hSt' := (receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps hQbStep st hSt
        ((u, es'), st') hmem).mono hBq
      have hStLen' := fsFullImpl_skippedLenLe ae G maxForwardJumps _ st hStLen ((u, es'), st') hmem
      exact ih u q' (by simpa using hmx u) (hSendMx u) es' st'
        hInv' hVR' hLen' hExt' hExtLen' hSt' hStLen'

theorem simulateQ_runFSUni_fsClamp_fsAtomicB_eq_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 B_q Δcka qep t : ℕ) (lam : I) (b : Bool)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A)
    (st₀ : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hSt₀ : RSReach maxForwardJumps 0 st₀.receiverState)
    (hStLen₀ : SkippedLenLe st₀.receiverState) :
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      (runFSUni cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep t b A)).run st₀ =
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      (runFSUni cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep t b A)).run st₀ := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  let mo : Mode := ⟨false, none, t⟩
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  unfold runFSUni
  have hRaw : ∀ (fs' : FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)),
      engRun (hooksFS cka prng fs' Δcka mo 0) (2 + Δcka) qep fs'.maxSkip
        (CryptoGames.SM.Config.priv t) (polUni12 Δcka t) (initFS cka prng fs' lam mo 0) {} b A =
        (initFSRaw cka prng fs' lam mo 0 b >>= fun es₀ =>
          (simulateQ (implE (hooksFS cka prng fs' Δcka mo 0) (2 + Δcka) qep fs'.maxSkip
            mo.cfg (polUni12 Δcka t)) A).run es₀ >>= fun res => pure (some res)) := by
    intro fs'
    unfold engRun initFS initFSRaw
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mo, CryptoGames.SM.Construction.Mode.cfg]
    refine bind_congr fun kr => bind_congr fun kc => bind_congr fun ⟨⟨σ, k, sid⟩, h₁⟩ =>
      bind_congr fun ⟨ext, h₂⟩ => ?_
    rfl
  rw [hRaw, hRaw]
  have hInitEq :
      initFSRaw cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam mo 0 b =
        initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo 0 b := by
    unfold initFSRaw fsClamp fsAtomicB; rfl
  have hInitEq2 :
      initFSRaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo 0 b =
        initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo 0 b := by
    unfold initFSRaw lFS; rfl
  rw [hInitEq, hInitEq2, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨es₀, st₁⟩ hmem₀ => ?_
  have hes₀ := fst_mem_support_of_mem_support_simulateQ_run _ _ st₀ hmem₀
  have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
  have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
    Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo 0 b
    hqB hB1 hBB es₀ hes₀
  have ⟨hVR₀, hext₀⟩ := initFSRaw_vrInv_fromAEADPRG cka prng ae G maxForwardJumps lam mo 0 b
    B_q qAdv es₀ hes₀
  have hLen₀ := initFSRaw_skippedLenLe cka prng ae G maxForwardJumps lam mo 0 b B_q qAdv es₀ hes₀
  have hExt₀ : FSVROkStep maxForwardJumps (B_q - qAdv) (es₀.h.ext.map Prod.snd) := by
    simp [hext₀, FSVROkStep]
  have hExtLen₀ : OptSkippedLenLe (es₀.h.ext.map Prod.snd) := by simp [hext₀, OptSkippedLenLe]
  have hSt₁ : RSReach maxForwardJumps (B_q - qAdv) st₁.receiverState :=
    (receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps
      (isQueryBoundP_initFSRaw_dec cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo 0 b)
      st₀ hSt₀ (es₀, st₁) hmem₀).mono (Nat.zero_le _)
  have hStLen₁ : SkippedLenLe st₁.receiverState :=
    fsFullImpl_skippedLenLe ae G maxForwardJumps
      (initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo 0 b) st₀ hStLen₀
      (es₀, st₁) hmem₀
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  have hSim := simulateQ_implE_pol_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf
    (B_q + 1) B B0 B_q qAdv Δcka qep mo (polUni12 Δcka t) 0 hB hB0 hA' hSendOk es₀ st₁
    hInv₀.sm hVR₀ hLen₀ hExt₀ hExtLen₀ hSt₁ hStLen₁
  have hms1 : (fsClamp B (fsAtomicB C ℓ encT idOf B0)).maxSkip = maxForwardJumps := rfl
  have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms1, hms2, hSim]

theorem fsaeadGame_redFSPrivUni_atomic_eq
    {Pt KR RSt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType KR]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivUni (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep t A) =
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivUni (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep t A) := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  unfold CryptoGames.FSAEAD.game redFSPrivUni
  refine bind_congr fun b => bind_congr fun k => ?_
  rw [runFSUni_dhSchemeFb_eq Dh prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep t false A]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_runFSUni_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf
    B B0 B_q Δcka qep t lam false hB hB0 A qAdv hA hqB hSendOk
    (CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b)
    (CryptoGames.SM.Engine.RSReach.init ae G maxForwardJumps k) (skippedLenLe_init ae G maxForwardJumps k)]

theorem fsaeadGame_redFSPrivUniCoin_atomic_eq
    {Pt KR RSt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType KR]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivUniCoin (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep t A) =
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivUniCoin (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep t A) := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  unfold CryptoGames.FSAEAD.game redFSPrivUniCoin
  refine bind_congr fun b => bind_congr fun k => ?_
  rw [runFSUni_dhSchemeFb_eq Dh prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep t false A]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_runFSUni_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf
    B B0 B_q Δcka qep t lam false hB hB0 A qAdv hA hqB hSendOk
    (CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b)
    (CryptoGames.SM.Engine.RSReach.init ae G maxForwardJumps k) (skippedLenLe_init ae G maxForwardJumps k)]

end Computational.Proofs.SessionCostedFig8.Stage2Swap

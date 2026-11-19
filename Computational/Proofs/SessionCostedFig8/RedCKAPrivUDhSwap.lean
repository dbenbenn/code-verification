/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Fig8SchemeBridge -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs -- proof-setup: allow-public-import

/-!
# `dhSchemeFb Dh → dhScheme Dh` Swap for Stage-2 `redCKAPrivU` (`hooksCKAU`)

Extends `Fig8SchemeBridge.ckaBranch_redCKAPriv_dhSchemeFb_eq` to `SM.Construction.redCKAPrivU`
(`hooksCKAU`), showing `CKA.branch (dhSchemeFb Dh) Δcka tStar b (redCKAPrivU (dhSchemeFb Dh) ...)`
equals `CKA.branch (dhScheme Dh) Δcka tStar b (redCKAPrivU (dhScheme Dh) ...)` with `no proof gaps`.-/

public section

set_option autoImplicit false

open OracleComp OracleSpec
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge
  (DdhRoleOk CkaStateInv OptPartySync OptCKASync ckaFullImpl
   optPartySync_of_epoch_eq simulateQ_ckaFullImpl_liftProb
   liftC_corrQuery_support liftC_receiveQuery_support liftC_sendFamily_support
   dhSchemeFb_send_of_roleOk dhSchemeFb_receive_of_roleOk
   ddhRoleOk_initA ddhRoleOk_initB ckaStateInv_init
   ckaBranch_dhSchemeFb_eq accept_st_eq record_st_eq)

open scoped ENNReal
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.SM (Record)
open CryptoGames.SM.Construction (CKAUState Header Mode PartyState SchemeAdversary cacheCU hooksCKAU initCKA initCKAU liftC redCKAPrivU runCKAU sampleT)
open CryptoGames.SM.Engine (Ctx EState VP abortE challE coinsE commitE corrE deliverE engRun implE injectE run_liftH_bind transmitE vRecv vRecvStep1 vRecv_eq_bind vSend vSendStep1 vSend_eq_bind)

namespace Computational.Proofs.SessionCostedFig8.RedCKAPrivUDhSwap

section InterpretedCKAUSwap

variable {Pt KR RSt SS RS M E : Type}

private lemma simulateQ_stateTLift_ckau_eq [SampleableType Pt] {K α : Type}
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (Δ tStar : ℕ)
    (m : CryptoGames.SM.Engine.TComp
      (CryptoGames.CKA.spec (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) α)
    (hu : CKAUState Pt Pt K)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt) :
    (simulateQ (ckaFullImpl cka Δ tStar) ((StateT.lift m).run hu)).run sc =
      (fun w => ((w.1.1, hu), w.2)) <$>
        (simulateQ (ckaFullImpl cka Δ tStar) ((liftC m).run hu.1)).run sc := by
  simp only [liftC, StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private lemma liftU_corrQuery_support [Zero Pt] [SampleableType Pt] {K : Type}
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ) (P : Party) (hu : CKAUState Pt Pt K)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc)
    {z : (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt) × CKAUState Pt Pt K) ×
      CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt}
    (hz : z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
      ((StateT.lift (CryptoGames.CKA.corrQuery P)).run hu)).run sc)) :
    z.2 = sc ∧ ∀ γ, z.1.1 = some γ → DdhRoleOk P (sc.epoch P) γ := by
  rw [simulateQ_stateTLift_ckau_eq, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact liftC_corrQuery_support Dh Δ tStar P hu.1 sc hsc hw

private lemma liftU_receiveQuery_support [Zero Pt] [SampleableType Pt] {K : Type}
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ) (P : Party) (hu : CKAUState Pt Pt K)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc)
    {z : (Option Unit × CKAUState Pt Pt K) ×
      CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt}
    (hz : z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
      ((StateT.lift (CryptoGames.CKA.receiveQuery P)).run hu)).run sc)) :
    CkaStateInv z.2 ∧
    (z.1.1 = none → z.2 = sc) ∧
    (z.1.1 = some () → z.2.epoch P = sc.epoch P + 1 ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  rw [simulateQ_stateTLift_ckau_eq, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact liftC_receiveQuery_support Dh Δ tStar P hu.1 sc hsc hw

private lemma liftU_sendFamily_support [Zero Pt] [SampleableType Pt] {K : Type}
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar tH t : ℕ) (P : Party) (r : Option (BitVec 256))
    (hu : CKAUState Pt Pt K)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc)
    {z : (Option (Pt × Pt) × CKAUState Pt Pt K) ×
      CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt}
    (hz : z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
      ((match r with
        | some c => StateT.lift (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
        | none =>
          if t = tH then StateT.lift (CryptoGames.CKA.challQuery P)
          else StateT.lift (CryptoGames.CKA.sendQuery P)).run hu)).run sc)) :
    CkaStateInv z.2 ∧
    (∀ T' Ik, z.1.1 = some (T', Ik) →
      z.2.epoch P = sc.epoch P + 1 ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  have hMap :
      (simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
        ((match r with
          | some c => StateT.lift (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
          | none =>
            if t = tH then StateT.lift (CryptoGames.CKA.challQuery P)
            else StateT.lift (CryptoGames.CKA.sendQuery P)).run hu)).run sc =
      (fun w => ((w.1.1, hu), w.2)) <$>
        (simulateQ (ckaFullImpl (dhScheme Dh) Δ tStar)
          ((match r with
            | some c => liftC (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
            | none =>
              if t = tH then liftC (CryptoGames.CKA.challQuery P)
              else liftC (CryptoGames.CKA.sendQuery P)).run hu.1)).run sc := by
    rcases r with _ | c
    · split_ifs <;> exact simulateQ_stateTLift_ckau_eq _ _ _ _ _ _
    · exact simulateQ_stateTLift_ckau_eq _ _ _ _ _ _
  rw [hMap, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact liftC_sendFamily_support Dh Δ tStar tH t P r hu.1 sc hsc hw

private lemma vSend_ckaUSync_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType K] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar : ℕ) (mo : Mode)
    (ctx : Ctx (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS M E) (P : Party)
    (s : VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) (m : M)
    (pair : Option (M × M)) (r : Option (BitVec 256)) (hu : CKAUState Pt Pt K)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc) (hs : OptPartySync sc P s) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((vSend (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) ctx P s m pair r).run hu)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((vSend (hooksCKAU (dhScheme Dh) prng fs Δcka mo) ctx P s m pair r).run hu)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((vSend (hooksCKAU (dhScheme Dh) prng fs Δcka mo) ctx P s m pair r).run hu)).run sc),
      CkaStateInv z.2 ∧
      (∀ st' ct, z.1.1 = some (st', ct) →
        OptPartySync z.2 P st' ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  have hStep1 :
      (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
        ((vSendStep1 (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) ctx P s r).run hu)).run sc =
      (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
        ((vSendStep1 (hooksCKAU (dhScheme Dh) prng fs Δcka mo) ctx P s r).run hu)).run sc ∧
      ∀ w ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
        ((vSendStep1 (hooksCKAU (dhScheme Dh) prng fs Δcka mo) ctx P s r).run hu)).run sc),
        CkaStateInv w.2 ∧
        (∀ s₁, w.1.1 = some s₁ →
          OptPartySync w.2 P s₁ ∧ ∀ Q, Q ≠ P → w.2.epoch Q = sc.epoch Q) := by
    unfold vSendStep1
    by_cases hSend : s.id.sendsIn (s.tcur + 1) = true
    · have hPSend : P.sendsIn (s.tcur + 1) = true := hs.1 ▸ hSend
      simp only [hSend, ↓reduceIte]
      have hStart :
          (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
            (((hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo).startSend ctx P (s.tcur + 1) s.γ s.root r).run hu)).run sc =
          (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
            (((hooksCKAU (dhScheme Dh) prng fs Δcka mo).startSend ctx P (s.tcur + 1) s.γ s.root r).run hu)).run sc ∧
          ∀ q ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
            (((hooksCKAU (dhScheme Dh) prng fs Δcka mo).startSend ctx P (s.tcur + 1) s.γ s.root r).run hu)).run sc),
            CkaStateInv q.2 ∧
            (∀ γ' T' σ' ss, q.1.1 = some (γ', T', σ', ss) →
              (match γ' with | some g => DdhRoleOk P (s.tcur + 1) g | none => s.tcur + 1 = q.2.epoch P) ∧
              ∀ Q, Q ≠ P → q.2.epoch Q = sc.epoch Q) := by
        rcases hγ : s.γ with _ | γ
        · refine ⟨rfl, fun w hw => ?_⟩
          unfold hooksCKAU at hw
          dsimp only at hw
          rw [StateT.run_bind, StateT.run_get, pure_bind] at hw
          dsimp only at hw
          have hw_ans : ∃ (ans : Option (Pt × Pt)) (hu₁ : CKAUState Pt Pt K)
              (sc₁ : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt),
              ((ans, hu₁), sc₁) ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
                ((match r with
                  | some c => StateT.lift (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
                  | none =>
                    if s.tcur + 1 = mo.tH then StateT.lift (CryptoGames.CKA.challQuery P)
                    else StateT.lift (CryptoGames.CKA.sendQuery P)).run hu)).run sc) ∧
              w ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
                ((match ans with
                  | none => pure none
                  | some (T', Ik) => do
                    cacheCU (s.tcur + 1) (T', Ik)
                    if s.tcur + 1 = mo.tStar then do
                      let kU ← StateT.lift (sampleT K)
                      let __x ← pure (kU, some kU)
                      modify fun st => (st.1, __x.2)
                      if mo.tH + Δcka ≤ s.tcur + 1 then
                        StateT.lift (CryptoGames.CKA.corrQuery P) >>=
                          fun (corrAns : Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) =>
                          match corrAns with
                          | none => pure none
                          | some γ => pure (some (some γ, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                      else pure (some (none, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                    else do
                      let __x ← pure ((prng.up s.root Ik).2, hu.2)
                      modify fun st => (st.1, __x.2)
                      if mo.tH + Δcka ≤ s.tcur + 1 then
                        StateT.lift (CryptoGames.CKA.corrQuery P) >>=
                          fun (corrAns : Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) =>
                          match corrAns with
                          | none => pure none
                          | some γ => pure (some (some γ, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                      else pure (some (none, T', (prng.up s.root Ik).1, fs.initSender __x.1))).run hu₁)).run sc₁) := by
            have finish_cont : ∀ (ans : Option (Pt × Pt)) (hu₁ : CKAUState Pt Pt K)
                (sc₁ : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
                (c_cont :
                  CryptoGames.SM.Engine.HM (CryptoGames.CKA.spec (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
                    (CKAUState Pt Pt K)
                    (Option (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt) × Pt × RSt × SS))),
                (c_cont = match ans with
                  | none => pure none
                  | some (T', Ik) => do
                    cacheCU (s.tcur + 1) (T', Ik)
                    if s.tcur + 1 = mo.tStar then do
                      let kU ← StateT.lift (sampleT K)
                      let __x ← pure (kU, some kU)
                      modify fun st => (st.1, __x.2)
                      if mo.tH + Δcka ≤ s.tcur + 1 then
                        StateT.lift (CryptoGames.CKA.corrQuery P) >>=
                          fun (corrAns : Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) =>
                          match corrAns with
                          | none => pure none
                          | some γ => pure (some (some γ, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                      else pure (some (none, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                    else do
                      let __x ← pure ((prng.up s.root Ik).2, hu.2)
                      modify fun st => (st.1, __x.2)
                      if mo.tH + Δcka ≤ s.tcur + 1 then
                        StateT.lift (CryptoGames.CKA.corrQuery P) >>=
                          fun (corrAns : Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) =>
                          match corrAns with
                          | none => pure none
                          | some γ => pure (some (some γ, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                      else pure (some (none, T', (prng.up s.root Ik).1, fs.initSender __x.1))) →
                w ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar) (c_cont.run hu₁)).run sc₁) →
                w ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
                  ((match ans with
                    | none => pure none
                    | some (T', Ik) => do
                      cacheCU (s.tcur + 1) (T', Ik)
                      if s.tcur + 1 = mo.tStar then do
                        let kU ← StateT.lift (sampleT K)
                        let __x ← pure (kU, some kU)
                        modify fun st => (st.1, __x.2)
                        if mo.tH + Δcka ≤ s.tcur + 1 then
                          StateT.lift (CryptoGames.CKA.corrQuery P) >>=
                            fun (corrAns : Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) =>
                            match corrAns with
                            | none => pure none
                            | some γ => pure (some (some γ, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                        else pure (some (none, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                      else do
                        let __x ← pure ((prng.up s.root Ik).2, hu.2)
                        modify fun st => (st.1, __x.2)
                        if mo.tH + Δcka ≤ s.tcur + 1 then
                          StateT.lift (CryptoGames.CKA.corrQuery P) >>=
                            fun (corrAns : Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) =>
                            match corrAns with
                            | none => pure none
                            | some γ => pure (some (some γ, T', (prng.up s.root Ik).1, fs.initSender __x.1))
                        else pure (some (none, T', (prng.up s.root Ik).1, fs.initSender __x.1))).run hu₁)).run sc₁) := by
              intro ans hu₁ sc₁ c_cont hf hmem
              rw [← hf]; exact hmem
            rcases r with _ | c
            · dsimp only at hw ⊢
              by_cases htH : s.tcur + 1 = mo.tH
              · rw [ite_eq_left htH] at hw ⊢
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
                obtain ⟨⟨⟨ans, hu₁⟩, sc₁⟩, hans, hw⟩ := hw
                dsimp only at hw
                refine ⟨ans, hu₁, sc₁, hans, finish_cont ans hu₁ sc₁ _ ?_ hw⟩
                rcases ans with _ | ⟨T', Ik⟩
                · rfl
                · dsimp only
                  congr 1; funext _
                  by_cases ht : s.tcur + 1 = mo.tStar
                  · rw [ite_eq_left ht, ite_eq_left ht]
                    congr 1; funext kU; rw [pure_bind, pure_bind]; congr 1; funext _
                    by_cases hf : mo.tH + Δcka ≤ s.tcur + 1
                    · rw [ite_eq_left hf, ite_eq_left hf]; congr 1; funext cA; cases cA <;> rfl
                    · rw [ite_eq_right hf, ite_eq_right hf]
                  · rw [ite_eq_right ht, ite_eq_right ht]
                    rw [pure_bind, pure_bind]; congr 1; funext _
                    by_cases hf : mo.tH + Δcka ≤ s.tcur + 1
                    · rw [ite_eq_left hf, ite_eq_left hf]; congr 1; funext cA; cases cA <;> rfl
                    · rw [ite_eq_right hf, ite_eq_right hf]
              · rw [ite_eq_right htH] at hw ⊢
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
                obtain ⟨⟨⟨ans, hu₁⟩, sc₁⟩, hans, hw⟩ := hw
                dsimp only at hw
                refine ⟨ans, hu₁, sc₁, hans, finish_cont ans hu₁ sc₁ _ ?_ hw⟩
                rcases ans with _ | ⟨T', Ik⟩
                · rfl
                · dsimp only
                  congr 1; funext _
                  by_cases ht : s.tcur + 1 = mo.tStar
                  · rw [ite_eq_left ht, ite_eq_left ht]
                    congr 1; funext kU; rw [pure_bind, pure_bind]; congr 1; funext _
                    by_cases hf : mo.tH + Δcka ≤ s.tcur + 1
                    · rw [ite_eq_left hf, ite_eq_left hf]; congr 1; funext cA; cases cA <;> rfl
                    · rw [ite_eq_right hf, ite_eq_right hf]
                  · rw [ite_eq_right ht, ite_eq_right ht]
                    rw [pure_bind, pure_bind]; congr 1; funext _
                    by_cases hf : mo.tH + Δcka ≤ s.tcur + 1
                    · rw [ite_eq_left hf, ite_eq_left hf]; congr 1; funext cA; cases cA <;> rfl
                    · rw [ite_eq_right hf, ite_eq_right hf]
            · dsimp only at hw ⊢
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
              obtain ⟨⟨⟨ans, hu₁⟩, sc₁⟩, hans, hw⟩ := hw
              dsimp only at hw
              refine ⟨ans, hu₁, sc₁, hans, finish_cont ans hu₁ sc₁ _ ?_ hw⟩
              rcases ans with _ | ⟨T', Ik⟩
              · rfl
              · dsimp only
                congr 1; funext _
                by_cases ht : s.tcur + 1 = mo.tStar
                · rw [ite_eq_left ht, ite_eq_left ht]
                  congr 1; funext kU; rw [pure_bind, pure_bind]; congr 1; funext _
                  by_cases hf : mo.tH + Δcka ≤ s.tcur + 1
                  · rw [ite_eq_left hf, ite_eq_left hf]; congr 1; funext cA; cases cA <;> rfl
                  · rw [ite_eq_right hf, ite_eq_right hf]
                · rw [ite_eq_right ht, ite_eq_right ht]
                  rw [pure_bind, pure_bind]; congr 1; funext _
                  by_cases hf : mo.tH + Δcka ≤ s.tcur + 1
                  · rw [ite_eq_left hf, ite_eq_left hf]; congr 1; funext cA; cases cA <;> rfl
                  · rw [ite_eq_right hf, ite_eq_right hf]
          obtain ⟨ans, hu₁, sc₁, hans, hw⟩ := hw_ans
          have ⟨hsc₁, hep₁⟩ := liftU_sendFamily_support Dh Δcka tStar mo.tH (s.tcur + 1) P r hu sc hsc hans
          have hstcur : s.tcur = sc.epoch P := by have h2 := hs.2; rw [hγ] at h2; exact h2
          rcases ans with _ | ⟨T', Ik⟩
          · simp only [StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw
            subst hw; exact ⟨hsc₁, fun _ _ _ _ hEq => nomatch hEq⟩
          · have ⟨hepP, hepQ⟩ := hep₁ T' Ik rfl
            dsimp only at hsc₁ hepP hepQ hw
            have hw_mid : ∃ (kEpoch : K) (hu₂ : CKAUState Pt Pt K),
                w ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
                  ((if mo.tH + Δcka ≤ s.tcur + 1 then
                      StateT.lift (CryptoGames.CKA.corrQuery P) >>= fun corrAns =>
                        match corrAns with
                        | none => pure none
                        | some γ => pure (some (some γ, T', (prng.up s.root Ik).1, fs.initSender kEpoch))
                    else pure (some (none, T', (prng.up s.root Ik).1, fs.initSender kEpoch))).run hu₂)).run sc₁) := by
              by_cases ht : s.tcur + 1 = mo.tStar
              · rw [ite_eq_left ht] at hw
                simp only [cacheCU, StateT.run_bind, StateT.run_lift,
                  StateT.run_modify, bind_assoc, pure_bind,
                  simulateQ_bind] at hw
                rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hw
                simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hw
                obtain ⟨kU, _, hw⟩ := hw
                exact ⟨kU, _, hw⟩
              · rw [ite_eq_right ht] at hw
                simp only [cacheCU, StateT.run_bind, StateT.run_modify,
                  pure_bind] at hw
                exact ⟨(prng.up s.root Ik).2, _, hw⟩
            obtain ⟨kEpoch, hu₂, hw⟩ := hw_mid
            by_cases hfin : mo.tH + Δcka ≤ s.tcur + 1
            · simp only [hfin, ↓reduceIte] at hw
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind,
                mem_support_bind_iff] at hw
              obtain ⟨⟨⟨corrAns, hu₃⟩, sc₂⟩, hcorr, hw⟩ := hw
              have ⟨hsc₂_eq, hRole₂⟩ := liftU_corrQuery_support Dh Δcka tStar P _ sc₁ hsc₁ hcorr
              dsimp only at hsc₂_eq hRole₂; subst hsc₂_eq
              rcases corrAns with _ | γ'
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hw
                subst hw; exact ⟨hsc₁, fun _ _ _ _ hEq => nomatch hEq⟩
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hw
                subst hw
                refine ⟨hsc₁, fun g' _ _ _ hEq => ?_⟩
                cases hEq
                have hR : DdhRoleOk P (s.tcur + 1) γ' := by
                  rw [hstcur, ← hepP]; exact hRole₂ γ' rfl
                exact ⟨hR, hepQ⟩
            · simp only [hfin, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw
              subst hw
              refine ⟨hsc₁, fun _ _ _ _ hEq => ?_⟩
              cases hEq
              exact ⟨by dsimp; omega, hepQ⟩
        · dsimp only [hooksCKAU]
          have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
          have hCoinsEq : ∀ coins : BitVec 256,
              (dhSchemeFb Dh).send γ coins = (dhScheme Dh).send γ coins ∧
                DdhRoleOk P (s.tcur + 1) ((dhScheme Dh).send γ coins).1 :=
            fun coins => dhSchemeFb_send_of_roleOk Dh hRole hPSend coins
          rcases r with _ | c
          · simp only [StateT.run_bind, StateT.run_get, StateT.run_lift,
              cacheCU, StateT.run_modify, bind_assoc, pure_bind, simulateQ_bind]
            refine ⟨bind_congr fun p => by rw [(hCoinsEq p.1).1], fun w hw => ?_⟩
            rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hw
            simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hw
            obtain ⟨coins, _, hw⟩ := hw
            by_cases ht : s.tcur + 1 = mo.tStar
            · simp only [ht, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_modify,
                StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure] at hw
              rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hw
              simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
                Set.mem_singleton_iff] at hw
              obtain ⟨_, _, hw⟩ := hw; subst hw
              refine ⟨hsc, fun _ _ _ _ hEq => ?_⟩
              cases hEq
              exact ⟨(hCoinsEq coins).2, fun _ _ => rfl⟩
            · simp only [ht, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
              subst hw
              refine ⟨hsc, fun _ _ _ _ hEq => ?_⟩
              cases hEq
              exact ⟨(hCoinsEq coins).2, fun _ _ => rfl⟩
          · simp only [pure_bind, (hCoinsEq c).1]
            refine ⟨trivial, fun w hw => ?_⟩
            by_cases ht : s.tcur + 1 = mo.tStar
            · simp only [ht, ↓reduceIte, cacheCU, StateT.run_bind, StateT.run_get, StateT.run_lift,
                StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind,
                simulateQ_bind, simulateQ_pure] at hw
              rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hw
              simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
                Set.mem_singleton_iff] at hw
              obtain ⟨_, _, hw⟩ := hw; subst hw
              refine ⟨hsc, fun _ _ _ _ hEq => ?_⟩
              cases hEq
              exact ⟨(hCoinsEq c).2, fun _ _ => rfl⟩
            · simp only [ht, ↓reduceIte, cacheCU, StateT.run_bind, StateT.run_get,
                StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
              subst hw
              refine ⟨hsc, fun _ _ _ _ hEq => ?_⟩
              cases hEq
              exact ⟨(hCoinsEq c).2, fun _ _ => rfl⟩
      rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind,
        StateT.run_bind, StateT.run_bind, hStart.1]
      refine ⟨rfl, fun w hw => ?_⟩
      rw [mem_support_bind_iff] at hw
      obtain ⟨⟨⟨res, hu₁⟩, sc₁⟩, hq, hw⟩ := hw
      have ⟨hsc₁, hqPost⟩ := hStart.2 _ hq
      rcases res with _ | ⟨γ', T', σ', ss⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
        subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        have ⟨hRole', hepQ⟩ := hqPost γ' T' σ' ss rfl
        exact ⟨hsc₁, fun s₁ hs₁ => by dsimp at hs₁; cases hs₁; exact ⟨⟨hs.1, hRole'⟩, hepQ⟩⟩
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff]
      refine ⟨trivial, fun w hw => ?_⟩
      subst hw
      exact ⟨hsc, fun s₁ hs₁ => by dsimp at hs₁; cases hs₁; exact ⟨hs, fun _ _ => rfl⟩⟩
  rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind,
    StateT.run_bind, StateT.run_bind, hStep1.1]
  have hFsEq : (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo).fsSend =
      (hooksCKAU (dhScheme Dh) prng fs Δcka mo).fsSend := rfl
  rw [hFsEq]
  refine ⟨rfl, fun z hz => ?_⟩
  rw [mem_support_bind_iff] at hz
  obtain ⟨⟨⟨s₁?, hu₁⟩, sc₁⟩, hw, hz⟩ := hz
  have ⟨hsc₁, hs₁Sync⟩ := hStep1.2 _ hw
  rcases s₁? with _ | s₁
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨hsc₁, fun _ _ hEq => by cases hEq⟩
  · have ⟨hs₁P, hepQ⟩ := hs₁Sync s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨hsc₁, fun _ _ hEq => by cases hEq; exact ⟨hs₁P, hepQ⟩⟩
    · simp only [hvS, hooksCKAU, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hsc₁, fun st' ct hEq => by cases hEq; exact ⟨hs₁P, hepQ⟩⟩

private lemma vRecv_hooksCKAU_pure_eq [DecidableEq Pt] [Zero Pt] {K : Type} [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka : ℕ) (mo : Mode)
    (ctx : Ctx (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS M E) (P : Party)
    (s : VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) (c : Header Pt × E)
    (rec_ : Option (Record M (Header Pt × E))) (hu : CKAUState Pt Pt K)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hs : OptPartySync sc P s) :
    (vRecv (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) ctx P s c rec_).run hu =
      (vRecv (hooksCKAU (dhScheme Dh) prng fs Δcka mo) ctx P s c rec_).run hu ∧
    ∃ out,
      (vRecv (hooksCKAU (dhScheme Dh) prng fs Δcka mo) ctx P s c rec_).run hu = pure out ∧
      ∀ st' t' i' m', out.1 = some (some (st', t', i', m')) →
        st'.id = P ∧
        (((s.tcur < st'.tcur && s.γ.isNone) = false ∧ OptPartySync sc P st') ∨
         ((s.tcur < st'.tcur && s.γ.isNone) = true ∧ st'.γ = none ∧ st'.tcur = sc.epoch P + 1)) := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [href, ↓reduceIte, StateT.run_pure]
    exact ⟨trivial, _, rfl, fun _ _ _ _ hEq => by cases hEq⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hNotSend : s.id.sendsIn c.1.1 = false :=
      (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href)).1
    have hStep1 :
        ∃ out1,
          (vRecvStep1 (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) ctx P s c).run hu = pure out1 ∧
          (vRecvStep1 (hooksCKAU (dhScheme Dh) prng fs Δcka mo) ctx P s c).run hu = pure out1 ∧
          ∀ s₁, out1.1 = some (some s₁) →
            s₁.id = P ∧
            (((s.tcur < s₁.tcur && s.γ.isNone) = false ∧ OptPartySync sc P s₁) ∨
             ((s.tcur < s₁.tcur && s.γ.isNone) = true ∧ s₁.γ = none ∧ s₁.tcur = sc.epoch P + 1)) := by
      unfold vRecvStep1
      by_cases ht : c.1.1 = s.tcur + 1
      · simp only [ht, ↓reduceIte]
        rcases hTn : c.1.2 with _ | Tn
        · exact ⟨_, StateT.run_pure _ _, StateT.run_pure _ _, fun _ hEq => by cases hEq⟩
        · have hPRecv : P.sendsIn (s.tcur + 1) = false := by
            rw [← hs.1, ← ht]; exact hNotSend
          dsimp only [hooksCKAU]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          have hMapEq :
              (s.γ.map fun γ => ((dhSchemeFb Dh).receive γ Tn).1) =
                (s.γ.map fun γ => ((dhScheme Dh).receive γ Tn).1) := by
            rcases hγ : s.γ with _ | γ
            · rfl
            · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
              exact congrArg (fun p => some p.1) (dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn).1
          rcases hcache : hu.1.cache (s.tcur + 1) with _ | ⟨Tc, Ik⟩
          · by_cases hauth : (mo.auth && decide (s.tcur + 1 = mo.tStar)) = true
            · simp only [hauth, ↓reduceIte]
              rcases hγ : s.γ with _ | γ
              · simp only [StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
              · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
                have ⟨hEq, hRole'⟩ := dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                simp only [hEq, StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
                  dsimp at hs₁; cases hs₁
                  exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hRole'⟩⟩⟩⟩
            · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
              exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
          · by_cases hTc : Tc = Tn
            · simp only [hTc, ↓reduceIte, hMapEq, StateT.run_pure, pure_bind]
              refine ⟨_, rfl, rfl, fun s₁ hs₁ => ?_⟩
              dsimp at hs₁; cases hs₁
              rcases hγ : s.γ with _ | γ
              · refine ⟨hs.1, Or.inr ⟨by simp, rfl, ?_⟩⟩
                have h2 := hs.2; rw [hγ] at h2; dsimp; omega
              · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
                have ⟨_, hRole'⟩ := dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hRole'⟩⟩⟩
            · simp only [hTc, ↓reduceIte]
              by_cases hauth : (mo.auth && decide (s.tcur + 1 = mo.tStar)) = true
              · simp only [hauth, ↓reduceIte]
                rcases hγ : s.γ with _ | γ
                · simp only [StateT.run_pure, pure_bind]
                  exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
                · have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
                  have ⟨hEq, hRole'⟩ := dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                  simp only [hEq, StateT.run_pure, pure_bind]
                  exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
                    dsimp at hs₁; cases hs₁
                    exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hRole'⟩⟩⟩⟩
              · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
      · simp only [ht, ↓reduceIte, StateT.run_pure]
        exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
          dsimp at hs₁; cases hs₁; exact ⟨hs.1, Or.inl ⟨by simp, hs⟩⟩⟩
    obtain ⟨⟨s₁?, hu₁⟩, hPureFb, hPureDh, hPost1⟩ := hStep1
    rw [hPureFb, hPureDh, pure_bind, pure_bind]
    rcases s₁? with _ | (_ | s₁)
    · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
    · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
    · dsimp only
      rcases hvR : s₁.vR c.1.1 with _ | v
      · rw [StateT.run_pure]
        exact ⟨rfl, _, rfl, fun _ _ _ _ hEq => nomatch hEq⟩
      · dsimp only [hooksCKAU]
        rw [pure_bind]
        rcases hrc : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
        · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
        · exact ⟨rfl, _, StateT.run_pure _ _, fun st' _ _ _ hEq => by
            dsimp at hEq; cases hEq; exact hPost1 s₁ rfl⟩

private lemma commitE_ckaUSync [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar : ℕ) (mo : Mode)
    (s : Ctx (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS M E) (P : Party)
    (old new : VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS)
    (pos : CryptoGames.SM.Pos)
    (es : EState (VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) M
      (Header Pt × E) (CKAUState Pt Pt K))
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc)
    (hS : ∀ Q, OptPartySync sc Q (s.st Q))
    (_hEs : es.abort = false → ∀ Q, OptPartySync sc Q (es.g.st Q))
    (hNew : new.id = P ∧
      (((old.tcur < new.tcur && old.γ.isNone) = false ∧ OptPartySync sc P new) ∨
       ((old.tcur < new.tcur && old.γ.isNone) = true ∧ new.γ = none ∧ new.tcur = sc.epoch P + 1))) :
    (commitE (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) s P old new pos).run es =
      (commitE (hooksCKAU (dhScheme Dh) prng fs Δcka mo) s P old new pos).run es ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((commitE (hooksCKAU (dhScheme Dh) prng fs Δcka mo) s P old new pos).run es)).run sc),
      CkaStateInv z.2 ∧
      (z.1.1 = none → OptCKASync z.1.2 z.2) ∧
      (∀ s₁, z.1.1 = some s₁ → z.1.2.abort = es.abort ∧
        ∀ Q, OptPartySync z.2 Q (s₁.st Q)) := by
  refine ⟨rfl, fun z hz => ?_⟩
  unfold commitE abortE at hz
  dsimp only [hooksCKAU] at hz
  rw [run_liftH_bind] at hz
  rcases hNew.2 with ⟨hCond, hSyncNew⟩ | ⟨hCond, hγNone, htcurNew⟩
  · rw [hCond] at hz
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    refine ⟨hsc, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
    cases hs₁
    by_cases hQP : Q = P
    · subst hQP; simp [hSyncNew]
    · simp [Function.update_of_ne hQP, accept_st_eq, hS Q]
  · rw [hCond] at hz
    simp only [↓reduceIte] at hz
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨⟨rcvAns, hu₁⟩, sc₁⟩, hrcv, hz⟩ := hz
    have ⟨hsc₁, _, hRcvOk⟩ := liftU_receiveQuery_support Dh Δcka tStar P es.h sc hsc hrcv
    rcases rcvAns with _ | ⟨⟩
    · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      dsimp only
      exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
    · have ⟨hepP, hepQ⟩ := hRcvOk rfl
      dsimp only at hsc₁ hepP hepQ
      by_cases hfin : mo.tH + Δcka ≤ new.tcur
      · simp only [hfin, ↓reduceIte] at hz
        rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨corrAns, hu₂⟩, sc₂⟩, hcorr, hz⟩ := hz
        have ⟨hsc₂_eq, hRole₂⟩ := liftU_corrQuery_support Dh Δcka tStar P hu₁ sc₁ hsc₁ hcorr
        dsimp only at hsc₂_eq hRole₂
        subst hsc₂_eq
        rcases corrAns with _ | γ'
        · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          dsimp only
          exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
        · simp only [StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          dsimp only
          refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
          cases hs₁
          by_cases hQP : Q = P
          · subst hQP
            have hR : DdhRoleOk Q new.tcur γ' := by rw [htcurNew, ← hepP]; exact hRole₂ γ' rfl
            simp only [Function.update_self, accept_st_eq]
            exact ⟨hNew.1, hR⟩
          · simp [Function.update_of_ne hQP, accept_st_eq]
            exact optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)
      · simp only [hfin, ↓reduceIte, StateT.run_pure, pure_bind, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        dsimp only
        refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
        cases hs₁
        by_cases hQP : Q = P
        · subst hQP
          simp only [Function.update_self, accept_st_eq]
          refine ⟨hNew.1, ?_⟩
          rw [hγNone, htcurNew, hepP]
        · simp [Function.update_of_ne hQP, accept_st_eq]
          exact optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)

private lemma implE_ckaUSync_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep maxSkip : ℕ) (mo : Mode)
    (es : EState (VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) M
      (Header Pt × E) (CKAUState Pt Pt K))
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (t : (CryptoGames.SM.spec
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)).Domain)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
        (.inr t)).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKAU (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
        (.inr t)).run es)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKAU (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
        (.inr t)).run es)).run sc), OptCKASync z.1.2 z.2 := by
  let hk₁ := hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo
  let hk₂ := hooksCKAU (dhScheme Dh) prng fs Δcka mo
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₁ (2 + Δcka) qep mo.policy (P, m, r) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₂ (2 + Δcka) qep mo.policy (P, m, r) := rfl
    rw [hI₁, hI₂]; unfold transmitE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => by cases h'⟩⟩
        · have hs₁All : ∀ Q, OptPartySync sc Q (s₁.st Q) := fun Q => by
            rw [CryptoGames.SM.Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
          have hvs := vSend_ckaUSync_eq Dh prng fs Δcka tStar mo s₁ P (s₁.st P) m none r es.h sc
            hSync.1 (hs₁All P)
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
          rw [run_liftH_bind, run_liftH_bind]
          simp only [simulateQ_bind, StateT.run_bind]
          rw [hvs.1]
          refine ⟨rfl, fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz
          obtain ⟨⟨⟨vsRes, hu'⟩, sc₁⟩, hvsMem, hz⟩ := hz
          have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
          rcases vsRes with _ | ⟨st', ct⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
          · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨hsc₁, fun _ Q => ?_⟩
            by_cases hQP : Q = P
            · subst hQP; simp [record_st_eq, hst'P]
            · simp [record_st_eq, Function.update_of_ne hQP]
              exact optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₁ (2 + Δcka) qep mo.cfg mo.policy (P, m₀, m₁, r) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₂ (2 + Δcka) qep mo.cfg mo.policy (P, m₀, m₁, r) := rfl
    rw [hI₁, hI₂]; unfold challE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((mo.cfg (M := M)).challAllowedIn (s₁.epoch P))) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
          · have hs₁All : ∀ Q, OptPartySync sc Q (s₁.st Q) := fun Q => by
              rw [CryptoGames.SM.Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
            have hvs := vSend_ckaUSync_eq Dh prng fs Δcka tStar mo s₁ P (s₁.st P)
              (((mo.cfg (M := M)).challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀))
              (some (m₀, m₁)) r es.h sc hSync.1 (hs₁All P)
            simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
            rw [run_liftH_bind, run_liftH_bind]
            simp only [simulateQ_bind, StateT.run_bind]
            rw [hvs.1]
            refine ⟨rfl, fun z hz => ?_⟩
            rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨vsRes, hu'⟩, sc₁⟩, hvsMem, hz⟩ := hz
            have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
            rcases vsRes with _ | ⟨st', ct⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
            · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz
              refine ⟨hsc₁, fun _ Q => ?_⟩
              by_cases hQP : Q = P
              · subst hQP; simp [record_st_eq, hst'P]
              · simp [record_st_eq, Function.update_of_ne hQP]
                exact optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₁ maxSkip mo.cfg (P, c) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₂ maxSkip mo.cfg (P, c) := rfl
    rw [hI₁, hI₂]; unfold deliverE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · obtain ⟨hvrEq, ⟨⟨vrRes, hu'⟩, hvrPure, hvrPost⟩⟩ :=
          vRecv_hooksCKAU_pure_eq Dh prng fs Δcka mo es.g P (es.g.st P) c (some r) es.h sc
            (hSync.2 habF P)
        rw [run_liftH_bind, run_liftH_bind]
        dsimp only [hk₁, hk₂]
        simp only [hvrEq, hvrPure, pure_bind]
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
        · split_ifs <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               simulateQ_pure, support_pure, Set.mem_singleton_iff];
             exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
        · have hcm := commitE_ckaUSync Dh prng fs Δcka tStar mo es.g P (es.g.st P) st' r.pos
            { es with h := hu' } sc hSync.1 (hSync.2 habF) hSync.2 (hvrPost st' t' i' m' rfl)
          simp only [StateT.run_bind, simulateQ_bind]
          rw [hcm.1]
          refine ⟨rfl, fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz
          obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
          obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hcmNone rfl
          · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨hsc₁, fun _ Q => ?_⟩
            split_ifs <;> exact hs₁Sync Q
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inr (P, c)))) =
        injectE hk₁ (2 + Δcka) qep mo.cfg (P, c) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inl (.inr (P, c)))) =
        injectE hk₂ (2 + Δcka) qep mo.cfg (P, c) := rfl
    rw [hI₁, hI₂]; unfold injectE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := by
        rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href) with ⟨h1, _⟩
        rcases Bool.or_eq_false_iff.mp h1 with ⟨h2, _⟩
        exact (Bool.or_eq_false_iff.mp h2).1
      obtain ⟨hvrEq, ⟨⟨vrRes, hu'⟩, hvrPure, hvrPost⟩⟩ :=
        vRecv_hooksCKAU_pure_eq Dh prng fs Δcka mo es.g P (es.g.st P) c none es.h sc
          (hSync.2 habF P)
      simp only [href, Bool.false_eq_true, ↓reduceIte]
      rw [run_liftH_bind, run_liftH_bind]
      dsimp only [hk₁, hk₂]
      simp only [hvrEq, hvrPure, pure_bind]
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · simp only [hqep, ↓reduceIte]
          by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
          · have hcm := commitE_ckaUSync Dh prng fs Δcka tStar mo es.g P (es.g.st P) st'
              ⟨P.other, t', i'⟩ { es with h := hu' } sc hSync.1 (hSync.2 habF) hSync.2
              (hvrPost st' t' i' m' rfl)
            simp only [htriv, ↓reduceIte, StateT.run_bind, simulateQ_bind]
            rw [hcm.1]
            refine ⟨rfl, fun z hz => ?_⟩
            rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
            obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
            rcases cmRes with _ | s₁
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hcmNone rfl
            · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨hsc₁, fun _ => hs₁Sync⟩
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
            split_ifs <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 simulateQ_pure, support_pure, Set.mem_singleton_iff];
               exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inr P)) =
        corrE hk₁ mo.policy P := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr (.inr P)) =
        corrE hk₂ mo.policy P := rfl
    rw [hI₁, hI₂]
    have hRevEq : hk₁.reveal = hk₂.reveal := rfl
    unfold corrE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hRevEq]
    refine ⟨trivial, fun z hz => ?_⟩
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P)) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hSync
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P) = true
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hz
        rw [run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, hu'⟩, sc₁⟩, hrev, hz⟩ := hz
        have hsc₁_eq : sc₁ = sc := by
          dsimp only [hk₂, hooksCKAU] at hrev
          rcases hγ : (es.g.st P).γ with _ | γ
          · simp only [hγ, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hrev
            obtain ⟨⟨⟨corrAns, hu₂⟩, sc₂⟩, hcorr, hrev⟩ := hrev
            have ⟨heq, _⟩ := liftU_corrQuery_support Dh Δcka tStar P es.h sc hSync.1 hcorr
            subst heq
            rcases corrAns with _ | γ' <;>
              (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hrev;
               exact (Prod.mk.inj hrev).2)
          · simp only [hγ, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hrev
            exact (Prod.mk.inj hrev).2
        subst hsc₁_eq
        rcases revRes with _ | stP
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hSync

private lemma simulateQ_implE_ckaUSync_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K α : Type} [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep maxSkip : ℕ) (mo : Mode)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)) α)
    (es : EState (VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS) M
      (Header Pt × E) (CKAUState Pt Pt K))
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (implE (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip
        mo.cfg mo.policy) oa).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (implE (hooksCKAU (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip
        mo.cfg mo.policy) oa).run es)).run sc := by
  induction oa using OracleComp.inductionOn generalizing es sc with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · have hInl₁ :
          (implE (hooksCKAU (dhSchemeFb Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
            (.inl n)).run es = (coinsE n).run es := rfl
      have hInl₂ :
          (implE (hooksCKAU (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip mo.cfg mo.policy
            (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl₁, hInl₂]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, simulateQ_bind, simulateQ_HasQuery_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at hmem
      have hInlQ : ckaFullImpl (dhScheme Dh) Δcka tStar (Sum.inl n) =
          StateT.lift ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1))) := rfl
      rw [hInlQ, StateT.run_lift] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨_, _, hEq⟩ := hmem
      rcases Prod.mk.inj hEq with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨rfl, hesEq⟩
      dsimp only [id]
      rw [hesEq, hscEq]
      exact ih u es sc hSync
    · obtain ⟨hEq, hPost⟩ := implE_ckaUSync_eq Dh prng fs Δcka tStar qep maxSkip mo es sc t_sm hSync
      rw [hEq]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem =>
        ih _ es' sc' (hPost _ hmem)

theorem simulateQ_runCKAU_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ) (mo : Mode)
    (b : Bool)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hsc : CkaStateInv sc) (hep₀ : ∀ P, sc.epoch P = 0) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      (runCKAU (dhSchemeFb Dh) prng fs lam Δcka qep mo b A)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      (runCKAU (dhScheme Dh) prng fs lam Δcka qep mo b A)).run sc := by
  unfold runCKAU engRun
  have hInit : initCKAU (dhSchemeFb Dh) prng fs lam mo = initCKAU (dhScheme Dh) prng fs lam mo := rfl
  rw [hInit, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨vs, hu⟩, sc₁⟩ hmem => ?_
  have hSyncInit : sc₁ = sc ∧ ∀ vA vB, vs = some (vA, vB) →
      OptCKASync (M := M) (E := Header Pt × E)
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := b }, h := hu } sc := by
    have hInitRun : (initCKAU (dhScheme Dh) prng fs lam mo).run ({}, none) =
        ((initCKA (dhScheme Dh) prng fs lam mo).run {} >>= fun x => pure (x.1, (x.2, none))) := rfl
    rw [hInitRun] at hmem
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨⟨⟨vs₀, h₀⟩, sc₁'⟩, hmem, hEqU⟩ := hmem
    rcases Prod.mk.inj hEqU with ⟨hEqU1, rfl⟩
    rcases Prod.mk.inj hEqU1 with ⟨rfl, rfl⟩
    unfold initCKA at hmem
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, bind_assoc, pure_bind] at hmem
    rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
    simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hmem
    obtain ⟨kr, _, hmem⟩ := hmem
    rcases htL : mo.tL with _ | tLv
    · simp only [htL, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind] at hmem
      rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨kc, _, hmem⟩ := hmem
      rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩
      rw [hvs, Option.some.injEq] at hEq; cases hEq
      refine ⟨hsc, fun _ P => ?_⟩
      cases P
      · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
      · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
    · simp only [htL, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩
      rw [hvs, Option.some.injEq] at hEq; cases hEq
      refine ⟨hsc, fun _ P => ?_⟩
      cases P <;> exact ⟨rfl, (hep₀ _).symm⟩
  obtain ⟨hscEq, hSyncInit⟩ := hSyncInit
  rw [hscEq]
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · dsimp only
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    rw [simulateQ_implE_ckaUSync_eq Dh prng fs Δcka tStar qep fs.maxSkip mo A _ sc
      (hSyncInit vA vB rfl)]

theorem ckaBranch_redCKAPrivU_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (i : ℕ) (b : Bool)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (redCKAPrivU (dhSchemeFb Dh) prng fs lam Δcka qep tL i A) =
    CryptoGames.CKA.branch (dhScheme Dh) Δcka tStar b
      (redCKAPrivU (dhScheme Dh) prng fs lam Δcka qep tL i A) := by
  rw [ckaBranch_dhSchemeFb_eq]
  unfold CryptoGames.CKA.branch redCKAPrivU
  refine bind_congr fun k => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [simulateQ_bind, StateT.run_bind]
  rw [sampleT, simulateQ_ckaFullImpl_liftProb]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun bSM => ?_
  rw [simulateQ_runCKAU_dhSchemeFb_eq Dh prng fs lam Δcka tStar qep ⟨false, tL, i⟩ bSM A
    (CryptoGames.CKA.initState (dhScheme Dh) k b) (ckaStateInv_init Dh k b) (fun _ => rfl)]

end InterpretedCKAUSwap

end Computational.Proofs.SessionCostedFig8.RedCKAPrivUDhSwap

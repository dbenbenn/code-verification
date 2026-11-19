/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3
import Computational.Proofs.ReductionDsl.SM.RedFS
import Computational.Proofs.ReductionDsl.Notation

/-!
# Stage-2 Multi-Session FS-AEAD Reductions & Bounds for Shifted `DeliverForge` (`B1` & `B2`, `[B7]`)

Defines `redFSAuthDFShiftedPaperMultiGenProg`, `redFSAuthDFShiftedPaperMultiProg`, and
`redFSAuthDFShiftedDir2PaperMultiProg` over `fsaeadMultiHeaderAdIface`, together with query bounds
and evaluation bridges.-/

public section

set_option autoImplicit false

open CryptoGames (AEADScheme CKAScheme FSAEADScheme PRFPRNG)
open CryptoGames.CKA (ckaSMQDF)
open CryptoGames.PRFPRNG (prngOps prngSMCodecDF prngSig)
open CryptoGames.SM.Construction (FSMultiSpec FSMultiState Header Mode PartyState finishFSMultiE fsClamp fsHdrDecWt fsMultiEsTy fsaeadMultiHeaderAdIface hooksFSMulti hooksFSMultiC initFSMultiEStateC initFSMultiRaw)
open CryptoGames.SM.Engine (EState TComp VP authOut challEC commitEC corrECShiftedPaper deliverEC deliverForgeEC deliverForgeECB1 deliverForgeECGen implECDFShiftedPaperGen implECShiftedPaperGen injectEC injectECB1 injectECGen modeCfgEC transmitEC vRecvC vRecvStep1C vSendC vSendStep1C)
open ReductionDsl (CostedReduction Expr handlerImpl)

namespace Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2Aux

open OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation

section HooksFSMultiCDFShiftedPaper

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

section ClampEvalHelpers

set_option linter.unusedSectionVars false
variable [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K]
open _root_.CryptoGames.SM (Config Pos Record)
open _root_.CryptoGames.SM.Construction (FSMultiBook FSMultiEngineInv FSMultiHBounded FSVROkMultiStep
  epMgmt_st_eq fsMultiHsEnc fsMultiVpEnc hooksFSMultiC_agrees hooksFSMultiL
  hooksFSMulti_vrInv_fromAEADPRG liftFSMulti lookupMultiF mkParties realParty regSessMulti
  regSessOptMulti rootFSMulti vRecv_fsClamp_multi_eq)
open _root_.CryptoGames.SM.Construction.DeliverForge (afterCorrShifted corrEShiftedPaper deliverForgeE
  deliverForgeEB1 implEDFShiftedPaperGen injectEB1 trivB1)
open _root_.CryptoGames.SM.Engine (HM Policy SMEngineInv SMVRInv abortE challE challE_inv coinsE commitE
  corrEShiftedPaper_inv deliverE deliverE_inv deliverForgeEB1_inv deliverForgeEGen
  deliverForgeEGen_inv deliverForgeE_inv esEnc eval_bind eval_ret
  implEDFShiftedPaper_b_eq implEDFShiftedPaper_inv implEDFShiftedPaper_vrInv injectEB1_inv
  injectE injectEGen injectEGen_inv injectE_inv liftH modeCfgEC_agrees rdecDF_implECDFShiftedPaper_eval
  run_liftH_bind transmitE transmitE_inv vRecv vRecvStep1 vRecv_eq_bind
  vSend vSendStep1 vSend_eq_bind vpTblEnc)
private theorem hooksFSMultiL_reveal_eq (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (hvR : ∀ t, L ≤ t → vp.vR t = none) :
    ∀ ctx P, (hooksFSMultiL cka prng fs L Δcka mo gMain la).reveal ctx P vp =
      (hooksFSMulti cka prng fs Δcka mo gMain la).reveal ctx P vp := by
  intro ctx P
  have hvR_eq : (fun t => if t < L then match vp.vR t with | some (.inl rs) => some rs | _ => none else none) =
      (fun t => match vp.vR t with | some (.inl rs) => some rs | _ => none) := by
    funext t; by_cases ht : t < L
    · simp [ht]
    · simp [ht, hvR t (Nat.le_of_not_lt ht)]
  have hTail : ∀ (vS? : Option (Option SS)) (s₁ : FSMultiState T RSt K I E), ((match vS? with
        | none => pure none
        | some vS =>
          if (match vp.vR mo.tStar with | some (.inr _) => true | _ => false) = true then pure none
          else pure (some (realParty vp vp.γ vp.root vS fun t =>
            if t < L then match vp.vR t with | some (.inl rs) => some rs | _ => none else none)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) (Option (PartyState Γ T RSt SS RS))).run s₁) =
      ((match vS? with
        | none => pure none
        | some vS =>
          if (match vp.vR mo.tStar with | some (.inr _) => true | _ => false) = true then pure none
          else pure (some (realParty vp vp.γ vp.root vS fun t =>
            match vp.vR t with | some (.inl rs) => some rs | _ => none)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) (Option (PartyState Γ T RSt SS RS))).run s₁) := by
    intro vS? s₁; rcases vS? with _ | vS; · rfl
    dsimp only; split_ifs; · rfl
    simp only [StateT.run_pure]; congr 4
  refine StateT.ext fun s => ?_; unfold hooksFSMultiL hooksFSMulti; dsimp only
  rcases vp.vS with _ | (ss | sIdx)
  · simp only [pure_bind]; exact hTail (some none) s
  · simp only [pure_bind]; exact hTail (some (some ss)) s
  · by_cases hla : la = true
    · simp only [hla, ↓reduceIte]; rfl
    · simp only [hla, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine bind_congr fun ⟨ans, s₁⟩ => ?_
      rcases ans with _ | ss; · rfl
      simp only [StateT.run_bind, StateT.run_modify, pure_bind]; exact hTail (some (some ss)) _
private theorem corrEShiftedPaper_hooksFSMultiL_eq
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L l : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode)
    (gMain la : Bool) (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) :
    ∀ P (_ : ∀ t, L ≤ t → (es.g.st P).vR t = none),
      (corrEShiftedPaper l (hooksFSMultiL cka prng fs L Δcka mo gMain la) π P).run es =
        (corrEShiftedPaper l (hooksFSMulti cka prng fs Δcka mo gMain la) π P).run es := by
  intro P hvR; unfold corrEShiftedPaper; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !es.g.corrAllowedPaper P)
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp [hdoom]
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        hooksFSMultiL_reveal_eq cka prng fs L Δcka mo gMain la (es.g.st P) hvR es.g P]
private theorem implEDFShiftedPaper_hooksFSMultiL_eq (b1 : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L l Δ qep maxSkip tStar : ℕ)
    (cfg : Config M) (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (q : (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hVR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (implEDFShiftedPaperGen b1 l (hooksFSMultiL cka prng fs L Δcka mo gMain la) Δ qep maxSkip
        tStar cfg π (.inr q)).run es =
      (implEDFShiftedPaperGen b1 l (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep maxSkip
        tStar cfg π (.inr q)).run es := by
  rcases q with (((((arg | arg) | arg) | arg) | P) | arg)
  · rfl
  · rfl
  · rfl
  · cases b1 <;> rfl
  · exact corrEShiftedPaper_hooksFSMultiL_eq cka prng fs L l π Δcka mo gMain la es P (hVR P)
  · cases b1 <;> rfl
private def bookTransLen {T' E' : Type} (book : ℕ → Option (FSMultiBook T' E')) (sIdx : ℕ) : ℕ :=
  match book sIdx with | some bk => bk.fsTrans.length | none => 0
private theorem FSMultiEngineInv_bookTransLen_le {L B q : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hInv : FSMultiEngineInv L B q es) (sIdx : ℕ) : bookTransLen es.h.book sIdx + q ≤ B := by
  unfold bookTransLen; cases hbk : es.h.book sIdx with
  | none => dsimp only; have := hInv.tcur_le .A; omega
  | some bk => exact hInv.fsTrans_le sIdx bk hbk
private theorem bookTransLen_update_sCorr {T' E' : Type}
    (book : ℕ → Option (FSMultiBook T' E')) (sIdx sIdx' : ℕ) :
    bookTransLen (Function.update book sIdx (some { (book sIdx).getD {} with sCorr := true })) sIdx' =
      bookTransLen book sIdx' := by
  by_cases h : sIdx' = sIdx
  · subst h; simp only [bookTransLen, Function.update_self]; cases book sIdx' <;> rfl
  · simp [bookTransLen, Function.update_of_ne h]
private theorem bookTransLen_update_cons {T' E' : Type}
    (book : ℕ → Option (FSMultiBook T' E')) (sIdx cnt' : ℕ) (x : ℕ × Header T' × E') (sIdx' : ℕ) :
    bookTransLen (Function.update book sIdx
      (some { (book sIdx).getD {} with fsCount := cnt', fsTrans := x :: ((book sIdx).getD {}).fsTrans })) sIdx' ≤
      bookTransLen book sIdx' + 1 := by
  by_cases h : sIdx' = sIdx
  · subst h; simp only [bookTransLen, Function.update_self, List.length_cons]
    cases book sIdx' <;> simp [Option.getD]
  · simp only [bookTransLen, Function.update_of_ne h]; omega
private theorem bookTransLen_update_filter {T' E' : Type}
    (book : ℕ → Option (FSMultiBook T' E')) (sIdx : ℕ) (p : (ℕ × Header T' × E') → Bool) (sIdx' : ℕ) :
    bookTransLen (Function.update book sIdx
      (some { (book sIdx).getD {} with fsTrans := ((book sIdx).getD {}).fsTrans.filter p })) sIdx' ≤
      bookTransLen book sIdx' := by
  by_cases h : sIdx' = sIdx
  · subst h; simp only [bookTransLen, Function.update_self]
    cases book sIdx' with
    | none => simp [Option.getD]
    | some bk => exact List.length_filter_le p bk.fsTrans
  · simp [bookTransLen, Function.update_of_ne h]
private theorem liftFSMulti_state_eq {α : Type} (sIdx : ℕ)
    (q : CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((liftFSMulti sIdx q).run h), res.2 = h := by
  intro res hmem
  simp only [liftFSMulti, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨_, _, hEq⟩ := hmem; exact (Prod.mk.inj hEq).2
private theorem lookupMultiF_preserve (Ik : I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run h),
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions = h.sessions ∧ res.2.book = h.book := by
  intro res hmem; unfold lookupMultiF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  cases hlk : h.table.lookup Ik with
  | some _ =>
    simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  | none =>
    simp only [hlk, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨_, _, rfl⟩ := hmem; exact ⟨le_rfl, rfl, rfl⟩
private theorem regSessMulti_preserve (Ik : I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run h),
      res.2.table = h.table ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧ res.2.book = h.book := by
  intro res hmem; unfold regSessMulti at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem; split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨rfl, by simp, rfl⟩
private theorem regSessOptMulti_preserve (sid : Option I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((regSessOptMulti (SS := SS) (RS := RS) (M := M) sid).run h),
      res.2.table = h.table ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧ res.2.book = h.book := by
  intro res hmem; rcases sid with _ | Ik
  · simp only [regSessOptMulti, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [regSessOptMulti, StateT.run_map, support_map, Set.mem_image] at hmem
    obtain ⟨⟨idx, h'⟩, hmem', rfl⟩ := hmem; exact regSessMulti_preserve Ik h (idx, h') hmem'
private theorem rootFSMulti_preserve (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (Ik : I)
    (σ : RSt) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((rootFSMulti (SS := SS) (RS := RS) (M := M) prng mo t Ik σ).run h),
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions = h.sessions ∧ res.2.book = h.book := by
  intro res hmem; unfold rootFSMulti at hmem; split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨_, _, _, _, rfl⟩ := hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨k, h₁⟩, hlk, hmem⟩ := hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem
    exact lookupMultiF_preserve Ik h (k, h₁) hlk
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨_, _, rfl⟩ := hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
private theorem fsMultiStartSend_preserve (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (t : ℕ) (γ : Γ) (σ : RSt) (r : Option CCoins)
    (h : FSMultiState T RSt K I E) : ∀ ctx P res,
      res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P t γ σ r).run h) →
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro ctx P res hmem; dsimp only [hooksFSMulti] at hmem
  have hTail : ∀ coins : CCoins, res ∈ support (((do
        let (σ', k, sid) ← rootFSMulti prng mo t (cka.send γ coins).2.2 σ
        let optIdx ← regSessOptMulti sid
        modify fun s : FSMultiState T RSt K I E =>
          { s with cache := Function.update s.cache t (some ((cka.send γ coins).2.1, σ', k, optIdx)) }
        let ssv : SS ⊕ ℕ := match optIdx with | none => .inl (fs.initSender k) | some sIdx => .inr sIdx
        return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ', ssv)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h) →
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
    intro coins hmemC
    rw [StateT.run_bind, mem_support_bind_iff] at hmemC; obtain ⟨⟨⟨σ', k, sid⟩, h₁⟩, hrt, hmemC⟩ := hmemC
    rw [StateT.run_bind, mem_support_bind_iff] at hmemC; obtain ⟨⟨optIdx, h₂⟩, hreg, hmemC⟩ := hmemC
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmemC
    subst hmemC
    have hP1 := rootFSMulti_preserve (SS := SS) (RS := RS) (M := M) prng mo t (cka.send γ coins).2.2 σ h ((σ', k, sid), h₁) hrt
    have hP2 := regSessOptMulti_preserve (SS := SS) (RS := RS) (M := M) sid h₁ (optIdx, h₂) hreg
    exact ⟨by dsimp only; rw [hP2.1]; exact hP1.1, by dsimp only; rw [← hP1.2.1]; exact hP2.2.1,
      by dsimp only; rw [hP2.2.2, hP1.2.2]⟩
  rcases r with _ | c
  · dsimp only at hmem; rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, h₀⟩, hCoins, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hCoins
    obtain ⟨_, _, _, rfl⟩ := hCoins; exact hTail coins hmem
  · dsimp only at hmem; rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem; exact hTail c hmem
private theorem fsMultiStartRecv_preserve (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (t : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSMultiState T RSt K I E) : ∀ ctx P res,
      res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startRecv ctx P t γ σ Tn).run h) →
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro ctx P res hmem; dsimp only [hooksFSMulti] at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem; dsimp only at hmem
  have hNoneCase : res ∈ support (((if gMain then pure (some none)
        else if mo.auth && decide (t = mo.tStar) then
          if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
          else do
            let kk := cka.receive γ Tn; let _ ← lookupMultiF kk.2; let sIdx ← regSessMulti kk.2
            pure (some (some (kk.1, (prng.up σ kk.2).1, (.inr sIdx : RS ⊕ ℕ))))
        else pure (some none) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h)) →
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
    intro hmemN; split_ifs at hmemN
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN
      subst hmemN; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN
      subst hmemN; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · rw [StateT.run_bind, mem_support_bind_iff] at hmemN; obtain ⟨⟨k', h₁⟩, hlk, hmemN⟩ := hmemN
      rw [StateT.run_bind, mem_support_bind_iff] at hmemN; obtain ⟨⟨sIdx, h₂⟩, hreg, hmemN⟩ := hmemN
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN; subst hmemN
      have hP1 := lookupMultiF_preserve (SS := SS) (RS := RS) (M := M) (cka.receive γ Tn).2 h (k', h₁) hlk
      have hP2 := regSessMulti_preserve (SS := SS) (RS := RS) (M := M) (cka.receive γ Tn).2 h₁ (sIdx, h₂) hreg
      exact ⟨by dsimp only; rw [hP2.1]; exact hP1.1, by dsimp only; rw [← hP1.2.1]; exact hP2.2.1,
        by dsimp only; rw [hP2.2.2, hP1.2.2]⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN
      subst hmemN; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
  rcases hca : h.cache t with _ | ⟨Tc, σc, k, optIdx⟩
  · rw [hca] at hmem; exact hNoneCase hmem
  · rw [hca] at hmem; dsimp only at hmem; by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [hEq, ↓reduceIte] at hmem; exact hNoneCase hmem
private theorem fsMultiFsSend_preserve (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (t : ℕ) (ssv : SS ⊕ ℕ)
    (hdr : Header T) (m : M) (pair : Option (M × M)) (h : FSMultiState T RSt K I E) : ∀ ctx P res,
      res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).fsSend ctx P t ssv hdr m pair).run h) →
      res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
      (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx' + 1) := by
  intro ctx P res hmem; dsimp only [hooksFSMulti] at hmem; rcases ssv with ss | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨rfl, rfl, fun _ => Nat.le_add_right _ _⟩
  · rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem; dsimp only at hmem
    have hRest : ∀ (ok : Bool) (h₁ : FSMultiState T RSt K I E),
        h₁.table = h.table → h₁.sessions = h.sessions →
        (∀ j, bookTransLen h₁.book j = bookTransLen h.book j) →
        res ∈ support (((do
          let ok' ← pure ok
          if !ok' then return none
          let e? ← match pair with
            | some (m₀, m₁) => liftFSMulti sIdx (CryptoGames.FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
            | none => liftFSMulti sIdx (CryptoGames.FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
          match e? with
          | none => return none
          | some e =>
            modify fun s : FSMultiState T RSt K I E =>
              let b := (s.book sIdx).getD {}
              let cnt' := b.fsCount + 1
              { s with book := Function.update s.book sIdx (some { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }) }
            return some ((.inr sIdx : SS ⊕ ℕ), e) :
          HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h₁)) →
        res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
        (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx' + 1) := by
      intro ok h₁ htb hse hbk hmem2
      rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem2; dsimp only at hmem2
      cases ok
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
        subst hmem2; exact ⟨htb, hse, fun j => by rw [hbk j]; exact Nat.le_add_right _ _⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem2
        rcases pair with _ | ⟨m₀, m₁⟩ <;>
        · simp only [liftFSMulti, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem2
          obtain ⟨e?, _, hmem2⟩ := hmem2; rcases e? with _ | e
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2; exact ⟨htb, hse, fun j => by rw [hbk j]; exact Nat.le_add_right _ _⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2; refine ⟨htb, hse, fun j => ?_⟩
            dsimp only; rw [← hbk j]; exact bookTransLen_update_cons h₁.book sIdx _ _ j
    by_cases hc : (!ctx.safeCh (2 + Δcka) P && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hc, ↓reduceIte] at hmem; by_cases hla : la = true
      · simp only [hla, ↓reduceIte] at hmem; exact hRest false h rfl rfl (fun _ => rfl) hmem
      · simp only [hla, Bool.false_eq_true, ↓reduceIte, liftFSMulti, StateT.run_bind,
          StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
        obtain ⟨ans, _, hmem⟩ := hmem; rcases ans with _ | _
        · exact hRest false h rfl rfl (fun _ => rfl) hmem
        · rw [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
          refine hRest true _ ?_ ?_ ?_ hmem
          · rfl
          · rfl
          · exact bookTransLen_update_sCorr h.book sIdx
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
      exact hRest true h rfl rfl (fun _ => rfl) hmem
private theorem fsMultiFsRecv_preserve (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (t : ℕ) (rsv : RS ⊕ ℕ)
    (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E))) (h : FSMultiState T RSt K I E) :
    ∀ ctx P res,
      res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).fsRecv ctx P t rsv hdr e rec).run h) →
      res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
      (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx') := by
  intro ctx P res hmem; dsimp only [hooksFSMulti] at hmem; rcases rsv with rs | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨rfl, rfl, fun _ => le_rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    set bk : FSMultiBook T E := (h.book sIdx).getD {}
    set matched : Option (ℕ × Header T × E) := bk.fsTrans.find? (fun x => x.2 == (hdr, e))
    have hAfterOk : ∀ (la' ok : Bool) (h₁ : FSMultiState T RSt K I E),
        h₁.table = h.table → h₁.sessions = h.sessions →
        (∀ sIdx', bookTransLen h₁.book sIdx' = bookTransLen h.book sIdx') →
        res ∈ support (((do
          if !ok then return none
          let qres ← if matched.isSome then
              liftFSMulti sIdx (CryptoGames.FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
            else
              liftFSMulti sIdx (CryptoGames.FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          match qres with
          | none => return none
          | some .rejected => return some none
          | some (.accepted i mo') =>
            let s1 ← get
            let bk1 := (s1.book sIdx).getD {}
            if la' && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
              modify fun s : FSMultiState T RSt K I E => { s with lfWin := true }
              return none
            else
              let drop := (matched.map (·.1)).getD i
              modify fun s : FSMultiState T RSt K I E =>
                let b := (s.book sIdx).getD {}
                { s with book := Function.update s.book sIdx (some { b with fsTrans := b.fsTrans.filter (·.1 != drop) }) }
              match mo', rec with
              | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
              | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
              | none, none => return none :
          HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h₁)) →
        res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
        (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx') := by
      intro la' ok h₁ hTbl hSess hTr hmem₁
      cases ok
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem₁
        subst hmem₁; exact ⟨hTbl, hSess, fun j => le_of_eq (hTr j)⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem₁
        have hAfterQ : ∀ qres : Option (CryptoGames.FSAEAD.ReceiveResult M),
            res ∈ support (((match qres with
              | none => pure none
              | some .rejected => pure (some none)
              | some (.accepted i mo') => do
                let s1 ← get
                let bk1 := (s1.book sIdx).getD {}
                if la' && matched.isNone && (!bk1.sCorr) && decide (bk1.fsCount < i) then
                  modify fun s : FSMultiState T RSt K I E => { s with lfWin := true }; return none
                else
                  let drop := (matched.map (·.1)).getD i
                  modify fun s : FSMultiState T RSt K I E =>
                    let b := (s.book sIdx).getD {}
                    { s with book := Function.update s.book sIdx (some { b with fsTrans := b.fsTrans.filter (·.1 != drop) }) }
                  match mo', rec with
                  | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
                  | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
                  | none, none => return none :
              HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h₁)) →
            res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
            (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx') := by
          intro qres hmemQ; rcases qres with _ | (_ | ⟨i, mo'⟩)
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ
            subst hmemQ; exact ⟨hTbl, hSess, fun j => le_of_eq (hTr j)⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ
            subst hmemQ; exact ⟨hTbl, hSess, fun j => le_of_eq (hTr j)⟩
          · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmemQ; split_ifs at hmemQ
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmemQ
              subst hmemQ; exact ⟨hTbl, hSess, fun j => le_of_eq (hTr j)⟩
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmemQ
              rcases mo' with _ | m
              · rcases rec with _ | r <;>
                  (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ;
                   subst hmemQ; exact ⟨hTbl, hSess, fun j => (bookTransLen_update_filter h₁.book sIdx _ j).trans (le_of_eq (hTr j))⟩)
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ
                subst hmemQ; exact ⟨hTbl, hSess, fun j => (bookTransLen_update_filter h₁.book sIdx _ j).trans (le_of_eq (hTr j))⟩
        by_cases hm : matched.isSome = true <;>
          (simp only [hm, Bool.false_eq_true, ↓reduceIte, liftFSMulti, StateT.run_bind,
             StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem₁;
           obtain ⟨qres, _, hmem₁⟩ := hmem₁; exact hAfterQ qres hmem₁)
    by_cases hc : (matched.isNone && !(CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t) && !bk.sCorr) = true
    · simp only [hc, ↓reduceIte] at hmem; by_cases hla : la = true
      · simp only [hla, ↓reduceIte] at hmem
        exact hAfterOk _ false h rfl rfl (fun _ => rfl) hmem
      · simp only [hla, Bool.false_eq_true, ↓reduceIte] at hmem
        rw [StateT.run_bind, liftFSMulti, StateT.run_lift] at hmem
        simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hmem
        obtain ⟨ans, _, hmem⟩ := hmem; rcases ans with _ | _
        · exact hAfterOk _ false h rfl rfl (fun _ => rfl) hmem
        · rw [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
          refine hAfterOk _ true _ ?_ ?_ ?_ hmem
          · rfl
          · rfl
          · exact bookTransLen_update_sCorr h.book sIdx
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
      exact hAfterOk _ true h rfl rfl (fun _ => rfl) hmem
private theorem fsMultiReveal_preserve (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (h : FSMultiState T RSt K I E) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) : ∀ ctx P res,
      res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).reveal ctx P vp).run h) →
      res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
      (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx') := by
  intro ctx P res hmem; simp only [hooksFSMulti, pure_bind] at hmem
  have hStep2 : ∀ (vS : Option SS) (h₁ : FSMultiState T RSt K I E),
      h₁.table = h.table → h₁.sessions = h.sessions →
      (∀ j, bookTransLen h₁.book j ≤ bookTransLen h.book j) →
      res ∈ support (((if (match vp.vR mo.tStar with | some (.inr _) => true | _ => false) = true then pure none
        else pure (some (realParty vp vp.γ vp.root vS fun t =>
          match vp.vR t with | some (.inl rs) => some rs | _ => none)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h₁)) →
      res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
      (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx') := by
    intro vS h₁ htb hse hbk hmem2; split_ifs at hmem2 <;>
      (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2;
       subst hmem2; exact ⟨htb, hse, hbk⟩)
  rcases hvS : vp.vS with _ | (ss | sIdx)
  · simp only [hvS] at hmem; exact hStep2 none h rfl rfl (fun _ => le_rfl) hmem
  · simp only [hvS] at hmem; exact hStep2 (some ss) h rfl rfl (fun _ => le_rfl) hmem
  · simp only [hvS] at hmem; by_cases hla : la = true
    · simp only [hla, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨rfl, rfl, fun _ => le_rfl⟩
    · simp only [hla, Bool.false_eq_true, ↓reduceIte, liftFSMulti, StateT.run_bind,
        StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨ans, _, hmem⟩ := hmem; rcases ans with _ | ss
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨rfl, rfl, fun _ => le_rfl⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
        refine hStep2 (some ss) _ ?_ ?_ ?_ hmem
        · rfl
        · rfl
        · exact fun j => le_of_eq (bookTransLen_update_sCorr h.book sIdx j)
private theorem vSend_fsMulti_preserve (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (h : FSMultiState T RSt K I E) : ∀ ctx P res,
      res ∈ support ((vSend (hooksFSMulti cka prng fs Δcka mo gMain la) ctx P s m pair r).run h) →
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
      (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx' + 1) ∧
      (∀ st' c, res.1 = some (st', c) → s.tcur ≤ st'.tcur ∧ st'.tcur ≤ s.tcur + 1 ∧ st'.vR = s.vR) := by
  intro ctx P ⟨vsRes, h'⟩ hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
  have hStep1 : h₁.table.length ≤ h.table.length + 1 ∧ h₁.sessions.length ≤ h.sessions.length + 1 ∧
      h₁.book = h.book ∧ (∀ s₁, s₁? = some s₁ → s.tcur ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧ s₁.vR = s.vR) := by
    unfold vSendStep1 at hmem1; split_ifs at hmem1
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem1
      obtain ⟨⟨ssRes, h₁'⟩, hss, hmem1⟩ := hmem1
      have hPres := fsMultiStartSend_preserve cka prng fs Δcka mo gMain la (s.tcur + 1) s.γ s.root r h ctx P (ssRes, h₁') hss
      rcases ssRes with _ | ⟨γ', T', σ', ss⟩ <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1;
         rcases hmem1 with ⟨rfl, rfl⟩)
      · exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
      · exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun s₁ hs₁ => by cases hs₁; exact ⟨Nat.le_succ _, le_rfl, rfl⟩⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      rcases hmem1 with ⟨rfl, rfl⟩
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl, fun s₁ hs₁ => by cases hs₁; exact ⟨le_rfl, Nat.le_succ _, rfl⟩⟩
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hmem2 with ⟨rfl, rfl⟩
    exact ⟨hStep1.1, hStep1.2.1, fun sIdx' => by rw [hStep1.2.2.1]; exact Nat.le_add_right _ _, fun _ _ h => by cases h⟩
  · have hs₁ := hStep1.2.2.2 s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hStep1.1, hStep1.2.1, fun sIdx' => by rw [hStep1.2.2.1]; exact Nat.le_add_right _ _,
        fun st' c hEq => by cases hEq; exact hs₁⟩
    · simp only [hvS, StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
      have hPres2 := fsMultiFsSend_preserve cka prng fs Δcka mo gMain la s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m pair h₁ ctx P (fsRes, h₂) hfs
      rcases fsRes with _ | ⟨v', e⟩ <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2;
         rcases hmem2 with ⟨rfl, rfl⟩)
      · exact ⟨by rw [hPres2.1]; exact hStep1.1, by rw [hPres2.2.1]; exact hStep1.2.1,
          fun sIdx' => by rw [← hStep1.2.2.1]; exact hPres2.2.2 sIdx', fun _ _ h => by cases h⟩
      · exact ⟨by rw [hPres2.1]; exact hStep1.1, by rw [hPres2.2.1]; exact hStep1.2.1,
          fun sIdx' => by rw [← hStep1.2.2.1]; exact hPres2.2.2 sIdx', fun st' c hEq => by cases hEq; exact hs₁⟩
private theorem vRecv_fsMulti_preserve (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (c : Header T × E)
    (rec : Option (CryptoGames.SM.Record M (Header T × E))) (h : FSMultiState T RSt K I E)
    (hvR : ∀ t, s.tcur < t → s.vR t = none) : ∀ ctx P res,
      res ∈ support ((vRecv (hooksFSMulti cka prng fs Δcka mo gMain la) ctx P s c rec).run h) →
      res.2.table.length ≤ h.table.length + 1 ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
      (∀ sIdx', bookTransLen res.2.book sIdx' ≤ bookTransLen h.book sIdx') ∧
      (∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
        st'.tcur ≤ s.tcur + 1 ∧ (∀ t, st'.tcur < t → st'.vR t = none)) := by
  intro ctx P ⟨vrRes, h'⟩ hmem; rw [vRecv_eq_bind] at hmem
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, fun _ => le_rfl, fun _ _ _ _ h => by cases h⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
    have htle : c.1.1 ≤ s.tcur + 1 := by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1; omega
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    have hStep1 : h₁.table.length ≤ h.table.length + 1 ∧ h₁.sessions.length ≤ h.sessions.length + 1 ∧
        h₁.book = h.book ∧ (∀ s₁, s₁? = some (some s₁) →
          c.1.1 ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧ (∀ t, s₁.tcur < t → s₁.vR t = none)) := by
      unfold vRecvStep1 at hmem1; by_cases h2 : c.1.1 = s.tcur + 1
      · simp only [h2, ↓reduceIte] at hmem1; rcases hTn : c.1.2 with _ | Tn
        · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
          rcases hmem1 with ⟨rfl, rfl⟩; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl, fun _ h => by cases h⟩
        · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem1
          obtain ⟨⟨srRes, h₁'⟩, hsr, hmem1⟩ := hmem1
          have hPres := fsMultiStartRecv_preserve cka prng fs Δcka mo gMain la (s.tcur + 1) s.γ s.root Tn h ctx P (srRes, h₁') hsr
          rcases srRes with _ | _ | ⟨γ', σ', rs⟩ <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1;
             rcases hmem1 with ⟨rfl, rfl⟩)
          · exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
          · exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
          · refine ⟨hPres.1, hPres.2.1, hPres.2.2, fun s₁ hs₁ => ?_⟩
            cases hs₁; refine ⟨by omega, le_rfl, fun t ht => ?_⟩
            dsimp only at ht ⊢; rw [Function.update_of_ne (by omega)]; exact hvR t (by omega)
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl, fun s₁ hs₁ => by cases hs₁; exact ⟨by omega, Nat.le_succ _, hvR⟩⟩
    rcases s₁? with _ | _ | s₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hStep1.1, hStep1.2.1, fun sIdx' => by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hStep1.1, hStep1.2.1, fun sIdx' => by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
    · have hs₁ := hStep1.2.2.2 s₁ rfl
      rcases hvR1 : s₁.vR c.1.1 with _ | v
      · simp only [hvR1, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨hStep1.1, hStep1.2.1, fun sIdx' => by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
      · simp only [hvR1, StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨frRes, h₂⟩, hfr, hmem2⟩ := hmem2
        have hPres2 := fsMultiFsRecv_preserve cka prng fs Δcka mo gMain la c.1.1 v c.1 c.2 rec h₁ ctx P (frRes, h₂) hfr
        rcases frRes with _ | _ | ⟨v', i, m⟩ <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2;
           rcases hmem2 with ⟨rfl, rfl⟩)
        · exact ⟨by rw [hPres2.1]; exact hStep1.1, by rw [hPres2.2.1]; exact hStep1.2.1,
            fun sIdx' => by rw [← hStep1.2.2.1]; exact hPres2.2.2 sIdx', fun _ _ _ _ h => by cases h⟩
        · exact ⟨by rw [hPres2.1]; exact hStep1.1, by rw [hPres2.2.1]; exact hStep1.2.1,
            fun sIdx' => by rw [← hStep1.2.2.1]; exact hPres2.2.2 sIdx', fun _ _ _ _ h => by cases h⟩
        · refine ⟨by rw [hPres2.1]; exact hStep1.1, by rw [hPres2.2.1]; exact hStep1.2.1,
            fun sIdx' => by rw [← hStep1.2.2.1]; exact hPres2.2.2 sIdx', fun st' t' i' m' hEq => ?_⟩
          cases hEq; refine ⟨hs₁.2.1, fun t ht => ?_⟩
          dsimp only at ht ⊢; rw [Function.update_of_ne (by omega)]; exact hs₁.2.2 t ht
private theorem commitE_fsMulti_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) :
    ∀ s P old new pos, (commitE (hooksFSMulti cka prng fs Δcka mo gMain la) s P old new pos).run es =
        pure (some { s.accept P new pos with st := Function.update (s.accept P new pos).st P new }, es) := by
  intro s P old new pos; unfold commitE
  simp only [pure_bind, run_liftH_bind, hooksFSMulti, StateT.run_pure]
private theorem mkFSMultiEngineInv {L B q : ℕ}
    {es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hSm : SMEngineInv L B q es'.g) (htb : es'.h.table.length + q ≤ B + 1)
    (hse : es'.h.sessions.length + q ≤ B + 1) (hbk : ∀ sIdx', bookTransLen es'.h.book sIdx' + q ≤ B)
    (htcur : ∀ P, (es'.g.st P).tcur + q ≤ B)
    (hvR : ∀ P t, (es'.g.st P).tcur < t → (es'.g.st P).vR t = none) : FSMultiEngineInv L B q es' :=
  ⟨hSm, htb, hse, fun sIdx bk h => by have := hbk sIdx; simp [bookTransLen, h] at this; exact this, htcur, hvR⟩
private theorem mkFSMultiEngineInv_unchangedSt {L B q : ℕ}
    {es es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hInv : FSMultiEngineInv L B (q + 1) es) (hSm : SMEngineInv L B q es'.g) (hst : es'.g.st = es.g.st)
    (htb : es'.h.table.length ≤ es.h.table.length + 1)
    (hse : es'.h.sessions.length ≤ es.h.sessions.length + 1)
    (hbk : ∀ sIdx', bookTransLen es'.h.book sIdx' ≤ bookTransLen es.h.book sIdx' + 1) :
    FSMultiEngineInv L B q es' := by
  have hInvQ := hInv.mono (Nat.le_succ q)
  exact mkFSMultiEngineInv hSm (by have := hInv.table_le; omega) (by have := hInv.sessions_le; omega)
    (fun sIdx' => by have := FSMultiEngineInv_bookTransLen_le hInv sIdx'; have := hbk sIdx'; omega)
    (fun Q => by rw [hst]; exact hInvQ.tcur_le Q)
    (fun Q t ht => by rw [hst] at ht ⊢; exact hInvQ.vR_none_of_gt Q t ht)
private theorem mkFSMultiEngineInv_updatedSt {L B q : ℕ}
    {es es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hInv : FSMultiEngineInv L B (q + 1) es) (hSm : SMEngineInv L B q es'.g)
    {P} {st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)} (hst : es'.g.st = Function.update es.g.st P st')
    (htcur' : st'.tcur ≤ (es.g.st P).tcur + 1) (hvR' : ∀ t, st'.tcur < t → st'.vR t = none)
    (htb : es'.h.table.length ≤ es.h.table.length + 1)
    (hse : es'.h.sessions.length ≤ es.h.sessions.length + 1)
    (hbk : ∀ sIdx', bookTransLen es'.h.book sIdx' ≤ bookTransLen es.h.book sIdx' + 1) :
    FSMultiEngineInv L B q es' := by
  have hInvQ := hInv.mono (Nat.le_succ q)
  refine mkFSMultiEngineInv hSm (by have := hInv.table_le; omega) (by have := hInv.sessions_le; omega)
    (fun sIdx' => by have := FSMultiEngineInv_bookTransLen_le hInv sIdx'; have := hbk sIdx'; omega)
    (fun Q => ?_) (fun Q t ht => ?_)
  · rw [hst]; by_cases hQ : Q = P
    · subst hQ; rw [Function.update_self]; have := hInv.tcur_le Q; omega
    · rw [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
  · rw [hst] at ht ⊢; by_cases hQ : Q = P
    · subst hQ; rw [Function.update_self] at ht ⊢; exact hvR' t ht
    · rw [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
private theorem transmitE_fsMulti_inv (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ arg res, res ∈ support ((transmitE (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep π arg).run es) →
      FSMultiEngineInv L B q res.2 := by
  intro ⟨P, m, r⟩ ⟨out, es'⟩ hmem
  have hInvQ := hInv.mono (Nat.le_succ q)
  have hSm := transmitE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) π es (P, m, r) hInv.sm (out, es') hmem
  unfold transmitE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem; by_cases hdoom : π.leakDoom es.g s₁
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact mkFSMultiEngineInv_unchangedSt hInv hSm rfl (Nat.le_add_right _ _) (Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _)
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        have hPres := vSend_fsMulti_preserve cka prng fs Δcka mo gMain la (s₁.st P) m none r es.h s₁ P (vsRes, h') hvs
        dsimp only at hPres; have hSt₁ : s₁.st = es.g.st := epMgmt_st_eq hep
        rcases vsRes with _ | ⟨st', c⟩ <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
           rcases hmem with ⟨_, rfl⟩)
        · exact mkFSMultiEngineInv_unchangedSt hInv hSm rfl hPres.1 hPres.2.1 hPres.2.2.1
        · have hst' := hPres.2.2.2 st' c rfl; rw [hSt₁] at hst'
          exact mkFSMultiEngineInv_updatedSt hInv hSm (P := P) (st' := st')
            (by dsimp only [CryptoGames.SM.GameState.record]; rw [hSt₁]) hst'.2.1
            (fun t ht => by rw [hst'.2.2]; exact hInv.vR_none_of_gt P t (by have := hst'.1; omega))
            hPres.1 hPres.2.1 hPres.2.2.1
private theorem challE_fsMulti_inv (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (cfg : Config M) (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ arg res, res ∈ support ((challE (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep cfg π arg).run es) →
      FSMultiEngineInv L B q res.2 := by
  intro ⟨P, m₀, m₁, r⟩ ⟨out, es'⟩ hmem
  have hInvQ := hInv.mono (Nat.le_succ q)
  have hSm := challE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) cfg π es (P, m₀, m₁, r) hInv.sm (out, es') hmem
  unfold challE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem; by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem; by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact mkFSMultiEngineInv_unchangedSt hInv hSm rfl (Nat.le_add_right _ _) (Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _)
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hPres := vSend_fsMulti_preserve cka prng fs Δcka mo gMain la (s₁.st P) _ (some (m₀, m₁)) r es.h s₁ P (vsRes, h') hvs
          dsimp only at hPres; have hSt₁ : s₁.st = es.g.st := epMgmt_st_eq hep
          rcases vsRes with _ | ⟨st', c⟩ <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩)
          · exact mkFSMultiEngineInv_unchangedSt hInv hSm rfl hPres.1 hPres.2.1 hPres.2.2.1
          · have hst' := hPres.2.2.2 st' c rfl; rw [hSt₁] at hst'
            exact mkFSMultiEngineInv_updatedSt hInv hSm (P := P) (st' := st')
              (by dsimp only [CryptoGames.SM.GameState.record]; rw [hSt₁]) hst'.2.1
              (fun t ht => by rw [hst'.2.2]; exact hInv.vR_none_of_gt P t (by have := hst'.1; omega))
              hPres.1 hPres.2.1 hPres.2.2.1
private theorem accept_update_st_eq
    {s : CryptoGames.SM.GameState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)}
    (P : CryptoGames.Party) (st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : CryptoGames.SM.Pos) :
    Function.update (s.accept P st' pos).st P st' = Function.update s.st P st' := by
  funext Q; cases Q <;> cases P <;> rfl
private theorem vRecv_post_fsMulti_inv (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q : ℕ} (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : FSMultiEngineInv L B (q + 1) es) (hSm : SMEngineInv L B q es'.g)
    (P : CryptoGames.Party) (cTarget : Header T × E) (rec : Option (Record M (Header T × E)))
    {vrRes : Option (Option (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) × ℕ × ℕ × M))} {h' : FSMultiState T RSt K I E}
    (hvr : (vrRes, h') ∈ support ((vRecv (hooksFSMulti cka prng fs Δcka mo gMain la) es.g P (es.g.st P) cTarget rec).run es.h))
    (hh : es'.h = h') (hst : es'.g.st = es.g.st ∨ ∃ st' t' i' m',
      vrRes = some (some (st', t', i', m')) ∧ es'.g.st = Function.update es.g.st P st') :
    FSMultiEngineInv L B q es' := by
  have hPres := vRecv_fsMulti_preserve cka prng fs Δcka mo gMain la (es.g.st P) cTarget rec es.h (hInv.vR_none_of_gt P) es.g P (vrRes, h') hvr
  dsimp only at hPres; rw [← hh] at hPres
  have hbk1 : ∀ sIdx', bookTransLen es'.h.book sIdx' ≤ bookTransLen es.h.book sIdx' + 1 :=
    fun sIdx' => le_trans (hPres.2.2.1 sIdx') (Nat.le_add_right _ _)
  rcases hst with hst | ⟨st', t', i', m', hvrEq, hst⟩
  · exact mkFSMultiEngineInv_unchangedSt hInv hSm hst hPres.1 hPres.2.1 hbk1
  · have hst' := hPres.2.2.2 st' t' i' m' hvrEq
    exact mkFSMultiEngineInv_updatedSt hInv hSm hst hst'.1 hst'.2 hPres.1 hPres.2.1 hbk1
private theorem deliverE_fsMulti_inv (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q maxSkip : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ arg res, res ∈ support ((deliverE (hooksFSMulti cka prng fs Δcka mo gMain la) maxSkip cfg arg).run es) →
      FSMultiEngineInv L B q res.2 := by
  intro ⟨P, c⟩ ⟨out, es'⟩ hmem
  have hInvQ := hInv.mono (Nat.le_succ q)
  have hSm := deliverE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) cfg es (P, c) hInv.sm (out, es') hmem
  unfold deliverE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c (some r) hvr rfl (.inl rfl)
      · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r) <;>
          (simp only [hmust, ↓reduceIte, Bool.false_eq_true, StateT.run_bind, StateT.run_modify,
             StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
           rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c (some r) hvr rfl (.inl rfl))
      · simp only [StateT.run_bind, commitE_fsMulti_eq, pure_bind, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c (some r) hvr rfl
          (.inr ⟨st', t', i', m', rfl, by dsimp only; split_ifs <;> exact accept_update_st_eq P st' r.pos⟩)
private theorem injectEGen_fsMulti_inv (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep tStar : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ arg res, res ∈ support ((injectEGen b1 (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep tStar cfg arg).run es) →
      FSMultiEngineInv L B q res.2 := by
  intro ⟨P, c⟩ ⟨out, es'⟩ hmem
  have hSm := injectEGen_inv b1 (hooksFSMulti cka prng fs Δcka mo gMain la) cfg es (P, c) hInv.sm (out, es') hmem
  cases b1
  · simp only [injectEGen, Bool.false_eq_true, ↓reduceIte] at hmem
    unfold injectE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem; rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
        · simp only [hqep, ↓reduceIte] at hmem; by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMulti_eq, pure_bind, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inr ⟨st', t', i', m', rfl, accept_update_st_eq P st' _⟩)
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem; by_cases hf : cfg.injectFull t'
            · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
            · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
  · simp only [injectEGen, ↓reduceIte] at hmem
    unfold injectEB1 abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem; rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
        · simp only [hqep, ↓reduceIte] at hmem; by_cases htriv : trivB1 tStar es.g ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMulti_eq, pure_bind, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inr ⟨st', t', i', m', rfl, accept_update_st_eq P st' _⟩)
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem; by_cases hf : cfg.injectFull t'
            · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
            · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c none hvr rfl (.inl rfl)
private theorem deliverForgeEGen_fsMulti_inv (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep tStar : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ arg res, res ∈ support ((deliverForgeEGen b1 (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep tStar cfg arg).run es) →
      FSMultiEngineInv L B q res.2 := by
  intro ⟨P, c, c'⟩ ⟨out, es'⟩ hmem
  have hSm := deliverForgeEGen_inv b1 (hooksFSMulti cka prng fs Δcka mo gMain la) cfg es (P, c, c') hInv.sm (out, es') hmem
  cases b1
  · simp only [deliverForgeEGen, Bool.false_eq_true, ↓reduceIte] at hmem
    unfold deliverForgeE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem; rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
      · simp only [htr] at hmem; by_cases hbad : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem; rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
          · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch)
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem; by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
              · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMulti_eq, pure_bind, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩
                exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inr ⟨st', t', i', m', rfl, accept_update_st_eq P st' _⟩)
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem; by_cases hf : cfg.injectFull t'
                · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
                · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
  · simp only [deliverForgeEGen, ↓reduceIte] at hmem
    unfold deliverForgeEB1 abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem; rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
      · simp only [htr] at hmem; by_cases hbad : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ q)
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem; rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
          · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch)
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem; by_cases htriv : trivB1 tStar es.g ⟨P.other, t', i'⟩
              · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMulti_eq, pure_bind, StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩
                exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inr ⟨st', t', i', m', rfl, accept_update_st_eq P st' _⟩)
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem; by_cases hf : cfg.injectFull t'
                · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
                · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact vRecv_post_fsMulti_inv cka prng fs Δcka mo gMain la es _ hInv hSm P c' none hvr rfl (.inl rfl)
private theorem corrEShiftedPaper_fsMulti_inv (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q : ℕ} (l : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ P res, res ∈ support ((corrEShiftedPaper l (hooksFSMulti cka prng fs Δcka mo gMain la) π P).run es) →
      FSMultiEngineInv L B q res.2 := by
  intro P ⟨out, es'⟩ hmem
  have hInvQ := hInv.mono (Nat.le_succ q)
  have hSm := corrEShiftedPaper_inv (hooksFSMulti cka prng fs Δcka mo gMain la) l π es P hInv.sm (out, es') hmem
  unfold corrEShiftedPaper abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact mkFSMultiEngineInv_unchangedSt hInv hSm rfl (Nat.le_add_right _ _) (Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _)
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hPres := fsMultiReveal_preserve cka prng fs Δcka mo gMain la es.h (es.g.st P) es.g P (revRes, h') hrev
      have hbk1 : ∀ sIdx', bookTransLen h'.book sIdx' ≤ bookTransLen es.h.book sIdx' + 1 :=
        fun sIdx' => le_trans (hPres.2.2 sIdx') (Nat.le_add_right _ _)
      rcases revRes with _ | st <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩;
         exact mkFSMultiEngineInv_unchangedSt hInv hSm rfl (by dsimp only; rw [hPres.1]; exact Nat.le_add_right _ _)
           (by dsimp only; rw [hPres.2.1]; exact Nat.le_add_right _ _) hbk1)
private theorem implEDFShiftedPaper_fsMulti_inv (b1 : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {L B q Δ qep maxSkip tStar : ℕ} (l : ℕ)
    (cfg : Config M) (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (q_df : (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((implEDFShiftedPaperGen b1 l (hooksFSMulti cka prng fs Δcka mo gMain la)
        Δ qep maxSkip tStar cfg π (.inr q_df)).run es), FSMultiEngineInv L B q res.2 := by
  rcases q_df with (((((arg | arg) | arg) | arg) | P) | arg)
  · exact transmitE_fsMulti_inv cka prng fs π Δcka mo gMain la es hInv arg
  · exact challE_fsMulti_inv cka prng fs cfg π Δcka mo gMain la es hInv arg
  · exact deliverE_fsMulti_inv cka prng fs cfg Δcka mo gMain la es hInv arg
  · exact injectEGen_fsMulti_inv b1 cka prng fs cfg Δcka mo gMain la es hInv arg
  · exact corrEShiftedPaper_fsMulti_inv cka prng fs l π Δcka mo gMain la es hInv P
  · exact deliverForgeEGen_fsMulti_inv b1 cka prng fs cfg Δcka mo gMain la es hInv arg
include ckaInitA ckaInitB prngInit lam sampKR sampKC in
theorem simulateQ_implECDFShiftedPaper_fsMulti_eq (b1 : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q l Δ Δcka qep tStar : ℕ) (mo mo' : Mode) (gMain la : Bool)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) = fs.receive rs hdr e) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ}, oa.IsQueryBoundP
        (ReductionDsl.isGameQuery (G := CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)),
        FSMultiEngineInv L B_q qAdv es → (simulateQ
          (handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
              L l Δ qep fs.maxSkip tStar (modeCfgEC OO mo') mo'.policy .v0 .v1)) oa).run (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E))
            (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M)) es) =
          (Prod.map id (esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M))) <$>
            (simulateQ (implEDFShiftedPaperGen b1 l (hooksFSMulti cka prng fs Δcka mo gMain la)
              Δ qep fs.maxSkip tStar mo'.cfg mo'.policy) oa).run es) ∧ ∀ res ∈ support ((simulateQ
            (implEDFShiftedPaperGen b1 l (hooksFSMulti cka prng fs Δcka mo gMain la)
              Δ qep fs.maxSkip tStar mo'.cfg mo'.policy) oa).run es),
          FSMultiEngineInv L B_q 0 res.2 ∧ res.2.g.b = es.g.b := by
  have hHk := hooksFSMultiC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) cka prng fs L B Δcka mo gMain la
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend heqT heqI heqE hSampCCoins hSampI hSampK hFsRecvB
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR)
    (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) (γvT := .base .γ)
    (svT := .base .sig) (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
  let hsE := fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (T := T)
    (RSt := RSt) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E)
  have hVp : fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR)
      (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) = vpE := rfl
  intro α oa; induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hInv; refine ⟨by simp [simulateQ_pure, Prod.map], fun res hmem => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_bind, simulateQ_query, StateT.run_bind, simulateQ_bind, simulateQ_query, StateT.run_bind]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    cases q with
    | inl n =>
      have hCoinL : ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
              L l Δ qep fs.maxSkip tStar (modeCfgEC OO mo') mo'.policy .v0 .v1)) (.inl n)).run
            (esEnc (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I)
              (KR := KR) (K := K) (M := M) (E := E)) hsE es) =
          (fun u => (u, esEnc (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins)
              (I := I) (KR := KR) (K := K) (M := M) (E := E)) hsE es)) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (implEDFShiftedPaperGen b1 l (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep fs.maxSkip
            tStar mo'.cfg mo'.policy (.inl n)).run es =
          (fun u => (u, es)) <$> query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [implEDFShiftedPaperGen, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hInv).1, fun res hmem => ?_⟩
      rw [mem_support_bind_iff] at hmem; obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [ReductionDsl.isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (ReductionDsl.isGameQuery (G := CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m :=
        fun u => by simpa [ReductionDsl.isGameQuery] using hq.2 u
      have hStepL := rdecDF_implECDFShiftedPaper_eval b1 hDefaultE hsE (FSMultiHBounded L)
        (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
        (hooksFSMultiL cka prng fs L Δcka mo gMain la) hHk L l Δ qep fs.maxSkip tStar
        (modeCfgEC OO mo') mo'.cfg (modeCfgEC_agrees mo') heqT heqM heqE mo'.policy .v0 .v1
        (.cons (esEnc vpE hsE es)
          (.cons ((CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
        es t hInv.toFSMultiHBounded hInv.sm.toBoundedEngine (fun _ _ _ _ => trivial) rfl rfl
      rw [implEDFShiftedPaper_hooksFSMultiL_eq b1 cka prng fs L l Δ qep fs.maxSkip tStar mo'.cfg
        mo'.policy Δcka mo gMain la es t hInv.vR_none_of_le_L] at hStepL
      have hStep : ((handlerImpl (C := prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFShiftedPaperGen b1 (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
              L l Δ qep fs.maxSkip tStar (modeCfgEC OO mo') mo'.policy .v0 .v1)) (.inr t)).run
            (esEnc (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I)
              (KR := KR) (K := K) (M := M) (E := E)) hsE es) =
          Prod.map id (esEnc (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins)
              (I := I) (KR := KR) (K := K) (M := M) (E := E)) hsE) <$>
            (implEDFShiftedPaperGen b1 l (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep
              fs.maxSkip tStar mo'.cfg mo'.policy (.inr t)).run es := by
        rw [hVp]; dsimp only [vpE] at hStepL ⊢
        simp only [handlerImpl, StateT.run_mk, prngSMCodecDF, ← hStepL,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · exact (ih u (hqm u) es₁
          (implEDFShiftedPaper_fsMulti_inv b1 cka prng fs l mo'.cfg mo'.policy Δcka mo gMain la
            es t hInv (u, es₁) hmem)).1
      · intro res hmem; rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hInv₁ := implEDFShiftedPaper_fsMulti_inv b1 cka prng fs l mo'.cfg mo'.policy Δcka mo
          gMain la es t hInv (u, es₁) hmem₁
        have hb₁ := implEDFShiftedPaper_b_eq b1 (hooksFSMulti cka prng fs Δcka mo gMain la) l
          mo'.cfg mo'.policy es t (u, es₁) hmem₁
        obtain ⟨hInv₂, hb₂⟩ := (ih u (hqm u) es₁ hInv₁).2 res hmem₂
        exact ⟨hInv₂, hb₂.trans hb₁⟩
end ClampEvalHelpers

end HooksFSMultiCDFShiftedPaper

end Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2Aux

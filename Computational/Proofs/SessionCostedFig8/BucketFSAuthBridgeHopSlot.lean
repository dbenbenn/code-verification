/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import Computational.Proofs.ReductionDsl.SM.Engine

/-!
# Slot-Parameterized Local `(tL, par)`-Bucket Game (`localAuthBucketMainSlot`)

Section 1 of the simulation bridge for `BucketFSAuthBridgeHop` (`N09b`):
1. Defines `localAuthBucketMainSlot`, which routes fresh active `(tL, par)`-bucket session keys
   `sIdxMain q tL t0 < M_sess` through `multiSessSpec (keySlotSpec K)`.
2. Proves `localAuthBucketMainSlot_offRange` (`sessOffRange M_sess` query count `0`),
   `localAuthBucketMainSlot_lazy_eq`, and `localAuthBucketMainPar_eq_eager_ks` (rewriting to eager
   pre-sampled `ks ← sampleVec ($ᵗ K) k0 M_sess` under `keySlotFixedImpl ks`).
3. Proves `localMainSlot_halted_eq` and `localMainSlot_postLeak_eq`, showing that once halted
   (`abort || win`) or `postLeak tL es.g = true`, `localAuthBucketMainSlot` under
   `keySlotFixedImpl ks` coincides identically with `localAuthBucketMainPar`.-/

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot

public section

open scoped ENNReal
open OracleSpec OracleComp
open _root_.CryptoGames (PRFPRNG CKAScheme FSAEADScheme Party)
open _root_.CryptoGames.SM (GameState Record RecvResult ltOpt lastLeakGuessAdmissible
  authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (Header PartyState mkParties realParty
  SchemeAdversary healEpoch sampleT)
open _root_.CryptoGames.SM.Engine (Hooks HM EState VP Ctx
  liftH run_liftH_bind abortE commitE
  vSend vSendStep1 vSend_eq_bind vRecv vRecvStep1 vRecv_eq_bind deliverE injectE)
open _root_.CryptoGames.SM.Construction.AuthL11 (lImpl nilSpec)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift sessLiftCore
  sessLift_inl sessLift_inr lazyInit sessOffRange multiSessSpec)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak bucketAuthCfg
  LocalBucketAuthState LocalBucketAuthEState lookupLocalBucketAuthF rootLocalBucketAuth
  hooksLocalBucketAuth hooksLocalBucketAuthMain initLocalBucketAuth implLocalBucketAuthGen
  localAuthBucketMainPar)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (validGuessBucketParAuth)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (sIdxMain
  sampleVec keySlotSpec keySlotImpl keySlot_lazy_eq_eager)

/-! ### 1. Definitions (`localAuthBucketMainSlot` & `keySlotFixedImpl`) -/

structure LocalMainSlotState (T Sig K I : Type) where
  loc : LocalBucketAuthState T Sig K I := {}
  usedSlot : ℕ → Bool := fun _ => false

abbrev SlotHM (T Sig K I : Type) (α : Type) :=
  StateT (LocalMainSlotState T Sig K I) (OracleComp (unifSpec + multiSessSpec (keySlotSpec K))) α

@[expose] def sampleOrSlot {T Sig K I : Type} [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ) : SlotHM T Sig K I K := do
  let st ← get
  if useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx then
    modify fun s => { s with usedSlot := Function.update s.usedSlot sIdx true }
    StateT.lift (query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩))
  else
    StateT.lift (sampleT K)

private theorem sampleOrSlot_pos_run {T Sig K I : Type} [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ) (st : LocalMainSlotState T Sig K I)
    (hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true) :
    (sampleOrSlot M_sess useSlot sIdx).run st =
      ((query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩)) >>=
        fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
          Pure.pure ((k : K), { st with usedSlot := Function.update st.usedSlot sIdx true })) := by
  simp only [sampleOrSlot, hc, ↓reduceIte, StateT.run_bind, StateT.run_get,
    StateT.run_modify, pure_bind]
  rfl

@[expose] def lookupLocalMainSlotF {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx t0 : ℕ) (ik : I) : SlotHM T Sig K I K := do
  let tb0 := (← get).loc.fTable t0
  match tb0.lookup ik with
  | some k => return k
  | none =>
    let k ← sampleOrSlot M_sess useSlot sIdx
    modify fun s =>
      { s with loc := { s.loc with fTable := Function.update s.loc.fTable t0 ((ik, k) :: tb0) } }
    return k

@[expose] def rootLocalMainSlot {KR T Sig K I : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δcka q qep M_sess : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig) :
    SlotHM T Sig K I (Sig × K) := do
  let tH := healEpoch tL
  let pIk := prng.up σ0 ik0
  let useSlot := validGuessBucketParAuth Δcka tL par t0
  let sIdx := sIdxMain q tL t0
  if pl || qep + 1 < t0 then
    return (pIk.1, pIk.2)
  else if tL.isSome && t0 = tH then
    let ir ← StateT.lift (sampleT I)
    let kSample ← sampleOrSlot M_sess useSlot sIdx
    return ((prng.up σ0 ir).1, kSample)
  else if !(t0 < tH) then
    let kLookup ← lookupLocalMainSlotF M_sess useSlot sIdx t0 ik0
    return (pIk.1, kLookup)
  else
    return (pIk.1, pIk.2)

@[expose] def hooksLocalMainSlot {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) :
    Hooks (multiSessSpec (keySlotSpec K)) (LocalMainSlotState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS where
  startSend ctx _ t0 γ0 σ0 r0 := do
    let pl := postLeak tL ctx
    let coins ← match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ0 coins
    let (σ', kVal) ← rootLocalMainSlot prng Δcka q qep M_sess tL par t0 pl c.2.2 σ0
    modify fun s =>
      { s with loc := { s.loc with cache := Function.update s.loc.cache t0 (some (c.2.1, σ', kVal)) } }
    return some (c.1, c.2.1, σ', fs.initSender kVal)
  startRecv _ _ t0 γ0 _ tn0 := do
    let tH := healEpoch tL
    let honest := match (← get).loc.cache t0 with
      | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
      | none => none
    match honest with
    | some (σc, kVal) =>
      return some (some ((cka.receive γ0 tn0).1, σc, fs.initReceiver kVal))
    | none =>
      if !(qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
          (tL.isSome && decide (t0 = tH)) then
        return none
      else
        return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := pure (some (realParty vp vp.γ vp.root vp.vS vp.vR))

@[expose] def initLocalMainSlot {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) :
    SlotHM T Sig K I (Option (VP Γ T Sig SS RS × VP Γ T Sig SS RS)) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ0, k0) ← rootLocalMainSlot prng Δcka q qep M_sess tL par 0 false lam (prng.init kr)
  return some (mkParties (cka.initA kc) (cka.initB kc) σ0
    (fs.initSender k0) (fs.initReceiver k0))

abbrev LocalMainSlotEState (Γ T Sig SS RS M E K I : Type) :=
  EState (VP Γ T Sig SS RS) M (Header T × E) (LocalMainSlotState T Sig K I) × Option ℕ

@[expose] def implLocalMainSlot {Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (multiSessSpec (keySlotSpec K)) (LocalMainSlotState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) :
    QueryImpl (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (LocalMainSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
  let cfg := bucketAuthCfg (M := M) Δcka tL
  let i₀ : QueryImpl unifSpec
      (StateT (LocalMainSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun n => StateT.lift (query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl n))
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (LocalMainSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun ⟨P, m, r⟩ => do
      let (es0, winEp0) ← get
      if es0.abort || es0.g.win then return none
      match es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => return none
      | some s₁ =>
        let (res, h') ← StateT.lift ((vSend hk s₁ P (s₁.st P) m none r).run es0.h)
        match res with
        | none =>
          set ({ es0 with h := h', abort := true }, winEp0)
          return none
        | some (st', ct) =>
          let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
          set ({ es0 with g := s₁.record (2 + Δcka) P st' recE false, h := h' }, winEp0)
          return some ct
  let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (LocalMainSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun _ => pure none
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (LocalMainSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun x => do
      let (es0, winEp0) ← get
      let (out, es') ← StateT.lift ((deliverE hk maxSkip cfg x).run es0)
      set (es', winEp0)
      return out
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (LocalMainSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun x => do
      let (es0, winEp0) ← get
      let wasWin := es0.g.win
      let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg x).run es0)
      let winEp' := if !wasWin && es'.g.win then some x.2.1.1 else winEp0
      set (es', winEp')
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (StateT (LocalMainSlotEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + multiSessSpec (keySlotSpec K)))) :=
    fun P => do
      let (es0, winEp0) ← get
      if es0.abort || es0.g.win || !(es0.g.corrAllowed P) then return none
      let s₁ := es0.g.afterCorr P
      let (res, h') ← StateT.lift ((hk.reveal es0.g P (es0.g.st P)).run es0.h)
      match res with
      | none =>
        set ({ es0 with h := h', abort := true }, winEp0)
        return none
      | some stOut =>
        set ({ es0 with g := s₁, h := h' }, winEp0)
        return some stOut
  HAdd.hAdd i₀ (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

@[expose] def localAuthBucketMainSlot {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) Bool := do
  let (vs, h) ← (initLocalMainSlot cka prng fs lam Δcka q qep M_sess tL par).run {}
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig SS RS M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let (_, es, winEp) ←
      (simulateQ (implLocalMainSlot (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par)
        Δcka qep fs.maxSkip tL) A).run ({ g, h }, none)
    return match winEp with
      | none => false
      | some tWin => !es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g &&
          (decide (Party.senderOf tWin == Party.A) == par)

@[expose] def keySlotFixedImpl {K : Type} (ks : ℕ → K) :
    QueryImpl (unifSpec + multiSessSpec (keySlotSpec K)) ProbComp :=
  let i₀ : QueryImpl unifSpec ProbComp := QueryImpl.ofLift unifSpec ProbComp
  let i₁ : QueryImpl (multiSessSpec (keySlotSpec K)) ProbComp := fun ⟨sIdx, _⟩ => pure (ks sIdx)
  i₀ + i₁

theorem simulateQ_sessLift_keySlotImpl_run {K α : Type} (ks : ℕ → K)
    (m : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) :
    (simulateQ (sessLift (keySlotImpl K)) m).run ks =
      (fun a => (a, ks)) <$> simulateQ (keySlotFixedImpl ks) m := by
  induction m using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    rw [StateT.run_bind, map_bind]
    rcases t with n | ⟨sIdx, u⟩
    · simp only [sessLift_inl, keySlotFixedImpl, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun x => ih x
    · cases u
      have hstep : (sessLift (keySlotImpl K) (.inr ⟨sIdx, ()⟩)).run ks =
          Pure.pure (ks sIdx, ks) := by
        simp only [sessLift_inr, sessLiftCore, keySlotImpl]
        change (fun r : K × K => (r.1, Function.update ks sIdx r.2)) <$>
          (Pure.pure (ks sIdx, ks sIdx) : ProbComp (K × K)) = _
        simp
      simp only [monadLift_self, hstep, keySlotFixedImpl, QueryImpl.add_apply_inr]
      exact ih (ks sIdx)

theorem simulateQ_sessLift_keySlotImpl_fst {K α : Type} (ks : ℕ → K)
    (m : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) :
    Prod.fst <$> (simulateQ (sessLift (keySlotImpl K)) m).run ks =
      simulateQ (keySlotFixedImpl ks) m := by
  rw [simulateQ_sessLift_keySlotImpl_run, Functor.map_map]; simp

/-! ### 2. Pure Step Reductions for `vRecv`, `deliverE`, and `injectE` -/

theorem vRecv_localMain_pure {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (vp : VP Γ T Sig SS RS)
    (c : Header T × E) (recOpt : Option (Record M (Header T × E)))
    (st : LocalMainSlotState T Sig K I) :
    ∃ vout,
      (vRecv (hooksLocalBucketAuthMain cka prng fs Δcka qep tL) ctx P vp c recOpt).run st.loc =
        pure (vout, st.loc) ∧
      (vRecv (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par) ctx P vp c recOpt).run st =
        pure (vout, st) := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases hbad : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp [hbad]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hs1 : ∃ s1?,
        (vRecvStep1 (hooksLocalBucketAuthMain cka prng fs Δcka qep tL) ctx P vp c).run st.loc =
          pure (s1?, st.loc) ∧
        (vRecvStep1 (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par) ctx P vp c).run st =
          pure (s1?, st) := by
      unfold vRecvStep1
      by_cases hnew : c.1.1 = vp.tcur + 1
      · simp only [hnew, ↓reduceIte]
        cases c.1.2 with
        | none => exact ⟨some none, rfl, rfl⟩
        | some Tn =>
          dsimp only [hooksLocalBucketAuthMain, hooksLocalBucketAuth, hooksLocalMainSlot]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          cases hc : st.loc.cache (vp.tcur + 1) with
          | none =>
            dsimp only
            split <;> simp
          | some trip =>
            rcases trip with ⟨tCached, σc, kVal⟩
            by_cases htc : tCached = Tn
            · simp [htc]
            · simp only [htc, ↓reduceIte]
              split <;> simp
      · simp [hnew]
    rcases hs1 with ⟨s1?, hs1L, hs1R⟩
    rw [hs1L, hs1R]
    simp only [pure_bind]
    rcases s1? with _ | (_ | s1)
    · exact ⟨none, rfl, rfl⟩
    · exact ⟨some none, rfl, rfl⟩
    · dsimp only
      cases hv : s1.vR c.1.1 with
      | none => simp
      | some v =>
        dsimp only [hooksLocalBucketAuthMain, hooksLocalBucketAuth, hooksLocalMainSlot]
        cases hrec : fs.receive v c.1 c.2 with
        | none => simp
        | some res => rcases res with ⟨v', i, m⟩; simp

theorem deliverE_localMain_pure {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (x : Party × (Header T × E))
    (esSlot : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalMainSlotState T Sig K I)) :
    ∃ out g' abort',
      g'.tL = esSlot.g.tL ∧
      (deliverE (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
        fs.maxSkip (bucketAuthCfg (M := M) Δcka tL) x).run
        { g := esSlot.g, h := esSlot.h.loc, abort := esSlot.abort } =
        pure (out, { g := g', h := esSlot.h.loc, abort := abort' }) ∧
      (deliverE (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par)
        fs.maxSkip (bucketAuthCfg (M := M) Δcka tL) x).run esSlot =
        pure (out, { g := g', h := esSlot.h, abort := abort' }) := by
  rcases x with ⟨P, c⟩
  dsimp only [deliverE]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hhalt : (esSlot.abort || esSlot.g.win) = true
  · simp [hhalt]
  · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
    cases esSlot.g.inTransit P.other c with
    | none => exact ⟨none, esSlot.g, esSlot.abort, rfl, rfl, rfl⟩
    | some r =>
      rcases vRecv_localMain_pure cka prng fs Δcka q qep M_sess tL par esSlot.g P
        (esSlot.g.st P) c (some r) esSlot.h with ⟨vout, hvL, hvR⟩
      simp only [run_liftH_bind, hvL, hvR, pure_bind]
      rcases vout with _ | (_ | ⟨st', t', i', m'⟩)
      · simp [abortE]
      · dsimp only; split <;> simp
      · simp [commitE, hooksLocalBucketAuthMain, hooksLocalBucketAuth,
          hooksLocalMainSlot]
        split <;> rfl

theorem injectE_localMain_pure {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (x : Party × (Header T × E))
    (esSlot : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalMainSlotState T Sig K I)) :
    ∃ out g' abort',
      g'.tL = esSlot.g.tL ∧
      (injectE (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
        (2 + Δcka) qep (bucketAuthCfg (M := M) Δcka tL) x).run
        { g := esSlot.g, h := esSlot.h.loc, abort := esSlot.abort } =
        pure (out, { g := g', h := esSlot.h.loc, abort := abort' }) ∧
      (injectE (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par)
        (2 + Δcka) qep (bucketAuthCfg (M := M) Δcka tL) x).run esSlot =
        pure (out, { g := g', h := esSlot.h, abort := abort' }) := by
  rcases x with ⟨P, c⟩
  dsimp only [injectE]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hskip : (esSlot.abort || esSlot.g.win || (esSlot.g.inTransit P.other c).isSome ||
      !(esSlot.g.safeInj (2 + Δcka))) = true
  · simp [hskip]
  · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
    rcases vRecv_localMain_pure cka prng fs Δcka q qep M_sess tL par esSlot.g P
      (esSlot.g.st P) c none esSlot.h with ⟨rv, hvL, hvR⟩
    simp only [run_liftH_bind, hvL, hvR, pure_bind]
    rcases rv with _ | (_ | ⟨st', t', i', m'⟩)
    · simp [abortE]
    · exact ⟨some .rejected, esSlot.g, esSlot.abort, rfl, rfl, rfl⟩
    · by_cases hq : qep + 1 < t'
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        by_cases htriv : esSlot.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
        · simp [htriv, commitE, hooksLocalBucketAuthMain, hooksLocalBucketAuth,
            hooksLocalMainSlot]
          rfl
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          split <;> simp

/-! ### 3. Off-Range `0`-Query Bound (`localAuthBucketMainSlot_offRange`) -/

private inductive ZeroOff {K α : Type} (M_sess : ℕ) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α → Prop where
  | pure (a : α) : ZeroOff M_sess (Pure.pure a)
  | query_bind {t : (unifSpec + multiSessSpec (keySlotSpec K)).Domain}
      {k : (unifSpec + multiSessSpec (keySlotSpec K)).Range t →
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α}
      (ht : sessOffRange M_sess t = false)
      (hk : ∀ y, ZeroOff M_sess (k y)) :
      ZeroOff M_sess (liftM (OracleSpec.query t) >>= k)

private theorem ZeroOff.bind {K α β : Type} {M_sess : ℕ}
    {mx : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α}
    {f : α → OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) β}
    (h : ZeroOff M_sess mx) (hf : ∀ a, ZeroOff M_sess (f a)) :
    ZeroOff M_sess (mx >>= f) := by
  induction h with
  | pure a => rw [pure_bind]; exact hf a
  | query_bind ht _ ih => rw [bind_assoc]; exact ZeroOff.query_bind ht ih

private theorem ZeroOff.query_false {K : Type} {M_sess : ℕ}
    (t : (unifSpec + multiSessSpec (keySlotSpec K)).Domain)
    (ht : sessOffRange M_sess t = false) :
    ZeroOff M_sess
      (liftM (OracleSpec.query t) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) := by
  rw [← bind_pure (liftM (OracleSpec.query t) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _)]
  exact ZeroOff.query_bind ht fun y => ZeroOff.pure y

private theorem ZeroOff.to_isQueryBoundP {K α : Type} {M_sess : ℕ}
    {oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α}
    (h : ZeroOff M_sess oa) :
    oa.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0 := by
  induction h with
  | pure _ => exact isQueryBoundP_pure _ _ 0
  | query_bind ht _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [ht]), fun y => by simpa [ht] using ih y⟩

private theorem ZeroOff.sampleT_run {K HS α : Type} (M_sess : ℕ) [SampleableType α] (h : HS) :
    ZeroOff M_sess ((StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run h) := by
  rw [StateT.run_lift]
  suffices hs : ∀ oa : ProbComp α,
      ZeroOff M_sess (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) by
    exact (hs ($ᵗ α : ProbComp α)).bind fun a => ZeroOff.pure (a, h)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => exact ZeroOff.pure a
  | query_bind t k ih =>
    exact (ZeroOff.query_false (.inl t) rfl).bind ih

private theorem ZeroOff.sampleOrSlot_run {T Sig K I : Type} [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ) (st : LocalMainSlotState T Sig K I) :
    ZeroOff M_sess ((sampleOrSlot M_sess useSlot sIdx).run st) := by
  by_cases hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true
  · rw [sampleOrSlot_pos_run M_sess useSlot sIdx st hc]
    have hoff :
        sessOffRange M_sess
          (.inr ⟨sIdx, ()⟩ : (unifSpec + multiSessSpec (keySlotSpec K)).Domain) = false := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp [sessOffRange, Nat.not_le.mpr hc.1.2]
    exact (ZeroOff.query_false _ hoff).bind fun _ => ZeroOff.pure _
  · dsimp only [sampleOrSlot]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact ZeroOff.sampleT_run M_sess st

private theorem ZeroOff.root_run {KR T Sig K I : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δcka q qep M_sess : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig)
    (st : LocalMainSlotState T Sig K I) :
    ZeroOff M_sess ((rootLocalMainSlot prng Δcka q qep M_sess tL par t0 pl ik0 σ0).run st) := by
  dsimp only [rootLocalMainSlot]
  split
  · exact ZeroOff.pure _
  · split
    · rw [StateT.run_bind]
      refine (ZeroOff.sampleT_run M_sess st).bind fun p1 => ?_
      rw [StateT.run_bind]
      exact (ZeroOff.sampleOrSlot_run M_sess _ _ p1.2).bind fun _ => ZeroOff.pure _
    · split
      · rw [StateT.run_bind]
        refine ZeroOff.bind ?_ (fun _ => ZeroOff.pure _)
        dsimp only [lookupLocalMainSlotF]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOff.pure _
        · rw [StateT.run_bind]
          refine (ZeroOff.sampleOrSlot_run M_sess _ _ st).bind fun p1 => ?_
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroOff.pure _
      · exact ZeroOff.pure _

private theorem ZeroOff.vSend_run {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool) [Inhabited E]
    (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (vp : VP Γ T Sig SS RS)
    (m : M) (pair : Option (M × M)) (r0 : Option CCoins)
    (st : LocalMainSlotState T Sig K I) :
    ZeroOff M_sess ((vSend (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par)
      ctx P vp m pair r0).run st) := by
  rw [vSend_eq_bind, StateT.run_bind]
  have hs1 : ZeroOff M_sess
      ((vSendStep1 (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par) ctx P vp r0).run st) := by
    unfold vSendStep1
    split
    · rw [StateT.run_bind]
      have hss : ZeroOff M_sess
          (((hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par).startSend
            ctx P (vp.tcur + 1) vp.γ vp.root r0).run st) := by
        dsimp only [hooksLocalMainSlot]
        cases r0 with
        | none =>
          rw [StateT.run_bind]
          refine (ZeroOff.sampleT_run M_sess st).bind fun p1 => ?_
          rw [StateT.run_bind]
          refine (ZeroOff.root_run prng Δcka q qep M_sess tL par _ _ _ _ p1.2).bind fun p2 => ?_
          rcases p2 with ⟨⟨_, _⟩, _⟩
          simp
          exact ZeroOff.pure _
        | some c =>
          rw [StateT.run_bind]
          simp only [StateT.run_pure, pure_bind]
          rw [StateT.run_bind]
          refine (ZeroOff.root_run prng Δcka q qep M_sess tL par _ _ _ _ st).bind fun p2 => ?_
          rcases p2 with ⟨⟨_, _⟩, _⟩
          simp
          exact ZeroOff.pure _
      refine hss.bind fun p => ?_
      rcases p.1 with _ | ⟨_, _, _, _⟩ <;> exact ZeroOff.pure _
    · exact ZeroOff.pure _
  refine hs1.bind fun p => ?_
  cases p.1 with
  | none => exact ZeroOff.pure _
  | some s1 =>
    dsimp only
    cases hv : s1.vS with
    | none => simp only [StateT.run_pure]; exact ZeroOff.pure _
    | some v =>
      dsimp only [hooksLocalMainSlot]
      simp only [StateT.run_pure, pure_bind]
      exact ZeroOff.pure _

theorem localAuthBucketMainSlot_offRange {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    (localAuthBucketMainSlot cka prng fs lam Δcka q qep M_sess tL par A).IsQueryBoundP
      (fun t => sessOffRange M_sess t = true) 0 := by
  apply ZeroOff.to_isQueryBoundP
  dsimp only [localAuthBucketMainSlot]
  have hinit : ZeroOff M_sess
      ((initLocalMainSlot cka prng fs lam Δcka q qep M_sess tL par).run {}) := by
    dsimp only [initLocalMainSlot]
    rw [StateT.run_bind]
    refine (ZeroOff.sampleT_run (K := K) (α := KR) M_sess ({} : LocalMainSlotState T Sig K I)).bind fun p1 => ?_
    rw [StateT.run_bind]
    refine (ZeroOff.sampleT_run (K := K) (α := KC) M_sess p1.2).bind fun p2 => ?_
    rw [StateT.run_bind]
    refine (ZeroOff.root_run prng Δcka q qep M_sess tL par 0 false lam (prng.init p1.1) p2.2).bind
      fun p3 => ?_
    rcases p3 with ⟨⟨_, _⟩, _⟩
    exact ZeroOff.pure _
  let hk := hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par
  have hsim : ∀ (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
      (s : LocalMainSlotEState Γ T Sig SS RS M E K I),
      ZeroOff M_sess ((simulateQ (implLocalMainSlot hk Δcka qep fs.maxSkip tL) oa).run s) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro s; exact ZeroOff.pure (a, s)
    | query_bind t k ih =>
      intro ⟨es0, we0⟩
      rw [simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind]
      refine ZeroOff.bind ?_ (fun p => ih p.1 p.2)
      rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | x) | x) | P)
      · dsimp only [implLocalMainSlot, QueryImpl.add_apply_inl]
        rw [StateT.run_lift]
        exact (ZeroOff.query_false (.inl n) rfl).bind fun _ => ZeroOff.pure _
      · dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOff.pure _
        · split
          · exact ZeroOff.pure _
          · rw [StateT.run_bind, StateT.run_lift]
            refine ((ZeroOff.vSend_run cka prng fs Δcka q qep M_sess tL par _ P _ m none r es0.h).bind
              fun _ => ZeroOff.pure _).bind fun p => ?_
            rcases p with ⟨⟨res, _⟩, _⟩
            cases res <;> simp <;> exact ZeroOff.pure _
      · dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        exact ZeroOff.pure _
      · dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rcases deliverE_localMain_pure cka prng fs Δcka q qep M_sess tL par x es0 with ⟨_, _, _, _, _, hR⟩
        simp [hk, hR]
        exact ZeroOff.pure _
      · dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rcases injectE_localMain_pure cka prng fs Δcka q qep M_sess tL par x es0 with ⟨_, _, _, _, _, hR⟩
        simp [hk, hR]
        exact ZeroOff.pure _
      · dsimp only [implLocalMainSlot, QueryImpl.add_apply_inr]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOff.pure _
        · dsimp only [hk, hooksLocalMainSlot]
          simp
          exact ZeroOff.pure _
  refine hinit.bind fun ⟨vs, _⟩ => ?_
  cases vs with
  | none => exact ZeroOff.pure _
  | some pair =>
    rcases pair with ⟨_, _⟩
    exact (hsim A _).bind fun _ => ZeroOff.pure _

/-! ### 4. Lazy-to-Eager Key-Slot Equivalence (`localAuthBucketMainPar_eq_eager_ks`) -/

private def EqDistRel {α β : Type} (R : α → β → Prop)
    (mL : ProbComp α) (mR : ProbComp β) : Prop :=
  ∀ (fL : α → ProbComp Bool) (fR : β → ProbComp Bool),
    (∀ a b, R a b → 𝒟[fL a] = 𝒟[fR b]) →
    𝒟[mL >>= fL] = 𝒟[mR >>= fR]

private theorem EqDistRel.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    EqDistRel R (Pure.pure a) (Pure.pure b) := by
  intro fL fR hf; simp only [pure_bind]; exact hf a b h

private theorem EqDistRel.bind {α₁ β₁ α₂ β₂ : Type}
    {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {mL : ProbComp α₁} {mR : ProbComp β₁}
    {kL : α₁ → ProbComp α₂} {kR : β₁ → ProbComp β₂}
    (hm : EqDistRel R₁ mL mR)
    (hk : ∀ a b, R₁ a b → EqDistRel R₂ (kL a) (kR b)) :
    EqDistRel R₂ (mL >>= kL) (mR >>= kR) := by
  intro fL fR hf; simp only [bind_assoc]
  exact hm (fun a => kL a >>= fL) (fun b => kR b >>= fR) fun a b hab => hk a b hab fL fR hf

private theorem EqDistRel.same {ξ α β : Type} {R : α → β → Prop}
    (c : ProbComp ξ) (gL : ξ → α) (gR : ξ → β) (hg : ∀ x, R (gL x) (gR x)) :
    EqDistRel R (c >>= fun x => Pure.pure (gL x)) (c >>= fun x => Pure.pure (gR x)) := by
  intro fL fR hf; simp only [bind_assoc, pure_bind]
  exact evalDist_bind_congr _ _ _ fun x => hf _ _ (hg x)

private def LazySlotSync {T Sig K I : Type}
    (tbl : ℕ → Option K) (st : LocalMainSlotState T Sig K I)
    (hLoc : LocalBucketAuthState T Sig K I) : Prop :=
  st.loc = hLoc ∧ ∀ i, st.usedSlot i = false → tbl i = none

private abbrev lazySlotImpl (K : Type) [SampleableType K] :=
  sessLift (lazyInit ($ᵗ K : ProbComp K) (keySlotImpl K))

theorem sim_sampleT_lImpl {α : Type} [SampleableType α] :
    simulateQ lImpl (sampleT (tspec := nilSpec) α) = ($ᵗ α : ProbComp α) := by
  suffices h : ∀ oa : ProbComp α, simulateQ lImpl (liftM oa : OracleComp (unifSpec + nilSpec) α) = oa from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ lImpl
      ((liftM (OracleSpec.query (spec := unifSpec + nilSpec) (.inl t)) :
        OracleComp (unifSpec + nilSpec) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + nilSpec) α)) = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      lImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    congr 1; funext u; exact ih u

theorem sim_sampleT_fixed {K α : Type} [SampleableType α] (ks : ℕ → K) :
    simulateQ (keySlotFixedImpl ks)
      (sampleT (tspec := multiSessSpec (keySlotSpec K)) α) = ($ᵗ α : ProbComp α) := by
  suffices h : ∀ oa : ProbComp α,
      simulateQ (keySlotFixedImpl ks)
        (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) = oa from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ (keySlotFixedImpl ks)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl t)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)) = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      keySlotFixedImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    congr 1; funext u; exact ih u

private theorem sim_sampleT_lazy_run {K α : Type} [SampleableType K] [SampleableType α]
    (tbl : ℕ → Option K) :
    (simulateQ (lazySlotImpl K)
      (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run tbl =
      (($ᵗ α : ProbComp α) >>= fun a => Pure.pure (a, tbl)) := by
  suffices h : ∀ oa : ProbComp α,
      (simulateQ (lazySlotImpl K)
        (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)).run tbl =
        (oa >>= fun a => Pure.pure (a, tbl)) from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change (simulateQ (lazySlotImpl K)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl t)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α))).run tbl = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, lazySlotImpl]
    simp only [sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private def HMRel {T Sig K I α : Type} :
    (α × LocalBucketAuthState T Sig K I) →
    ((α × LocalMainSlotState T Sig K I) × (ℕ → Option K)) → Prop :=
  fun ⟨aL, hLoc⟩ ⟨⟨aR, st⟩, tbl⟩ => aL = aR ∧ LazySlotSync tbl st hLoc

private theorem eqDist_sampleT_hm {T Sig K I α : Type} [SampleableType K] [SampleableType α]
    {tbl : ℕ → Option K} {st : LocalMainSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel HMRel
      (simulateQ lImpl ((StateT.lift (sampleT (tspec := nilSpec) α)).run hLoc))
      ((simulateQ (lazySlotImpl K)
        ((StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run st)).run tbl) := by
  simp only [StateT.run_lift, simulateQ_bind,
    simulateQ_pure, sim_sampleT_lImpl, StateT.run_bind, sim_sampleT_lazy_run,
    bind_assoc, pure_bind]
  exact EqDistRel.same ($ᵗ α : ProbComp α) (fun a => (a, hLoc)) (fun a => ((a, st), tbl))
    fun _ => ⟨rfl, hsync⟩

private theorem eqDist_sampleOrSlot {T Sig K I : Type} [SampleableType K]
    (M_sess : ℕ) (useSlot : Bool) (sIdx : ℕ)
    {tbl : ℕ → Option K} {st : LocalMainSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel HMRel
      (simulateQ lImpl ((StateT.lift (sampleT (tspec := nilSpec) K)).run hLoc))
      ((simulateQ (lazySlotImpl K) ((sampleOrSlot M_sess useSlot sIdx).run st)).run tbl) := by
  by_cases hc : (useSlot && decide (sIdx < M_sess) && !st.usedSlot sIdx) = true
  · have hus : st.usedSlot sIdx = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc; exact hc.2
    have htbl : tbl sIdx = none := hsync.2 sIdx hus
    rw [sampleOrSlot_pos_run M_sess useSlot sIdx st hc]
    intro fL fR hf
    have hL :
        (simulateQ lImpl ((StateT.lift (sampleT (tspec := nilSpec) K)).run hLoc) >>= fL) =
          (($ᵗ K : ProbComp K) >>= fun k => fL (k, hLoc)) := by
      simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, sim_sampleT_lImpl,
        bind_assoc, pure_bind]
    have hq :
        (lazySlotImpl K (.inr ⟨sIdx, ()⟩)).run tbl =
          (($ᵗ K : ProbComp K) >>= fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
            Pure.pure (k, Function.update tbl sIdx (some (k : K)))) := by
      simp [-bind_pure_comp, lazySlotImpl, sessLift_inr, sessLiftCore, lazyInit, keySlotImpl,
        htbl, map_eq_bind_pure_comp]
      refine bind_congr fun k => ?_
      change (Pure.pure (k, k) : ProbComp ((keySlotSpec K).Range () × K)) >>= _ = _
      rw [pure_bind]
    have hR :
        (((simulateQ (lazySlotImpl K)
            ((query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩)) >>=
              fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
                Pure.pure ((k : K), { st with usedSlot := Function.update st.usedSlot sIdx true }))).run tbl) >>= fR) =
          (($ᵗ K : ProbComp K) >>= fun k =>
            fR ((k, { st with usedSlot := Function.update st.usedSlot sIdx true }),
              Function.update tbl sIdx (some k))) := by
      erw [simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      erw [StateT.run_bind, hq]
      simp only [simulateQ_pure, StateT.run_pure]
      erw [bind_assoc, bind_assoc]
      refine bind_congr fun k => ?_
      erw [pure_bind, pure_bind]
      rfl
    erw [hL, hR]
    refine evalDist_bind_congr _ _ _ fun k =>
      hf (k, hLoc)
         ((k, { st with usedSlot := Function.update st.usedSlot sIdx true }),
           Function.update tbl sIdx (some k))
         ⟨rfl, hsync.1, ?_⟩
    intro i hi
    by_cases his : i = sIdx
    · subst his; simp at hi
    · simp only [Function.update_of_ne his] at hi ⊢; exact hsync.2 i hi
  · dsimp only [sampleOrSlot]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact eqDist_sampleT_hm hsync

private theorem eqDist_hm_bind {T Sig K I α β : Type} [SampleableType K]
    {mL : HM nilSpec (LocalBucketAuthState T Sig K I) α}
    {mR : SlotHM T Sig K I α}
    {kL : α → HM nilSpec (LocalBucketAuthState T Sig K I) β}
    {kR : α → SlotHM T Sig K I β}
    {tbl : ℕ → Option K} {st : LocalMainSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hm : EqDistRel HMRel (simulateQ lImpl (mL.run hLoc))
      ((simulateQ (lazySlotImpl K) (mR.run st)).run tbl))
    (hk : ∀ x tbl' st' hLoc', LazySlotSync tbl' st' hLoc' →
      EqDistRel HMRel (simulateQ lImpl ((kL x).run hLoc'))
        ((simulateQ (lazySlotImpl K) ((kR x).run st')).run tbl')) :
    EqDistRel HMRel (simulateQ lImpl ((mL >>= kL).run hLoc))
      ((simulateQ (lazySlotImpl K) ((mR >>= kR).run st)).run tbl) := by
  simp only [StateT.run_bind, simulateQ_bind]
  exact hm.bind fun ⟨xL, hLoc'⟩ ⟨⟨xR, st'⟩, tbl'⟩ ⟨hx, hsync'⟩ => by
    subst hx; exact hk xL tbl' st' hLoc' hsync'

private theorem eqDist_root {KR T Sig K I : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δcka q qep M_sess : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig)
    {tbl : ℕ → Option K} {st : LocalMainSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel HMRel
      (simulateQ lImpl ((rootLocalBucketAuth prng qep tL t0 pl ik0 σ0).run hLoc))
      ((simulateQ (lazySlotImpl K)
        ((rootLocalMainSlot prng Δcka q qep M_sess tL par t0 pl ik0 σ0).run st)).run tbl) := by
  dsimp only [rootLocalBucketAuth, rootLocalMainSlot]
  split
  · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
  · split
    · refine eqDist_hm_bind (eqDist_sampleT_hm hsync) fun ir tbl1 st1 hLoc1 hsync1 => ?_
      refine eqDist_hm_bind (eqDist_sampleOrSlot M_sess _ _ hsync1) fun k tbl2 st2 hLoc2 hsync2 => ?_
      simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync2⟩
    · split
      · refine eqDist_hm_bind ?_ fun k tbl1 st1 hLoc1 hsync1 => ?_
        · dsimp only [lookupLocalBucketAuthF, lookupLocalMainSlotF]
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.1]
          cases (hLoc.fTable t0).lookup ik0 with
          | some k =>
            simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
          | none =>
            refine eqDist_hm_bind (eqDist_sampleOrSlot M_sess _ _ hsync)
              fun k tbl1 st1 hLoc1 hsync1 => ?_
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
            exact EqDistRel.pure ⟨rfl, by rw [hsync1.1], hsync1.2⟩
        · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
      · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩

private theorem eqDist_vSend {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx Γ T Sig SS RS M E) (P : Party) (vp : VP Γ T Sig SS RS)
    (m : M) (pair : Option (M × M)) (r0 : Option CCoins)
    {tbl : ℕ → Option K} {st : LocalMainSlotState T Sig K I} {hLoc : LocalBucketAuthState T Sig K I}
    (hsync : LazySlotSync tbl st hLoc) :
    EqDistRel HMRel
      (simulateQ lImpl ((vSend (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
        ctx P vp m pair r0).run hLoc))
      ((simulateQ (lazySlotImpl K) ((vSend (hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par)
        ctx P vp m pair r0).run st)).run tbl) := by
  rw [vSend_eq_bind, vSend_eq_bind]
  refine eqDist_hm_bind (K := K) ?_ fun s1? tbl1 st1 hLoc1 hsync1 => ?_
  · unfold vSendStep1
    split
    · refine eqDist_hm_bind (K := K) ?_ fun res tbl1 st1 hLoc1 hsync1 => ?_
      · dsimp only [hooksLocalBucketAuthMain, hooksLocalBucketAuth, hooksLocalMainSlot]
        cases r0 with
        | none =>
          refine eqDist_hm_bind (eqDist_sampleT_hm hsync) fun coins tbl1 st1 hLoc1 hsync1 => ?_
          refine eqDist_hm_bind (eqDist_root prng Δcka q qep M_sess tL par _ _ _ _ hsync1)
            fun ⟨σ', kVal⟩ tbl2 st2 hLoc2 hsync2 => ?_
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
          exact EqDistRel.pure ⟨rfl, by rw [hsync2.1], hsync2.2⟩
        | some c =>
          simp only [pure_bind]
          refine eqDist_hm_bind (eqDist_root prng Δcka q qep M_sess tL par _ _ _ _ hsync)
            fun ⟨σ', kVal⟩ tbl2 st2 hLoc2 hsync2 => ?_
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
          exact EqDistRel.pure ⟨rfl, by rw [hsync2.1], hsync2.2⟩
      · rcases res with _ | ⟨_, _, _, _⟩ <;>
          simp only [StateT.run_pure, simulateQ_pure] <;> exact EqDistRel.pure ⟨rfl, hsync1⟩
    · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync⟩
  · cases s1? with
    | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
    | some s1 =>
      dsimp only
      cases hv : s1.vS with
      | none => simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRel.pure ⟨rfl, hsync1⟩
      | some v =>
        dsimp only [hooksLocalBucketAuthMain, hooksLocalBucketAuth, hooksLocalMainSlot]
        simp only [StateT.run_pure, pure_bind, simulateQ_pure]
        exact EqDistRel.pure ⟨rfl, hsync1⟩

theorem localAuthBucketMainSlot_lazy_eq {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthBucketMainPar cka prng fs lam Δcka qep tL par A] =
      𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit ($ᵗ K : ProbComp K) (keySlotImpl K)))
        (localAuthBucketMainSlot cka prng fs lam Δcka q qep M_sess tL par A)).run
        (fun _ => none)] := by
  have hinit : EqDistRel HMRel
      (simulateQ lImpl ((initLocalBucketAuth cka prng fs lam qep tL).run {}))
      ((simulateQ (lazySlotImpl K)
        ((initLocalMainSlot cka prng fs lam Δcka q qep M_sess tL par).run {})).run
        (fun _ => none)) := by
    dsimp only [initLocalBucketAuth, initLocalMainSlot]
    have hsync0 : LazySlotSync (K := K) (fun _ => none) ({} : LocalMainSlotState T Sig K I) {} :=
      ⟨rfl, fun _ _ => rfl⟩
    refine eqDist_hm_bind (eqDist_sampleT_hm hsync0) fun kr tbl1 st1 hLoc1 hsync1 => ?_
    refine eqDist_hm_bind (eqDist_sampleT_hm hsync1) fun kc tbl2 st2 hLoc2 hsync2 => ?_
    refine eqDist_hm_bind (eqDist_root prng Δcka q qep M_sess tL par 0 false lam (prng.init kr) hsync2)
      fun ⟨σ0, k0⟩ tbl3 st3 hLoc3 hsync3 => ?_
    simp only [StateT.run_pure, simulateQ_pure]
    exact EqDistRel.pure ⟨rfl, hsync3⟩
  let hkL := hooksLocalBucketAuthMain cka prng fs Δcka qep tL
  let hkR := hooksLocalMainSlot cka prng fs Δcka q qep M_sess tL par
  have hsim : ∀ (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
      (g : Ctx Γ T Sig SS RS M E) (abort : Bool) (winEp : Option ℕ)
      (tbl : ℕ → Option K) (st : LocalMainSlotState T Sig K I) (hLoc : LocalBucketAuthState T Sig K I),
      LazySlotSync tbl st hLoc →
      EqDistRel
        (fun (pL : Bool × LocalBucketAuthEState Γ T Sig SS RS M E K I)
             (pR : (Bool × LocalMainSlotEState Γ T Sig SS RS M E K I) × (ℕ → Option K)) =>
          pL.1 = pR.1.1 ∧ pL.2.2 = pR.1.2.2 ∧
          pL.2.1.g = pR.1.2.1.g ∧ pL.2.1.abort = pR.1.2.1.abort ∧
          LazySlotSync pR.2 pR.1.2.1.h pL.2.1.h)
        (simulateQ lImpl ((simulateQ (implLocalBucketAuthGen hkL Δcka qep fs.maxSkip tL false) oa).run
          ({ g := g, h := hLoc, abort := abort }, winEp)))
        ((simulateQ (lazySlotImpl K)
          ((simulateQ (implLocalMainSlot hkR Δcka qep fs.maxSkip tL) oa).run
            ({ g := g, h := st, abort := abort }, winEp))).run tbl) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro g abort winEp tbl st hLoc hsync
      simp only [simulateQ_pure, StateT.run_pure]
      exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
    | query_bind t k ih =>
      intro g abort winEp tbl st hLoc hsync
      rw [simulateQ_query_bind, simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind]
      refine EqDistRel.bind
        (R₁ := fun (pL : _ × LocalBucketAuthEState Γ T Sig SS RS M E K I)
                   (pR : (_ × LocalMainSlotEState Γ T Sig SS RS M E K I) × (ℕ → Option K)) =>
          pL.1 = pR.1.1 ∧ pL.2.2 = pR.1.2.2 ∧
          pL.2.1.g = pR.1.2.1.g ∧ pL.2.1.abort = pR.1.2.1.abort ∧
          LazySlotSync pR.2 pR.1.2.1.h pL.2.1.h)
        ?_ ?_
      · rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | x) | x) | P)
        · dsimp only [implLocalBucketAuthGen, implLocalMainSlot, QueryImpl.add_apply_inl]
          intro fL fR hf
          simp [-bind_pure_comp, lImpl, lazySlotImpl, sessLift_inl, map_eq_bind_pure_comp]
          exact evalDist_bind_congr _ _ _ fun u =>
            hf (u, ({ g := g, h := hLoc, abort := abort }, winEp))
               ((u, ({ g := g, h := st, abort := abort }, winEp)), tbl)
               ⟨rfl, rfl, rfl, rfl, hsync⟩
        · dsimp only [implLocalBucketAuthGen, implLocalMainSlot,
            QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hhalt : (abort || g.win) = true
          · simp only [hhalt, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
          · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
            cases g.epMgmt (2 + Δcka) qep P r.isSome with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure]
              exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
            | some s1 =>
              simp only [StateT.run_bind, StateT.run_lift,
                bind_assoc, pure_bind, simulateQ_bind]
              refine (eqDist_vSend cka prng fs Δcka q qep M_sess tL par s1 P (s1.st P) m none r hsync).bind
                fun ⟨resL, hLoc'⟩ ⟨⟨resR, st'⟩, tbl'⟩ ⟨hres, hsync'⟩ => ?_
              subst hres
              rcases resL with _ | ⟨stP', ct⟩ <;>
                simp <;>
                exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync'⟩
        · dsimp only [implLocalBucketAuthGen, implLocalMainSlot,
            QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          simp only [StateT.run_pure, simulateQ_pure]
          exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
        · dsimp only [implLocalBucketAuthGen, implLocalMainSlot,
            QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          rcases deliverE_localMain_pure cka prng fs Δcka q qep M_sess tL par x
            { g := g, h := st, abort := abort } with ⟨out, g', abort', _, hL, hR⟩
          rw [hsync.1] at hL
          simp [hkL, hkR, hL, hR]
          exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
        · dsimp only [implLocalBucketAuthGen, implLocalMainSlot,
            QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
          rcases injectE_localMain_pure cka prng fs Δcka q qep M_sess tL par x
            { g := g, h := st, abort := abort } with ⟨out, g', abort', _, hL, hR⟩
          rw [hsync.1] at hL
          simp [hkL, hkR, hL, hR]
          exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
        · dsimp only [implLocalBucketAuthGen, implLocalMainSlot, QueryImpl.add_apply_inr]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hskip : (abort || g.win || !(g.corrAllowed P)) = true
          · simp only [hskip, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
          · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
            dsimp only [hkL, hkR, hooksLocalBucketAuthMain, hooksLocalBucketAuth, hooksLocalMainSlot]
            simp
            exact EqDistRel.pure ⟨rfl, rfl, rfl, rfl, hsync⟩
      · intro ⟨uL, ⟨esL, weL⟩⟩ ⟨⟨uR, ⟨esR, weR⟩⟩, tbl'⟩ ⟨hu, hwe, hg, habort, hsync'⟩
        subst hu; subst hwe
        cases esL; cases esR; dsimp only at hg habort hsync'
        subst hg; subst habort
        exact ih uL _ _ weL tbl' _ _ hsync'
  dsimp only [localAuthBucketMainPar, localAuthBucketMainSlot]
  rw [map_eq_bind_pure_comp]
  simp only [Function.comp_def, simulateQ_bind, StateT.run_bind, bind_assoc]
  refine hinit ?_ ?_ ?_
  intro ⟨vsL, hLoc0⟩ ⟨⟨vsR, st0⟩, tbl0⟩ ⟨hvs, hsync0⟩
  subst hvs
  cases vsL with
  | none => simp
  | some pair =>
    rcases pair with ⟨vA, vB⟩
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    convert hsim A _ false none tbl0 st0 hLoc0 hsync0 _ _ ?_
    intro ⟨_, ⟨esL, weL⟩⟩ ⟨⟨_, ⟨esR, weR⟩⟩, _⟩ ⟨_, hwe, hg, habort, _⟩
    subst hwe
    dsimp only at hg habort
    cases weL <;> simp [hg, habort]

theorem localAuthBucketMainPar_eq_eager_ks {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (k0 : K)
    (Δcka q qep M_sess : ℕ) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthBucketMainPar cka prng fs lam Δcka qep tL par A] =
      𝒟[sampleVec ($ᵗ K : ProbComp K) k0 M_sess >>= fun ks =>
          simulateQ (keySlotFixedImpl ks)
            (localAuthBucketMainSlot cka prng fs lam Δcka q qep M_sess tL par A)] := by
  rw [localAuthBucketMainSlot_lazy_eq cka prng fs lam Δcka q qep M_sess tL par A,
    keySlot_lazy_eq_eager k0 M_sess
      (localAuthBucketMainSlot cka prng fs lam Δcka q qep M_sess tL par A)
      (localAuthBucketMainSlot_offRange cka prng fs lam Δcka q qep M_sess tL par A)]
  refine evalDist_bind_congr _ _ _ fun ks => ?_
  rw [simulateQ_sessLift_keySlotImpl_fst]

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSlot

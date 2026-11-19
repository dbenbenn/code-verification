/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthMultiRealBase -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthMultiRealPaperAux
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
import Computational.Proofs.ReductionDsl.SM.RedFS
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions

/-!
# Real Multi-Session Hop-3 Coupling (`localAuthDFPaper ≤ multiSessRealWinProb`)

Couples the post-PRNG local game `AuthL11.localAuthDFPaper` to the two-mode
(`la = false` + `la = true`) real multi-session `FSMultiSpec` experiments (`multiSessRealWinProb`).-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Computational.Proofs.E2E.SessionAuthMultiRealPaper

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState ReceiveResult
  withPub transmitQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt hp hInit DG transmitHWith corruptSenderH deliverH
  injectH SpecialOps)
open _root_.CryptoGames.SM (Config GameState Pos Record RecvResult
  authLosingConditionsAvoided healedBy lastLeakGuessAdmissible ltOpt maxOpt)
open _root_.CryptoGames.SM.Engine (Ctx EState HM Hooks Policy TComp VP abortE authOut challE
  coinsE commitE corrE deliverE injectE liftH transmitE vRecv vSend)
open _root_.CryptoGames.SM.Construction (FSMultiBook FSMultiSpec FSMultiState Header Mode
  PartyState healEpoch hooksFSMulti initFSMultiRaw liftFSMulti lookupMultiF mkParties realParty
  regSessMulti regSessOptMulti redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket
  rootFSMulti runFSMultiDFPaper sampleT)
open _root_.CryptoGames.SM.Construction.AuthL11 (LState eraseSt)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF MakesAtMostQueriesDF
  SchemeAdversaryDF bucketAuthCfg corrEPaper deliverForgeE engRunDFPaperBucket
  hooksLocalBucket implEDFPaper initLocalBucket specDF)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalRoundTripShort
  maxForwardJumps rustLenBound)
open _root_.CryptoVerification.LibsignalSession (signalRoundTripShort_proto)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  dummyKey lAead lAeadR lChainPRG lFS lIdeal lPubOf)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF badSendMsgDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit multiSessSpec sessLift sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (
  LeAdd LeOne leAdd_of_lhs_zero leAdd_of_le_main leAdd_of_la_one leOne_of_lhs_zero
  leAdd_bind leAdd_bind_dummy_loc leOne_bind leOne_bind_dummy_loc
  keySlotSpec pubFsMultiImpl
  pubFsMultiImpl_inl_run pubFsMultiImpl_transmit_run pubFsMultiImpl_corruptSender_run
  pubFsMultiImpl_deliver_some_run pubFsMultiImpl_inject_none_run pubFsMultiImpl_inject_some_run
  lFS_receive_eq)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt (
  SessHSt ActiveSessInv activeSessInv_init activeSessInv_to_phase2
  activeSessInv_matched_iff activeSessInv_corruptSender activeSessInv_transmit
  activeSessInv_deliver activeSessInv_inject_phase2 activeSessInv_inject_phase1)

/-! ### 1. Policy & Healing Arithmetic Lemmas -/

private theorem ltOpt_of_validGuess_le (Δcka : ℕ) (tL : Option ℕ) (t ep : ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true) (hle : t ≤ ep) :
    ltOpt tL ep = true := by
  cases tL with
  | none => rfl
  | some l =>
    unfold lastLeakGuessAdmissible healedBy at hvg
    simp only [decide_eq_true_eq] at hvg
    unfold ltOpt
    simp only [decide_eq_true_eq]
    omega

private theorem corrDoom_of_receiverOf_le {St M C : Type} (g : GameState St M C)
    (Δcka : ℕ) (tL : Option ℕ) (t : ℕ) (P : Party)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (hP : P = Party.receiverOf t) (hle : t ≤ g.epoch P) :
    (⟨true, tL, t⟩ : Mode).policy.corrDoom g P = true := by
  subst hP
  have hlt := ltOpt_of_validGuess_le Δcka tL t (g.epoch (Party.receiverOf t)) hvg hle
  simp [Mode.policy, Policy.corrDoom, hlt]

private theorem healedBy_leak_false {St M C : Type} (g : GameState St M C) (e Δ t : ℕ)
    (h : ¬ (e + Δ ≤ t)) :
    healedBy (g.leak e).tL Δ t = false := by
  cases htL : g.tL with
  | none =>
    simp only [GameState.leak, htL, maxOpt, healedBy, decide_eq_false_iff_not]
    exact h
  | some l =>
    simp only [GameState.leak, htL, maxOpt, healedBy, decide_eq_false_iff_not]
    omega

private theorem healedBy_leak_mono_false {St M C : Type} (g : GameState St M C) (e Δ t : ℕ)
    (hfalse : healedBy g.tL Δ t = false) :
    healedBy (g.leak e).tL Δ t = false := by
  cases htL : g.tL with
  | none => rw [htL] at hfalse; simp [healedBy] at hfalse
  | some l =>
    rw [htL] at hfalse
    simp only [healedBy, decide_eq_false_iff_not] at hfalse
    simp only [GameState.leak, htL, maxOpt, healedBy, decide_eq_false_iff_not]
    omega

private theorem healedBy_afterCorr_false {St M C : Type} (g : GameState St M C) (P : Party)
    (Δcka t : ℕ) (ht : t ≤ g.epoch P) :
    healedBy (g.afterCorr P).tL (2 + Δcka) t = false := by
  unfold GameState.afterCorr
  dsimp only
  apply healedBy_leak_false
  cases P <;> omega

private theorem healedBy_epMgmt_false {St M C : Type} (g s₁ : GameState St M C)
    (Δ qep : ℕ) (P : Party) (fresh : Bool) (t : ℕ)
    (hep : g.epMgmt Δ qep P fresh = some s₁)
    (hfalse : healedBy g.tL Δ t = false) :
    healedBy s₁.tL Δ t = false := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep
  all_goals subst hep; first | exact hfalse | exact healedBy_leak_mono_false g _ Δ t hfalse

private theorem healedBy_false_of_not_safeCh_le {St M C : Type} (g : GameState St M C)
    (Δ t : ℕ) (P : Party) (hle : t ≤ g.epoch P)
    (hnsafe : g.safeCh Δ P = false) :
    healedBy g.tL Δ t = false := by
  unfold GameState.safeCh at hnsafe
  cases htL : g.tL with
  | none => rw [htL] at hnsafe; simp [healedBy] at hnsafe
  | some l =>
    rw [htL] at hnsafe
    simp only [healedBy, decide_eq_false_iff_not] at hnsafe ⊢
    omega

/-! ### 2. Slot-Parameterized Local Game (`W6a` exact match) & Stateless Terminal Helpers -/

private structure LocalSlotState (T Sig K I : Type) where
  loc : LState T Sig K I := {}
  usedSlot : ℕ → Bool := fun _ => false

private abbrev SlotHM (T Sig K I : Type) :=
  HM (multiSessSpec (keySlotSpec K)) (LocalSlotState T Sig K I)

private def sampleOrSlot {T Sig K I : Type} [SampleableType K]
    (M_sess sIdx : ℕ) : SlotHM T Sig K I K := do
  let st ← get
  if decide (sIdx < M_sess) && !st.usedSlot sIdx then
    modify fun s => { s with usedSlot := Function.update s.usedSlot sIdx true }
    StateT.lift (query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩))
  else
    StateT.lift (sampleT K)

private def lookupSlotFL {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (M_sess : ℕ) (Ik : I) : SlotHM T Sig K I K := do
  let st ← get
  match st.loc.table.lookup Ik with
  | some k => return k
  | none =>
    let k ← sampleOrSlot M_sess st.loc.sessions.length
    modify fun s => { s with loc := { s.loc with table := (Ik, k) :: s.loc.table } }
    return k

private def regSessSlot {T Sig K I : Type} [DecidableEq I] (Ik : I) : SlotHM T Sig K I ℕ := do
  let st ← get
  if Ik ∈ st.loc.sessions then return st.loc.sessions.idxOf Ik
  else
    modify fun s => { s with loc := { s.loc with sessions := st.loc.sessions ++ [Ik] } }
    return st.loc.sessions.length

private def regSessOfSlot {T Sig K I : Type} [DecidableEq I]
    (sid : Option I) : SlotHM T Sig K I (Option ℕ) :=
  match sid with
  | none => pure none
  | some Ik => some <$> regSessSlot Ik

private def rootSlotL {KR T Sig K I : Type} [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (mo : Mode) (M_sess : ℕ) (ep : ℕ) (Ik : I) (σ : Sig) :
    SlotHM T Sig K I (Sig × K × Option I) := do
  if mo.tStar < ep then
    let p := prng.up σ Ik
    return (p.1, p.2, none)
  else if ep = mo.tStar then
    if mo.tL.isSome && ep = mo.tH then
      let Ir ← StateT.lift (sampleT I)
      let sIdx := (← get).loc.sessions.length
      let k ← sampleOrSlot M_sess sIdx
      return ((prng.up σ Ir).1, k, some Ir)
    else
      let k ← lookupSlotFL M_sess Ik
      return ((prng.up σ Ik).1, k, some Ik)
  else if mo.tL.isSome && ep = mo.tH then
    let Ir ← StateT.lift (sampleT I)
    let p := prng.up σ Ir
    return (p.1, p.2, none)
  else
    let p := prng.up σ Ik
    return (p.1, p.2, none)

private def hooksSlotLocal {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (M_sess : ℕ) :
    Hooks (multiSessSpec (keySlotSpec K)) (LocalSlotState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig (SS × Option ℕ) (RS × Option ℕ) where
  startSend _ _ ep γ σ r := do
    let coins ← match r with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ coins
    let (σ', k, sid) ← rootSlotL prng mo M_sess ep c.2.2 σ
    let idx? ← regSessOfSlot sid
    modify fun s => { s with loc := { s.loc with cache := Function.update s.loc.cache ep (some (c.2.1, σ', k, idx?)) } }
    return some (c.1, c.2.1, σ', (fs.initSender k, idx?))
  startRecv _ _ ep γ σ Tn := do
    let honest := match (← get).loc.cache ep with
      | some (Tc, σc, k, idx?) => if Tc = Tn then some (σc, k, idx?) else none
      | none => none
    match honest with
    | some (σc, k, idx?) =>
      return some (some ((cka.receive γ Tn).1, σc, (fs.initReceiver k, idx?)))
    | none =>
      if mo.auth && ep = mo.tStar then
        if mo.tL.isSome && mo.tStar = mo.tH then return none
        let kk := cka.receive γ Tn
        let k' ← lookupSlotFL M_sess kk.2
        let idx ← regSessSlot kk.2
        return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
      else return some none
  fsSend _ _ _ ssv h m _ := do
    let o := fs.send ssv.1 h m
    return some ((o.1, ssv.2), o.2)
  fsRecv _ _ _ rsv h e _ := do
    match fs.receive rsv.1 h e with
    | none => return some none
    | some (rs', i, m) =>
      modify fun s => { s with loc := { s.loc with lastIdx := rsv.2 } }
      return some (some ((rs', rsv.2), i, m))
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    return some (realParty vp vp.γ vp.root (vp.vS.map Prod.fst) (fun ep => (vp.vR ep).map Prod.fst))

private def initSlotLocal {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (mo : Mode) (M_sess : ℕ) :
    SlotHM T Sig K I (Option (PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) ×
      PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ, k, sid) ← rootSlotL prng mo M_sess 0 lam (prng.init kr)
  let idx? ← regSessOfSlot sid
  return some (mkParties (cka.initA kc) (cka.initB kc) σ
    (fs.initSender k, idx?) (fs.initReceiver k, idx?))

private abbrev EStateSlot (Γ T Sig SS RS M E K I : Type) :=
  EState (PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) (LocalSlotState T Sig K I)

private def localAuthDFPaperSlot {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← (initSlotLocal cka prng fs lam mo M_sess).run {}
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let (_, es) ← (simulateQ (implEDFPaper (hooksSlotLocal cka prng fs mo M_sess)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) A).run { g := g, h := h }
    return authOut (2 + Δcka) mo.policy es

private def keySlotFixedImpl {K : Type} (ks : ℕ → K) :
    QueryImpl (unifSpec + multiSessSpec (keySlotSpec K)) ProbComp :=
  let i₀ : QueryImpl unifSpec ProbComp := QueryImpl.ofLift unifSpec ProbComp
  let i₁ : QueryImpl (multiSessSpec (keySlotSpec K)) ProbComp := fun ⟨sIdx, _⟩ => pure (ks sIdx)
  i₀ + i₁

private theorem implEDFPaper_inl_run {ι : Type} {S : OracleSpec ι} {H Γ T Sig SS RS M E CCoins Γ' Sig' SS' RS' : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks S H Γ T Sig SS RS M E CCoins Γ' Sig' SS' RS')
    (Δ qep maxSkip : ℕ) (cfg : Config M) (pol : Policy) (n : ℕ)
    (es : EState (VP Γ' T Sig' SS' RS') M (Header T × E) H) :
    (implEDFPaper hk Δ qep maxSkip cfg pol (.inl n)).run es =
      (liftM (OracleSpec.query (spec := unifSpec + S) (.inl n)) >>= fun u => pure (u, es)) := by
  simp [implEDFPaper, QueryImpl.add_apply_inl, coinsE, StateT.lift, StateT.run]

private def haltAnsDF {St M CCoins C : Type} :
    (qry : (specDF St M CCoins C).Domain) → (specDF St M CCoins C).Range qry
  | .inl (.inl (.inl (.inl (.inl _)))) => none
  | .inl (.inl (.inl (.inl (.inr _)))) => none
  | .inl (.inl (.inl (.inr _))) => none
  | .inl (.inl (.inr _)) => none
  | .inl (.inr _) => none
  | .inr _ => none

private theorem implEDFPaper_inr_run_of_halt {ι : Type} {S : OracleSpec ι} {H Γ T Sig SS RS M E CCoins Γ' Sig' SS' RS' : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks S H Γ T Sig SS RS M E CCoins Γ' Sig' SS' RS')
    (Δ qep maxSkip : ℕ) (cfg : Config M) (pol : Policy)
    (qry : (specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ' T Sig' SS' RS') M (Header T × E) H)
    (hhalt : (es.abort || es.g.win) = true) :
    (implEDFPaper hk Δ qep maxSkip cfg pol (.inr qry)).run es = pure (haltAnsDF qry, es) := by
  have hhalt' := (Bool.or_eq_true _ _).mp hhalt
  rcases qry with ((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (transmitE hk Δ qep pol (P, m, rc)).run es = _; simp [transmitE, haltAnsDF, hhalt']
  · change (challE hk Δ qep cfg pol (P, m₀, m₁, rc)).run es = _; simp [challE, haltAnsDF, hhalt']
  · change (deliverE hk maxSkip cfg (P, c)).run es = _; simp [deliverE, haltAnsDF, hhalt']
  · change (injectE hk Δ qep cfg (P, c)).run es = _; simp [injectE, haltAnsDF, hhalt']
  · change (corrEPaper hk pol P).run es = _; simp [corrEPaper, haltAnsDF, hhalt']
  · change (deliverForgeE hk Δ qep cfg (P, c, c')).run es = _; simp [deliverForgeE, haltAnsDF, hhalt']

private abbrev runSlotFixed {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep M_sess : ℕ) (mo : Mode)
    (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (esL : EStateSlot Γ T Sig SS RS M E K I) (ks : ℕ → K) : ProbComp Bool :=
  simulateQ (keySlotFixedImpl ks) do
    let (_, es) ← (simulateQ (implEDFPaper (hooksSlotLocal cka prng fs mo M_sess)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL
    return authOut (2 + Δcka) mo.policy es

private abbrev runMultiPaper {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep : ℕ) (mo : Mode) (la : Bool)
    (oa : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (esM : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)
      (FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (stM : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) : ProbComp Bool :=
  Prod.fst <$> (simulateQ (pubFsMultiImpl (fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 la))) do
    let (_, es) ← (simulateQ (implEDFPaper
      (hooksFSMulti (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo false la)
      (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) oa).run esM
    return (if la then es.h.lfWin else authOut (2 + Δcka) mo.policy es)).run stM

private theorem leOne_both_halt_terminal {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess : ℕ) (mo : Mode)
    (oa : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (esL : _) (esM : _) (ks : ℕ → BitVec 256) (stM : _)
    (hhaltL : (esL.abort || esL.g.win) = true)
    (hab : esL.abort = esM.abort) (hwin : esL.g.win = esM.g.win)
    (herase : eraseSt esL.g = eraseSt esM.g) :
    LeOne
      (runSlotFixed (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep M_sess mo oa esL ks)
      (runMultiPaper C Dh encPt encT idOf Δcka qep mo false oa esM stM) := by
  have hhaltM : (esM.abort || esM.g.win) = true := by rwa [← hab, ← hwin]
  induction oa using OracleComp.inductionOn generalizing stM with
  | pure _ =>
    simp only [runSlotFixed, runMultiPaper, simulateQ_pure, StateT.run_pure, pure_bind,
      Bool.false_eq_true, ↓reduceIte, map_pure, LeOne]
    have hauth : authOut (2 + Δcka) mo.policy esL = authOut (2 + Δcka) mo.policy esM := by
      simp only [authOut, hab, hwin, _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_authOK herase]
    rw [hauth]
  | query_bind q cont ih =>
    unfold runSlotFixed runMultiPaper
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, map_bind]
    rcases q with n | qry
    · rw [implEDFPaper_inl_run, implEDFPaper_inl_run, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        keySlotFixedImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        pubFsMultiImpl_inl_run, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind]
      exact leOne_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ => ih u stM
    · rw [implEDFPaper_inr_run_of_halt _ _ _ _ _ _ qry esL hhaltL,
          implEDFPaper_inr_run_of_halt _ _ _ _ _ _ qry esM hhaltM]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact ih (haltAnsDF qry) stM

private theorem leAdd_both_halt_terminal {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {cL : ProbComp Bool}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess : ℕ) (mo : Mode)
    (oa : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (esL : _) (esM : _) (ks : ℕ → BitVec 256) (stM : _)
    (hhaltL : (esL.abort || esL.g.win) = true)
    (hab : esL.abort = esM.abort) (hwin : esL.g.win = esM.g.win)
    (herase : eraseSt esL.g = eraseSt esM.g) :
    LeAdd
      (runSlotFixed (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep M_sess mo oa esL ks)
      (runMultiPaper C Dh encPt encT idOf Δcka qep mo false oa esM stM)
      cL :=
  leAdd_of_le_main (leOne_both_halt_terminal C Dh encPt encT idOf Δcka qep M_sess mo oa
    esL esM ks stM hhaltL hab hwin herase)

private theorem evalDist_runMultiPaper_true_eq_one_of_lfWin
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep : ℕ) (mo : Mode)
    (oa : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (esR : _) (stL : _) (hab : esR.abort = true) (hlf : esR.h.lfWin = true) :
    𝒟[runMultiPaper C Dh encPt encT idOf Δcka qep mo true oa esR stL] {true} = 1 := by
  have hhalt : (esR.abort || esR.g.win) = true := by simp [hab]
  induction oa using OracleComp.inductionOn generalizing stL with
  | pure _ => simp [runMultiPaper, hlf]
  | query_bind q cont ih =>
    unfold runMultiPaper
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, map_bind]
    rcases q with n | qry
    · rw [implEDFPaper_inl_run, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        pubFsMultiImpl_inl_run, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
      trans ∫⁻ (_ : Fin (n + 1)), (1 : ℝ≥0∞) ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))]
      · exact MeasureTheory.lintegral_congr fun u => ih u stL
      · rw [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
    · rw [implEDFPaper_inr_run_of_halt _ _ _ _ _ _ qry esR hhalt]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact ih (haltAnsDF qry) stL

private theorem leOne_slot_abort_terminal {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    {cM : ProbComp Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep M_sess : ℕ) (mo : Mode)
    (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (esL : EStateSlot Γ T Sig SS RS M E K I) (ks : ℕ → K)
    (habL : esL.abort = true) :
    LeOne (runSlotFixed cka prng fs Δcka qep M_sess mo oa esL ks) cM := by
  have hhalt : (esL.abort || esL.g.win) = true := by simp [habL]
  refine leOne_of_lhs_zero ?_
  induction oa using OracleComp.inductionOn with
  | pure _ => simp [runSlotFixed, authOut, habL]
  | query_bind q cont ih =>
    unfold runSlotFixed
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind]
    rcases q with n | qry
    · rw [implEDFPaper_inl_run]
      simp only [bind_assoc, simulateQ_bind, simulateQ_query, simulateQ_pure,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, pure_bind,
        keySlotFixedImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
      exact _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun u _ => by
        simpa [runSlotFixed, keySlotFixedImpl] using ih u
    · rw [implEDFPaper_inr_run_of_halt _ _ _ _ _ _ qry esL hhalt]
      simp only [simulateQ_pure, pure_bind]
      exact ih (haltAnsDF qry)

/-! ### 3. Synchronized State Invariant `SyncPaperMulti` -/

private structure SyncPaperMulti {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esL : EStateSlot (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) Pt)
    (esM : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)
      (FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ) : Prop where
  habL : esL.abort = false
  habM : esM.abort = false
  hwinL : esL.g.win = false
  hwinM : esM.g.win = false
  hbL : esL.g.b = false
  hbM : esM.g.b = false
  herase : eraseSt esL.g = eraseSt esM.g
  htrans_ep : ∀ r ∈ esL.g.trans, r.pos.epoch = r.ct.1.1
  hlf : phase1 = true → esM.h.lfWin = false
  hhealed : phase1 = false → healedBy esL.g.tL (2 + Δcka) t = false
  hidL : ∀ P, (esL.g.st P).id = P
  hidM : ∀ P, (esM.g.st P).id = P
  htcurL : ∀ P, (esL.g.st P).tcur = esL.g.epoch P
  htcurM : ∀ P, (esM.g.st P).tcur = (esL.g.st P).tcur
  hγ : ∀ P, (esM.g.st P).γ = (esL.g.st P).γ
  hroot : ∀ P, (esM.g.st P).root = (esL.g.st P).root
  hckaMsg : ∀ P, (esM.g.st P).curCkaMsg = (esL.g.st P).curCkaMsg
  hvS : ∀ P,
    match (esL.g.st P).vS with
    | none => (esM.g.st P).vS = none
    | some (ss, none) => (esM.g.st P).vS = some (.inl ss)
    | some (_, some sIdx) =>
      (esM.g.st P).vS = some (.inr sIdx) ∧ sIdx < esM.h.sessions.length ∧
        P = Party.senderOf t ∧ t ≤ (esL.g.st P).tcur
  hvR_hi : ∀ P ep, ((esL.g.st P).tcur < ep ∨ P.sendsIn ep = true) →
    (esL.g.st P).vR ep = none ∧ (esM.g.st P).vR ep = none
  hvR_ne : ∀ P ep, ep ≠ t →
    match (esL.g.st P).vR ep with
    | none => (esM.g.st P).vR ep = none
    | some (rs, optIdx) => optIdx = none ∧ (esM.g.st P).vR ep = some (.inl rs)
  hvR_eq : ∀ P,
    match (esL.g.st P).vR t with
    | none => (esM.g.st P).vR t = none
    | some (_, optIdx) =>
      ∃ sIdx, optIdx = some sIdx ∧ (esM.g.st P).vR t = some (.inr sIdx) ∧
        sIdx < esM.h.sessions.length ∧ t ≤ (esL.g.st P).tcur ∧ P = Party.receiverOf t
  hsess : esM.h.sessions = esL.h.loc.sessions
  hnodup : esL.h.loc.sessions.Nodup
  hlen : esL.h.loc.sessions.length + rem ≤ M_sess
  hused : ∀ i, esL.h.usedSlot i = decide (i < esL.h.loc.sessions.length)
  htH_empty : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = true →
    (esL.g.st (Party.senderOf t)).tcur < t →
    esL.h.loc.sessions = []
  htblL_lk : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = false →
    ∀ Ik, esL.h.loc.table.lookup Ik =
      if Ik ∈ esL.h.loc.sessions then some (ks (esL.h.loc.sessions.idxOf Ik)) else none
  htblM_lk : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = false →
    ∀ Ik, (esM.h.table.lookup Ik).isSome = decide (Ik ∈ esM.h.sessions)
  hcache_ne : ∀ ep, ep ≠ t →
    match esL.h.loc.cache ep with
    | none => esM.h.cache ep = none
    | some (Tc, σc, k, idx?) => idx? = none ∧ esM.h.cache ep = some (Tc, σc, k, none)
  hcache_lt : (esL.g.st (Party.senderOf t)).tcur < t →
    esL.h.loc.cache t = none ∧ esM.h.cache t = none
  hcache_eq :
    match esL.h.loc.cache t with
    | none => esM.h.cache t = none
    | some (Tc, σc, k, idx?) =>
      ∃ sIdx kM, idx? = some sIdx ∧ k = ks sIdx ∧ sIdx < esM.h.sessions.length ∧
        esM.h.cache t = some (Tc, σc, kM, some sIdx)
  hbook_out : ∀ i, esM.h.sessions.length ≤ i →
    esM.h.book i = none ∧ tblM i = hInit (bs i) (.seed (ks i)) ∧
      (phase1 = true → tblL i = hInit (bs i) (.seed (ks i)))
  hbook_in : ∀ i, i < esM.h.sessions.length →
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let rs_i := match (esL.g.st (Party.receiverOf t)).vR t with
      | some (rs, some j) => if j = i then rs else fs.initReceiver (ks i)
      | _ => fs.initReceiver (ks i)
    ∃ ss_i,
      ActiveSessInv C ℓ encT idOf phase1 (ks i) ss_i rs_i
        ((esM.h.book i).getD {}) (tblM i) (tblL i) ∧
      ((esL.g.st (Party.senderOf t)).tcur < t → ss_i = fs.initSender (ks i)) ∧
      (∀ P ss, (esL.g.st P).vS = some (ss, some i) → ss_i = ss)

private theorem syncPaperMulti_to_phase2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {ℓ : ℕ}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL tblL' : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true rem esL esM tblM tblL)
    (hheal : healedBy esL.g.tL (2 + Δcka) t = false) :
    SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false rem esL esM tblM tblL' :=
  { hsync with
    hlf := fun h => Bool.noConfusion h
    hhealed := fun _ => hheal
    hbook_out := fun i hi =>
      let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
      ⟨hb, hm, fun h => Bool.noConfusion h⟩
    hbook_in := fun i hi =>
      let ⟨ss_i, hinv, hss1, hss2⟩ := hsync.hbook_in i hi
      ⟨ss_i, activeSessInv_to_phase2 C ℓ encT idOf hinv, hss1, hss2⟩ }

private theorem SyncPaperMulti.inTransit_ep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {ℓ : ℕ}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem esL esM tblM tblL)
    {P : Party} {c : Header Pt × ℕ × LibsignalCiphertextWithSalt32}
    {r : Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)}
    (h : esL.g.inTransit P c = some r) :
    r.pos.epoch = c.1.1 := by
  unfold GameState.inTransit at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  rw [← hp.2]
  exact hsync.htrans_ep r hmem

/-! ### 4. Monadic `Coupled2` and `Coupled3` Combinators -/

private theorem ell_add_16_lt_rustLenBound {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) : ℓ + 16 < rustLenBound := by
  unfold rustLenBound; omega

private inductive Coupled2 {α β : Type} (R : α → β → Prop) : ProbComp α → ProbComp β → Prop where
  | pure {a : α} {b : β} (h : R a b) : Coupled2 R (Pure.pure a) (Pure.pure b)
  | bind_same {γ : Type} (c : ProbComp γ) {f : γ → ProbComp α} {g : γ → ProbComp β}
      (h : ∀ x, Coupled2 R (f x) (g x)) : Coupled2 R (c >>= f) (c >>= g)
  | bind_dummy_r {γ : Type} (c : ProbComp γ) {mL : ProbComp α} {g : γ → ProbComp β}
      (h : ∀ x, Coupled2 R mL (g x)) : Coupled2 R mL (c >>= g)
  | eq {mL mL' : ProbComp α} {mR mR' : ProbComp β}
      (hL : mL = mL') (hR : mR = mR') (h : Coupled2 R mL' mR') : Coupled2 R mL mR

private theorem Coupled2.bind {α β α' β' : Type} {R₁ : α → β → Prop} {R₂ : α' → β' → Prop}
    {mL : ProbComp α} {mR : ProbComp β} {fL : α → ProbComp α'} {fR : β → ProbComp β'}
    (hc : Coupled2 R₁ mL mR) (hk : ∀ a b, R₁ a b → Coupled2 R₂ (fL a) (fR b)) :
    Coupled2 R₂ (mL >>= fL) (mR >>= fR) := by
  induction hc with
  | pure h => simpa only [pure_bind] using hk _ _ h
  | bind_same c _ ih =>
    simpa only [bind_assoc] using Coupled2.bind_same c ih
  | bind_dummy_r c _ ih =>
    simpa only [bind_assoc] using Coupled2.bind_dummy_r c ih
  | eq hL hR _ ih =>
    exact Coupled2.eq (congrArg (· >>= fL) hL) (congrArg (· >>= fR) hR) ih

private theorem Coupled2.to_leOne {α β : Type} {R : α → β → Prop}
    {mL : ProbComp α} {mR : ProbComp β} {kL : α → ProbComp Bool} {kR : β → ProbComp Bool}
    (hc : Coupled2 R mL mR) (hk : ∀ a b, R a b → LeOne (kL a) (kR b)) :
    LeOne (mL >>= kL) (mR >>= kR) := by
  induction hc with
  | pure h => simpa only [pure_bind] using hk _ _ h
  | bind_same c _ ih =>
    simp only [bind_assoc]
    exact leOne_bind c fun x _ => ih x
  | bind_dummy_r c _ ih =>
    simp only [bind_assoc]
    exact leOne_bind_dummy_loc c fun x _ => ih x
  | eq hL hR _ ih =>
    rw [hL, hR]; exact ih

private theorem evalDist_bind_const_true_loc {α : Type} (oa : ProbComp α) (c : ProbComp Bool) :
    𝒟[oa >>= fun _ => c] {true} = 𝒟[c] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp only [pure_bind]
  | query_bind t k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
    have hcongr : (fun u => 𝒟[k u >>= fun _ => c] {true}) = fun _ => 𝒟[c] {true} := by
      funext u; exact ih u
    rw [hcongr, MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ,
      mul_one]

private theorem leAdd_swap {mL m₁ m₂ : ProbComp Bool} (h : LeAdd mL m₁ m₂) :
    LeAdd mL m₂ m₁ := by
  unfold LeAdd at h ⊢
  rwa [add_comm]

private theorem leAdd_bind_same_m1 {γ : Type} (c : ProbComp γ)
    (f g₁ : γ → ProbComp Bool) (m₂ : ProbComp Bool)
    (h : ∀ x, LeAdd (f x) (g₁ x) m₂) :
    LeAdd (c >>= f) (c >>= g₁) m₂ := by
  have hloc : LeAdd (c >>= f) (c >>= g₁) (c >>= fun _ => m₂) :=
    leAdd_bind c fun x _ => h x
  unfold LeAdd at hloc ⊢
  rwa [evalDist_bind_const_true_loc c m₂] at hloc

private theorem leAdd_bind_dummy_m2 {γ : Type} (c : ProbComp γ)
    (mL : ProbComp Bool) (m₁ : ProbComp Bool) (g₂ : γ → ProbComp Bool)
    (h : ∀ x, LeAdd mL m₁ (g₂ x)) :
    LeAdd mL m₁ (c >>= g₂) := by
  have hloc : LeAdd mL (c >>= fun _ => m₁) (c >>= g₂) :=
    leAdd_bind_dummy_loc c fun x _ => h x
  unfold LeAdd at hloc ⊢
  rwa [evalDist_bind_const_true_loc c m₁] at hloc

private theorem leAdd_bind_dummy_m1 {γ : Type} (c : ProbComp γ)
    (mL : ProbComp Bool) (g₁ : γ → ProbComp Bool) (m₂ : ProbComp Bool)
    (h : ∀ x, LeAdd mL (g₁ x) m₂) :
    LeAdd mL (c >>= g₁) m₂ :=
  leAdd_swap (leAdd_bind_dummy_m2 c mL m₂ g₁ fun x => leAdd_swap (h x))

private inductive Coupled3 {α β₁ β₂ : Type} (R : α → β₁ → β₂ → Prop) :
    ProbComp α → ProbComp β₁ → ProbComp β₂ → Prop where
  | pure {a : α} {b₁ : β₁} {b₂ : β₂} (h : R a b₁ b₂) :
      Coupled3 R (Pure.pure a) (Pure.pure b₁) (Pure.pure b₂)
  | bind_same {γ : Type} (c : ProbComp γ)
      {f : γ → ProbComp α} {g₁ : γ → ProbComp β₁} {g₂ : γ → ProbComp β₂}
      (h : ∀ x, Coupled3 R (f x) (g₁ x) (g₂ x)) :
      Coupled3 R (c >>= f) (c >>= g₁) (c >>= g₂)
  | bind_same_m1 {γ : Type} (c : ProbComp γ)
      {f : γ → ProbComp α} {g₁ : γ → ProbComp β₁} {m₂ : ProbComp β₂}
      (h : ∀ x, Coupled3 R (f x) (g₁ x) m₂) :
      Coupled3 R (c >>= f) (c >>= g₁) m₂
  | bind_dummy_loc {γ : Type} (c : ProbComp γ) {mL : ProbComp α}
      {g₁ : γ → ProbComp β₁} {g₂ : γ → ProbComp β₂}
      (h : ∀ x, Coupled3 R mL (g₁ x) (g₂ x)) :
      Coupled3 R mL (c >>= g₁) (c >>= g₂)
  | bind_dummy_m1 {γ : Type} (c : ProbComp γ) {mL : ProbComp α}
      {g₁ : γ → ProbComp β₁} {m₂ : ProbComp β₂}
      (h : ∀ x, Coupled3 R mL (g₁ x) m₂) :
      Coupled3 R mL (c >>= g₁) m₂
  | bind_dummy_m2 {γ : Type} (c : ProbComp γ) {mL : ProbComp α}
      {m₁ : ProbComp β₁} {g₂ : γ → ProbComp β₂}
      (h : ∀ x, Coupled3 R mL m₁ (g₂ x)) :
      Coupled3 R mL m₁ (c >>= g₂)
  | eq {mL mL' : ProbComp α} {m₁ m₁' : ProbComp β₁} {m₂ m₂' : ProbComp β₂}
      (hL : mL = mL') (h₁ : m₁ = m₁') (h₂ : m₂ = m₂')
      (h : Coupled3 R mL' m₁' m₂') : Coupled3 R mL m₁ m₂

private theorem Coupled3.bind {α β₁ β₂ α' β₁' β₂' : Type}
    {R₁ : α → β₁ → β₂ → Prop} {R₂ : α' → β₁' → β₂' → Prop}
    {mL : ProbComp α} {m₁ : ProbComp β₁} {m₂ : ProbComp β₂}
    {fL : α → ProbComp α'} {f₁ : β₁ → ProbComp β₁'} {f₂ : β₂ → ProbComp β₂'}
    (hc : Coupled3 R₁ mL m₁ m₂)
    (hk : ∀ a b₁ b₂, R₁ a b₁ b₂ → Coupled3 R₂ (fL a) (f₁ b₁) (f₂ b₂)) :
    Coupled3 R₂ (mL >>= fL) (m₁ >>= f₁) (m₂ >>= f₂) := by
  induction hc with
  | pure h => simpa only [pure_bind] using hk _ _ _ h
  | bind_same c _ ih =>
    simpa only [bind_assoc] using Coupled3.bind_same c ih
  | bind_same_m1 c _ ih =>
    simpa only [bind_assoc] using Coupled3.bind_same_m1 c ih
  | bind_dummy_loc c _ ih =>
    simpa only [bind_assoc] using Coupled3.bind_dummy_loc c ih
  | bind_dummy_m1 c _ ih =>
    simpa only [bind_assoc] using Coupled3.bind_dummy_m1 c ih
  | bind_dummy_m2 c _ ih =>
    simpa only [bind_assoc] using Coupled3.bind_dummy_m2 c ih
  | eq hL h₁ h₂ _ ih =>
    exact Coupled3.eq (congrArg (· >>= fL) hL) (congrArg (· >>= f₁) h₁) (congrArg (· >>= f₂) h₂) ih

private theorem Coupled3.mono {α β₁ β₂ : Type}
    {R₁ R₂ : α → β₁ → β₂ → Prop}
    {mL : ProbComp α} {m₁ : ProbComp β₁} {m₂ : ProbComp β₂}
    (hc : Coupled3 R₁ mL m₁ m₂) (himp : ∀ a b₁ b₂, R₁ a b₁ b₂ → R₂ a b₁ b₂) :
    Coupled3 R₂ mL m₁ m₂ := by
  have heq : ∀ {T : Type} (x : ProbComp T), x = (x >>= Pure.pure) := fun x => (bind_pure x).symm
  exact Coupled3.eq (heq mL) (heq m₁) (heq m₂)
    (hc.bind fun a b₁ b₂ h => Coupled3.pure (himp a b₁ b₂ h))

private theorem probComp_nonempty {γ : Type} (c : ProbComp γ) : Nonempty γ := by
  induction c using OracleComp.inductionOn with
  | pure x => exact ⟨x⟩
  | query_bind n _ ih => exact ih ⟨0, Nat.zero_lt_succ n⟩

private theorem Coupled3.to_coupled2 {α β₁ β₂ : Type} {R : α → β₁ → β₂ → Prop}
    {mL : ProbComp α} {m₁ : ProbComp β₁} {m₂ : ProbComp β₂}
    (hc : Coupled3 R mL m₁ m₂) :
    Coupled2 (fun a b₁ => ∃ b₂, R a b₁ b₂) mL m₁ := by
  induction hc with
  | pure h => exact Coupled2.pure ⟨_, h⟩
  | bind_same c _ ih => exact Coupled2.bind_same c ih
  | bind_same_m1 c _ ih => exact Coupled2.bind_same c ih
  | bind_dummy_loc c _ ih => exact Coupled2.bind_dummy_r c ih
  | bind_dummy_m1 c _ ih => exact Coupled2.bind_dummy_r c ih
  | bind_dummy_m2 c _ ih =>
    rcases probComp_nonempty c with ⟨x₀⟩
    exact ih x₀
  | eq hL h₁ _ _ ih => exact Coupled2.eq hL h₁ ih

private theorem Coupled2.to_coupled3_m2 {α β₁ β₂ : Type}
    {R : α → β₁ → Prop} {R₃ : α → β₁ → β₂ → Prop}
    {mL : ProbComp α} {m₁ : ProbComp β₁} (m₂ : ProbComp β₂)
    (hc : Coupled2 R mL m₁) (himp : ∀ a b₁ b₂, R a b₁ → R₃ a b₁ b₂) :
    Coupled3 R₃ mL m₁ m₂ := by
  induction hc with
  | pure h =>
    exact Coupled3.eq rfl rfl (bind_pure m₂).symm
      (Coupled3.bind_dummy_m2 m₂ fun b₂ => Coupled3.pure (himp _ _ b₂ h))
  | bind_same c _ ih => exact Coupled3.bind_same_m1 c ih
  | bind_dummy_r c _ ih => exact Coupled3.bind_dummy_m1 c ih
  | eq hL hR _ ih => exact Coupled3.eq hL hR rfl ih

private theorem Coupled3.to_leAdd {α β₁ β₂ : Type} {R : α → β₁ → β₂ → Prop}
    {mL : ProbComp α} {m₁ : ProbComp β₁} {m₂ : ProbComp β₂}
    {kL : α → ProbComp Bool} {k₁ : β₁ → ProbComp Bool} {k₂ : β₂ → ProbComp Bool}
    (hc : Coupled3 R mL m₁ m₂)
    (hk : ∀ a b₁ b₂, R a b₁ b₂ → LeAdd (kL a) (k₁ b₁) (k₂ b₂)) :
    LeAdd (mL >>= kL) (m₁ >>= k₁) (m₂ >>= k₂) := by
  induction hc with
  | pure h => simpa only [pure_bind] using hk _ _ _ h
  | bind_same c _ ih =>
    simp only [bind_assoc]
    exact leAdd_bind c fun x _ => ih x
  | bind_same_m1 c _ ih =>
    simp only [bind_assoc]
    exact leAdd_bind_same_m1 c _ _ _ ih
  | bind_dummy_loc c _ ih =>
    simp only [bind_assoc]
    exact leAdd_bind_dummy_loc c fun x _ => ih x
  | bind_dummy_m1 c _ ih =>
    simp only [bind_assoc]
    exact leAdd_bind_dummy_m1 c _ _ _ ih
  | bind_dummy_m2 c _ ih =>
    simp only [bind_assoc]
    exact leAdd_bind_dummy_m2 c _ _ _ ih
  | eq hL h₁ h₂ _ ih =>
    rw [hL, h₁, h₂]; exact ih

/-! ### 5. `sampleT` Reductions, `HookBookInv`, `lookup_regSess_coupled`, and `root_regSessOpt_coupled` -/

private theorem sim_sampleT_fixed {K α : Type} [SampleableType α] (ks : ℕ → K) :
    simulateQ (keySlotFixedImpl ks)
      (sampleT (tspec := multiSessSpec (keySlotSpec K)) α) = ($ᵗ α : ProbComp α) := by
  suffices h : ∀ oa : ProbComp α,
      simulateQ (keySlotFixedImpl ks)
        (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) = oa from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    change simulateQ (keySlotFixedImpl ks)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl n)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)) = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      keySlotFixedImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    congr 1; funext u; exact ih u

private theorem StateT_lift_run {m : Type → Type} [Monad m] {σ α : Type}
    (c : m α) (s : σ) : (StateT.lift c : StateT σ m α).run s = (c >>= fun a => pure (a, s)) := rfl

private theorem simulateQ_keySlotFixedImpl_query_inr {K α : Type}
    (sIdx : ℕ) (f : K → OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)
    (ks : ℕ → K) :
    simulateQ (keySlotFixedImpl ks)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) K) >>= f) =
      simulateQ (keySlotFixedImpl ks) (f (ks sIdx)) := by
  erw [simulateQ_query_bind]

private theorem simulateQ_keySlotFixedImpl_sampleT {K α β : Type} [SampleableType α]
    (f : α → OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) β) (ks : ℕ → K) :
    simulateQ (keySlotFixedImpl ks) (sampleT α >>= f) =
      (($ᵗ α : ProbComp α) >>= fun x => simulateQ (keySlotFixedImpl ks) (f x)) := by
  rw [simulateQ_bind, sim_sampleT_fixed]

private theorem simulateQ_run_liftM_unif {ι : Type} {S : OracleSpec.{0, 0} ι} {α σ : Type}
    (qimpl : QueryImpl (unifSpec + S) (StateT σ ProbComp))
    (hinl : ∀ n st, (qimpl (.inl n)).run st =
      (liftM (OracleSpec.query (spec := unifSpec) n) >>= fun u => pure (u, st)))
    (oa : ProbComp α) (st : σ) :
    (simulateQ qimpl (liftM oa : OracleComp (unifSpec + S) α)).run st =
      (oa >>= fun x => pure (x, st)) := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind n k ih =>
    change (simulateQ qimpl
      ((liftM (OracleSpec.query (spec := unifSpec + S) (.inl n)) : OracleComp (unifSpec + S) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + S) α))).run st = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    simp only [StateT.run_bind, hinl, bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private theorem run_pubFsMultiImpl_sampleT {Pt α β σ : Type} {ℓ : ℕ} [SampleableType α]
    (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (f : α → TComp (FSMultiSpec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)) β)
    (st : (ℕ → Bool) × (ℕ → σ)) :
    (simulateQ (pubFsMultiImpl impl) (sampleT α >>= f)).run st =
      (($ᵗ α : ProbComp α) >>= fun x => (simulateQ (pubFsMultiImpl impl) (f x)).run st) := by
  have h0 := simulateQ_run_liftM_unif (pubFsMultiImpl impl) (pubFsMultiImpl_inl_run impl) ($ᵗ α) st
  unfold sampleT TComp at *
  rw [simulateQ_bind, StateT.run_bind, h0, bind_assoc]
  simp only [pure_bind]

private theorem sampleOrSlot_run_pos {T Sig K I : Type} [SampleableType K]
    (M_sess sIdx : ℕ) (st : LocalSlotState T Sig K I)
    (hlt : sIdx < M_sess) (hused : st.usedSlot sIdx = false) :
    (sampleOrSlot M_sess sIdx).run st =
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) K) >>=
        fun k => Pure.pure (k, { st with usedSlot := Function.update st.usedSlot sIdx true })) := by
  have hc : (decide (sIdx < M_sess) && !st.usedSlot sIdx) = true := by simp [hlt, hused]
  simp only [sampleOrSlot, StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte,
    StateT.run_modify]
  rfl

private theorem lookupSlotFL_run_some {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (M_sess : ℕ) (Ik : I) (st : LocalSlotState T Sig K I) {k : K}
    (hlk : st.loc.table.lookup Ik = some k) :
    (lookupSlotFL M_sess Ik).run st = Pure.pure (k, st) := by
  simp [lookupSlotFL, hlk]

private theorem lookupSlotFL_run_none {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (M_sess : ℕ) (Ik : I) (st : LocalSlotState T Sig K I)
    (hlk : st.loc.table.lookup Ik = none)
    (hlt : st.loc.sessions.length < M_sess) (hused : st.usedSlot st.loc.sessions.length = false) :
    (lookupSlotFL M_sess Ik).run st =
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K))
        (.inr ⟨st.loc.sessions.length, ()⟩)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) K) >>= fun k =>
        Pure.pure (k, { loc := { st.loc with table := (Ik, k) :: st.loc.table }
                        usedSlot := Function.update st.usedSlot st.loc.sessions.length true })) := by
  have hc : (decide (st.loc.sessions.length < M_sess) && !st.usedSlot st.loc.sessions.length) = true := by
    simp [hlt, hused]
  simp only [lookupSlotFL, StateT.run_bind, StateT.run_get, pure_bind, hlk,
    sampleOrSlot, hc, ↓reduceIte, StateT.run_modify, bind_assoc]
  rfl

private theorem regSessSlot_run_mem {T Sig K I : Type} [DecidableEq I]
    (Ik : I) (st : LocalSlotState T Sig K I) (hmem : Ik ∈ st.loc.sessions) :
    (regSessSlot Ik).run st = Pure.pure (st.loc.sessions.idxOf Ik, st) := by
  simp [regSessSlot, hmem]

private theorem regSessSlot_run_not_mem {T Sig K I : Type} [DecidableEq I]
    (Ik : I) (st : LocalSlotState T Sig K I) (hnmem : Ik ∉ st.loc.sessions) :
    (regSessSlot Ik).run st =
      Pure.pure (st.loc.sessions.length,
        { st with loc := { st.loc with sessions := st.loc.sessions ++ [Ik] } }) := by
  simp [regSessSlot, hnmem]

private theorem lookupMultiF_run_some {SS RS T M E Sig K I : Type} [DecidableEq I] [SampleableType K]
    (Ik : I) (st : FSMultiState T Sig K I E) {k : K} (hlk : st.table.lookup Ik = some k) :
    (lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run st = Pure.pure (k, st) := by
  simp [lookupMultiF, hlk]

private theorem lookupMultiF_run_none {SS RS T M E Sig K I : Type} [DecidableEq I] [SampleableType K]
    (Ik : I) (st : FSMultiState T Sig K I E) (hlk : st.table.lookup Ik = none) :
    (lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run st =
      (sampleT K >>= fun k => Pure.pure (k, { st with table := (Ik, k) :: st.table })) := by
  simp [lookupMultiF, hlk, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]

private theorem regSessMulti_run_mem {SS RS T M E Sig K I : Type} [DecidableEq I]
    (Ik : I) (st : FSMultiState T Sig K I E) (hmem : Ik ∈ st.sessions) :
    (regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run st = Pure.pure (st.sessions.idxOf Ik, st) := by
  simp [regSessMulti, hmem]

private theorem regSessMulti_run_not_mem {SS RS T M E Sig K I : Type} [DecidableEq I]
    (Ik : I) (st : FSMultiState T Sig K I E) (hnmem : Ik ∉ st.sessions) :
    (regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run st =
      Pure.pure (st.sessions.length, { st with sessions := st.sessions ++ [Ik] }) := by
  simp [regSessMulti, hnmem]

private theorem table_lookup_cons_inv {I K : Type} [DecidableEq I]
    {tbl : List (I × K)} {sessions : List I} {ks : ℕ → K} {Ik : I}
    (hnmem : Ik ∉ sessions)
    (htbl : ∀ J, tbl.lookup J = if J ∈ sessions then some (ks (sessions.idxOf J)) else none) :
    ∀ J, ((Ik, ks sessions.length) :: tbl).lookup J =
      if J ∈ sessions ++ [Ik] then some (ks ((sessions ++ [Ik]).idxOf J)) else none := by
  intro J
  by_cases hJ : J = Ik
  · subst hJ
    simp [List.lookup, _root_.CryptoGames.SM.Construction.AuthL11.idxOf_append_singleton_self hnmem]
  · have hbeq : (J == Ik) = false := beq_eq_false_iff_ne.mpr hJ
    rw [List.lookup_cons, hbeq, htbl J]
    by_cases hm : J ∈ sessions
    · have hm' : J ∈ sessions ++ [Ik] := List.mem_append_left _ hm
      simp [hm, hm', _root_.CryptoGames.SM.Construction.AuthL11.idxOf_append_singleton_of_mem hm]
    · have hm' : J ∉ sessions ++ [Ik] := by
        intro hc; rcases List.mem_append.mp hc with h1 | h2
        · exact hm h1
        · exact hJ (List.mem_singleton.mp h2)
      simp [hm, hm']

private theorem table_multi_cons_inv {I K : Type} [DecidableEq I]
    {tbl : List (I × K)} {sessions : List I} {Ik : I} {k : K}
    (htbl : ∀ J, (tbl.lookup J).isSome = decide (J ∈ sessions)) :
    ∀ J, (((Ik, k) :: tbl).lookup J).isSome = decide (J ∈ sessions ++ [Ik]) := by
  intro J
  by_cases hJ : J = Ik
  · subst hJ; simp [List.lookup]
  · have hbeq : (J == Ik) = false := beq_eq_false_iff_ne.mpr hJ
    rw [List.lookup_cons, hbeq, htbl J]
    simp [List.mem_append, hJ]

private theorem usedSlot_update_inv {used : ℕ → Bool} {n : ℕ}
    (hslot : ∀ i, used i = decide (i < n)) :
    ∀ i, Function.update used n true i = decide (i < n + 1) := by
  intro i
  by_cases hi : i = n
  · subst hi; simp
  · rw [Function.update_of_ne hi, hslot i]
    by_cases hlt : i < n
    · have hlt' : i < n + 1 := by omega
      simp [hlt, hlt']
    · have hlt' : ¬(i < n + 1) := by omega
      simp [hlt, hlt']

private theorem liftFSMulti_inr_run {SS RS T M E Sig K I σ : Type}
    (impl : QueryImpl (unifSpec + FSMultiSpec SS RS T M E) (StateT σ ProbComp))
    (sIdx : ℕ) (q : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiState T Sig K I E) (st : σ) :
    (simulateQ impl
      ((liftFSMulti sIdx
        (query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inr q))).run h)).run st =
      ((impl (.inr ⟨sIdx, q⟩)).run st >>= fun p => pure ((p.1, h), p.2)) := by
  unfold liftFSMulti TComp FSMultiSpec at *
  rw [StateT_lift_run, _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions.query_eq_liftM,
      simulateQ_query]
  dsimp only [OracleQuery.input_query, OracleQuery.cont_query]
  erw [_root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions.query_eq_liftM,
       simulateQ_bind, StateT.run_bind, simulateQ_map, simulateQ_query,
       id_map, id_map]
  change (do
    let p ← (impl (Sum.inr ⟨sIdx, q⟩)).run st
    (simulateQ impl (pure (p.1, h))).run p.2) = _
  simp only [simulateQ_pure, StateT.run_pure]

private theorem liftFSMulti_transmit_eval {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (ℕ × LibsignalCiphertextWithSalt32)} {s' : SessHSt Pt ℓ}
    (hstep : (transmitHWith (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) (hp 0 0 la) (DG (lChainPRG C.F))
        (none : Option (SpecialOps _ _ _ ProbComp)) ((h, pm.1), pm.2)).run (tbl sIdx) =
      Pure.pure (u, s')) :
    (simulateQ (pubFsMultiImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((liftFSMulti sIdx (transmitQuery (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256)) h pm)).run hM)).run
      (fun _ => false, tbl) =
    Pure.pure ((u, hM), (fun _ => false, Function.update tbl sIdx s')) := by
  erw [_root_.CryptoGames.FSAEAD.transmitQuery.eq_def, liftFSMulti_inr_run,
       pubFsMultiImpl_transmit_run C ℓ encT idOf la sIdx h pm tbl hstep, pure_bind]; rfl

private theorem liftFSMulti_corruptSender_eval {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (sIdx : ℕ)
    (hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (RatchetSenderState (BitVec 256))} {s' : SessHSt Pt ℓ}
    (hstep : ((corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
        StateT (SessHSt Pt ℓ) ProbComp _)).run (tbl sIdx) = Pure.pure (u, s')) :
    (simulateQ (pubFsMultiImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
      ((liftFSMulti sIdx (corruptSenderQuery (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (AssocData := Header Pt) (Message := LibsignalMsgPublicPart × Plain ℓ)
          (Ciphertext := ℕ × LibsignalCiphertextWithSalt32))).run hM)).run
      (fun _ => false, tbl) =
    Pure.pure ((u, hM), (fun _ => false, Function.update tbl sIdx s')) := by
  erw [_root_.CryptoGames.FSAEAD.corruptSenderQuery.eq_def, liftFSMulti_inr_run,
       pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tbl hstep, pure_bind]; rfl

private theorem liftFSMulti_deliver_some_eval {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec e.2 = some p)
    (hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (ReceiveResult (Plain ℓ))} {s' : SessHSt Pt ℓ}
    (hstep : (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 la) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), e)).run (tbl sIdx) = Pure.pure (u, s')) :
    (simulateQ (pubFsMultiImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((liftFSMulti sIdx (deliverQuery (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (Message := LibsignalMsgPublicPart × Plain ℓ) h e)).run hM)).run
      (fun _ => false, tbl) =
    Pure.pure ((u.map (withPub p), hM), (fun _ => false, Function.update tbl sIdx s')) := by
  rcases e with ⟨i, ct⟩
  erw [_root_.CryptoGames.FSAEAD.deliverQuery.eq_def, liftFSMulti_inr_run,
       pubFsMultiImpl_deliver_some_run C ℓ encT idOf la sIdx h i ct p hp_pub tbl hstep, pure_bind]; rfl

private theorem liftFSMulti_inject_none_eval {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (hp_none : lPubOf protoSignalCodec e.2 = none)
    (hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tbl : ℕ → SessHSt Pt ℓ) :
    (simulateQ (pubFsMultiImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((liftFSMulti sIdx (injectQuery (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (Message := LibsignalMsgPublicPart × Plain ℓ) h e)).run hM)).run
      (fun _ => false, tbl) =
    Pure.pure ((some ReceiveResult.rejected, hM), (fun _ => false, tbl)) := by
  rcases e with ⟨i, ct⟩
  erw [_root_.CryptoGames.FSAEAD.injectQuery.eq_def, liftFSMulti_inr_run,
       pubFsMultiImpl_inject_none_run C ℓ encT idOf la sIdx h i ct hp_none tbl, pure_bind]; rfl

private theorem liftFSMulti_inject_some_eval {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool)
    (sIdx : ℕ) (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (p : LibsignalMsgPublicPart) (hp_pub : lPubOf protoSignalCodec e.2 = some p)
    (hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tbl : ℕ → SessHSt Pt ℓ)
    {u : Option (ReceiveResult (Plain ℓ))} {s' : SessHSt Pt ℓ}
    (hstep : (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 la) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), e)).run (tbl sIdx) = Pure.pure (u, s')) :
    (simulateQ (pubFsMultiImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps (hp 0 0 la)))
      ((liftFSMulti sIdx (injectQuery (SenderState := RatchetSenderState (BitVec 256))
          (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
          (Message := LibsignalMsgPublicPart × Plain ℓ) h e)).run hM)).run
      (fun _ => false, tbl) =
    Pure.pure ((u.map (withPub p), hM), (fun _ => false, Function.update tbl sIdx s')) := by
  rcases e with ⟨i, ct⟩
  erw [_root_.CryptoGames.FSAEAD.injectQuery.eq_def, liftFSMulti_inr_run,
       pubFsMultiImpl_inject_some_run C ℓ encT idOf la sIdx h i ct p hp_pub tbl hstep, pure_bind]; rfl

private structure HookBookInv {Pt Sig : Type} [DecidableEq Pt]
    (M_sess t : ℕ) (tL : Option ℕ) (ks : ℕ → BitVec 256) (rem : ℕ)
    (hL : LocalSlotState Pt Sig (BitVec 256) Pt)
    (hM : FSMultiState Pt Sig (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) : Prop where
  hsess : hM.sessions = hL.loc.sessions
  hnodup : hL.loc.sessions.Nodup
  hlen : hL.loc.sessions.length + rem ≤ M_sess
  hused : ∀ i, hL.usedSlot i = decide (i < hL.loc.sessions.length)
  htblL_lk : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = false →
    ∀ Ik, hL.loc.table.lookup Ik =
      if Ik ∈ hL.loc.sessions then some (ks (hL.loc.sessions.idxOf Ik)) else none
  htblM_lk : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = false →
    ∀ Ik, (hM.table.lookup Ik).isSome = decide (Ik ∈ hM.sessions)

private theorem HookBookInv.mono_rem {Pt Sig : Type} [DecidableEq Pt]
    {M_sess t rem rem' : ℕ} {tL : Option ℕ} {ks : ℕ → BitVec 256}
    {hL : LocalSlotState Pt Sig (BitVec 256) Pt}
    {hM : FSMultiState Pt Sig (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    (h : HookBookInv M_sess t tL ks rem hL hM) (hle : rem' ≤ rem) :
    HookBookInv M_sess t tL ks rem' hL hM :=
  { h with hlen := le_trans (Nat.add_le_add_left hle _) h.hlen }

private theorem lookup_regSess_coupled {Pt Sig : Type} [DecidableEq Pt] {ℓ : ℕ}
    {impl₀ impl₁ : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (SessHSt Pt ℓ) ProbComp)}
    {M_sess t rem' : ℕ} {tL : Option ℕ} {ks : ℕ → BitVec 256}
    {hL : LocalSlotState Pt Sig (BitVec 256) Pt}
    {hM : FSMultiState Pt Sig (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {s₀ s₁ : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)}
    (hbk : HookBookInv M_sess t tL ks (rem' + 1) hL hM)
    (htH : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = false)
    (Ik : Pt) :
    Coupled3
      (fun (rL : (BitVec 256 × ℕ) × LocalSlotState Pt Sig (BitVec 256) Pt)
           (r₀ r₁ : ((BitVec 256 × ℕ) × FSMultiState Pt Sig (BitVec 256) Pt
             (ℕ × LibsignalCiphertextWithSalt32)) × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
        ∃ sIdx kM,
          rL.1 = (ks sIdx, sIdx) ∧
          r₀.1.1 = (kM, sIdx) ∧ r₁.1.1 = (kM, sIdx) ∧
          r₁.1.2 = r₀.1.2 ∧ r₀.2 = s₀ ∧ r₁.2 = s₁ ∧
          sIdx < r₀.1.2.sessions.length ∧
          HookBookInv M_sess t tL ks rem' rL.2 r₀.1.2 ∧
          rL.2.loc.cache = hL.loc.cache ∧ r₀.1.2.cache = hM.cache ∧
          r₀.1.2.book = hM.book ∧ r₀.1.2.lfWin = hM.lfWin ∧
          (r₀.1.2.sessions = hM.sessions ∨ r₀.1.2.sessions = hM.sessions ++ [Ik]))
      (simulateQ (keySlotFixedImpl ks)
        ((do let k ← lookupSlotFL M_sess Ik; let idx ← regSessSlot Ik; return (k, idx)).run hL))
      ((simulateQ (pubFsMultiImpl impl₀)
        ((do let kM ← lookupMultiF (SS := RatchetSenderState (BitVec 256))
               (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
               (M := LibsignalMsgPublicPart × Plain ℓ) Ik
             let idx ← regSessMulti Ik
             return (kM, idx)).run hM)).run s₀)
      ((simulateQ (pubFsMultiImpl impl₁)
        ((do let kM ← lookupMultiF (SS := RatchetSenderState (BitVec 256))
               (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
               (M := LibsignalMsgPublicPart × Plain ℓ) Ik
             let idx ← regSessMulti Ik
             return (kM, idx)).run hM)).run s₁) := by
  have hlkL := hbk.htblL_lk htH Ik
  have hlkM := hbk.htblM_lk htH Ik
  by_cases hmem : Ik ∈ hL.loc.sessions
  · have hmemM : Ik ∈ hM.sessions := by rwa [hbk.hsess]
    simp only [hmem, ↓reduceIte] at hlkL
    rw [decide_eq_true hmemM, Option.isSome_iff_exists] at hlkM
    rcases hlkM with ⟨kM, hkM⟩
    have hL_eq : simulateQ (keySlotFixedImpl ks)
        ((do let k ← lookupSlotFL M_sess Ik; let idx ← regSessSlot Ik; return (k, idx)).run hL) =
        Pure.pure ((ks (hL.loc.sessions.idxOf Ik), hL.loc.sessions.idxOf Ik), hL) := by
      rw [StateT.run_bind, lookupSlotFL_run_some M_sess Ik hL hlkL, pure_bind,
          StateT.run_bind, regSessSlot_run_mem Ik hL hmem, pure_bind, StateT.run_pure, simulateQ_pure]
    have hM_eq : ∀ (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
          (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
          (StateT (SessHSt Pt ℓ) ProbComp)) (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
        ((simulateQ (pubFsMultiImpl impl)
          ((do let kM' ← lookupMultiF (SS := RatchetSenderState (BitVec 256))
                 (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                 (M := LibsignalMsgPublicPart × Plain ℓ) Ik
               let idx ← regSessMulti Ik
               return (kM', idx)).run hM)).run s) =
        Pure.pure (((kM, hM.sessions.idxOf Ik), hM), s) := by
      intro impl s
      rw [StateT.run_bind, lookupMultiF_run_some Ik hM hkM, pure_bind,
          StateT.run_bind, regSessMulti_run_mem Ik hM hmemM, pure_bind, StateT.run_pure,
          simulateQ_pure, StateT.run_pure]
    refine Coupled3.eq hL_eq (hM_eq impl₀ s₀) (hM_eq impl₁ s₁) (Coupled3.pure ?_)
    refine ⟨hL.loc.sessions.idxOf Ik, kM, rfl, ?_, ?_, rfl, rfl, rfl, ?_,
      hbk.mono_rem (by omega), rfl, rfl, rfl, rfl, Or.inl rfl⟩
    · simp [hbk.hsess]
    · simp [hbk.hsess]
    · rw [hbk.hsess]; exact List.idxOf_lt_length_of_mem hmem
  · have hmemM : Ik ∉ hM.sessions := by rwa [hbk.hsess]
    simp only [hmem, ↓reduceIte] at hlkL
    have hkM_none : hM.table.lookup Ik = none := by
      simpa [hmemM] using hlkM
    let sIdx := hL.loc.sessions.length
    have hsIdx_lt : sIdx < M_sess := by have := hbk.hlen; omega
    have hused_f : hL.usedSlot sIdx = false := by simp [hbk.hused, sIdx]
    have hL_eq : simulateQ (keySlotFixedImpl ks)
        ((do let k ← lookupSlotFL M_sess Ik; let idx ← regSessSlot Ik; return (k, idx)).run hL) =
        Pure.pure ((ks sIdx, sIdx),
          { loc := { hL.loc with table := (Ik, ks sIdx) :: hL.loc.table,
                                 sessions := hL.loc.sessions ++ [Ik] },
            usedSlot := Function.update hL.usedSlot sIdx true }) := by
      rw [StateT.run_bind, lookupSlotFL_run_none M_sess Ik hL hlkL hsIdx_lt hused_f,
        bind_assoc, simulateQ_keySlotFixedImpl_query_inr]
      simp only [pure_bind, StateT.run_bind]
      rw [regSessSlot_run_not_mem Ik _ (by simpa using hmem)]
      simp [StateT.run_pure, simulateQ_pure, sIdx]
    have hM_eq : ∀ (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
          (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
          (StateT (SessHSt Pt ℓ) ProbComp)) (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
        (simulateQ (pubFsMultiImpl impl)
          ((do let kM ← lookupMultiF (SS := RatchetSenderState (BitVec 256))
                 (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                 (M := LibsignalMsgPublicPart × Plain ℓ) Ik
               let idx ← regSessMulti Ik
               return (kM, idx)).run hM)).run s =
        (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kM =>
          Pure.pure (((kM, sIdx),
            { hM with table := (Ik, kM) :: hM.table, sessions := hM.sessions ++ [Ik] }), s)) := by
      intro impl s
      rw [StateT.run_bind, lookupMultiF_run_none Ik hM hkM_none, bind_assoc, run_pubFsMultiImpl_sampleT]
      congr 1; funext kM
      simp only [pure_bind, StateT.run_bind]
      rw [regSessMulti_run_not_mem Ik _ (by simpa using hmemM)]
      simp [StateT.run_pure, simulateQ_pure, hbk.hsess, sIdx]
    refine Coupled3.eq hL_eq (hM_eq impl₀ s₀) (hM_eq impl₁ s₁)
      (Coupled3.bind_dummy_loc ($ᵗ (BitVec 256)) fun kM => Coupled3.pure ?_)
    refine ⟨sIdx, kM, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, Or.inr rfl⟩
    · simp [hbk.hsess, sIdx]
    · refine ⟨by simp [hbk.hsess], ?_, ?_, ?_,
        fun htH' => table_lookup_cons_inv hmem (hbk.htblL_lk htH'),
        fun htH' => table_multi_cons_inv (hbk.htblM_lk htH')⟩
      · exact List.nodup_append.mpr ⟨hbk.hnodup, List.nodup_singleton _, fun x hx y hy hxy => by
          rw [List.mem_singleton] at hy; subst hy; subst hxy; exact hmem hx⟩
      · dsimp only; rw [List.length_append, List.length_singleton]; have := hbk.hlen; omega
      · intro i; dsimp only; rw [List.length_append, List.length_singleton]
        exact usedSlot_update_inv hbk.hused i

private theorem root_regSessOpt_coupled {KR Pt Sig : Type} [DecidableEq Pt] [SampleableType Pt] {ℓ : ℕ}
    {impl₀ impl₁ : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (SessHSt Pt ℓ) ProbComp)}
    (prng : PRFPRNG KR Sig Pt (BitVec 256))
    {M_sess t ep rem' : ℕ} {tL : Option ℕ} {ks : ℕ → BitVec 256}
    {hL : LocalSlotState Pt Sig (BitVec 256) Pt}
    {hM : FSMultiState Pt Sig (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {s₀ s₁ : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)}
    (hbk : HookBookInv M_sess t tL ks (rem' + 1) hL hM)
    (hempty : ep = t → (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = true →
      hL.loc.sessions = [])
    (Ik : Pt) (σ : Sig) :
    let mo : Mode := ⟨true, tL, t⟩
    Coupled3
      (fun (rL : (Sig × BitVec 256 × Option ℕ) × LocalSlotState Pt Sig (BitVec 256) Pt)
           (r₀ r₁ : ((Sig × BitVec 256 × Option ℕ) × FSMultiState Pt Sig (BitVec 256) Pt
             (ℕ × LibsignalCiphertextWithSalt32)) × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
        r₁.1.2 = r₀.1.2 ∧ r₀.2 = s₀ ∧ r₁.2 = s₁ ∧
        HookBookInv M_sess t tL ks rem' rL.2 r₀.1.2 ∧
        rL.2.loc.cache = hL.loc.cache ∧ r₀.1.2.cache = hM.cache ∧
        r₀.1.2.book = hM.book ∧ r₀.1.2.lfWin = hM.lfWin ∧
        (∃ J, r₀.1.2.sessions = hM.sessions ∨ r₀.1.2.sessions = hM.sessions ++ [J]) ∧
        (if ep = t then
          ∃ sIdx σ' kM,
            rL.1 = (σ', ks sIdx, some sIdx) ∧
            r₀.1.1 = (σ', kM, some sIdx) ∧ r₁.1.1 = (σ', kM, some sIdx) ∧
            sIdx < r₀.1.2.sessions.length
         else
          ∃ σ' k,
            rL.1 = (σ', k, none) ∧ r₀.1.1 = (σ', k, none) ∧ r₁.1.1 = (σ', k, none) ∧
            rL.2 = hL ∧ r₀.1.2 = hM))
      (simulateQ (keySlotFixedImpl ks)
        ((do let (σ', k, sid) ← rootSlotL prng mo M_sess ep Ik σ
             let idx? ← regSessOfSlot sid
             return (σ', k, idx?)).run hL))
      ((simulateQ (pubFsMultiImpl impl₀)
        ((do let (σ', k, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
               (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
               (M := LibsignalMsgPublicPart × Plain ℓ) prng mo ep Ik σ
             let idx? ← regSessOptMulti sid
             return (σ', k, idx?)).run hM)).run s₀)
      ((simulateQ (pubFsMultiImpl impl₁)
        ((do let (σ', k, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
               (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
               (M := LibsignalMsgPublicPart × Plain ℓ) prng mo ep Ik σ
             let idx? ← regSessOptMulti sid
             return (σ', k, idx?)).run hM)).run s₁) := by
  intro mo
  by_cases hgt : mo.tStar < ep
  · have hL_eq : simulateQ (keySlotFixedImpl ks)
        ((do let (σ', k, sid) ← rootSlotL prng mo M_sess ep Ik σ
             let idx? ← regSessOfSlot sid
             return (σ', k, idx?)).run hL) =
        Pure.pure (((prng.up σ Ik).1, (prng.up σ Ik).2, none), hL) := by
      simp [rootSlotL, hgt, regSessOfSlot]
    have hM_eq : ∀ (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
        (StateT (SessHSt Pt ℓ) ProbComp)) (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
        (simulateQ (pubFsMultiImpl impl)
          ((do let (σ', k, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
                 (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                 (M := LibsignalMsgPublicPart × Plain ℓ) prng mo ep Ik σ
               let idx? ← regSessOptMulti sid
               return (σ', k, idx?)).run hM)).run s =
        Pure.pure ((((prng.up σ Ik).1, (prng.up σ Ik).2, none), hM), s) := by
      intro impl s; simp [rootFSMulti, hgt, regSessOptMulti]
    rw [hL_eq, hM_eq impl₀ s₀, hM_eq impl₁ s₁]
    have hne : ep ≠ t := by dsimp [mo] at hgt; omega
    refine Coupled3.pure ⟨rfl, rfl, rfl, hbk.mono_rem (by omega), rfl, rfl, rfl, rfl, ⟨Ik, Or.inl rfl⟩, ?_⟩
    simp [hne]
  · by_cases heq : ep = mo.tStar
    · have hep : ep = t := heq
      subst hep
      have hmo : mo.tStar = ep := rfl
      by_cases htH : (mo.tL.isSome && decide (ep = mo.tH)) = true
      · have hsessL : hL.loc.sessions = [] := hempty rfl htH
        have hsessM : hM.sessions = [] := by rw [hbk.hsess, hsessL]
        have hM0 : 0 < M_sess := by have := hbk.hlen; rw [hsessL] at this; simp at this; omega
        have hused0 : hL.usedSlot 0 = false := by simp [hbk.hused, hsessL]
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            ((do let (σ', k, sid) ← rootSlotL prng mo M_sess ep Ik σ
                 let idx? ← regSessOfSlot sid
                 return (σ', k, idx?)).run hL) =
            (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
              Pure.pure (((prng.up σ Ir).1, ks 0, some 0),
                { loc := { hL.loc with sessions := [Ir] },
                  usedSlot := Function.update hL.usedSlot 0 true })) := by
          simp only [rootSlotL, hmo, lt_irrefl, ↓reduceIte, htH, StateT.run_bind, StateT_lift_run,
            StateT.run_get, StateT.run_pure, pure_bind, bind_assoc]
          rw [simulateQ_keySlotFixedImpl_sampleT]
          congr 1; funext Ir
          have hlen0 : hL.loc.sessions.length = 0 := by simp [hsessL]
          rw [hlen0, sampleOrSlot_run_pos M_sess 0 hL hM0 hused0, bind_assoc,
            simulateQ_keySlotFixedImpl_query_inr]
          have hreg : regSessOfSlot (T := Pt) (Sig := Sig) (K := BitVec 256) (some Ir) =
              (regSessSlot Ir >>= fun idx => pure (some idx)) := rfl
          simp only [pure_bind, hreg, StateT.run_bind]
          rw [regSessSlot_run_not_mem Ir _ (by simp [hsessL])]
          simp [hsessL, StateT.run_pure, simulateQ_pure]
        have hM_eq : ∀ (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
            (StateT (SessHSt Pt ℓ) ProbComp)) (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
            (simulateQ (pubFsMultiImpl impl)
              ((do let (σ', k, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
                     (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                     (M := LibsignalMsgPublicPart × Plain ℓ) prng mo ep Ik σ
                   let idx? ← regSessOptMulti sid
                   return (σ', k, idx?)).run hM)).run s =
            (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
              ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kM =>
                Pure.pure ((((prng.up σ Ir).1, kM, some 0),
                  { hM with sessions := [Ir] }), s)) := by
          intro impl s
          simp only [rootFSMulti, hmo, lt_irrefl, ↓reduceIte, htH, StateT.run_bind, StateT_lift_run,
            StateT.run_pure, pure_bind, bind_assoc]
          rw [run_pubFsMultiImpl_sampleT]
          congr 1; funext Ir
          rw [run_pubFsMultiImpl_sampleT]
          congr 1; funext kM
          have hreg : regSessOptMulti (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (T := Pt)
              (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
              (Sig := Sig) (K := BitVec 256) (some Ir) =
              (regSessMulti Ir >>= fun idx => pure (some idx)) := rfl
          simp only [hreg, StateT.run_bind, StateT.run_pure]
          rw [regSessMulti_run_not_mem Ir _ (by simp [hsessM])]
          simp [hsessM, StateT.run_pure, simulateQ_pure]
        refine Coupled3.eq hL_eq (hM_eq impl₀ s₀) (hM_eq impl₁ s₁)
          (Coupled3.bind_same ($ᵗ Pt) fun Ir =>
            Coupled3.bind_dummy_loc ($ᵗ (BitVec 256)) fun kM => Coupled3.pure ?_)
        refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, ⟨Ir, Or.inr (by simp [hsessM])⟩, ?_⟩
        · refine ⟨rfl, List.nodup_singleton Ir, ?_, ?_,
            (fun htH' => by dsimp [mo] at htH; rw [htH] at htH'; cases htH'),
            (fun htH' => by dsimp [mo] at htH; rw [htH] at htH'; cases htH')⟩
          · have hlen0 := hbk.hlen; rw [hsessL] at hlen0; simp at hlen0 ⊢; omega
          · have hused' : ∀ i, hL.usedSlot i = decide (i < 0) := by
              intro i; simpa [hsessL] using hbk.hused i
            exact usedSlot_update_inv hused'
        · simp only [↓reduceIte]
          exact ⟨0, (prng.up σ Ir).1, kM, rfl, rfl, rfl, by simp⟩
      · have htH_f : (tL.isSome && decide (ep = mo.tH)) = false := Bool.eq_false_iff.mpr htH
        have htH_mo : (mo.tL.isSome && decide (ep = mo.tH)) = false := htH_f
        have hregL : regSessOfSlot (T := Pt) (Sig := Sig) (K := BitVec 256) (some Ik) =
            (regSessSlot Ik >>= fun idx => pure (some idx)) := rfl
        have hregM : regSessOptMulti (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (T := Pt)
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            (Sig := Sig) (K := BitVec 256) (some Ik) =
            (regSessMulti Ik >>= fun idx => pure (some idx)) := rfl
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            ((do let (σ', k, sid) ← rootSlotL prng mo M_sess ep Ik σ
                 let idx? ← regSessOfSlot sid
                 return (σ', k, idx?)).run hL) =
            (simulateQ (keySlotFixedImpl ks)
              ((do let k ← lookupSlotFL M_sess Ik; let idx ← regSessSlot Ik; return (k, idx)).run hL) >>=
              fun r => Pure.pure (((prng.up σ Ik).1, r.1.1, some r.1.2), r.2)) := by
          simp only [rootSlotL, hmo, lt_irrefl, ↓reduceIte, htH_mo,
            Bool.false_eq_true, hregL, StateT.run_bind, StateT.run_pure,
            pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure]
        have hM_eq : ∀ (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
            (StateT (SessHSt Pt ℓ) ProbComp)) (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
            (simulateQ (pubFsMultiImpl impl)
              ((do let (σ', k, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
                     (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                     (M := LibsignalMsgPublicPart × Plain ℓ) prng mo ep Ik σ
                   let idx? ← regSessOptMulti sid
                   return (σ', k, idx?)).run hM)).run s =
            ((simulateQ (pubFsMultiImpl impl)
              ((do let kM ← lookupMultiF (SS := RatchetSenderState (BitVec 256))
                     (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                     (M := LibsignalMsgPublicPart × Plain ℓ) Ik
                   let idx ← regSessMulti Ik
                   return (kM, idx)).run hM)).run s >>=
              fun r => Pure.pure ((((prng.up σ Ik).1, r.1.1.1, some r.1.1.2), r.1.2), r.2)) := by
          intro impl s
          simp only [rootFSMulti, hmo, lt_irrefl, ↓reduceIte, htH_mo,
            Bool.false_eq_true, hregM, StateT.run_bind, StateT.run_pure,
            pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure]
        refine Coupled3.eq hL_eq (hM_eq impl₀ s₀) (hM_eq impl₁ s₁)
          ((lookup_regSess_coupled (impl₀ := impl₀) (impl₁ := impl₁) (s₀ := s₀) (s₁ := s₁) hbk htH_f Ik).bind ?_)
        intro rL r₀ r₁ ⟨sIdx, kM, hrL1, hr01, hr11, hr12, hs0, hs1, hsIdx, hbk', hcL, hcM, hbM, hlfM, hsess_or⟩
        refine Coupled3.pure ⟨hr12, hs0, hs1, hbk', hcL, hcM, hbM, hlfM, ⟨Ik, hsess_or⟩, ?_⟩
        simp only [↓reduceIte, hrL1, hr01, hr11]
        exact ⟨sIdx, (prng.up σ Ik).1, kM, rfl, rfl, rfl, hsIdx⟩
    · have hne : ep ≠ t := heq
      by_cases htH : (mo.tL.isSome && decide (ep = mo.tH)) = true
      · have hL_eq : simulateQ (keySlotFixedImpl ks)
            ((do let (σ', k, sid) ← rootSlotL prng mo M_sess ep Ik σ
                 let idx? ← regSessOfSlot sid
                 return (σ', k, idx?)).run hL) =
            (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
              Pure.pure (((prng.up σ Ir).1, (prng.up σ Ir).2, none), hL)) := by
          simp only [rootSlotL, hgt, heq, ↓reduceIte, htH, StateT.run_bind, StateT_lift_run,
            StateT.run_pure, pure_bind, bind_assoc, regSessOfSlot]
          rw [simulateQ_keySlotFixedImpl_sampleT]
          simp [simulateQ_pure]
        have hM_eq : ∀ (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
            (StateT (SessHSt Pt ℓ) ProbComp)) (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
            (simulateQ (pubFsMultiImpl impl)
              ((do let (σ', k, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
                     (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                     (M := LibsignalMsgPublicPart × Plain ℓ) prng mo ep Ik σ
                   let idx? ← regSessOptMulti sid
                   return (σ', k, idx?)).run hM)).run s =
            (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
              Pure.pure ((((prng.up σ Ir).1, (prng.up σ Ir).2, none), hM), s)) := by
          intro impl s
          simp only [rootFSMulti, hgt, heq, ↓reduceIte, htH, StateT.run_bind, StateT_lift_run,
            StateT.run_pure, pure_bind, bind_assoc, regSessOptMulti]
          rw [run_pubFsMultiImpl_sampleT]
          simp [simulateQ_pure, StateT.run_pure]
        refine Coupled3.eq hL_eq (hM_eq impl₀ s₀) (hM_eq impl₁ s₁)
          (Coupled3.bind_same ($ᵗ Pt) fun Ir => Coupled3.pure ?_)
        refine ⟨rfl, rfl, rfl, hbk.mono_rem (by omega), rfl, rfl, rfl, rfl, ⟨Ik, Or.inl rfl⟩, ?_⟩
        simp [hne]
      · have htH_f : (mo.tL.isSome && decide (ep = mo.tH)) = false := Bool.eq_false_iff.mpr htH
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            ((do let (σ', k, sid) ← rootSlotL prng mo M_sess ep Ik σ
                 let idx? ← regSessOfSlot sid
                 return (σ', k, idx?)).run hL) =
            Pure.pure (((prng.up σ Ik).1, (prng.up σ Ik).2, none), hL) := by
          simp [rootSlotL, hgt, heq, htH_f, regSessOfSlot]
        have hM_eq : ∀ (impl : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
            (StateT (SessHSt Pt ℓ) ProbComp)) (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
            (simulateQ (pubFsMultiImpl impl)
              ((do let (σ', k, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
                     (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                     (M := LibsignalMsgPublicPart × Plain ℓ) prng mo ep Ik σ
                   let idx? ← regSessOptMulti sid
                   return (σ', k, idx?)).run hM)).run s =
            Pure.pure ((((prng.up σ Ik).1, (prng.up σ Ik).2, none), hM), s) := by
          intro impl s; simp [rootFSMulti, hgt, heq, htH_f, regSessOptMulti]
        rw [hL_eq, hM_eq impl₀ s₀, hM_eq impl₁ s₁]
        refine Coupled3.pure ⟨rfl, rfl, rfl, hbk.mono_rem (by omega), rfl, rfl, rfl, rfl, ⟨Ik, Or.inl rfl⟩, ?_⟩
        simp [hne]

/-! ### 6. Initialization Coupling (`init_coupled3`) & `corrEPaper` Step Lemmas -/

private theorem challAllowedIn_auth_false {Msg : Type} (t ep : ℕ) :
    (Config.auth (Msg := Msg) t).challAllowedIn ep = false := rfl

private theorem party_eq_senderOf_of_sendsIn_true (P : Party) (ep : ℕ)
    (hs : P.sendsIn ep = true) : P = Party.senderOf ep := by
  cases P <;>
    simp only [Party.sendsIn, Party.senderOf, beq_iff_eq] at hs ⊢ <;>
    split_ifs at hs ⊢ <;> simp_all

private theorem party_eq_receiverOf_of_sendsIn_false (P : Party) (ep : ℕ)
    (hs : P.sendsIn ep = false) : P = Party.receiverOf ep := by
  cases P <;>
    simp only [Party.sendsIn, Party.receiverOf, Party.senderOf, Party.other, beq_iff_eq] at hs ⊢ <;>
    split_ifs at hs ⊢ <;> simp_all

private theorem SyncPaperMulti.mono_rem {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {ℓ : ℕ}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem rem' : ℕ}
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem esL esM tblM tblL)
    (hle : rem' ≤ rem) :
    SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem' esL esM tblM tblL :=
  { hsync with hlen := Nat.le_trans (Nat.add_le_add_left hle _) hsync.hlen }

private theorem SyncPaperMulti.hookBookInv {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {ℓ : ℕ}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem esL esM tblM tblL) :
    HookBookInv M_sess t tL ks rem esL.h esM.h :=
  { hsess := hsync.hsess
    hnodup := hsync.hnodup
    hlen := hsync.hlen
    hused := hsync.hused
    htblL_lk := hsync.htblL_lk
    htblM_lk := hsync.htblM_lk }

private theorem init_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (Δcka q M_sess t : ℕ) (hM : q + 1 ≤ M_sess) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
    let st0 := (fun (_ : ℕ) => false, tbl0)
    let phase1₀ := healedBy (none : Option ℕ) (2 + Δcka) t
    Coupled3
      (fun (rL : Option (PartyState _ _ _ _ _ × PartyState _ _ _ _ _) × LocalSlotState _ _ _ _)
           (r₀ r₁ : EState _ _ _ _ × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
        ∃ vA vB,
          rL.1 = some (vA, vB) ∧
          r₁.1 = r₀.1 ∧ r₀.2 = st0 ∧ r₁.2 = st0 ∧
          let gL : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
            (RatchetSenderState (BitVec 256) × Option ℕ)
            (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
            { st := fun P => match P with | .A => vA | .B => vB, b := false }
          SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1₀ q
            { g := gL, h := rL.2 } r₀.1 tbl0 tbl0)
      (simulateQ (keySlotFixedImpl ks) ((initSlotLocal cka prng fs lam mo M_sess).run {}))
      ((simulateQ (pubFsMultiImpl implF) (initFSMultiRaw cka prng fs lam mo false)).run st0)
      ((simulateQ (pubFsMultiImpl implT) (initFSMultiRaw cka prng fs lam mo false)).run st0) := by
  intro cka prng fs mo implF implT tbl0 st0 phase1₀
  have hbk0 : HookBookInv M_sess t tL ks (q + 1)
      ({} : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt)
      ({} : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) := by
    refine ⟨rfl, List.nodup_nil, by simpa using hM, fun i => by simp, fun _ Ik => by simp, fun _ Ik => by simp⟩
  have hL_eq : simulateQ (keySlotFixedImpl ks) ((initSlotLocal cka prng fs lam mo M_sess).run {}) =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kr =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kc =>
          simulateQ (keySlotFixedImpl ks)
            ((do let (σ, k, sid) ← rootSlotL prng mo M_sess 0 lam (prng.init kr)
                 let idx? ← regSessOfSlot sid
                 return (σ, k, idx?)).run {}) >>= fun r =>
            Pure.pure (some (mkParties (cka.initA kc) (cka.initB kc) r.1.1
              (fs.initSender r.1.2.1, r.1.2.2) (fs.initReceiver r.1.2.1, r.1.2.2)), r.2)) := by
    simp only [initSlotLocal, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
    rw [simulateQ_keySlotFixedImpl_sampleT]
    refine bind_congr fun kr => ?_
    rw [simulateQ_keySlotFixedImpl_sampleT]
    refine bind_congr fun kc => ?_
    simp [simulateQ_bind]
  have hM_eq : ∀ impl,
      ((simulateQ (pubFsMultiImpl impl) (initFSMultiRaw cka prng fs lam mo false)).run st0) =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kr =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kc =>
          ((simulateQ (pubFsMultiImpl impl)
            ((do let (σ, kM, sid) ← rootFSMulti (SS := RatchetSenderState (BitVec 256))
                   (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                   (M := LibsignalMsgPublicPart × Plain ℓ) prng mo 0 lam (prng.init kr)
                 let optIdx ← regSessOptMulti sid
                 return (σ, kM, optIdx)).run {})).run st0) >>= fun r =>
            let ssv0 : RatchetSenderState (BitVec 256) ⊕ ℕ := match r.1.1.2.2 with
              | none => .inl (fs.initSender r.1.1.2.1) | some sIdx => .inr sIdx
            let rsv0 : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ := match r.1.1.2.2 with
              | none => .inl (fs.initReceiver r.1.1.2.1) | some sIdx => .inr sIdx
            let pAB := mkParties (T := Pt) (cka.initA kc) (cka.initB kc) r.1.1.1 ssv0 rsv0
            Pure.pure (({ g := { st := fun | .A => pAB.1 | .B => pAB.2, b := false }, h := r.1.2 } :
              EState _ _ _ _), r.2)) := by
    intro impl
    dsimp only [initFSMultiRaw]
    rw [run_pubFsMultiImpl_sampleT]
    refine bind_congr fun kr => ?_
    rw [run_pubFsMultiImpl_sampleT]
    refine bind_congr fun kc => ?_
    simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
    refine bind_congr fun x => ?_
    rcases x with ⟨⟨⟨σ, k, sid⟩, h₁⟩, s₁⟩
    simp only [StateT.run_pure, simulateQ_pure, pure_bind]
    refine bind_congr fun y => ?_
    rcases y with ⟨⟨optIdx, h₂⟩, s₂⟩
    rfl
  refine Coupled3.eq hL_eq (hM_eq implF) (hM_eq implT)
    (Coupled3.bind_same ($ᵗ (BitVec 256)) fun kr =>
      Coupled3.bind_same ($ᵗ (BitVec 256)) fun kc => ?_)
  refine (root_regSessOpt_coupled (impl₀ := implF) (impl₁ := implT) (s₀ := st0) (s₁ := st0)
    prng hbk0 (fun _ _ => rfl) lam (prng.init kr)).bind ?_
  intro rL r₀ r₁ ⟨hr12, hs0, hs1, hbk', hcL, hcM, hbM, hlfM, _, hbranch⟩
  rcases rL with ⟨⟨σL, kL, idxL⟩, hL'⟩
  rcases r₀ with ⟨⟨⟨σ0, k0, idx0⟩, hM0⟩, s0'⟩
  rcases r₁ with ⟨⟨⟨σ1, k1, idx1⟩, hM1⟩, s1'⟩
  dsimp only at hr12 hs0 hs1 hbk' hcL hcM hbM hlfM hbranch ⊢
  subst hr12; subst hs0; subst hs1
  by_cases ht0 : 0 = t
  · subst ht0
    simp only [↓reduceIte] at hbranch
    rcases hbranch with ⟨sIdx, σ', kM, heqL, heq0, heq1, hsIdx_lt⟩
    rcases Prod.mk.inj heqL with ⟨rfl, hkidxL⟩; rcases Prod.mk.inj hkidxL with ⟨rfl, rfl⟩
    rcases Prod.mk.inj heq0 with ⟨rfl, hkidx0⟩; rcases Prod.mk.inj hkidx0 with ⟨rfl, rfl⟩
    rcases Prod.mk.inj heq1 with ⟨rfl, hkidx1⟩; rcases Prod.mk.inj hkidx1 with ⟨rfl, rfl⟩
    apply Coupled3.pure
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    refine
      { habL := rfl, habM := rfl, hwinL := rfl, hwinM := rfl, hbL := rfl, hbM := rfl
        herase := rfl
        htrans_ep := fun _ h => by cases h
        hlf := fun _ => hlfM
        hhealed := fun hp => hp
        hidL := fun P => by cases P <;> rfl
        hidM := fun P => by cases P <;> rfl
        htcurL := fun P => by cases P <;> rfl
        htcurM := fun P => by cases P <;> rfl
        hγ := fun P => by cases P <;> rfl
        hroot := fun P => by cases P <;> rfl
        hckaMsg := fun P => by cases P <;> rfl
        hvS := fun P => by
          cases P
          · rfl
          · exact ⟨rfl, hsIdx_lt, rfl, le_rfl⟩
        hvR_hi := fun P ep h => by
          cases P <;> dsimp [mkParties] at h ⊢
          · by_cases hep0 : ep = 0
            · subst hep0
              rcases h with hlt | hs
              · omega
              · dsimp [Party.sendsIn, Party.senderOf] at hs; cases hs
            · simp [hep0]
          · exact ⟨rfl, rfl⟩
        hvR_ne := fun P ep hep => by
          cases P <;> simp [mkParties, hep]
        hvR_eq := fun P => by
          cases P
          · exact ⟨sIdx, rfl, rfl, hsIdx_lt, le_rfl, rfl⟩
          · rfl
        hsess := hbk'.hsess
        hnodup := hbk'.hnodup
        hlen := hbk'.hlen
        hused := hbk'.hused
        htH_empty := fun _ hlt => by dsimp [mkParties] at hlt; omega
        htblL_lk := hbk'.htblL_lk
        htblM_lk := hbk'.htblM_lk
        hcache_ne := fun ep _ => by dsimp; rw [hcL, hcM]
        hcache_lt := fun hlt => by dsimp [mkParties] at hlt; omega
        hcache_eq := by dsimp; rw [hcL, hcM]
        hbook_out := fun i _ => ⟨by dsimp; rw [hbM], rfl, fun _ => rfl⟩
        hbook_in := fun i hi => by
          dsimp [mkParties, Party.receiverOf, Party.senderOf, Party.other]
          have hbk_none : (hM1.book i).getD {} = {} := by rw [hbM]; rfl
          rw [hbk_none]
          have hrs_eq : (if sIdx = i then fs.initReceiver (ks sIdx) else fs.initReceiver (ks i)) =
              fs.initReceiver (ks i) := by split_ifs with h <;> [subst h; skip] <;> rfl
          rw [hrs_eq]
          refine ⟨fs.initSender (ks i), activeSessInv_init C ℓ encT idOf phase1₀ (ks i) (bs i),
            fun _ => rfl, fun P ss hv => ?_⟩
          cases P
          · cases hv
          · simp only [Option.some.injEq, Prod.mk.injEq] at hv
            rcases hv with ⟨rfl, rfl⟩; rfl }
  · simp only [ht0, ↓reduceIte] at hbranch
    rcases hbranch with ⟨σ', k, heqL, heq0, heq1, rfl, rfl⟩
    rcases Prod.mk.inj heqL with ⟨rfl, hkidxL⟩; rcases Prod.mk.inj hkidxL with ⟨rfl, rfl⟩
    rcases Prod.mk.inj heq0 with ⟨rfl, hkidx0⟩; rcases Prod.mk.inj hkidx0 with ⟨rfl, rfl⟩
    rcases Prod.mk.inj heq1 with ⟨rfl, hkidx1⟩; rcases Prod.mk.inj hkidx1 with ⟨rfl, rfl⟩
    apply Coupled3.pure
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    refine
      { habL := rfl, habM := rfl, hwinL := rfl, hwinM := rfl, hbL := rfl, hbM := rfl
        herase := rfl
        htrans_ep := fun _ h => by cases h
        hlf := fun _ => rfl
        hhealed := fun hp => hp
        hidL := fun P => by cases P <;> rfl
        hidM := fun P => by cases P <;> rfl
        htcurL := fun P => by cases P <;> rfl
        htcurM := fun P => by cases P <;> rfl
        hγ := fun P => by cases P <;> rfl
        hroot := fun P => by cases P <;> rfl
        hckaMsg := fun P => by cases P <;> rfl
        hvS := fun P => by cases P <;> rfl
        hvR_hi := fun P ep h => by
          cases P <;> dsimp [mkParties] at h ⊢
          · by_cases hep0 : ep = 0
            · subst hep0
              rcases h with hlt | hs
              · omega
              · dsimp [Party.sendsIn, Party.senderOf] at hs; cases hs
            · simp [hep0]
          · exact ⟨rfl, rfl⟩
        hvR_ne := fun P ep _ => by
          cases P
          · dsimp [mkParties]; split_ifs <;> simp
          · rfl
        hvR_eq := fun P => by
          have ht_ne : t ≠ 0 := Ne.symm ht0
          cases P <;> simp [mkParties, ht_ne]
        hsess := rfl
        hnodup := List.nodup_nil
        hlen := by dsimp; omega
        hused := fun i => by simp
        htH_empty := fun _ _ => rfl
        htblL_lk := fun _ Ik => by simp
        htblM_lk := fun _ Ik => by simp
        hcache_ne := fun _ _ => rfl
        hcache_lt := fun _ => ⟨rfl, rfl⟩
        hcache_eq := rfl
        hbook_out := fun _ _ => ⟨rfl, rfl, fun _ => rfl⟩
        hbook_in := fun i hi => by simp at hi }

/-! ### 7. Oracle Step Couplings (`challE`, `corrEPaper`, `vSend`/`transmitE`, `vRecv`/`deliverE`/`injectE`/`deliverForgeE`) -/

private theorem eraseSt_corrAllowedPaper {St₁ St₂ Msg C : Type}
    {g₁ : GameState St₁ Msg C} {g₂ : GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (P : Party) :
    g₁.corrAllowedPaper P = g₂.corrAllowedPaper P := by
  have h1 : g₁.corrAllowedPaper P = (eraseSt g₁).corrAllowedPaper P := rfl
  have h2 : g₂.corrAllowedPaper P = (eraseSt g₂).corrAllowedPaper P := rfl
  rw [h1, h2, h]

private theorem eraseSt_mustBeCorrect {St₁ St₂ Msg C : Type}
    {g₁ : GameState St₁ Msg C} {g₂ : GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (maxSkip : ℕ) (P : Party) (r : Record Msg C) :
    g₁.mustBeCorrect maxSkip P r = g₂.mustBeCorrect maxSkip P r := by
  have heq : g₁.mustBeCorrect maxSkip P r = (eraseSt g₁).mustBeCorrect maxSkip P r := rfl
  have heq2 : g₂.mustBeCorrect maxSkip P r = (eraseSt g₂).mustBeCorrect maxSkip P r := rfl
  rw [heq, heq2, h]

private theorem epMgmt_st_eq_of_some {St Msg C : Type} {g s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {fresh : Bool}
    (hep : g.epMgmt Δ qep P fresh = some s₁) : s₁.st = g.st := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep
  all_goals subst hep; rfl

private theorem epMgmt_win_eq_of_some {St Msg C : Type} {g s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {fresh : Bool}
    (hep : g.epMgmt Δ qep P fresh = some s₁) : s₁.win = g.win := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep
  all_goals subst hep; rfl

private theorem epMgmt_b_eq_of_some {St Msg C : Type} {g s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {fresh : Bool}
    (hep : g.epMgmt Δ qep P fresh = some s₁) : s₁.b = g.b := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep
  all_goals subst hep; rfl

private theorem epMgmt_trans_eq_of_some {St Msg C : Type} {g s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {fresh : Bool}
    (hep : g.epMgmt Δ qep P fresh = some s₁) : s₁.trans = g.trans := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep
  all_goals subst hep; rfl

private theorem epMgmt_map_eraseSt {St Msg C : Type}
    (g : GameState St Msg C) (Δ qep : ℕ) (P : Party) (fresh : Bool) :
    (g.epMgmt Δ qep P fresh).map eraseSt = (eraseSt g).epMgmt Δ qep P fresh := by
  have hep : (eraseSt g).epoch P = g.epoch P := rfl
  have hsc : (eraseSt g).safeCh Δ P = g.safeCh Δ P := rfl
  unfold GameState.epMgmt
  simp only [hep, hsc]
  split_ifs <;> rfl

private theorem eraseSt_epMgmt_sync {St₁ St₂ Msg C : Type}
    {g₁ : GameState St₁ Msg C} {g₂ : GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (Δ qep : ℕ) (P : Party) (fresh : Bool) :
    (g₁.epMgmt Δ qep P fresh).map eraseSt = (g₂.epMgmt Δ qep P fresh).map eraseSt := by
  rw [epMgmt_map_eraseSt, epMgmt_map_eraseSt, h]

private def EpochQepInv {St Msg C : Type} (qep : ℕ) (g : GameState St Msg C) : Prop :=
  ∀ P : Party, g.epoch P ≤ qep + 1 ∧ (g.epoch P = qep + 1 → P.sendsIn (qep + 1) = false)

private theorem sendsIn_succ_true_of_false (P : Party) (ep : ℕ) (h : P.sendsIn ep = false) :
    P.sendsIn (ep + 1) = true := by
  cases P <;>
    simp only [Party.sendsIn, beq_eq_false_iff_ne, beq_iff_eq] at h ⊢ <;>
    omega

private theorem epochQepInv_init {St Msg C : Type} (qep : ℕ) (st : Party → St) (b : Bool) :
    EpochQepInv qep ({ st := st, b := b } : GameState St Msg C) :=
  fun _ => ⟨Nat.zero_le _, fun h => by dsimp at h; omega⟩

private theorem epochQepInv_epMgmt {St Msg C : Type} {qep Δ : ℕ} {g s₁ : GameState St Msg C}
    {P : Party} {fresh : Bool}
    (hqep : EpochQepInv qep g) (hep : g.epMgmt Δ qep P fresh = some s₁) :
    EpochQepInv qep s₁ := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with hs hgt hb hgt2 <;> simp only [Option.some.injEq] at hep
  · subst hep
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      simp only [GameState.leak, Function.update_self]
      exact ⟨by omega, fun h => by omega⟩
    · simp only [GameState.leak, Function.update_of_ne hQP]
      exact hqep Q
  · subst hep
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      simp only [Function.update_self]
      exact ⟨by omega, fun h => by omega⟩
    · simp only [Function.update_of_ne hQP]
      exact hqep Q
  · subst hep; exact hqep

private theorem epochQepInv_afterCorr {St Msg C : Type} {qep : ℕ} {g : GameState St Msg C}
    (P : Party) (hqep : EpochQepInv qep g) :
    EpochQepInv qep (g.afterCorr P) := hqep

private theorem epochQepInv_record {St Msg C : Type} {qep Δ : ℕ} {g : GameState St Msg C}
    (P : Party) (st' : St) (r : Record Msg C) (isChall : Bool) (hqep : EpochQepInv qep g) :
    EpochQepInv qep (g.record Δ P st' r isChall) := hqep

private theorem epochQepInv_vRecv_le {St Msg C : Type} {qep ep : ℕ} {g : GameState St Msg C}
    {P : Party} (hqep : EpochQepInv qep g) (hs : P.sendsIn ep = false)
    (hle : ep ≤ g.epoch P + 1) :
    ep ≤ qep + 1 := by
  obtain ⟨h1, h2⟩ := hqep P
  by_cases heq : g.epoch P = qep + 1
  · have hsf := h2 heq
    have hst := sendsIn_succ_true_of_false P (qep + 1) hsf
    by_cases hep2 : ep = qep + 2
    · subst hep2; rw [hst] at hs; cases hs
    · omega
  · omega

private theorem epochQepInv_accept {St Msg C : Type} {qep : ℕ} {g : GameState St Msg C}
    (P : Party) (st' : St) (pos : Pos)
    (hqep : EpochQepInv qep g) (hs : P.sendsIn pos.epoch = false) (hle : pos.epoch ≤ qep + 1) :
    EpochQepInv qep (g.accept P st' pos) := by
  intro Q
  by_cases hQP : Q = P
  · subst hQP
    dsimp only [GameState.accept, GameState.delete]
    rw [Function.update_self]
    refine ⟨Nat.max_le.mpr ⟨(hqep Q).1, hle⟩, fun hmax => ?_⟩
    by_cases hpe : pos.epoch = qep + 1
    · rwa [← hpe]
    · have hge : g.epoch Q = qep + 1 := by have := (hqep Q).1; omega
      exact (hqep Q).2 hge
  · dsimp only [GameState.accept, GameState.delete]
    rw [Function.update_of_ne hQP]
    exact hqep Q

private theorem activeSessInv_phase1_to_false {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {phase1 : Bool} {k : BitVec 256} {ss : _} {rs : _} {bk : _} {sM sL : _}
    (h : ActiveSessInv C ℓ encT idOf phase1 k ss rs bk sM sL) :
    ActiveSessInv C ℓ encT idOf false k ss rs bk sM sL := by
  cases phase1
  · exact h
  · exact activeSessInv_to_phase2 C ℓ encT idOf h

private def StepPost2 {Pt R : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) (rem : ℕ)
    (rL : R × EStateSlot (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) Pt)
    (rM : (R × EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)
      (FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))) ×
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) : Prop :=
  rL.2.abort = true ∨
  (rL.1 = rM.1.1 ∧
    ((rL.2.abort = false ∧ rL.2.g.win = true ∧ rM.1.2.abort = false ∧ rM.1.2.g.win = true ∧
        eraseSt rL.2.g = eraseSt rM.1.2.g) ∨
     (∃ tblM' tblL', rM.2 = (fun _ => false, tblM') ∧ EpochQepInv qep rL.2.g ∧
        SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false rem rL.2 rM.1.2 tblM' tblL')))

private def StepPost3 {Pt R : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) (rem : ℕ)
    (rL : R × EStateSlot (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) Pt)
    (r₀ r₁ : (R × EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)
      (FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))) ×
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) : Prop :=
  rL.2.abort = true ∨
  (r₁.1.2.abort = true ∧ r₁.1.2.h.lfWin = true) ∨
  (rL.1 = r₀.1.1 ∧ rL.2.abort = false ∧ rL.2.g.win = true ∧ r₀.1.2.abort = false ∧ r₀.1.2.g.win = true ∧
    eraseSt rL.2.g = eraseSt r₀.1.2.g) ∨
  (rL.1 = r₀.1.1 ∧ ∃ tblM' tblL', r₀.2 = (fun _ => false, tblM') ∧ EpochQepInv qep rL.2.g ∧
    SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false rem rL.2 r₀.1.2 tblM' tblL') ∨
  (rL.1 = r₀.1.1 ∧ rL.1 = r₁.1.1 ∧ r₁.1.2 = r₀.1.2 ∧
    ∃ tblM' tblL', r₀.2 = (fun _ => false, tblM') ∧ r₁.2 = (fun _ => false, tblL') ∧ EpochQepInv qep rL.2.g ∧
      SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true rem rL.2 r₀.1.2 tblM' tblL')

private theorem stepPost2_imp_stepPost3 {Pt R : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {ℓ : ℕ}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka qep M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {rem : ℕ}
    {rL : _} {r₀ r₁ : _}
    (h : StepPost2 (R := R) C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem rL r₀) :
    StepPost3 (R := R) C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem rL r₀ r₁ := by
  rcases h with hab | ⟨heq, hwin | hsync⟩
  · exact Or.inl hab
  · rcases hwin with ⟨h1, h2, h3, h4, h5⟩
    exact Or.inr (Or.inr (Or.inl ⟨heq, h1, h2, h3, h4, h5⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨heq, hsync⟩)))

@[simp]
private theorem liftH_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv T Sv SSv RSv M E α : Type}
    (x : HM tspec HS α) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem challE_auth_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep : ℕ) (tL : Option ℕ) (t : ℕ) (π : Policy)
    (qry : Party × M × M × Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (challE hk Δ qep (⟨true, tL, t⟩ : Mode).cfg π qry).run es = pure (none, es) := by
  rcases qry with ⟨P, m₀, m₁, r⟩
  unfold challE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : (es.abort || es.g.win) = true
  · simp [h1, StateT.run_pure]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt Δ qep P r.isSome with
    | none => simp [StateT.run_pure]
    | some s₁ =>
      have hch : (⟨true, tL, t⟩ : Mode).cfg.challAllowedIn (Msg := M) (s₁.epoch P) = false :=
        challAllowedIn_auth_false t (s₁.epoch P)
      simp [hch, StateT.run_pure]

private theorem corrEPaper_coupled_phase2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {phase1 : Bool} {rem : ℕ}
    (P : Party)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 (rem + 1) esL esM tblM tblL)
    (hheal_after : esL.g.corrAllowedPaper P = true →
      ((⟨true, tL, t⟩ : Mode).policy.leakDoom esL.g (esL.g.afterCorr P) ||
        (⟨true, tL, t⟩ : Mode).policy.corrDoom esL.g P) = false →
      healedBy (esL.g.afterCorr P).tL (2 + Δcka) t = false)
    (hheal_stay : esL.g.corrAllowedPaper P = false → healedBy esL.g.tL (2 + Δcka) t = false) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (StepPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((corrEPaper (hooksSlotLocal cka prng fs mo M_sess) mo.policy P).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((corrEPaper (hooksFSMulti cka prng fs Δcka mo false false) mo.policy P).run esM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  unfold corrEPaper
  have hca_eq : esL.g.corrAllowedPaper P = esM.g.corrAllowedPaper P :=
    eraseSt_corrAllowedPaper hsync.herase P
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habL, hsync.habM,
    hsync.hwinL, hsync.hwinM, Bool.false_or]
  by_cases hca : esL.g.corrAllowedPaper P = true
  · have hcaM : esM.g.corrAllowedPaper P = true := hca_eq.symm.trans hca
    simp only [hca, hcaM, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have herase1 : eraseSt (esL.g.afterCorr P) = eraseSt (esM.g.afterCorr P) :=
      _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_afterCorr hsync.herase P
    have hdoom_eq :
        (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) =
        (mo.policy.leakDoom esM.g (esM.g.afterCorr P) || mo.policy.corrDoom esM.g P) := by
      rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_leakDoom hsync.herase herase1 mo.policy,
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_corrDoom hsync.herase mo.policy P]
    by_cases hdoom : (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) = true
    · have hdoomM : (mo.policy.leakDoom esM.g (esM.g.afterCorr P) || mo.policy.corrDoom esM.g P) = true :=
        hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify,
        pure_bind, StateT.run_pure, simulateQ_pure]
      exact Coupled2.pure (Or.inl rfl)
    · simp only [Bool.not_eq_true] at hdoom
      have hdoomM : (mo.policy.leakDoom esM.g (esM.g.afterCorr P) || mo.policy.corrDoom esM.g P) = false :=
        hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, Bool.false_eq_true, ↓reduceIte]
      have hcd_false : mo.policy.corrDoom esL.g P = false := by
        cases h : mo.policy.corrDoom esL.g P
        · rfl
        · rw [h, Bool.or_true] at hdoom; cases hdoom
      have hvRt_L : (esL.g.st P).vR t = none := by
        have hv := hsync.hvR_eq P
        cases hP : (esL.g.st P).vR t with
        | none => rfl
        | some ro =>
          rw [hP] at hv
          rcases hv with ⟨_, _, _, _, hle, hP_eq⟩
          rw [hsync.htcurL P] at hle
          have hcd_true := corrDoom_of_receiverOf_le esL.g Δcka tL t P hvg hP_eq hle
          rw [hcd_true] at hcd_false; cases hcd_false
      have hvRt_M : (esM.g.st P).vR t = none := by
        have hv := hsync.hvR_eq P; rw [hvRt_L] at hv; exact hv
      have hrealParty_eq : ∀ (vS : Option (RatchetSenderState (BitVec 256)))
          (fM : ℕ → Option (RatchetReceiverState (BitVec 256) (BitVec 256))),
          (∀ ep, ((esL.g.st P).vR ep).map Prod.fst = fM ep) →
          realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root vS
            (fun ep => ((esL.g.st P).vR ep).map Prod.fst) =
          realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root vS fM := by
        intro vS fM hfM
        dsimp only [realParty]
        have hid_eq : (esL.g.st P).id = (esM.g.st P).id := (hsync.hidL P).trans (hsync.hidM P).symm
        rw [hid_eq, ← hsync.hroot P, ← hsync.hγ P, ← hsync.hckaMsg P, ← hsync.htcurM P, funext hfM]
      have hheal1 : healedBy (esL.g.afterCorr P).tL (2 + Δcka) t = false := hheal_after hca hdoom
      have hvS_sync := hsync.hvS P
      cases hvSL : (esL.g.st P).vS with
      | none =>
        rw [hvSL] at hvS_sync
        dsimp only [hooksSlotLocal, hooksFSMulti, mo]
        simp only [liftH_run, hvSL, hvS_sync, hvRt_M, StateT.run_bind, StateT.run_pure, pure_bind,
          StateT.run_modify, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, Option.map_none]
        apply Coupled2.pure
        refine Or.inr ⟨congrArg some (hrealParty_eq none _ fun ep => by
          by_cases hep : ep = t
          · subst hep; simp [hvRt_L, hvRt_M]
          · have hv := hsync.hvR_ne P ep hep
            cases hP : (esL.g.st P).vR ep with
            | none => rw [hP] at hv; simp [hv]
            | some ro => rw [hP] at hv; rcases hv with ⟨_, hvM⟩; simp [hvM]),
          Or.inr ⟨tblM, tblL, rfl, epochQepInv_afterCorr P hqep, ?_⟩⟩
        refine
          { habL := hsync.habL, habM := hsync.habM
            hwinL := hsync.hwinL, hwinM := hsync.hwinM
            hbL := hsync.hbL, hbM := hsync.hbM
            herase := herase1
            htrans_ep := hsync.htrans_ep
            hlf := fun h => Bool.noConfusion h
            hhealed := fun _ => hheal1
            hidL := hsync.hidL, hidM := hsync.hidM
            htcurL := hsync.htcurL, htcurM := hsync.htcurM
            hγ := hsync.hγ, hroot := hsync.hroot, hckaMsg := hsync.hckaMsg
            hvS := hsync.hvS, hvR_hi := hsync.hvR_hi, hvR_ne := hsync.hvR_ne, hvR_eq := hsync.hvR_eq
            hsess := hsync.hsess, hnodup := hsync.hnodup
            hlen := Nat.le_trans (Nat.add_le_add_left (Nat.le_succ rem) _) hsync.hlen
            hused := hsync.hused, htH_empty := hsync.htH_empty
            htblL_lk := hsync.htblL_lk, htblM_lk := hsync.htblM_lk
            hcache_ne := hsync.hcache_ne, hcache_lt := hsync.hcache_lt, hcache_eq := hsync.hcache_eq
            hbook_out := fun i hi =>
              let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
              ⟨hb, hm, fun h => Bool.noConfusion h⟩
            hbook_in := fun i hi =>
              let ⟨ss_i, hinv, hss1, hss2⟩ := hsync.hbook_in i hi
              ⟨ss_i, activeSessInv_phase1_to_false C encT idOf hinv, hss1, hss2⟩ }
      | some so =>
        rcases so with ⟨ss, optIdx⟩
        cases optIdx with
        | none =>
          rw [hvSL] at hvS_sync
          dsimp only [hooksSlotLocal, hooksFSMulti, mo]
          simp only [liftH_run, hvSL, hvS_sync, hvRt_M, StateT.run_bind, StateT.run_pure, pure_bind,
            StateT.run_modify, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, Option.map_some]
          apply Coupled2.pure
          refine Or.inr ⟨congrArg some (hrealParty_eq (some ss) _ fun ep => by
            by_cases hep : ep = t
            · subst hep; simp [hvRt_L, hvRt_M]
            · have hv := hsync.hvR_ne P ep hep
              cases hP : (esL.g.st P).vR ep with
              | none => rw [hP] at hv; simp [hv]
              | some ro => rw [hP] at hv; rcases hv with ⟨_, hvM⟩; simp [hvM]),
            Or.inr ⟨tblM, tblL, rfl, epochQepInv_afterCorr P hqep, ?_⟩⟩
          refine
            { habL := hsync.habL, habM := hsync.habM
              hwinL := hsync.hwinL, hwinM := hsync.hwinM
              hbL := hsync.hbL, hbM := hsync.hbM
              herase := herase1
              htrans_ep := hsync.htrans_ep
              hlf := fun h => Bool.noConfusion h
              hhealed := fun _ => hheal1
              hidL := hsync.hidL, hidM := hsync.hidM
              htcurL := hsync.htcurL, htcurM := hsync.htcurM
              hγ := hsync.hγ, hroot := hsync.hroot, hckaMsg := hsync.hckaMsg
              hvS := hsync.hvS, hvR_hi := hsync.hvR_hi, hvR_ne := hsync.hvR_ne, hvR_eq := hsync.hvR_eq
              hsess := hsync.hsess, hnodup := hsync.hnodup
              hlen := Nat.le_trans (Nat.add_le_add_left (Nat.le_succ rem) _) hsync.hlen
              hused := hsync.hused, htH_empty := hsync.htH_empty
              htblL_lk := hsync.htblL_lk, htblM_lk := hsync.htblM_lk
              hcache_ne := hsync.hcache_ne, hcache_lt := hsync.hcache_lt, hcache_eq := hsync.hcache_eq
              hbook_out := fun i hi =>
                let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
                ⟨hb, hm, fun h => Bool.noConfusion h⟩
              hbook_in := fun i hi =>
                let ⟨ss_i, hinv, hss1, hss2⟩ := hsync.hbook_in i hi
                ⟨ss_i, activeSessInv_phase1_to_false C encT idOf hinv, hss1, hss2⟩ }
        | some sIdx =>
          rw [hvSL] at hvS_sync
          rcases hvS_sync with ⟨hvSM, hsIdx_lt, _, _⟩
          rcases hsync.hbook_in sIdx hsIdx_lt with ⟨ss_sIdx, hinv_sIdx, hss1, hss2⟩
          have hss_eq : ss_sIdx = ss := hss2 P ss hvSL
          subst hss_eq
          have hinv_f := activeSessInv_phase1_to_false C encT idOf hinv_sIdx
          rcases activeSessInv_corruptSender C ℓ encT idOf hinv_f with ⟨sM', hcs_eval, hinv'⟩
          let bk_upd := Function.update esM.h.book sIdx (some { (esM.h.book sIdx).getD {} with sCorr := true })
          refine Coupled2.eq
            (mL' := Pure.pure (some (realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root
              (some ss_sIdx) (fun ep => ((esL.g.st P).vR ep).map Prod.fst)),
              { esL with g := esL.g.afterCorr P }))
            (mR' := Pure.pure ((some (realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root
              (some ss_sIdx) (fun ep => ((esL.g.st P).vR ep).map Prod.fst)),
              { esM with g := esM.g.afterCorr P, h := { esM.h with book := bk_upd } }),
              (fun _ => false, Function.update tblM sIdx sM')))
            ?_ ?_ (Coupled2.pure ?_)
          · dsimp only [hooksSlotLocal]
            simp [hvSL, StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
          · dsimp only [hooksFSMulti, mo, implF]
            simp only [liftH_run, hvSM, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              simulateQ_bind, bind_assoc, pure_bind]
            rw [liftFSMulti_corruptSender_eval C encT idOf sIdx esM.h tblM hcs_eval]
            simp only [hvRt_M, bk_upd, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, pure_bind, Bool.false_eq_true, ↓reduceIte]
            congr 5
            funext ep
            by_cases hep : ep = t
            · subst hep; simp [hvRt_L, hvRt_M]
            · have hv := hsync.hvR_ne P ep hep
              cases hP : (esL.g.st P).vR ep with
              | none => rw [hP] at hv; simp [hv]
              | some ro => rw [hP] at hv; rcases hv with ⟨_, hvM⟩; simp [hvM]
          · refine Or.inr ⟨congrArg some (hrealParty_eq (some ss_sIdx) _ fun _ => rfl),
              Or.inr ⟨Function.update tblM sIdx sM', tblL, rfl, epochQepInv_afterCorr P hqep, ?_⟩⟩
            refine
              { habL := hsync.habL, habM := hsync.habM
                hwinL := hsync.hwinL, hwinM := hsync.hwinM
                hbL := hsync.hbL, hbM := hsync.hbM
                herase := herase1
                htrans_ep := hsync.htrans_ep
                hlf := fun h => Bool.noConfusion h
                hhealed := fun _ => hheal1
                hidL := hsync.hidL, hidM := hsync.hidM
                htcurL := hsync.htcurL, htcurM := hsync.htcurM
                hγ := hsync.hγ, hroot := hsync.hroot, hckaMsg := hsync.hckaMsg
                hvS := hsync.hvS, hvR_hi := hsync.hvR_hi, hvR_ne := hsync.hvR_ne, hvR_eq := hsync.hvR_eq
                hsess := hsync.hsess, hnodup := hsync.hnodup
                hlen := Nat.le_trans (Nat.add_le_add_left (Nat.le_succ rem) _) hsync.hlen
                hused := hsync.hused, htH_empty := hsync.htH_empty
                htblL_lk := hsync.htblL_lk, htblM_lk := hsync.htblM_lk
                hcache_ne := hsync.hcache_ne, hcache_lt := hsync.hcache_lt, hcache_eq := hsync.hcache_eq
                hbook_out := fun i hi => by
                  dsimp only at hi
                  have hne : i ≠ sIdx := by omega
                  let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
                  exact ⟨by dsimp [bk_upd]; rw [Function.update_of_ne hne]; exact hb,
                         by rw [Function.update_of_ne hne]; exact hm,
                         fun h => Bool.noConfusion h⟩
                hbook_in := fun i hi => by
                  by_cases hi_eq : i = sIdx
                  · subst hi_eq
                    refine ⟨ss_sIdx, ?_, hss1, hss2⟩
                    dsimp [bk_upd]
                    rw [Function.update_self, Function.update_self]
                    exact hinv'
                  · let ⟨ss_i, hinv_i, hss1_i, hss2_i⟩ := hsync.hbook_in i hi
                    refine ⟨ss_i, ?_, hss1_i, hss2_i⟩
                    dsimp [bk_upd]
                    rw [Function.update_of_ne hi_eq, Function.update_of_ne hi_eq]
                    exact activeSessInv_phase1_to_false C encT idOf hinv_i }
  · simp only [Bool.not_eq_true] at hca
    have hcaM : esM.g.corrAllowedPaper P = false := hca_eq.symm.trans hca
    simp only [hca, hcaM, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, hqep,
      { (hsync.mono_rem (Nat.le_succ rem)) with
        hlf := fun h => Bool.noConfusion h
        hhealed := fun _ => hheal_stay hca
        hbook_out := fun i hi =>
          let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
          ⟨hb, hm, fun h => Bool.noConfusion h⟩
        hbook_in := fun i hi =>
          let ⟨ss_i, hinv, hss1, hss2⟩ := hsync.hbook_in i hi
          ⟨ss_i, activeSessInv_phase1_to_false C encT idOf hinv, hss1, hss2⟩ }⟩⟩)

private theorem corrEPaper_coupled_phase1_stay {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (P : Party)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL)
    (hheal_true : esL.g.corrAllowedPaper P = true →
      ((⟨true, tL, t⟩ : Mode).policy.leakDoom esL.g (esL.g.afterCorr P) ||
        (⟨true, tL, t⟩ : Mode).policy.corrDoom esL.g P) = false →
      healedBy (esL.g.afterCorr P).tL (2 + Δcka) t = true) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((corrEPaper (hooksSlotLocal cka prng fs mo M_sess) mo.policy P).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((corrEPaper (hooksFSMulti cka prng fs Δcka mo false false) mo.policy P).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((corrEPaper (hooksFSMulti cka prng fs Δcka mo false true) mo.policy P).run esM)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  unfold corrEPaper
  have hca_eq : esL.g.corrAllowedPaper P = esM.g.corrAllowedPaper P :=
    eraseSt_corrAllowedPaper hsync.herase P
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habL, hsync.habM,
    hsync.hwinL, hsync.hwinM, Bool.false_or]
  by_cases hca : esL.g.corrAllowedPaper P = true
  · have hcaM : esM.g.corrAllowedPaper P = true := hca_eq.symm.trans hca
    simp only [hca, hcaM, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have herase1 : eraseSt (esL.g.afterCorr P) = eraseSt (esM.g.afterCorr P) :=
      _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_afterCorr hsync.herase P
    have hdoom_eq :
        (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) =
        (mo.policy.leakDoom esM.g (esM.g.afterCorr P) || mo.policy.corrDoom esM.g P) := by
      rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_leakDoom hsync.herase herase1 mo.policy,
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_corrDoom hsync.herase mo.policy P]
    by_cases hdoom : (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) = true
    · have hdoomM : (mo.policy.leakDoom esM.g (esM.g.afterCorr P) || mo.policy.corrDoom esM.g P) = true :=
        hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify,
        pure_bind, StateT.run_pure, simulateQ_pure]
      exact Coupled3.pure (Or.inl rfl)
    · simp only [Bool.not_eq_true] at hdoom
      have hdoomM : (mo.policy.leakDoom esM.g (esM.g.afterCorr P) || mo.policy.corrDoom esM.g P) = false :=
        hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, Bool.false_eq_true, ↓reduceIte]
      have hheal1 := hheal_true hca hdoom
      have hcd_false : mo.policy.corrDoom esL.g P = false := by
        cases h : mo.policy.corrDoom esL.g P
        · rfl
        · rw [h, Bool.or_true] at hdoom; cases hdoom
      have hvRt_L : (esL.g.st P).vR t = none := by
        have hv := hsync.hvR_eq P
        cases hP : (esL.g.st P).vR t with
        | none => rfl
        | some ro =>
          rw [hP] at hv
          rcases hv with ⟨_, _, _, _, hle, hP_eq⟩
          rw [hsync.htcurL P] at hle
          have hcd_true := corrDoom_of_receiverOf_le esL.g Δcka tL t P hvg hP_eq hle
          rw [hcd_true] at hcd_false; cases hcd_false
      have hvRt_M : (esM.g.st P).vR t = none := by
        have hv := hsync.hvR_eq P; rw [hvRt_L] at hv; exact hv
      have hrealParty_eq : ∀ (vS : Option (RatchetSenderState (BitVec 256)))
          (fM : ℕ → Option (RatchetReceiverState (BitVec 256) (BitVec 256))),
          (∀ ep, ((esL.g.st P).vR ep).map Prod.fst = fM ep) →
          realParty (esL.g.st P) (esL.g.st P).γ (esL.g.st P).root vS
            (fun ep => ((esL.g.st P).vR ep).map Prod.fst) =
          realParty (esM.g.st P) (esM.g.st P).γ (esM.g.st P).root vS fM := by
        intro vS fM hfM
        dsimp only [realParty]
        have hid_eq : (esL.g.st P).id = (esM.g.st P).id := (hsync.hidL P).trans (hsync.hidM P).symm
        rw [hid_eq, ← hsync.hroot P, ← hsync.hγ P, ← hsync.hckaMsg P, ← hsync.htcurM P, funext hfM]
      have hvS_sync := hsync.hvS P
      cases hvSL : (esL.g.st P).vS with
      | none =>
        rw [hvSL] at hvS_sync
        dsimp only [hooksSlotLocal, hooksFSMulti, mo]
        simp only [liftH_run, hvSL, hvS_sync, hvRt_M, StateT.run_bind, StateT.run_pure, pure_bind,
          StateT.run_modify, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, Option.map_none]
        apply Coupled3.pure
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨congrArg some (hrealParty_eq none _ fun ep => by
            by_cases hep : ep = t
            · subst hep; simp [hvRt_L, hvRt_M]
            · have hv := hsync.hvR_ne P ep hep
              cases hP : (esL.g.st P).vR ep with
              | none => rw [hP] at hv; simp [hv]
              | some ro => rw [hP] at hv; rcases hv with ⟨_, hvM⟩; simp [hvM]),
          congrArg some (hrealParty_eq none _ fun ep => by
            by_cases hep : ep = t
            · subst hep; simp [hvRt_L, hvRt_M]
            · have hv := hsync.hvR_ne P ep hep
              cases hP : (esL.g.st P).vR ep with
              | none => rw [hP] at hv; simp [hv]
              | some ro => rw [hP] at hv; rcases hv with ⟨_, hvM⟩; simp [hvM]),
          rfl, tblM, tblL, rfl, rfl, epochQepInv_afterCorr P hqep, ?_⟩)))
        exact
          { (hsync.mono_rem (Nat.le_succ rem)) with
            habL := hsync.habL, habM := hsync.habM
            hwinL := hsync.hwinL, hwinM := hsync.hwinM
            hbL := hsync.hbL, hbM := hsync.hbM
            herase := herase1
            hhealed := fun hp => Bool.noConfusion hp }
      | some so =>
        rcases so with ⟨ss, optIdx⟩
        cases optIdx with
        | none =>
          rw [hvSL] at hvS_sync
          dsimp only [hooksSlotLocal, hooksFSMulti, mo]
          simp only [liftH_run, hvSL, hvS_sync, hvRt_M, StateT.run_bind, StateT.run_pure, pure_bind,
            StateT.run_modify, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, Option.map_some]
          apply Coupled3.pure
          refine Or.inr (Or.inr (Or.inr (Or.inr ⟨congrArg some (hrealParty_eq (some ss) _ fun ep => by
              by_cases hep : ep = t
              · subst hep; simp [hvRt_L, hvRt_M]
              · have hv := hsync.hvR_ne P ep hep
                cases hP : (esL.g.st P).vR ep with
                | none => rw [hP] at hv; simp [hv]
                | some ro => rw [hP] at hv; rcases hv with ⟨_, hvM⟩; simp [hvM]),
            congrArg some (hrealParty_eq (some ss) _ fun ep => by
              by_cases hep : ep = t
              · subst hep; simp [hvRt_L, hvRt_M]
              · have hv := hsync.hvR_ne P ep hep
                cases hP : (esL.g.st P).vR ep with
                | none => rw [hP] at hv; simp [hv]
                | some ro => rw [hP] at hv; rcases hv with ⟨_, hvM⟩; simp [hvM]),
            rfl, tblM, tblL, rfl, rfl, epochQepInv_afterCorr P hqep, ?_⟩)))
          exact
            { (hsync.mono_rem (Nat.le_succ rem)) with
              habL := hsync.habL, habM := hsync.habM
              hwinL := hsync.hwinL, hwinM := hsync.hwinM
              hbL := hsync.hbL, hbM := hsync.hbM
              herase := herase1
              hhealed := fun hp => Bool.noConfusion hp }
        | some sIdx =>
          rw [hvSL] at hvS_sync
          rcases hvS_sync with ⟨_, _, _, hle⟩
          rw [hsync.htcurL P] at hle
          rw [healedBy_afterCorr_false esL.g P Δcka t hle] at hheal1
          cases hheal1
  · simp only [Bool.not_eq_true] at hca
    have hcaM : esM.g.corrAllowedPaper P = false := hca_eq.symm.trans hca
    simp only [hca, hcaM, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, hqep,
      hsync.mono_rem (Nat.le_succ rem)⟩))))

private theorem corrEPaper_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (P : Party)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((corrEPaper (hooksSlotLocal cka prng fs mo M_sess) mo.policy P).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((corrEPaper (hooksFSMulti cka prng fs Δcka mo false false) mo.policy P).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((corrEPaper (hooksFSMulti cka prng fs Δcka mo false true) mo.policy P).run esM)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  by_cases htrans : esL.g.corrAllowedPaper P = true ∧
      (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) = false ∧
      healedBy (esL.g.afterCorr P).tL (2 + Δcka) t = false
  · rcases htrans with ⟨hca, hdoom, hheal_f⟩
    have hc2 := corrEPaper_coupled_phase2 C Dh encPt encT idOf Δcka qep M_sess t tL hvg ks bs P hqep hsync
      (fun _ _ => hheal_f) (fun hca_f => by rw [hca] at hca_f; cases hca_f)
    exact Coupled2.to_coupled3_m2 _ hc2 fun _ _ _ => stepPost2_imp_stepPost3
  · refine corrEPaper_coupled_phase1_stay C Dh encPt encT idOf Δcka qep M_sess t tL hvg ks bs P hqep hsync ?_
    intro hca hdoom
    cases hh : healedBy (esL.g.afterCorr P).tL (2 + Δcka) t
    · exfalso; exact htrans ⟨hca, hdoom, hh⟩
    · rfl

/-! ### 8. `startSend_coupled3` and `startRecv_coupled3` -/

private theorem startRecv_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {impl₀ impl₁ : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (SessHSt Pt ℓ) ProbComp)}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka M_sess t ep rem' : ℕ) (tL : Option ℕ) (ks : ℕ → BitVec 256)
    (ctxL : _) (ctxM : _) (P : Party)
    {hL : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt}
    {hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    {s₀ s₁ : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)}
    (hbk : HookBookInv M_sess t tL ks (rem' + 1) hL hM)
    (hcache_ne : ∀ ep', ep' ≠ t →
      match hL.loc.cache ep' with
      | none => hM.cache ep' = none
      | some (Tc, σc, k, idx?) => idx? = none ∧ hM.cache ep' = some (Tc, σc, k, none))
    (hcache_eq :
      match hL.loc.cache t with
      | none => hM.cache t = none
      | some (Tc, σc, k, idx?) =>
        ∃ sIdx kM, idx? = some sIdx ∧ k = ks sIdx ∧ sIdx < hM.sessions.length ∧
          hM.cache t = some (Tc, σc, kM, some sIdx))
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σ : CryptoGames.Ratchet.RootKey) (Tn : Pt) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    Coupled3
      (fun (rL : Option (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt × CryptoGames.Ratchet.RootKey ×
              (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))) × LocalSlotState _ _ _ _)
           (r₀ r₁ : (Option (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt × CryptoGames.Ratchet.RootKey ×
              (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))) × FSMultiState _ _ _ _ _) ×
              ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
        r₁.1.2 = r₀.1.2 ∧ r₀.2 = s₀ ∧ r₁.2 = s₁ ∧
        HookBookInv M_sess t tL ks rem' rL.2 r₀.1.2 ∧
        rL.2.loc.cache = hL.loc.cache ∧ r₀.1.2.cache = hM.cache ∧
        r₀.1.2.book = hM.book ∧ r₀.1.2.lfWin = hM.lfWin ∧
        (∃ J, r₀.1.2.sessions = hM.sessions ∨ ((tL.isSome && decide (t = mo.tH)) = false ∧ r₀.1.2.sessions = hM.sessions ++ [J])) ∧
        ((rL.1 = none ∧ r₀.1.1 = none ∧ r₁.1.1 = none ∧ rL.2 = hL ∧ r₀.1.2 = hM) ∨
         (rL.1 = some none ∧ r₀.1.1 = some none ∧ r₁.1.1 = some none ∧ rL.2 = hL ∧ r₀.1.2 = hM) ∨
         (ep = t ∧ ∃ γ' σ' sIdx,
            rL.1 = some (some (γ', σ', (fs.initReceiver (ks sIdx), some sIdx))) ∧
            r₀.1.1 = some (some (γ', σ', .inr sIdx)) ∧
            r₁.1.1 = some (some (γ', σ', .inr sIdx)) ∧
            sIdx < r₀.1.2.sessions.length) ∨
         (ep ≠ t ∧ ∃ γ' σ' k,
            rL.1 = some (some (γ', σ', (fs.initReceiver k, none))) ∧
            r₀.1.1 = some (some (γ', σ', .inl (fs.initReceiver k))) ∧
            r₁.1.1 = some (some (γ', σ', .inl (fs.initReceiver k))) ∧
            rL.2 = hL ∧ r₀.1.2 = hM)))
      (simulateQ (keySlotFixedImpl ks)
        (((hooksSlotLocal cka prng fs mo M_sess).startRecv ctxL P ep γ σ Tn).run hL))
      ((simulateQ (pubFsMultiImpl impl₀)
        (((hooksFSMulti cka prng fs Δcka mo false false).startRecv ctxM P ep γ σ Tn).run hM)).run s₀)
      ((simulateQ (pubFsMultiImpl impl₁)
        (((hooksFSMulti cka prng fs Δcka mo false true).startRecv ctxM P ep γ σ Tn).run hM)).run s₁) := by
  intro cka prng fs mo
  have hbk' : HookBookInv M_sess t tL ks rem' hL hM := hbk.mono_rem (Nat.le_succ rem')
  let R_recv :=
    fun (rL : Option (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt × CryptoGames.Ratchet.RootKey ×
            (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))) × LocalSlotState _ _ _ _)
         (r₀ r₁ : (Option (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt × CryptoGames.Ratchet.RootKey ×
            (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))) × FSMultiState _ _ _ _ _) ×
            ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
      r₁.1.2 = r₀.1.2 ∧ r₀.2 = s₀ ∧ r₁.2 = s₁ ∧
      HookBookInv M_sess t tL ks rem' rL.2 r₀.1.2 ∧
      rL.2.loc.cache = hL.loc.cache ∧ r₀.1.2.cache = hM.cache ∧
      r₀.1.2.book = hM.book ∧ r₀.1.2.lfWin = hM.lfWin ∧
      (∃ J, r₀.1.2.sessions = hM.sessions ∨ ((tL.isSome && decide (t = mo.tH)) = false ∧ r₀.1.2.sessions = hM.sessions ++ [J])) ∧
      ((rL.1 = none ∧ r₀.1.1 = none ∧ r₁.1.1 = none ∧ rL.2 = hL ∧ r₀.1.2 = hM) ∨
       (rL.1 = some none ∧ r₀.1.1 = some none ∧ r₁.1.1 = some none ∧ rL.2 = hL ∧ r₀.1.2 = hM) ∨
       (ep = t ∧ ∃ γ' σ' sIdx,
          rL.1 = some (some (γ', σ', (fs.initReceiver (ks sIdx), some sIdx))) ∧
          r₀.1.1 = some (some (γ', σ', .inr sIdx)) ∧
          r₁.1.1 = some (some (γ', σ', .inr sIdx)) ∧
          sIdx < r₀.1.2.sessions.length) ∨
       (ep ≠ t ∧ ∃ γ' σ' k,
          rL.1 = some (some (γ', σ', (fs.initReceiver k, none))) ∧
          r₀.1.1 = some (some (γ', σ', .inl (fs.initReceiver k))) ∧
          r₁.1.1 = some (some (γ', σ', .inl (fs.initReceiver k))) ∧
          rL.2 = hL ∧ r₀.1.2 = hM))
  change Coupled3 R_recv _ _ _
  by_cases hep : ep = t
  · subst hep
    have hmiss :
        (hL.loc.cache ep = none ∧ hM.cache ep = none ∨
          ∃ Tc σc k idx? kM sIdx,
            hL.loc.cache ep = some (Tc, σc, k, idx?) ∧
            hM.cache ep = some (Tc, σc, kM, sIdx) ∧ Tc ≠ Tn) →
        Coupled3 R_recv
          (simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).startRecv ctxL P ep γ σ Tn).run hL))
          ((simulateQ (pubFsMultiImpl impl₀)
            (((hooksFSMulti cka prng fs Δcka mo false false).startRecv ctxM P ep γ σ Tn).run hM)).run s₀)
          ((simulateQ (pubFsMultiImpl impl₁)
            (((hooksFSMulti cka prng fs Δcka mo false true).startRecv ctxM P ep γ σ Tn).run hM)).run s₁) := by
      intro hm_cases
      by_cases htH : (mo.tL.isSome && decide (ep = mo.tH)) = true
      · rcases hm_cases with ⟨hcL, hcM⟩ | ⟨Tc, σc, k, idx?, kM, optIdx, hcL, hcM, hT⟩
        · dsimp only [hooksSlotLocal, hooksFSMulti]
          simp [StateT.run_bind, StateT.run_get, hcL, hcM,
            show mo.auth = true from rfl, show mo.tStar = ep from rfl,
            htH, StateT.run_pure, simulateQ_pure]
          exact Coupled3.pure ⟨rfl, rfl, rfl, hbk', rfl, rfl, rfl, rfl, ⟨Tn, Or.inl rfl⟩,
            Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · dsimp only [hooksSlotLocal, hooksFSMulti]
          simp [StateT.run_bind, StateT.run_get, hcL, hcM, hT,
            show mo.auth = true from rfl, show mo.tStar = ep from rfl,
            htH, StateT.run_pure, simulateQ_pure]
          exact Coupled3.pure ⟨rfl, rfl, rfl, hbk', rfl, rfl, rfl, rfl, ⟨Tn, Or.inl rfl⟩,
            Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      · have htH_f : (mo.tL.isSome && decide (ep = mo.tH)) = false := Bool.eq_false_iff.mpr htH
        let kk := cka.receive γ Tn
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).startRecv ctxL P ep γ σ Tn).run hL) =
            (simulateQ (keySlotFixedImpl ks)
              ((do let k' ← lookupSlotFL M_sess kk.2; let idx ← regSessSlot kk.2; return (k', idx)).run hL) >>=
              fun r => Pure.pure (some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver r.1.1, some r.1.2))), r.2)) := by
          rcases hm_cases with ⟨hcL, _⟩ | ⟨Tc, σc, k, idx?, _, _, hcL, _, hT⟩
          · dsimp only [hooksSlotLocal]
            rw [StateT.run_bind, StateT.run_get]
            simp only [pure_bind, hcL, show mo.auth = true from rfl, show mo.tStar = ep from rfl,
              Bool.true_and, decide_true, ↓reduceIte, htH_f, Bool.false_eq_true]
            simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, kk]
          · dsimp only [hooksSlotLocal]
            rw [StateT.run_bind, StateT.run_get]
            simp only [pure_bind, hcL, hT, show mo.auth = true from rfl, show mo.tStar = ep from rfl,
              Bool.true_and, decide_true, ↓reduceIte, htH_f, Bool.false_eq_true]
            simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, kk]
        have hM_eq : ∀ impl la (s : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)),
            ((simulateQ (pubFsMultiImpl impl)
              (((hooksFSMulti cka prng fs Δcka mo false la).startRecv ctxM P ep γ σ Tn).run hM)).run s) =
            (((simulateQ (pubFsMultiImpl impl)
              ((do let kM ← lookupMultiF (SS := RatchetSenderState (BitVec 256))
                     (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                     (M := LibsignalMsgPublicPart × Plain ℓ) kk.2
                   let sIdx ← regSessMulti kk.2
                   return (kM, sIdx)).run hM)).run s) >>=
              fun r => Pure.pure ((some (some (kk.1, (prng.up σ kk.2).1, .inr r.1.1.2)), r.1.2), r.2)) := by
          intro impl la s
          rcases hm_cases with ⟨_, hcM⟩ | ⟨Tc, σc, _, _, kM, optIdx, _, hcM, hT⟩
          · dsimp only [hooksFSMulti]
            rw [StateT.run_bind, StateT.run_get]
            simp only [pure_bind, hcM, Bool.false_eq_true, ↓reduceIte,
              show mo.auth = true from rfl, show mo.tStar = ep from rfl,
              Bool.true_and, decide_true, htH_f]
            simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, kk]
          · dsimp only [hooksFSMulti]
            rw [StateT.run_bind, StateT.run_get]
            simp only [pure_bind, hcM, hT, Bool.false_eq_true, ↓reduceIte,
              show mo.auth = true from rfl, show mo.tStar = ep from rfl,
              Bool.true_and, decide_true, htH_f]
            simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, kk]
        refine Coupled3.eq hL_eq (hM_eq impl₀ false s₀) (hM_eq impl₁ true s₁)
          ((lookup_regSess_coupled (impl₀ := impl₀) (impl₁ := impl₁) (s₀ := s₀) (s₁ := s₁)
            hbk htH_f kk.2).bind ?_)
        intro rL r₀ r₁ ⟨sIdx, kM, hrL1, hr01, hr11, hr12, hs0, hs1, hsIdx, hbk2, hcL, hcM, hbM, hlfM, hsess_or⟩
        refine Coupled3.pure ⟨hr12, hs0, hs1, hbk2, hcL, hcM, hbM, hlfM, ⟨kk.2, hsess_or.imp id fun h => ⟨htH_f, h⟩⟩,
          Or.inr (Or.inr (Or.inl ⟨rfl, kk.1, (prng.up σ kk.2).1, sIdx, ?_, ?_, ?_, hsIdx⟩))⟩
        · simp [hrL1]
        · simp [hr01]
        · simp [hr11]
    cases hcL : hL.loc.cache ep with
    | none =>
      rw [hcL] at hcache_eq
      exact hmiss (Or.inl ⟨hcL, hcache_eq⟩)
    | some entry =>
      rcases entry with ⟨Tc, σc, k, idx?⟩
      rw [hcL] at hcache_eq
      rcases hcache_eq with ⟨sIdx, kM, rfl, rfl, hsIdx_lt, hcM⟩
      by_cases hT : Tc = Tn
      · dsimp only [hooksSlotLocal, hooksFSMulti]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL, hcM, hT, ↓reduceIte,
          StateT.run_pure, simulateQ_pure]
        exact Coupled3.pure ⟨rfl, rfl, rfl, hbk', rfl, rfl, rfl, rfl, ⟨Tn, Or.inl rfl⟩,
          Or.inr (Or.inr (Or.inl ⟨rfl, (cka.receive γ Tn).1, σc, sIdx, rfl, rfl, rfl, hsIdx_lt⟩))⟩
      · exact hmiss (Or.inr ⟨Tc, σc, ks sIdx, some sIdx, kM, some sIdx, hcL, hcM, hT⟩)
  · have hc_sync := hcache_ne ep hep
    cases hcL : hL.loc.cache ep with
    | none =>
      rw [hcL] at hc_sync
      dsimp only [hooksSlotLocal, hooksFSMulti, mo]
      simp [StateT.run_bind, StateT.run_get, hcL, hc_sync, hep, StateT.run_pure, simulateQ_pure]
      exact Coupled3.pure ⟨rfl, rfl, rfl, hbk', rfl, rfl, rfl, rfl, ⟨Tn, Or.inl rfl⟩,
        Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩
    | some entry =>
      rcases entry with ⟨Tc, σc, k, idx?⟩
      rw [hcL] at hc_sync
      rcases hc_sync with ⟨rfl, hcM⟩
      by_cases hT : Tc = Tn
      · dsimp only [hooksSlotLocal, hooksFSMulti]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hcL, hcM, hT, ↓reduceIte,
          StateT.run_pure, simulateQ_pure]
        exact Coupled3.pure ⟨rfl, rfl, rfl, hbk', rfl, rfl, rfl, rfl, ⟨Tn, Or.inl rfl⟩,
          Or.inr (Or.inr (Or.inr ⟨hep, (cka.receive γ Tn).1, σc, k, rfl, rfl, rfl, rfl, rfl⟩))⟩
      · dsimp only [hooksSlotLocal, hooksFSMulti, mo]
        simp [StateT.run_bind, StateT.run_get, hcL, hcM, hT, hep, StateT.run_pure, simulateQ_pure]
        exact Coupled3.pure ⟨rfl, rfl, rfl, hbk', rfl, rfl, rfl, rfl, ⟨Tn, Or.inl rfl⟩,
          Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)⟩

/-! ### 9. `fsSend` and `fsRecv` Hook Couplings -/

private theorem activeSessInv_false_set_sL {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL sL' : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM sL) :
    ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM sL' :=
  let ⟨stR, h⟩ := hinv
  ⟨stR, { h with syncRML := fun hp1 => Bool.noConfusion hp1 }⟩

private theorem map_withPub_rejected {ℓ : ℕ} (p : LibsignalMsgPublicPart) :
    withPub p (ReceiveResult.rejected : ReceiveResult (Plain ℓ)) =
      ReceiveResult.rejected := rfl

private theorem map_withPub_accepted {ℓ : ℕ} (p : LibsignalMsgPublicPart) (idx : ℕ) (m : Plain ℓ) :
    withPub p (ReceiveResult.accepted idx (some m)) =
      ReceiveResult.accepted idx (some (p, m)) := rfl

private theorem hdr_ct_beq_eq {Pt : Type} [DecidableEq Pt]
    (x y : Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :
    @BEq.beq _ (@instBEqProd (Header Pt) (ℕ × LibsignalCiphertextWithSalt32) inferInstance instBEqOfDecidableEq) x y =
      (x == y) := by
  rcases x with ⟨h1, n1, c1⟩
  rcases y with ⟨h2, n2, c2⟩
  have hn : decide (n1 = n2) = (n1 == n2) := by cases h : (n1 == n2) <;> simp_all
  have hc : decide (c1 = c2) = (c1 == c2) := by cases h : (c1 == c2) <;> simp_all
  change (h1 == h2 && decide ((n1, c1) = (n2, c2))) = (h1 == h2 && (n1 == n2 && c1 == c2))
  simp [Prod.mk.injEq, hn, hc]

private theorem fsRecv_coupled2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka M_sess t ep : ℕ) (tL : Option ℕ) (ks : ℕ → BitVec 256)
    (ctxL : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (ctxM : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (hheal_f : ep = t → healedBy ctxM.tL (2 + Δcka) t = false)
    (hL : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt)
    (hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (rsvL : RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
    (rsvM : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (ssLoc : RatchetSenderState (BitVec 256))
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (recL : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)))
    (recM : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)))
    (hv : (ep ≠ t ∧ ∃ rs, rsvL = (rs, none) ∧ rsvM = .inl rs) ∨
      (ep = t ∧ ∃ rsLoc sIdx,
        rsvL = (rsLoc, some sIdx) ∧ rsvM = .inr sIdx ∧ sIdx < hM.sessions.length ∧
        ActiveSessInv C ℓ encT idOf false (ks sIdx) ssLoc rsLoc
          ((hM.book sIdx).getD {}) (tblM sIdx) (tblL sIdx))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2
      (fun (rL : Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ) ×
              ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × LocalSlotState _ _ _ _)
           (rM : (Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
              ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × FSMultiState _ _ _ _ _) ×
              ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
        rL.2.usedSlot = hL.usedSlot ∧
        rL.2.loc.cache = hL.loc.cache ∧ rL.2.loc.table = hL.loc.table ∧ rL.2.loc.sessions = hL.loc.sessions ∧
        match rsvL with
        | (rs, none) =>
          ep ≠ t ∧
          match fs.receive rs hdr e with
          | none => rL.1 = some none ∧ rM = ((some none, hM), (fun _ => false, tblM))
          | some (rs', idxOut, pmOut) =>
            rL.1 = some (some ((rs', none), idxOut, pmOut)) ∧
            rM = ((some (some (.inl rs', idxOut, pmOut)), hM), (fun _ => false, tblM))
        | (rsLoc, some sIdx) =>
          ep = t ∧
          ∃ hM' tblM',
            rM.2 = (fun _ => false, tblM') ∧
            rM.1.2 = hM' ∧
            hM'.cache = hM.cache ∧ hM'.table = hM.table ∧
            hM'.sessions = hM.sessions ∧ hM'.lfWin = hM.lfWin ∧
            (∀ i, i ≠ sIdx → hM'.book i = hM.book i ∧ tblM' i = tblM i) ∧
            match fs.receive rsLoc hdr e with
            | none =>
              rL.1 = some none ∧ rM.1.1 = some none ∧
              ActiveSessInv C ℓ encT idOf false (ks sIdx) ssLoc rsLoc
                ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL sIdx)
            | some (rsLoc', idxOut, pmOut) =>
              rL.1 = some (some ((rsLoc', some sIdx), idxOut, pmOut)) ∧
              rM.1.1 = some (some (.inr sIdx, idxOut, pmOut)) ∧
              ActiveSessInv C ℓ encT idOf false (ks sIdx) ssLoc rsLoc'
                ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL sIdx))
      (simulateQ (keySlotFixedImpl ks)
        (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep rsvL hdr e recL).run hL))
      ((simulateQ (pubFsMultiImpl implF)
        (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep rsvM hdr e recM).run hM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  rcases hv with ⟨hep, rs, rfl, rfl⟩ | ⟨rfl, rsLoc, sIdx, rfl, rfl, hsIdx_lt, hinv⟩
  · dsimp only [hooksSlotLocal, hooksFSMulti]
    cases hrec : fs.receive rs hdr e with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure, Option.map_none]
      exact Coupled2.pure ⟨rfl, rfl, rfl, rfl, hep, rfl, rfl⟩
    | some o =>
      rcases o with ⟨rs', idxOut, pmOut⟩
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure, Option.map_some]
      exact Coupled2.pure ⟨rfl, rfl, rfl, rfl, hep, rfl, rfl⟩
  · have hheal := hheal_f rfl
    let bk := (hM.book sIdx).getD {}
    cases hmatch : bk.fsTrans.find? (fun x => x.2 == (hdr, e)) with
    | some mEntry =>
      rcases activeSessInv_deliver C hD signalRoundTripShort_proto ℓ (ell_add_16_lt_rustLenBound hℓ)
        encT idOf hinv hdr e hmatch with ⟨p, hpub, hdeliv⟩
      cases hrec : fs.receive rsLoc hdr e with
      | none =>
        rw [hrec] at hdeliv
        rcases hdeliv with ⟨sM', sL', hdelM, _, hinv'⟩
        let tblM' := Function.update tblM sIdx sM'
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
            Pure.pure (some none, hL) := by
          dsimp only [hooksSlotLocal]; simp [hrec, StateT.run_pure, simulateQ_pure]
        have hM_eq : ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM)) =
            Pure.pure ((some none, hM), (fun _ => false, tblM')) := by
          dsimp only [hooksFSMulti, implF]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = some mEntry from hmatch,
            Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind,
            Bool.not_true, Option.isSome_some]
          rw [liftFSMulti_deliver_some_eval C encT idOf false sIdx hdr e p hpub hM tblM hdelM]
          simp [map_withPub_rejected, StateT.run_pure, simulateQ_pure, tblM']
        refine Coupled2.eq hL_eq hM_eq (Coupled2.pure ?_)
        refine ⟨rfl, rfl, rfl, rfl, rfl, hM, tblM', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · intro i hne; simp [tblM', Function.update_of_ne hne]
        · rw [hrec]
          exact ⟨rfl, rfl, by simpa [tblM', bk, Function.update_self] using activeSessInv_false_set_sL (sL' := tblL sIdx) hinv'⟩
      | some o =>
        rcases o with ⟨rsLoc', idxOut, pmOut⟩
        rw [hrec] at hdeliv
        rcases hdeliv with ⟨hm1, sM', sL', hdelM, _, hpm1, hinv'⟩
        have hpm_eq : (p, pmOut.2) = pmOut := Prod.ext hpm1.symm rfl
        let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
          { bk with fsTrans := bk.fsTrans.filter (·.1 != mEntry.1) }
        let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
        let tblM' := Function.update tblM sIdx sM'
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
            Pure.pure (some (some ((rsLoc', some sIdx), idxOut, pmOut)),
              { hL with loc := { hL.loc with lastIdx := some sIdx } }) := by
          dsimp only [hooksSlotLocal]
          simp [hrec, StateT.run_modify, simulateQ_pure]
        have hM_eq : ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM)) =
            Pure.pure ((some (some (.inr sIdx, idxOut, pmOut)), hM'), (fun _ => false, tblM')) := by
          dsimp only [hooksFSMulti, implF]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = some mEntry from hmatch,
            Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind,
            Bool.not_true, Option.isSome_some]
          rw [liftFSMulti_deliver_some_eval C encT idOf false sIdx hdr e p hpub hM tblM hdelM]
          simp [map_withPub_accepted, hpm_eq, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, hM', tblM', bk', bk]
        refine Coupled2.eq hL_eq hM_eq (Coupled2.pure ?_)
        refine ⟨rfl, rfl, rfl, rfl, rfl, hM', tblM', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · intro i hne; simp [hM', tblM', Function.update_of_ne hne]
        · rw [hrec]
          exact ⟨rfl, rfl, by simpa [hM', tblM', bk', Function.update_self] using activeSessInv_false_set_sL (sL' := tblL sIdx) hinv'⟩
    | none =>
      -- Ensure sCorr = true first (either via corruptSenderQuery or already bk.sCorr = true)
      have hpre_corr : ∃ (hM₁ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
          (tblM₁ : ℕ → SessHSt Pt ℓ),
          hM₁.cache = hM.cache ∧ hM₁.table = hM.table ∧
          hM₁.sessions = hM.sessions ∧ hM₁.lfWin = hM.lfWin ∧
          (∀ i, i ≠ sIdx → hM₁.book i = hM.book i ∧ tblM₁ i = tblM i) ∧
          ((hM₁.book sIdx).getD {}).sCorr = true ∧
          ((hM₁.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none ∧
          ActiveSessInv C ℓ encT idOf false (ks sIdx) ssLoc rsLoc
            ((hM₁.book sIdx).getD {}) (tblM₁ sIdx) (tblL sIdx) ∧
          ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM)) =
          ((simulateQ (pubFsMultiImpl implF)
            ((do
              let res ← liftFSMulti sIdx (injectQuery (SenderState := RatchetSenderState (BitVec 256))
                (ReceiverState := RatchetReceiverState (BitVec 256) (BitVec 256))
                (Message := LibsignalMsgPublicPart × Plain ℓ) hdr e)
              match res with
              | none => pure none
              | some .rejected => pure (some none)
              | some (.accepted i mo') =>
                let _ ← get
                let drop := (Option.map (fun x : ℕ × (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) => x.1) none).getD i
                modify fun (s : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) =>
                  let b := (s.book sIdx).getD {}
                  let b' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                    { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                  { s with book := Function.update s.book sIdx (some b') }
                match mo', recM with
                | some m, _ => pure (some (some ((Sum.inr sIdx : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ), i, m)))
                | none, some r => pure (some (some ((Sum.inr sIdx : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ), i, r.msg)))
                | none, none => pure none).run hM₁)).run (fun _ => false, tblM₁)) := by
        cases hsc : ((hM.book sIdx).getD {}).sCorr with
        | true =>
          refine ⟨hM, tblM, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, hsc, hmatch, hinv, ?_⟩
          dsimp only [hooksFSMulti]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
            Option.isNone_none, hheal, hsc, Bool.not_true, Bool.not_false, Bool.true_and,
            Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
            Option.map_none, Option.getD_none]
          refine congrArg (fun f => ((simulateQ (pubFsMultiImpl implF) ((liftFSMulti sIdx (injectQuery hdr e) >>= f).run _)).run _)) ?_
          funext res; cases res with
          | none => rfl
          | some rr => cases rr with
            | rejected => rfl
            | accepted i mo' => cases mo' <;> cases recM <;> rfl
        | false =>
          rcases activeSessInv_corruptSender C ℓ encT idOf hinv with ⟨sM₁, hcs_eval, hinv₁⟩
          let bk₁ : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) := { bk with sCorr := true }
          let hM₁ := { hM with book := Function.update hM.book sIdx (some bk₁) }
          let tblM₁ := Function.update tblM sIdx sM₁
          refine ⟨hM₁, tblM₁, rfl, rfl, rfl, rfl,
            fun i hne => by simp [hM₁, tblM₁, Function.update_of_ne hne],
            by simp [hM₁, bk₁, Function.update_self],
            by simpa [hM₁, bk₁, bk, Function.update_self] using hmatch,
            by simpa [hM₁, tblM₁, bk₁, bk, Function.update_self] using hinv₁,
            ?_⟩
          dsimp only [hooksFSMulti]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
            Option.isNone_none, hheal, hsc, Bool.not_false, Bool.not_true, Bool.true_and,
            Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
            Option.map_none, Option.getD_none]
          rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
          rw [liftFSMulti_corruptSender_eval C encT idOf sIdx hM tblM hcs_eval]
          simp only [pure_bind]
          rw [StateT.run_bind, StateT.run_modify]
          simp only [pure_bind, hM₁, tblM₁, bk₁, bk]
          refine congrArg (fun f => ((simulateQ (pubFsMultiImpl implF) ((liftFSMulti sIdx (injectQuery hdr e) >>= f).run _)).run _)) ?_
          funext res; cases res with
          | none => rfl
          | some rr => cases rr with
            | rejected => rfl
            | accepted i mo' => cases mo' <;> cases recM <;> rfl
      rcases hpre_corr with ⟨hM₁, tblM₁, hc1, ht1, hs1, hlf1, hne1, hsc1, hmatch1, hinv₁, hM_unfold⟩
      cases hpub : lPubOf protoSignalCodec e.2 with
      | none =>
        have hrec_none : fs.receive rsLoc hdr e = none := by
          dsimp only [fs]; rw [lFS_receive_eq, hpub]
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
            Pure.pure (some none, hL) := by
          dsimp only [hooksSlotLocal]; simp [hrec_none, StateT.run_pure, simulateQ_pure]
        have hM_eq : ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM)) =
            Pure.pure ((some none, hM₁), (fun _ => false, tblM₁)) := by
          rw [hM_unfold]
          dsimp only [implF]
          simp only [StateT.run_bind, simulateQ_bind]
          rw [liftFSMulti_inject_none_eval C encT idOf false sIdx hdr e hpub hM₁ tblM₁]
          simp [StateT.run_pure, simulateQ_pure]
        refine Coupled2.eq hL_eq hM_eq (Coupled2.pure ?_)
        refine ⟨rfl, rfl, rfl, rfl, rfl, hM₁, tblM₁, rfl, rfl, hc1, ht1, hs1, hlf1, hne1, ?_⟩
        rw [hrec_none]
        exact ⟨rfl, rfl, hinv₁⟩
      | some p =>
        have hinj := activeSessInv_inject_phase2 C ℓ encT idOf hinv₁ hsc1 hdr e hmatch1 p hpub
        cases hrec : fs.receive rsLoc hdr e with
        | none =>
          rw [hrec] at hinj
          rcases hinj with ⟨sM₂, hinjM, hinv₂⟩
          let tblM₂ := Function.update tblM₁ sIdx sM₂
          have hL_eq : simulateQ (keySlotFixedImpl ks)
              (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
              Pure.pure (some none, hL) := by
            dsimp only [hooksSlotLocal]; simp [hrec, StateT.run_pure, simulateQ_pure]
          have hM_eq : ((simulateQ (pubFsMultiImpl implF)
              (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
              (fun _ => false, tblM)) =
              Pure.pure ((some none, hM₁), (fun _ => false, tblM₂)) := by
            rw [hM_unfold]
            dsimp only [implF]
            simp only [StateT.run_bind, simulateQ_bind]
            rw [liftFSMulti_inject_some_eval C encT idOf false sIdx hdr e p hpub hM₁ tblM₁ hinjM]
            simp [map_withPub_rejected, StateT.run_pure, simulateQ_pure, tblM₂]
          refine Coupled2.eq hL_eq hM_eq (Coupled2.pure ?_)
          refine ⟨rfl, rfl, rfl, rfl, rfl, hM₁, tblM₂, rfl, rfl, hc1, ht1, hs1, hlf1, ?_, ?_⟩
          · intro i hne
            rcases hne1 i hne with ⟨hb_i, ht_i⟩
            exact ⟨hb_i, by simp [tblM₂, Function.update_of_ne hne, ht_i]⟩
          · rw [hrec]
            exact ⟨rfl, rfl, by simpa [tblM₂, Function.update_self] using hinv₂⟩
        | some o =>
          rcases o with ⟨rsLoc', idxOut, pmOut⟩
          rw [hrec] at hinj
          rcases hinj with ⟨sM₂, hinjM, hpm1, hinv₂⟩
          have hpm_eq : (p, pmOut.2) = pmOut := Prod.ext hpm1.symm rfl
          let bk₂ : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { (hM₁.book sIdx).getD {} with fsTrans := ((hM₁.book sIdx).getD {}).fsTrans.filter (·.1 != idxOut) }
          let hM₂ := { hM₁ with book := Function.update hM₁.book sIdx (some bk₂) }
          let tblM₂ := Function.update tblM₁ sIdx sM₂
          have hL_eq : simulateQ (keySlotFixedImpl ks)
              (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
              Pure.pure (some (some ((rsLoc', some sIdx), idxOut, pmOut)),
                { hL with loc := { hL.loc with lastIdx := some sIdx } }) := by
            dsimp only [hooksSlotLocal]
            simp [hrec, StateT.run_modify, simulateQ_pure]
          have hM_eq : ((simulateQ (pubFsMultiImpl implF)
              (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
              (fun _ => false, tblM)) =
              Pure.pure ((some (some (.inr sIdx, idxOut, pmOut)), hM₂), (fun _ => false, tblM₂)) := by
            rw [hM_unfold]
            dsimp only [implF]
            simp only [StateT.run_bind, simulateQ_bind]
            rw [liftFSMulti_inject_some_eval C encT idOf false sIdx hdr e p hpub hM₁ tblM₁ hinjM]
            simp [map_withPub_accepted, hpm_eq, StateT.run_modify,
              StateT.run_pure, simulateQ_pure, hM₂, tblM₂, bk₂]
          refine Coupled2.eq hL_eq hM_eq (Coupled2.pure ?_)
          refine ⟨rfl, rfl, rfl, rfl, rfl, hM₂, tblM₂, rfl, rfl, hc1, ht1, hs1, hlf1, ?_, ?_⟩
          · intro i hne
            rcases hne1 i hne with ⟨hb_i, ht_i⟩
            exact ⟨by simp [hM₂, Function.update_of_ne hne, hb_i],
                   by simp [tblM₂, Function.update_of_ne hne, ht_i]⟩
          · rw [hrec]
            exact ⟨rfl, rfl, by simpa [hM₂, tblM₂, bk₂, Function.update_self] using hinv₂⟩

private theorem fsRecv_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka M_sess t ep : ℕ) (tL : Option ℕ) (ks : ℕ → BitVec 256)
    (ctxL : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (ctxM : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (hheal : healedBy ctxM.tL (2 + Δcka) t = true)
    (hL : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt)
    (hM : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (rsvL : RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
    (rsvM : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (ssLoc : RatchetSenderState (BitVec 256))
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (recL : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)))
    (recM : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)))
    (hv : (ep ≠ t ∧ ∃ rs, rsvL = (rs, none) ∧ rsvM = .inl rs) ∨
      (ep = t ∧ ∃ rsLoc sIdx,
        rsvL = (rsLoc, some sIdx) ∧ rsvM = .inr sIdx ∧ sIdx < hM.sessions.length ∧
        ActiveSessInv C ℓ encT idOf true (ks sIdx) ssLoc rsLoc
          ((hM.book sIdx).getD {}) (tblM sIdx) (tblL sIdx))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3
      (fun (rL : Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ) ×
              ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × LocalSlotState _ _ _ _)
           (r₀ r₁ : (Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
              ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × FSMultiState _ _ _ _ _) ×
              ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
        (r₁.1.1 = none ∧ r₁.1.2.lfWin = true) ∨
        (rL.2.usedSlot = hL.usedSlot ∧
          rL.2.loc.cache = hL.loc.cache ∧ rL.2.loc.table = hL.loc.table ∧ rL.2.loc.sessions = hL.loc.sessions ∧
          r₁.1.2 = r₀.1.2 ∧
          match rsvL with
          | (rs, none) =>
            ep ≠ t ∧
            match fs.receive rs hdr e with
            | none =>
              rL.1 = some none ∧
              r₀ = ((some none, hM), (fun _ => false, tblM)) ∧
              r₁ = ((some none, hM), (fun _ => false, tblL))
            | some (rs', idxOut, pmOut) =>
              rL.1 = some (some ((rs', none), idxOut, pmOut)) ∧
              r₀ = ((some (some (.inl rs', idxOut, pmOut)), hM), (fun _ => false, tblM)) ∧
              r₁ = ((some (some (.inl rs', idxOut, pmOut)), hM), (fun _ => false, tblL))
          | (rsLoc, some sIdx) =>
            ep = t ∧
            ∃ hM' tblM' tblL',
              r₀ = ((r₀.1.1, hM'), (fun _ => false, tblM')) ∧
              r₁ = ((r₁.1.1, hM'), (fun _ => false, tblL')) ∧
              hM'.cache = hM.cache ∧ hM'.table = hM.table ∧
              hM'.sessions = hM.sessions ∧ hM'.lfWin = hM.lfWin ∧
              (∀ i, i ≠ sIdx → hM'.book i = hM.book i ∧ tblM' i = tblM i ∧ tblL' i = tblL i) ∧
              match fs.receive rsLoc hdr e with
              | none =>
                rL.1 = some none ∧ r₀.1.1 = some none ∧ r₁.1.1 = some none ∧
                ActiveSessInv C ℓ encT idOf true (ks sIdx) ssLoc rsLoc
                  ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL' sIdx)
              | some (rsLoc', idxOut, pmOut) =>
                rL.1 = some (some ((rsLoc', some sIdx), idxOut, pmOut)) ∧
                r₀.1.1 = some (some (.inr sIdx, idxOut, pmOut)) ∧
                r₁.1.1 = some (some (.inr sIdx, idxOut, pmOut)) ∧
                ActiveSessInv C ℓ encT idOf true (ks sIdx) ssLoc rsLoc'
                  ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL' sIdx)))
      (simulateQ (keySlotFixedImpl ks)
        (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep rsvL hdr e recL).run hL))
      ((simulateQ (pubFsMultiImpl implF)
        (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep rsvM hdr e recM).run hM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv ctxM P ep rsvM hdr e recM).run hM)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  rcases hv with ⟨hep, rs, rfl, rfl⟩ | ⟨rfl, rsLoc, sIdx, rfl, rfl, hsIdx_lt, hinv⟩
  · dsimp only [hooksSlotLocal, hooksFSMulti]
    cases hrec : fs.receive rs hdr e with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure, Option.map_none]
      exact Coupled3.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hep, rfl, rfl, rfl⟩)
    | some o =>
      rcases o with ⟨rs', idxOut, pmOut⟩
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure, Option.map_some]
      exact Coupled3.pure (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hep, rfl, rfl, rfl⟩)
  · let bk := (hM.book sIdx).getD {}
    cases hmatch : bk.fsTrans.find? (fun x => x.2 == (hdr, e)) with
    | some mEntry =>
      rcases activeSessInv_deliver C hD signalRoundTripShort_proto ℓ (ell_add_16_lt_rustLenBound hℓ)
        encT idOf hinv hdr e hmatch with ⟨p, hpub, hdeliv⟩
      cases hrec : fs.receive rsLoc hdr e with
      | none =>
        rw [hrec] at hdeliv
        rcases hdeliv with ⟨sM', sL', hdelM, hdelL_fn, hinv'⟩
        have hdelL := hdelL_fn rfl
        let tblM' := Function.update tblM sIdx sM'
        let tblL' := Function.update tblL sIdx sL'
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
            Pure.pure (some none, hL) := by
          dsimp only [hooksSlotLocal]; simp [hrec, StateT.run_pure, simulateQ_pure]
        have h0_eq : ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM)) =
            Pure.pure ((some none, hM), (fun _ => false, tblM')) := by
          dsimp only [hooksFSMulti, implF]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = some mEntry from hmatch,
            Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind,
            Bool.not_true, Option.isSome_some]
          rw [liftFSMulti_deliver_some_eval C encT idOf false sIdx hdr e p hpub hM tblM hdelM]
          simp [map_withPub_rejected, StateT.run_pure, simulateQ_pure, tblM']
        have h1_eq : ((simulateQ (pubFsMultiImpl implT)
            (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblL)) =
            Pure.pure ((some none, hM), (fun _ => false, tblL')) := by
          dsimp only [hooksFSMulti, implT]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = some mEntry from hmatch,
            Option.isNone_some, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind,
            Bool.not_true, Option.isSome_some]
          rw [liftFSMulti_deliver_some_eval C encT idOf true sIdx hdr e p hpub hM tblL hdelL]
          simp [map_withPub_rejected, StateT.run_pure, simulateQ_pure, tblL']
        refine Coupled3.eq hL_eq h0_eq h1_eq (Coupled3.pure (Or.inr ?_))
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hM, tblM', tblL', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · intro i hne; simp [tblM', tblL', Function.update_of_ne hne]
        · rw [hrec]
          exact ⟨rfl, rfl, rfl, by simpa [tblM', tblL', bk, Function.update_self] using hinv'⟩
      | some o =>
        rcases o with ⟨rsLoc', idxOut, pmOut⟩
        rw [hrec] at hdeliv
        rcases hdeliv with ⟨hm1, sM', sL', hdelM, hdelL_fn, hpm1, hinv'⟩
        have hdelL := hdelL_fn rfl
        have hpm_eq : (p, pmOut.2) = pmOut := Prod.ext hpm1.symm rfl
        let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
          { bk with fsTrans := bk.fsTrans.filter (·.1 != mEntry.1) }
        let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
        let tblM' := Function.update tblM sIdx sM'
        let tblL' := Function.update tblL sIdx sL'
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
            Pure.pure (some (some ((rsLoc', some sIdx), idxOut, pmOut)),
              { hL with loc := { hL.loc with lastIdx := some sIdx } }) := by
          dsimp only [hooksSlotLocal]
          simp [hrec, StateT.run_modify, simulateQ_pure]
        have h0_eq : ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM)) =
            Pure.pure ((some (some (.inr sIdx, idxOut, pmOut)), hM'), (fun _ => false, tblM')) := by
          dsimp only [hooksFSMulti, implF]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = some mEntry from hmatch,
            Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind,
            Bool.not_true, Option.isSome_some]
          rw [liftFSMulti_deliver_some_eval C encT idOf false sIdx hdr e p hpub hM tblM hdelM]
          simp [map_withPub_accepted, hpm_eq, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, hM', tblM', bk', bk]
        have h1_eq : ((simulateQ (pubFsMultiImpl implT)
            (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblL)) =
            Pure.pure ((some (some (.inr sIdx, idxOut, pmOut)), hM'), (fun _ => false, tblL')) := by
          dsimp only [hooksFSMulti, implT]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = some mEntry from hmatch,
            Option.isNone_some, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind,
            Bool.not_true, Option.isSome_some]
          rw [liftFSMulti_deliver_some_eval C encT idOf true sIdx hdr e p hpub hM tblL hdelL]
          simp [map_withPub_accepted, hpm_eq, StateT.run_modify, StateT.run_pure,
            simulateQ_pure, hM', tblL', bk', bk]
        refine Coupled3.eq hL_eq h0_eq h1_eq (Coupled3.pure (Or.inr ?_))
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hM', tblM', tblL', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · intro i hne; simp [hM', tblM', tblL', Function.update_of_ne hne]
        · rw [hrec]
          exact ⟨rfl, rfl, rfl, by simpa [hM', tblM', tblL', bk', Function.update_self] using hinv'⟩
    | none =>
      cases hpub : lPubOf protoSignalCodec e.2 with
      | none =>
        have hrec_none : fs.receive rsLoc hdr e = none := by
          dsimp only [fs]; rw [lFS_receive_eq, hpub]
        have hL_eq : simulateQ (keySlotFixedImpl ks)
            (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
            Pure.pure (some none, hL) := by
          dsimp only [hooksSlotLocal]; simp [hrec_none, StateT.run_pure, simulateQ_pure]
        have h0_eq : ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM)) =
            Pure.pure ((some none, hM), (fun _ => false, tblM)) := by
          dsimp only [hooksFSMulti, implF]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
            hheal, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, Option.isSome_none]
          rw [liftFSMulti_inject_none_eval C encT idOf false sIdx hdr e hpub hM tblM]
          simp [StateT.run_pure, simulateQ_pure]
        have h1_eq : ((simulateQ (pubFsMultiImpl implT)
            (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblL)) =
            Pure.pure ((some none, hM), (fun _ => false, tblL)) := by
          dsimp only [hooksFSMulti, implT]
          rw [StateT.run_bind, StateT.run_get]
          simp only [pure_bind, hdr_ct_beq_eq,
            show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
            Option.isNone_none, hheal, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, simulateQ_bind, Option.isSome_none]
          rw [liftFSMulti_inject_none_eval C encT idOf true sIdx hdr e hpub hM tblL]
          simp [StateT.run_pure, simulateQ_pure]
        refine Coupled3.eq hL_eq h0_eq h1_eq (Coupled3.pure (Or.inr ?_))
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hM, tblM, tblL, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ _ => ⟨rfl, rfl, rfl⟩, ?_⟩
        rw [hrec_none]
        exact ⟨rfl, rfl, rfl, hinv⟩
      | some p =>
        rcases activeSessInv_inject_phase1 C ℓ encT idOf hinv hdr e hmatch p hpub with
          ⟨msg, sL', hsc_f, hcnt_lt, hinjL⟩ | hinj2
        · -- Lookahead win on la = true!
          let rL_val : Option (Option ((RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ) ×
              ℕ × (LibsignalMsgPublicPart × Plain ℓ))) × LocalSlotState _ _ _ _ :=
            match fs.receive rsLoc hdr e with
            | none => (some none, hL)
            | some (rs', i, m) =>
              (some (some ((rs', some sIdx), i, m)), { hL with loc := { hL.loc with lastIdx := some sIdx } })
          have hL_eq : simulateQ (keySlotFixedImpl ks)
              (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
              Pure.pure rL_val := by
            dsimp only [hooksSlotLocal, rL_val]
            cases hrec : fs.receive rsLoc hdr e <;>
              simp [StateT.run_modify, StateT.run_pure, simulateQ_pure]
          let tblL' := Function.update tblL sIdx sL'
          have h1_eq : ((simulateQ (pubFsMultiImpl implT)
              (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
              (fun _ => false, tblL)) =
              Pure.pure ((none, { hM with lfWin := true }), (fun _ => false, tblL')) := by
            dsimp only [hooksFSMulti, implT]
            rw [StateT.run_bind, StateT.run_get]
            simp only [pure_bind, hdr_ct_beq_eq,
              show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
              Option.isNone_none, hheal, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, simulateQ_bind, Option.isSome_none]
            rw [liftFSMulti_inject_some_eval C encT idOf true sIdx hdr e p hpub hM tblL hinjL]
            simp [map_withPub_accepted, StateT.run_get, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, hsc_f, hcnt_lt, tblL']
          let m₀ := ((simulateQ (pubFsMultiImpl implF)
            (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
            (fun _ => false, tblM))
          exact Coupled3.eq hL_eq (bind_pure m₀).symm h1_eq
            (Coupled3.bind_dummy_m1 m₀ fun _ => Coupled3.pure (Or.inl ⟨rfl, rfl⟩))
        · cases hrec : fs.receive rsLoc hdr e with
          | none =>
            rw [hrec] at hinj2
            rcases hinj2 with ⟨sM', sL', hinjM, hinjL, hinv'⟩
            let tblM' := Function.update tblM sIdx sM'
            let tblL' := Function.update tblL sIdx sL'
            have hL_eq : simulateQ (keySlotFixedImpl ks)
                (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
                Pure.pure (some none, hL) := by
              dsimp only [hooksSlotLocal]; simp [hrec, StateT.run_pure, simulateQ_pure]
            have h0_eq : ((simulateQ (pubFsMultiImpl implF)
                (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
                (fun _ => false, tblM)) =
                Pure.pure ((some none, hM), (fun _ => false, tblM')) := by
              dsimp only [hooksFSMulti, implF]
              rw [StateT.run_bind, StateT.run_get]
              simp only [pure_bind, hdr_ct_beq_eq,
                show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
                hheal, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, simulateQ_bind, Option.isSome_none]
              rw [liftFSMulti_inject_some_eval C encT idOf false sIdx hdr e p hpub hM tblM hinjM]
              simp [map_withPub_rejected, StateT.run_pure, simulateQ_pure, tblM']
            have h1_eq : ((simulateQ (pubFsMultiImpl implT)
                (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
                (fun _ => false, tblL)) =
                Pure.pure ((some none, hM), (fun _ => false, tblL')) := by
              dsimp only [hooksFSMulti, implT]
              rw [StateT.run_bind, StateT.run_get]
              simp only [pure_bind, hdr_ct_beq_eq,
                show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
                Option.isNone_none, hheal, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, simulateQ_bind, Option.isSome_none]
              rw [liftFSMulti_inject_some_eval C encT idOf true sIdx hdr e p hpub hM tblL hinjL]
              simp [map_withPub_rejected, StateT.run_pure, simulateQ_pure, tblL']
            refine Coupled3.eq hL_eq h0_eq h1_eq (Coupled3.pure (Or.inr ?_))
            refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hM, tblM', tblL', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
            · intro i hne; simp [tblM', tblL', Function.update_of_ne hne]
            · rw [hrec]
              exact ⟨rfl, rfl, rfl, by simpa [tblM', tblL', bk, Function.update_self] using hinv'⟩
          | some o =>
            rcases o with ⟨rsLoc', idxOut, pmOut⟩
            rw [hrec] at hinj2
            rcases hinj2 with ⟨sM', sL', hinjM, hinjL, hcnt_le, hpm1, hinv'⟩
            have hpm_eq : (p, pmOut.2) = pmOut := Prod.ext hpm1.symm rfl
            have hnlf : ¬ (((hM.book sIdx).getD {}).sCorr = false ∧ ((hM.book sIdx).getD {}).fsCount < idxOut) :=
              fun ⟨hsc, hlt⟩ => Nat.not_lt.mpr (hcnt_le hsc) hlt
            let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
              { bk with fsTrans := bk.fsTrans.filter (·.1 != idxOut) }
            let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
            let tblM' := Function.update tblM sIdx sM'
            let tblL' := Function.update tblL sIdx sL'
            have hL_eq : simulateQ (keySlotFixedImpl ks)
                (((hooksSlotLocal cka prng fs mo M_sess).fsRecv ctxL P ep (rsLoc, some sIdx) hdr e recL).run hL) =
                Pure.pure (some (some ((rsLoc', some sIdx), idxOut, pmOut)),
                  { hL with loc := { hL.loc with lastIdx := some sIdx } }) := by
              dsimp only [hooksSlotLocal]
              simp [hrec, StateT.run_modify, simulateQ_pure]
            have h0_eq : ((simulateQ (pubFsMultiImpl implF)
                (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
                (fun _ => false, tblM)) =
                Pure.pure ((some (some (.inr sIdx, idxOut, pmOut)), hM'), (fun _ => false, tblM')) := by
              dsimp only [hooksFSMulti, implF]
              rw [StateT.run_bind, StateT.run_get]
              simp only [pure_bind, hdr_ct_beq_eq,
                show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
                hheal, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, simulateQ_bind, Option.isSome_none]
              rw [liftFSMulti_inject_some_eval C encT idOf false sIdx hdr e p hpub hM tblM hinjM]
              simp [map_withPub_accepted, hpm_eq, StateT.run_map, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, hM', tblM', bk', bk]
            have h1_eq : ((simulateQ (pubFsMultiImpl implT)
                (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv ctxM P ep (.inr sIdx) hdr e recM).run hM)).run
                (fun _ => false, tblL)) =
                Pure.pure ((some (some (.inr sIdx, idxOut, pmOut)), hM'), (fun _ => false, tblL')) := by
              dsimp only [hooksFSMulti, implT]
              rw [StateT.run_bind, StateT.run_get]
              simp only [pure_bind, hdr_ct_beq_eq,
                show ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) = none from hmatch,
                Option.isNone_none, hheal, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, simulateQ_bind, Option.isSome_none]
              rw [liftFSMulti_inject_some_eval C encT idOf true sIdx hdr e p hpub hM tblL hinjL]
              simp [map_withPub_accepted, hpm_eq, StateT.run_get, StateT.run_map, StateT.run_modify, StateT.run_pure,
                simulateQ_pure,
                hnlf, hM', tblL', bk', bk]
            refine Coupled3.eq hL_eq h0_eq h1_eq (Coupled3.pure (Or.inr ?_))
            refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hM', tblM', tblL', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
            · intro i hne; simp [hM', tblM', tblL', Function.update_of_ne hne]
            · rw [hrec]
              exact ⟨rfl, rfl, rfl, by simpa [hM', tblM', tblL', bk', Function.update_self] using hinv'⟩

-- End of base slice

/-! ### 7B. `vSend` and `transmitE` Step Couplings -/

private theorem epMgmt_sendsIn_true {St Msg C : Type} {g s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hs : P.sendsIn (g.epoch P + 1) = true)
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁.epoch = Function.update g.epoch P (g.epoch P + 1) := by
  unfold GameState.epMgmt at hep
  simp only [hs, ↓reduceIte] at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep <;> subst hep <;> rfl

private theorem epMgmt_sendsIn_false {St Msg C : Type} {g s₁ : GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hs : P.sendsIn (g.epoch P + 1) = false)
    (hep : g.epMgmt Δ qep P bad = some s₁) :
    s₁ = g := by
  unfold GameState.epMgmt at hep
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
  split_ifs at hep
  simp only [Option.some.injEq] at hep
  exact hep.symm

private theorem eraseSt_record_eq {St₁ St₂ Msg C : Type}
    {s₁ : GameState St₁ Msg C} {s₂ : GameState St₂ Msg C}
    (h : eraseSt s₁ = eraseSt s₂) (Δ : ℕ) (P : Party) (st₁ : St₁) (st₂ : St₂)
    (r : Record Msg C) (isChall : Bool) :
    eraseSt (s₁.record Δ P st₁ r isChall) = eraseSt (s₂.record Δ P st₂ r isChall) := by
  cases s₁; cases s₂
  dsimp only [eraseSt] at h
  injection h
  subst_vars
  rfl

private theorem sampleOptCoins_coupled3 {Pt Sig : Type} {ℓ : ℕ}
    {impl₀ impl₁ : QueryImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (SessHSt Pt ℓ) ProbComp)}
    (ks : ℕ → BitVec 256)
    (r : Option (BitVec 256))
    (hL : LocalSlotState Pt Sig (BitVec 256) Pt)
    (hM : FSMultiState Pt Sig (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (s₀ s₁ : (ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) :
    Coupled3
      (fun (rL : BitVec 256 × LocalSlotState Pt Sig (BitVec 256) Pt)
           (r₀ r₁ : (BitVec 256 × FSMultiState Pt Sig (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
             ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) =>
        r₀.1.1 = rL.1 ∧ r₁.1.1 = rL.1 ∧
        rL.2 = hL ∧ r₀.1.2 = hM ∧ r₁.1.2 = hM ∧ r₀.2 = s₀ ∧ r₁.2 = s₁)
      (simulateQ (keySlotFixedImpl ks)
        ((match r with | some c => pure c | none => StateT.lift (sampleT (BitVec 256))).run hL))
      ((simulateQ (pubFsMultiImpl impl₀)
        ((match r with
          | some c => pure c
          | none => StateT.lift (sampleT (tspec := FSMultiSpec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt (LibsignalMsgPublicPart × Plain ℓ)
              (ℕ × LibsignalCiphertextWithSalt32)) (BitVec 256))).run hM)).run s₀)
      ((simulateQ (pubFsMultiImpl impl₁)
        ((match r with
          | some c => pure c
          | none => StateT.lift (sampleT (tspec := FSMultiSpec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt (LibsignalMsgPublicPart × Plain ℓ)
              (ℕ × LibsignalCiphertextWithSalt32)) (BitVec 256))).run hM)).run s₁) := by
  cases r with
  | some c =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact Coupled3.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | none =>
    simp only [StateT.run_lift]
    rw [simulateQ_keySlotFixedImpl_sampleT, run_pubFsMultiImpl_sampleT, run_pubFsMultiImpl_sampleT]
    simp only [simulateQ_pure, StateT.run_pure]
    exact Coupled3.bind_same ($ᵗ (BitVec 256)) fun c =>
      Coupled3.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem hooksSlotLocal_startSend_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt] {ℓ : ℕ}
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG CryptoGames.Ratchet.RootKey CryptoGames.Ratchet.RootKey Pt CryptoGames.Ratchet.ChainKey)
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (mo : Mode) (M_sess : ℕ)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ)
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σ : CryptoGames.Ratchet.RootKey)
    (r : Option (BitVec 256)) :
    (hooksSlotLocal cka prng fs mo M_sess).startSend ctx P ep γ σ r =
    ((match r with
      | some c => pure c
      | none => StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec (BitVec 256))) (BitVec 256))) >>=
      fun coins => (hooksSlotLocal cka prng fs mo M_sess).startSend ctx P ep γ σ (some coins)) := by
  cases r <;> (dsimp only [hooksSlotLocal]; simp only [pure_bind])

private theorem hooksFSMulti_startSend_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt] {ℓ : ℕ}
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG CryptoGames.Ratchet.RootKey CryptoGames.Ratchet.RootKey Pt CryptoGames.Ratchet.ChainKey)
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ)
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σ : CryptoGames.Ratchet.RootKey)
    (r : Option (BitVec 256)) :
    (hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P ep γ σ r =
    ((match r with
      | some c => pure c
      | none => StateT.lift (sampleT (tspec := FSMultiSpec (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt (LibsignalMsgPublicPart × Plain ℓ)
          (ℕ × LibsignalCiphertextWithSalt32)) (BitVec 256))) >>=
      fun coins => (hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P ep γ σ (some coins)) := by
  cases r <;> (dsimp only [hooksFSMulti]; simp only [pure_bind])

private theorem fsSend_inr_phase2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka : ℕ) (mo : Mode)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (sIdx : ℕ)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hM₁ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM₁ tblL₁ : ℕ → SessHSt Pt ℓ)
    (hinv : ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc ((hM₁.book sIdx).getD {}) (tblM₁ sIdx) (tblL₁ sIdx))
    (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ) (hshort : pm.1.shortB = true) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let o := fs.send ssLoc hdr pm
    ∃ bk_sIdx sM' sL',
      (simulateQ (pubFsMultiImpl implF)
        (((hooksFSMulti cka prng fs Δcka mo false false).fsSend ctx P ep (.inr sIdx) hdr pm none).run hM₁)).run
        (fun _ => false, tblM₁) =
      Pure.pure ((some (.inr sIdx, o.2), { hM₁ with book := Function.update hM₁.book sIdx (some bk_sIdx) }),
        (fun _ => false, Function.update tblM₁ sIdx sM')) ∧
      ActiveSessInv C ℓ encT idOf false k o.1 rsLoc bk_sIdx sM' sL' := by
  intro cka prng fs implF o
  dsimp only [hooksFSMulti]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcs_cond : (!(ctx.safeCh (2 + Δcka) P) && !((hM₁.book sIdx).getD {}).sCorr) = true
  · simp only [hcs_cond, ↓reduceIte, Bool.false_eq_true, StateT.run_bind, simulateQ_bind]
    rcases activeSessInv_corruptSender C ℓ encT idOf hinv with ⟨sM_cs, hcs_eval, hinv_cs⟩
    let bk0 := (hM₁.book sIdx).getD {}
    let bk_cs : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) := { bk0 with sCorr := true }
    let hM_cs := { hM₁ with book := Function.update hM₁.book sIdx (some bk_cs) }
    let tblM_cs := Function.update tblM₁ sIdx sM_cs
    have hinv_cs' : ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc
        ((hM_cs.book sIdx).getD {}) (tblM_cs sIdx) (tblL₁ sIdx) := by
      dsimp only [hM_cs, tblM_cs, bk_cs, bk0]
      rw [Function.update_self, Function.update_self]
      exact hinv_cs
    rcases activeSessInv_transmit C signalRoundTripShort_proto ℓ
        (ell_add_16_lt_rustLenBound hℓ) encT idOf hinv_cs' hdr pm hshort with
      ⟨sM', sL', htx_eval, _, hinv_tx⟩
    let cnt' := ((hM_cs.book sIdx).getD {}).fsCount + 1
    let bk_sIdx : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
      { (hM_cs.book sIdx).getD {} with fsCount := cnt', fsTrans := (cnt', hdr, o.2) :: ((hM_cs.book sIdx).getD {}).fsTrans }
    refine ⟨bk_sIdx, sM', sL', ?_, hinv_tx⟩
    rw [liftFSMulti_corruptSender_eval C encT idOf sIdx hM₁ tblM₁ hcs_eval]
    simp only [pure_bind, StateT.run_bind, StateT.run_modify,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
    change ((simulateQ (pubFsMultiImpl implF)
        ((liftFSMulti sIdx (transmitQuery hdr pm)).run hM_cs)).run (fun _ => false, tblM_cs)) >>= _ = _
    rw [liftFSMulti_transmit_eval C encT idOf false sIdx hdr pm hM_cs tblM_cs htx_eval]
    simp [o, fs, hM_cs, tblM_cs, bk_cs, bk0, bk_sIdx, cnt', Function.update_idem,
      StateT.run_modify, StateT.run_pure, simulateQ_pure]
  · simp only [hcs_cond, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
      StateT.run_bind, simulateQ_bind]
    rcases activeSessInv_transmit C signalRoundTripShort_proto ℓ
        (ell_add_16_lt_rustLenBound hℓ) encT idOf hinv hdr pm hshort with
      ⟨sM', sL', htx_eval, _, hinv_tx⟩
    let bk0 := (hM₁.book sIdx).getD {}
    let cnt' := bk0.fsCount + 1
    let bk_sIdx : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
      { bk0 with fsCount := cnt', fsTrans := (cnt', hdr, o.2) :: bk0.fsTrans }
    refine ⟨bk_sIdx, sM', sL', ?_, hinv_tx⟩
    rw [liftFSMulti_transmit_eval C encT idOf false sIdx hdr pm hM₁ tblM₁ htx_eval]
    simp [o, fs, bk0, bk_sIdx, cnt', StateT.run_modify, StateT.run_pure, simulateQ_pure]

private theorem fsSend_inr_phase1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka : ℕ) (mo : Mode)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (sIdx : ℕ)
    (hsafe : ctx.safeCh (2 + Δcka) P = true)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hM₁ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM₁ tblL₁ : ℕ → SessHSt Pt ℓ)
    (hinv : ActiveSessInv C ℓ encT idOf true k ssLoc rsLoc ((hM₁.book sIdx).getD {}) (tblM₁ sIdx) (tblL₁ sIdx))
    (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ) (hshort : pm.1.shortB = true) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    let o := fs.send ssLoc hdr pm
    ∃ bk_sIdx sM' sL',
      (simulateQ (pubFsMultiImpl implF)
        (((hooksFSMulti cka prng fs Δcka mo false false).fsSend ctx P ep (.inr sIdx) hdr pm none).run hM₁)).run
        (fun _ => false, tblM₁) =
      Pure.pure ((some (.inr sIdx, o.2), { hM₁ with book := Function.update hM₁.book sIdx (some bk_sIdx) }),
        (fun _ => false, Function.update tblM₁ sIdx sM')) ∧
      (simulateQ (pubFsMultiImpl implT)
        (((hooksFSMulti cka prng fs Δcka mo false true).fsSend ctx P ep (.inr sIdx) hdr pm none).run hM₁)).run
        (fun _ => false, tblL₁) =
      Pure.pure ((some (.inr sIdx, o.2), { hM₁ with book := Function.update hM₁.book sIdx (some bk_sIdx) }),
        (fun _ => false, Function.update tblL₁ sIdx sL')) ∧
      ActiveSessInv C ℓ encT idOf true k o.1 rsLoc bk_sIdx sM' sL' := by
  intro cka prng fs implF implT o
  rcases activeSessInv_transmit C signalRoundTripShort_proto ℓ
      (ell_add_16_lt_rustLenBound hℓ) encT idOf hinv hdr pm hshort with
    ⟨sM', sL', htxM, htxL_fn, hinv_tx⟩
  have htxL := htxL_fn rfl
  let bk0 := (hM₁.book sIdx).getD {}
  let cnt' := bk0.fsCount + 1
  let bk_sIdx : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
    { bk0 with fsCount := cnt', fsTrans := (cnt', hdr, o.2) :: bk0.fsTrans }
  refine ⟨bk_sIdx, sM', sL', ?_, ?_, hinv_tx⟩
  · dsimp only [hooksFSMulti]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hsafe, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
    rw [liftFSMulti_transmit_eval C encT idOf false sIdx hdr pm hM₁ tblM₁ htxM]
    simp [o, fs, bk0, bk_sIdx, cnt', StateT.run_modify, StateT.run_pure, simulateQ_pure]
  · dsimp only [hooksFSMulti]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hsafe, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
    rw [liftFSMulti_transmit_eval C encT idOf true sIdx hdr pm hM₁ tblL₁ htxL]
    simp [o, fs, bk0, bk_sIdx, cnt', StateT.run_modify, StateT.run_pure, simulateQ_pure]

private theorem hbook_after_reg_at_t {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem esL esM tblM tblL)
    (htcur_lt : (esL.g.st (Party.senderOf t)).tcur < t)
    {hM₁ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    (hbook_eq : hM₁.book = esM.h.book)
    (hsess_le : esM.h.sessions.length ≤ hM₁.sessions.length) :
    (∀ i, hM₁.sessions.length ≤ i →
      hM₁.book i = none ∧ tblM i = hInit (bs i) (.seed (ks i)) ∧
        (phase1 = true → tblL i = hInit (bs i) (.seed (ks i)))) ∧
    (∀ i, i < hM₁.sessions.length →
      let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
      let rs_i := match (esL.g.st (Party.receiverOf t)).vR t with
        | some (rs, some j) => if j = i then rs else fs.initReceiver (ks i)
        | _ => fs.initReceiver (ks i)
      ActiveSessInv C ℓ encT idOf phase1 (ks i) (fs.initSender (ks i)) rs_i
        ((hM₁.book i).getD {}) (tblM i) (tblL i)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hbook_eq]
    exact hsync.hbook_out i (Nat.le_trans hsess_le hi)
  · intro fs rs_i
    rw [hbook_eq]
    by_cases hi_old : i < esM.h.sessions.length
    · rcases hsync.hbook_in i hi_old with ⟨ss_i, hinv, hss1, _⟩
      rw [hss1 htcur_lt] at hinv
      exact hinv
    · have hi_ge : esM.h.sessions.length ≤ i := by omega
      rcases hsync.hbook_out i hi_ge with ⟨hb_none, htblM_i, htblL_i⟩
      have hrs_eq : rs_i = fs.initReceiver (ks i) := by
        dsimp only [rs_i]
        have hv := hsync.hvR_eq (Party.receiverOf t)
        cases hP : (esL.g.st (Party.receiverOf t)).vR t with
        | none => rfl
        | some ro =>
          rcases ro with ⟨rs, optJ⟩
          rw [hP] at hv
          rcases hv with ⟨j, rfl, _, hj_lt, _, _⟩
          have hj_ne : j ≠ i := by omega
          simp [hj_ne]
      rw [hrs_eq, hb_none, Option.getD_none, htblM_i]
      have hinit1 := activeSessInv_init C ℓ encT idOf true (ks i) (bs i)
      cases phase1
      · exact activeSessInv_to_phase2 C ℓ encT idOf hinit1
      · rw [htblL_i rfl]; exact hinit1

private theorem syncPaperMulti_after_record {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 phase1' : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL tblM' tblL' : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 (rem + 1) esL esM tblM tblL)
    {P : Party} {m : LibsignalMsgPublicPart × Plain ℓ}
    {s₁L : GameState _ (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)}
    {s₁M : GameState _ (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)}
    (herase1 : eraseSt s₁L = eraseSt s₁M)
    (hs₁_stL : s₁L.st = esL.g.st) (hs₁_stM : s₁M.st = esM.g.st)
    (hs₁_winL : s₁L.win = false) (hs₁_winM : s₁M.win = false)
    (hs₁_bL : s₁L.b = false) (hs₁_bM : s₁M.b = false)
    (hs₁_trans : s₁L.trans = esL.g.trans)
    (hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q)
    (hs₁_ep_mono : esL.g.epoch P ≤ s₁L.epoch P)
    {stL' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)}
    {stM' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)}
    {ct : Header Pt × ℕ × LibsignalCiphertextWithSalt32}
    {hL' : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt}
    {hM' : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    (hct_ep : ct.1.1 = s₁L.epoch P)
    (hst_id : stL'.id = P ∧ stM'.id = P)
    (hst_tcur : stL'.tcur = s₁L.epoch P ∧ stM'.tcur = s₁L.epoch P)
    (hst_γ : stM'.γ = stL'.γ)
    (hst_root : stM'.root = stL'.root)
    (hst_cka : stM'.curCkaMsg = stL'.curCkaMsg)
    (hst_vR : stL'.vR = (esL.g.st P).vR ∧ stM'.vR = (esM.g.st P).vR)
    (hst_vS :
      match stL'.vS with
      | none => stM'.vS = none
      | some (ss, none) => stM'.vS = some (.inl ss)
      | some (_, some sIdx) =>
        stM'.vS = some (.inr sIdx) ∧ sIdx < hM'.sessions.length ∧
          P = Party.senderOf t ∧ t ≤ stL'.tcur)
    (hsess_le : esM.h.sessions.length ≤ hM'.sessions.length)
    (hlf' : phase1' = true → hM'.lfWin = false)
    (hhealed' : phase1' = false → healedBy s₁L.tL (2 + Δcka) t = false)
    (hbk' : HookBookInv M_sess t tL ks rem hL' hM')
    (htH_empty' : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = true →
      (Function.update esL.g.st P stL' (Party.senderOf t)).tcur < t →
      hL'.loc.sessions = [])
    (hcache_ne' : ∀ ep, ep ≠ t →
      match hL'.loc.cache ep with
      | none => hM'.cache ep = none
      | some (Tc, σc, k, idx?) => idx? = none ∧ hM'.cache ep = some (Tc, σc, k, none))
    (hcache_lt' : (Function.update esL.g.st P stL' (Party.senderOf t)).tcur < t →
      hL'.loc.cache t = none ∧ hM'.cache t = none)
    (hcache_eq' :
      match hL'.loc.cache t with
      | none => hM'.cache t = none
      | some (Tc, σc, k, idx?) =>
        ∃ sIdx kM, idx? = some sIdx ∧ k = ks sIdx ∧ sIdx < hM'.sessions.length ∧
          hM'.cache t = some (Tc, σc, kM, some sIdx))
    (hbook_out' : ∀ i, hM'.sessions.length ≤ i →
      hM'.book i = none ∧ tblM' i = hInit (bs i) (.seed (ks i)) ∧
        (phase1' = true → tblL' i = hInit (bs i) (.seed (ks i))))
    (hbook_in' : ∀ i, i < hM'.sessions.length →
      let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
      let rs_i := match (esL.g.st (Party.receiverOf t)).vR t with
        | some (rs, some j) => if j = i then rs else fs.initReceiver (ks i)
        | _ => fs.initReceiver (ks i)
      ∃ ss_i,
        ActiveSessInv C ℓ encT idOf phase1' (ks i) ss_i rs_i
          ((hM'.book i).getD {}) (tblM' i) (tblL' i) ∧
        ((Function.update esL.g.st P stL' (Party.senderOf t)).tcur < t → ss_i = fs.initSender (ks i)) ∧
        (∀ Q ss, (Function.update esL.g.st P stL' Q).vS = some (ss, some i) → ss_i = ss)) :
    let recL : Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32) :=
      ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, ct⟩
    let recM : Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32) :=
      ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ct⟩
    SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1' rem
      { esL with g := s₁L.record (2 + Δcka) P stL' recL false, h := hL' }
      { esM with g := s₁M.record (2 + Δcka) P stM' recM false, h := hM' }
      tblM' tblL' := by
  intro recL recM
  have hep_eq : s₁L.epoch = s₁M.epoch := congrArg GameState.epoch herase1
  have hidx_eq : s₁L.idx = s₁M.idx := congrArg GameState.idx herase1
  have hrec_eq : recM = recL := by dsimp [recL, recM]; rw [hep_eq, hidx_eq]
  have hvR_stL : ∀ Q, (Function.update s₁L.st P stL' Q).vR = (esL.g.st Q).vR := by
    intro Q; rw [hs₁_stL]; by_cases hQ : Q = P
    · subst hQ; simp [hst_vR.1]
    · simp [hQ]
  have hvR_stM : ∀ Q, (Function.update s₁M.st P stM' Q).vR = (esM.g.st Q).vR := by
    intro Q; rw [hs₁_stM]; by_cases hQ : Q = P
    · subst hQ; simp [hst_vR.2]
    · simp [hQ]
  have htcur_mono : ∀ Q, (esL.g.st Q).tcur ≤ (Function.update s₁L.st P stL' Q).tcur := by
    intro Q; rw [hs₁_stL]; by_cases hQ : Q = P
    · subst hQ; simp only [Function.update_self, hst_tcur.1, hsync.htcurL Q]; exact hs₁_ep_mono
    · simp [hQ]
  refine
    { habL := hsync.habL, habM := hsync.habM
      hwinL := hs₁_winL, hwinM := hs₁_winM
      hbL := hs₁_bL, hbM := hs₁_bM
      herase := by
        rw [hrec_eq]
        exact eraseSt_record_eq herase1 (2 + Δcka) P stL' stM' recL false
      htrans_ep := fun r hr => by
        dsimp only [GameState.record] at hr
        rcases List.mem_cons.mp hr with rfl | hmem
        · exact hct_ep.symm
        · rw [hs₁_trans] at hmem; exact hsync.htrans_ep r hmem
      hlf := hlf'
      hhealed := hhealed'
      hidL := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stL]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_id.1]
        · simp [hQ, hsync.hidL Q]
      hidM := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stM]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_id.2]
        · simp [hQ, hsync.hidM Q]
      htcurL := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stL]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_tcur.1]
        · simp [hQ, hsync.htcurL Q, hs₁_ep_other Q hQ]
      htcurM := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_tcur.1, hst_tcur.2]
        · simp [hQ, hsync.htcurM Q]
      hγ := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_γ]
        · simp [hQ, hsync.hγ Q]
      hroot := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_root]
        · simp [hQ, hsync.hroot Q]
      hckaMsg := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_cka]
        · simp [hQ, hsync.hckaMsg Q]
      hvS := fun Q => by
        dsimp [GameState.record]; rw [hs₁_stL, hs₁_stM]
        by_cases hQ : Q = P
        · subst hQ; simpa using hst_vS
        · simp only [Function.update_of_ne hQ]
          have hv := hsync.hvS Q
          cases hQ_vS : (esL.g.st Q).vS with
          | none => rw [hQ_vS] at hv; exact hv
          | some so =>
            rcases so with ⟨ss, optIdx⟩
            cases optIdx with
            | none => rw [hQ_vS] at hv; exact hv
            | some sIdx =>
              rw [hQ_vS] at hv
              rcases hv with ⟨hvM, hlt, hPs, hle⟩
              exact ⟨hvM, Nat.lt_of_lt_of_le hlt hsess_le, hPs, hle⟩
      hvR_hi := fun Q ep hhi => by
        dsimp [GameState.record]
        rw [hvR_stL Q, hvR_stM Q]
        apply hsync.hvR_hi Q ep
        rcases hhi with hlt | hs
        · exact Or.inl (Nat.lt_of_le_of_lt (htcur_mono Q) hlt)
        · exact Or.inr hs
      hvR_ne := fun Q ep hne => by
        dsimp [GameState.record]
        rw [hvR_stL Q, hvR_stM Q]
        exact hsync.hvR_ne Q ep hne
      hvR_eq := fun Q => by
        dsimp [GameState.record]
        rw [hvR_stL Q, hvR_stM Q]
        have hv := hsync.hvR_eq Q
        cases hQ_vR : (esL.g.st Q).vR t with
        | none => rw [hQ_vR] at hv; exact hv
        | some ro =>
          rw [hQ_vR] at hv
          rcases hv with ⟨sIdx, hopt, hvM, hlt, hle, hPr⟩
          exact ⟨sIdx, hopt, hvM, Nat.lt_of_lt_of_le hlt hsess_le,
            Nat.le_trans hle (htcur_mono Q), hPr⟩
      hsess := hbk'.hsess
      hnodup := hbk'.hnodup
      hlen := hbk'.hlen
      hused := hbk'.hused
      htH_empty := fun htH hlt => by
        dsimp [GameState.record] at hlt; rw [hs₁_stL] at hlt
        exact htH_empty' htH hlt
      htblL_lk := hbk'.htblL_lk
      htblM_lk := hbk'.htblM_lk
      hcache_ne := hcache_ne'
      hcache_lt := fun hlt => by
        dsimp [GameState.record] at hlt; rw [hs₁_stL] at hlt
        exact hcache_lt' hlt
      hcache_eq := hcache_eq'
      hbook_out := hbook_out'
      hbook_in := fun i hi => by
        dsimp [GameState.record]
        rw [hvR_stL (Party.receiverOf t), hs₁_stL]
        exact hbook_in' i hi }


private theorem hooksSlotLocal_startSend_some_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt] {ℓ : ℕ}
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG CryptoGames.Ratchet.RootKey CryptoGames.Ratchet.RootKey Pt CryptoGames.Ratchet.ChainKey)
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (mo : Mode) (M_sess : ℕ)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ)
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σ : CryptoGames.Ratchet.RootKey)
    (coins : BitVec 256) :
    (hooksSlotLocal cka prng fs mo M_sess).startSend ctx P ep γ σ (some coins) =
    ((do let (σ', k, sid) ← rootSlotL prng mo M_sess ep (cka.send γ coins).2.2 σ
         let idx? ← regSessOfSlot sid
         return (σ', k, idx?)) >>= fun ⟨σ', k, idx?⟩ => do
      modify fun s => { s with loc := { s.loc with cache := Function.update s.loc.cache ep (some ((cka.send γ coins).2.1, σ', k, idx?)) } }
      return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ', (fs.initSender k, idx?))) := by
  dsimp only [hooksSlotLocal]
  simp only [pure_bind, bind_assoc]

private theorem hooksFSMulti_startSend_some_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt] {ℓ : ℕ}
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG CryptoGames.Ratchet.RootKey CryptoGames.Ratchet.RootKey Pt CryptoGames.Ratchet.ChainKey)
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ)
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σ : CryptoGames.Ratchet.RootKey)
    (coins : BitVec 256) :
    (hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P ep γ σ (some coins) =
    ((do let (σ', k, sid) ← rootFSMulti prng mo ep (cka.send γ coins).2.2 σ
         let idx? ← regSessOptMulti sid
         return (σ', k, idx?)) >>= fun ⟨σ', k, idx?⟩ => do
      modify fun s => { s with cache := Function.update s.cache ep (some ((cka.send γ coins).2.1, σ', k, idx?)) }
      return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ',
        match idx? with | none => .inl (fs.initSender k) | some sIdx => .inr sIdx)) := by
  dsimp only [hooksFSMulti]
  simp only [pure_bind, bind_assoc]; rfl
private theorem transmitE_coupled_phase2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {phase1 : Bool} {rem : ℕ}
    (qry : Party × (LibsignalMsgPublicPart × Plain ℓ) × Option (BitVec 256))
    (hshort : qry.2.1.1.shortB = true)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 (rem + 1) esL esM tblM tblL)
    (hheal_none : esL.g.epMgmt (2 + Δcka) qep qry.1 qry.2.2.isSome = none →
      healedBy esL.g.tL (2 + Δcka) t = false)
    (hheal_some : ∀ s₁L, esL.g.epMgmt (2 + Δcka) qep qry.1 qry.2.2.isSome = some s₁L →
      (⟨true, tL, t⟩ : Mode).policy.leakDoom esL.g s₁L = false →
      healedBy s₁L.tL (2 + Δcka) t = false) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (StepPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((transmitE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.policy qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((transmitE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.policy qry).run esM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  rcases qry with ⟨P, m, r⟩
  dsimp only at hshort hheal_none hheal_some
  unfold transmitE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habL, hsync.habM,
    hsync.hwinL, hsync.hwinM, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  have hep_sync := eraseSt_epMgmt_sync hsync.herase (2 + Δcka) qep P r.isSome
  cases hepL : esL.g.epMgmt (2 + Δcka) qep P r.isSome with
  | none =>
    rw [hepL, Option.map_none] at hep_sync
    have hepM : esM.g.epMgmt (2 + Δcka) qep P r.isSome = none :=
      Option.map_eq_none_iff.mp hep_sync.symm
    simp only [hepM, StateT.run_pure, simulateQ_pure]
    exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, hqep,
      { (hsync.mono_rem (Nat.le_succ rem)) with
        hlf := fun h => Bool.noConfusion h
        hhealed := fun _ => hheal_none hepL
        hbook_out := fun i hi =>
          let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
          ⟨hb, hm, fun h => Bool.noConfusion h⟩
        hbook_in := fun i hi =>
          let ⟨ss_i, hinv, hss1, hss2⟩ := hsync.hbook_in i hi
          ⟨ss_i, (by cases phase1; exact hinv; exact activeSessInv_to_phase2 C ℓ encT idOf hinv),
            hss1, hss2⟩ }⟩⟩)
  | some s₁L =>
    rw [hepL, Option.map_some] at hep_sync
    rcases Option.map_eq_some_iff.mp hep_sync.symm with ⟨s₁M, hepM, herase1'⟩
    have herase1 : eraseSt s₁L = eraseSt s₁M := herase1'.symm
    simp only [hepM]
    have hdoom_eq : mo.policy.leakDoom esL.g s₁L = mo.policy.leakDoom esM.g s₁M :=
      _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_leakDoom hsync.herase herase1 mo.policy
    by_cases hdoom : mo.policy.leakDoom esL.g s₁L = true
    · have hdoomM : mo.policy.leakDoom esM.g s₁M = true := hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify,
        pure_bind, StateT.run_pure, simulateQ_pure]
      exact Coupled2.pure (Or.inl rfl)
    · simp only [Bool.not_eq_true] at hdoom
      have hdoomM : mo.policy.leakDoom esM.g s₁M = false := hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, Bool.false_eq_true, ↓reduceIte]
      have hheal1 := hheal_some s₁L hepL hdoom
      have hs₁_stL := epMgmt_st_eq_of_some hepL
      have hs₁_stM := epMgmt_st_eq_of_some hepM
      have hs₁_winL := (epMgmt_win_eq_of_some hepL).trans hsync.hwinL
      have hs₁_winM := (epMgmt_win_eq_of_some hepM).trans hsync.hwinM
      have hs₁_bL := (epMgmt_b_eq_of_some hepL).trans hsync.hbL
      have hs₁_bM := (epMgmt_b_eq_of_some hepM).trans hsync.hbM
      have hs₁_trans := epMgmt_trans_eq_of_some hepL
      unfold vSend
      simp only [hs₁_stL, hs₁_stM, hsync.hidL P, hsync.hidM P, hsync.htcurM P, hsync.htcurL P,
        hsync.hγ P, hsync.hroot P]
      by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
      · have hs₁_ep := epMgmt_sendsIn_true hsends hepL
        have hep'_eq : esL.g.epoch P + 1 = s₁L.epoch P := by
          rw [hs₁_ep, Function.update_self]
        have hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q := by
          intro Q hQ; rw [hs₁_ep, Function.update_of_ne hQ]
        have hs₁_ep_mono : esL.g.epoch P ≤ s₁L.epoch P := by omega
        simp only [hsends, ↓reduceIte]
        rw [hooksSlotLocal_startSend_eq, hooksFSMulti_startSend_eq]
        simp only [StateT.run_bind, liftH_run, simulateQ_bind, bind_assoc]
        refine Coupled2.bind
          ((sampleOptCoins_coupled3 (impl₀ := implF) (impl₁ := implF) ks r esL.h esM.h
            (fun _ => false, tblM) (fun _ => false, tblM)).to_coupled2) ?_
        rintro ⟨coins, hL0⟩ ⟨⟨coinsM, hM0⟩, s0⟩ ⟨_, hcoinsM, _, rfl, rfl, _, rfl, _⟩
        dsimp only at hcoinsM; subst coinsM
        dsimp only
        let cc := cka.send (esL.g.st P).γ coins
        let ep' := esL.g.epoch P + 1
        have hempty_arg : ep' = t → (tL.isSome && decide (t = mo.tH)) = true →
            esL.h.loc.sessions = [] := by
          intro hep_t htH
          have hPs : P = Party.senderOf t := by
            apply party_eq_senderOf_of_sendsIn_true
            simpa [ep', hep_t] using hsends
          apply hsync.htH_empty htH
          rw [← hPs, hsync.htcurL P]
          omega
        refine Coupled2.eq
          (by rw [hooksSlotLocal_startSend_some_eq, StateT.run_bind, simulateQ_bind, bind_assoc])
          (by rw [hooksFSMulti_startSend_some_eq, StateT.run_bind, simulateQ_bind, StateT.run_bind, bind_assoc]) ?_
        refine Coupled2.bind
          ((root_regSessOpt_coupled (impl₀ := implF) (impl₁ := implF) (s₀ := (fun _ => false, tblM))
            (s₁ := (fun _ => false, tblM)) prng hsync.hookBookInv hempty_arg cc.2.2 (esL.g.st P).root).to_coupled2) ?_
        rintro ⟨⟨σ', kL, idxL⟩, hL₁⟩ ⟨⟨⟨σM', kM, idxM⟩, hM₁⟩, s₁_st⟩
          ⟨_, _, rfl, _, hbk', hcacheL_eq, hcacheM_eq, hbookM_eq, hlfM_eq, ⟨J, hsess_step⟩, hsplit⟩
        have hsess_le : esM.h.sessions.length ≤ hM₁.sessions.length := by
          rcases hsess_step with h | h <;> rw [h] <;> simp
        by_cases hep_t : ep' = t
        · simp only [hep_t, ↓reduceIte] at hsplit
          dsimp only [ep'] at hep_t
          rcases hsplit with ⟨sIdx, σ_out, kM_out, hrL, hrM, _, hsIdx_lt⟩
          rcases Prod.mk.inj hrL with ⟨hσL, hrL2⟩; rcases Prod.mk.inj hrL2 with ⟨hkL, hidxL⟩
          rcases Prod.mk.inj hrM with ⟨hσM, hrM2⟩; rcases Prod.mk.inj hrM2 with ⟨hkM, hidxM⟩
          subst σ' kL idxL σM' kM idxM
          have hPs : P = Party.senderOf t := by
            apply party_eq_senderOf_of_sendsIn_true
            simpa [hep_t] using hsends
          have htcur_lt : (esL.g.st (Party.senderOf t)).tcur < t := by
            rw [← hPs, hsync.htcurL P]; omega
          have ⟨hbook_out1, hbook_in1⟩ := hbook_after_reg_at_t hsync htcur_lt hbookM_eq hsess_le
          let hL₂ : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt :=
            { hL₁ with loc := { hL₁.loc with cache := Function.update hL₁.loc.cache t (some (cc.2.1, σ_out, ks sIdx, some sIdx)) } }
          let hM₂ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { hM₁ with cache := Function.update hM₁.cache t (some (cc.2.1, σ_out, kM_out, some sIdx)) }
          let hdr : Header Pt := (t, some cc.2.1)
          have hinv_sIdx : ActiveSessInv C ℓ encT idOf false (ks sIdx) (fs.initSender (ks sIdx))
              (match (esL.g.st (Party.receiverOf t)).vR t with
                | some (rs, some j) => if j = sIdx then rs else fs.initReceiver (ks sIdx)
                | _ => fs.initReceiver (ks sIdx))
              ((hM₂.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) := by
            have h0 := hbook_in1 sIdx hsIdx_lt
            cases phase1
            · exact h0
            · exact activeSessInv_to_phase2 C ℓ encT idOf h0
          rcases fsSend_inr_phase2 C Dh hℓ encPt encT idOf Δcka mo s₁M P t sIdx hM₂ tblM tblL
              hinv_sIdx hdr m hshort with
            ⟨bk_sIdx, sM', sL', hfsM_eval, hinv_after⟩
          let o := fs.send (fs.initSender (ks sIdx)) hdr m
          let stL' : VP _ _ _ _ _ :=
            { esL.g.st P with tcur := t, γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (o.1, some sIdx) }
          let stM' : VP _ _ _ _ _ :=
            { esM.g.st P with tcur := t, γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (Sum.inr sIdx : RatchetSenderState (BitVec 256) ⊕ ℕ) }
          let hM' := { hM₂ with book := Function.update hM₂.book sIdx (some bk_sIdx) }
          refine Coupled2.eq
            (mL' :=
              Pure.pure (some (hdr, o.2),
                { esL with g := s₁L.record (2 + Δcka) P stL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hL₂ }))
            (mR' :=
              Pure.pure ((some (hdr, o.2),
                { esM with g := s₁M.record (2 + Δcka) P stM' ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hM' }),
                (fun _ => false, Function.update tblM sIdx sM')))
            (by
            dsimp only [hooksSlotLocal]
            simp [hep_t, StateT.run_modify, simulateQ_pure, hsync.hidL P,
              hL₂, hdr, o, stL', cc])
            (by
            simp only [hep_t, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_bind, simulateQ_pure, bind_assoc]
            dsimp only [hdr, hM₂, cc] at hfsM_eval
            rw [hfsM_eval]
            dsimp only [fs, hM', hM₂, stM', hdr, o, cc]
            simp [StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
            (Coupled2.pure ?_)
          refine Or.inr ⟨rfl, Or.inr ⟨Function.update tblM sIdx sM', Function.update tblL sIdx sL', rfl, epochQepInv_record _ _ _ _ (epochQepInv_epMgmt hqep hepL), ?_⟩⟩
          have hs₁_ep_t : s₁L.epoch P = t := hep'_eq.symm.trans hep_t
          exact syncPaperMulti_after_record hsync herase1 hs₁_stL hs₁_stM hs₁_winL hs₁_winM
            hs₁_bL hs₁_bM hs₁_trans hs₁_ep_other hs₁_ep_mono
            hs₁_ep_t.symm ⟨hsync.hidL P, hsync.hidM P⟩ ⟨hs₁_ep_t.symm, hs₁_ep_t.symm⟩
            rfl rfl rfl ⟨rfl, rfl⟩
            ⟨rfl, hsIdx_lt, hPs, Nat.le_refl t⟩
            hsess_le (fun h => Bool.noConfusion h) (fun _ => hheal1) ⟨hbk'.hsess, hbk'.hnodup, hbk'.hlen, hbk'.hused, hbk'.htblL_lk, hbk'.htblM_lk⟩
            (fun _ hlt => by subst hPs; simp [stL'] at hlt)
            (fun ep hne => by
              dsimp only [hL₂, hM₂, hM']
              rw [Function.update_of_ne hne, Function.update_of_ne hne, hcacheL_eq, hcacheM_eq]
              exact hsync.hcache_ne ep hne)
            (fun hlt => by subst hPs; simp [stL'] at hlt)
            (by
              dsimp only [hL₂, hM₂, hM']
              rw [Function.update_self, Function.update_self]
              exact ⟨sIdx, kM_out, rfl, rfl, hsIdx_lt, rfl⟩)
            (fun i hi => by
              have hne : i ≠ sIdx := by dsimp [hM', hM₂] at hi; omega
              rcases hbook_out1 i hi with ⟨hb, hm, _⟩
              exact ⟨by dsimp [hM', hM₂]; rw [Function.update_of_ne hne]; exact hb,
                     by rw [Function.update_of_ne hne]; exact hm,
                     fun h => Bool.noConfusion h⟩)
            (fun i hi => by
              by_cases hi_eq : i = sIdx
              · subst hi_eq
                refine ⟨o.1, ?_, fun hlt => by subst hPs; simp [stL'] at hlt, ?_⟩
                · dsimp [hM', hM₂]
                  rw [Function.update_self, Function.update_self, Function.update_self]
                  exact hinv_after
                · intro Q ss hQ_vS
                  by_cases hQP : Q = P
                  · subst hQP; simp [stL'] at hQ_vS; exact hQ_vS
                  · rw [Function.update_of_ne hQP] at hQ_vS
                    have hv := hsync.hvS Q; rw [hQ_vS] at hv
                    rcases hv with ⟨_, _, hQs, hle⟩
                    subst hQs; omega
              · refine ⟨fs.initSender (ks i), ?_, fun _ => rfl, ?_⟩
                · dsimp [hM', hM₂]
                  rw [Function.update_of_ne hi_eq, Function.update_of_ne hi_eq, Function.update_of_ne hi_eq]
                  have h0 := hbook_in1 i hi
                  cases phase1
                  · exact h0
                  · exact activeSessInv_to_phase2 C ℓ encT idOf h0
                · intro Q ss hQ_vS
                  by_cases hQP : Q = P
                  · subst hQP; simp [stL'] at hQ_vS; exfalso; exact hi_eq hQ_vS.2.symm
                  · rw [Function.update_of_ne hQP] at hQ_vS
                    have hv := hsync.hvS Q; rw [hQ_vS] at hv
                    rcases hv with ⟨_, _, hQs, hle⟩
                    subst hQs; omega)
        · simp only [hep_t, ↓reduceIte] at hsplit
          rcases hsplit with ⟨σ_out, k_out, hrL, hrM, _, hhL_eq, hhM_eq⟩
          rcases Prod.mk.inj hrL with ⟨hσL, hrL2⟩; rcases Prod.mk.inj hrL2 with ⟨hkL, hidxL⟩
          rcases Prod.mk.inj hrM with ⟨hσM, hrM2⟩; rcases Prod.mk.inj hrM2 with ⟨hkM, hidxM⟩
          subst σ' kL idxL σM' kM idxM hL₁ hM₁
          let hL₂ : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt :=
            { esL.h with loc := { esL.h.loc with cache := Function.update esL.h.loc.cache ep' (some (cc.2.1, σ_out, k_out, none)) } }
          let hM₂ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { esM.h with cache := Function.update esM.h.cache ep' (some (cc.2.1, σ_out, k_out, none)) }
          let hdr : Header Pt := (ep', some cc.2.1)
          let o := fs.send (fs.initSender k_out) hdr m
          let stL' : VP _ _ _ _ _ :=
            { esL.g.st P with tcur := ep', γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (o.1, (none : Option ℕ)) }
          let stM' : VP _ _ _ _ _ :=
            { esM.g.st P with tcur := ep', γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (Sum.inl o.1 : RatchetSenderState (BitVec 256) ⊕ ℕ) }
          refine Coupled2.eq
            (mL' :=
              Pure.pure (some (hdr, o.2),
                { esL with g := s₁L.record (2 + Δcka) P stL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hL₂ }))
            (mR' :=
              Pure.pure ((some (hdr, o.2),
                { esM with g := s₁M.record (2 + Δcka) P stM' ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hM₂ }),
                (fun _ => false, tblM)))
            (by
            dsimp only [hooksSlotLocal, hL₂, hdr, o, stL', ep', cc]
            simp [StateT.run_modify, simulateQ_pure, hsync.hidL P])
            (by
            dsimp only [hooksFSMulti, hM₂, hdr, o, stM', ep', cc]
            simp [StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
            (Coupled2.pure ?_)
          refine Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, epochQepInv_record _ _ _ _ (epochQepInv_epMgmt hqep hepL), ?_⟩⟩
          have htcur_mono_s : (esL.g.st (Party.senderOf t)).tcur ≤
              (Function.update esL.g.st P stL' (Party.senderOf t)).tcur := by
            by_cases hPs : Party.senderOf t = P
            · subst hPs; simp [stL', hsync.htcurL, ep']
            · simp [hPs]
          exact syncPaperMulti_after_record hsync herase1 hs₁_stL hs₁_stM hs₁_winL hs₁_winM
            hs₁_bL hs₁_bM hs₁_trans hs₁_ep_other hs₁_ep_mono
            hep'_eq ⟨hsync.hidL P, hsync.hidM P⟩ ⟨hep'_eq, hep'_eq⟩
            rfl rfl rfl ⟨rfl, rfl⟩ rfl (Nat.le_refl _)
            (fun h => Bool.noConfusion h) (fun _ => hheal1) ⟨hbk'.hsess, hbk'.hnodup, hbk'.hlen, hbk'.hused, hbk'.htblL_lk, hbk'.htblM_lk⟩
            (fun htH hlt => hsync.htH_empty htH (Nat.lt_of_le_of_lt htcur_mono_s hlt))
            (fun ep hne => by
              dsimp only [hL₂, hM₂]
              by_cases he : ep = ep'
              · subst he; simp
              · rw [Function.update_of_ne he, Function.update_of_ne he]; exact hsync.hcache_ne ep hne)
            (fun hlt => by
              dsimp only [hL₂, hM₂]
              rw [Function.update_of_ne (Ne.symm hep_t), Function.update_of_ne (Ne.symm hep_t)]
              exact hsync.hcache_lt (Nat.lt_of_le_of_lt htcur_mono_s hlt))
            (by
              dsimp only [hL₂, hM₂]
              rw [Function.update_of_ne (Ne.symm hep_t), Function.update_of_ne (Ne.symm hep_t)]
              exact hsync.hcache_eq)
            (fun i hi =>
              let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
              ⟨hb, hm, fun h => Bool.noConfusion h⟩)
            (fun i hi => by
              rcases hsync.hbook_in i hi with ⟨ss_i, hinv, hss1, hss2⟩
              refine ⟨ss_i, (by cases phase1; exact hinv; exact activeSessInv_to_phase2 C ℓ encT idOf hinv),
                fun hlt => hss1 (Nat.lt_of_le_of_lt htcur_mono_s hlt), ?_⟩
              intro Q ss hQ_vS
              by_cases hQP : Q = P
              · subst hQP; simp [stL'] at hQ_vS
              · rw [Function.update_of_ne hQP] at hQ_vS; exact hss2 Q ss hQ_vS)
      · simp only [Bool.not_eq_true] at hsends
        have hs₁L_eq := epMgmt_sendsIn_false hsends hepL
        have hs₁M_eq : s₁M = esM.g := by
          apply epMgmt_sendsIn_false _ hepM
          have heq_ep : esM.g.epoch P = esL.g.epoch P :=
            congrFun (congrArg GameState.epoch hsync.herase.symm) P
          rw [heq_ep]; exact hsends
        subst hs₁L_eq hs₁M_eq
        simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
        have hvS_sync := hsync.hvS P
        let hdr : Header Pt := ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg)
        have hhdrM : ((esM.g.st P).tcur, (esM.g.st P).curCkaMsg) = hdr := by
          simp [hdr, hsync.htcurM P, hsync.hckaMsg P]
        cases hvSL : (esL.g.st P).vS with
        | none =>
          rw [hvSL] at hvS_sync
          let ct : Header Pt × ℕ × LibsignalCiphertextWithSalt32 := (hdr, default)
          refine Coupled2.eq
            (mL' :=
              Pure.pure (some ct,
                { esL with g := esL.g.record (2 + Δcka) P (esL.g.st P) ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, ct⟩ false }))
            (mR' :=
              Pure.pure ((some ct,
                { esM with g := esM.g.record (2 + Δcka) P (esM.g.st P) ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, ct⟩ false }),
                (fun _ => false, tblM)))
            (by
            simp [liftH_run, hvSL, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hdr, ct])
            (by
            simp [liftH_run, hvS_sync, hhdrM, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, ct])
            (Coupled2.pure ?_)
          refine Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, epochQepInv_record _ _ _ _ hqep, ?_⟩⟩
          exact syncPaperMulti_after_record hsync hsync.herase rfl rfl hsync.hwinL hsync.hwinM
            hsync.hbL hsync.hbM rfl (fun _ _ => rfl) (Nat.le_refl _)
            (hsync.htcurL P) ⟨hsync.hidL P, hsync.hidM P⟩
            ⟨hsync.htcurL P, (hsync.htcurM P).trans (hsync.htcurL P)⟩
            (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩
            (by rw [hvSL]; exact hvS_sync) (Nat.le_refl _)
            (fun h => Bool.noConfusion h) (fun _ => hheal1)
            (let hbk0 := hsync.hookBookInv.mono_rem (Nat.le_succ rem); ⟨hbk0.hsess, hbk0.hnodup, hbk0.hlen, hbk0.hused, hbk0.htblL_lk, hbk0.htblM_lk⟩)
            (by simpa [Function.update_eq_self] using hsync.htH_empty)
            hsync.hcache_ne
            (by simpa [Function.update_eq_self] using hsync.hcache_lt)
            hsync.hcache_eq
            (fun i hi =>
              let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
              ⟨hb, hm, fun h => Bool.noConfusion h⟩)
            (fun i hi => by
              rcases hsync.hbook_in i hi with ⟨ss_i, hinv, hss1, hss2⟩
              refine ⟨ss_i, (by cases phase1; exact hinv; exact activeSessInv_to_phase2 C ℓ encT idOf hinv),
                by simpa [Function.update_eq_self] using hss1, ?_⟩
              intro Q ss hQ_vS
              rw [Function.update_eq_self] at hQ_vS; exact hss2 Q ss hQ_vS)
        | some so =>
          rcases so with ⟨ss, optIdx⟩
          cases optIdx with
          | none =>
            rw [hvSL] at hvS_sync
            let o := fs.send ss hdr m
            let stL' := { esL.g.st P with vS := some (o.1, (none : Option ℕ)) }
            let stM' := { esM.g.st P with vS := some (Sum.inl o.1 : RatchetSenderState (BitVec 256) ⊕ ℕ) }
            refine Coupled2.eq
              (mL' :=
                Pure.pure (some (hdr, o.2),
                  { esL with g := esL.g.record (2 + Δcka) P stL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, (hdr, o.2)⟩ false }))
              (mR' :=
                Pure.pure ((some (hdr, o.2),
                  { esM with g := esM.g.record (2 + Δcka) P stM' ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, (hdr, o.2)⟩ false }),
                  (fun _ => false, tblM)))
              (by
              dsimp only [hooksSlotLocal]
              simp [liftH_run, hvSL, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hdr, o, stL'])
              (by
              dsimp only [hooksFSMulti]
              simp [liftH_run, hvS_sync, hhdrM, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, o, stM'])
              (Coupled2.pure ?_)
            refine Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, epochQepInv_record _ _ _ _ hqep, ?_⟩⟩
            have htcur_same : (Function.update esL.g.st P stL' (Party.senderOf t)).tcur =
                (esL.g.st (Party.senderOf t)).tcur := by
              by_cases hPs : Party.senderOf t = P
              · subst hPs; simp [stL']
              · simp [hPs]
            exact syncPaperMulti_after_record hsync hsync.herase rfl rfl hsync.hwinL hsync.hwinM
              hsync.hbL hsync.hbM rfl (fun _ _ => rfl) (Nat.le_refl _)
              (hsync.htcurL P) ⟨hsync.hidL P, hsync.hidM P⟩
              ⟨hsync.htcurL P, (hsync.htcurM P).trans (hsync.htcurL P)⟩
              (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩
              rfl (Nat.le_refl _)
              (fun h => Bool.noConfusion h) (fun _ => hheal1)
              (let hbk0 := hsync.hookBookInv.mono_rem (Nat.le_succ rem); ⟨hbk0.hsess, hbk0.hnodup, hbk0.hlen, hbk0.hused, hbk0.htblL_lk, hbk0.htblM_lk⟩)
              (fun htH hlt => hsync.htH_empty htH (htcur_same ▸ hlt))
              hsync.hcache_ne
              (fun hlt => hsync.hcache_lt (htcur_same ▸ hlt))
              hsync.hcache_eq
              (fun i hi =>
                let ⟨hb, hm, _⟩ := hsync.hbook_out i hi
                ⟨hb, hm, fun h => Bool.noConfusion h⟩)
              (fun i hi => by
                rcases hsync.hbook_in i hi with ⟨ss_i, hinv, hss1, hss2⟩
                refine ⟨ss_i, (by cases phase1; exact hinv; exact activeSessInv_to_phase2 C ℓ encT idOf hinv),
                  fun hlt => hss1 (htcur_same ▸ hlt), ?_⟩
                intro Q ss' hQ_vS
                by_cases hQP : Q = P
                · subst hQP; simp [stL'] at hQ_vS
                · rw [Function.update_of_ne hQP] at hQ_vS; exact hss2 Q ss' hQ_vS)
          | some sIdx =>
            rw [hvSL] at hvS_sync
            rcases hvS_sync with ⟨hvSM, hsIdx_lt, hPs, hle_t⟩
            rcases hsync.hbook_in sIdx hsIdx_lt with ⟨ss_sIdx, hinv_sIdx, hss1, hss2⟩
            have hss_eq : ss_sIdx = ss := hss2 P ss hvSL
            subst hss_eq
            have hinv_f : ActiveSessInv C ℓ encT idOf false (ks sIdx) ss_sIdx
                  (match (esL.g.st (Party.receiverOf t)).vR t with
                   | some (rs, some j) => if j = sIdx then rs else fs.initReceiver (ks sIdx)
                   | _ => fs.initReceiver (ks sIdx))
                ((esM.h.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) := by
              cases phase1
              · exact hinv_sIdx
              · exact activeSessInv_to_phase2 C ℓ encT idOf hinv_sIdx
            rcases fsSend_inr_phase2 C Dh hℓ encPt encT idOf Δcka mo esM.g P (esM.g.st P).tcur sIdx
                esM.h tblM tblL hinv_f hdr m hshort with
              ⟨bk_sIdx, sM', sL', hfsM_eval, hinv_after⟩
            let o := fs.send ss_sIdx hdr m
            let stL' := { esL.g.st P with vS := some (o.1, some sIdx) }
            let stM' := { esM.g.st P with vS := some (Sum.inr sIdx : RatchetSenderState (BitVec 256) ⊕ ℕ) }
            let hM' := { esM.h with book := Function.update esM.h.book sIdx (some bk_sIdx) }
            refine Coupled2.eq
              (mL' :=
                Pure.pure (some (hdr, o.2),
                  { esL with g := esL.g.record (2 + Δcka) P stL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, (hdr, o.2)⟩ false }))
              (mR' :=
                Pure.pure ((some (hdr, o.2),
                  { esM with g := esM.g.record (2 + Δcka) P stM' ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                             h := hM' }),
                  (fun _ => false, Function.update tblM sIdx sM')))
              (by
              dsimp only [hooksSlotLocal]
              simp [liftH_run, hvSL, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hdr, o, stL'])
              (by
              simp only [liftH_run, hvSM, hhdrM, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_assoc]
              dsimp only [hdr] at hfsM_eval
              rw [hfsM_eval]
              dsimp only [fs, hM', stM', hdr, o]
              simp [StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
              (Coupled2.pure ?_)
            refine Or.inr ⟨rfl, Or.inr ⟨Function.update tblM sIdx sM', Function.update tblL sIdx sL', rfl, epochQepInv_record _ _ _ _ hqep, ?_⟩⟩
            have htcur_same : (Function.update esL.g.st P stL' (Party.senderOf t)).tcur =
                (esL.g.st (Party.senderOf t)).tcur := by
              by_cases hPs' : Party.senderOf t = P
              · subst hPs'; simp [stL']
              · simp [hPs']
            exact syncPaperMulti_after_record hsync hsync.herase rfl rfl hsync.hwinL hsync.hwinM
              hsync.hbL hsync.hbM rfl (fun _ _ => rfl) (Nat.le_refl _)
              (hsync.htcurL P) ⟨hsync.hidL P, hsync.hidM P⟩
              ⟨hsync.htcurL P, (hsync.htcurM P).trans (hsync.htcurL P)⟩
              (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩
              ⟨rfl, hsIdx_lt, hPs, hle_t⟩ (Nat.le_refl _)
              (fun h => Bool.noConfusion h) (fun _ => hheal1)
              (let hbk0 := hsync.hookBookInv.mono_rem (Nat.le_succ rem); ⟨hbk0.hsess, hbk0.hnodup, hbk0.hlen, hbk0.hused, hbk0.htblL_lk, hbk0.htblM_lk⟩)
              (fun htH hlt => hsync.htH_empty htH (htcur_same ▸ hlt))
              hsync.hcache_ne
              (fun hlt => hsync.hcache_lt (htcur_same ▸ hlt))
              hsync.hcache_eq
              (fun i hi => by
                have hne : i ≠ sIdx := by dsimp [hM'] at hi; omega
                rcases hsync.hbook_out i hi with ⟨hb, hm, _⟩
                exact ⟨by dsimp [hM']; rw [Function.update_of_ne hne]; exact hb,
                       by rw [Function.update_of_ne hne]; exact hm,
                       fun h => Bool.noConfusion h⟩)
              (fun i hi => by
                by_cases hi_eq : i = sIdx
                · subst hi_eq
                  refine ⟨o.1, ?_, fun hlt => by rw [htcur_same, ← hPs] at hlt; omega, ?_⟩
                  · dsimp [hM']
                    rw [Function.update_self, Function.update_self, Function.update_self]
                    exact hinv_after
                  · intro Q ss' hQ_vS
                    by_cases hQP : Q = P
                    · subst hQP; simp [stL'] at hQ_vS; exact hQ_vS
                    · rw [Function.update_of_ne hQP] at hQ_vS
                      have hv := hsync.hvS Q; rw [hQ_vS] at hv
                      rcases hv with ⟨_, _, hQs, _⟩
                      exfalso; exact hQP (hQs.trans hPs.symm)
                · rcases hsync.hbook_in i hi with ⟨ss_i, hinv_i, hss1_i, hss2_i⟩
                  refine ⟨ss_i, ?_, fun hlt => hss1_i (htcur_same ▸ hlt), ?_⟩
                  · dsimp [hM']
                    rw [Function.update_of_ne hi_eq, Function.update_of_ne hi_eq, Function.update_of_ne hi_eq]
                    cases phase1
                    · exact hinv_i
                    · exact activeSessInv_to_phase2 C ℓ encT idOf hinv_i
                  · intro Q ss' hQ_vS
                    by_cases hQP : Q = P
                    · subst hQP; simp [stL'] at hQ_vS; exfalso; exact hi_eq hQ_vS.2.symm
                    · rw [Function.update_of_ne hQP] at hQ_vS; exact hss2_i Q ss' hQ_vS)

private theorem transmitE_coupled_phase1_stay {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × (LibsignalMsgPublicPart × Plain ℓ) × Option (BitVec 256))
    (hshort : qry.2.1.1.shortB = true)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL)
    (hheal_true : ∀ s₁L, esL.g.epMgmt (2 + Δcka) qep qry.1 qry.2.2.isSome = some s₁L →
      (⟨true, tL, t⟩ : Mode).policy.leakDoom esL.g s₁L = false →
      healedBy s₁L.tL (2 + Δcka) t = true) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((transmitE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.policy qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((transmitE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.policy qry).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((transmitE (hooksFSMulti cka prng fs Δcka mo false true) (2 + Δcka) qep mo.policy qry).run esM)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  rcases qry with ⟨P, m, r⟩
  dsimp only at hshort hheal_true
  unfold transmitE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habL, hsync.habM,
    hsync.hwinL, hsync.hwinM, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  have hep_sync := eraseSt_epMgmt_sync hsync.herase (2 + Δcka) qep P r.isSome
  cases hepL : esL.g.epMgmt (2 + Δcka) qep P r.isSome with
  | none =>
    rw [hepL, Option.map_none] at hep_sync
    have hepM : esM.g.epMgmt (2 + Δcka) qep P r.isSome = none :=
      Option.map_eq_none_iff.mp hep_sync.symm
    simp only [hepM, StateT.run_pure, simulateQ_pure]
    exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, hqep, hsync.mono_rem (Nat.le_succ rem)⟩))))
  | some s₁L =>
    rw [hepL, Option.map_some] at hep_sync
    rcases Option.map_eq_some_iff.mp hep_sync.symm with ⟨s₁M, hepM, herase1'⟩
    have herase1 : eraseSt s₁L = eraseSt s₁M := herase1'.symm
    simp only [hepM]
    have hdoom_eq : mo.policy.leakDoom esL.g s₁L = mo.policy.leakDoom esM.g s₁M :=
      _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_leakDoom hsync.herase herase1 mo.policy
    by_cases hdoom : mo.policy.leakDoom esL.g s₁L = true
    · have hdoomM : mo.policy.leakDoom esM.g s₁M = true := hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify,
        pure_bind, StateT.run_pure, simulateQ_pure]
      exact Coupled3.pure (Or.inl rfl)
    · simp only [Bool.not_eq_true] at hdoom
      have hdoomM : mo.policy.leakDoom esM.g s₁M = false := hdoom_eq.symm.trans hdoom
      simp only [hdoom, hdoomM, Bool.false_eq_true, ↓reduceIte]
      have hheal1 := hheal_true s₁L hepL hdoom
      have hs₁_stL := epMgmt_st_eq_of_some hepL
      have hs₁_stM := epMgmt_st_eq_of_some hepM
      have hs₁_winL := (epMgmt_win_eq_of_some hepL).trans hsync.hwinL
      have hs₁_winM := (epMgmt_win_eq_of_some hepM).trans hsync.hwinM
      have hs₁_bL := (epMgmt_b_eq_of_some hepL).trans hsync.hbL
      have hs₁_bM := (epMgmt_b_eq_of_some hepM).trans hsync.hbM
      have hs₁_trans := epMgmt_trans_eq_of_some hepL
      unfold vSend
      simp only [hs₁_stL, hs₁_stM, hsync.hidL P, hsync.hidM P, hsync.htcurM P, hsync.htcurL P,
        hsync.hγ P, hsync.hroot P]
      by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
      · have hs₁_ep := epMgmt_sendsIn_true hsends hepL
        have hep'_eq : esL.g.epoch P + 1 = s₁L.epoch P := by
          rw [hs₁_ep, Function.update_self]
        have hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q := by
          intro Q hQ; rw [hs₁_ep, Function.update_of_ne hQ]
        have hs₁_ep_mono : esL.g.epoch P ≤ s₁L.epoch P := by omega
        simp only [hsends, ↓reduceIte]
        rw [hooksSlotLocal_startSend_eq, hooksFSMulti_startSend_eq, hooksFSMulti_startSend_eq]
        simp only [StateT.run_bind, liftH_run, simulateQ_bind, bind_assoc]
        refine Coupled3.bind
          (sampleOptCoins_coupled3 (impl₀ := implF) (impl₁ := implT) ks r esL.h esM.h
            (fun _ => false, tblM) (fun _ => false, tblL)) ?_
        rintro ⟨coins, hL0⟩ ⟨⟨coinsM0, hM0⟩, s0⟩ ⟨⟨coinsM1, hM1⟩, s1⟩
          ⟨hcoins0, hcoins1, rfl, rfl, rfl, rfl, rfl⟩
        dsimp only at hcoins0 hcoins1; subst coinsM0 coinsM1
        dsimp only
        let cc := cka.send (esL.g.st P).γ coins
        let ep' := esL.g.epoch P + 1
        have hempty_arg : ep' = t → (tL.isSome && decide (t = mo.tH)) = true →
            esL.h.loc.sessions = [] := by
          intro hep_t htH
          have hPs : P = Party.senderOf t := by
            apply party_eq_senderOf_of_sendsIn_true
            simpa [ep', hep_t] using hsends
          apply hsync.htH_empty htH
          rw [← hPs, hsync.htcurL P]
          omega
        refine Coupled3.eq
          (by rw [hooksSlotLocal_startSend_some_eq, StateT.run_bind, simulateQ_bind, bind_assoc])
          (by rw [hooksFSMulti_startSend_some_eq, StateT.run_bind, simulateQ_bind, StateT.run_bind, bind_assoc])
          (by rw [hooksFSMulti_startSend_some_eq, StateT.run_bind, simulateQ_bind, StateT.run_bind, bind_assoc]) ?_
        refine Coupled3.bind
          (root_regSessOpt_coupled (impl₀ := implF) (impl₁ := implT)
            (s₀ := (fun _ => false, tblM)) (s₁ := (fun _ => false, tblL))
            prng hsync.hookBookInv hempty_arg cc.2.2 (esL.g.st P).root) ?_
        rintro ⟨⟨σ', kL, idxL⟩, hL₁⟩ ⟨⟨⟨σM0, kM0, idxM0⟩, hM₁⟩, s₀_st⟩ ⟨⟨⟨σM1, kM1, idxM1⟩, hM₁'⟩, s₁_st⟩
          ⟨hhM1_eq, rfl, rfl, hbk', hcacheL_eq, hcacheM_eq, hbookM_eq, hlfM_eq, ⟨J, hsess_step⟩, hsplit⟩
        dsimp only at hhM1_eq; subst hM₁'
        have hsess_le : esM.h.sessions.length ≤ hM₁.sessions.length := by
          rcases hsess_step with h | h <;> rw [h] <;> simp
        by_cases hep_t : ep' = t
        · simp only [hep_t, ↓reduceIte] at hsplit
          dsimp only [ep'] at hep_t
          rcases hsplit with ⟨sIdx, σ_out, kM_out, hrL, hrM0, hrM1, hsIdx_lt⟩
          rcases Prod.mk.inj hrL with ⟨hσL, hrL2⟩; rcases Prod.mk.inj hrL2 with ⟨hkL, hidxL⟩
          rcases Prod.mk.inj hrM0 with ⟨hσM0, hrM02⟩; rcases Prod.mk.inj hrM02 with ⟨hkM0, hidxM0⟩
          rcases Prod.mk.inj hrM1 with ⟨hσM1, hrM12⟩; rcases Prod.mk.inj hrM12 with ⟨hkM1, hidxM1⟩
          subst σ' kL idxL σM0 kM0 idxM0 σM1 kM1 idxM1
          have hPs : P = Party.senderOf t := by
            apply party_eq_senderOf_of_sendsIn_true
            simpa [hep_t] using hsends
          have htcur_lt : (esL.g.st (Party.senderOf t)).tcur < t := by
            rw [← hPs, hsync.htcurL P]; omega
          have hs₁_ep_t : s₁L.epoch P = t := hep'_eq.symm.trans hep_t
          have hsafeL : s₁L.safeCh (2 + Δcka) P = true := by
            cases hs : s₁L.safeCh (2 + Δcka) P
            · have hhf := healedBy_false_of_not_safeCh_le s₁L (2 + Δcka) t P (by omega) hs
              rw [hhf] at hheal1; cases hheal1
            · rfl
          have hsafeM : s₁M.safeCh (2 + Δcka) P = true := by
            rw [← _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_safeCh herase1 (2 + Δcka) P]
            exact hsafeL
          have ⟨hbook_out1, hbook_in1⟩ := hbook_after_reg_at_t hsync htcur_lt hbookM_eq hsess_le
          let hL₂ : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt :=
            { hL₁ with loc := { hL₁.loc with cache := Function.update hL₁.loc.cache t (some (cc.2.1, σ_out, ks sIdx, some sIdx)) } }
          let hM₂ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { hM₁ with cache := Function.update hM₁.cache t (some (cc.2.1, σ_out, kM_out, some sIdx)) }
          let hdr : Header Pt := (t, some cc.2.1)
          rcases fsSend_inr_phase1 C Dh hℓ encPt encT idOf Δcka mo s₁M P t sIdx hsafeM hM₂ tblM tblL
              (hbook_in1 sIdx hsIdx_lt) hdr m hshort with
            ⟨bk_sIdx, sM', sL', hfsM0_eval, hfsM1_eval, hinv_after⟩
          let o := fs.send (fs.initSender (ks sIdx)) hdr m
          let stL' : VP _ _ _ _ _ :=
            { esL.g.st P with tcur := t, γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (o.1, some sIdx) }
          let stM' : VP _ _ _ _ _ :=
            { esM.g.st P with tcur := t, γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (Sum.inr sIdx : RatchetSenderState (BitVec 256) ⊕ ℕ) }
          let hM' := { hM₂ with book := Function.update hM₂.book sIdx (some bk_sIdx) }
          refine Coupled3.eq
            (mL' :=
              Pure.pure (some (hdr, o.2),
                { esL with g := s₁L.record (2 + Δcka) P stL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hL₂ }))
            (m₁' :=
              Pure.pure ((some (hdr, o.2),
                { esM with g := s₁M.record (2 + Δcka) P stM' ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hM' }),
                (fun _ => false, Function.update tblM sIdx sM')))
            (m₂' :=
              Pure.pure ((some (hdr, o.2),
                { esM with g := s₁M.record (2 + Δcka) P stM' ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hM' }),
                (fun _ => false, Function.update tblL sIdx sL')))
            (by
            dsimp only [hooksSlotLocal]
            simp [hep_t, StateT.run_modify, simulateQ_pure, hsync.hidL P,
              hL₂, hdr, o, stL', cc])
            (by
            simp only [hep_t, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_bind, simulateQ_pure, bind_assoc]
            dsimp only [hdr, hM₂, cc] at hfsM0_eval
            rw [hfsM0_eval]
            dsimp only [fs, hM', hM₂, stM', hdr, o, cc]
            simp [StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
            (by
            simp only [hep_t, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_bind, simulateQ_pure, bind_assoc]
            dsimp only [hdr, hM₂, cc] at hfsM1_eval
            rw [hfsM1_eval]
            dsimp only [fs, hM', hM₂, stM', hdr, o, cc]
            simp [StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
            (Coupled3.pure ?_)
          refine Or.inr (Or.inr (Or.inr (Or.inr
            ⟨rfl, rfl, rfl, Function.update tblM sIdx sM', Function.update tblL sIdx sL', rfl, rfl, epochQepInv_record _ _ _ _ (epochQepInv_epMgmt hqep hepL), ?_⟩)))
          exact syncPaperMulti_after_record hsync herase1 hs₁_stL hs₁_stM hs₁_winL hs₁_winM
            hs₁_bL hs₁_bM hs₁_trans hs₁_ep_other hs₁_ep_mono
            hs₁_ep_t.symm ⟨hsync.hidL P, hsync.hidM P⟩ ⟨hs₁_ep_t.symm, hs₁_ep_t.symm⟩
            rfl rfl rfl ⟨rfl, rfl⟩
            ⟨rfl, hsIdx_lt, hPs, Nat.le_refl t⟩
            hsess_le (fun _ => by dsimp [hM', hM₂]; rw [hlfM_eq]; exact hsync.hlf rfl)
            (fun h => Bool.noConfusion h) ⟨hbk'.hsess, hbk'.hnodup, hbk'.hlen, hbk'.hused, hbk'.htblL_lk, hbk'.htblM_lk⟩
            (fun _ hlt => by subst hPs; simp [stL'] at hlt)
            (fun ep hne => by
              dsimp only [hL₂, hM₂, hM']
              rw [Function.update_of_ne hne, Function.update_of_ne hne, hcacheL_eq, hcacheM_eq]
              exact hsync.hcache_ne ep hne)
            (fun hlt => by subst hPs; simp [stL'] at hlt)
            (by
              dsimp only [hL₂, hM₂, hM']
              rw [Function.update_self, Function.update_self]
              exact ⟨sIdx, kM_out, rfl, rfl, hsIdx_lt, rfl⟩)
            (fun i hi => by
              have hne : i ≠ sIdx := by dsimp [hM', hM₂] at hi; omega
              rcases hbook_out1 i hi with ⟨hb, hm, hl⟩
              exact ⟨by dsimp [hM', hM₂]; rw [Function.update_of_ne hne]; exact hb,
                     by rw [Function.update_of_ne hne]; exact hm,
                     fun hp => by rw [Function.update_of_ne hne]; exact hl hp⟩)
            (fun i hi => by
              by_cases hi_eq : i = sIdx
              · subst hi_eq
                refine ⟨o.1, ?_, fun hlt => by subst hPs; simp [stL'] at hlt, ?_⟩
                · dsimp [hM', hM₂]
                  rw [Function.update_self, Function.update_self, Function.update_self]
                  exact hinv_after
                · intro Q ss hQ_vS
                  by_cases hQP : Q = P
                  · subst hQP; simp [stL'] at hQ_vS; exact hQ_vS
                  · rw [Function.update_of_ne hQP] at hQ_vS
                    have hv := hsync.hvS Q; rw [hQ_vS] at hv
                    rcases hv with ⟨_, _, hQs, _⟩
                    subst hQs; omega
              · refine ⟨fs.initSender (ks i), ?_, fun _ => rfl, ?_⟩
                · dsimp [hM', hM₂]
                  rw [Function.update_of_ne hi_eq, Function.update_of_ne hi_eq, Function.update_of_ne hi_eq]
                  exact hbook_in1 i hi
                · intro Q ss hQ_vS
                  by_cases hQP : Q = P
                  · subst hQP; simp [stL'] at hQ_vS; exfalso; exact hi_eq hQ_vS.2.symm
                  · rw [Function.update_of_ne hQP] at hQ_vS
                    have hv := hsync.hvS Q; rw [hQ_vS] at hv
                    rcases hv with ⟨_, _, hQs, _⟩
                    subst hQs; omega)
        · simp only [hep_t, ↓reduceIte] at hsplit
          rcases hsplit with ⟨σ_out, k_out, hrL, hrM0, hrM1, hhL_eq, hhM_eq⟩
          rcases Prod.mk.inj hrL with ⟨hσL, hrL2⟩; rcases Prod.mk.inj hrL2 with ⟨hkL, hidxL⟩
          rcases Prod.mk.inj hrM0 with ⟨hσM0, hrM02⟩; rcases Prod.mk.inj hrM02 with ⟨hkM0, hidxM0⟩
          rcases Prod.mk.inj hrM1 with ⟨hσM1, hrM12⟩; rcases Prod.mk.inj hrM12 with ⟨hkM1, hidxM1⟩
          subst σ' kL idxL σM0 kM0 idxM0 σM1 kM1 idxM1 hL₁ hM₁
          let hL₂ : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt :=
            { esL.h with loc := { esL.h.loc with cache := Function.update esL.h.loc.cache ep' (some (cc.2.1, σ_out, k_out, none)) } }
          let hM₂ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { esM.h with cache := Function.update esM.h.cache ep' (some (cc.2.1, σ_out, k_out, none)) }
          let hdr : Header Pt := (ep', some cc.2.1)
          let o := fs.send (fs.initSender k_out) hdr m
          let stL' : VP _ _ _ _ _ :=
            { esL.g.st P with tcur := ep', γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (o.1, (none : Option ℕ)) }
          let stM' : VP _ _ _ _ _ :=
            { esM.g.st P with tcur := ep', γ := cc.1, curCkaMsg := some cc.2.1, root := σ_out,
                              vS := some (Sum.inl o.1 : RatchetSenderState (BitVec 256) ⊕ ℕ) }
          refine Coupled3.eq
            (mL' :=
              Pure.pure (some (hdr, o.2),
                { esL with g := s₁L.record (2 + Δcka) P stL' ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hL₂ }))
            (m₁' :=
              Pure.pure ((some (hdr, o.2),
                { esM with g := s₁M.record (2 + Δcka) P stM' ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hM₂ }),
                (fun _ => false, tblM)))
            (m₂' :=
              Pure.pure ((some (hdr, o.2),
                { esM with g := s₁M.record (2 + Δcka) P stM' ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                           h := hM₂ }),
                (fun _ => false, tblL)))
            (by
            dsimp only [hooksSlotLocal, hL₂, hdr, o, stL', ep', cc]
            simp [StateT.run_modify, simulateQ_pure, hsync.hidL P])
            (by
            dsimp only [hooksFSMulti, hM₂, hdr, o, stM', ep', cc]
            simp [StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
            (by
            dsimp only [hooksFSMulti, hM₂, hdr, o, stM', ep', cc]
            simp [StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
            (Coupled3.pure ?_)
          refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, epochQepInv_record _ _ _ _ (epochQepInv_epMgmt hqep hepL), ?_⟩)))
          have htcur_mono_s : (esL.g.st (Party.senderOf t)).tcur ≤
              (Function.update esL.g.st P stL' (Party.senderOf t)).tcur := by
            by_cases hPs : Party.senderOf t = P
            · subst hPs; simp [stL', hsync.htcurL, ep']
            · simp [hPs]
          exact syncPaperMulti_after_record hsync herase1 hs₁_stL hs₁_stM hs₁_winL hs₁_winM
            hs₁_bL hs₁_bM hs₁_trans hs₁_ep_other hs₁_ep_mono
            hep'_eq ⟨hsync.hidL P, hsync.hidM P⟩ ⟨hep'_eq, hep'_eq⟩
            rfl rfl rfl ⟨rfl, rfl⟩ rfl (Nat.le_refl _)
            (fun _ => hsync.hlf rfl) (fun h => Bool.noConfusion h) ⟨hbk'.hsess, hbk'.hnodup, hbk'.hlen, hbk'.hused, hbk'.htblL_lk, hbk'.htblM_lk⟩
            (fun htH hlt => hsync.htH_empty htH (Nat.lt_of_le_of_lt htcur_mono_s hlt))
            (fun ep hne => by
              dsimp only [hL₂, hM₂]
              by_cases he : ep = ep'
              · subst he; simp
              · rw [Function.update_of_ne he, Function.update_of_ne he]; exact hsync.hcache_ne ep hne)
            (fun hlt => by
              dsimp only [hL₂, hM₂]
              rw [Function.update_of_ne (Ne.symm hep_t), Function.update_of_ne (Ne.symm hep_t)]
              exact hsync.hcache_lt (Nat.lt_of_le_of_lt htcur_mono_s hlt))
            (by
              dsimp only [hL₂, hM₂]
              rw [Function.update_of_ne (Ne.symm hep_t), Function.update_of_ne (Ne.symm hep_t)]
              exact hsync.hcache_eq)
            hsync.hbook_out
            (fun i hi => by
              rcases hsync.hbook_in i hi with ⟨ss_i, hinv, hss1, hss2⟩
              refine ⟨ss_i, hinv, fun hlt => hss1 (Nat.lt_of_le_of_lt htcur_mono_s hlt), ?_⟩
              intro Q ss hQ_vS
              by_cases hQP : Q = P
              · subst hQP; simp [stL'] at hQ_vS
              · rw [Function.update_of_ne hQP] at hQ_vS; exact hss2 Q ss hQ_vS)
      · simp only [Bool.not_eq_true] at hsends
        have hs₁L_eq := epMgmt_sendsIn_false hsends hepL
        have hs₁M_eq : s₁M = esM.g := by
          apply epMgmt_sendsIn_false _ hepM
          have heq_ep : esM.g.epoch P = esL.g.epoch P :=
            congrFun (congrArg GameState.epoch hsync.herase.symm) P
          rw [heq_ep]; exact hsends
        subst hs₁L_eq hs₁M_eq
        simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
        have hvS_sync := hsync.hvS P
        let hdr : Header Pt := ((esL.g.st P).tcur, (esL.g.st P).curCkaMsg)
        have hhdrM : ((esM.g.st P).tcur, (esM.g.st P).curCkaMsg) = hdr := by
          simp [hdr, hsync.htcurM P, hsync.hckaMsg P]
        cases hvSL : (esL.g.st P).vS with
        | none =>
          rw [hvSL] at hvS_sync
          let ct : Header Pt × ℕ × LibsignalCiphertextWithSalt32 := (hdr, default)
          refine Coupled3.eq
            (mL' :=
              Pure.pure (some ct,
                { esL with g := esL.g.record (2 + Δcka) P (esL.g.st P) ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, ct⟩ false }))
            (m₁' :=
              Pure.pure ((some ct,
                { esM with g := esM.g.record (2 + Δcka) P (esM.g.st P) ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, ct⟩ false }),
                (fun _ => false, tblM)))
            (m₂' :=
              Pure.pure ((some ct,
                { esM with g := esM.g.record (2 + Δcka) P (esM.g.st P) ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, ct⟩ false }),
                (fun _ => false, tblL)))
            (by
            simp [liftH_run, hvSL, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hdr, ct])
            (by
            simp [liftH_run, hvS_sync, hhdrM, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, ct])
            (by
            simp [liftH_run, hvS_sync, hhdrM, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, ct])
            (Coupled3.pure ?_)
          refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, epochQepInv_record _ _ _ _ hqep, ?_⟩)))
          exact syncPaperMulti_after_record hsync hsync.herase rfl rfl hsync.hwinL hsync.hwinM
            hsync.hbL hsync.hbM rfl (fun _ _ => rfl) (Nat.le_refl _)
            (hsync.htcurL P) ⟨hsync.hidL P, hsync.hidM P⟩
            ⟨hsync.htcurL P, (hsync.htcurM P).trans (hsync.htcurL P)⟩
            (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩
            (by rw [hvSL]; exact hvS_sync) (Nat.le_refl _)
            (fun _ => hsync.hlf rfl) (fun h => Bool.noConfusion h)
            (let hbk0 := hsync.hookBookInv.mono_rem (Nat.le_succ rem); ⟨hbk0.hsess, hbk0.hnodup, hbk0.hlen, hbk0.hused, hbk0.htblL_lk, hbk0.htblM_lk⟩)
            (by simpa [Function.update_eq_self] using hsync.htH_empty)
            hsync.hcache_ne
            (by simpa [Function.update_eq_self] using hsync.hcache_lt)
            hsync.hcache_eq
            hsync.hbook_out
            (fun i hi => by
              rcases hsync.hbook_in i hi with ⟨ss_i, hinv, hss1, hss2⟩
              refine ⟨ss_i, hinv, by simpa [Function.update_eq_self] using hss1, ?_⟩
              intro Q ss hQ_vS
              rw [Function.update_eq_self] at hQ_vS; exact hss2 Q ss hQ_vS)
        | some so =>
          rcases so with ⟨ss, optIdx⟩
          cases optIdx with
          | none =>
            rw [hvSL] at hvS_sync
            let o := fs.send ss hdr m
            let stL' := { esL.g.st P with vS := some (o.1, (none : Option ℕ)) }
            let stM' := { esM.g.st P with vS := some (Sum.inl o.1 : RatchetSenderState (BitVec 256) ⊕ ℕ) }
            refine Coupled3.eq
              (mL' :=
                Pure.pure (some (hdr, o.2),
                  { esL with g := esL.g.record (2 + Δcka) P stL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, (hdr, o.2)⟩ false }))
              (m₁' :=
                Pure.pure ((some (hdr, o.2),
                  { esM with g := esM.g.record (2 + Δcka) P stM' ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, (hdr, o.2)⟩ false }),
                  (fun _ => false, tblM)))
              (m₂' :=
                Pure.pure ((some (hdr, o.2),
                  { esM with g := esM.g.record (2 + Δcka) P stM' ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, (hdr, o.2)⟩ false }),
                  (fun _ => false, tblL)))
              (by
              dsimp only [hooksSlotLocal]
              simp [liftH_run, hvSL, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hdr, o, stL'])
              (by
              dsimp only [hooksFSMulti]
              simp [liftH_run, hvS_sync, hhdrM, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, o, stM'])
              (by
              dsimp only [hooksFSMulti]
              simp [liftH_run, hvS_sync, hhdrM, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, o, stM'])
              (Coupled3.pure ?_)
            refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, epochQepInv_record _ _ _ _ hqep, ?_⟩)))
            have htcur_same : (Function.update esL.g.st P stL' (Party.senderOf t)).tcur =
                (esL.g.st (Party.senderOf t)).tcur := by
              by_cases hPs : Party.senderOf t = P
              · subst hPs; simp [stL']
              · simp [hPs]
            exact syncPaperMulti_after_record hsync hsync.herase rfl rfl hsync.hwinL hsync.hwinM
              hsync.hbL hsync.hbM rfl (fun _ _ => rfl) (Nat.le_refl _)
              (hsync.htcurL P) ⟨hsync.hidL P, hsync.hidM P⟩
              ⟨hsync.htcurL P, (hsync.htcurM P).trans (hsync.htcurL P)⟩
              (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩
              rfl (Nat.le_refl _)
              (fun _ => hsync.hlf rfl) (fun h => Bool.noConfusion h)
              (let hbk0 := hsync.hookBookInv.mono_rem (Nat.le_succ rem); ⟨hbk0.hsess, hbk0.hnodup, hbk0.hlen, hbk0.hused, hbk0.htblL_lk, hbk0.htblM_lk⟩)
              (fun htH hlt => hsync.htH_empty htH (htcur_same ▸ hlt))
              hsync.hcache_ne
              (fun hlt => hsync.hcache_lt (htcur_same ▸ hlt))
              hsync.hcache_eq
              hsync.hbook_out
              (fun i hi => by
                rcases hsync.hbook_in i hi with ⟨ss_i, hinv, hss1, hss2⟩
                refine ⟨ss_i, hinv, fun hlt => hss1 (htcur_same ▸ hlt), ?_⟩
                intro Q ss' hQ_vS
                by_cases hQP : Q = P
                · subst hQP; simp [stL'] at hQ_vS
                · rw [Function.update_of_ne hQP] at hQ_vS; exact hss2 Q ss' hQ_vS)
          | some sIdx =>
            rw [hvSL] at hvS_sync
            rcases hvS_sync with ⟨hvSM, hsIdx_lt, hPs, hle_t⟩
            rcases hsync.hbook_in sIdx hsIdx_lt with ⟨ss_sIdx, hinv_sIdx, hss1, hss2⟩
            have hss_eq : ss_sIdx = ss := hss2 P ss hvSL
            subst hss_eq
            have hsafeL : esL.g.safeCh (2 + Δcka) P = true := by
              cases hs : esL.g.safeCh (2 + Δcka) P
              · have hle_ep : t ≤ esL.g.epoch P := by rw [← hsync.htcurL P]; exact hle_t
                have hhf := healedBy_false_of_not_safeCh_le esL.g (2 + Δcka) t P hle_ep hs
                rw [hhf] at hheal1; cases hheal1
              · rfl
            have hsafeM : esM.g.safeCh (2 + Δcka) P = true := by
              rw [← _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_safeCh hsync.herase (2 + Δcka) P]
              exact hsafeL
            rcases fsSend_inr_phase1 C Dh hℓ encPt encT idOf Δcka mo esM.g P (esM.g.st P).tcur sIdx
                hsafeM esM.h tblM tblL hinv_sIdx hdr m hshort with
              ⟨bk_sIdx, sM', sL', hfsM0_eval, hfsM1_eval, hinv_after⟩
            let o := fs.send ss_sIdx hdr m
            let stL' : VP _ _ _ _ _ := { esL.g.st P with vS := some (o.1, some sIdx) }
            let stM' : VP _ _ _ _ _ := { esM.g.st P with vS := some (Sum.inr sIdx : RatchetSenderState (BitVec 256) ⊕ ℕ) }
            let hM' := { esM.h with book := Function.update esM.h.book sIdx (some bk_sIdx) }
            refine Coupled3.eq
              (mL' :=
                Pure.pure (some (hdr, o.2),
                  { esL with g := esL.g.record (2 + Δcka) P stL' ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, (hdr, o.2)⟩ false }))
              (m₁' :=
                Pure.pure ((some (hdr, o.2),
                  { esM with g := esM.g.record (2 + Δcka) P stM' ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                             h := hM' }),
                  (fun _ => false, Function.update tblM sIdx sM')))
              (m₂' :=
                Pure.pure ((some (hdr, o.2),
                  { esM with g := esM.g.record (2 + Δcka) P stM' ⟨⟨P, esM.g.epoch P, esM.g.idx P + 1⟩, m, (hdr, o.2)⟩ false,
                             h := hM' }),
                  (fun _ => false, Function.update tblL sIdx sL')))
              (by
              dsimp only [hooksSlotLocal]
              simp [liftH_run, hvSL, StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure, hdr, o, stL'])
              (by
              simp only [liftH_run, hvSM, hhdrM, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_assoc]
              dsimp only [hdr] at hfsM0_eval
              rw [hfsM0_eval]
              dsimp only [fs, hM', stM', hdr, o]
              simp [StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
              (by
              simp only [liftH_run, hvSM, hhdrM, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_assoc]
              dsimp only [hdr] at hfsM1_eval
              rw [hfsM1_eval]
              dsimp only [fs, hM', stM', hdr, o]
              simp [StateT.run_modify, StateT.run_pure, simulateQ_pure, hsync.hidM P])
              (Coupled3.pure ?_)
            refine Or.inr (Or.inr (Or.inr (Or.inr
              ⟨rfl, rfl, rfl, Function.update tblM sIdx sM', Function.update tblL sIdx sL', rfl, rfl, epochQepInv_record _ _ _ _ hqep, ?_⟩)))
            have htcur_same : (Function.update esL.g.st P stL' (Party.senderOf t)).tcur =
                (esL.g.st (Party.senderOf t)).tcur := by
              by_cases hPs' : Party.senderOf t = P
              · subst hPs'; simp [stL']
              · simp [hPs']
            exact syncPaperMulti_after_record hsync hsync.herase rfl rfl hsync.hwinL hsync.hwinM
              hsync.hbL hsync.hbM rfl (fun _ _ => rfl) (Nat.le_refl _)
              (hsync.htcurL P) ⟨hsync.hidL P, hsync.hidM P⟩
              ⟨hsync.htcurL P, (hsync.htcurM P).trans (hsync.htcurL P)⟩
              (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩
              ⟨rfl, hsIdx_lt, hPs, hle_t⟩ (Nat.le_refl _)
              (fun _ => hsync.hlf rfl) (fun h => Bool.noConfusion h)
              (let hbk0 := hsync.hookBookInv.mono_rem (Nat.le_succ rem); ⟨hbk0.hsess, hbk0.hnodup, hbk0.hlen, hbk0.hused, hbk0.htblL_lk, hbk0.htblM_lk⟩)
              (fun htH hlt => hsync.htH_empty htH (htcur_same ▸ hlt))
              hsync.hcache_ne
              (fun hlt => hsync.hcache_lt (htcur_same ▸ hlt))
              hsync.hcache_eq
              (fun i hi => by
                have hne : i ≠ sIdx := by dsimp [hM'] at hi; omega
                rcases hsync.hbook_out i hi with ⟨hb, hm, hl⟩
                exact ⟨by dsimp [hM']; rw [Function.update_of_ne hne]; exact hb,
                       by rw [Function.update_of_ne hne]; exact hm,
                       fun hp => by rw [Function.update_of_ne hne]; exact hl hp⟩)
              (fun i hi => by
                by_cases hi_eq : i = sIdx
                · subst hi_eq
                  refine ⟨o.1, ?_, fun hlt => by rw [htcur_same, ← hPs] at hlt; omega, ?_⟩
                  · dsimp [hM']
                    rw [Function.update_self, Function.update_self, Function.update_self]
                    exact hinv_after
                  · intro Q ss' hQ_vS
                    by_cases hQP : Q = P
                    · subst hQP; simp [stL'] at hQ_vS; exact hQ_vS
                    · rw [Function.update_of_ne hQP] at hQ_vS
                      have hv := hsync.hvS Q; rw [hQ_vS] at hv
                      rcases hv with ⟨_, _, hQs, _⟩
                      exfalso; exact hQP (hQs.trans hPs.symm)
                · rcases hsync.hbook_in i hi with ⟨ss_i, hinv_i, hss1_i, hss2_i⟩
                  refine ⟨ss_i, ?_, fun hlt => hss1_i (htcur_same ▸ hlt), ?_⟩
                  · dsimp [hM']
                    rw [Function.update_of_ne hi_eq, Function.update_of_ne hi_eq, Function.update_of_ne hi_eq]
                    exact hinv_i
                  · intro Q ss' hQ_vS
                    by_cases hQP : Q = P
                    · subst hQP; simp [stL'] at hQ_vS; exfalso; exact hi_eq hQ_vS.2.symm
                    · rw [Function.update_of_ne hQP] at hQ_vS; exact hss2_i Q ss' hQ_vS)


private theorem transmitE_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × (LibsignalMsgPublicPart × Plain ℓ) × Option (BitVec 256))
    (hshort : qry.2.1.1.shortB = true)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((transmitE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.policy qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((transmitE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.policy qry).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((transmitE (hooksFSMulti cka prng fs Δcka mo false true) (2 + Δcka) qep mo.policy qry).run esM)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  by_cases htrans : ∃ s₁L,
      esL.g.epMgmt (2 + Δcka) qep qry.1 qry.2.2.isSome = some s₁L ∧
      mo.policy.leakDoom esL.g s₁L = false ∧
      healedBy s₁L.tL (2 + Δcka) t = false
  · rcases htrans with ⟨s₁L, hep, hdoom, hheal_f⟩
    have hc2 := transmitE_coupled_phase2 C Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qry hshort hqep hsync
      (fun hnone => by rw [hep] at hnone; cases hnone)
      (fun s₁L' hep' _ => by rw [hep] at hep'; injection hep' with heq; subst heq; exact hheal_f)
    exact Coupled2.to_coupled3_m2 _ hc2 fun _ _ _ => stepPost2_imp_stepPost3
  · refine transmitE_coupled_phase1_stay C Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qry hshort hqep hsync ?_
    intro s₁L hep hdoom
    cases hh : healedBy s₁L.tL (2 + Δcka) t
    · exfalso; exact htrans ⟨s₁L, hep, hdoom, hh⟩
    · rfl



/-! ### 7C.1 Deterministic `vRecv` / `commitE` / `deliverE` / `injectE` / `deliverForgeE` Run Lemmas -/

private theorem injectFull_auth_of_ne {Msg : Type} {t ep : ℕ} (hne : ep ≠ t) :
    (Config.auth (Msg := Msg) t).injectFull ep = false := by
  simp [Config.auth, beq_eq_false_iff_ne, hne]

private theorem receiverOf_ne_senderOf (ep : ℕ) :
    Party.receiverOf ep ≠ Party.senderOf ep := by
  unfold Party.receiverOf Party.senderOf Party.other
  split_ifs <;> decide

private theorem eraseSt_win_true {St₁ St₂ Msg C : Type}
    {g₁ : GameState St₁ Msg C} {g₂ : GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) :
    eraseSt { g₁ with win := true } = eraseSt { g₂ with win := true } := by
  have h1 : eraseSt { g₁ with win := true } = { eraseSt g₁ with win := true } := rfl
  have h2 : eraseSt { g₂ with win := true } = { eraseSt g₂ with win := true } := rfl
  rw [h1, h2, h]

private theorem function_update_idem {α : Sort _} [DecidableEq α] {β : α → Sort _}
    (f : ∀ a, β a) (a : α) (x y : β a) :
    Function.update (Function.update f a x) a y = Function.update f a y := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h]

private theorem accept_update_st_idem {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) (new : St) (pos : Pos) :
    { s.accept P new pos with st := Function.update (s.accept P new pos).st P new } =
      s.accept P new pos := by
  have hst : Function.update (s.accept P new pos).st P new = (s.accept P new pos).st := by
    funext Q
    dsimp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst hQ; simp
    · simp [hQ]
  rw [hst]

private theorem commitE_slotLocal_run {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (M_sess : ℕ)
    (s : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (old new : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) (pos : Pos)
    (es : EStateSlot Γ T Sig SS RS M E K I) :
    (commitE (hooksSlotLocal cka prng fs mo M_sess) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksSlotLocal, liftH_run, StateT.run_pure, accept_update_st_idem]

private theorem commitE_fsMulti_run {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (s : Ctx Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (old new : VP Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos)
    (es : EState (VP Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T Sig K I E)) :
    (commitE (hooksFSMulti cka prng fs Δcka mo gMain la) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksFSMulti, liftH_run, StateT.run_pure, accept_update_st_idem]

private theorem vRecv_guard_true_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) (h : HS)
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true) :
    (vRecv hk ctx P s c rec).run h = pure (some none, h) := by
  unfold vRecv
  simp [hg, StateT.run_pure]

private theorem vRecv_reuse_none_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) (h : HS)
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = false)
    (hne : c.1.1 ≠ s.tcur + 1)
    (hvR : s.vR c.1.1 = none) :
    (vRecv hk ctx P s c rec).run h = pure (some none, h) := by
  unfold vRecv
  simp [hg, hne, hvR, StateT.run_bind, StateT.run_pure]

private theorem vRecv_reuse_some_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) (h : HS)
    (v : RSv)
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = false)
    (hne : c.1.1 ≠ s.tcur + 1)
    (hvR : s.vR c.1.1 = some v) :
    (vRecv hk ctx P s c rec).run h =
      ((hk.fsRecv ctx P c.1.1 v c.1 c.2 rec).run h >>= fun r =>
        pure (match r.1 with
          | none => none
          | some none => some none
          | some (some (v', i, m)) =>
            some (some ({ s with vR := Function.update s.vR c.1.1 (some v') }, c.1.1, i, m)),
          r.2)) := by
  unfold vRecv
  simp only [hg, Bool.false_eq_true, ↓reduceIte, hne, StateT.run_bind, StateT.run_pure,
    pure_bind, hvR]
  congr 1
  funext r
  rcases r with ⟨(_ | _ | ⟨v', i, m⟩), h'⟩ <;> simp [StateT.run_pure]

private theorem vRecv_fresh_none_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) (h : HS)
    (_hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = false)
    (heq : c.1.1 = s.tcur + 1)
    (hTn : c.1.2 = none) :
    (vRecv hk ctx P s c rec).run h = pure (some none, h) := by
  unfold vRecv
  simp [heq, hTn, StateT.run_pure]

private theorem vRecv_fresh_some_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec : Option (Record M (Header T × E))) (h : HS)
    (Tn : T)
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = false)
    (heq : c.1.1 = s.tcur + 1)
    (hTn : c.1.2 = some Tn) :
    (vRecv hk ctx P s c rec).run h =
      ((hk.startRecv ctx P c.1.1 s.γ s.root Tn).run h >>= fun r1 =>
        match r1.1 with
        | none => pure (none, r1.2)
        | some none => pure (some none, r1.2)
        | some (some (γ', σ', rs)) =>
          (hk.fsRecv ctx P c.1.1 rs c.1 c.2 rec).run r1.2 >>= fun r2 =>
            pure (match r2.1 with
              | none => none
              | some none => some none
              | some (some (v', i, m)) =>
                some (some ({ s with tcur := c.1.1, γ := γ', root := σ',
                                     vR := Function.update s.vR c.1.1 (some v') }, c.1.1, i, m)),
              r2.2)) := by
  unfold vRecv
  dsimp only
  rw [hg]
  simp only [Bool.false_eq_true, ↓reduceIte, heq, hTn, StateT.run_bind, StateT.run_pure,
    pure_bind, bind_assoc]
  congr 1
  funext r1
  rcases r1 with ⟨(_ | _ | ⟨γ', σ', rs⟩), h1⟩
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp only [StateT.run_pure, pure_bind, Function.update_self, StateT.run_bind]
    congr 1
    funext r2
    rcases r2 with ⟨(_ | _ | ⟨v', i, m⟩), h2⟩ <;> simp [StateT.run_pure, function_update_idem]

private theorem deliverE_some_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) (P : Party) (c : Header T × E)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (r : Record M (Header T × E))
    (hhalt : (es.abort || es.g.win) = false)
    (htr : es.g.inTransit P.other c = some r) :
    (deliverE hk maxSkip (⟨true, tL, t⟩ : Mode).cfg (P, c)).run es =
      ((vRecv hk es.g P (es.g.st P) c (some r)).run es.h >>= fun p =>
        match p.1 with
        | none => pure (none, { es with abort := true, h := p.2 })
        | some none => pure (some .rejected, { es with h := p.2 })
        | some (some (st', t', i', m')) =>
          (commitE hk es.g P (es.g.st P) st' r.pos).run { es with h := p.2 } >>= fun q =>
            match q.1 with
            | none => pure (none, q.2)
            | some s₁ =>
              pure (some (.accepted t' i' (if es.g.chall.contains r.pos then none else some m')),
                    { q.2 with g := s₁ })) := by
  have hdw : (⟨true, tL, t⟩ : Mode).cfg.deliverWin (Msg := M) = false := rfl
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hhalt, Bool.false_eq_true, ↓reduceIte,
    htr, hdw, Bool.false_and, liftH_run, bind_assoc]
  congr 1
  funext p
  rcases p with ⟨(_ | _ | ⟨st', t', i', m'⟩), h'⟩
  · simp [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure]
  · simp [StateT.run_pure]
  · simp only [pure_bind, StateT.run_bind]
    congr 1
    funext q
    rcases q with ⟨(_ | s₁), es'⟩ <;> simp [StateT.run_modify, StateT.run_pure]

private theorem injectE_active_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep : ℕ) (cfg : Config M) (P : Party) (c : Header T × E)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (hg : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ)) = false) :
    (injectE hk Δ qep cfg (P, c)).run es =
      ((vRecv hk es.g P (es.g.st P) c none).run es.h >>= fun p =>
        match p.1 with
        | none => pure (none, { es with abort := true, h := p.2 })
        | some none => pure (some .rejected, { es with h := p.2 })
        | some (some (st', t', i', m')) =>
          if qep + 1 < t' then pure (some .rejected, { es with h := p.2 })
          else
            let pos : Pos := ⟨P.other, t', i'⟩
            if es.g.trivial Δ pos then
              (commitE hk es.g P (es.g.st P) st' pos).run { es with h := p.2 } >>= fun q =>
                match q.1 with
                | none => pure (none, q.2)
                | some s₁ => pure (some (.accepted t' i' (some m')), { q.2 with g := s₁ })
            else
              if cfg.injectFull t' then
                pure (some .rejected, { es with g := { es.g with win := true }, h := p.2 })
              else
                pure (some .rejected, { es with h := p.2 })) := by
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, Bool.false_eq_true, ↓reduceIte,
    liftH_run, bind_assoc]
  congr 1
  funext p
  rcases p with ⟨(_ | _ | ⟨st', t', i', m'⟩), h'⟩
  · simp [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure]
  · simp [StateT.run_pure]
  · simp only [pure_bind]
    by_cases hlt : qep + 1 < t'
    · simp [hlt, StateT.run_pure]
    · simp only [hlt, ↓reduceIte]
      by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
      · simp only [htriv, ↓reduceIte, StateT.run_bind]
        congr 1
        funext q
        rcases q with ⟨(_ | s₁), es'⟩ <;> simp [StateT.run_modify, StateT.run_pure]
      · simp only [Bool.not_eq_true] at htriv
        simp only [htriv, Bool.false_eq_true, ↓reduceIte]
        by_cases hinj : cfg.injectFull t' = true
        · simp [hinj, StateT.run_bind, StateT.run_modify, StateT.run_pure]
        · simp only [Bool.not_eq_true] at hinj
          simp [hinj, StateT.run_pure]

private theorem deliverForgeE_active_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep : ℕ) (cfg : Config M) (P : Party) (c c' : Header T × E)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (r : Record M (Header T × E))
    (hhalt : (es.abort || es.g.win) = false)
    (htr : es.g.inTransit P.other c = some r)
    (hg : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = false) :
    (deliverForgeE hk Δ qep cfg (P, c, c')).run es =
      ((vRecv hk es.g P (es.g.st P) c' none).run es.h >>= fun p =>
        match p.1 with
        | none => pure (none, { es with abort := true, h := p.2 })
        | some none => pure (some .rejected, { es with h := p.2 })
        | some (some (st', t', i', m')) =>
          if qep + 1 < t' || t' != r.pos.epoch then pure (some .rejected, { es with h := p.2 })
          else
            let pos : Pos := ⟨P.other, t', i'⟩
            if es.g.trivial Δ pos then
              (commitE hk es.g P (es.g.st P) st' pos).run { es with h := p.2 } >>= fun q =>
                match q.1 with
                | none => pure (none, q.2)
                | some s₁ => pure (some (.accepted t' i' (some m')), { q.2 with g := s₁ })
            else
              if cfg.injectFull t' then
                pure (some .rejected, { es with g := { es.g with win := true }, h := p.2 })
              else
                pure (some .rejected, { es with h := p.2 })) := by
  unfold deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hhalt, Bool.false_eq_true, ↓reduceIte,
    htr, hg, liftH_run, bind_assoc]
  congr 1
  funext p
  rcases p with ⟨(_ | _ | ⟨st', t', i', m'⟩), h'⟩
  · simp [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure]
  · simp [StateT.run_pure]
  · simp only [pure_bind]
    by_cases hlt : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
    · simp [hlt, StateT.run_pure]
    · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
      by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
      · simp only [htriv, ↓reduceIte, StateT.run_bind]
        congr 1
        funext q
        rcases q with ⟨(_ | s₁), es'⟩ <;> simp [StateT.run_modify, StateT.run_pure]
      · simp only [Bool.not_eq_true] at htriv
        simp only [htriv, Bool.false_eq_true, ↓reduceIte]
        by_cases hinj : cfg.injectFull t' = true
        · simp [hinj, StateT.run_bind, StateT.run_modify, StateT.run_pure]
        · simp only [Bool.not_eq_true] at hinj
          simp [hinj, StateT.run_pure]

/-! ### 7C.2 `SyncPaperMulti` Preservation Helpers for `vRecv` -/

private theorem SyncPaperMulti.with_hL_eq {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {ℓ : ℕ}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem esL esM tblM tblL)
    {hL' : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt}
    (hused : hL'.usedSlot = esL.h.usedSlot)
    (hcache : hL'.loc.cache = esL.h.loc.cache)
    (htable : hL'.loc.table = esL.h.loc.table)
    (hsess : hL'.loc.sessions = esL.h.loc.sessions) :
    SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem
      { esL with h := hL' } esM tblM tblL :=
  { hsync with
    hsess := hsync.hsess.trans hsess.symm
    hnodup := hsess ▸ hsync.hnodup
    hlen := hsess ▸ hsync.hlen
    hused := fun i => by dsimp; rw [hused, hsess]; exact hsync.hused i
    htH_empty := fun htH hlt => by dsimp; rw [hsess]; exact hsync.htH_empty htH hlt
    htblL_lk := fun htH Ik => by dsimp; rw [htable, hsess]; exact hsync.htblL_lk htH Ik
    hcache_ne := fun ep hne => by dsimp; rw [hcache]; exact hsync.hcache_ne ep hne
    hcache_lt := fun hlt => by dsimp; rw [hcache]; exact hsync.hcache_lt hlt
    hcache_eq := by dsimp; rw [hcache]; exact hsync.hcache_eq }

private theorem senderOf_tcur_lt_iff_of_vRecv {Γ T Sig SS RS : Type}
    (st : Party → VP Γ T Sig SS RS) (P : Party) (st' : VP Γ T Sig SS RS) (ep t : ℕ)
    (hsends : P.sendsIn ep = false)
    (hle : ep ≤ (st P).tcur + 1)
    (htcur : st'.tcur = max (st P).tcur ep) :
    (Function.update st P st' (Party.senderOf t)).tcur < t ↔ (st (Party.senderOf t)).tcur < t := by
  by_cases hPs : Party.senderOf t = P
  · have hep_ne : ep ≠ t := by
      intro heq
      subst heq
      have hPr := party_eq_receiverOf_of_sendsIn_false P ep hsends
      exact receiverOf_ne_senderOf ep (hPr.symm.trans hPs.symm)
    rw [hPs, Function.update_self, htcur]
    have : max (st P).tcur ep = (st P).tcur ∨ max (st P).tcur ep = ep := max_choice _ _
    rcases this with h | h <;> omega
  · simp [hPs]

private theorem hbook_after_startRecv_at_t {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 (rem + 1) esL esM tblM tblL)
    (hvR_none : (esL.g.st (Party.receiverOf t)).vR t = none)
    {hM₁ : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    (hbook_eq : hM₁.book = esM.h.book)
    (hsess_le : esM.h.sessions.length ≤ hM₁.sessions.length) :
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    (∀ i, hM₁.sessions.length ≤ i →
      hM₁.book i = none ∧ tblM i = hInit (bs i) (.seed (ks i)) ∧
        (phase1 = true → tblL i = hInit (bs i) (.seed (ks i)))) ∧
    (∀ i, i < hM₁.sessions.length →
      ∃ ss_i,
        ActiveSessInv C ℓ encT idOf phase1 (ks i) ss_i (fs.initReceiver (ks i))
          ((hM₁.book i).getD {}) (tblM i) (tblL i) ∧
        ((esL.g.st (Party.senderOf t)).tcur < t → ss_i = fs.initSender (ks i)) ∧
        (∀ Q ss, (esL.g.st Q).vS = some (ss, some i) → ss_i = ss)) := by
  intro fs
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hbook_eq]
    exact hsync.hbook_out i (Nat.le_trans hsess_le hi)
  · by_cases hi_old : i < esM.h.sessions.length
    · have hbi := hsync.hbook_in i hi_old
      dsimp only at hbi
      rw [hvR_none, ← hbook_eq] at hbi
      exact hbi
    · have hi_ge : esM.h.sessions.length ≤ i := Nat.le_of_not_lt hi_old
      rcases hsync.hbook_out i hi_ge with ⟨hb0, hm0, hl0⟩
      refine ⟨fs.initSender (ks i), ?_, fun _ => rfl, ?_⟩
      · rw [hbook_eq, hb0, Option.getD_none, hm0]
        cases phase1
        · exact activeSessInv_to_phase2 C ℓ encT idOf (activeSessInv_init C ℓ encT idOf true (ks i) (bs i))
        · rw [hl0 rfl]
          exact activeSessInv_init C ℓ encT idOf true (ks i) (bs i)
      · intro Q ss hQ_vS
        have hv := hsync.hvS Q
        rw [hQ_vS] at hv
        omega

private theorem syncPaperMulti_after_vRecv_reject {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL tblM' tblL' : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 (rem + 1) esL esM tblM tblL)
    {hL' : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt}
    {hM' : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    (hbk' : HookBookInv M_sess t tL ks rem hL' hM')
    (hsess_le : esM.h.sessions.length ≤ hM'.sessions.length)
    (htH_sess : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = true →
      hM'.sessions = esM.h.sessions)
    (hcacheL : hL'.loc.cache = esL.h.loc.cache)
    (hcacheM : hM'.cache = esM.h.cache)
    (hlfM : hM'.lfWin = esM.h.lfWin)
    (hbook_out' : ∀ i, hM'.sessions.length ≤ i →
      hM'.book i = none ∧ tblM' i = hInit (bs i) (.seed (ks i)) ∧
        (phase1 = true → tblL' i = hInit (bs i) (.seed (ks i))))
    (hbook_in' : ∀ i, i < hM'.sessions.length →
      let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
      let rs_i := match (esL.g.st (Party.receiverOf t)).vR t with
        | some (rs, some j) => if j = i then rs else fs.initReceiver (ks i)
        | _ => fs.initReceiver (ks i)
      ∃ ss_i,
        ActiveSessInv C ℓ encT idOf phase1 (ks i) ss_i rs_i
          ((hM'.book i).getD {}) (tblM' i) (tblL' i) ∧
        ((esL.g.st (Party.senderOf t)).tcur < t → ss_i = fs.initSender (ks i)) ∧
        (∀ Q ss, (esL.g.st Q).vS = some (ss, some i) → ss_i = ss)) :
    SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem
      { esL with h := hL' } { esM with h := hM' } tblM' tblL' :=
  { hsync with
    hlf := fun hp => by dsimp; rw [hlfM]; exact hsync.hlf hp
    hvS := fun Q => by
      dsimp
      have hv := hsync.hvS Q
      cases hQ : (esL.g.st Q).vS with
      | none => rw [hQ] at hv; exact hv
      | some so =>
        rcases so with ⟨ss, (_ | sIdx)⟩
        · rw [hQ] at hv; exact hv
        · rw [hQ] at hv
          exact ⟨hv.1, Nat.lt_of_lt_of_le hv.2.1 hsess_le, hv.2.2⟩
    hvR_eq := fun Q => by
      dsimp
      have hv := hsync.hvR_eq Q
      cases hQ : (esL.g.st Q).vR t with
      | none => rw [hQ] at hv; exact hv
      | some ro =>
        rw [hQ] at hv
        rcases hv with ⟨sIdx, h1, h2, hlt, h3, h4⟩
        exact ⟨sIdx, h1, h2, Nat.lt_of_lt_of_le hlt hsess_le, h3, h4⟩
    hsess := hbk'.hsess
    hnodup := hbk'.hnodup
    hlen := hbk'.hlen
    hused := hbk'.hused
    htH_empty := fun htH hlt => by
      dsimp
      rw [← hbk'.hsess, htH_sess htH, hsync.hsess]
      exact hsync.htH_empty htH hlt
    htblL_lk := hbk'.htblL_lk
    htblM_lk := hbk'.htblM_lk
    hcache_ne := fun ep hne => by dsimp; rw [hcacheL, hcacheM]; exact hsync.hcache_ne ep hne
    hcache_lt := fun hlt => by dsimp; rw [hcacheL, hcacheM]; exact hsync.hcache_lt hlt
    hcache_eq := by
      dsimp; rw [hcacheL, hcacheM]
      have hc := hsync.hcache_eq
      cases hct : esL.h.loc.cache t with
      | none => rw [hct] at hc; exact hc
      | some co =>
        rw [hct] at hc
        rcases hc with ⟨sIdx, kM, h1, h2, hlt, h4⟩
        exact ⟨sIdx, kM, h1, h2, Nat.lt_of_lt_of_le hlt hsess_le, h4⟩
    hbook_out := hbook_out'
    hbook_in := hbook_in' }

private theorem syncPaperMulti_after_accept {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {Δcka M_sess t : ℕ} {tL : Option ℕ}
    {ks : ℕ → BitVec 256} {bs : ℕ → Bool} {phase1 : Bool} {rem : ℕ}
    {esL : _} {esM : _} {tblM tblL tblM' tblL' : ℕ → SessHSt Pt ℓ}
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 (rem + 1) esL esM tblM tblL)
    {P : Party} {ep : ℕ} {pos : Pos}
    (hpos_ep : pos.epoch = ep)
    (hsends_f : P.sendsIn ep = false)
    (hle_tcur : ep ≤ (esL.g.st P).tcur + 1)
    {stL' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)}
    {stM' : VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)}
    {rsvL' : RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ}
    {rsvM' : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ}
    {hL' : LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt}
    {hM' : FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)}
    (hst_id : stL'.id = P ∧ stM'.id = P)
    (hst_tcur : stL'.tcur = max (esL.g.st P).tcur ep ∧ stM'.tcur = stL'.tcur)
    (hst_γ : stM'.γ = stL'.γ)
    (hst_root : stM'.root = stL'.root)
    (hst_cka : stM'.curCkaMsg = stL'.curCkaMsg)
    (hst_vS : stL'.vS = (esL.g.st P).vS ∧ stM'.vS = (esM.g.st P).vS)
    (hst_vR : stL'.vR = Function.update (esL.g.st P).vR ep (some rsvL') ∧
              stM'.vR = Function.update (esM.g.st P).vR ep (some rsvM'))
    (hrsv : (ep ≠ t ∧ ∃ rs', rsvL' = (rs', none) ∧ rsvM' = .inl rs') ∨
            (ep = t ∧ ∃ rsLoc' sIdx, rsvL' = (rsLoc', some sIdx) ∧ rsvM' = .inr sIdx ∧ sIdx < hM'.sessions.length))
    (hbk' : HookBookInv M_sess t tL ks rem hL' hM')
    (hsess_le : esM.h.sessions.length ≤ hM'.sessions.length)
    (htH_sess : (tL.isSome && decide (t = (⟨true, tL, t⟩ : Mode).tH)) = true →
      hM'.sessions = esM.h.sessions)
    (hcacheL : hL'.loc.cache = esL.h.loc.cache)
    (hcacheM : hM'.cache = esM.h.cache)
    (hlfM : hM'.lfWin = esM.h.lfWin)
    (hbook_out' : ∀ i, hM'.sessions.length ≤ i →
      hM'.book i = none ∧ tblM' i = hInit (bs i) (.seed (ks i)) ∧
        (phase1 = true → tblL' i = hInit (bs i) (.seed (ks i))))
    (hbook_in' : ∀ i, i < hM'.sessions.length →
      let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
      let rs_i := match (Function.update esL.g.st P stL' (Party.receiverOf t)).vR t with
        | some (rs, some j) => if j = i then rs else fs.initReceiver (ks i)
        | _ => fs.initReceiver (ks i)
      ∃ ss_i,
        ActiveSessInv C ℓ encT idOf phase1 (ks i) ss_i rs_i
          ((hM'.book i).getD {}) (tblM' i) (tblL' i) ∧
        ((esL.g.st (Party.senderOf t)).tcur < t → ss_i = fs.initSender (ks i)) ∧
        (∀ Q ss, (esL.g.st Q).vS = some (ss, some i) → ss_i = ss)) :
    SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs phase1 rem
      { esL with g := esL.g.accept P stL' pos, h := hL' }
      { esM with g := esM.g.accept P stM' pos, h := hM' }
      tblM' tblL' := by
  have htcur_mono : ∀ Q, (esL.g.st Q).tcur ≤ (Function.update esL.g.st P stL' Q).tcur := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ; simp [hst_tcur.1]
    · simp [hQ]
  have htcur_sender_iff := senderOf_tcur_lt_iff_of_vRecv esL.g.st P stL' ep t hsends_f hle_tcur hst_tcur.1
  have hvS_stL : ∀ Q, (Function.update esL.g.st P stL' Q).vS = (esL.g.st Q).vS := by
    intro Q; by_cases hQ : Q = P
    · subst hQ; simp [hst_vS.1]
    · simp [hQ]
  have hvS_stM : ∀ Q, (Function.update esM.g.st P stM' Q).vS = (esM.g.st Q).vS := by
    intro Q; by_cases hQ : Q = P
    · subst hQ; simp [hst_vS.2]
    · simp [hQ]
  refine
    { habL := hsync.habL, habM := hsync.habM
      hwinL := hsync.hwinL, hwinM := hsync.hwinM
      hbL := hsync.hbL, hbM := hsync.hbM
      herase := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_accept hsync.herase P stL' stM' pos
      htrans_ep := fun r hr => by
        dsimp only [GameState.accept, GameState.delete] at hr
        exact hsync.htrans_ep r (List.mem_of_mem_filter hr)
      hlf := fun hp => by dsimp; rw [hlfM]; exact hsync.hlf hp
      hhealed := fun hp => hsync.hhealed hp
      hidL := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_id.1]
        · simp [hQ, hsync.hidL Q]
      hidM := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_id.2]
        · simp [hQ, hsync.hidM Q]
      htcurL := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ
          simp only [Function.update_self, hst_tcur.1, hsync.htcurL Q, hpos_ep]
        · simp [hQ, hsync.htcurL Q]
      htcurM := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_tcur.2]
        · simp [hQ, hsync.htcurM Q]
      hγ := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_γ]
        · simp [hQ, hsync.hγ Q]
      hroot := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_root]
        · simp [hQ, hsync.hroot Q]
      hckaMsg := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ; simp [hst_cka]
        · simp [hQ, hsync.hckaMsg Q]
      hvS := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        rw [hvS_stL Q, hvS_stM Q]
        have hv := hsync.hvS Q
        cases hQ : (esL.g.st Q).vS with
        | none => rw [hQ] at hv; exact hv
        | some so =>
          rcases so with ⟨ss, (_ | sIdx)⟩
          · rw [hQ] at hv; exact hv
          · rw [hQ] at hv
            exact ⟨hv.1, Nat.lt_of_lt_of_le hv.2.1 hsess_le, hv.2.2.1,
              Nat.le_trans hv.2.2.2 (htcur_mono Q)⟩
      hvR_hi := fun Q ep' hhi => by
        dsimp only [GameState.accept, GameState.delete] at hhi ⊢
        by_cases hQ : Q = P
        · subst hQ
          simp only [Function.update_self] at hhi ⊢
          have hep_ne : ep' ≠ ep := by
            intro heq
            subst heq
            rcases hhi with hlt | hs
            · rw [hst_tcur.1] at hlt; omega
            · rw [hsends_f] at hs; cases hs
          rw [hst_vR.1, hst_vR.2, Function.update_of_ne hep_ne, Function.update_of_ne hep_ne]
          apply hsync.hvR_hi Q ep'
          rcases hhi with hlt | hs
          · rw [hst_tcur.1] at hlt; exact Or.inl (by omega)
          · exact Or.inr hs
        · simp only [Function.update_of_ne hQ] at hhi ⊢
          exact hsync.hvR_hi Q ep' hhi
      hvR_ne := fun Q ep' hne => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ
          simp only [Function.update_self, hst_vR.1, hst_vR.2]
          by_cases heq : ep' = ep
          · subst heq
            rcases hrsv with ⟨_, rs', rfl, rfl⟩ | ⟨rfl, _⟩
            · simp
            · exact absurd rfl hne
          · rw [Function.update_of_ne heq, Function.update_of_ne heq]
            exact hsync.hvR_ne Q ep' hne
        · simp only [Function.update_of_ne hQ]
          exact hsync.hvR_ne Q ep' hne
      hvR_eq := fun Q => by
        dsimp only [GameState.accept, GameState.delete]
        by_cases hQ : Q = P
        · subst hQ
          simp only [Function.update_self, hst_vR.1, hst_vR.2]
          by_cases heq : t = ep
          · subst heq
            rcases hrsv with ⟨hne, _⟩ | ⟨_, rsLoc', sIdx, rfl, rfl, hsIdx_lt⟩
            · exact absurd rfl hne
            · simp only [Function.update_self]
              exact ⟨sIdx, rfl, rfl, hsIdx_lt, by rw [hst_tcur.1]; exact Nat.le_max_right _ _,
                party_eq_receiverOf_of_sendsIn_false Q t hsends_f⟩
          · rw [Function.update_of_ne heq, Function.update_of_ne heq]
            have hv := hsync.hvR_eq Q
            cases hQv : (esL.g.st Q).vR t with
            | none => rw [hQv] at hv; exact hv
            | some ro =>
              rw [hQv] at hv
              rcases hv with ⟨sIdx, h1, h2, hlt, hle, hPr⟩
              exact ⟨sIdx, h1, h2, Nat.lt_of_lt_of_le hlt hsess_le,
                by rw [hst_tcur.1]; exact Nat.le_trans hle (Nat.le_max_left _ _), hPr⟩
        · simp only [Function.update_of_ne hQ]
          have hv := hsync.hvR_eq Q
          cases hQv : (esL.g.st Q).vR t with
          | none => rw [hQv] at hv; exact hv
          | some ro =>
            rw [hQv] at hv
            rcases hv with ⟨sIdx, h1, h2, hlt, hle, hPr⟩
            exact ⟨sIdx, h1, h2, Nat.lt_of_lt_of_le hlt hsess_le, hle, hPr⟩
      hsess := hbk'.hsess
      hnodup := hbk'.hnodup
      hlen := hbk'.hlen
      hused := hbk'.hused
      htH_empty := fun htH hlt => by
        dsimp only [GameState.accept, GameState.delete] at hlt ⊢
        rw [← hbk'.hsess, htH_sess htH, hsync.hsess]
        exact hsync.htH_empty htH (htcur_sender_iff.mp hlt)
      htblL_lk := hbk'.htblL_lk
      htblM_lk := hbk'.htblM_lk
      hcache_ne := fun ep' hne => by dsimp; rw [hcacheL, hcacheM]; exact hsync.hcache_ne ep' hne
      hcache_lt := fun hlt => by
        dsimp only [GameState.accept, GameState.delete] at hlt ⊢
        rw [hcacheL, hcacheM]
        exact hsync.hcache_lt (htcur_sender_iff.mp hlt)
      hcache_eq := by
        dsimp; rw [hcacheL, hcacheM]
        have hc := hsync.hcache_eq
        cases hct : esL.h.loc.cache t with
        | none => rw [hct] at hc; exact hc
        | some co =>
          rw [hct] at hc
          rcases hc with ⟨sIdx, kM, h1, h2, hlt, h4⟩
          exact ⟨sIdx, kM, h1, h2, Nat.lt_of_lt_of_le hlt hsess_le, h4⟩
      hbook_out := hbook_out'
      hbook_in := fun i hi => by
        dsimp only [GameState.accept, GameState.delete]
        rcases hbook_in' i hi with ⟨ss_i, hinv, hss1, hss2⟩
        refine ⟨ss_i, hinv, fun hlt => hss1 (htcur_sender_iff.mp hlt), fun Q ss hQv => ?_⟩
        rw [hvS_stL Q] at hQv
        exact hss2 Q ss hQv }

private def VRecvPost2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) (rem : ℕ)
    (P : Party) (ep : ℕ)
    (esL : EStateSlot (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) Pt)
    (esM : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)
      (FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (rL : Option (Option (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ) ×
      ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
      LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt)
    (rM : (Option (Option (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
      ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
      FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) : Prop :=
  rL.1 = none ∨
  (rL.1 = some none ∧ rM.1.1 = some none ∧
    ∃ tblM' tblL', rM.2 = (fun _ => false, tblM') ∧
      SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false rem
        { esL with h := rL.2 } { esM with h := rM.1.2 } tblM' tblL') ∨
  (∃ stL' stM' i' m' tblM' tblL',
    rL.1 = some (some (stL', ep, i', m')) ∧
    rM.1.1 = some (some (stM', ep, i', m')) ∧
    rM.2 = (fun _ => false, tblM') ∧
    P.sendsIn ep = false ∧ ep ≤ qep + 1 ∧
    (∀ pos : Pos, pos.epoch = ep →
      SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false rem
        { esL with g := esL.g.accept P stL' pos, h := rL.2 }
        { esM with g := esM.g.accept P stM' pos, h := rM.1.2 } tblM' tblL') ∧
    (ep ≠ t →
      SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false rem
        { esL with h := rL.2 } { esM with h := rM.1.2 } tblM' tblL'))

private def VRecvPost3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) (rem : ℕ)
    (P : Party) (ep : ℕ)
    (esL : EStateSlot (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) (BitVec 256) Pt)
    (esM : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × ℕ × LibsignalCiphertextWithSalt32)
      (FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (rL : Option (Option (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) × Option ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ) ×
      ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
      LocalSlotState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt)
    (r₀ r₁ : (Option (Option (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt CryptoGames.Ratchet.RootKey
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) ×
      ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) ×
      FSMultiState Pt CryptoGames.Ratchet.RootKey (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) ×
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) : Prop :=
  rL.1 = none ∨
  (r₁.1.1 = none ∧ r₁.1.2.lfWin = true) ∨
  (rL.1 = some none ∧ r₀.1.1 = some none ∧ r₁.1.1 = some none ∧ r₁.1.2 = r₀.1.2 ∧
    ∃ tblM' tblL', r₀.2 = (fun _ => false, tblM') ∧ r₁.2 = (fun _ => false, tblL') ∧
      SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true rem
        { esL with h := rL.2 } { esM with h := r₀.1.2 } tblM' tblL') ∨
  (∃ stL' stM' i' m' tblM' tblL',
    rL.1 = some (some (stL', ep, i', m')) ∧
    r₀.1.1 = some (some (stM', ep, i', m')) ∧
    r₁.1.1 = some (some (stM', ep, i', m')) ∧
    r₁.1.2 = r₀.1.2 ∧
    r₀.2 = (fun _ => false, tblM') ∧ r₁.2 = (fun _ => false, tblL') ∧
    P.sendsIn ep = false ∧ ep ≤ qep + 1 ∧
    (∀ pos : Pos, pos.epoch = ep →
      SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true rem
        { esL with g := esL.g.accept P stL' pos, h := rL.2 }
        { esM with g := esM.g.accept P stM' pos, h := r₀.1.2 } tblM' tblL') ∧
    (ep ≠ t →
      SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true rem
        { esL with h := rL.2 } { esM with h := r₀.1.2 } tblM' tblL'))



/-! ### 7C.3 `vRecv_coupled2` and `vRecv_coupled3` -/

private theorem vRecv_coupled2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (P : Party) (c : Fig8C Pt)
    (recL recM : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (VRecvPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem P c.1.1 esL esM)
      (simulateQ (keySlotFixedImpl ks)
        ((vRecv (hooksSlotLocal cka prng fs mo M_sess) esL.g P (esL.g.st P) c recL).run esL.h))
      ((simulateQ (pubFsMultiImpl implF)
        ((vRecv (hooksFSMulti cka prng fs Δcka mo false false) esM.g P (esM.g.st P) c recM).run esM.h)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  have hheal_M : healedBy esM.g.tL (2 + Δcka) t = false := by
    rw [← _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_tL hsync.herase]
    exact hsync.hhealed rfl
  by_cases hgL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = true
  · have hgM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = true := by
      simpa [hsync.hidL P, hsync.hidM P, hsync.htcurM P] using hgL
    rw [vRecv_guard_true_run _ _ _ _ _ _ _ hgL, vRecv_guard_true_run _ _ _ _ _ _ _ hgM]
    simp only [simulateQ_pure, StateT.run_pure]
    exact Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM, tblL, rfl, hsync.mono_rem (Nat.le_succ rem)⟩))
  · simp only [Bool.not_eq_true] at hgL
    have hgM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
      simpa [hsync.hidL P, hsync.hidM P, hsync.htcurM P] using hgL
    have ⟨hsends_id, hnot_lt⟩ := Bool.or_eq_false_iff.mp hgL
    have hsends_f : P.sendsIn c.1.1 = false := by rwa [hsync.hidL P] at hsends_id
    have hle_tcur : c.1.1 ≤ (esL.g.st P).tcur + 1 := by
      simp only [decide_eq_false_iff_not] at hnot_lt; omega
    have hle_qep : c.1.1 ≤ qep + 1 :=
      epochQepInv_vRecv_le hqep hsends_f (by rwa [hsync.htcurL P] at hle_tcur)
    by_cases hfresh : c.1.1 = (esL.g.st P).tcur + 1
    · have hfreshM : c.1.1 = (esM.g.st P).tcur + 1 := by rw [hsync.htcurM P]; exact hfresh
      cases hTn : c.1.2 with
      | none =>
        rw [vRecv_fresh_none_run _ _ _ _ _ _ _ hgL hfresh hTn,
            vRecv_fresh_none_run _ _ _ _ _ _ _ hgM hfreshM hTn]
        simp only [simulateQ_pure, StateT.run_pure]
        exact Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM, tblL, rfl, hsync.mono_rem (Nat.le_succ rem)⟩))
      | some Tn =>
        rw [vRecv_fresh_some_run _ _ _ _ _ _ _ Tn hgL hfresh hTn,
            vRecv_fresh_some_run _ _ _ _ _ _ _ Tn hgM hfreshM hTn,
            hsync.hγ P, hsync.hroot P, simulateQ_bind, simulateQ_bind, StateT.run_bind]
        refine Coupled2.bind
          ((startRecv_coupled3 (impl₀ := implF) (impl₁ := implF)
            (s₀ := (fun _ => false, tblM)) (s₁ := (fun _ => false, tblM))
            C Dh encPt encT idOf Δcka M_sess t c.1.1 rem tL ks esL.g esM.g P
            hsync.hookBookInv hsync.hcache_ne hsync.hcache_eq
            (esL.g.st P).γ (esL.g.st P).root Tn).to_coupled2) ?_
        rintro ⟨r1L_val, hL₁⟩ ⟨⟨r1M_val, hM₁⟩, s1⟩
          ⟨_, _, rfl, _, hbk1, hcacheL1, hcacheM1, hbookM1, hlfM1, ⟨J, hsess1⟩, hcases1⟩
        have hsess_le1 : esM.h.sessions.length ≤ hM₁.sessions.length := by
          rcases hsess1 with h | ⟨_, h⟩
          · rw [h]
          · rw [h]; simp
        have htH_sess1 : (tL.isSome && decide (t = mo.tH)) = true → hM₁.sessions = esM.h.sessions := by
          intro htH
          rcases hsess1 with h | ⟨hf, _⟩
          · exact h
          · rw [htH] at hf; cases hf
        rcases hcases1 with ⟨hrL, hrM, _, hhL, hhM⟩ | ⟨hrL, hrM, _, hhL, hhM⟩ |
            ⟨hep_t, γ', σ', sIdx, hrL, hrM, _, hsIdx_lt⟩ | ⟨hep_ne, γ', σ', k, hrL, hrM, _, hhL, hhM⟩
        · dsimp only at hrL hrM; subst r1L_val r1M_val
          simp only [simulateQ_pure, StateT.run_pure]
          exact Coupled2.pure (Or.inl rfl)
        · dsimp only at hrL hrM hhL hhM; subst r1L_val r1M_val hL₁ hM₁
          simp only [simulateQ_pure, StateT.run_pure]
          exact Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM, tblL, rfl, hsync.mono_rem (Nat.le_succ rem)⟩))
        · dsimp only at hep_t hrL hrM hsIdx_lt; subst r1L_val r1M_val
          simp only [simulateQ_bind, StateT.run_bind]
          have hPr : P = Party.receiverOf t := by
            apply party_eq_receiverOf_of_sendsIn_false; simpa [hep_t] using hsends_f
          have hvR_none : (esL.g.st (Party.receiverOf t)).vR t = none :=
            (hsync.hvR_hi (Party.receiverOf t) t (Or.inl (by rw [← hPr]; omega))).1
          have ⟨hbook_out1, hbook_in1⟩ := hbook_after_startRecv_at_t hsync hvR_none hbookM1 hsess_le1
          rcases hbook_in1 sIdx hsIdx_lt with ⟨ssLoc, hinv1, hss1, hss2⟩
          refine Coupled2.bind
            (fsRecv_coupled2 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              (fun _ => hheal_M) hL₁ hM₁ tblM tblL
              (fs.initReceiver (ks sIdx), some sIdx) (.inr sIdx) ssLoc c.1 c.2 recL recM
              (Or.inr ⟨hep_t, fs.initReceiver (ks sIdx), sIdx, rfl, rfl, hsIdx_lt, hinv1⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ ⟨⟨r2M_val, hM'⟩, s2⟩
            ⟨hused2, hcacheL2, htableL2, hsessL2, _, hM'_tmp, tblM', rfl, rfl,
              hcacheM2, htableM2, hsessM2, hlfM2, hother2, hrec_cases⟩
          simp only [simulateQ_pure, StateT.run_pure]
          have hbk2 : HookBookInv M_sess t tL ks rem hL₂ hM' :=
            { hsess := hsessM2.trans (hbk1.hsess.trans hsessL2.symm)
              hnodup := hsessL2 ▸ hbk1.hnodup
              hlen := hsessL2 ▸ hbk1.hlen
              hused := fun i => by rw [hused2, hsessL2]; exact hbk1.hused i
              htblL_lk := fun htH Ik => by rw [htableL2, hsessL2]; exact hbk1.htblL_lk htH Ik
              htblM_lk := fun htH Ik => by rw [htableM2, hsessM2]; exact hbk1.htblM_lk htH Ik }
          have hsess_le2 : esM.h.sessions.length ≤ hM'.sessions.length := by rw [hsessM2]; exact hsess_le1
          have htH_sess2 : (tL.isSome && decide (t = mo.tH)) = true → hM'.sessions = esM.h.sessions :=
            fun htH => hsessM2.trans (htH_sess1 htH)
          have hbook_out2 : ∀ i, hM'.sessions.length ≤ i →
              hM'.book i = none ∧ tblM' i = hInit (bs i) (.seed (ks i)) ∧
                (false = true → tblL i = hInit (bs i) (.seed (ks i))) := by
            intro i hi
            rw [hsessM2] at hi
            have hne : i ≠ sIdx := by omega
            rw [(hother2 i hne).1, (hother2 i hne).2]
            exact hbook_out1 i hi
          cases hrec : fs.receive (fs.initReceiver (ks sIdx)) c.1 c.2 with
          | none =>
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M, hinv2⟩
            dsimp only at hr2L hr2M; subst r2L_val r2M_val
            refine Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM', tblL, rfl, ?_⟩))
            refine syncPaperMulti_after_vRecv_reject hsync hbk2 hsess_le2 htH_sess2
              (hcacheL2.trans hcacheL1) (hcacheM2.trans hcacheM1) (hlfM2.trans hlfM1) hbook_out2 ?_
            intro i hi
            rw [hvR_none]
            by_cases hi_eq : i = sIdx
            · subst hi_eq; exact ⟨ssLoc, hinv2, hss1, hss2⟩
            · rw [(hother2 i hi_eq).1, (hother2 i hi_eq).2]
              exact hbook_in1 i (by rwa [← hsessM2])
          | some o =>
            rcases o with ⟨rsLoc', idxOut, pmOut⟩
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M, hinv2⟩
            dsimp only at hr2L hr2M; subst r2L_val r2M_val
            refine Coupled2.pure (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM', tblL, rfl, rfl, rfl, hsends_f, hle_qep, ?_, fun hne => absurd hep_t hne⟩))
            intro pos hpos_ep
            refine syncPaperMulti_after_accept hsync hpos_ep hsends_f hle_tcur
              ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_right (show (esL.g.st P).tcur ≤ c.1.1 by omega)).symm, rfl⟩
              rfl rfl (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
              (Or.inr ⟨hep_t, rsLoc', sIdx, rfl, rfl, by rwa [hsessM2]⟩)
              hbk2 hsess_le2 htH_sess2 (hcacheL2.trans hcacheL1) (hcacheM2.trans hcacheM1) (hlfM2.trans hlfM1) hbook_out2 ?_
            intro i hi
            have hPr_eq : Function.update esL.g.st P
                { esL.g.st P with tcur := c.1.1, γ := γ', root := σ',
                                  vR := Function.update (esL.g.st P).vR c.1.1 (some (rsLoc', some sIdx)) }
                (Party.receiverOf t) =
                { esL.g.st P with tcur := c.1.1, γ := γ', root := σ',
                                  vR := Function.update (esL.g.st P).vR c.1.1 (some (rsLoc', some sIdx)) } := by
              rw [← hPr, Function.update_self]
            rw [hPr_eq]
            dsimp only
            rw [hep_t, Function.update_self]
            by_cases hi_eq : i = sIdx
            · subst hi_eq
              simp only [↓reduceIte]
              exact ⟨ssLoc, hinv2, hss1, hss2⟩
            · simp only [show ¬(sIdx = i) from Ne.symm hi_eq, ↓reduceIte]
              rw [(hother2 i hi_eq).1, (hother2 i hi_eq).2]
              exact hbook_in1 i (by rwa [← hsessM2])
        · dsimp only at hep_ne hrL hrM hhL hhM; subst r1L_val r1M_val hL₁ hM₁
          simp only [simulateQ_bind, StateT.run_bind]
          refine Coupled2.bind
            (fsRecv_coupled2 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              (fun _ => hheal_M) esL.h esM.h tblM tblL
              (fs.initReceiver k, none) (.inl (fs.initReceiver k)) (fs.initSender (ks 0)) c.1 c.2 recL recM
              (Or.inl ⟨hep_ne, fs.initReceiver k, rfl, rfl⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ r2M ⟨hused2, hcacheL2, htableL2, hsessL2, _, hrec_cases⟩
          cases hrec : fs.receive (fs.initReceiver k) c.1 c.2 with
          | none =>
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M⟩
            subst hr2M; dsimp only at hr2L; subst r2L_val
            simp only [simulateQ_pure, StateT.run_pure]
            exact Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM, tblL, rfl,
              (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩))
          | some o =>
            rcases o with ⟨rs', idxOut, pmOut⟩
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M⟩
            subst hr2M; dsimp only at hr2L; subst r2L_val
            simp only [simulateQ_pure, StateT.run_pure]
            refine Coupled2.pure (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM, tblL, rfl, rfl, rfl, hsends_f, hle_qep, ?_,
              fun _ => (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩))
            intro pos hpos_ep
            have hsync_hL := (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2
            refine syncPaperMulti_after_accept (hsync.with_hL_eq hused2 hcacheL2 htableL2 hsessL2)
              hpos_ep hsends_f hle_tcur
              ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_right (show (esL.g.st P).tcur ≤ c.1.1 by omega)).symm, rfl⟩
              rfl rfl (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
              (Or.inl ⟨hep_ne, rs', rfl, rfl⟩)
              hsync_hL.hookBookInv (Nat.le_refl _) (fun _ => rfl) rfl rfl rfl
              hsync.hbook_out ?_
            intro i hi
            have hvR_unch : (Function.update esL.g.st P
                { esL.g.st P with tcur := c.1.1, γ := γ', root := σ',
                                  vR := Function.update (esL.g.st P).vR c.1.1 (some (rs', none)) }
                (Party.receiverOf t)).vR t = (esL.g.st (Party.receiverOf t)).vR t := by
              by_cases hQ : Party.receiverOf t = P
              · rw [hQ, Function.update_self]; dsimp only; rw [Function.update_of_ne (Ne.symm hep_ne)]
              · rw [Function.update_of_ne hQ]
            rw [hvR_unch]
            exact hsync.hbook_in i hi
    · have hfreshM : c.1.1 ≠ (esM.g.st P).tcur + 1 := by rw [hsync.htcurM P]; exact hfresh
      have hep_le : c.1.1 ≤ (esL.g.st P).tcur := by omega
      cases hvRL : (esL.g.st P).vR c.1.1 with
      | none =>
        have hvRM : (esM.g.st P).vR c.1.1 = none := by
          by_cases hep_t : c.1.1 = t
          · subst hep_t; have hv := hsync.hvR_eq P; rw [hvRL] at hv; exact hv
          · have hv := hsync.hvR_ne P c.1.1 hep_t; rw [hvRL] at hv; exact hv
        rw [vRecv_reuse_none_run _ _ _ _ _ _ _ hgL hfresh hvRL,
            vRecv_reuse_none_run _ _ _ _ _ _ _ hgM hfreshM hvRM]
        simp only [simulateQ_pure, StateT.run_pure]
        exact Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM, tblL, rfl, hsync.mono_rem (Nat.le_succ rem)⟩))
      | some rsvL =>
        by_cases hep_t : c.1.1 = t
        · have hv := hsync.hvR_eq P
          have hvRL_t : (esL.g.st P).vR t = some rsvL := hep_t ▸ hvRL
          rw [hvRL_t] at hv
          rcases hv with ⟨sIdx, hopt, hvRM_t, hsIdx_lt, _, hPr⟩
          rcases rsvL with ⟨rsLoc, optIdx⟩
          dsimp only at hopt; subst optIdx
          have hvRM : (esM.g.st P).vR c.1.1 = some (.inr sIdx) := by simpa [hep_t] using hvRM_t
          rw [vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgL hfresh hvRL,
              vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgM hfreshM hvRM,
              simulateQ_bind, simulateQ_bind, StateT.run_bind]
          have hbi_sIdx := hsync.hbook_in sIdx hsIdx_lt
          dsimp only at hbi_sIdx
          rw [← hPr, hvRL_t] at hbi_sIdx
          simp only [↓reduceIte] at hbi_sIdx
          rcases hbi_sIdx with ⟨ssLoc, hinv0, hss1, hss2⟩
          refine Coupled2.bind
            (fsRecv_coupled2 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              (fun _ => hheal_M) esL.h esM.h tblM tblL
              (rsLoc, some sIdx) (.inr sIdx) ssLoc c.1 c.2 recL recM
              (Or.inr ⟨hep_t, rsLoc, sIdx, rfl, rfl, hsIdx_lt, hinv0⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ ⟨⟨r2M_val, hM'⟩, s2⟩
            ⟨hused2, hcacheL2, htableL2, hsessL2, _, hM'_tmp, tblM', rfl, rfl,
              hcacheM2, htableM2, hsessM2, hlfM2, hother2, hrec_cases⟩
          simp only [simulateQ_pure, StateT.run_pure]
          have hbk0 := (hsync.mono_rem (Nat.le_succ rem)).hookBookInv
          have hbk2 : HookBookInv M_sess t tL ks rem hL₂ hM' :=
            { hsess := hsessM2.trans (hbk0.hsess.trans hsessL2.symm)
              hnodup := hsessL2 ▸ hbk0.hnodup
              hlen := hsessL2 ▸ hbk0.hlen
              hused := fun i => by rw [hused2, hsessL2]; exact hbk0.hused i
              htblL_lk := fun htH Ik => by rw [htableL2, hsessL2]; exact hbk0.htblL_lk htH Ik
              htblM_lk := fun htH Ik => by rw [htableM2, hsessM2]; exact hbk0.htblM_lk htH Ik }
          have hsess_le2 : esM.h.sessions.length ≤ hM'.sessions.length := by rw [hsessM2]
          have hbook_out2 : ∀ i, hM'.sessions.length ≤ i →
              hM'.book i = none ∧ tblM' i = hInit (bs i) (.seed (ks i)) ∧
                (false = true → tblL i = hInit (bs i) (.seed (ks i))) := by
            intro i hi; rw [hsessM2] at hi
            have hne : i ≠ sIdx := by omega
            rw [(hother2 i hne).1, (hother2 i hne).2]
            exact hsync.hbook_out i hi
          cases hrec : fs.receive rsLoc c.1 c.2 with
          | none =>
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M, hinv2⟩
            dsimp only at hr2L hr2M; subst r2L_val r2M_val
            refine Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM', tblL, rfl, ?_⟩))
            refine syncPaperMulti_after_vRecv_reject hsync hbk2 hsess_le2 (fun _ => hsessM2)
              hcacheL2 hcacheM2 hlfM2 hbook_out2 ?_
            intro i hi
            by_cases hi_eq : i = sIdx
            · subst hi_eq
              rw [← hPr, hvRL_t]
              simp only [↓reduceIte]
              exact ⟨ssLoc, hinv2, hss1, hss2⟩
            · rw [(hother2 i hi_eq).1, (hother2 i hi_eq).2]
              exact hsync.hbook_in i (by rwa [← hsessM2])
          | some o =>
            rcases o with ⟨rsLoc', idxOut, pmOut⟩
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M, hinv2⟩
            dsimp only at hr2L hr2M; subst r2L_val r2M_val
            refine Coupled2.pure (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM', tblL, rfl, rfl, rfl, hsends_f, hle_qep, ?_, fun hne => absurd hep_t hne⟩))
            intro pos hpos_ep
            refine syncPaperMulti_after_accept hsync hpos_ep hsends_f hle_tcur
              ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_left hep_le).symm, hsync.htcurM P⟩
              (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
              (Or.inr ⟨hep_t, rsLoc', sIdx, rfl, rfl, by rwa [hsessM2]⟩)
              hbk2 hsess_le2 (fun _ => hsessM2) hcacheL2 hcacheM2 hlfM2 hbook_out2 ?_
            intro i hi
            rw [← hPr, Function.update_self]
            dsimp only
            rw [hep_t, Function.update_self]
            by_cases hi_eq : i = sIdx
            · subst hi_eq
              simp only [↓reduceIte]
              exact ⟨ssLoc, hinv2, hss1, hss2⟩
            · simp only [show ¬(sIdx = i) from Ne.symm hi_eq, ↓reduceIte]
              rw [(hother2 i hi_eq).1, (hother2 i hi_eq).2]
              have hbi_i := hsync.hbook_in i (by rwa [← hsessM2])
              dsimp only at hbi_i
              rw [← hPr, hvRL_t] at hbi_i
              simp only [show ¬(sIdx = i) from Ne.symm hi_eq, ↓reduceIte] at hbi_i
              exact hbi_i
        · have hv := hsync.hvR_ne P c.1.1 hep_t
          rw [hvRL] at hv
          rcases rsvL with ⟨rs, optIdx⟩
          rcases hv with ⟨rfl, hvRM⟩
          rw [vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgL hfresh hvRL,
              vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgM hfreshM hvRM,
              simulateQ_bind, simulateQ_bind, StateT.run_bind]
          refine Coupled2.bind
            (fsRecv_coupled2 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              (fun _ => hheal_M) esL.h esM.h tblM tblL
              (rs, none) (.inl rs) (fs.initSender (ks 0)) c.1 c.2 recL recM
              (Or.inl ⟨hep_t, rs, rfl, rfl⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ r2M ⟨hused2, hcacheL2, htableL2, hsessL2, _, hrec_cases⟩
          cases hrec : fs.receive rs c.1 c.2 with
          | none =>
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M⟩
            subst hr2M; dsimp only at hr2L; subst r2L_val
            simp only [simulateQ_pure, StateT.run_pure]
            exact Coupled2.pure (Or.inr (Or.inl ⟨rfl, rfl, tblM, tblL, rfl,
              (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩))
          | some o =>
            rcases o with ⟨rs', idxOut, pmOut⟩
            rw [hrec] at hrec_cases
            rcases hrec_cases with ⟨hr2L, hr2M⟩
            subst hr2M; dsimp only at hr2L; subst r2L_val
            simp only [simulateQ_pure, StateT.run_pure]
            refine Coupled2.pure (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM, tblL, rfl, rfl, rfl, hsends_f, hle_qep, ?_,
              fun _ => (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩))
            intro pos hpos_ep
            have hsync_hL := (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2
            refine syncPaperMulti_after_accept (hsync.with_hL_eq hused2 hcacheL2 htableL2 hsessL2)
              hpos_ep hsends_f hle_tcur
              ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_left hep_le).symm, hsync.htcurM P⟩
              (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
              (Or.inl ⟨hep_t, rs', rfl, rfl⟩)
              hsync_hL.hookBookInv (Nat.le_refl _) (fun _ => rfl) rfl rfl rfl
              hsync.hbook_out ?_
            intro i hi
            have hvR_unch : (Function.update esL.g.st P
                { esL.g.st P with vR := Function.update (esL.g.st P).vR c.1.1 (some (rs', none)) }
                (Party.receiverOf t)).vR t = (esL.g.st (Party.receiverOf t)).vR t := by
              by_cases hQ : Party.receiverOf t = P
              · rw [hQ, Function.update_self]; dsimp only; rw [Function.update_of_ne (Ne.symm hep_t)]
              · rw [Function.update_of_ne hQ]
            rw [hvR_unch]
            exact hsync.hbook_in i hi



private theorem vRecv_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (P : Party) (c : Fig8C Pt)
    (recL recM : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hheal : healedBy esL.g.tL (2 + Δcka) t = true)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (VRecvPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem P c.1.1 esL esM)
      (simulateQ (keySlotFixedImpl ks)
        ((vRecv (hooksSlotLocal cka prng fs mo M_sess) esL.g P (esL.g.st P) c recL).run esL.h))
      ((simulateQ (pubFsMultiImpl implF)
        ((vRecv (hooksFSMulti cka prng fs Δcka mo false false) esM.g P (esM.g.st P) c recM).run esM.h)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((vRecv (hooksFSMulti cka prng fs Δcka mo false true) esM.g P (esM.g.st P) c recM).run esM.h)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  have hheal_M : healedBy esM.g.tL (2 + Δcka) t = true := by
    rw [← _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_tL hsync.herase]
    exact hheal
  by_cases hgL : ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = true
  · have hgM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = true := by
      simpa [hsync.hidL P, hsync.hidM P, hsync.htcurM P] using hgL
    rw [vRecv_guard_true_run _ _ _ _ _ _ _ hgL,
        vRecv_guard_true_run _ _ _ _ _ _ _ hgM,
        vRecv_guard_true_run _ _ _ _ _ _ _ hgM]
    simp only [simulateQ_pure, StateT.run_pure]
    exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM, tblL, rfl, rfl,
      hsync.mono_rem (Nat.le_succ rem)⟩)))
  · simp only [Bool.not_eq_true] at hgL
    have hgM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
      simpa [hsync.hidL P, hsync.hidM P, hsync.htcurM P] using hgL
    have ⟨hsends_id, hnot_lt⟩ := Bool.or_eq_false_iff.mp hgL
    have hsends_f : P.sendsIn c.1.1 = false := by rwa [hsync.hidL P] at hsends_id
    have hle_tcur : c.1.1 ≤ (esL.g.st P).tcur + 1 := by
      simp only [decide_eq_false_iff_not] at hnot_lt; omega
    have hle_qep : c.1.1 ≤ qep + 1 :=
      epochQepInv_vRecv_le hqep hsends_f (by rwa [hsync.htcurL P] at hle_tcur)
    by_cases hfresh : c.1.1 = (esL.g.st P).tcur + 1
    · have hfreshM : c.1.1 = (esM.g.st P).tcur + 1 := by rw [hsync.htcurM P]; exact hfresh
      cases hTn : c.1.2 with
      | none =>
        rw [vRecv_fresh_none_run _ _ _ _ _ _ _ hgL hfresh hTn,
            vRecv_fresh_none_run _ _ _ _ _ _ _ hgM hfreshM hTn,
            vRecv_fresh_none_run _ _ _ _ _ _ _ hgM hfreshM hTn]
        simp only [simulateQ_pure, StateT.run_pure]
        exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM, tblL, rfl, rfl,
          hsync.mono_rem (Nat.le_succ rem)⟩)))
      | some Tn =>
        rw [vRecv_fresh_some_run _ _ _ _ _ _ _ Tn hgL hfresh hTn,
            vRecv_fresh_some_run _ _ _ _ _ _ _ Tn hgM hfreshM hTn,
            vRecv_fresh_some_run _ _ _ _ _ _ _ Tn hgM hfreshM hTn,
            hsync.hγ P, hsync.hroot P,
            simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
        refine Coupled3.bind
          (startRecv_coupled3 (impl₀ := implF) (impl₁ := implT)
            (s₀ := (fun _ => false, tblM)) (s₁ := (fun _ => false, tblL))
            C Dh encPt encT idOf Δcka M_sess t c.1.1 rem tL ks esL.g esM.g P
            hsync.hookBookInv hsync.hcache_ne hsync.hcache_eq
            (esL.g.st P).γ (esL.g.st P).root Tn) ?_
        rintro ⟨r1L_val, hL₁⟩ ⟨⟨r1₀_val, hM₁⟩, s₀⟩ ⟨⟨r1₁_val, hM₁'⟩, s₁⟩
          ⟨hhM1_eq, rfl, rfl, hbk1, hcacheL1, hcacheM1, hbookM1, hlfM1, ⟨J, hsess1⟩, hcases1⟩
        dsimp only at hhM1_eq; subst hM₁'
        have hsess_le1 : esM.h.sessions.length ≤ hM₁.sessions.length := by
          rcases hsess1 with h | ⟨_, h⟩
          · rw [h]
          · rw [h]; simp
        have htH_sess1 : (tL.isSome && decide (t = mo.tH)) = true → hM₁.sessions = esM.h.sessions := by
          intro htH
          rcases hsess1 with h | ⟨hf, _⟩
          · exact h
          · rw [htH] at hf; cases hf
        rcases hcases1 with ⟨hrL, hr0, hr1, hhL, hhM⟩ | ⟨hrL, hr0, hr1, hhL, hhM⟩ |
            ⟨hep_t, γ', σ', sIdx, hrL, hr0, hr1, hsIdx_lt⟩ | ⟨hep_ne, γ', σ', k, hrL, hr0, hr1, hhL, hhM⟩
        · dsimp only at hrL hr0 hr1; subst r1L_val r1₀_val r1₁_val
          simp only [simulateQ_pure, StateT.run_pure]
          exact Coupled3.pure (Or.inl rfl)
        · dsimp only at hrL hr0 hr1 hhL hhM; subst r1L_val r1₀_val r1₁_val hL₁ hM₁
          simp only [simulateQ_pure, StateT.run_pure]
          exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM, tblL, rfl, rfl,
            hsync.mono_rem (Nat.le_succ rem)⟩)))
        · dsimp only at hep_t hrL hr0 hr1 hsIdx_lt; subst r1L_val r1₀_val r1₁_val
          simp only [simulateQ_bind, StateT.run_bind]
          have hPr : P = Party.receiverOf t := by
            apply party_eq_receiverOf_of_sendsIn_false; simpa [hep_t] using hsends_f
          have hvR_none : (esL.g.st (Party.receiverOf t)).vR t = none :=
            (hsync.hvR_hi (Party.receiverOf t) t (Or.inl (by rw [← hPr]; omega))).1
          have ⟨hbook_out1, hbook_in1⟩ := hbook_after_startRecv_at_t hsync hvR_none hbookM1 hsess_le1
          rcases hbook_in1 sIdx hsIdx_lt with ⟨ssLoc, hinv1, hss1, hss2⟩
          refine Coupled3.bind
            (fsRecv_coupled3 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              hheal_M hL₁ hM₁ tblM tblL
              (fs.initReceiver (ks sIdx), some sIdx) (.inr sIdx) ssLoc c.1 c.2 recL recM
              (Or.inr ⟨hep_t, fs.initReceiver (ks sIdx), sIdx, rfl, rfl, hsIdx_lt, hinv1⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ ⟨⟨r2₀_val, hM₂⟩, s2₀⟩ ⟨⟨r2₁_val, hM₂'⟩, s2₁⟩ hfs3
          simp only [simulateQ_pure, StateT.run_pure]
          rcases hfs3 with ⟨hr2₁_none, hlf2⟩ |
            ⟨hused2, hcacheL2, htableL2, hsessL2, hhM2_eq, _, hM', tblM', tblL',
              hr0_eq, hr1_eq, hcacheM2, htableM2, hsessM2, hlfM2, hother2, hrec_cases⟩
          · dsimp only at hr2₁_none hlf2; subst r2₁_val
            exact Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf2⟩))
          · rcases Prod.mk.inj hr0_eq with ⟨hr0_1, hr0_2⟩
            rcases Prod.mk.inj hr0_1 with ⟨_, hhM_eq⟩
            rcases Prod.mk.inj hr1_eq with ⟨hr1_1, hr1_2⟩
            rcases Prod.mk.inj hr1_1 with ⟨_, hhM'_eq⟩
            subst hM₂ hM₂' s2₀ s2₁
            have hbk2 : HookBookInv M_sess t tL ks rem hL₂ hM' :=
              { hsess := hsessM2.trans (hbk1.hsess.trans hsessL2.symm)
                hnodup := hsessL2 ▸ hbk1.hnodup
                hlen := hsessL2 ▸ hbk1.hlen
                hused := fun i => by rw [hused2, hsessL2]; exact hbk1.hused i
                htblL_lk := fun htH Ik => by rw [htableL2, hsessL2]; exact hbk1.htblL_lk htH Ik
                htblM_lk := fun htH Ik => by rw [htableM2, hsessM2]; exact hbk1.htblM_lk htH Ik }
            have hsess_le2 : esM.h.sessions.length ≤ hM'.sessions.length := by rw [hsessM2]; exact hsess_le1
            have htH_sess2 : (tL.isSome && decide (t = mo.tH)) = true → hM'.sessions = esM.h.sessions :=
              fun htH => hsessM2.trans (htH_sess1 htH)
            have hbook_out2 : ∀ i, hM'.sessions.length ≤ i →
                hM'.book i = none ∧ tblM' i = hInit (bs i) (.seed (ks i)) ∧
                  (true = true → tblL' i = hInit (bs i) (.seed (ks i))) := by
              intro i hi; rw [hsessM2] at hi
              have hne : i ≠ sIdx := by omega
              rcases hother2 i hne with ⟨hb_eq, hm_eq, hl_eq⟩
              rw [hb_eq, hm_eq, hl_eq]
              exact hbook_out1 i hi
            cases hrec : fs.receive (fs.initReceiver (ks sIdx)) c.1 c.2 with
            | none =>
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁, hinv2⟩
              dsimp only at hr2L hr2₀ hr2₁; subst r2L_val r2₀_val r2₁_val
              refine Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM', tblL', rfl, rfl, ?_⟩)))
              refine syncPaperMulti_after_vRecv_reject hsync hbk2 hsess_le2 htH_sess2
                (hcacheL2.trans hcacheL1) (hcacheM2.trans hcacheM1) (hlfM2.trans hlfM1) hbook_out2 ?_
              intro i hi
              rw [hvR_none]
              by_cases hi_eq : i = sIdx
              · subst hi_eq; exact ⟨ssLoc, hinv2, hss1, hss2⟩
              · rcases hother2 i hi_eq with ⟨hb_eq, hm_eq, hl_eq⟩
                rw [hb_eq, hm_eq, hl_eq]
                exact hbook_in1 i (by rwa [← hsessM2])
            | some o =>
              rcases o with ⟨rsLoc', idxOut, pmOut⟩
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁, hinv2⟩
              dsimp only at hr2L hr2₀ hr2₁; subst r2L_val r2₀_val r2₁_val
              refine Coupled3.pure (Or.inr (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM', tblL',
                rfl, rfl, rfl, rfl, rfl, rfl, hsends_f, hle_qep, ?_, fun hne => absurd hep_t hne⟩)))
              intro pos hpos_ep
              refine syncPaperMulti_after_accept hsync hpos_ep hsends_f hle_tcur
                ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_right (show (esL.g.st P).tcur ≤ c.1.1 by omega)).symm, rfl⟩
                rfl rfl (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
                (Or.inr ⟨hep_t, rsLoc', sIdx, rfl, rfl, by rwa [hsessM2]⟩)
                hbk2 hsess_le2 htH_sess2 (hcacheL2.trans hcacheL1) (hcacheM2.trans hcacheM1) (hlfM2.trans hlfM1) hbook_out2 ?_
              intro i hi
              have hPr_eq : Function.update esL.g.st P
                  { esL.g.st P with tcur := c.1.1, γ := γ', root := σ',
                                    vR := Function.update (esL.g.st P).vR c.1.1 (some (rsLoc', some sIdx)) }
                  (Party.receiverOf t) =
                  { esL.g.st P with tcur := c.1.1, γ := γ', root := σ',
                                    vR := Function.update (esL.g.st P).vR c.1.1 (some (rsLoc', some sIdx)) } := by
                rw [← hPr, Function.update_self]
              rw [hPr_eq]
              dsimp only
              rw [hep_t, Function.update_self]
              by_cases hi_eq : i = sIdx
              · subst hi_eq
                simp only [↓reduceIte]
                exact ⟨ssLoc, hinv2, hss1, hss2⟩
              · simp only [show ¬(sIdx = i) from Ne.symm hi_eq, ↓reduceIte]
                rcases hother2 i hi_eq with ⟨hb_eq, hm_eq, hl_eq⟩
                rw [hb_eq, hm_eq, hl_eq]
                exact hbook_in1 i (by rwa [← hsessM2])
        · dsimp only at hep_ne hrL hr0 hr1 hhL hhM; subst r1L_val r1₀_val r1₁_val hL₁ hM₁
          simp only [simulateQ_bind, StateT.run_bind]
          refine Coupled3.bind
            (fsRecv_coupled3 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              hheal_M esL.h esM.h tblM tblL
              (fs.initReceiver k, none) (.inl (fs.initReceiver k)) (fs.initSender (ks 0)) c.1 c.2 recL recM
              (Or.inl ⟨hep_ne, fs.initReceiver k, rfl, rfl⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ r2₀ r2₁ hfs3
          rcases hfs3 with ⟨hr2₁_none, hlf2⟩ | ⟨hused2, hcacheL2, htableL2, hsessL2, hhM2_eq, _, hrec_cases⟩
          · rcases r2₁ with ⟨⟨r2₁_val, hM₂'⟩, s2₁⟩
            dsimp only at hr2₁_none hlf2; subst r2₁_val
            simp only [simulateQ_pure, StateT.run_pure]
            exact Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf2⟩))
          · cases hrec : fs.receive (fs.initReceiver k) c.1 c.2 with
            | none =>
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁⟩
              subst hr2₀ hr2₁; dsimp only at hr2L; subst r2L_val
              simp only [simulateQ_pure, StateT.run_pure]
              exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM, tblL, rfl, rfl,
                (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩)))
            | some o =>
              rcases o with ⟨rs', idxOut, pmOut⟩
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁⟩
              subst hr2₀ hr2₁; dsimp only at hr2L; subst r2L_val
              simp only [simulateQ_pure, StateT.run_pure]
              refine Coupled3.pure (Or.inr (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM, tblL,
                rfl, rfl, rfl, rfl, rfl, rfl, hsends_f, hle_qep, ?_,
                fun _ => (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩)))
              intro pos hpos_ep
              have hsync_hL := (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2
              refine syncPaperMulti_after_accept (hsync.with_hL_eq hused2 hcacheL2 htableL2 hsessL2)
                hpos_ep hsends_f hle_tcur
                ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_right (show (esL.g.st P).tcur ≤ c.1.1 by omega)).symm, rfl⟩
                rfl rfl (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
                (Or.inl ⟨hep_ne, rs', rfl, rfl⟩)
                hsync_hL.hookBookInv (Nat.le_refl _) (fun _ => rfl) rfl rfl rfl
                hsync.hbook_out ?_
              intro i hi
              have hvR_unch : (Function.update esL.g.st P
                  { esL.g.st P with tcur := c.1.1, γ := γ', root := σ',
                                    vR := Function.update (esL.g.st P).vR c.1.1 (some (rs', none)) }
                  (Party.receiverOf t)).vR t = (esL.g.st (Party.receiverOf t)).vR t := by
                by_cases hQ : Party.receiverOf t = P
                · rw [hQ, Function.update_self]; dsimp only; rw [Function.update_of_ne (Ne.symm hep_ne)]
                · rw [Function.update_of_ne hQ]
              rw [hvR_unch]
              exact hsync.hbook_in i hi
    · have hfreshM : c.1.1 ≠ (esM.g.st P).tcur + 1 := by rw [hsync.htcurM P]; exact hfresh
      have hep_le : c.1.1 ≤ (esL.g.st P).tcur := by omega
      cases hvRL : (esL.g.st P).vR c.1.1 with
      | none =>
        have hvRM : (esM.g.st P).vR c.1.1 = none := by
          by_cases hep_t : c.1.1 = t
          · subst hep_t; have hv := hsync.hvR_eq P; rw [hvRL] at hv; exact hv
          · have hv := hsync.hvR_ne P c.1.1 hep_t; rw [hvRL] at hv; exact hv
        rw [vRecv_reuse_none_run _ _ _ _ _ _ _ hgL hfresh hvRL,
            vRecv_reuse_none_run _ _ _ _ _ _ _ hgM hfreshM hvRM,
            vRecv_reuse_none_run _ _ _ _ _ _ _ hgM hfreshM hvRM]
        simp only [simulateQ_pure, StateT.run_pure]
        exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM, tblL, rfl, rfl,
          hsync.mono_rem (Nat.le_succ rem)⟩)))
      | some rsvL =>
        by_cases hep_t : c.1.1 = t
        · have hv := hsync.hvR_eq P
          have hvRL_t : (esL.g.st P).vR t = some rsvL := hep_t ▸ hvRL
          rw [hvRL_t] at hv
          rcases hv with ⟨sIdx, hopt, hvRM_t, hsIdx_lt, _, hPr⟩
          rcases rsvL with ⟨rsLoc, optIdx⟩
          dsimp only at hopt; subst optIdx
          have hvRM : (esM.g.st P).vR c.1.1 = some (.inr sIdx) := by simpa [hep_t] using hvRM_t
          rw [vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgL hfresh hvRL,
              vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgM hfreshM hvRM,
              vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgM hfreshM hvRM,
              simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
          have hbi_sIdx := hsync.hbook_in sIdx hsIdx_lt
          dsimp only at hbi_sIdx
          rw [← hPr, hvRL_t] at hbi_sIdx
          simp only [↓reduceIte] at hbi_sIdx
          rcases hbi_sIdx with ⟨ssLoc, hinv0, hss1, hss2⟩
          refine Coupled3.bind
            (fsRecv_coupled3 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              hheal_M esL.h esM.h tblM tblL
              (rsLoc, some sIdx) (.inr sIdx) ssLoc c.1 c.2 recL recM
              (Or.inr ⟨hep_t, rsLoc, sIdx, rfl, rfl, hsIdx_lt, hinv0⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ ⟨⟨r2₀_val, hM₂⟩, s2₀⟩ ⟨⟨r2₁_val, hM₂'⟩, s2₁⟩ hfs3
          simp only [simulateQ_pure, StateT.run_pure]
          rcases hfs3 with ⟨hr2₁_none, hlf2⟩ |
            ⟨hused2, hcacheL2, htableL2, hsessL2, hhM2_eq, _, hM', tblM', tblL',
              hr0_eq, hr1_eq, hcacheM2, htableM2, hsessM2, hlfM2, hother2, hrec_cases⟩
          · dsimp only at hr2₁_none hlf2; subst r2₁_val
            exact Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf2⟩))
          · rcases Prod.mk.inj hr0_eq with ⟨hr0_1, hr0_2⟩
            rcases Prod.mk.inj hr0_1 with ⟨_, hhM_eq⟩
            rcases Prod.mk.inj hr1_eq with ⟨hr1_1, hr1_2⟩
            rcases Prod.mk.inj hr1_1 with ⟨_, hhM'_eq⟩
            subst hM₂ hM₂' s2₀ s2₁
            have hbk0 := (hsync.mono_rem (Nat.le_succ rem)).hookBookInv
            have hbk2 : HookBookInv M_sess t tL ks rem hL₂ hM' :=
              { hsess := hsessM2.trans (hbk0.hsess.trans hsessL2.symm)
                hnodup := hsessL2 ▸ hbk0.hnodup
                hlen := hsessL2 ▸ hbk0.hlen
                hused := fun i => by rw [hused2, hsessL2]; exact hbk0.hused i
                htblL_lk := fun htH Ik => by rw [htableL2, hsessL2]; exact hbk0.htblL_lk htH Ik
                htblM_lk := fun htH Ik => by rw [htableM2, hsessM2]; exact hbk0.htblM_lk htH Ik }
            have hsess_le2 : esM.h.sessions.length ≤ hM'.sessions.length := by rw [hsessM2]
            have hbook_out2 : ∀ i, hM'.sessions.length ≤ i →
                hM'.book i = none ∧ tblM' i = hInit (bs i) (.seed (ks i)) ∧
                  (true = true → tblL' i = hInit (bs i) (.seed (ks i))) := by
              intro i hi; rw [hsessM2] at hi
              have hne : i ≠ sIdx := by omega
              rcases hother2 i hne with ⟨hb_eq, hm_eq, hl_eq⟩
              rw [hb_eq, hm_eq, hl_eq]
              exact hsync.hbook_out i hi
            cases hrec : fs.receive rsLoc c.1 c.2 with
            | none =>
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁, hinv2⟩
              dsimp only at hr2L hr2₀ hr2₁; subst r2L_val r2₀_val r2₁_val
              refine Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM', tblL', rfl, rfl, ?_⟩)))
              refine syncPaperMulti_after_vRecv_reject hsync hbk2 hsess_le2 (fun _ => hsessM2)
                hcacheL2 hcacheM2 hlfM2 hbook_out2 ?_
              intro i hi
              by_cases hi_eq : i = sIdx
              · subst hi_eq
                rw [← hPr, hvRL_t]
                simp only [↓reduceIte]
                exact ⟨ssLoc, hinv2, hss1, hss2⟩
              · rcases hother2 i hi_eq with ⟨hb_eq, hm_eq, hl_eq⟩
                rw [hb_eq, hm_eq, hl_eq]
                exact hsync.hbook_in i (by rwa [← hsessM2])
            | some o =>
              rcases o with ⟨rsLoc', idxOut, pmOut⟩
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁, hinv2⟩
              dsimp only at hr2L hr2₀ hr2₁; subst r2L_val r2₀_val r2₁_val
              refine Coupled3.pure (Or.inr (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM', tblL',
                rfl, rfl, rfl, rfl, rfl, rfl, hsends_f, hle_qep, ?_, fun hne => absurd hep_t hne⟩)))
              intro pos hpos_ep
              refine syncPaperMulti_after_accept hsync hpos_ep hsends_f hle_tcur
                ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_left hep_le).symm, hsync.htcurM P⟩
                (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
                (Or.inr ⟨hep_t, rsLoc', sIdx, rfl, rfl, by rwa [hsessM2]⟩)
                hbk2 hsess_le2 (fun _ => hsessM2) hcacheL2 hcacheM2 hlfM2 hbook_out2 ?_
              intro i hi
              rw [← hPr, Function.update_self]
              dsimp only
              rw [hep_t, Function.update_self]
              by_cases hi_eq : i = sIdx
              · subst hi_eq
                simp only [↓reduceIte]
                exact ⟨ssLoc, hinv2, hss1, hss2⟩
              · simp only [show ¬(sIdx = i) from Ne.symm hi_eq, ↓reduceIte]
                rcases hother2 i hi_eq with ⟨hb_eq, hm_eq, hl_eq⟩
                rw [hb_eq, hm_eq, hl_eq]
                have hbi_i := hsync.hbook_in i (by rwa [← hsessM2])
                dsimp only at hbi_i
                rw [← hPr, hvRL_t] at hbi_i
                simp only [show ¬(sIdx = i) from Ne.symm hi_eq, ↓reduceIte] at hbi_i
                exact hbi_i
        · have hv := hsync.hvR_ne P c.1.1 hep_t
          rw [hvRL] at hv
          rcases rsvL with ⟨rs, optIdx⟩
          rcases hv with ⟨rfl, hvRM⟩
          rw [vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgL hfresh hvRL,
              vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgM hfreshM hvRM,
              vRecv_reuse_some_run _ _ _ _ _ _ _ _ hgM hfreshM hvRM,
              simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
          refine Coupled3.bind
            (fsRecv_coupled3 C hD Dh hℓ encPt encT idOf Δcka M_sess t c.1.1 tL ks esL.g esM.g P
              hheal_M esL.h esM.h tblM tblL
              (rs, none) (.inl rs) (fs.initSender (ks 0)) c.1 c.2 recL recM
              (Or.inl ⟨hep_t, rs, rfl, rfl⟩)) ?_
          rintro ⟨r2L_val, hL₂⟩ r2₀ r2₁ hfs3
          rcases hfs3 with ⟨hr2₁_none, hlf2⟩ | ⟨hused2, hcacheL2, htableL2, hsessL2, _, _, hrec_cases⟩
          · rcases r2₁ with ⟨⟨r2₁_val, hM₂'⟩, s2₁⟩
            dsimp only at hr2₁_none hlf2; subst r2₁_val
            simp only [simulateQ_pure, StateT.run_pure]
            exact Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf2⟩))
          · cases hrec : fs.receive rs c.1 c.2 with
            | none =>
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁⟩
              subst hr2₀ hr2₁; dsimp only at hr2L; subst r2L_val
              simp only [simulateQ_pure, StateT.run_pure]
              exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, tblM, tblL, rfl, rfl,
                (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩)))
            | some o =>
              rcases o with ⟨rs', idxOut, pmOut⟩
              rw [hrec] at hrec_cases
              rcases hrec_cases with ⟨hr2L, hr2₀, hr2₁⟩
              subst hr2₀ hr2₁; dsimp only at hr2L; subst r2L_val
              simp only [simulateQ_pure, StateT.run_pure]
              refine Coupled3.pure (Or.inr (Or.inr (Or.inr ⟨_, _, idxOut, pmOut, tblM, tblL,
                rfl, rfl, rfl, rfl, rfl, rfl, hsends_f, hle_qep, ?_,
                fun _ => (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2⟩)))
              intro pos hpos_ep
              have hsync_hL := (hsync.mono_rem (Nat.le_succ rem)).with_hL_eq hused2 hcacheL2 htableL2 hsessL2
              refine syncPaperMulti_after_accept (hsync.with_hL_eq hused2 hcacheL2 htableL2 hsessL2)
                hpos_ep hsends_f hle_tcur
                ⟨hsync.hidL P, hsync.hidM P⟩ ⟨(Nat.max_eq_left hep_le).symm, hsync.htcurM P⟩
                (hsync.hγ P) (hsync.hroot P) (hsync.hckaMsg P) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
                (Or.inl ⟨hep_t, rs', rfl, rfl⟩)
                hsync_hL.hookBookInv (Nat.le_refl _) (fun _ => rfl) rfl rfl rfl
                hsync.hbook_out ?_
              intro i hi
              have hvR_unch : (Function.update esL.g.st P
                  { esL.g.st P with vR := Function.update (esL.g.st P).vR c.1.1 (some (rs', none)) }
                  (Party.receiverOf t)).vR t = (esL.g.st (Party.receiverOf t)).vR t := by
                by_cases hQ : Party.receiverOf t = P
                · rw [hQ, Function.update_self]; dsimp only; rw [Function.update_of_ne (Ne.symm hep_t)]
                · rw [Function.update_of_ne hQ]
              rw [hvR_unch]
              exact hsync.hbook_in i hi



/-! ### 7C.4 `deliverE`, `injectE`, and `deliverForgeE` Step Couplings -/

private theorem deliverE_coupled2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × Fig8C Pt)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (StepPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((deliverE (hooksSlotLocal cka prng fs mo M_sess) maxForwardJumps mo.cfg qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((deliverE (hooksFSMulti cka prng fs Δcka mo false false) maxForwardJumps mo.cfg qry).run esM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  rcases qry with ⟨P, c⟩
  have hhaltL : (esL.abort || esL.g.win) = false := by simp [hsync.habL, hsync.hwinL]
  have hhaltM : (esM.abort || esM.g.win) = false := by simp [hsync.habM, hsync.hwinM]
  have htr_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c
  cases htrL : esL.g.inTransit P.other c with
  | none =>
    have htrM : esM.g.inTransit P.other c = none := htr_eq.symm.trans htrL
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hhaltL, hhaltM, Bool.false_eq_true,
      ↓reduceIte, htrL, htrM, StateT.run_pure, simulateQ_pure]
    exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, hqep, hsync.mono_rem (Nat.le_succ rem)⟩⟩)
  | some r =>
    have htrM : esM.g.inTransit P.other c = some r := htr_eq.symm.trans htrL
    have hr_ep : r.pos.epoch = c.1.1 := hsync.inTransit_ep htrL
    rw [deliverE_some_run _ _ _ _ P c esL r hhaltL htrL,
        deliverE_some_run _ _ _ _ P c esM r hhaltM htrM,
        simulateQ_bind, simulateQ_bind, StateT.run_bind]
    refine Coupled2.bind
      (vRecv_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs P c (some r) (some r) hqep hsync) ?_
    rintro ⟨pL_val, hL'⟩ ⟨⟨pM_val, hM'⟩, sM⟩ hpost
    rcases hpost with hpL | ⟨hpL, hpM, tblM', tblL', rfl, hsync'⟩ |
        ⟨stL', stM', i', m', tblM', tblL', hpL, hpM, rfl, hsends_f, hle_qep, hacc, _⟩
    · dsimp only at hpL; subst pL_val
      simp only [simulateQ_pure]
      exact Coupled2.eq rfl (bind_pure _).symm (Coupled2.bind_dummy_r _ fun _ => Coupled2.pure (Or.inl rfl))
    · dsimp only at hpL hpM; subst pL_val pM_val
      simp only [simulateQ_pure, StateT.run_pure]
      exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl, hqep, hsync'⟩⟩)
    · dsimp only at hpL hpM; subst pL_val pM_val
      dsimp only
      rw [commitE_slotLocal_run, commitE_fsMulti_run]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure,
        _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_chall hsync.herase]
      exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl,
        epochQepInv_accept P stL' r.pos hqep (by rwa [hr_ep]) (by rwa [hr_ep]),
        hacc r.pos hr_ep⟩⟩)

private theorem deliverE_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × Fig8C Pt)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((deliverE (hooksSlotLocal cka prng fs mo M_sess) maxForwardJumps mo.cfg qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((deliverE (hooksFSMulti cka prng fs Δcka mo false false) maxForwardJumps mo.cfg qry).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((deliverE (hooksFSMulti cka prng fs Δcka mo false true) maxForwardJumps mo.cfg qry).run esM)).run
        (fun _ => false, tblL)) := by
  cases hheal : healedBy esL.g.tL (2 + Δcka) t
  · intro cka prng fs mo implF implT
    exact Coupled2.to_coupled3_m2 _
      (deliverE_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qry hqep
        (syncPaperMulti_to_phase2 (tblL' := tblL) hsync hheal))
      (fun _ _ _ h2 => stepPost2_imp_stepPost3 h2)
  · intro cka prng fs mo implF implT
    rcases qry with ⟨P, c⟩
    have hhaltL : (esL.abort || esL.g.win) = false := by simp [hsync.habL, hsync.hwinL]
    have hhaltM : (esM.abort || esM.g.win) = false := by simp [hsync.habM, hsync.hwinM]
    have htr_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c
    cases htrL : esL.g.inTransit P.other c with
    | none =>
      have htrM : esM.g.inTransit P.other c = none := htr_eq.symm.trans htrL
      unfold deliverE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hhaltL, hhaltM, Bool.false_eq_true,
        ↓reduceIte, htrL, htrM, StateT.run_pure, simulateQ_pure]
      exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, hqep,
        hsync.mono_rem (Nat.le_succ rem)⟩))))
    | some r =>
      have htrM : esM.g.inTransit P.other c = some r := htr_eq.symm.trans htrL
      have hr_ep : r.pos.epoch = c.1.1 := hsync.inTransit_ep htrL
      rw [deliverE_some_run _ _ _ _ P c esL r hhaltL htrL,
          deliverE_some_run _ _ _ _ P c esM r hhaltM htrM,
          deliverE_some_run _ _ _ _ P c esM r hhaltM htrM,
          simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
      refine Coupled3.bind
        (vRecv_coupled3 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs P c (some r) (some r) hqep hheal hsync) ?_
      rintro ⟨pL_val, hL'⟩ ⟨⟨p₀_val, hM₀'⟩, s₀⟩ ⟨⟨p₁_val, hM₁'⟩, s₁⟩ hpost
      rcases hpost with hpL | ⟨hp₁, hlf⟩ | ⟨hpL, hp₀, hp₁, hhM_eq, tblM', tblL', rfl, rfl, hsync'⟩ |
          ⟨stL', stM', i', m', tblM', tblL', hpL, hp₀, hp₁, hhM_eq, rfl, rfl, hsends_f, hle_qep, hacc, _⟩
      · dsimp only at hpL; subst pL_val
        simp only [simulateQ_pure]
        exact Coupled3.eq rfl (bind_pure _).symm (bind_pure _).symm
          (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.bind_dummy_m2 _ fun _ => Coupled3.pure (Or.inl rfl))
      · dsimp only at hp₁ hlf; subst p₁_val
        simp only [simulateQ_pure, StateT.run_pure]
        rcases pL_val with _ | _ | ⟨st', t', i', m'⟩
        · simp only [simulateQ_pure]
          exact Coupled3.eq rfl (bind_pure _).symm rfl
            (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
        · simp only [simulateQ_pure]
          exact Coupled3.eq rfl (bind_pure _).symm rfl
            (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
        · dsimp only; rw [commitE_slotLocal_run]; simp only [pure_bind, simulateQ_pure]
          exact Coupled3.eq rfl (bind_pure _).symm rfl
            (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
      · dsimp only at hpL hp₀ hp₁ hhM_eq; subst pL_val p₀_val p₁_val hM₁'
        simp only [simulateQ_pure, StateT.run_pure]
        exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl, hqep, hsync'⟩))))
      · dsimp only at hpL hp₀ hp₁ hhM_eq; subst pL_val p₀_val p₁_val hM₁'
        dsimp only
        rw [commitE_slotLocal_run, commitE_fsMulti_run, commitE_fsMulti_run]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure,
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_chall hsync.herase]
        exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl,
          epochQepInv_accept P stL' r.pos hqep (by rwa [hr_ep]) (by rwa [hr_ep]),
          hacc r.pos hr_ep⟩))))

private theorem injectE_coupled2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × Fig8C Pt)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (StepPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((injectE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.cfg qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((injectE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.cfg qry).run esM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  rcases qry with ⟨P, c⟩
  have hg_eq : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome || !(esL.g.safeInj (2 + Δcka))) =
      (esM.abort || esM.g.win || (esM.g.inTransit P.other c).isSome || !(esM.g.safeInj (2 + Δcka))) := by
    rw [hsync.habL, hsync.habM, hsync.hwinL, hsync.hwinM,
        _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c,
        _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_safeInj hsync.herase (2 + Δcka)]
  by_cases hgL : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome || !(esL.g.safeInj (2 + Δcka))) = true
  · have hgM := hg_eq.symm.trans hgL
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hgL, hgM, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, hqep, hsync.mono_rem (Nat.le_succ rem)⟩⟩)
  · simp only [Bool.not_eq_true] at hgL
    have hgM := hg_eq.symm.trans hgL
    rw [injectE_active_run _ _ _ _ P c esL hgL, injectE_active_run _ _ _ _ P c esM hgM,
        simulateQ_bind, simulateQ_bind, StateT.run_bind]
    refine Coupled2.bind
      (vRecv_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs P c none none hqep hsync) ?_
    rintro ⟨pL_val, hL'⟩ ⟨⟨pM_val, hM'⟩, sM⟩ hpost
    rcases hpost with hpL | ⟨hpL, hpM, tblM', tblL', rfl, hsync'⟩ |
        ⟨stL', stM', i', m', tblM', tblL', hpL, hpM, rfl, hsends_f, hle_qep, hacc, hnocommit⟩
    · dsimp only at hpL; subst pL_val
      simp only [simulateQ_pure]
      exact Coupled2.eq rfl (bind_pure _).symm (Coupled2.bind_dummy_r _ fun _ => Coupled2.pure (Or.inl rfl))
    · dsimp only at hpL hpM; subst pL_val pM_val
      simp only [simulateQ_pure, StateT.run_pure]
      exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl, hqep, hsync'⟩⟩)
    · dsimp only at hpL hpM; subst pL_val pM_val
      dsimp only
      have hlt_f : ¬ (qep + 1 < c.1.1) := by omega
      simp only [hlt_f, ↓reduceIte]
      have htriv_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hsync.herase (2 + Δcka) ⟨P.other, c.1.1, i'⟩
      by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
      · have htrivM := htriv_eq.symm.trans htriv
        simp only [htriv, htrivM, ↓reduceIte]
        rw [commitE_slotLocal_run, commitE_fsMulti_run]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure]
        exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl,
          epochQepInv_accept P stL' ⟨P.other, c.1.1, i'⟩ hqep hsends_f hle_qep, hacc ⟨P.other, c.1.1, i'⟩ rfl⟩⟩)
      · simp only [Bool.not_eq_true] at htriv
        have htrivM := htriv_eq.symm.trans htriv
        simp only [htriv, htrivM, Bool.false_eq_true, ↓reduceIte]
        by_cases hep_t : c.1.1 = t
        · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c.1.1 = true := by
            simp [mo, Mode.cfg, Config.auth, hep_t]
          simp only [hinj, ↓reduceIte, simulateQ_pure, StateT.run_pure]
          exact Coupled2.pure (Or.inr ⟨rfl, Or.inl ⟨hsync.habL, rfl, hsync.habM, rfl,
            eraseSt_win_true hsync.herase⟩⟩)
        · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c.1.1 = false :=
            injectFull_auth_of_ne hep_t
          simp only [hinj, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure]
          exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl, hqep, hnocommit hep_t⟩⟩)

private theorem injectE_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × Fig8C Pt)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((injectE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.cfg qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((injectE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.cfg qry).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((injectE (hooksFSMulti cka prng fs Δcka mo false true) (2 + Δcka) qep mo.cfg qry).run esM)).run
        (fun _ => false, tblL)) := by
  cases hheal : healedBy esL.g.tL (2 + Δcka) t
  · intro cka prng fs mo implF implT
    exact Coupled2.to_coupled3_m2 _
      (injectE_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qry hqep
        (syncPaperMulti_to_phase2 (tblL' := tblL) hsync hheal))
      (fun _ _ _ h2 => stepPost2_imp_stepPost3 h2)
  · intro cka prng fs mo implF implT
    rcases qry with ⟨P, c⟩
    have hg_eq : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome || !(esL.g.safeInj (2 + Δcka))) =
        (esM.abort || esM.g.win || (esM.g.inTransit P.other c).isSome || !(esM.g.safeInj (2 + Δcka))) := by
      rw [hsync.habL, hsync.habM, hsync.hwinL, hsync.hwinM,
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c,
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_safeInj hsync.herase (2 + Δcka)]
    by_cases hgL : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome || !(esL.g.safeInj (2 + Δcka))) = true
    · have hgM := hg_eq.symm.trans hgL
      unfold injectE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hgL, hgM, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, hqep,
        hsync.mono_rem (Nat.le_succ rem)⟩))))
    · simp only [Bool.not_eq_true] at hgL
      have hgM := hg_eq.symm.trans hgL
      rw [injectE_active_run _ _ _ _ P c esL hgL,
          injectE_active_run _ _ _ _ P c esM hgM,
          injectE_active_run _ _ _ _ P c esM hgM,
          simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
      refine Coupled3.bind
        (vRecv_coupled3 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs P c none none hqep hheal hsync) ?_
      rintro ⟨pL_val, hL'⟩ ⟨⟨p₀_val, hM₀'⟩, s₀⟩ ⟨⟨p₁_val, hM₁'⟩, s₁⟩ hpost
      rcases hpost with hpL | ⟨hp₁, hlf⟩ | ⟨hpL, hp₀, hp₁, hhM_eq, tblM', tblL', rfl, rfl, hsync'⟩ |
          ⟨stL', stM', i', m', tblM', tblL', hpL, hp₀, hp₁, hhM_eq, rfl, rfl, hsends_f, hle_qep, hacc, hnocommit⟩
      · dsimp only at hpL; subst pL_val
        simp only [simulateQ_pure]
        exact Coupled3.eq rfl (bind_pure _).symm (bind_pure _).symm
          (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.bind_dummy_m2 _ fun _ => Coupled3.pure (Or.inl rfl))
      · dsimp only at hp₁ hlf; subst p₁_val
        simp only [simulateQ_pure, StateT.run_pure]
        rcases pL_val with _ | _ | ⟨st', t', i', m'⟩
        · simp only [simulateQ_pure]
          exact Coupled3.eq rfl (bind_pure _).symm rfl
            (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
        · simp only [simulateQ_pure]
          exact Coupled3.eq rfl (bind_pure _).symm rfl
            (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
        · dsimp only
          split_ifs <;> simp only [commitE_slotLocal_run, pure_bind, simulateQ_pure] <;>
            exact Coupled3.eq rfl (bind_pure _).symm rfl
              (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
      · dsimp only at hpL hp₀ hp₁ hhM_eq; subst pL_val p₀_val p₁_val hM₁'
        simp only [simulateQ_pure, StateT.run_pure]
        exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl, hqep, hsync'⟩))))
      · dsimp only at hpL hp₀ hp₁ hhM_eq; subst pL_val p₀_val p₁_val hM₁'
        dsimp only
        have hlt_f : ¬ (qep + 1 < c.1.1) := by omega
        simp only [hlt_f, ↓reduceIte]
        have htriv_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hsync.herase (2 + Δcka) ⟨P.other, c.1.1, i'⟩
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        · have htrivM := htriv_eq.symm.trans htriv
          simp only [htriv, htrivM, ↓reduceIte]
          rw [commitE_slotLocal_run, commitE_fsMulti_run, commitE_fsMulti_run]
          simp only [pure_bind, simulateQ_pure, StateT.run_pure]
          exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl,
            epochQepInv_accept P stL' ⟨P.other, c.1.1, i'⟩ hqep hsends_f hle_qep, hacc ⟨P.other, c.1.1, i'⟩ rfl⟩))))
        · simp only [Bool.not_eq_true] at htriv
          have htrivM := htriv_eq.symm.trans htriv
          simp only [htriv, htrivM, Bool.false_eq_true, ↓reduceIte]
          by_cases hep_t : c.1.1 = t
          · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c.1.1 = true := by
              simp [mo, Mode.cfg, Config.auth, hep_t]
            simp only [hinj, ↓reduceIte, simulateQ_pure, StateT.run_pure]
            exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, hsync.habL, rfl, hsync.habM, rfl,
              eraseSt_win_true hsync.herase⟩)))
          · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c.1.1 = false :=
              injectFull_auth_of_ne hep_t
            simp only [hinj, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure]
            exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl,
              hqep, hnocommit hep_t⟩))))

private theorem deliverForgeE_coupled2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × Fig8C Pt × Fig8C Pt)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (StepPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((deliverForgeE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.cfg qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((deliverForgeE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.cfg qry).run esM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  rcases qry with ⟨P, c, c'⟩
  have hhaltL : (esL.abort || esL.g.win) = false := by simp [hsync.habL, hsync.hwinL]
  have hhaltM : (esM.abort || esM.g.win) = false := by simp [hsync.habM, hsync.hwinM]
  have htr_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c
  cases htrL : esL.g.inTransit P.other c with
  | none =>
    have htrM : esM.g.inTransit P.other c = none := htr_eq.symm.trans htrL
    unfold deliverForgeE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hhaltL, hhaltM, Bool.false_eq_true,
      ↓reduceIte, htrL, htrM, StateT.run_pure, simulateQ_pure]
    exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, hqep, hsync.mono_rem (Nat.le_succ rem)⟩⟩)
  | some r =>
    have htrM : esM.g.inTransit P.other c = some r := htr_eq.symm.trans htrL
    have hr_ep : r.pos.epoch = c.1.1 := hsync.inTransit_ep htrL
    have hg_eq : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) =
        ((esM.g.inTransit P.other c').isSome || esM.g.comp.contains r.pos || c.1 != c'.1) := by
      rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c',
          _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_comp hsync.herase]
    by_cases hgL : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) = true
    · have hgM := hg_eq.symm.trans hgL
      unfold deliverForgeE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hhaltL, hhaltM, Bool.false_eq_true,
        ↓reduceIte, htrL, htrM, hgL, hgM, StateT.run_pure, simulateQ_pure]
      exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, hqep, hsync.mono_rem (Nat.le_succ rem)⟩⟩)
    · simp only [Bool.not_eq_true] at hgL
      have hgM := hg_eq.symm.trans hgL
      have hc1_eq : c.1 = c'.1 := by
        have hneq : (c.1 != c'.1) = false := (Bool.or_eq_false_iff.mp hgL).2
        exact bne_eq_false_iff_eq.mp hneq
      have hc'_ep : c'.1.1 = r.pos.epoch := by rw [← hc1_eq, hr_ep]
      rw [deliverForgeE_active_run _ _ _ _ P c c' esL r hhaltL htrL hgL,
          deliverForgeE_active_run _ _ _ _ P c c' esM r hhaltM htrM hgM,
          simulateQ_bind, simulateQ_bind, StateT.run_bind]
      refine Coupled2.bind
        (vRecv_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs P c' none none hqep hsync) ?_
      rintro ⟨pL_val, hL'⟩ ⟨⟨pM_val, hM'⟩, sM⟩ hpost
      rcases hpost with hpL | ⟨hpL, hpM, tblM', tblL', rfl, hsync'⟩ |
          ⟨stL', stM', i', m', tblM', tblL', hpL, hpM, rfl, hsends_f, hle_qep, hacc, hnocommit⟩
      · dsimp only at hpL; subst pL_val
        simp only [simulateQ_pure]
        exact Coupled2.eq rfl (bind_pure _).symm (Coupled2.bind_dummy_r _ fun _ => Coupled2.pure (Or.inl rfl))
      · dsimp only at hpL hpM; subst pL_val pM_val
        simp only [simulateQ_pure, StateT.run_pure]
        exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl, hqep, hsync'⟩⟩)
      · dsimp only at hpL hpM; subst pL_val pM_val
        dsimp only
        have hguard_f : (decide (qep + 1 < c'.1.1) || c'.1.1 != r.pos.epoch) = false := by
          simp [hc'_ep, show ¬(qep + 1 < r.pos.epoch) by omega]
        simp only [hguard_f, Bool.false_eq_true, ↓reduceIte]
        have htriv_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hsync.herase (2 + Δcka) ⟨P.other, c'.1.1, i'⟩
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
        · have htrivM := htriv_eq.symm.trans htriv
          simp only [htriv, htrivM, ↓reduceIte]
          rw [commitE_slotLocal_run, commitE_fsMulti_run]
          simp only [pure_bind, simulateQ_pure, StateT.run_pure]
          exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl,
            epochQepInv_accept P stL' ⟨P.other, c'.1.1, i'⟩ hqep hsends_f hle_qep, hacc ⟨P.other, c'.1.1, i'⟩ rfl⟩⟩)
        · simp only [Bool.not_eq_true] at htriv
          have htrivM := htriv_eq.symm.trans htriv
          simp only [htriv, htrivM, Bool.false_eq_true, ↓reduceIte]
          by_cases hep_t : c'.1.1 = t
          · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c'.1.1 = true := by
              simp [mo, Mode.cfg, Config.auth, hep_t]
            simp only [hinj, ↓reduceIte, simulateQ_pure, StateT.run_pure]
            exact Coupled2.pure (Or.inr ⟨rfl, Or.inl ⟨hsync.habL, rfl, hsync.habM, rfl,
              eraseSt_win_true hsync.herase⟩⟩)
          · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c'.1.1 = false :=
              injectFull_auth_of_ne hep_t
            simp only [hinj, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure]
            exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM', tblL', rfl, hqep, hnocommit hep_t⟩⟩)

private theorem deliverForgeE_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (Dh : DHFun (BitVec 256) Pt) (hℓ : ℓ < 10 ^ 6)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × Fig8C Pt × Fig8C Pt)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((deliverForgeE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.cfg qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((deliverForgeE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.cfg qry).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((deliverForgeE (hooksFSMulti cka prng fs Δcka mo false true) (2 + Δcka) qep mo.cfg qry).run esM)).run
        (fun _ => false, tblL)) := by
  cases hheal : healedBy esL.g.tL (2 + Δcka) t
  · intro cka prng fs mo implF implT
    exact Coupled2.to_coupled3_m2 _
      (deliverForgeE_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qry hqep
        (syncPaperMulti_to_phase2 (tblL' := tblL) hsync hheal))
      (fun _ _ _ h2 => stepPost2_imp_stepPost3 h2)
  · intro cka prng fs mo implF implT
    rcases qry with ⟨P, c, c'⟩
    have hhaltL : (esL.abort || esL.g.win) = false := by simp [hsync.habL, hsync.hwinL]
    have hhaltM : (esM.abort || esM.g.win) = false := by simp [hsync.habM, hsync.hwinM]
    have htr_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c
    cases htrL : esL.g.inTransit P.other c with
    | none =>
      have htrM : esM.g.inTransit P.other c = none := htr_eq.symm.trans htrL
      unfold deliverForgeE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hhaltL, hhaltM, Bool.false_eq_true,
        ↓reduceIte, htrL, htrM, StateT.run_pure, simulateQ_pure]
      exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, hqep,
        hsync.mono_rem (Nat.le_succ rem)⟩))))
    | some r =>
      have htrM : esM.g.inTransit P.other c = some r := htr_eq.symm.trans htrL
      have hr_ep : r.pos.epoch = c.1.1 := hsync.inTransit_ep htrL
      have hg_eq : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) =
          ((esM.g.inTransit P.other c').isSome || esM.g.comp.contains r.pos || c.1 != c'.1) := by
        rw [_root_.CryptoGames.SM.Construction.AuthL11.eraseSt_inTransit hsync.herase P.other c',
            _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_comp hsync.herase]
      by_cases hgL : ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) = true
      · have hgM := hg_eq.symm.trans hgL
        unfold deliverForgeE
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hhaltL, hhaltM, Bool.false_eq_true,
          ↓reduceIte, htrL, htrM, hgL, hgM, StateT.run_pure, simulateQ_pure]
        exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, hqep,
          hsync.mono_rem (Nat.le_succ rem)⟩))))
      · simp only [Bool.not_eq_true] at hgL
        have hgM := hg_eq.symm.trans hgL
        have hc1_eq : c.1 = c'.1 := by
          have hneq : (c.1 != c'.1) = false := (Bool.or_eq_false_iff.mp hgL).2
          exact bne_eq_false_iff_eq.mp hneq
        have hc'_ep : c'.1.1 = r.pos.epoch := by rw [← hc1_eq, hr_ep]
        rw [deliverForgeE_active_run _ _ _ _ P c c' esL r hhaltL htrL hgL,
            deliverForgeE_active_run _ _ _ _ P c c' esM r hhaltM htrM hgM,
            deliverForgeE_active_run _ _ _ _ P c c' esM r hhaltM htrM hgM,
            simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
        refine Coupled3.bind
          (vRecv_coupled3 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs P c' none none hqep hheal hsync) ?_
        rintro ⟨pL_val, hL'⟩ ⟨⟨p₀_val, hM₀'⟩, s₀⟩ ⟨⟨p₁_val, hM₁'⟩, s₁⟩ hpost
        rcases hpost with hpL | ⟨hp₁, hlf⟩ | ⟨hpL, hp₀, hp₁, hhM_eq, tblM', tblL', rfl, rfl, hsync'⟩ |
            ⟨stL', stM', i', m', tblM', tblL', hpL, hp₀, hp₁, hhM_eq, rfl, rfl, hsends_f, hle_qep, hacc, hnocommit⟩
        · dsimp only at hpL; subst pL_val
          simp only [simulateQ_pure]
          exact Coupled3.eq rfl (bind_pure _).symm (bind_pure _).symm
            (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.bind_dummy_m2 _ fun _ => Coupled3.pure (Or.inl rfl))
        · dsimp only at hp₁ hlf; subst p₁_val
          simp only [simulateQ_pure, StateT.run_pure]
          rcases pL_val with _ | _ | ⟨st', t', i', m'⟩
          · simp only [simulateQ_pure]
            exact Coupled3.eq rfl (bind_pure _).symm rfl
              (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
          · simp only [simulateQ_pure]
            exact Coupled3.eq rfl (bind_pure _).symm rfl
              (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
          · dsimp only
            split_ifs <;> simp only [commitE_slotLocal_run, pure_bind, simulateQ_pure] <;>
              exact Coupled3.eq rfl (bind_pure _).symm rfl
                (Coupled3.bind_dummy_m1 _ fun _ => Coupled3.pure (Or.inr (Or.inl ⟨rfl, hlf⟩)))
        · dsimp only at hpL hp₀ hp₁ hhM_eq; subst pL_val p₀_val p₁_val hM₁'
          simp only [simulateQ_pure, StateT.run_pure]
          exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl, hqep, hsync'⟩))))
        · dsimp only at hpL hp₀ hp₁ hhM_eq; subst pL_val p₀_val p₁_val hM₁'
          dsimp only
          have hguard_f : (decide (qep + 1 < c'.1.1) || c'.1.1 != r.pos.epoch) = false := by
            simp [hc'_ep, show ¬(qep + 1 < r.pos.epoch) by omega]
          simp only [hguard_f, Bool.false_eq_true, ↓reduceIte]
          have htriv_eq := _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_trivial hsync.herase (2 + Δcka) ⟨P.other, c'.1.1, i'⟩
          by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c'.1.1, i'⟩ = true
          · have htrivM := htriv_eq.symm.trans htriv
            simp only [htriv, htrivM, ↓reduceIte]
            rw [commitE_slotLocal_run, commitE_fsMulti_run, commitE_fsMulti_run]
            simp only [pure_bind, simulateQ_pure, StateT.run_pure]
            exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl,
              epochQepInv_accept P stL' ⟨P.other, c'.1.1, i'⟩ hqep hsends_f hle_qep, hacc ⟨P.other, c'.1.1, i'⟩ rfl⟩))))
          · simp only [Bool.not_eq_true] at htriv
            have htrivM := htriv_eq.symm.trans htriv
            simp only [htriv, htrivM, Bool.false_eq_true, ↓reduceIte]
            by_cases hep_t : c'.1.1 = t
            · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c'.1.1 = true := by
                simp [mo, Mode.cfg, Config.auth, hep_t]
              simp only [hinj, ↓reduceIte, simulateQ_pure, StateT.run_pure]
              exact Coupled3.pure (Or.inr (Or.inr (Or.inl ⟨rfl, hsync.habL, rfl, hsync.habM, rfl,
                eraseSt_win_true hsync.herase⟩)))
            · have hinj : mo.cfg.injectFull (Msg := LibsignalMsgPublicPart × Plain ℓ) c'.1.1 = false :=
                injectFull_auth_of_ne hep_t
              simp only [hinj, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure]
              exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM', tblL', rfl, rfl,
                hqep, hnocommit hep_t⟩))))

/-! ### 8. Dispatch, Multi-Step `OracleComp` Induction, and Per-Key `LeAdd` Assembly -/

private theorem healedBy_afterCorr_false_of_false {St Msg C : Type} {g : GameState St Msg C}
    {Δ t : ℕ} (P : Party) (h : healedBy g.tL Δ t = false) :
    healedBy (g.afterCorr P).tL Δ t = false := by
  unfold GameState.afterCorr
  exact healedBy_leak_mono_false g _ Δ t h

private theorem challE_coupled2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × (LibsignalMsgPublicPart × Plain ℓ) × (LibsignalMsgPublicPart × Plain ℓ) × Option (BitVec 256))
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (StepPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((challE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.cfg mo.policy qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((challE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  rw [challE_auth_run, challE_auth_run]
  simp only [simulateQ_pure, StateT.run_pure]
  have hsync' : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false rem esL esM tblM tblL :=
    { hsync with hlen := Nat.le_trans (Nat.add_le_add_left (Nat.le_succ rem) _) hsync.hlen }
  exact Coupled2.pure (Or.inr ⟨rfl, Or.inr ⟨tblM, tblL, rfl, hqep, hsync'⟩⟩)

private theorem challE_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) {rem : ℕ}
    (qry : Party × (LibsignalMsgPublicPart × Plain ℓ) × (LibsignalMsgPublicPart × Plain ℓ) × Option (BitVec 256))
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((challE (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep mo.cfg mo.policy qry).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((challE (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((challE (hooksFSMulti cka prng fs Δcka mo false true) (2 + Δcka) qep mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  rw [challE_auth_run, challE_auth_run, challE_auth_run]
  simp only [simulateQ_pure, StateT.run_pure]
  have hsync' : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true rem esL esM tblM tblL :=
    { hsync with hlen := Nat.le_trans (Nat.add_le_add_left (Nat.le_succ rem) _) hsync.hlen }
  exact Coupled3.pure (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, tblM, tblL, rfl, rfl, hqep, hsync'⟩))))

private theorem implEDFPaper_inr_coupled2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (hℓ : ℓ < 10 ^ 6)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) (rem : ℕ)
    (qry : (specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (hbad : _root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF
      (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (.inr qry) = false)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    Coupled2 (StepPost2 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((implEDFPaper (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inr qry)).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((implEDFPaper (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr qry)).run esM)).run
        (fun _ => false, tblM)) := by
  intro cka prng fs mo implF
  have hms : fs.maxSkip = maxForwardJumps := rfl
  rw [hms]
  have hheal0 : healedBy esL.g.tL (2 + Δcka) t = false := hsync.hhealed rfl
  rcases qry with ((((qryTx | qryCh) | qryDel) | qryInj) | P) | qryDf
  · have hshA : atomicShortPubB qryTx.2.1.1 = true := by
      rcases qryTx with ⟨_, m, _⟩
      simpa [_root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF] using hbad
    have hsh : qryTx.2.1.1.shortB = true :=
      Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB_imp_shortB hshA
    exact transmitE_coupled_phase2 C Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryTx hsh hqep hsync
      (fun _ => hheal0) (fun s₁L hep _ => healedBy_epMgmt_false esL.g s₁L (2 + Δcka) qep qryTx.1 qryTx.2.2.isSome t hep hheal0)
  · exact challE_coupled2 C Dh encPt encT idOf Δcka qep M_sess t tL ks bs qryCh hqep hsync
  · exact deliverE_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryDel hqep hsync
  · exact injectE_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryInj hqep hsync
  · exact corrEPaper_coupled_phase2 C Dh encPt encT idOf Δcka qep M_sess t tL hvg ks bs P hqep hsync
      (fun _ _ => healedBy_afterCorr_false_of_false P hheal0) (fun _ => hheal0)
  · exact deliverForgeE_coupled2 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryDf hqep hsync

private theorem implEDFPaper_inr_coupled3 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (hℓ : ℓ < 10 ^ 6)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) (rem : ℕ)
    (qry : (specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (hbad : _root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF
      (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (.inr qry) = false)
    {esL : _} {esM : _} {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true (rem + 1) esL esM tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, tL, t⟩
    let implF := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 false)
    let implT := _root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (hp 0 0 true)
    Coupled3 (StepPost3 C Dh ℓ encPt encT idOf Δcka qep M_sess t tL ks bs rem)
      (simulateQ (keySlotFixedImpl ks)
        ((implEDFPaper (hooksSlotLocal cka prng fs mo M_sess) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inr qry)).run esL))
      ((simulateQ (pubFsMultiImpl implF)
        ((implEDFPaper (hooksFSMulti cka prng fs Δcka mo false false) (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr qry)).run esM)).run
        (fun _ => false, tblM))
      ((simulateQ (pubFsMultiImpl implT)
        ((implEDFPaper (hooksFSMulti cka prng fs Δcka mo false true) (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr qry)).run esM)).run
        (fun _ => false, tblL)) := by
  intro cka prng fs mo implF implT
  have hms : fs.maxSkip = maxForwardJumps := rfl
  rw [hms]
  rcases qry with ((((qryTx | qryCh) | qryDel) | qryInj) | P) | qryDf
  · have hshA : atomicShortPubB qryTx.2.1.1 = true := by
      rcases qryTx with ⟨_, m, _⟩
      simpa [_root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF] using hbad
    have hsh : qryTx.2.1.1.shortB = true :=
      Computational.Proofs.ReductionDsl.Fig8Atomic.atomicShortPubB_imp_shortB hshA
    exact transmitE_coupled3 C Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryTx hsh hqep hsync
  · exact challE_coupled3 C Dh encPt encT idOf Δcka qep M_sess t tL ks bs qryCh hqep hsync
  · exact deliverE_coupled3 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryDel hqep hsync
  · exact injectE_coupled3 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryInj hqep hsync
  · exact corrEPaper_coupled3 C Dh encPt encT idOf Δcka qep M_sess t tL hvg ks bs P hqep hsync
  · exact deliverForgeE_coupled3 C hD Dh hℓ encPt encT idOf Δcka qep M_sess t tL ks bs qryDf hqep hsync

private theorem run_coupled_phase2 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (hℓ : ℓ < 10 ^ 6)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (q_rem : ℕ)
    (oa : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : oa.IsQueryBoundP (fun x => x.isRight = true) q_rem)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) oa)
    (esL : _) (esM : _) (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs false q_rem esL esM tblM tblL) :
    LeOne
      (runSlotFixed (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep M_sess ⟨true, tL, t⟩ oa esL ks)
      (runMultiPaper C Dh encPt encT idOf Δcka qep ⟨true, tL, t⟩ false oa esM (fun _ => false, tblM)) := by
  induction oa using OracleComp.inductionOn generalizing q_rem esL esM tblM tblL with
  | pure _ =>
    simp only [runSlotFixed, runMultiPaper, simulateQ_pure, StateT.run_pure, pure_bind,
      Bool.false_eq_true, ↓reduceIte, map_pure, LeOne]
    have hauth : authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy esL =
        authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy esM := by
      simp only [authOut, hsync.habL, hsync.habM, hsync.hwinL, hsync.hwinM,
        _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_authOK hsync.herase]
    rw [hauth]
  | query_bind x cont ih =>
    unfold SendMsgsOkDF at hsh
    rw [isQueryBoundP_query_bind_iff] at hq hsh
    unfold runSlotFixed runMultiPaper
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, map_bind]
    rcases x with n | qry
    · have hq' : ∀ u, (cont u).IsQueryBoundP (fun x => x.isRight = true) q_rem := by
        intro u; simpa using hq.2 u
      have hsh' : ∀ u, SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (cont u) := by
        intro u; unfold SendMsgsOkDF; simpa [_root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF] using hsh.2 u
      rw [implEDFPaper_inl_run, implEDFPaper_inl_run, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        keySlotFixedImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        pubFsMultiImpl_inl_run, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind]
      exact leOne_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ =>
        ih u q_rem (hq' u) (hsh' u) esL esM tblM tblL hqep hsync
    · cases q_rem with
      | zero => simp at hq
      | succ q' =>
        have hq' : ∀ u, (cont u).IsQueryBoundP (fun x => x.isRight = true) q' := by
          intro u; simpa using hq.2 u
        have hbad : _root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF
            (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (.inr qry) = false := by
          rcases hsh.1 with h0 | h0
          · exact Bool.eq_false_iff.mpr h0
          · omega
        have hsh' : ∀ u, SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (cont u) := by
          intro u; unfold SendMsgsOkDF; simpa [hbad] using hsh.2 u
        have hstep2 := implEDFPaper_inr_coupled2 ℓ C Dh hD encPt encT idOf hℓ
          Δcka qep M_sess t tL hvg ks bs q' qry hbad hqep hsync
        refine hstep2.to_leOne fun rL rM hpost => ?_
        rcases hpost with habL | ⟨hans, hwin | ⟨tblM', tblL', hstM, hqep', hsync'⟩⟩
        · exact leOne_slot_abort_terminal _ _ _ _ _ _ _ (cont rL.1) rL.2 ks habL
        · rcases hwin with ⟨hab1, hw1, hab2, hw2, her⟩
          rw [hans]
          exact leOne_both_halt_terminal C Dh encPt encT idOf Δcka qep M_sess ⟨true, tL, t⟩
            (cont rM.1.1) rL.2 rM.1.2 ks rM.2 (by simp [hw1]) (hab1.trans hab2.symm) (hw1.trans hw2.symm) her
        · rw [hans, hstM]
          exact ih rM.1.1 q' (hq' rM.1.1) (hsh' rM.1.1) rL.2 rM.1.2 tblM' tblL' hqep' hsync'

private theorem run_coupled_phase1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (hℓ : ℓ < 10 ^ 6)
    (Δcka qep M_sess t : ℕ) (tL : Option ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (q_rem : ℕ)
    (oa : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : oa.IsQueryBoundP (fun x => x.isRight = true) q_rem)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) oa)
    (esL : _) (esM : _) (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hqep : EpochQepInv qep esL.g)
    (hsync : SyncPaperMulti C Dh ℓ encPt encT idOf Δcka M_sess t tL ks bs true q_rem esL esM tblM tblL) :
    LeAdd
      (runSlotFixed (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep M_sess ⟨true, tL, t⟩ oa esL ks)
      (runMultiPaper C Dh encPt encT idOf Δcka qep ⟨true, tL, t⟩ false oa esM (fun _ => false, tblM))
      (runMultiPaper C Dh encPt encT idOf Δcka qep ⟨true, tL, t⟩ true oa esM (fun _ => false, tblL)) := by
  induction oa using OracleComp.inductionOn generalizing q_rem esL esM tblM tblL with
  | pure _ =>
    refine leAdd_of_le_main ?_
    simp only [runSlotFixed, runMultiPaper, simulateQ_pure, StateT.run_pure, pure_bind,
      Bool.false_eq_true, ↓reduceIte, map_pure, LeOne]
    have hauth : authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy esL =
        authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy esM := by
      simp only [authOut, hsync.habL, hsync.habM, hsync.hwinL, hsync.hwinM,
        _root_.CryptoGames.SM.Construction.AuthL11.eraseSt_authOK hsync.herase]
    rw [hauth]
  | query_bind x cont ih =>
    unfold SendMsgsOkDF at hsh
    rw [isQueryBoundP_query_bind_iff] at hq hsh
    unfold runSlotFixed runMultiPaper
    rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, StateT.run_bind,
      bind_assoc, bind_assoc, bind_assoc,
      simulateQ_bind, simulateQ_bind, simulateQ_bind,
      StateT.run_bind, StateT.run_bind, map_bind, map_bind]
    rcases x with n | qry
    · have hq' : ∀ u, (cont u).IsQueryBoundP (fun x => x.isRight = true) q_rem := by
        intro u; simpa using hq.2 u
      have hsh' : ∀ u, SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (cont u) := by
        intro u; unfold SendMsgsOkDF; simpa [_root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF] using hsh.2 u
      rw [implEDFPaper_inl_run, implEDFPaper_inl_run, implEDFPaper_inl_run,
        simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        keySlotFixedImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        pubFsMultiImpl_inl_run, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind]
      exact leAdd_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ =>
        ih u q_rem (hq' u) (hsh' u) esL esM tblM tblL hqep hsync
    · cases q_rem with
      | zero => simp at hq
      | succ q' =>
        have hq' : ∀ u, (cont u).IsQueryBoundP (fun x => x.isRight = true) q' := by
          intro u; simpa using hq.2 u
        have hbad : _root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF
            (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (.inr qry) = false := by
          rcases hsh.1 with h0 | h0
          · exact Bool.eq_false_iff.mpr h0
          · omega
        have hsh' : ∀ u, SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (cont u) := by
          intro u; unfold SendMsgsOkDF; simpa [hbad] using hsh.2 u
        have hstep3 := implEDFPaper_inr_coupled3 ℓ C Dh hD encPt encT idOf hℓ
          Δcka qep M_sess t tL hvg ks bs q' qry hbad hqep hsync
        refine hstep3.to_leAdd fun rL r₀ r₁ hpost => ?_
        rcases hpost with habL | ⟨habR, hlfR⟩ | ⟨hans, hab1, hw1, hab2, hw2, her⟩ |
            ⟨hans, tblM', tblL', hst0, hqep', hsync2⟩ |
            ⟨hans0, hans1, hes1, tblM', tblL', hst0, hst1, hqep', hsync1⟩
        · exact leAdd_of_le_main (leOne_slot_abort_terminal _ _ _ _ _ _ _ (cont rL.1) rL.2 ks habL)
        · exact leAdd_of_la_one (evalDist_runMultiPaper_true_eq_one_of_lfWin C Dh encPt encT idOf
            Δcka qep ⟨true, tL, t⟩ (cont r₁.1.1) r₁.1.2 r₁.2 habR hlfR)
        · rw [hans]
          exact leAdd_both_halt_terminal C Dh encPt encT idOf Δcka qep M_sess ⟨true, tL, t⟩
            (cont r₀.1.1) rL.2 r₀.1.2 ks r₀.2 (by simp [hw1]) (hab1.trans hab2.symm) (hw1.trans hw2.symm) her
        · rw [hans, hst0]
          exact leAdd_of_le_main (run_coupled_phase2 ℓ C Dh hD encPt encT idOf hℓ
            Δcka qep M_sess t tL hvg ks bs q' (cont r₀.1.1) (hq' r₀.1.1) (hsh' r₀.1.1)
            rL.2 r₀.1.2 tblM' tblL' hqep' hsync2)
        · rw [← hans0, ← hans1, hes1, hst0, hst1]
          exact ih rL.1 q' (hq' rL.1) (hsh' rL.1) rL.2 r₀.1.2 tblM' tblL' hqep' hsync1

private theorem localAuthDFPaper_perKey_coupling {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q M_sess Δcka qep : ℕ) (hM : q + 1 ≤ M_sess) (tL : Option ℕ) (t : ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool) :
    LeAdd
      (simulateQ (keySlotFixedImpl ks)
        (localAuthDFPaperSlot (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          lam Δcka qep M_sess tL t A))
      (Prod.fst <$> (simulateQ (pubFsMultiImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
          (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps (hp 0 0 false)))
          (redFSAuthDFPaperMulti (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep false tL t A)).run
        (fun _ => false, fun i => hInit (bs i) (.seed (ks i))))
      (Prod.fst <$> (simulateQ (pubFsMultiImpl (_root_.CryptoVerification.E2E.Signed.SessionFS.fsImpl
          (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf)
          (lChainPRG C.F) maxForwardJumps (hp 0 0 true)))
          (redFSAuthDFPaperMulti (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep true tL t A)).run
        (fun _ => false, fun i => hInit (bs i) (.seed (ks i)))) := by
  have hA_inr : A.IsQueryBoundP (fun x => x.isRight = true) q :=
    hq.of_imp fun x hx => by cases x <;> [cases hx; rfl]
  have hInit := init_coupled3 (ℓ := ℓ) C Dh encPt encT idOf lam Δcka q M_sess t hM tL ks bs
  simp only [localAuthDFPaperSlot, redFSAuthDFPaperMulti, runFSMultiDFPaper, bind_assoc]
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, map_bind,
    simulateQ_bind, StateT.run_bind, map_bind]
  refine hInit.to_leAdd fun rL r₀ r₁ hpost => ?_
  rcases hpost with ⟨vA, vB, hrL, hr1, hst0, hst1, hsync0⟩
  have hqep0 := epochQepInv_init
    (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (C := Header Pt × ℕ × LibsignalCiphertextWithSalt32)
    qep (fun P => match P with | .A => vA | .B => vB) false
  rcases rL with ⟨vsL, hL⟩
  dsimp only at hrL hsync0
  subst hrL
  rw [hr1, hst0, hst1]
  cases hp1 : healedBy (none : Option ℕ) (2 + Δcka) t
  · rw [hp1] at hsync0
    exact leAdd_of_le_main (run_coupled_phase2 ℓ C Dh hD encPt encT idOf hℓ
      Δcka qep M_sess t tL hvg ks bs q A hA_inr hsh _ r₀.1 _ _ hqep0 hsync0)
  · rw [hp1] at hsync0
    exact run_coupled_phase1 ℓ C Dh hD encPt encT idOf hℓ
      Δcka qep M_sess t tL hvg ks bs q A hA_inr hsh _ r₀.1 _ _ hqep0 hsync0

private abbrev paperFsImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (la : Bool) :=
  fsImpl (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) maxForwardJumps (hp 0 0 la)

private theorem simulateQ_sessLift_keySlotImpl_run_loc {K α : Type} (ks : ℕ → K)
    (m : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) :
    (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.sessLift
      (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.keySlotImpl K)) m).run ks =
      (fun a => (a, ks)) <$> simulateQ (keySlotFixedImpl ks) m := by
  induction m using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    rw [StateT.run_bind, map_bind]
    rcases t with n | ⟨sIdx, u⟩
    · simp only [CryptoVerification.E2E.Signed.SessionRouter.sessLift_inl, keySlotFixedImpl,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun x => ih x
    · cases u
      have hstep :
          (CryptoVerification.E2E.Signed.SessionRouter.sessLift
            (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.keySlotImpl K)
            (.inr ⟨sIdx, ()⟩)).run ks = Pure.pure (ks sIdx, ks) := by
        simp only [CryptoVerification.E2E.Signed.SessionRouter.sessLift_inr,
          CryptoVerification.E2E.Signed.SessionRouter.sessLiftCore,
          Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.keySlotImpl]
        change (fun r : K × K => (r.1, Function.update ks sIdx r.2)) <$>
          (Pure.pure (ks sIdx, ks sIdx) : ProbComp (K × K)) = _
        simp
      simp only [monadLift_self, hstep, keySlotFixedImpl, QueryImpl.add_apply_inr]
      exact ih (ks sIdx)

private theorem simulateQ_sessLift_keySlotImpl_fst_loc {K α : Type} (ks : ℕ → K)
    (m : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) :
    Prod.fst <$> (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.sessLift
      (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.keySlotImpl K)) m).run ks =
      simulateQ (keySlotFixedImpl ks) m := by
  rw [simulateQ_sessLift_keySlotImpl_run_loc, Functor.map_map]; simp

private theorem sampleOrSlot_pos_run_loc {T Sig K I : Type} [SampleableType K]
    (M_sess sIdx : ℕ) (st : LocalSlotState T Sig K I)
    (hc : (decide (sIdx < M_sess) && !st.usedSlot sIdx) = true) :
    (sampleOrSlot M_sess sIdx).run st =
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩))) >>=
        fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
          Pure.pure ((k : K), { st with usedSlot := Function.update st.usedSlot sIdx true })) := by
  simp only [sampleOrSlot, hc, ↓reduceIte, StateT.run_bind, StateT.run_get,
    StateT.run_modify, pure_bind]
  rfl

private inductive ZeroOffSlot {K α : Type} (M_sess : ℕ) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α → Prop where
  | pure (a : α) : ZeroOffSlot M_sess (Pure.pure a)
  | query_bind {t : (unifSpec + multiSessSpec (keySlotSpec K)).Domain}
      {k : (unifSpec + multiSessSpec (keySlotSpec K)).Range t →
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α}
      (ht : CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess t = false)
      (hk : ∀ y, ZeroOffSlot M_sess (k y)) :
      ZeroOffSlot M_sess (liftM (OracleSpec.query t) >>= k)

private theorem ZeroOffSlot.bind {K α β : Type} {M_sess : ℕ}
    {mx : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α}
    {f : α → OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) β}
    (h : ZeroOffSlot M_sess mx) (hf : ∀ a, ZeroOffSlot M_sess (f a)) :
    ZeroOffSlot M_sess (mx >>= f) := by
  induction h with
  | pure a => rw [pure_bind]; exact hf a
  | query_bind ht _ ih => rw [bind_assoc]; exact ZeroOffSlot.query_bind ht ih

private theorem ZeroOffSlot.query_false {K : Type} {M_sess : ℕ}
    (t : (unifSpec + multiSessSpec (keySlotSpec K)).Domain)
    (ht : CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess t = false) :
    ZeroOffSlot M_sess
      (liftM (OracleSpec.query t) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) := by
  rw [← bind_pure (liftM (OracleSpec.query t) :
    OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _)]
  exact ZeroOffSlot.query_bind ht fun y => ZeroOffSlot.pure y

private theorem ZeroOffSlot.to_isQueryBoundP {K α : Type} {M_sess : ℕ}
    {oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α}
    (h : ZeroOffSlot M_sess oa) :
    oa.IsQueryBoundP (fun t => CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess t = true) 0 := by
  induction h with
  | pure _ => exact isQueryBoundP_pure _ _ 0
  | query_bind ht _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [ht]), fun y => by simpa [ht] using ih y⟩

private theorem ZeroOffSlot.sampleT_run {K HS α : Type} (M_sess : ℕ) [SampleableType α] (h : HS) :
    ZeroOffSlot M_sess ((StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run h) := by
  rw [StateT.run_lift]
  suffices hs : ∀ oa : ProbComp α,
      ZeroOffSlot M_sess (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α) by
    exact (hs ($ᵗ α : ProbComp α)).bind fun a => ZeroOffSlot.pure (a, h)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => exact ZeroOffSlot.pure a
  | query_bind t k ih => exact (ZeroOffSlot.query_false (.inl t) rfl).bind ih

private theorem ZeroOffSlot.sampleOrSlot_run {T Sig K I : Type} [SampleableType K]
    (M_sess sIdx : ℕ) (st : LocalSlotState T Sig K I) :
    ZeroOffSlot M_sess ((sampleOrSlot M_sess sIdx).run st) := by
  by_cases hc : (decide (sIdx < M_sess) && !st.usedSlot sIdx) = true
  · rw [sampleOrSlot_pos_run_loc M_sess sIdx st hc]
    have hoff :
        CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess
          (.inr ⟨sIdx, ()⟩ : (unifSpec + multiSessSpec (keySlotSpec K)).Domain) = false := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp [CryptoVerification.E2E.Signed.SessionRouter.sessOffRange, Nat.not_le.mpr hc.1]
    exact (ZeroOffSlot.query_false _ hoff).bind fun _ => ZeroOffSlot.pure _
  · dsimp only [sampleOrSlot]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact ZeroOffSlot.sampleT_run M_sess st

private theorem ZeroOffSlot.lookupSlotFL_run {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (M_sess : ℕ) (Ik : I) (st : LocalSlotState T Sig K I) :
    ZeroOffSlot M_sess ((lookupSlotFL M_sess Ik).run st) := by
  dsimp only [lookupSlotFL]
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact ZeroOffSlot.pure _
  · rw [StateT.run_bind]
    refine (ZeroOffSlot.sampleOrSlot_run M_sess _ st).bind fun p1 => ?_
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    exact ZeroOffSlot.pure _

private theorem ZeroOffSlot.regSessSlot_run {T Sig K I : Type} [DecidableEq I]
    (M_sess : ℕ) (Ik : I) (st : LocalSlotState T Sig K I) :
    ZeroOffSlot M_sess ((regSessSlot Ik).run st) := by
  dsimp only [regSessSlot]
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp only [StateT.run_pure, StateT.run_bind, StateT.run_modify, pure_bind] <;>
    exact ZeroOffSlot.pure _

private theorem ZeroOffSlot.regSessOfSlot_run {T Sig K I : Type} [DecidableEq I]
    (M_sess : ℕ) (sid : Option I) (st : LocalSlotState T Sig K I) :
    ZeroOffSlot M_sess ((regSessOfSlot sid).run st) := by
  cases sid with
  | none => exact ZeroOffSlot.pure _
  | some Ik =>
    dsimp only [regSessOfSlot]
    rw [map_eq_bind_pure_comp, StateT.run_bind]
    exact (ZeroOffSlot.regSessSlot_run M_sess Ik st).bind fun _ => ZeroOffSlot.pure _

private theorem ZeroOffSlot.rootSlotL_run {KR T Sig K I : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (mo : Mode) (M_sess ep : ℕ) (Ik : I) (σ : Sig)
    (st : LocalSlotState T Sig K I) :
    ZeroOffSlot M_sess ((rootSlotL prng mo M_sess ep Ik σ).run st) := by
  dsimp only [rootSlotL]
  split
  · exact ZeroOffSlot.pure _
  · split
    · split
      · rw [StateT.run_bind]
        refine (ZeroOffSlot.sampleT_run M_sess st).bind fun p1 => ?_
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        exact (ZeroOffSlot.sampleOrSlot_run M_sess _ p1.2).bind fun _ => ZeroOffSlot.pure _
      · rw [StateT.run_bind]
        exact (ZeroOffSlot.lookupSlotFL_run M_sess Ik st).bind fun _ => ZeroOffSlot.pure _
    · split
      · rw [StateT.run_bind]
        exact (ZeroOffSlot.sampleT_run M_sess st).bind fun _ => ZeroOffSlot.pure _
      · exact ZeroOffSlot.pure _

private theorem ZeroOffSlot.vSend_run {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (M_sess : ℕ)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E) (P : Party)
    (vp : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (m : M) (pair : Option (M × M)) (r0 : Option CCoins)
    (st : LocalSlotState T Sig K I) :
    ZeroOffSlot M_sess ((_root_.CryptoGames.SM.Engine.vSend (hooksSlotLocal cka prng fs mo M_sess)
      ctx P vp m pair r0).run st) := by
  dsimp only [_root_.CryptoGames.SM.Engine.vSend]
  split
  · rw [StateT.run_bind]
    have hss : ZeroOffSlot M_sess
        (((hooksSlotLocal cka prng fs mo M_sess).startSend
          ctx P (vp.tcur + 1) vp.γ vp.root r0).run st) := by
      dsimp only [hooksSlotLocal]
      cases r0 with
      | none =>
        rw [StateT.run_bind]
        refine (ZeroOffSlot.sampleT_run M_sess st).bind fun p1 => ?_
        rw [StateT.run_bind]
        refine (ZeroOffSlot.rootSlotL_run prng mo M_sess _ _ _ p1.2).bind fun p2 => ?_
        rcases p2 with ⟨⟨_, _, sid⟩, st2⟩
        rw [StateT.run_bind]
        refine (ZeroOffSlot.regSessOfSlot_run M_sess sid st2).bind fun _ => ?_
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact ZeroOffSlot.pure _
      | some c =>
        simp only [pure_bind, StateT.run_bind]
        refine (ZeroOffSlot.rootSlotL_run prng mo M_sess _ _ _ st).bind fun p2 => ?_
        rcases p2 with ⟨⟨_, _, sid⟩, st2⟩
        dsimp only
        refine (ZeroOffSlot.regSessOfSlot_run M_sess sid st2).bind fun _ => ?_
        simp only [StateT.run_modify, StateT.run_pure, pure_bind]
        exact ZeroOffSlot.pure _
    refine hss.bind fun p => ?_
    rcases p.1 with _ | ⟨_, _, _, _⟩
    · simp only [pure_bind, StateT.run_pure]; exact ZeroOffSlot.pure _
    · simp only [pure_bind, hooksSlotLocal, StateT.run_pure]
      exact ZeroOffSlot.pure _
  · simp only [pure_bind]
    cases vp.vS with
    | none => simp only [StateT.run_pure]; exact ZeroOffSlot.pure _
    | some v => simp only [hooksSlotLocal, StateT.run_pure, pure_bind]; exact ZeroOffSlot.pure _

private theorem ZeroOffSlot.vRecv_run {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (M_sess : ℕ)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E) (P : Party)
    (vp : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (st : LocalSlotState T Sig K I) :
    ZeroOffSlot M_sess ((_root_.CryptoGames.SM.Engine.vRecv (hooksSlotLocal cka prng fs mo M_sess)
      ctx P vp c rec).run st) := by
  dsimp only [_root_.CryptoGames.SM.Engine.vRecv]
  split
  · exact ZeroOffSlot.pure _
  · split
    · cases c.1.2 with
      | none => simp only [pure_bind, StateT.run_pure]; exact ZeroOffSlot.pure _
      | some Tn =>
        rw [StateT.run_bind]
        have hsr : ZeroOffSlot M_sess
            (((hooksSlotLocal cka prng fs mo M_sess).startRecv
              ctx P c.1.1 vp.γ vp.root Tn).run st) := by
          dsimp only [hooksSlotLocal]
          rw [StateT.run_bind, StateT.run_get, pure_bind]
          cases st.loc.cache c.1.1 with
          | some entry =>
            rcases entry with ⟨Tc, σc, k, idx?⟩
            by_cases hTc : Tc = Tn
            · simp only [hTc, ↓reduceIte, StateT.run_pure]; exact ZeroOffSlot.pure _
            · simp only [hTc, ↓reduceIte]
              split
              · split
                · exact ZeroOffSlot.pure _
                · rw [StateT.run_bind]
                  refine (ZeroOffSlot.lookupSlotFL_run M_sess _ st).bind fun p1 => ?_
                  rw [StateT.run_bind]
                  exact (ZeroOffSlot.regSessSlot_run M_sess _ p1.2).bind fun _ => ZeroOffSlot.pure _
              · exact ZeroOffSlot.pure _
          | none =>
            dsimp only
            split
            · split
              · exact ZeroOffSlot.pure _
              · rw [StateT.run_bind]
                refine (ZeroOffSlot.lookupSlotFL_run M_sess _ st).bind fun p1 => ?_
                rw [StateT.run_bind]
                exact (ZeroOffSlot.regSessSlot_run M_sess _ p1.2).bind fun _ => ZeroOffSlot.pure _
            · exact ZeroOffSlot.pure _
        refine hsr.bind fun p => ?_
        rcases p.1 with _ | (_ | ⟨γ', σ', rsv⟩)
        · simp only [pure_bind, StateT.run_pure]; exact ZeroOffSlot.pure _
        · simp only [pure_bind, StateT.run_pure]; exact ZeroOffSlot.pure _
        · simp only [pure_bind, Function.update_self, hooksSlotLocal]
          cases fs.receive rsv.1 c.1 c.2 with
          | none => simp only [StateT.run_pure, pure_bind]; exact ZeroOffSlot.pure _
          | some out =>
            rcases out with ⟨_, _, _⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact ZeroOffSlot.pure _
    · simp only [pure_bind]
      cases vp.vR c.1.1 with
      | none => simp only [StateT.run_pure]; exact ZeroOffSlot.pure _
      | some rsv =>
        dsimp only [hooksSlotLocal]
        cases fs.receive rsv.1 c.1 c.2 with
        | none => simp only [StateT.run_pure, pure_bind]; exact ZeroOffSlot.pure _
        | some out =>
          rcases out with ⟨_, _, _⟩
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroOffSlot.pure _

private theorem ZeroOffSlot.liftH_run {T Sig K I Γ SS RS M E α : Type} {M_sess : ℕ}
    {m : SlotHM T Sig K I α}
    (hm : ∀ st : LocalSlotState T Sig K I, ZeroOffSlot M_sess (m.run st))
    (es : EStateSlot Γ T Sig SS RS M E K I) :
    ZeroOffSlot M_sess ((_root_.CryptoGames.SM.Engine.liftH m).run es) := by
  dsimp only [_root_.CryptoGames.SM.Engine.liftH, StateT.run]
  exact (hm es.h).bind fun _ => ZeroOffSlot.pure _

private theorem commitE_pure_run_ob {ι : Type} {S : OracleSpec.{0, 0} ι}
    {H Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq M] [DecidableEq T] [DecidableEq E]
    (hk : Hooks S H Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (hcomm : ∀ s₁ P old new, hk.commit s₁ P old new = pure (some new))
    (s : Ctx Γv T Sv SSv RSv M E) (P : Party) (old new : VP Γv T Sv SSv RSv)
    (pos : _root_.CryptoGames.SM.Pos)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) H) :
    (_root_.CryptoGames.SM.Engine.commitE hk s P old new pos).run es =
      pure (some { (s.accept P new pos) with st := Function.update (s.accept P new pos).st P new }, es) := by
  cases es
  simp [_root_.CryptoGames.SM.Engine.commitE, hcomm]

private theorem localAuthDFPaperSlot_offRange {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    (localAuthDFPaperSlot cka prng fs lam Δcka qep M_sess tL t A).IsQueryBoundP
      (fun u => CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess u = true) 0 := by
  apply ZeroOffSlot.to_isQueryBoundP
  dsimp only [localAuthDFPaperSlot]
  let mo : Mode := ⟨true, tL, t⟩
  have hinit : ZeroOffSlot M_sess ((initSlotLocal cka prng fs lam mo M_sess).run {}) := by
    dsimp only [initSlotLocal]
    rw [StateT.run_bind]
    refine (ZeroOffSlot.sampleT_run (K := K) (α := KR) M_sess ({} : LocalSlotState T Sig K I)).bind fun p1 => ?_
    rw [StateT.run_bind]
    refine (ZeroOffSlot.sampleT_run (K := K) (α := KC) M_sess p1.2).bind fun p2 => ?_
    rw [StateT.run_bind]
    refine (ZeroOffSlot.rootSlotL_run prng mo M_sess 0 lam (prng.init p1.1) p2.2).bind fun p3 => ?_
    rcases p3 with ⟨⟨_, _, sid⟩, st3⟩
    dsimp only
    rw [StateT.run_bind]
    refine (ZeroOffSlot.regSessOfSlot_run M_sess sid st3).bind fun _ => ?_
    exact ZeroOffSlot.pure _
  let hk := hooksSlotLocal cka prng fs mo M_sess
  have hsim : ∀ (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
      (es : EStateSlot Γ T Sig SS RS M E K I),
      ZeroOffSlot M_sess
        ((simulateQ (implEDFPaper hk (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro es; exact ZeroOffSlot.pure (a, es)
    | query_bind qry k ih =>
      intro es
      rw [simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind]
      refine ZeroOffSlot.bind ?_ (fun p => ih p.1 p.2)
      rcases qry with n | ((((⟨P, m, rc⟩ | qryCh) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
      · rw [implEDFPaper_inl_run]
        exact (ZeroOffSlot.query_false (.inl n) rfl).bind fun _ => ZeroOffSlot.pure _
      · change ZeroOffSlot M_sess ((transmitE hk (2 + Δcka) qep mo.policy (P, m, rc)).run es)
        dsimp only [transmitE]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOffSlot.pure _
        · split
          · exact ZeroOffSlot.pure _
          · split
            · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
                StateT.run_pure, pure_bind]
              exact ZeroOffSlot.pure _
            · rw [StateT.run_bind]
              refine (ZeroOffSlot.liftH_run
                (fun st => ZeroOffSlot.vSend_run cka prng fs mo M_sess _ P _ m none rc st) es).bind fun p => ?_
              rcases p.1 with _ | ⟨_, _⟩ <;>
                simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
                  StateT.run_pure, pure_bind] <;>
                exact ZeroOffSlot.pure _
      · change ZeroOffSlot M_sess ((challE hk (2 + Δcka) qep mo.cfg mo.policy qryCh).run es)
        rw [challE_auth_run]
        exact ZeroOffSlot.pure _
      · change ZeroOffSlot M_sess ((deliverE hk fs.maxSkip mo.cfg (P, c)).run es)
        dsimp only [deliverE]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOffSlot.pure _
        · split
          · exact ZeroOffSlot.pure _
          · rw [StateT.run_bind]
            refine (ZeroOffSlot.liftH_run
              (fun st => ZeroOffSlot.vRecv_run cka prng fs mo M_sess _ P _ c _ st) es).bind fun p => ?_
            rcases p.1 with _ | (_ | ⟨st', t', i', m'⟩)
            · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
                StateT.run_pure, pure_bind]
              exact ZeroOffSlot.pure _
            · dsimp only
              split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                exact ZeroOffSlot.pure _
            · dsimp only
              rw [StateT.run_bind, commitE_pure_run_ob hk (fun _ _ _ _ => rfl)]
              simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure]
              exact ZeroOffSlot.pure _
      · change ZeroOffSlot M_sess ((injectE hk (2 + Δcka) qep mo.cfg (P, c)).run es)
        dsimp only [injectE]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOffSlot.pure _
        · rw [StateT.run_bind]
          refine (ZeroOffSlot.liftH_run
            (fun st => ZeroOffSlot.vRecv_run cka prng fs mo M_sess _ P _ c none st) es).bind fun p => ?_
          rcases p.1 with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
              StateT.run_pure, pure_bind]
            exact ZeroOffSlot.pure _
          · exact ZeroOffSlot.pure _
          · dsimp only
            split
            · exact ZeroOffSlot.pure _
            · split
              · rw [StateT.run_bind, commitE_pure_run_ob hk (fun _ _ _ _ => rfl)]
                simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure]
                exact ZeroOffSlot.pure _
              · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                  exact ZeroOffSlot.pure _
      · change ZeroOffSlot M_sess ((corrEPaper hk mo.policy P).run es)
        dsimp only [corrEPaper]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOffSlot.pure _
        · split
          · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
              StateT.run_pure, pure_bind]
            exact ZeroOffSlot.pure _
          · rw [StateT.run_bind]
            refine (ZeroOffSlot.liftH_run (fun st => by
              dsimp only [hk, hooksSlotLocal]
              exact ZeroOffSlot.pure _) es).bind fun p => ?_
            rcases p.1 with _ | _ <;>
              simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
                StateT.run_pure, pure_bind] <;>
              exact ZeroOffSlot.pure _
      · change ZeroOffSlot M_sess ((deliverForgeE hk (2 + Δcka) qep mo.cfg (P, c, c')).run es)
        dsimp only [deliverForgeE]
        rw [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ZeroOffSlot.pure _
        · split
          · exact ZeroOffSlot.pure _
          · split
            · exact ZeroOffSlot.pure _
            · rw [StateT.run_bind]
              refine (ZeroOffSlot.liftH_run
                (fun st => ZeroOffSlot.vRecv_run cka prng fs mo M_sess _ P _ c' none st) es).bind fun p => ?_
              rcases p.1 with _ | (_ | ⟨st', t', i', m'⟩)
              · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
                  StateT.run_pure, pure_bind]
                exact ZeroOffSlot.pure _
              · exact ZeroOffSlot.pure _
              · dsimp only
                split
                · exact ZeroOffSlot.pure _
                · split
                  · rw [StateT.run_bind, commitE_pure_run_ob hk (fun _ _ _ _ => rfl)]
                    simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure]
                    exact ZeroOffSlot.pure _
                  · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                      exact ZeroOffSlot.pure _
  refine hinit.bind fun ⟨vs, _⟩ => ?_
  cases vs with
  | none => exact ZeroOffSlot.pure _
  | some pair =>
    rcases pair with ⟨_, _⟩
    exact (hsim A _).bind fun _ => ZeroOffSlot.pure _

private def EqDistRelLoc {α β : Type} (R : α → β → Prop)
    (mL : ProbComp α) (mR : ProbComp β) : Prop :=
  ∀ (fL : α → ProbComp Bool) (fR : β → ProbComp Bool),
    (∀ a b, R a b → 𝒟[fL a] = 𝒟[fR b]) →
    𝒟[mL >>= fL] = 𝒟[mR >>= fR]

private theorem EqDistRelLoc.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    EqDistRelLoc R (Pure.pure a) (Pure.pure b) := by
  intro fL fR hf; simp only [pure_bind]; exact hf a b h

private theorem EqDistRelLoc.bind {α₁ β₁ α₂ β₂ : Type}
    {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {mL : ProbComp α₁} {mR : ProbComp β₁}
    {kL : α₁ → ProbComp α₂} {kR : β₁ → ProbComp β₂}
    (hm : EqDistRelLoc R₁ mL mR)
    (hk : ∀ a b, R₁ a b → EqDistRelLoc R₂ (kL a) (kR b)) :
    EqDistRelLoc R₂ (mL >>= kL) (mR >>= kR) := by
  intro fL fR hf; simp only [bind_assoc]
  exact hm (fun a => kL a >>= fL) (fun b => kR b >>= fR) fun a b hab => hk a b hab fL fR hf

private theorem EqDistRelLoc.same {ξ α β : Type} {R : α → β → Prop}
    (c : ProbComp ξ) (gL : ξ → α) (gR : ξ → β) (hg : ∀ x, R (gL x) (gR x)) :
    EqDistRelLoc R (c >>= fun x => Pure.pure (gL x)) (c >>= fun x => Pure.pure (gR x)) := by
  intro fL fR hf; simp only [bind_assoc, pure_bind]
  exact evalDist_bind_congr _ _ _ fun x => hf _ _ (hg x)

private def LazySlotSyncPaper {T Sig K I : Type}
    (tbl : ℕ → Option K) (st : LocalSlotState T Sig K I)
    (hLoc : LState T Sig K I) : Prop :=
  st.loc = hLoc ∧ ∀ i, st.usedSlot i = false → tbl i = none

private abbrev lazySlotImplLoc (K : Type) [SampleableType K] :=
  _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift
    (_root_.CryptoVerification.E2E.Signed.SessionRouter.lazyInit ($ᵗ K : ProbComp K)
      (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.keySlotImpl K))

private theorem sim_sampleT_lazy_run_loc {K α : Type} [SampleableType K] [SampleableType α]
    (tbl : ℕ → Option K) :
    (simulateQ (lazySlotImplLoc K)
      (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run tbl =
      (($ᵗ α : ProbComp α) >>= fun a => Pure.pure (a, tbl)) := by
  suffices h : ∀ oa : ProbComp α,
      (simulateQ (lazySlotImplLoc K)
        (liftM oa : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α)).run tbl =
        (oa >>= fun a => Pure.pure (a, tbl)) from
    h ($ᵗ α : ProbComp α)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change (simulateQ (lazySlotImplLoc K)
      ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inl t)) :
        OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) _) >>=
      fun u => (liftM (k u) : OracleComp (unifSpec + multiSessSpec (keySlotSpec K)) α))).run tbl = _
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, lazySlotImplLoc]
    simp only [_root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_inl,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private def HMRelPaper {T Sig K I α : Type} :
    (α × LState T Sig K I) →
    ((α × LocalSlotState T Sig K I) × (ℕ → Option K)) → Prop :=
  fun ⟨aL, hLoc⟩ ⟨⟨aR, st⟩, tbl⟩ => aL = aR ∧ LazySlotSyncPaper tbl st hLoc

private theorem eqDist_sampleT_hm_loc {T Sig K I α : Type} [SampleableType K] [SampleableType α]
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((StateT.lift (sampleT (tspec := _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) α)).run hLoc))
      ((simulateQ (lazySlotImplLoc K)
        ((StateT.lift (sampleT (tspec := multiSessSpec (keySlotSpec K)) α)).run st)).run tbl) := by
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure,
    _root_.CryptoGames.SM.Construction.AuthL11.simulateQ_lImpl_sampleT,
    StateT.run_bind, sim_sampleT_lazy_run_loc, bind_assoc, pure_bind]
  exact EqDistRelLoc.same ($ᵗ α : ProbComp α) (fun a => (a, hLoc)) (fun a => ((a, st), tbl))
    fun _ => ⟨rfl, hsync⟩

private theorem eqDist_sampleOrSlot_loc {T Sig K I : Type} [SampleableType K]
    (M_sess sIdx : ℕ)
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((StateT.lift (sampleT (tspec := _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) K)).run hLoc))
      ((simulateQ (lazySlotImplLoc K) ((sampleOrSlot M_sess sIdx).run st)).run tbl) := by
  by_cases hc : (decide (sIdx < M_sess) && !st.usedSlot sIdx) = true
  · have hus : st.usedSlot sIdx = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc; exact hc.2
    have htbl : tbl sIdx = none := hsync.2 sIdx hus
    rw [sampleOrSlot_pos_run_loc M_sess sIdx st hc]
    intro fL fR hf
    have hL :
        (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
          ((StateT.lift (sampleT (tspec := _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) K)).run hLoc) >>= fL) =
          (($ᵗ K : ProbComp K) >>= fun k => fL (k, hLoc)) := by
      simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure,
        _root_.CryptoGames.SM.Construction.AuthL11.simulateQ_lImpl_sampleT, bind_assoc, pure_bind]
    have hq :
        (lazySlotImplLoc K (.inr ⟨sIdx, ()⟩)).run tbl =
          (($ᵗ K : ProbComp K) >>= fun (k : (unifSpec + multiSessSpec (keySlotSpec K)).Range (.inr ⟨sIdx, ()⟩)) =>
            Pure.pure (k, Function.update tbl sIdx (some (k : K)))) := by
      simp [-bind_pure_comp, lazySlotImplLoc,
        _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_inr,
        _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLiftCore,
        _root_.CryptoVerification.E2E.Signed.SessionRouter.lazyInit,
        Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.keySlotImpl,
        htbl, map_eq_bind_pure_comp]
      refine bind_congr fun k => ?_
      change (Pure.pure (k, k) : ProbComp ((keySlotSpec K).Range () × K)) >>= _ = _
      rw [pure_bind]
    have hR :
        (((simulateQ (lazySlotImplLoc K)
            ((liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (keySlotSpec K)) (.inr ⟨sIdx, ()⟩))) >>=
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
    exact eqDist_sampleT_hm_loc hsync

private theorem eqDist_hm_bind_loc {T Sig K I α β : Type} [SampleableType K]
    {mL : HM _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LState T Sig K I) α}
    {mR : SlotHM T Sig K I α}
    {kL : α → HM _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LState T Sig K I) β}
    {kR : α → SlotHM T Sig K I β}
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hm : EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl (mL.run hLoc))
      ((simulateQ (lazySlotImplLoc K) (mR.run st)).run tbl))
    (hk : ∀ x tbl' st' hLoc', LazySlotSyncPaper tbl' st' hLoc' →
      EqDistRelLoc HMRelPaper
        (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl ((kL x).run hLoc'))
        ((simulateQ (lazySlotImplLoc K) ((kR x).run st')).run tbl')) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl ((mL >>= kL).run hLoc))
      ((simulateQ (lazySlotImplLoc K) ((mR >>= kR).run st)).run tbl) := by
  simp only [StateT.run_bind, simulateQ_bind]
  exact hm.bind fun ⟨xL, hLoc'⟩ ⟨⟨xR, st'⟩, tbl'⟩ ⟨hx, hsync'⟩ => by
    subst hx; exact hk xL tbl' st' hLoc' hsync'

private theorem eqDist_lookupFL_loc {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (M_sess : ℕ) (Ik : I)
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Construction.AuthL11.lookupFL Ik).run hLoc))
      ((simulateQ (lazySlotImplLoc K) ((lookupSlotFL M_sess Ik).run st)).run tbl) := by
  dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.lookupFL, lookupSlotFL]
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind, hsync.1]
  cases hLoc.table.lookup Ik with
  | some k =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact EqDistRelLoc.pure ⟨rfl, hsync⟩
  | none =>
    refine eqDist_hm_bind_loc (eqDist_sampleOrSlot_loc M_sess _ hsync)
      fun k tbl1 st1 hLoc1 hsync1 => ?_
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
    exact EqDistRelLoc.pure ⟨rfl, by rw [hsync1.1], hsync1.2⟩

private theorem eqDist_regSess_loc {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (Ik : I)
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Construction.AuthL11.regSess Ik).run hLoc))
      ((simulateQ (lazySlotImplLoc K) ((regSessSlot Ik).run st)).run tbl) := by
  dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.regSess, regSessSlot]
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind, hsync.1]
  split
  · simp only [StateT.run_pure, simulateQ_pure]
    exact EqDistRelLoc.pure ⟨rfl, hsync⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_modify, StateT.run_pure,
      pure_bind, simulateQ_pure, hsync.1]
    exact EqDistRelLoc.pure ⟨rfl, rfl, hsync.2⟩

private theorem eqDist_regSessOf_loc {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (sid : Option I)
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Construction.AuthL11.regSessOf sid).run hLoc))
      ((simulateQ (lazySlotImplLoc K) ((regSessOfSlot sid).run st)).run tbl) := by
  cases sid with
  | none =>
    dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.regSessOf, regSessOfSlot]
    simp only [StateT.run_pure, simulateQ_pure]
    exact EqDistRelLoc.pure ⟨rfl, hsync⟩
  | some Ik =>
    dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.regSessOf, regSessOfSlot]
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    refine eqDist_hm_bind_loc (eqDist_regSess_loc Ik hsync) fun idx tbl1 st1 hLoc1 hsync1 => ?_
    simp only [Function.comp_def, StateT.run_pure, simulateQ_pure]
    exact EqDistRelLoc.pure ⟨rfl, hsync1⟩

private theorem eqDist_rootL_loc {KR T Sig K I : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (mo : Mode) (M_sess ep : ℕ) (Ik : I) (σ : Sig)
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Construction.AuthL11.rootL prng mo ep Ik σ).run hLoc))
      ((simulateQ (lazySlotImplLoc K) ((rootSlotL prng mo M_sess ep Ik σ).run st)).run tbl) := by
  dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.rootL, rootSlotL]
  split
  · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, hsync⟩
  · split
    · split
      · refine eqDist_hm_bind_loc (eqDist_sampleT_hm_loc hsync) fun Ir tbl1 st1 hLoc1 hsync1 => ?_
        simp only [StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind]
        refine (eqDist_sampleOrSlot_loc M_sess st1.loc.sessions.length hsync1).bind
          fun ⟨kL, hLoc2⟩ ⟨⟨kR, st2⟩, tbl2⟩ ⟨hk, hsync2⟩ => ?_
        subst hk
        simp only [StateT.run_pure, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, hsync2⟩
      · refine eqDist_hm_bind_loc (eqDist_lookupFL_loc M_sess Ik hsync)
          fun k tbl1 st1 hLoc1 hsync1 => ?_
        simp only [StateT.run_pure, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, hsync1⟩
    · split
      · refine eqDist_hm_bind_loc (eqDist_sampleT_hm_loc hsync) fun Ir tbl1 st1 hLoc1 hsync1 => ?_
        simp only [StateT.run_pure, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, hsync1⟩
      · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, hsync⟩

private theorem eqDist_vSend_loc {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (M_sess : ℕ)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E) (P : Party)
    (vp : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (m : M) (pair : Option (M × M)) (r0 : Option CCoins)
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Engine.vSend
          (_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal cka prng fs mo)
          ctx P vp m pair r0).run hLoc))
      ((simulateQ (lazySlotImplLoc K)
        ((_root_.CryptoGames.SM.Engine.vSend (hooksSlotLocal cka prng fs mo M_sess)
          ctx P vp m pair r0).run st)).run tbl) := by
  dsimp only [_root_.CryptoGames.SM.Engine.vSend]
  by_cases hs : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hs, ↓reduceIte]
    refine eqDist_hm_bind_loc (K := K) ?_ fun res tbl1 st1 hLoc1 hsync1 => ?_
    · dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal, hooksSlotLocal]
      cases r0 with
      | none =>
        refine eqDist_hm_bind_loc (eqDist_sampleT_hm_loc hsync) fun coins tbl1 st1 hLoc1 hsync1 => ?_
        refine eqDist_hm_bind_loc (eqDist_rootL_loc prng mo M_sess _ _ _ hsync1)
          fun ⟨σ', kVal, sid⟩ tbl2 st2 hLoc2 hsync2 => ?_
        refine eqDist_hm_bind_loc (eqDist_regSessOf_loc sid hsync2)
          fun idx? tbl3 st3 hLoc3 hsync3 => ?_
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, by rw [hsync3.1], hsync3.2⟩
      | some c =>
        simp only [pure_bind]
        refine eqDist_hm_bind_loc (eqDist_rootL_loc prng mo M_sess _ _ _ hsync)
          fun ⟨σ', kVal, sid⟩ tbl2 st2 hLoc2 hsync2 => ?_
        refine eqDist_hm_bind_loc (eqDist_regSessOf_loc sid hsync2)
          fun idx? tbl3 st3 hLoc3 hsync3 => ?_
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, by rw [hsync3.1], hsync3.2⟩
    · rcases res with _ | ⟨γ', T', σ', ss⟩
      · simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, hsync1⟩
      · dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal, hooksSlotLocal]
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, hsync1⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, pure_bind]
    cases vp.vS with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact EqDistRelLoc.pure ⟨rfl, hsync⟩
    | some v =>
      dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal, hooksSlotLocal]
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact EqDistRelLoc.pure ⟨rfl, hsync⟩

private theorem eqDist_vRecv_loc {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (M_sess : ℕ)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E) (P : Party)
    (vp : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (c : Header T × E) (rec : Option (Record M (Header T × E)))
    {tbl : ℕ → Option K} {st : LocalSlotState T Sig K I} {hLoc : LState T Sig K I}
    (hsync : LazySlotSyncPaper tbl st hLoc) :
    EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Engine.vRecv
          (_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal cka prng fs mo)
          ctx P vp c rec).run hLoc))
      ((simulateQ (lazySlotImplLoc K)
        ((_root_.CryptoGames.SM.Engine.vRecv (hooksSlotLocal cka prng fs mo M_sess)
          ctx P vp c rec).run st)).run tbl) := by
  rcases c with ⟨⟨ep, hdrT⟩, e⟩
  dsimp only [_root_.CryptoGames.SM.Engine.vRecv]
  by_cases hbad : (vp.id.sendsIn ep || decide (vp.tcur + 1 < ep)) = true
  · simp only [hbad, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact EqDistRelLoc.pure ⟨rfl, hsync⟩
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    by_cases heq : ep = vp.tcur + 1
    · simp only [heq, ↓reduceIte]
      cases hdrT with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, hsync⟩
      | some Tn =>
        refine eqDist_hm_bind_loc (K := K) ?_ fun res tbl1 st1 hLoc1 hsync1 => ?_
        · dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal, hooksSlotLocal]
          rw [StateT.run_bind, StateT.run_get, pure_bind,
              StateT.run_bind, StateT.run_get, pure_bind]
          dsimp only
          rw [hsync.1]
          have hmiss : EqDistRelLoc HMRelPaper
              (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
                ((if mo.auth && vp.tcur + 1 = mo.tStar then
                    if mo.tL.isSome && mo.tStar = mo.tH then pure none
                    else do
                      let kk := cka.receive vp.γ Tn
                      let k' ← _root_.CryptoGames.SM.Construction.AuthL11.lookupFL kk.2
                      let idx ← _root_.CryptoGames.SM.Construction.AuthL11.regSess kk.2
                      pure (some (some (kk.1, (prng.up vp.root kk.2).1, (fs.initReceiver k', some idx))))
                  else pure (some none)).run hLoc))
              ((simulateQ (lazySlotImplLoc K)
                ((if mo.auth && vp.tcur + 1 = mo.tStar then
                    if mo.tL.isSome && mo.tStar = mo.tH then pure none
                    else do
                      let kk := cka.receive vp.γ Tn
                      let k' ← lookupSlotFL M_sess kk.2
                      let idx ← regSessSlot kk.2
                      pure (some (some (kk.1, (prng.up vp.root kk.2).1, (fs.initReceiver k', some idx))))
                  else pure (some none)).run st)).run tbl) := by
            by_cases h1 : (mo.auth && decide (vp.tcur + 1 = mo.tStar)) = true
            · simp only [h1, ↓reduceIte]
              by_cases h2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
              · simp only [h2, ↓reduceIte, StateT.run_pure, simulateQ_pure]
                exact EqDistRelLoc.pure ⟨rfl, hsync⟩
              · simp only [h2, Bool.false_eq_true, ↓reduceIte]
                refine eqDist_hm_bind_loc (eqDist_lookupFL_loc M_sess _ hsync)
                  fun k' tbl1 st1 hLoc1 hsync1 => ?_
                refine eqDist_hm_bind_loc (eqDist_regSess_loc _ hsync1)
                  fun idx tbl2 st2 hLoc2 hsync2 => ?_
                simp only [StateT.run_pure, simulateQ_pure]
                exact EqDistRelLoc.pure ⟨rfl, hsync2⟩
            · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
              exact EqDistRelLoc.pure ⟨rfl, hsync⟩
          rcases hLoc.cache (vp.tcur + 1) with _ | ⟨Tc, σc, k, idx?⟩
          · exact hmiss
          · by_cases hTc : Tc = Tn
            · simp only [hTc, ↓reduceIte, StateT.run_pure, simulateQ_pure]
              exact EqDistRelLoc.pure ⟨rfl, hsync⟩
            · simp only [hTc, ↓reduceIte]
              exact hmiss
        · rcases res with _ | (_ | ⟨γ', σ', rsv⟩)
          · simp only [pure_bind, StateT.run_pure, simulateQ_pure]
            exact EqDistRelLoc.pure ⟨rfl, hsync1⟩
          · simp only [pure_bind, StateT.run_pure, simulateQ_pure]
            exact EqDistRelLoc.pure ⟨rfl, hsync1⟩
          · simp only [pure_bind, Function.update_self]
            refine eqDist_hm_bind_loc (K := K) ?_ fun out tbl2 st2 hLoc2 hsync2 => ?_
            · dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal, hooksSlotLocal]
              cases fs.receive rsv.1 (vp.tcur + 1, some Tn) e with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure]
                exact EqDistRelLoc.pure ⟨rfl, hsync1⟩
              | some triple =>
                rcases triple with ⟨rs', i, m⟩
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
                exact EqDistRelLoc.pure ⟨rfl, by rw [hsync1.1], hsync1.2⟩
            · rcases out with _ | (_ | ⟨_, _, _⟩) <;>
                simp only [StateT.run_pure, simulateQ_pure] <;>
                exact EqDistRelLoc.pure ⟨rfl, hsync2⟩
    · simp only [heq, ↓reduceIte, pure_bind]
      cases vp.vR ep with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact EqDistRelLoc.pure ⟨rfl, hsync⟩
      | some rsv =>
        refine eqDist_hm_bind_loc (K := K) ?_ fun out tbl2 st2 hLoc2 hsync2 => ?_
        · dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.hooksLocal, hooksSlotLocal]
          cases fs.receive rsv.1 (ep, hdrT) e with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure]
            exact EqDistRelLoc.pure ⟨rfl, hsync⟩
          | some triple =>
            rcases triple with ⟨rs', i, m⟩
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
            exact EqDistRelLoc.pure ⟨rfl, by rw [hsync.1], hsync.2⟩
        · rcases out with _ | (_ | ⟨_, _, _⟩) <;>
            simp only [StateT.run_pure, simulateQ_pure] <;>
            exact EqDistRelLoc.pure ⟨rfl, hsync2⟩

private def EMRelPaper {Γ T Sig SS RS M E K I α : Type} :
    (α × _root_.CryptoGames.SM.Construction.AuthL11.EStateL Γ T Sig SS RS M E K I) →
    ((α × EStateSlot Γ T Sig SS RS M E K I) × (ℕ → Option K)) → Prop :=
  fun ⟨aL, esL⟩ ⟨⟨aR, esR⟩, tbl⟩ =>
    aL = aR ∧ esL.g = esR.g ∧ esL.abort = esR.abort ∧ LazySlotSyncPaper tbl esR.h esL.h

private theorem eqDist_liftH_paper {Γ T Sig SS RS M E K I α : Type} [SampleableType K]
    {mL : HM _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LState T Sig K I) α}
    {mR : SlotHM T Sig K I α}
    {tbl : ℕ → Option K}
    {esL : _root_.CryptoGames.SM.Construction.AuthL11.EStateL Γ T Sig SS RS M E K I}
    {esR : EStateSlot Γ T Sig SS RS M E K I}
    (hg : esL.g = esR.g) (habort : esL.abort = esR.abort)
    (hm : EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl (mL.run esL.h))
      ((simulateQ (lazySlotImplLoc K) (mR.run esR.h)).run tbl)) :
    EqDistRelLoc EMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Engine.liftH mL).run esL))
      ((simulateQ (lazySlotImplLoc K)
        ((_root_.CryptoGames.SM.Engine.liftH mR).run esR)).run tbl) := by
  dsimp only [_root_.CryptoGames.SM.Engine.liftH, StateT.run]
  simp only [simulateQ_bind, simulateQ_pure]
  refine hm.bind fun ⟨aL, hLoc'⟩ ⟨⟨aR, st'⟩, tbl'⟩ ⟨ha, hsync'⟩ => ?_
  subst ha
  exact EqDistRelLoc.pure ⟨rfl, hg, habort, hsync'⟩

private theorem localAuthDFPaperSlot_lazy_eq {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[_root_.CryptoGames.SM.Construction.AuthL11.localAuthDFPaper cka prng fs lam Δcka qep tL t A] =
      𝒟[Prod.fst <$> (simulateQ (lazySlotImplLoc K)
        (localAuthDFPaperSlot cka prng fs lam Δcka qep M_sess tL t A)).run (fun _ => none)] := by
  let mo : Mode := ⟨true, tL, t⟩
  have hinit : EqDistRelLoc HMRelPaper
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
        ((_root_.CryptoGames.SM.Construction.AuthL11.initLocal cka prng fs lam mo).run {}))
      ((simulateQ (lazySlotImplLoc K)
        ((initSlotLocal cka prng fs lam mo M_sess).run {})).run (fun _ => none)) := by
    dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.initLocal, initSlotLocal]
    have hsync0 : LazySlotSyncPaper (K := K) (fun _ => none) ({} : LocalSlotState T Sig K I) {} :=
      ⟨rfl, fun _ _ => rfl⟩
    refine eqDist_hm_bind_loc (eqDist_sampleT_hm_loc hsync0) fun kr tbl1 st1 hLoc1 hsync1 => ?_
    refine eqDist_hm_bind_loc (eqDist_sampleT_hm_loc hsync1) fun kc tbl2 st2 hLoc2 hsync2 => ?_
    refine eqDist_hm_bind_loc (eqDist_rootL_loc prng mo M_sess 0 lam (prng.init kr) hsync2)
      fun ⟨σ0, k0, sid⟩ tbl3 st3 hLoc3 hsync3 => ?_
    refine eqDist_hm_bind_loc (eqDist_regSessOf_loc sid hsync3)
      fun idx? tbl4 st4 hLoc4 hsync4 => ?_
    simp only [StateT.run_pure, simulateQ_pure]
    exact EqDistRelLoc.pure ⟨rfl, hsync4⟩
  let hkL := _root_.CryptoGames.SM.Construction.AuthL11.hooksLocal cka prng fs mo
  let hkR := hooksSlotLocal cka prng fs mo M_sess
  have hsim : ∀ (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
      (g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E) (abort : Bool)
      (tbl : ℕ → Option K) (st : LocalSlotState T Sig K I) (hLoc : LState T Sig K I),
      LazySlotSyncPaper tbl st hLoc →
      EqDistRelLoc EMRelPaper
        (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
          ((simulateQ (implEDFPaper hkL (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run
            { g := g, h := hLoc, abort := abort }))
        ((simulateQ (lazySlotImplLoc K)
          ((simulateQ (implEDFPaper hkR (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run
            { g := g, h := st, abort := abort })).run tbl) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro g abort tbl st hLoc hsync
      simp only [simulateQ_pure, StateT.run_pure]
      exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
    | query_bind qry k ih =>
      intro g abort tbl st hLoc hsync
      rw [simulateQ_query_bind, simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind]
      refine EqDistRelLoc.bind (R₁ := EMRelPaper) ?_ ?_
      · rcases qry with n | ((((⟨P, m, rc⟩ | qryCh) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
        · rw [implEDFPaper_inl_run, implEDFPaper_inl_run]
          intro fL fR hf
          simp [-bind_pure_comp, _root_.CryptoGames.SM.Construction.AuthL11.lImpl,
            lazySlotImplLoc, _root_.CryptoVerification.E2E.Signed.SessionRouter.sessLift_inl,
            map_eq_bind_pure_comp]
          exact evalDist_bind_congr _ _ _ fun u =>
            hf (u, { g := g, h := hLoc, abort := abort })
               ((u, { g := g, h := st, abort := abort }), tbl)
               ⟨rfl, rfl, rfl, hsync⟩
        · change EqDistRelLoc EMRelPaper
            (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
              ((transmitE hkL (2 + Δcka) qep mo.policy (P, m, rc)).run { g := g, h := hLoc, abort := abort }))
            ((simulateQ (lazySlotImplLoc K)
              ((transmitE hkR (2 + Δcka) qep mo.policy (P, m, rc)).run { g := g, h := st, abort := abort })).run tbl)
          dsimp only [transmitE]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split
          · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
          · split
            · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
            · split
              · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
                  StateT.run_pure, pure_bind, simulateQ_pure]
                exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
              · simp only [StateT.run_bind, simulateQ_bind]
                refine (eqDist_liftH_paper rfl rfl
                  (eqDist_vSend_loc cka prng fs mo M_sess _ P _ m none rc hsync)).bind
                  fun ⟨resL, esL1⟩ ⟨⟨resR, esR1⟩, tbl1⟩ ⟨hres, hg1, hab1, hsync1⟩ => ?_
                subst hres
                rcases resL with _ | ⟨stP', ct⟩ <;>
                  simp [_root_.CryptoGames.SM.Engine.abortE, hg1, hab1] <;>
                  exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync1⟩
        · change EqDistRelLoc EMRelPaper
            (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
              ((challE hkL (2 + Δcka) qep mo.cfg mo.policy qryCh).run { g := g, h := hLoc, abort := abort }))
            ((simulateQ (lazySlotImplLoc K)
              ((challE hkR (2 + Δcka) qep mo.cfg mo.policy qryCh).run { g := g, h := st, abort := abort })).run tbl)
          rw [challE_auth_run, challE_auth_run]
          simp only [simulateQ_pure, StateT.run_pure]
          exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
        · change EqDistRelLoc EMRelPaper
            (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
              ((deliverE hkL fs.maxSkip mo.cfg (P, c)).run { g := g, h := hLoc, abort := abort }))
            ((simulateQ (lazySlotImplLoc K)
              ((deliverE hkR fs.maxSkip mo.cfg (P, c)).run { g := g, h := st, abort := abort })).run tbl)
          dsimp only [deliverE]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split
          · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
          · split
            · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
            · simp only [StateT.run_bind, simulateQ_bind]
              refine (eqDist_liftH_paper rfl rfl
                (eqDist_vRecv_loc cka prng fs mo M_sess _ P _ c _ hsync)).bind
                fun ⟨resL, esL1⟩ ⟨⟨resR, esR1⟩, tbl1⟩ ⟨hres, hg1, hab1, hsync1⟩ => ?_
              subst hres
              rcases resL with _ | (_ | ⟨st', t', i', m'⟩)
              · simp [_root_.CryptoGames.SM.Engine.abortE, hg1]
                exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync1⟩
              · dsimp only
                split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  pure_bind, simulateQ_pure] <;>
                  exact EqDistRelLoc.pure ⟨rfl, by simp [hg1], hab1, hsync1⟩
              · dsimp only
                simp only [StateT.run_bind, commitE_pure_run_ob hkL (fun _ _ _ _ => rfl),
                  commitE_pure_run_ob hkR (fun _ _ _ _ => rfl),
                  pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
                exact EqDistRelLoc.pure ⟨rfl, rfl, hab1, hsync1⟩
        · change EqDistRelLoc EMRelPaper
            (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
              ((injectE hkL (2 + Δcka) qep mo.cfg (P, c)).run { g := g, h := hLoc, abort := abort }))
            ((simulateQ (lazySlotImplLoc K)
              ((injectE hkR (2 + Δcka) qep mo.cfg (P, c)).run { g := g, h := st, abort := abort })).run tbl)
          dsimp only [injectE]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split
          · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
          · simp only [StateT.run_bind, simulateQ_bind]
            refine (eqDist_liftH_paper rfl rfl
              (eqDist_vRecv_loc cka prng fs mo M_sess _ P _ c none hsync)).bind
              fun ⟨resL, esL1⟩ ⟨⟨resR, esR1⟩, tbl1⟩ ⟨hres, hg1, hab1, hsync1⟩ => ?_
            subst hres
            rcases resL with _ | (_ | ⟨st', t', i', m'⟩)
            · simp [_root_.CryptoGames.SM.Engine.abortE, hg1]
              exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync1⟩
            · simp only [StateT.run_pure, simulateQ_pure]
              exact EqDistRelLoc.pure ⟨rfl, hg1, hab1, hsync1⟩
            · dsimp only
              split
              · simp only [StateT.run_pure, simulateQ_pure]
                exact EqDistRelLoc.pure ⟨rfl, hg1, hab1, hsync1⟩
              · split
                · simp only [StateT.run_bind, commitE_pure_run_ob hkL (fun _ _ _ _ => rfl),
                    commitE_pure_run_ob hkR (fun _ _ _ _ => rfl),
                    pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
                  exact EqDistRelLoc.pure ⟨rfl, rfl, hab1, hsync1⟩
                · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
                    pure_bind, simulateQ_pure] <;>
                    exact EqDistRelLoc.pure ⟨rfl, by simp [hg1], hab1, hsync1⟩
        · change EqDistRelLoc EMRelPaper
            (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
              ((corrEPaper hkL mo.policy P).run { g := g, h := hLoc, abort := abort }))
            ((simulateQ (lazySlotImplLoc K)
              ((corrEPaper hkR mo.policy P).run { g := g, h := st, abort := abort })).run tbl)
          dsimp only [corrEPaper]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split
          · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
          · split
            · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE, StateT.run_modify,
                StateT.run_pure, pure_bind, simulateQ_pure]
              exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
            · simp [hkL, hkR, _root_.CryptoGames.SM.Construction.AuthL11.hooksLocal,
                hooksSlotLocal]
              exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
        · change EqDistRelLoc EMRelPaper
            (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
              ((deliverForgeE hkL (2 + Δcka) qep mo.cfg (P, c, c')).run { g := g, h := hLoc, abort := abort }))
            ((simulateQ (lazySlotImplLoc K)
              ((deliverForgeE hkR (2 + Δcka) qep mo.cfg (P, c, c')).run { g := g, h := st, abort := abort })).run tbl)
          dsimp only [deliverForgeE]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split
          · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
          · split
            · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
            · split
              · simp only [StateT.run_pure, simulateQ_pure]; exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync⟩
              · simp only [StateT.run_bind, simulateQ_bind]
                refine (eqDist_liftH_paper rfl rfl
                  (eqDist_vRecv_loc cka prng fs mo M_sess _ P _ c' none hsync)).bind
                  fun ⟨resL, esL1⟩ ⟨⟨resR, esR1⟩, tbl1⟩ ⟨hres, hg1, hab1, hsync1⟩ => ?_
                subst hres
                rcases resL with _ | (_ | ⟨st', t', i', m'⟩)
                · simp [_root_.CryptoGames.SM.Engine.abortE, hg1]
                  exact EqDistRelLoc.pure ⟨rfl, rfl, rfl, hsync1⟩
                · simp only [StateT.run_pure, simulateQ_pure]
                  exact EqDistRelLoc.pure ⟨rfl, hg1, hab1, hsync1⟩
                · dsimp only
                  split
                  · simp only [StateT.run_pure, simulateQ_pure]
                    exact EqDistRelLoc.pure ⟨rfl, hg1, hab1, hsync1⟩
                  · split
                    · simp only [StateT.run_bind, commitE_pure_run_ob hkL (fun _ _ _ _ => rfl),
                        commitE_pure_run_ob hkR (fun _ _ _ _ => rfl),
                        pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
                      exact EqDistRelLoc.pure ⟨rfl, rfl, hab1, hsync1⟩
                    · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
                        pure_bind, simulateQ_pure] <;>
                        exact EqDistRelLoc.pure ⟨rfl, by simp [hg1], hab1, hsync1⟩
      · intro ⟨uL, esL'⟩ ⟨⟨uR, esR'⟩, tbl'⟩ ⟨hu, hg', habort', hsync'⟩
        subst hu
        cases esL'; cases esR'; dsimp only at hg' habort' hsync'
        subst hg'; subst habort'
        exact ih uL _ _ tbl' _ _ hsync'
  dsimp only [_root_.CryptoGames.SM.Construction.AuthL11.localAuthDFPaper,
    _root_.CryptoGames.SM.Construction.AuthL11.runLocDFPaper, localAuthDFPaperSlot]
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
    exact hsim A { st := fun P => match P with | .A => vA | .B => vB, b := false }
      false tbl0 st0 hLoc0 hsync0 _ _ fun ⟨_, esL⟩ ⟨⟨_, esR⟩, _⟩ ⟨_, hg, habort, _⟩ => by
        simp [authOut, hg, habort]

private theorem localAuthDFPaper_eq_eager_ks {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (k0 : K) (Δcka qep M_sess : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[_root_.CryptoGames.SM.Construction.AuthL11.localAuthDFPaper cka prng fs lam Δcka qep tL t A] =
      𝒟[Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sampleVec
          ($ᵗ K : ProbComp K) k0 M_sess >>= fun ks =>
          simulateQ (keySlotFixedImpl ks)
            (localAuthDFPaperSlot cka prng fs lam Δcka qep M_sess tL t A)] := by
  rw [localAuthDFPaperSlot_lazy_eq cka prng fs lam Δcka qep M_sess tL t A,
    Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.keySlot_lazy_eq_eager k0 M_sess
      (localAuthDFPaperSlot cka prng fs lam Δcka qep M_sess tL t A)
      (localAuthDFPaperSlot_offRange cka prng fs lam Δcka qep M_sess tL t A)]
  refine evalDist_bind_congr _ _ _ fun ks => ?_
  rw [simulateQ_sessLift_keySlotImpl_fst_loc]

private theorem epMgmt_st_loc {VPt Msg C : Type} {Δ qep : ℕ}
    {g s₁ : GameState VPt Msg C} {P : Party} {bad : Bool}
    (h : g.epMgmt Δ qep P bad = some s₁) : s₁.st = g.st := by
  unfold GameState.epMgmt GameState.leak at h
  split_ifs at h <;> cases h <;> rfl

private theorem record_st_loc {VPt Msg C : Type} (g : GameState VPt Msg C)
    (Δ : ℕ) (P : Party) (st' : VPt) (r : Record Msg C) (isChall : Bool) :
    (g.record Δ P st' r isChall).st = Function.update g.st P st' := by
  unfold GameState.record
  split_ifs <;> rfl

private theorem accept_st_loc {VPt Msg C : Type} (g : GameState VPt Msg C)
    (P : Party) (new : VPt) (pos : _root_.CryptoGames.SM.Pos) :
    Function.update (g.accept P new pos).st P new = Function.update g.st P new := by
  simp [GameState.accept, GameState.delete, Function.update_idem]

private theorem afterCorr_st_loc {VPt Msg C : Type} (g : GameState VPt Msg C) (P : Party) :
    (g.afterCorr P).st = g.st := by
  rfl

private theorem allSessLt_sampleT_loc {M_sess : ℕ} {SS RS T M E α : Type} [SampleableType α] :
    Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt
      (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      (sampleT (tspec := _root_.CryptoGames.SM.Construction.FSMultiSpec SS RS T M E) α) :=
  Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt.liftProbComp ($ᵗ α : ProbComp α)

private theorem liftH_fsm_spec_loc {Γ T RSt SS RS K I M E α : Type} {M_sess : ℕ}
    (x : HM (_root_.CryptoGames.SM.Construction.FSMultiSpec SS RS T M E)
      (FSMultiState T RSt K I E) α)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hx : Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess (x.run es.h)) :
    Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
      ((_root_.CryptoGames.SM.Engine.liftH x).run es) ∧
    ∀ u ∈ support ((_root_.CryptoGames.SM.Engine.liftH x).run es),
      ∃ z ∈ support (x.run es.h), u = (z.1, { es with h := z.2 }) := by
  dsimp only [_root_.CryptoGames.SM.Engine.liftH, StateT.run]
  refine ⟨hx.bind_support fun _ _ => .pure _, fun u hu => ?_⟩
  rw [mem_support_bind_iff] at hu
  obtain ⟨z, hz, hu⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff] at hu
  exact ⟨z, hz, hu⟩

private theorem multiSessIdxInv_mono_rem_loc {Γ T RSt SS RS K I M E : Type}
    {M_sess rem₁ rem₂ : ℕ} (hrem : rem₁ ≤ rem₂)
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (h : Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem₂ es) :
    Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem₁ es :=
  { h with len_le := Nat.le_trans (Nat.add_le_add_left hrem _) h.len_le }

private theorem multiSessIdxInv_of_st_eq_loc {Γ T RSt SS RS K I M E : Type}
    {M_sess rem : ℕ}
    {es es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (h : Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess (rem + 1) es)
    (hst : es'.g.st = es.g.st)
    (hlen_lo : es.h.sessions.length ≤ es'.h.sessions.length)
    (hlen_hi : es'.h.sessions.length ≤ es.h.sessions.length + 1)
    (hcache : ∀ ep Tc σc k sIdx,
      es'.h.cache ep = some (Tc, σc, k, some sIdx) → sIdx < es'.h.sessions.length) :
    Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem es' where
  vS_lt Q sIdx hQ := lt_of_lt_of_le (h.vS_lt Q sIdx (by rwa [hst] at hQ)) hlen_lo
  vR_lt Q ep sIdx hQ := lt_of_lt_of_le (h.vR_lt Q ep sIdx (by rwa [hst] at hQ)) hlen_lo
  cache_lt := hcache
  len_le := by have := h.len_le; omega

private theorem multiSessIdxInv_of_update_st_loc {Γ T RSt SS RS K I M E : Type}
    {M_sess rem : ℕ}
    {es es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (h : Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess (rem + 1) es)
    (P : Party) (st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hst : es'.g.st = Function.update es.g.st P st')
    (hlen_lo : es.h.sessions.length ≤ es'.h.sessions.length)
    (hlen_hi : es'.h.sessions.length ≤ es.h.sessions.length + 1)
    (hcache : ∀ ep Tc σc k sIdx,
      es'.h.cache ep = some (Tc, σc, k, some sIdx) → sIdx < es'.h.sessions.length)
    (hvS : ∀ sIdx, st'.vS = some (.inr sIdx) → sIdx < es'.h.sessions.length)
    (hvR : ∀ ep sIdx, st'.vR ep = some (.inr sIdx) → sIdx < es'.h.sessions.length) :
    Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem es' where
  vS_lt Q sIdx hQ := by
    rw [hst] at hQ
    by_cases hQP : Q = P
    · subst hQP; rw [Function.update_self] at hQ; exact hvS sIdx hQ
    · rw [Function.update_of_ne hQP] at hQ; exact lt_of_lt_of_le (h.vS_lt Q sIdx hQ) hlen_lo
  vR_lt Q ep sIdx hQ := by
    rw [hst] at hQ
    by_cases hQP : Q = P
    · subst hQP; rw [Function.update_self] at hQ; exact hvR ep sIdx hQ
    · rw [Function.update_of_ne hQP] at hQ; exact lt_of_lt_of_le (h.vR_lt Q ep sIdx hQ) hlen_lo
  cache_lt := hcache
  len_le := by have := h.len_le; omega

private theorem initFSMultiRaw_spec_loc {KC KR Γ T RSt SS RS M E CCoins K I : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool) {q M_sess : ℕ} (hqM : q + 1 ≤ M_sess) :
    Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
      (initFSMultiRaw cka prng fs lam mo b) ∧
    ∀ es₀ ∈ support (initFSMultiRaw cka prng fs lam mo b),
      Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess q es₀ := by
  unfold initFSMultiRaw
  refine ⟨?_, fun es₀ hes₀ => ?_⟩
  · refine (allSessLt_sampleT_loc (α := KR)).bind_support fun kr _ => ?_
    refine (allSessLt_sampleT_loc (α := KC)).bind_support fun kc _ => ?_
    refine (Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.rootFSMulti_spec
      (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (M_sess := M_sess)
      prng mo 0 lam (prng.init kr) {}).1.bind_support fun ⟨⟨_, _, sid⟩, h₁⟩ _ => ?_
    refine (Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.regSessOptMulti_spec
      (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (M_sess := M_sess)
      sid h₁).1.bind_support fun _ _ => .pure _
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hes₀
    obtain ⟨kr, _, kc, _, ⟨⟨σ, k, sid⟩, h₁⟩, hh₁, ⟨optIdx, h₂⟩, hh₂, rfl⟩ := hes₀
    obtain ⟨hh₁_sess, hh₁_cache, _, _⟩ :=
      (Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.rootFSMulti_spec
        (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (M_sess := M_sess)
        prng mo 0 lam (prng.init kr) {}).2 _ hh₁
    obtain ⟨hopt, _, hlen₂, hcache₂, _, _⟩ :=
      (Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.regSessOptMulti_spec
        (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (M_sess := M_sess)
        sid h₁).2 _ hh₂
    refine
      { vS_lt := fun P sIdx hs => ?_
        vR_lt := fun P ep sIdx hr => ?_
        cache_lt := fun ep Tc σc k' sIdx hc => ?_
        len_le := ?_ }
    · cases P <;> simp only [mkParties] at hs
      · nomatch hs
      · cases optIdx <;> simp at hs
        subst hs; exact hopt _ rfl
    · cases P <;> simp only [mkParties] at hr
      · split_ifs at hr
        cases optIdx <;> simp at hr
        subst hr; exact hopt _ rfl
      · nomatch hr
    · dsimp only at hc
      rw [hcache₂, hh₁_cache] at hc
      nomatch hc
    · dsimp only
      rw [hh₁_sess] at hlen₂
      simp only [List.length_nil] at hlen₂
      omega

private theorem step_inr_fsm_spec_loc {KC KR Γ T RSt SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep M_sess rem : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ)
    (qry : (specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hinv : Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess (rem + 1) es) :
    let mo : Mode := ⟨true, tL, t⟩
    let hk := hooksFSMulti cka prng fs Δcka mo false la
    let act := (implEDFPaper hk (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inr qry)).run es
    Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess act ∧
    ∀ u ∈ support act,
      Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem u.2 := by
  intro mo hk act
  have hlen1 : es.h.sessions.length + 1 ≤ M_sess := by have := hinv.len_le; omega
  rcases qry with ((((⟨P, m, rc⟩ | qryCh) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
        ((transmitE hk (2 + Δcka) qep mo.policy (P, m, rc)).run es) ∧
      ∀ u ∈ support ((transmitE hk (2 + Δcka) qep mo.policy (P, m, rc)).run es),
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem u.2
    dsimp only [transmitE]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hhalt : (es.abort || es.g.win) = true
    · simp only [hhalt, ↓reduceIte, StateT.run_pure]
      exact ⟨.pure _, fun u hu => by
        simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
        exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
    · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
      cases hep : es.g.epMgmt (2 + Δcka) qep P rc.isSome with
      | none =>
        simp only [StateT.run_pure]
        exact ⟨.pure _, fun u hu => by
          simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
          exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
      | some s₁ =>
        have hst₁ : s₁.st = es.g.st := epMgmt_st_loc hep
        by_cases hld : mo.policy.leakDoom es.g s₁ = true
        · simp only [hld, ↓reduceIte, StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
            StateT.run_modify, StateT.run_pure, pure_bind]
          exact ⟨.pure _, fun u hu => by
            simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
            exact multiSessIdxInv_of_st_eq_loc hinv rfl le_rfl (Nat.le_succ _) hinv.cache_lt⟩
        · simp only [hld, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          have hvs := Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.vSend_fsm_spec
            (M_sess := M_sess) cka prng fs Δcka mo la s₁ P (s₁.st P) m none rc es.h
            (fun sIdx hs => hinv.vS_lt P sIdx (hst₁ ▸ hs))
            (fun ep sIdx hr => hinv.vR_lt P ep sIdx (hst₁ ▸ hr))
            hinv.cache_lt hlen1
          obtain ⟨hlift_a, hlift_s⟩ := liftH_fsm_spec_loc _ es hvs.1
          refine ⟨hlift_a.bind_support fun w _ => by
            rcases w.1 with _ | ⟨_, _⟩ <;>
              simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
                StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact .pure _, fun u hu => ?_⟩
          rw [mem_support_bind_iff] at hu
          obtain ⟨w, hw, hu⟩ := hu
          obtain ⟨z, hz, rfl⟩ := hlift_s w hw
          obtain ⟨hl1, hl2, hca, hvp⟩ := hvs.2 z hz
          rcases hz1 : z.1 with _ | ⟨st', ct⟩
          · simp only [hz1, StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
              StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hu
            subst hu
            exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hca
          · simp only [hz1, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hu
            subst hu
            obtain ⟨hvS', hvR'⟩ := hvp st' ct hz1
            refine multiSessIdxInv_of_update_st_loc hinv P st' ?_ hl1 hl2 hca hvS' hvR'
            dsimp only
            rw [record_st_loc, hst₁]
  · change Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
        ((challE hk (2 + Δcka) qep mo.cfg mo.policy qryCh).run es) ∧
      ∀ u ∈ support ((challE hk (2 + Δcka) qep mo.cfg mo.policy qryCh).run es),
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem u.2
    rw [challE_auth_run]
    exact ⟨.pure _, fun u hu => by
      simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
      exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
  · change Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
        ((deliverE hk fs.maxSkip mo.cfg (P, c)).run es) ∧
      ∀ u ∈ support ((deliverE hk fs.maxSkip mo.cfg (P, c)).run es),
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem u.2
    dsimp only [deliverE]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hhalt : (es.abort || es.g.win) = true
    · simp only [hhalt, ↓reduceIte, StateT.run_pure]
      exact ⟨.pure _, fun u hu => by
        simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
        exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
    · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
      cases hit : es.g.inTransit P.other c with
      | none =>
        simp only [StateT.run_pure]
        exact ⟨.pure _, fun u hu => by
          simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
          exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
      | some r =>
        rw [StateT.run_bind]
        have hvr := Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.vRecv_fsm_spec
          (M_sess := M_sess) cka prng fs Δcka mo la es.g P (es.g.st P) c (some r) es.h
          (hinv.vS_lt P) (hinv.vR_lt P) hinv.cache_lt hlen1
        obtain ⟨hlift_a, hlift_s⟩ := liftH_fsm_spec_loc _ es hvr.1
        refine ⟨hlift_a.bind_support fun w _ => by
          rcases w.1 with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
              StateT.run_modify, StateT.run_pure, pure_bind]
            exact .pure _
          · dsimp only
            split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact .pure _
          · dsimp only
            rw [StateT.run_bind, commitE_pure_run_ob hk (fun _ _ _ _ => rfl)]
            simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure]
            exact .pure _,
          fun u hu => ?_⟩
        rw [mem_support_bind_iff] at hu
        obtain ⟨w, hw, hu⟩ := hu
        obtain ⟨z, hz, rfl⟩ := hlift_s w hw
        obtain ⟨hl1, hl2, hca, hvp⟩ := hvr.2 z hz
        have hcache' : ∀ ep Tc σc k sIdx,
            z.2.cache ep = some (Tc, σc, k, some sIdx) → sIdx < z.2.sessions.length :=
          fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx (hca ▸ hc)) hl1
        rcases hz1 : z.1 with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [hz1, StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
            StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hu
          subst hu
          exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
        · simp only [hz1] at hu
          split_ifs at hu <;>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hu <;>
            subst hu <;>
            exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
        · simp only [hz1] at hu
          rw [StateT.run_bind, commitE_pure_run_ob hk (fun _ _ _ _ => rfl)] at hu
          simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hu
          subst hu
          obtain ⟨hvS', hvR'⟩ := hvp st' t' i' m' hz1
          refine multiSessIdxInv_of_update_st_loc hinv P st' ?_ hl1 hl2 hcache' hvS' hvR'
          dsimp only
          split_ifs <;> exact accept_st_loc es.g P st' r.pos
  · change Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
        ((injectE hk (2 + Δcka) qep mo.cfg (P, c)).run es) ∧
      ∀ u ∈ support ((injectE hk (2 + Δcka) qep mo.cfg (P, c)).run es),
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem u.2
    dsimp only [injectE]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hskip : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
        !(es.g.safeInj (2 + Δcka))) = true
    · simp only [hskip, ↓reduceIte, StateT.run_pure]
      exact ⟨.pure _, fun u hu => by
        simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
        exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
    · simp only [hskip, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      have hvr := Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.vRecv_fsm_spec
        (M_sess := M_sess) cka prng fs Δcka mo la es.g P (es.g.st P) c none es.h
        (hinv.vS_lt P) (hinv.vR_lt P) hinv.cache_lt hlen1
      obtain ⟨hlift_a, hlift_s⟩ := liftH_fsm_spec_loc _ es hvr.1
      refine ⟨hlift_a.bind_support fun w _ => by
        rcases w.1 with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
            StateT.run_modify, StateT.run_pure, pure_bind]
          exact .pure _
        · exact .pure _
        · dsimp only
          split
          · exact .pure _
          · split
            · rw [StateT.run_bind, commitE_pure_run_ob hk (fun _ _ _ _ => rfl)]
              simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure]
              exact .pure _
            · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                exact .pure _,
        fun u hu => ?_⟩
      rw [mem_support_bind_iff] at hu
      obtain ⟨w, hw, hu⟩ := hu
      obtain ⟨z, hz, rfl⟩ := hlift_s w hw
      obtain ⟨hl1, hl2, hca, hvp⟩ := hvr.2 z hz
      have hcache' : ∀ ep Tc σc k sIdx,
          z.2.cache ep = some (Tc, σc, k, some sIdx) → sIdx < z.2.sessions.length :=
        fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx (hca ▸ hc)) hl1
      rcases hz1 : z.1 with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [hz1, StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
          StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hu
        subst hu
        exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
      · simp only [hz1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
        subst hu
        exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
      · simp only [hz1] at hu
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
          subst hu
          exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
        · simp only [hqep, ↓reduceIte] at hu
          by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
          · simp only [htriv, ↓reduceIte, StateT.run_bind,
              commitE_pure_run_ob hk (fun _ _ _ _ => rfl),
              pure_bind, StateT.run_modify, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hu
            subst hu
            obtain ⟨hvS', hvR'⟩ := hvp st' t' i' m' hz1
            exact multiSessIdxInv_of_update_st_loc hinv P st'
              (accept_st_loc es.g P st' ⟨P.other, t', i'⟩) hl1 hl2 hcache' hvS' hvR'
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hu
            split_ifs at hu <;>
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hu <;>
              subst hu <;>
              exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
  · change Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
        ((corrEPaper hk mo.policy P).run es) ∧
      ∀ u ∈ support ((corrEPaper hk mo.policy P).run es),
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem u.2
    dsimp only [corrEPaper]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hskip : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
    · simp only [hskip, ↓reduceIte, StateT.run_pure]
      exact ⟨.pure _, fun u hu => by
        simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
        exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
    · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
      by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) ||
          mo.policy.corrDoom es.g P) = true
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
          StateT.run_modify, StateT.run_pure, pure_bind]
        exact ⟨.pure _, fun u hu => by
          simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
          exact multiSessIdxInv_of_st_eq_loc hinv rfl le_rfl (Nat.le_succ _) hinv.cache_lt⟩
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        have hrev := Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.reveal_fsm_spec
          (SS := SS) (RS := RS) (M := M) (M_sess := M_sess)
          cka prng fs Δcka mo la es.g P (es.g.st P) es.h (hinv.vS_lt P)
          (Nat.le_of_succ_le hlen1)
        obtain ⟨hlift_a, hlift_s⟩ := liftH_fsm_spec_loc _ es hrev.1
        refine ⟨hlift_a.bind_support fun w _ => by
          rcases w.1 with _ | _ <;>
            simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
              StateT.run_modify, StateT.run_pure, pure_bind] <;>
            exact .pure _,
          fun u hu => ?_⟩
        rw [mem_support_bind_iff] at hu
        obtain ⟨w, hw, hu⟩ := hu
        obtain ⟨z, hz, rfl⟩ := hlift_s w hw
        obtain ⟨hsess_eq, hcache_eq⟩ := hrev.2 z hz
        have hl1 : es.h.sessions.length ≤ z.2.sessions.length := by rw [hsess_eq]
        have hl2 : z.2.sessions.length ≤ es.h.sessions.length + 1 := by
          rw [hsess_eq]; exact Nat.le_succ _
        have hcache' : ∀ ep Tc σc k sIdx,
            z.2.cache ep = some (Tc, σc, k, some sIdx) → sIdx < z.2.sessions.length :=
          fun ep Tc σc k sIdx hc => by
            rw [hsess_eq]; exact hinv.cache_lt ep Tc σc k sIdx (hcache_eq ▸ hc)
        rcases hz1 : z.1 with _ | st_rev
        · simp only [hz1, StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
            StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hu
          subst hu
          exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
        · simp only [hz1, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hu
          subst hu
          exact multiSessIdxInv_of_st_eq_loc hinv (afterCorr_st_loc es.g P) hl1 hl2 hcache'
  · change Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
        ((deliverForgeE hk (2 + Δcka) qep mo.cfg (P, c, c')).run es) ∧
      ∀ u ∈ support ((deliverForgeE hk (2 + Δcka) qep mo.cfg (P, c, c')).run es),
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem u.2
    dsimp only [deliverForgeE]
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hhalt : (es.abort || es.g.win) = true
    · simp only [hhalt, ↓reduceIte, StateT.run_pure]
      exact ⟨.pure _, fun u hu => by
        simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
        exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
    · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
      cases hit : es.g.inTransit P.other c with
      | none =>
        simp only [StateT.run_pure]
        exact ⟨.pure _, fun u hu => by
          simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
          exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
      | some r =>
        by_cases hbad : ((es.g.inTransit P.other c').isSome ||
            es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [hbad, ↓reduceIte, StateT.run_pure]
          exact ⟨.pure _, fun u hu => by
            simp only [support_pure, Set.mem_singleton_iff] at hu; subst hu
            exact multiSessIdxInv_mono_rem_loc (Nat.le_succ rem) hinv⟩
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          have hvr := Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.vRecv_fsm_spec
            (M_sess := M_sess) cka prng fs Δcka mo la es.g P (es.g.st P) c' none es.h
            (hinv.vS_lt P) (hinv.vR_lt P) hinv.cache_lt hlen1
          obtain ⟨hlift_a, hlift_s⟩ := liftH_fsm_spec_loc _ es hvr.1
          refine ⟨hlift_a.bind_support fun w _ => by
            rcases w.1 with _ | (_ | ⟨st', t', i', m'⟩)
            · simp only [StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
                StateT.run_modify, StateT.run_pure, pure_bind]
              exact .pure _
            · exact .pure _
            · dsimp only
              split
              · exact .pure _
              · split
                · rw [StateT.run_bind, commitE_pure_run_ob hk (fun _ _ _ _ => rfl)]
                  simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure]
                  exact .pure _
                · split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                    exact .pure _,
            fun u hu => ?_⟩
          rw [mem_support_bind_iff] at hu
          obtain ⟨w, hw, hu⟩ := hu
          obtain ⟨z, hz, rfl⟩ := hlift_s w hw
          obtain ⟨hl1, hl2, hca, hvp⟩ := hvr.2 z hz
          have hcache' : ∀ ep Tc σc k sIdx,
              z.2.cache ep = some (Tc, σc, k, some sIdx) → sIdx < z.2.sessions.length :=
            fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx (hca ▸ hc)) hl1
          rcases hz1 : z.1 with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [hz1, StateT.run_bind, _root_.CryptoGames.SM.Engine.abortE,
              StateT.run_modify, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hu
            subst hu
            exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
          · simp only [hz1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
            subst hu
            exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
          · simp only [hz1] at hu
            by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
              subst hu
              exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hu
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
              · simp only [htriv, ↓reduceIte, StateT.run_bind,
                  commitE_pure_run_ob hk (fun _ _ _ _ => rfl),
                  pure_bind, StateT.run_modify, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff] at hu
                subst hu
                obtain ⟨hvS', hvR'⟩ := hvp st' t' i' m' hz1
                exact multiSessIdxInv_of_update_st_loc hinv P st'
                  (accept_st_loc es.g P st' ⟨P.other, t', i'⟩) hl1 hl2 hcache' hvS' hvR'
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hu
                split_ifs at hu <;>
                  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
                    pure_bind, support_pure, Set.mem_singleton_iff] at hu <;>
                  subst hu <;>
                  exact multiSessIdxInv_of_st_eq_loc hinv rfl hl1 hl2 hcache'

private theorem redFSAuthDFPaperMulti_offRange_gen {KC KR Γ T RSt SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (q M_sess : ℕ) (hqM : q + 1 ≤ M_sess)
    (Δcka qep : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFPaperMulti cka prng fs lam Δcka qep la tL t A).IsQueryBoundP
      (fun u => CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess u = true) 0 := by
  apply Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt.to_isQueryBoundP
  dsimp only [redFSAuthDFPaperMulti, runFSMultiDFPaper]
  let mo : Mode := ⟨true, tL, t⟩
  let hk := hooksFSMulti cka prng fs Δcka mo false la
  have hsim : ∀ (oa : SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (rem : ℕ),
      MakesAtMostQueriesDF oa rem →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)),
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.MultiSessIdxInv M_sess rem es →
        Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.AllSessLt M_sess
          ((simulateQ (implEDFPaper hk (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro rem _ es _
      simp only [simulateQ_pure, StateT.run_pure]
      exact .pure (a, es)
    | query_bind qry k ih =>
      intro rem hqb es hinv
      unfold MakesAtMostQueriesDF at hqb
      rw [isQueryBoundP_query_bind_iff] at hqb
      rw [simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
      rw [StateT.run_bind]
      rcases qry with n | q_df
      · rw [implEDFPaper_inl_run, bind_assoc]
        refine .coin n _ fun u => ?_
        rw [pure_bind]
        exact ih u rem (by simpa [MakesAtMostQueriesDF] using hqb.2 u) es hinv
      · cases rem with
        | zero => simp at hqb
        | succ rem' =>
          have hstep := step_inr_fsm_spec_loc cka prng fs Δcka qep M_sess rem' la tL t q_df es hinv
          exact hstep.1.bind_support fun u hu =>
            ih u.1 rem' (by simpa [MakesAtMostQueriesDF] using hqb.2 u.1) u.2 (hstep.2 u hu)
  obtain ⟨hinit_a, hinit_s⟩ := initFSMultiRaw_spec_loc cka prng fs lam mo false hqM
  rw [bind_assoc]
  exact hinit_a.bind_support fun es₀ hes₀ =>
    (hsim A q hq es₀ (hinit_s es₀ hes₀)).bind_support fun _ _ => .pure _

private theorem redFSAuthDFPaperMulti_offRange
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka qep : ℕ) (la : Bool) (tL : Option ℕ) (t : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFPaperMulti (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A).IsQueryBoundP
      (fun u => CryptoVerification.E2E.Signed.SessionRouter.sessOffRange (2 * q + 2) u = true) 0 :=
  redFSAuthDFPaperMulti_offRange_gen (dhScheme Dh) (rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q (2 * q + 2) (by omega)
    Δcka qep la tL t A hq

/-- Sub-lemma 1: Eager `2 * q + 2` key-slot equivalence (`localAuthDFPaper` ↔ `localAuthDFPaperSlot`),
`pubFsMultiImpl` fusion, and `AllSessLt (2 * q + 2)` router off-range bound into `multiSessRealWinProb`. -/
private theorem outer_slot_and_multiSessReal_bridge
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hPerKey : ∀ (ks : ℕ → BitVec 256) (bs : ℕ → Bool),
      LeAdd
        (simulateQ (keySlotFixedImpl ks)
          (localAuthDFPaperSlot (dhScheme Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep (2 * q + 2) tL t A))
        (Prod.fst <$> (simulateQ (pubFsMultiImpl (paperFsImpl C ℓ encT idOf false))
            (redFSAuthDFPaperMulti (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep false tL t A)).run
          (fun _ => false, fun i => hInit (bs i) (.seed (ks i))))
        (Prod.fst <$> (simulateQ (pubFsMultiImpl (paperFsImpl C ℓ encT idOf true))
            (redFSAuthDFPaperMulti (dhScheme Dh) (rootPRNG C.F encPt)
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep true tL t A)).run
          (fun _ => false, fun i => hInit (bs i) (.seed (ks i))))) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A)
    𝒟[_root_.CryptoGames.SM.Construction.AuthL11.localAuthDFPaper (dhScheme Dh)
        (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL t A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  intro Adv
  have _ := And.intro hD (And.intro hinj (And.intro hdum (And.intro hℓ hsh)))
  let M_sess := 2 * q + 2
  let cka := dhScheme Dh
  let prng := rootPRNG C.F encPt
  let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  have hoff : ∀ la, (Adv la).IsQueryBoundP
      (fun u => CryptoVerification.E2E.Signed.SessionRouter.sessOffRange M_sess u = true) 0 :=
    fun la => Computational.Proofs.E2E.SessionAuthPubToAD.multiSessPubToAD_offRange
      protoSignalCodec _ M_sess
      (redFSAuthDFPaperMulti_offRange ℓ C Dh encPt encT idOf lam q Δcka qep la tL t A hq)
  rw [localAuthDFPaper_eq_eager_ks cka prng fs lam (0 : BitVec 256) Δcka qep M_sess tL t A]
  have hK : ∀ (ks : ℕ → BitVec 256) (bs : ℕ → Bool),
      LeAdd
        (simulateQ (keySlotFixedImpl ks)
          (localAuthDFPaperSlot cka prng fs lam Δcka qep M_sess tL t A))
        (Prod.fst <$> (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.sessLift
            (paperFsImpl C ℓ encT idOf false)) (Adv false)).run
          (fun i => hInit (bs i) (.seed (ks i))))
        (Prod.fst <$> (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.sessLift
            (paperFsImpl C ℓ encT idOf true)) (Adv true)).run
          (fun i => hInit (bs i) (.seed (ks i)))) := by
    intro ks bs
    dsimp only [Adv]
    rw [Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl,
      Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl]
    exact hPerKey ks bs
  have hStep : LeAdd
      (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sampleVec
          ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) (0 : BitVec 256) M_sess >>= fun ks =>
        simulateQ (keySlotFixedImpl ks)
          (localAuthDFPaperSlot cka prng fs lam Δcka qep M_sess tL t A))
      (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sampleVec
          ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) (0 : BitVec 256) M_sess >>= fun ks =>
        Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sampleVec
            ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
          Prod.fst <$> (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.sessLift
              (paperFsImpl C ℓ encT idOf false)) (Adv false)).run
            (fun i => hInit (bs i) (.seed (ks i))))
      (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sampleVec
          ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) (0 : BitVec 256) M_sess >>= fun ks =>
        Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.sampleVec
            ($ᵗ Bool : ProbComp Bool) false M_sess >>= fun bs =>
          Prod.fst <$> (simulateQ (CryptoVerification.E2E.Signed.SessionRouter.sessLift
              (paperFsImpl C ℓ encT idOf true)) (Adv true)).run
            (fun i => hInit (bs i) (.seed (ks i)))) :=
    leAdd_bind _ fun ks _ => leAdd_bind_dummy_loc _ fun bs _ => hK ks bs
  exact hStep.trans (add_le_add
    (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.multiFsEager_le_real
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps M_sess (0 : BitVec 256) false (Adv false) (hoff false))
    (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow.multiFsEager_le_real
      (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps M_sess (0 : BitVec 256) true (Adv true) (hoff true)))

end

end Computational.Proofs.E2E.SessionAuthMultiRealPaper

namespace Computational.Proofs.E2E.SessionAuthMultiReal

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (authLosingConditionsAvoided lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Construction (Header
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF bucketAuthCfg engRunDFPaperBucket
  hooksLocalBucket initLocalBucket)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift multiSessSpec)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb)

section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)


/-- Unshifted single-epoch (`AuthL11.localAuthDFPaper`) post-PRNG local game bounded by the two-mode
(`la = false` + `la = true`) `multiSessRealWinProb` of `redFSAuthDFPaperMulti`. -/
theorem localAuthDFPaper_le_multiSessRealWinProb
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A)
    𝒟[_root_.CryptoGames.SM.Construction.AuthL11.localAuthDFPaper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL t A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  intro Adv
  cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t with
  | false =>
    rw [Computational.Proofs.E2E.SessionAuthMultiRealPaperAux.localAuthDFPaper_eq_zero_of_not_validGuess
      (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL t hvg A]
    exact zero_le
  | true =>
    exact Computational.Proofs.E2E.SessionAuthMultiRealPaper.outer_slot_and_multiSessReal_bridge
      ℓ C Dh hD encPt encT hinj hdum idOf lam hℓ q Δcka qep tL t A hq hsh fun ks bs =>
        Computational.Proofs.E2E.SessionAuthMultiRealPaper.localAuthDFPaper_perKey_coupling
          ℓ C Dh hD encPt encT idOf lam hℓ q (2 * q + 2) Δcka qep (by omega) tL t hvg A hq hsh ks bs


end LibsignalBridges

end

end Computational.Proofs.E2E.SessionAuthMultiReal

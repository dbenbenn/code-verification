/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS
import Computational.Proofs.E2E.SessionAuthMultiRealBase
import Computational.Proofs.E2E.SessionAuthMultiRealPaperAux
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
import Computational.Proofs.ReductionDsl.SM.RedFS
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.E2E.SessionAuthMultiEndBase
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect

import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.SM.Theorem1.Queries
/-!
# Sub-lemmas for `SessionAuthMultiRealShiftedDir1`

Splits `localAuthDFShiftedPaper_le_multiSessRealWinProb` into four independent sub-lemmas:
1. `evalDist_localAuthDFShiftedPaper_eq_zero_of_qep_lt`: short-horizon (`qep + 1 < t`) zero bound.
2. `localAuthDFShiftedPaper_le_sampleVec`: lazy-to-eager session-key prefix hybrid.
3. `redFSAuthDFShiftedPaperMulti_offRange`: multi-session `sessOffRange q` query-bound `0`.
4. `localAuthPrefix_dir1_leAdd_pubFs`: per-`(ks, bs)` eager-keyed `LeAdd` simulation coupling.
-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthMultiRealShiftedDir1Split

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.FSAEAD.Thm5 (hp hInit)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM.Engine (EState Ctx Hooks authOut)
open _root_.CryptoGames.SM.Construction (Header Mode sampleT realParty)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF implEDFShiftedPaper localAuthDFShiftedPaper)
open _root_.CryptoGames.SM.Construction.AuthL11 (nilSpec lImpl LState regSess regSessOf initLocal)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lFS lIdeal lAeadR
  lChainPRG)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsImpl)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_offRange)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow
  (LeAdd sampleVec leAdd_bind leAdd_bind_dummy_loc multiFsEager_le_real
   pubFsMultiImpl simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt (SessHSt)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (redFSAuthDFShiftedPaperMulti)

/-! ### Prefix-Keyed Local `H2` Game Definitions -/

private def lookupFLPrefix {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (r : ℕ) (ks : ℕ → K) (Ik : I) :
    StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) K := do
  let s ← get
  match s.table.lookup Ik with
  | some k => return k
  | none =>
    let k_draw ← StateT.lift (sampleT K)
    let k := if s.sessions.length < r then ks s.sessions.length else k_draw
    modify fun s => { s with table := (Ik, k) :: s.table }
    return k

private def rootLPrefix {KR Sig I K T : Type} [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (mo : Mode) (r : ℕ) (ks : ℕ → K)
    (t : ℕ) (Ik : I) (σ : Sig) :
    StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (Sig × K × Option I) := do
  if mo.tStar < t then
    let p := prng.up σ Ik
    return (p.1, p.2, none)
  else if t = mo.tStar then
    if mo.tL.isSome && t = mo.tH then
      let Ir ← StateT.lift (sampleT I)
      let k_draw ← StateT.lift (sampleT K)
      let s ← get
      let k := if Ir ∈ s.sessions then k_draw
        else if s.sessions.length < r then ks s.sessions.length else k_draw
      return ((prng.up σ Ir).1, k, some Ir)
    else
      let k ← lookupFLPrefix r ks Ik
      return ((prng.up σ Ik).1, k, some Ik)
  else if mo.tL.isSome && t = mo.tH then
    let Ir ← StateT.lift (sampleT I)
    let p := prng.up σ Ir
    return (p.1, p.2, none)
  else
    let p := prng.up σ Ik
    return (p.1, p.2, none)

private def hooksLocalPrefix {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (r : ℕ) (ks : ℕ → K) :
    Hooks nilSpec (LState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig
      (SS × Option ℕ) (RS × Option ℕ) where
  startSend _ _ t γ σ rOpt := do
    let coins ← match rOpt with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ coins
    let (σ', k, sid) ← rootLPrefix prng mo r ks t c.2.2 σ
    let idx? ← regSessOf sid
    modify fun s => { s with cache := Function.update s.cache t (some (c.2.1, σ', k, idx?)) }
    return some (c.1, c.2.1, σ', (fs.initSender k, idx?))
  startRecv _ _ t γ σ Tn := do
    let honest := match (← get).cache t with
      | some (Tc, σc, k, idx?) => if Tc = Tn then some (σc, k, idx?) else none
      | none => none
    match honest with
    | some (σc, k, idx?) =>
      return some (some ((cka.receive γ Tn).1, σc, (fs.initReceiver k, idx?)))
    | none =>
      if mo.auth && t = mo.tStar then
        if mo.tL.isSome && mo.tStar = mo.tH then return none
        let kk := cka.receive γ Tn
        let k' ← lookupFLPrefix r ks kk.2
        let idx ← regSess kk.2
        return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
      else return some none
  fsSend _ _ _ ssv h m _ := do
    let o := fs.send ssv.1 h m
    return some ((o.1, ssv.2), o.2)
  fsRecv _ _ _ rsv h e _ := do
    match fs.receive rsv.1 h e with
    | none => return some none
    | some (rs', i, m) =>
      modify fun s => { s with lastIdx := rsv.2 }
      return some (some ((rs', rsv.2), i, m))
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    return some (realParty vp vp.γ vp.root (vp.vS.map Prod.fst) (fun t => (vp.vR t).map Prod.fst))

private def localAuthPrefix {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l : ℕ)
    (tL : Option ℕ) (t r : ℕ) (ks : ℕ → K)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let z ← simulateQ lImpl
      ((simulateQ (implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks) (2 + Δcka) qep
        fs.maxSkip mo.cfg mo.policy) A).run { g, h })
    return authOut (2 + Δcka) mo.policy z.2

private theorem le_multiSessRealWinProb_of_perKey {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Adv : Bool → Computational.Proofs.E2E.SessionAuthBridge.MultiSessFsAdv Pt ℓ)
    (LOCAL : ProbComp Bool) (LOCALks : (ℕ → BitVec 256) → ProbComp Bool)
    (M : ℕ) (k0 : BitVec 256)
    (hH1 : 𝒟[LOCAL] {true} ≤
      𝒟[sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= LOCALks] {true})
    (hH3 : ∀ la, (Adv la).IsQueryBoundP (fun t => sessOffRange M t = true) 0)
    (hK : ∀ (ks : ℕ → BitVec 256) (bs : ℕ → Bool), LeAdd (LOCALks ks)
      (Prod.fst <$> (simulateQ (sessLift (fsImpl
          (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
          maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
          (Adv false)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i))))
      (Prod.fst <$> (simulateQ (sessLift (fsImpl
          (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
          (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
          maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 true)))
          (Adv true)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i))))) :
    𝒟[LOCAL] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  refine hH1.trans ?_
  have hStep : LeAdd
      (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= LOCALks)
      (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= fun ks =>
        sampleVec ($ᵗ Bool : ProbComp Bool) false M >>= fun bs =>
          Prod.fst <$> (simulateQ (sessLift (fsImpl
            (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
            maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 false)))
            (Adv false)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i))))
      (sampleVec ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) k0 M >>= fun ks =>
        sampleVec ($ᵗ Bool : ProbComp Bool) false M >>= fun bs =>
          Prod.fst <$> (simulateQ (sessLift (fsImpl
            (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
            (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
            maxForwardJumps (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 true)))
            (Adv true)).run (fun i => _root_.CryptoGames.FSAEAD.Thm5.hInit (bs i) (.seed (ks i)))) :=
    leAdd_bind _ fun ks _ =>
      leAdd_bind_dummy_loc _ fun bs _ => hK ks bs
  exact hStep.trans (add_le_add
    (multiFsEager_le_real
      (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
      maxForwardJumps M k0 false (Adv false) (hH3 false))
    (multiFsEager_le_real
      (_root_.CryptoGames.Ratchet.LibsignalInst.lIdeal C protoSignalCodec ℓ encT)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lAeadR C protoSignalCodec ℓ encT idOf)
      (_root_.CryptoGames.Ratchet.LibsignalInst.lChainPRG C.F)
      maxForwardJumps M k0 true (Adv true) (hH3 true)))


namespace Sub123Helpers
set_option linter.unusedSectionVars false
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (Header
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF bucketAuthCfg engRunDFPaperBucket
  hooksLocalBucket initLocalBucket
  localAuthDFShiftedDir2Paper localAuthDFShiftedPaper)
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
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti)
open Computational.Proofs.E2E.SessionAuthMultiRealPaperAux (AllSessLt MultiSessIdxInv
  liftFSMulti_allSessLt lookupMultiF_allSessLt regSessMulti_spec regSessOptMulti_spec
  rootFSMulti_spec startSend_fsm_spec startRecv_fsm_spec fsSend_fsm_spec fsRecv_fsm_spec
  reveal_fsm_spec vSend_fsm_spec vRecv_fsm_spec)
private theorem liftH_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv T Sv SSv RSv M E α : Type}
    (x : StateT HS (_root_.CryptoGames.SM.Engine.TComp tspec) α)
    (es : _root_.CryptoGames.SM.Engine.EState
      (_root_.CryptoGames.SM.Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (_root_.CryptoGames.SM.Engine.liftH x).run es =
      (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := by
  dsimp only [_root_.CryptoGames.SM.Engine.liftH, StateT.run]

private theorem coinsE_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv T Sv SSv RSv M E : Type} (n : ℕ)
    (es : _root_.CryptoGames.SM.Engine.EState
      (_root_.CryptoGames.SM.Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (_root_.CryptoGames.SM.Engine.coinsE n).run es =
      ((liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl n)) :
        _root_.CryptoGames.SM.Engine.TComp tspec _) >>= fun b => pure (b, es)) := rfl

section ShiftedDir1IdxInv

open _root_.CryptoGames.SM (GameState Config healedBy lastLeakGuessAdmissible samIfNec)
open _root_.CryptoGames.SM.Engine (EState VP Policy Hooks vSend vRecv transmitE challE
  deliverE injectE commitE abortE coinsE authOut)
open _root_.CryptoGames.SM.Construction (FSMultiState FSMultiSpec Mode PartyState mkParties
  initFSMultiRaw hooksFSMulti rootFSMulti lookupMultiF regSessMulti regSessOptMulti liftFSMulti)
open _root_.CryptoGames.SM.Construction.DeliverForge (specDF deliverForgeE corrEShiftedPaper
  afterCorrShifted implEDFShiftedPaper implEDFShiftedPaperGen)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessOffRange)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  runFSMultiDFShiftedPaper redFSAuthDFShiftedPaperMultiGen)

private theorem admissible_shifted_guess {Δcka l t : ℕ}
    (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka)) :
    lastLeakGuessAdmissible (2 + Δcka) (some (l - 1)) t = true := by
  simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq]
  omega

private theorem initFSMultiRaw_allSessLt_and_inv
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q l t : ℕ) (ht0 : 0 < t) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    AllSessLt q (initFSMultiRaw (SS := SS) (RS := RS) (M := M) (E := E) cka prng fs lam mo false) ∧
    ∀ es₀ ∈ support (initFSMultiRaw (SS := SS) (RS := RS) (M := M) (E := E) cka prng fs lam mo false),
      MultiSessIdxInv q q es₀ := by
  intro mo
  have ht_ne : (0 : ℕ) ≠ mo.tStar := Nat.ne_of_lt ht0
  have htH_ne : (0 : ℕ) ≠ mo.tH := by
    simp [mo, Mode.tH, _root_.CryptoGames.SM.Construction.healEpoch]
  unfold initFSMultiRaw rootFSMulti regSessOptMulti
  simp only [Nat.not_lt_zero, ht_ne, htH_ne, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    StateT.run_pure, pure_bind]
  refine ⟨AllSessLt.bind_support (AllSessLt.liftProbComp ($ᵗ KR : ProbComp KR)) fun _ _ =>
    AllSessLt.bind_support (AllSessLt.liftProbComp ($ᵗ KC : ProbComp KC)) fun _ _ => .pure _, fun es₀ hes₀ => ?_⟩
  rw [mem_support_bind_iff] at hes₀; obtain ⟨kr, _, hes₀⟩ := hes₀
  rw [mem_support_bind_iff] at hes₀; obtain ⟨kc, _, hes₀⟩ := hes₀
  simp only [support_pure, Set.mem_singleton_iff] at hes₀; subst hes₀
  refine ⟨?_, ?_, ?_, by simp⟩
  · intro P sIdx h; cases P <;> simp [mkParties] at h
  · intro P ep sIdx h
    cases P <;> simp only [mkParties] at h
    · split at h <;> simp at h
    · simp at h
  · intro ep Tc σc k sIdx h; cases h

private theorem epMgmt_st_eq {St Msg C : Type} {s s₁ : GameState St Msg C} {Δ qep : ℕ}
    {P : Party} {fl : Bool} (h : s.epMgmt Δ qep P fl = some s₁) : s₁.st = s.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl

private theorem afterCorrShifted_st_eq {St Msg C : Type} (l : ℕ) (s : GameState St Msg C) (P : Party) :
    (afterCorrShifted l s P).st = s.st := by
  simp [afterCorrShifted, GameState.leak]

private theorem hooksFSMulti_commit {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (rcvA la : Bool) :
    (hooksFSMulti cka prng fs Δcka mo rcvA la).commit = fun _ _ _ new => pure (some new) := rfl

private theorem stepFSMulti_allSessLt_and_inv
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l t M_sess rem : ℕ) (la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hinv : MultiSessIdxInv M_sess rem es)
    (qry : (unifSpec + specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hrem : qry.isRight = true → 0 < rem) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let step := (implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false la)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run es
    AllSessLt M_sess step ∧
    ∀ z ∈ support step,
      MultiSessIdxInv M_sess (if qry.isRight then rem - 1 else rem) z.2 := by
  intro mo
  dsimp only
  have hpure_keep : ∀ {α : Type} (a : α) (es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)),
      es'.g.st = es.g.st → es'.h.sessions = es.h.sessions → es'.h.cache = es.h.cache →
      qry.isRight = true →
      AllSessLt M_sess (pure (a, es') : OracleComp (unifSpec + FSMultiSpec SS RS T M E) _) ∧
      ∀ z ∈ support (pure (a, es') : OracleComp (unifSpec + FSMultiSpec SS RS T M E) _),
        MultiSessIdxInv M_sess (rem - 1) z.2 := by
    intro α a es' hst hsess hca hinr
    have hpos := hrem hinr
    refine ⟨.pure _, fun z hz => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    exact ⟨fun P sIdx h => by rw [hsess]; exact hinv.vS_lt P sIdx (by simpa [hst] using h),
      fun P ep sIdx h => by rw [hsess]; exact hinv.vR_lt P ep sIdx (by simpa [hst] using h),
      fun ep Tc σc k sIdx h => by rw [hsess]; exact hinv.cache_lt ep Tc σc k sIdx (by simpa [hca] using h),
      by rw [hsess]; have := hinv.len_le; omega⟩
  rcases qry with n | (((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩)
  · simp only [implEDFShiftedPaper, Sum.isRight, QueryImpl.add_apply_inl, Bool.false_eq_true,
      ↓reduceIte, coinsE]
    dsimp only [StateT.lift, StateT.run]
    refine ⟨.coin n _ fun _ => .pure _, fun z hz => ?_⟩
    rw [mem_support_bind_iff] at hz; obtain ⟨_, _, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    exact hinv
  · -- transmitE
    have hpos : 0 < rem := hrem rfl
    have hlen1 : es.h.sessions.length + 1 ≤ M_sess := by have := hinv.len_le; omega
    simp only [implEDFShiftedPaper, Sum.isRight, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      transmitE, StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
    split
    · exact hpure_keep none es rfl rfl rfl rfl
    · cases hep : es.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none => exact hpure_keep none es rfl rfl rfl rfl
      | some s₁ =>
        have hst1 : s₁.st = es.g.st := epMgmt_st_eq hep
        dsimp only
        split
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          exact hpure_keep none { es with abort := true } rfl rfl rfl rfl
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind]
          obtain ⟨ha, hs⟩ := vSend_fsm_spec cka prng fs Δcka mo la s₁ P (s₁.st P) m none r_c es.h
            (by rw [hst1]; exact hinv.vS_lt P) (by rw [hst1]; exact hinv.vR_lt P) hinv.cache_lt hlen1
          refine ⟨ha.bind_support fun w _ => by
              rcases w with ⟨_ | ⟨_, _⟩, _⟩
              · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _,
            fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
          obtain ⟨hl1, hl2, hca, hvp⟩ := hs w hw
          rcases hw1 : w.1 with _ | ⟨st', c_out⟩
          · simp only [hw1, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
              fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
              hca, by dsimp only; have := hinv.len_le; omega⟩
          · simp only [hw1, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
            obtain ⟨hvpS, hvpR⟩ := hvp st' c_out hw1
            refine ⟨?_, ?_, hca, by dsimp only; have := hinv.len_le; omega⟩
            · intro Q sIdx h; simp only [GameState.record] at h
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self] at h; exact hvpS sIdx h
              · simp only [Function.update_of_ne hQ, hst1] at h; exact lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1
            · intro Q ep sIdx h; simp only [GameState.record] at h
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self] at h; exact hvpR ep sIdx h
              · simp only [Function.update_of_ne hQ, hst1] at h; exact lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1
  · -- challE
    have hpos : 0 < rem := hrem rfl
    have hlen1 : es.h.sessions.length + 1 ≤ M_sess := by have := hinv.len_le; omega
    simp only [implEDFShiftedPaper, Sum.isRight, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      challE, StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
    split
    · exact hpure_keep none es rfl rfl rfl rfl
    · cases hep : es.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none => exact hpure_keep none es rfl rfl rfl rfl
      | some s₁ =>
        have hst1 : s₁.st = es.g.st := epMgmt_st_eq hep
        dsimp only
        split
        · exact hpure_keep none es rfl rfl rfl rfl
        · split
          · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
            exact hpure_keep none { es with abort := true } rfl rfl rfl rfl
          · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind]
            obtain ⟨ha, hs⟩ := vSend_fsm_spec cka prng fs Δcka mo la s₁ P (s₁.st P)
              ((mo.cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)) (some (m₀, m₁)) r_c es.h
              (by rw [hst1]; exact hinv.vS_lt P) (by rw [hst1]; exact hinv.vR_lt P) hinv.cache_lt hlen1
            refine ⟨ha.bind_support fun w _ => by
                rcases w with ⟨_ | ⟨_, _⟩, _⟩
                · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _,
              fun z hz => ?_⟩
            rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
            obtain ⟨hl1, hl2, hca, hvp⟩ := hs w hw
            rcases hw1 : w.1 with _ | ⟨st', c_out⟩
            · simp only [hw1, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
                fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
                hca, by dsimp only; have := hinv.len_le; omega⟩
            · simp only [hw1, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
              obtain ⟨hvpS, hvpR⟩ := hvp st' c_out hw1
              refine ⟨?_, ?_, hca, by dsimp only; have := hinv.len_le; omega⟩
              · intro Q sIdx h; simp only [GameState.record] at h
                by_cases hQ : Q = P
                · subst hQ; simp only [Function.update_self] at h; exact hvpS sIdx h
                · simp only [Function.update_of_ne hQ, hst1] at h; exact lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1
              · intro Q ep sIdx h; simp only [GameState.record] at h
                by_cases hQ : Q = P
                · subst hQ; simp only [Function.update_self] at h; exact hvpR ep sIdx h
                · simp only [Function.update_of_ne hQ, hst1] at h; exact lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1
  · -- deliverE
    have hpos : 0 < rem := hrem rfl
    have hlen1 : es.h.sessions.length + 1 ≤ M_sess := by have := hinv.len_le; omega
    simp only [implEDFShiftedPaper, Sum.isRight, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      deliverE, StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
    split
    · exact hpure_keep none es rfl rfl rfl rfl
    · cases htr : es.g.inTransit P.other c with
      | none => exact hpure_keep none es rfl rfl rfl rfl
      | some rec =>
        simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind]
        obtain ⟨ha, hs⟩ := vRecv_fsm_spec cka prng fs Δcka mo la es.g P (es.g.st P) c (some rec) es.h
          (hinv.vS_lt P) (hinv.vR_lt P) hinv.cache_lt hlen1
        refine ⟨ha.bind_support fun w _ => by
            rcases w with ⟨_ | (_ | ⟨_, _, _, _⟩), _⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
            · dsimp only; split
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
              · simp only [StateT.run_pure]; exact .pure _
            · dsimp only
              simp only [commitE, hooksFSMulti_commit, StateT.run_bind, liftH_run,
                StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind]
              exact .pure _,
          fun z hz => ?_⟩
        rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
        obtain ⟨hl1, hl2, hca, hvp⟩ := hs w hw
        rcases hw1 : w.1 with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [hw1, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
            fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
            by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
            by dsimp only; have := hinv.len_le; omega⟩
        · simp only [hw1] at hz
          split at hz
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
              fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
              by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
              by dsimp only; have := hinv.len_le; omega⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
              fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
              by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
              by dsimp only; have := hinv.len_le; omega⟩
        · simp only [hw1, commitE, hooksFSMulti_commit, StateT.run_bind, liftH_run,
            StateT.run_pure, bind_assoc, pure_bind] at hz
          obtain ⟨hvpS, hvpR⟩ := hvp st' t' i' m' hw1
          simp only [StateT.run_modify, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz; subst hz
          refine ⟨?_, ?_, by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
            by dsimp only; have := hinv.len_le; omega⟩
          · intro Q sIdx h
            dsimp only [GameState.accept, GameState.delete] at h
            split_ifs at h
            all_goals
              dsimp only at h
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self] at h; exact hvpS sIdx h
              · simp only [Function.update_of_ne hQ] at h; exact lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1
          · intro Q ep sIdx h
            dsimp only [GameState.accept, GameState.delete] at h
            split_ifs at h
            all_goals
              dsimp only at h
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self] at h; exact hvpR ep sIdx h
              · simp only [Function.update_of_ne hQ] at h; exact lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1
  · -- injectE
    have hpos : 0 < rem := hrem rfl
    have hlen1 : es.h.sessions.length + 1 ≤ M_sess := by have := hinv.len_le; omega
    simp only [implEDFShiftedPaper, Sum.isRight, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      injectE, StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
    split
    · exact hpure_keep none es rfl rfl rfl rfl
    · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind]
      obtain ⟨ha, hs⟩ := vRecv_fsm_spec cka prng fs Δcka mo la es.g P (es.g.st P) c none es.h
        (hinv.vS_lt P) (hinv.vR_lt P) hinv.cache_lt hlen1
      refine ⟨ha.bind_support fun w _ => by
          rcases w with ⟨_ | (_ | ⟨_, _, _, _⟩), _⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
          · simp only [StateT.run_pure]; exact .pure _
          · dsimp only; split
            · simp only [StateT.run_pure]; exact .pure _
            · split
              · simp only [commitE, hooksFSMulti_commit, StateT.run_bind, liftH_run, StateT.run_modify,
                  StateT.run_pure, bind_assoc, pure_bind]; exact .pure _
              · split
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
                · simp only [StateT.run_pure]; exact .pure _,
        fun z hz => ?_⟩
      rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨hl1, hl2, hca, hvp⟩ := hs w hw
      rcases hw1 : w.1 with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [hw1, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
        exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
          fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
          by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
          by dsimp only; have := hinv.len_le; omega⟩
      · simp only [hw1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
        exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
          fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
          by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
          by dsimp only; have := hinv.len_le; omega⟩
      · simp only [hw1] at hz
        obtain ⟨hvpS, hvpR⟩ := hvp st' t' i' m' hw1
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
            fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
            by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
            by dsimp only; have := hinv.len_le; omega⟩
        · split at hz
          · simp only [commitE, hooksFSMulti_commit, StateT.run_bind, liftH_run, StateT.run_modify,
              StateT.run_pure, bind_assoc, pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
            refine ⟨?_, ?_, by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
              by dsimp only; have := hinv.len_le; omega⟩
            · intro Q sIdx h; dsimp only [GameState.accept, GameState.delete] at h
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self] at h; exact hvpS sIdx h
              · simp only [Function.update_of_ne hQ] at h; exact lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1
            · intro Q ep sIdx h; dsimp only [GameState.accept, GameState.delete] at h
              by_cases hQ : Q = P
              · subst hQ; simp only [Function.update_self] at h; exact hvpR ep sIdx h
              · simp only [Function.update_of_ne hQ] at h; exact lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1
          · split at hz
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
                fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
                by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
                by dsimp only; have := hinv.len_le; omega⟩
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
                fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
                by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
                by dsimp only; have := hinv.len_le; omega⟩
  · -- corrEShiftedPaper
    have hpos : 0 < rem := hrem rfl
    have hlen0 : es.h.sessions.length ≤ M_sess := by have := hinv.len_le; omega
    simp only [implEDFShiftedPaper, Sum.isRight, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
    split
    · exact hpure_keep none es rfl rfl rfl rfl
    · split
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
        exact hpure_keep none { es with abort := true } rfl rfl rfl rfl
      · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind]
        obtain ⟨ha, hs⟩ := reveal_fsm_spec cka prng fs Δcka mo la es.g P (es.g.st P) es.h (hinv.vS_lt P) hlen0
        refine ⟨ha.bind_support fun w _ => by
            rcases w with ⟨_ | _, _⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _,
          fun z hz => ?_⟩
        rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
        obtain ⟨hsess, hca⟩ := hs w hw
        rcases hw1 : w.1 with _ | stOut
        · simp only [hw1, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨fun Q sIdx h => by rw [hsess]; exact hinv.vS_lt Q sIdx h,
            fun Q ep sIdx h => by rw [hsess]; exact hinv.vR_lt Q ep sIdx h,
            fun ep Tc σc k sIdx hc => by rw [hsess]; exact hinv.cache_lt ep Tc σc k sIdx (by simpa [hca] using hc),
            by dsimp only; rw [hsess]; have := hinv.len_le; omega⟩
        · simp only [hw1, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨fun Q sIdx h => by rw [hsess]; exact hinv.vS_lt Q sIdx (by simpa [afterCorrShifted_st_eq] using h),
            fun Q ep sIdx h => by rw [hsess]; exact hinv.vR_lt Q ep sIdx (by simpa [afterCorrShifted_st_eq] using h),
            fun ep Tc σc k sIdx hc => by rw [hsess]; exact hinv.cache_lt ep Tc σc k sIdx (by simpa [hca] using hc),
            by dsimp only; rw [hsess]; have := hinv.len_le; omega⟩
  · -- deliverForgeE
    have hpos : 0 < rem := hrem rfl
    have hlen1 : es.h.sessions.length + 1 ≤ M_sess := by have := hinv.len_le; omega
    simp only [implEDFShiftedPaper, Sum.isRight, QueryImpl.add_apply_inr,
      deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
    split
    · exact hpure_keep none es rfl rfl rfl rfl
    · cases htr : es.g.inTransit P.other c₁ with
      | none => exact hpure_keep none es rfl rfl rfl rfl
      | some rec =>
        dsimp only
        split
        · exact hpure_keep none es rfl rfl rfl rfl
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind]
          obtain ⟨ha, hs⟩ := vRecv_fsm_spec cka prng fs Δcka mo la es.g P (es.g.st P) c₂ none es.h
            (hinv.vS_lt P) (hinv.vR_lt P) hinv.cache_lt hlen1
          refine ⟨ha.bind_support fun w _ => by
              rcases w with ⟨_ | (_ | ⟨_, _, _, _⟩), _⟩
              · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
              · simp only [StateT.run_pure]; exact .pure _
              · dsimp only; split
                · simp only [StateT.run_pure]; exact .pure _
                · split
                  · simp only [commitE, hooksFSMulti_commit, StateT.run_bind, liftH_run, StateT.run_modify,
                      StateT.run_pure, bind_assoc, pure_bind]; exact .pure _
                  · split
                    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; exact .pure _
                    · simp only [StateT.run_pure]; exact .pure _,
            fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
          obtain ⟨hl1, hl2, hca, hvp⟩ := hs w hw
          rcases hw1 : w.1 with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [hw1, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
              fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
              by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
              by dsimp only; have := hinv.len_le; omega⟩
          · simp only [hw1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
              fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
              by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
              by dsimp only; have := hinv.len_le; omega⟩
          · simp only [hw1] at hz
            obtain ⟨hvpS, hvpR⟩ := hvp st' t' i' m' hw1
            split at hz
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
                fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
                by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
                by dsimp only; have := hinv.len_le; omega⟩
            · split at hz
              · simp only [commitE, hooksFSMulti_commit, StateT.run_bind, liftH_run, StateT.run_modify,
                  StateT.run_pure, bind_assoc, pure_bind, support_pure, Set.mem_singleton_iff] at hz; subst hz
                refine ⟨?_, ?_, by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
                  by dsimp only; have := hinv.len_le; omega⟩
                · intro Q sIdx h; dsimp only [GameState.accept, GameState.delete] at h
                  by_cases hQ : Q = P
                  · subst hQ; simp only [Function.update_self] at h; exact hvpS sIdx h
                  · simp only [Function.update_of_ne hQ] at h; exact lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1
                · intro Q ep sIdx h; dsimp only [GameState.accept, GameState.delete] at h
                  by_cases hQ : Q = P
                  · subst hQ; simp only [Function.update_self] at h; exact hvpR ep sIdx h
                  · simp only [Function.update_of_ne hQ] at h; exact lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1
              · split at hz
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                    support_pure, Set.mem_singleton_iff] at hz; subst hz
                  exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
                    fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
                    by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
                    by dsimp only; have := hinv.len_le; omega⟩
                · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
                  exact ⟨fun Q sIdx h => lt_of_lt_of_le (hinv.vS_lt Q sIdx h) hl1,
                    fun Q ep sIdx h => lt_of_lt_of_le (hinv.vR_lt Q ep sIdx h) hl1,
                    by simpa [hca] using fun ep Tc σc k sIdx hc => lt_of_lt_of_le (hinv.cache_lt ep Tc σc k sIdx hc) hl1,
                    by dsimp only; have := hinv.len_le; omega⟩

private theorem redFSAuthDFShiftedPaperMulti_offRange
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep l t : ℕ) (ht0 : 0 < t) (la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFShiftedPaperMulti cka prng fs lam Δcka qep l t la A).IsQueryBoundP
      (fun u => sessOffRange q u = true) 0 := by
  refine AllSessLt.to_isQueryBoundP ?_
  unfold redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  have hImpl : implEDFShiftedPaperGen false l
      (hooksFSMulti cka prng fs Δcka ⟨true, some (l - 1), t⟩ false la)
      (2 + Δcka) qep fs.maxSkip t (⟨true, some (l - 1), t⟩ : Mode).cfg
      (⟨true, some (l - 1), t⟩ : Mode).policy =
    implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka ⟨true, some (l - 1), t⟩ false la)
      (2 + Δcka) qep fs.maxSkip (⟨true, some (l - 1), t⟩ : Mode).cfg
      (⟨true, some (l - 1), t⟩ : Mode).policy := rfl
  simp only [Bool.not_true, hImpl, bind_assoc]
  obtain ⟨hinit_all, hinit_inv⟩ := initFSMultiRaw_allSessLt_and_inv
    (SS := SS) (RS := RS) (M := M) (E := E) cka prng fs lam q l t ht0
  refine hinit_all.bind_support fun es₀ hes₀ => ?_
  suffices hloop : ∀ (oa : SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (rem : ℕ)
      (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)),
      MakesAtMostQueriesDF oa rem →
      MultiSessIdxInv q rem es →
      AllSessLt q
        ((simulateQ (implEDFShiftedPaper l
          (hooksFSMulti cka prng fs Δcka ⟨true, some (l - 1), t⟩ false la)
          (2 + Δcka) qep fs.maxSkip (⟨true, some (l - 1), t⟩ : Mode).cfg
          (⟨true, some (l - 1), t⟩ : Mode).policy) oa).run es >>=
          fun z => pure (if la then z.2.h.lfWin else authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy z.2)) from
    hloop A q es₀ hq (hinit_inv es₀ hes₀)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro rem es _ _; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact .pure _
  | query_bind qry cont ih =>
    intro rem es hq_oa hinv
    rw [MakesAtMostQueriesDF, isQueryBoundP_query_bind_iff] at hq_oa
    rw [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    have hrem : qry.isRight = true → 0 < rem := fun hinr => by
      rcases qry with n | q_df
      · cases hinr
      · exact hq_oa.1.resolve_left (by simp)
    obtain ⟨hstep_all, hstep_inv⟩ :=
      stepFSMulti_allSessLt_and_inv cka prng fs Δcka qep l t q rem la es hinv qry hrem
    refine hstep_all.bind_support fun z hz =>
      ih z.1 (if qry.isRight then rem - 1 else rem) z.2 ?_ (hstep_inv z hz)
    rcases qry with n | q_df <;> simpa [MakesAtMostQueriesDF, Sum.isRight] using hq_oa.2 z.1

end ShiftedDir1IdxInv
open _root_.CryptoGames.SM (Config ltOpt)
open _root_.CryptoGames.SM.Engine (EState VP transmitE challE deliverE injectE coinsE authOut)
open _root_.CryptoGames.SM.Construction (FSMultiState FSMultiSpec Mode hooksFSMulti)
open _root_.CryptoGames.SM.Construction.DeliverForge (corrEShiftedPaper deliverForgeE implEDFShiftedPaper)
open _root_.CryptoGames.SM.Construction.AuthL11 (evalDist_bind_eq_one evalDist_bind_congr_true)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (query_eq_liftM)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec)

private theorem simulateQ_lImpl_coinsE_run {Γv T Sv SSv RSv M E HS : Type}
    (n : ℕ) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
      ((_root_.CryptoGames.SM.Engine.coinsE n).run es) =
    (query (spec := unifSpec) n >>= fun u => pure (u, es)) := by
  dsimp only [_root_.CryptoGames.SM.Engine.coinsE, StateT.lift, StateT.run]
  simp [_root_.CryptoGames.SM.Construction.AuthL11.lImpl, QueryImpl.add_apply_inl,
    QueryImpl.id'_apply]

section PrefixKeying

open _root_.CryptoGames.SM.Engine (EState Ctx Hooks authOut)
open _root_.CryptoGames.SM.Construction (Mode PartyState sampleT realParty)
open _root_.CryptoGames.SM.Construction.DeliverForge (implEDFShiftedPaper)
open _root_.CryptoGames.SM.Construction.AuthL11 (nilSpec lImpl LState EStateL lookupFL regSess
  regSessOf rootL hooksLocal initLocal evalDist_bind_mono)

private theorem hooksLocalPrefix_zero_eq {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (ks : ℕ → K) :
    hooksLocalPrefix (M := M) cka prng fs mo 0 ks = hooksLocal cka prng fs mo := by
  have hlk : ∀ (Ik : I) (s : LState T Sig K I),
      (lookupFLPrefix (T := T) (Sig := Sig) 0 ks Ik).run s =
      (@lookupFL T I Sig K _ _ Ik).run s := by
    intro Ik s
    simp only [lookupFLPrefix, lookupFL, StateT.run_bind, StateT.run_get, pure_bind]
    cases h : s.table.lookup Ik <;> simp
  have hrt : ∀ (t' : ℕ) (Ik : I) (σ : Sig),
      rootLPrefix (T := T) prng mo 0 ks t' Ik σ =
      @rootL T I KR Sig K _ _ _ prng mo t' Ik σ := by
    intro t' Ik σ; apply StateT.ext; intro s
    unfold rootLPrefix rootL
    split_ifs <;> simp [hlk, StateT.run_bind]
  unfold hooksLocalPrefix hooksLocal
  have _hlk_ext : ∀ Ik : I, lookupFLPrefix (T := T) (Sig := Sig) 0 ks Ik =
      @lookupFL T I Sig K _ _ Ik := fun Ik => StateT.ext (hlk Ik)
  simp only [_hlk_ext]
  congr 1
  funext _ _ t' γ σ rOpt; cases rOpt <;> simp [hrt]

private theorem simulateQ_lImpl_sampleT_run {X σ : Type} [SampleableType X] (s : σ) :
    simulateQ lImpl ((StateT.lift (sampleT X) : StateT σ (_root_.CryptoGames.SM.Engine.TComp nilSpec) X).run s) =
      (($ᵗ X : ProbComp X) >>= fun x => pure (x, s)) :=
  _root_.CryptoGames.SM.Construction.AuthL11.simulateQ_lImpl_run_lift_sampleT s

private theorem lookupFLPrefix_eq_and_sessions {T Sig K I : Type} [DecidableEq I] [SampleableType K]
    (r : ℕ) (ks : ℕ → K) (v : K) (Ik : I) (s : LState T Sig K I) :
    (r < s.sessions.length →
      (lookupFLPrefix (T := T) (Sig := Sig) (r + 1) (Function.update ks r v) Ik).run s =
        (lookupFLPrefix (T := T) (Sig := Sig) r ks Ik).run s) ∧
    (∀ z ∈ support (simulateQ lImpl ((lookupFLPrefix (T := T) (Sig := Sig) r ks Ik).run s)),
      z.2.sessions = s.sessions) := by
  refine ⟨fun hlt => ?_, fun z hz => ?_⟩
  · have hn1 : ¬ (s.sessions.length < r) := by omega
    have hn2 : ¬ (s.sessions.length < r + 1) := by omega
    simp only [lookupFLPrefix, StateT.run_bind, StateT.run_get, pure_bind]
    cases s.table.lookup Ik <;> simp [hn1, hn2]
  · simp only [lookupFLPrefix, StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hlk : s.table.lookup Ik with
    | some k =>
      simp only [hlk, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
    | none =>
      simp only [hlk, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_bind, simulateQ_lImpl_sampleT_run, bind_assoc, simulateQ_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨_, _, rfl⟩ := hz; rfl

private theorem rootLPrefix_eq_and_sessions {KR Sig I K T : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (mo : Mode) (r : ℕ) (ks : ℕ → K) (v : K)
    (t' : ℕ) (Ik : I) (σ : Sig) (s : LState T Sig K I) :
    (r < s.sessions.length →
      (rootLPrefix (T := T) prng mo (r + 1) (Function.update ks r v) t' Ik σ).run s =
        (rootLPrefix (T := T) prng mo r ks t' Ik σ).run s) ∧
    (∀ z ∈ support (simulateQ lImpl ((rootLPrefix (T := T) prng mo r ks t' Ik σ).run s)),
      z.2.sessions = s.sessions) := by
  obtain ⟨hlk_eq, hlk_s⟩ := lookupFLPrefix_eq_and_sessions (T := T) (Sig := Sig) r ks v Ik s
  refine ⟨fun hlt => ?_, fun z hz => ?_⟩
  · have hn1 : ¬ (s.sessions.length < r) := by omega
    have hn_le : ¬ (s.sessions.length ≤ r) := by omega
    unfold rootLPrefix
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
      dsimp only [StateT.lift, StateT.run]
      simp [hn1, hn_le]
    · simp [hlk_eq hlt]
    · rfl
    · rfl
  · unfold rootLPrefix at hz
    split_ifs at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
    · simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, bind_assoc, pure_bind,
        simulateQ_bind, simulateQ_lImpl_sampleT_run, simulateQ_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨_, _, _, _, rfl⟩ := hz; rfl
    · simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨w, hw, rfl⟩ := hz; exact hlk_s w hw
    · simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
        simulateQ_bind, simulateQ_lImpl_sampleT_run, simulateQ_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨_, _, rfl⟩ := hz; rfl
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl

private theorem regSess_sessions_le {T Sig K I : Type} [DecidableEq I]
    (Ik : I) (s : LState T Sig K I) :
    ∀ z ∈ support (simulateQ lImpl ((regSess (T := T) (Sig := Sig) (K := K) Ik).run s)),
      s.sessions.length ≤ z.2.sessions.length := by
  intro z hz
  simp only [regSess, StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hmem : Ik ∈ s.sessions
  · simp only [hmem, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact le_rfl
  · simp only [hmem, ↓reduceIte] at hz
    subst hz; simp

private theorem regSessOf_sessions_le {T Sig K I : Type} [DecidableEq I]
    (sid : Option I) (s : LState T Sig K I) :
    ∀ z ∈ support (simulateQ lImpl ((regSessOf (T := T) (Sig := Sig) (K := K) sid).run s)),
      s.sessions.length ≤ z.2.sessions.length := by
  intro z hz
  cases sid with
  | none =>
    simp only [regSessOf, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact le_rfl
  | some Ik =>
    simp only [regSessOf, StateT.run_map, simulateQ_map, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact regSess_sessions_le Ik s w hw

private theorem vSend_prefix_eq_and_mono {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (r : ℕ) (ks : ℕ → K) (v : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : _root_.CryptoGames.SM.Engine.VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (m : M) (pair : Option (M × M)) (rOpt : Option CCoins) (s : LState T Sig K I) :
    (r < s.sessions.length →
      (_root_.CryptoGames.SM.Engine.vSend (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r v))
        ctx P vp m pair rOpt).run s =
      (_root_.CryptoGames.SM.Engine.vSend (hooksLocalPrefix cka prng fs mo r ks)
        ctx P vp m pair rOpt).run s) ∧
    (∀ z ∈ support (simulateQ lImpl
        ((_root_.CryptoGames.SM.Engine.vSend (hooksLocalPrefix cka prng fs mo r ks)
          ctx P vp m pair rOpt).run s)),
      s.sessions.length ≤ z.2.sessions.length) := by
  have hss_eq : ∀ coins : CCoins, r < s.sessions.length →
      ((hooksLocalPrefix (M := M) cka prng fs mo (r + 1) (Function.update ks r v)).startSend
        ctx P (vp.tcur + 1) vp.γ vp.root (some coins)).run s =
      ((hooksLocalPrefix (M := M) cka prng fs mo r ks).startSend
        ctx P (vp.tcur + 1) vp.γ vp.root (some coins)).run s := by
    intro coins hlt
    have hrt := (rootLPrefix_eq_and_sessions prng mo r ks v (vp.tcur + 1)
      (cka.send vp.γ coins).2.2 vp.root s).1 hlt
    dsimp only [hooksLocalPrefix]
    simp only [StateT.run_bind, StateT.run_pure, pure_bind, hrt]
  have hss_mono : ∀ coins : CCoins, ∀ w ∈ support (simulateQ lImpl
      (((hooksLocalPrefix (M := M) cka prng fs mo r ks).startSend
        ctx P (vp.tcur + 1) vp.γ vp.root (some coins)).run s)),
      s.sessions.length ≤ w.2.sessions.length := by
    intro coins w hw
    simp only [hooksLocalPrefix, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      simulateQ_bind, simulateQ_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨u, hu, u2, hu2, rfl⟩ := hw
    have hs1 := (rootLPrefix_eq_and_sessions prng mo r ks (ks 0) (vp.tcur + 1)
      (cka.send vp.γ coins).2.2 vp.root s).2 u hu
    have hs2 := regSessOf_sessions_le u.1.2.2 u.2 u2 hu2
    simpa [hs1] using hs2
  refine ⟨fun hlt => ?_, fun z hz => ?_⟩
  · unfold _root_.CryptoGames.SM.Engine.vSend
    split_ifs
    · cases rOpt with
      | some c =>
        simp only [StateT.run_bind, hss_eq c hlt]
        rfl
      | none =>
        have hnone : ∀ r' ks',
            ((hooksLocalPrefix (M := M) cka prng fs mo r' ks').startSend
              ctx P (vp.tcur + 1) vp.γ vp.root none).run s =
            ((StateT.lift (sampleT CCoins) : StateT _ _ CCoins).run s >>= fun p =>
              ((hooksLocalPrefix (M := M) cka prng fs mo r' ks').startSend
                ctx P (vp.tcur + 1) vp.γ vp.root (some p.1)).run p.2) := fun _ _ => rfl
        simp only [StateT.run_bind, hnone]
        have hcongr : ((StateT.lift (sampleT CCoins) : StateT _ _ CCoins).run s >>= fun p =>
            ((hooksLocalPrefix (M := M) cka prng fs mo (r + 1) (Function.update ks r v)).startSend
              ctx P (vp.tcur + 1) vp.γ vp.root (some p.1)).run p.2) =
          ((StateT.lift (sampleT CCoins) : StateT _ _ CCoins).run s >>= fun p =>
            ((hooksLocalPrefix (M := M) cka prng fs mo r ks).startSend
              ctx P (vp.tcur + 1) vp.γ vp.root (some p.1)).run p.2) := by
          dsimp only [StateT.lift, StateT.run]
          simp only [bind_assoc, pure_bind]
          exact bind_congr fun c => hss_eq c hlt
        rw [hcongr]
        rfl
    · cases vp.vS <;> rfl
  · unfold _root_.CryptoGames.SM.Engine.vSend at hz
    split_ifs at hz
    · simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      have hwl : s.sessions.length ≤ w.2.sessions.length := by
        cases rOpt with
        | some c => exact hss_mono c w hw
        | none =>
          have hnone : ((hooksLocalPrefix (M := M) cka prng fs mo r ks).startSend
              ctx P (vp.tcur + 1) vp.γ vp.root none).run s =
            ((StateT.lift (sampleT CCoins) : StateT _ _ CCoins).run s >>= fun p =>
              ((hooksLocalPrefix (M := M) cka prng fs mo r ks).startSend
                ctx P (vp.tcur + 1) vp.γ vp.root (some p.1)).run p.2) := rfl
          rw [hnone, simulateQ_bind, simulateQ_lImpl_sampleT_run, bind_assoc, mem_support_bind_iff] at hw
          obtain ⟨c, _, hw⟩ := hw
          exact hss_mono c w (by simpa only [pure_bind] using hw)
      rcases w with ⟨_ | ⟨γ', T', σ', ss⟩, s_w⟩
      · simp only [] at hz
        subst hz; exact hwl
      · simp only [hooksLocalPrefix, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwl
    · simp only [pure_bind, hooksLocalPrefix] at hz
      cases hvs : vp.vS with
      | none =>
        simp only [hvs, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      | some v0 =>
        simp only [hvs, StateT.run_pure, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl

private theorem vRecv_prefix_eq_and_mono {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (r : ℕ) (ks : ℕ → K) (v : K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : _root_.CryptoGames.SM.Engine.VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (c : Header T × E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (s : LState T Sig K I) :
    (r < s.sessions.length →
      (_root_.CryptoGames.SM.Engine.vRecv (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r v))
        ctx P vp c rec).run s =
      (_root_.CryptoGames.SM.Engine.vRecv (hooksLocalPrefix cka prng fs mo r ks)
        ctx P vp c rec).run s) ∧
    (∀ z ∈ support (simulateQ lImpl
        ((_root_.CryptoGames.SM.Engine.vRecv (hooksLocalPrefix cka prng fs mo r ks)
          ctx P vp c rec).run s)),
      s.sessions.length ≤ z.2.sessions.length) := by
  have hsr_eq : ∀ Tn : T, r < s.sessions.length →
      ((hooksLocalPrefix (M := M) cka prng fs mo (r + 1) (Function.update ks r v)).startRecv
        ctx P c.1.1 vp.γ vp.root Tn).run s =
      ((hooksLocalPrefix (M := M) cka prng fs mo r ks).startRecv
        ctx P c.1.1 vp.γ vp.root Tn).run s := by
    intro Tn hlt
    have hlk := (lookupFLPrefix_eq_and_sessions (T := T) (Sig := Sig) r ks v
      (cka.receive vp.γ Tn).2 s).1 hlt
    simp only [hooksLocalPrefix, StateT.run_bind, StateT.run_get, pure_bind]
    cases s.cache c.1.1 with
    | none => split_ifs <;> simp [StateT.run_bind, hlk]
    | some val =>
      rcases val with ⟨Tc, σc, k, idx?⟩
      by_cases hTc : Tc = Tn
      · simp [hTc]
      · simp only [hTc, ↓reduceIte]; split_ifs <;> simp [StateT.run_bind, hlk]
  have hsr_mono : ∀ Tn : T, ∀ w ∈ support (simulateQ lImpl
      (((hooksLocalPrefix (M := M) cka prng fs mo r ks).startRecv
        ctx P c.1.1 vp.γ vp.root Tn).run s)),
      s.sessions.length ≤ w.2.sessions.length := by
    intro Tn w hw
    simp only [hooksLocalPrefix, StateT.run_bind, StateT.run_get, pure_bind] at hw
    have hbr : ∀ (h1 : (mo.auth && decide (c.1.1 = mo.tStar)) = true)
        (h2 : ¬ (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true),
        w ∈ support (simulateQ lImpl ((do
          let kk := cka.receive vp.γ Tn
          let k' ← lookupFLPrefix r ks kk.2
          let idx ← regSess kk.2
          return some (some (kk.1, (prng.up vp.root kk.2).1, (fs.initReceiver k', some idx)))).run s)) →
        s.sessions.length ≤ w.2.sessions.length := by
      intro _ _ hw'
      simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw'
      obtain ⟨u, hu, u2, hu2, rfl⟩ := hw'
      have hs1 := (lookupFLPrefix_eq_and_sessions (T := T) (Sig := Sig) r ks (ks 0)
        (cka.receive vp.γ Tn).2 s).2 u hu
      have hs2 := regSess_sessions_le (cka.receive vp.γ Tn).2 u.2 u2 hu2
      simpa [hs1] using hs2
    cases hca : s.cache c.1.1 with
    | none =>
      simp only [hca] at hw
      split_ifs at hw with h1 h2
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
        subst hw; exact le_rfl
      · exact hbr h1 h2 hw
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
        subst hw; exact le_rfl
    | some val =>
      rcases val with ⟨Tc, σc, k, idx?⟩
      simp only [hca] at hw
      by_cases hTc : Tc = Tn
      · simp only [hTc, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hw
        subst hw; exact le_rfl
      · simp only [hTc, ↓reduceIte] at hw
        split_ifs at hw with h1 h2
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
          subst hw; exact le_rfl
        · exact hbr h1 h2 hw
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
          subst hw; exact le_rfl
  refine ⟨fun hlt => ?_, fun z hz => ?_⟩
  · unfold _root_.CryptoGames.SM.Engine.vRecv; dsimp only
    split_ifs
    · rfl
    · cases c.1.2 with
      | none => rfl
      | some Tn =>
        simp only [StateT.run_bind, hsr_eq Tn hlt]
        rfl
    · rfl
  · unfold _root_.CryptoGames.SM.Engine.vRecv at hz; dsimp only at hz
    split_ifs at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
    · cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      | some Tn =>
        simp only [hc2, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
        obtain ⟨w, hw, hz⟩ := hz
        have hwl := hsr_mono Tn w hw
        rcases w with ⟨_ | (_ | ⟨γ', σ', rs⟩), s_w⟩
        · simp only [] at hz
          subst hz; exact hwl
        · simp only [] at hz
          subst hz; exact hwl
        · simp only [hooksLocalPrefix, Function.update_self, StateT.run_bind, pure_bind] at hz
          cases hfs : fs.receive rs.1 c.1 c.2 with
          | none =>
            simp only [hfs, StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz; exact hwl
          | some out =>
            rcases out with ⟨rs', i, m⟩
            simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwl
    · simp only [pure_bind, hooksLocalPrefix] at hz
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      | some v0 =>
        simp only [hvR] at hz
        cases hfs : fs.receive v0.1 c.1 c.2 with
        | none =>
          simp only [hfs, StateT.run_pure, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl
        | some out =>
          rcases out with ⟨rs', i, m⟩
          simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl

private theorem stepLPrefix_eq_and_mono {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (r : ℕ) (ks : ℕ → K) (v : K)
    (qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    (r < esL.h.sessions.length →
      simulateQ lImpl ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r v))
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL) =
      simulateQ lImpl ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)) ∧
    (∀ z ∈ support (simulateQ lImpl ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)),
      esL.h.sessions.length ≤ z.2.h.sessions.length) := by
  refine ⟨fun hlt => ?_, fun z hz => ?_⟩
  · apply congrArg (simulateQ lImpl)
    rcases qry with n | (((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩)
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl]
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.transmitE, StateT.run_bind, StateT.run_get, pure_bind]
      split; · rfl
      cases esL.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none => rfl
      | some s₁ =>
        dsimp only
        split; · rfl
        simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind,
          (vSend_prefix_eq_and_mono cka prng fs mo r ks v s₁ P (s₁.st P) m none r_c esL.h).1 hlt]
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.challE, StateT.run_bind, StateT.run_get, pure_bind]
      split; · rfl
      cases esL.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none => rfl
      | some s₁ =>
        dsimp only
        split; · rfl
        split; · rfl
        simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind,
          (vSend_prefix_eq_and_mono cka prng fs mo r ks v s₁ P (s₁.st P) _ (some (m₀, m₁)) r_c esL.h).1 hlt]
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.deliverE, StateT.run_bind, StateT.run_get, pure_bind]
      split; · rfl
      cases esL.g.inTransit P.other c with
      | none => rfl
      | some rec =>
        dsimp only
        simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind,
          (vRecv_prefix_eq_and_mono cka prng fs mo r ks v esL.g P (esL.g.st P) c (some rec) esL.h).1 hlt]
        simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix]
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.injectE, StateT.run_bind, StateT.run_get, pure_bind]
      split; · rfl
      simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind,
        (vRecv_prefix_eq_and_mono cka prng fs mo r ks v esL.g P (esL.g.st P) c none esL.h).1 hlt]
      simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix]
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper, hooksLocalPrefix]
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind]
      split; · rfl
      cases esL.g.inTransit P.other c₁ with
      | none => rfl
      | some rec =>
        dsimp only
        split; · rfl
        simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind,
          (vRecv_prefix_eq_and_mono cka prng fs mo r ks v esL.g P (esL.g.st P) c₂ none esL.h).1 hlt]
        simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix]
  · rcases qry with n | (((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩)
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, _root_.CryptoGames.SM.Engine.coinsE] at hz
      dsimp only [StateT.lift, StateT.run] at hz
      simp only [lImpl, simulateQ_bind,
        simulateQ_pure] at hz
      rw [mem_support_bind_iff] at hz; obtain ⟨_, _, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact le_rfl
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.transmitE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      · cases hep : esL.g.epMgmt (2 + Δcka) qep P r_c.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl
        | some s₁ =>
          simp only [hep] at hz
          split at hz
          · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
              pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact le_rfl
          · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨w, hw, hz⟩ := hz
            have hwl := (vSend_prefix_eq_and_mono cka prng fs mo r ks (ks 0) s₁ P (s₁.st P) m none r_c esL.h).2 w hw
            rcases w with ⟨_ | ⟨st', c_out⟩, s_w⟩ <;>
              simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
                pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz <;>
              subst hz <;> exact hwl
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.challE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      · cases hep : esL.g.epMgmt (2 + Δcka) qep P r_c.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl
        | some s₁ =>
          simp only [hep] at hz
          split at hz
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact le_rfl
          · split at hz
            · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
                pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact le_rfl
            · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
              obtain ⟨w, hw, hz⟩ := hz
              have hwl := (vSend_prefix_eq_and_mono cka prng fs mo r ks (ks 0) s₁ P (s₁.st P) _ (some (m₀, m₁)) r_c esL.h).2 w hw
              rcases w with ⟨_ | ⟨st', c_out⟩, s_w⟩ <;>
                simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
                  pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz <;>
                subst hz <;> exact hwl
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.deliverE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      · cases htr : esL.g.inTransit P.other c with
        | none =>
          simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl
        | some rec =>
          simp only [htr, StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
          obtain ⟨w, hw, hz⟩ := hz
          have hwl := (vRecv_prefix_eq_and_mono cka prng fs mo r ks (ks 0) esL.g P (esL.g.st P) c (some rec) esL.h).2 w hw
          rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), s_w⟩
          · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
              pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwl
          · dsimp only at hz; split at hz <;>
              simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz <;>
              subst hz <;> exact hwl
          · dsimp only at hz
            simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix, StateT.run_bind,
              liftH_run, StateT.run_pure, StateT.run_modify, bind_assoc, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            rcases hz with rfl; exact hwl
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Engine.injectE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
        obtain ⟨w, hw, hz⟩ := hz
        have hwl := (vRecv_prefix_eq_and_mono cka prng fs mo r ks (ks 0) esL.g P (esL.g.st P) c none esL.h).2 w hw
        rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), s_w⟩
        · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
            pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwl
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwl
        · dsimp only at hz; split at hz
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwl
          · split at hz
            · simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix, StateT.run_bind,
                liftH_run, StateT.run_pure, StateT.run_modify, bind_assoc, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwl
            · split at hz <;>
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz <;>
                subst hz <;> exact hwl
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper,
        StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      · split at hz
        · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
            pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl
        · simp only [hooksLocalPrefix, StateT.run_bind, liftH_run, StateT.run_pure, StateT.run_modify,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr,
        _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact le_rfl
      · cases htr : esL.g.inTransit P.other c₁ with
        | none =>
          simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact le_rfl
        | some rec =>
          simp only [htr] at hz
          split at hz
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact le_rfl
          · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨w, hw, hz⟩ := hz
            have hwl := (vRecv_prefix_eq_and_mono cka prng fs mo r ks (ks 0) esL.g P
              (esL.g.st P) c₂ none esL.h).2 w hw
            rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), s_w⟩
            · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
                pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwl
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwl
            · dsimp only at hz; split at hz
              · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hwl
              · split at hz
                · simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix, StateT.run_bind,
                    liftH_run, StateT.run_pure, StateT.run_modify, bind_assoc, pure_bind,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hwl
                · split at hz <;>
                    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz <;>
                    subst hz <;> exact hwl

private theorem evalDist_runLocPrefix_eq_of_lt {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode)
    (r : ℕ) (ks : ℕ → K) (v : K)
    (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (esL : EStateL Γ T Sig SS RS M E K I) (hlt : r < esL.h.sessions.length) :
    𝒟[simulateQ lImpl ((simulateQ (implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)] {true} =
    𝒟[simulateQ lImpl ((simulateQ (implEDFShiftedPaper l
        (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r v))
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b => simp
  | query_bind qry cont ih =>
    simp only [simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_bind, bind_assoc]
    obtain ⟨heq, hmono⟩ := stepLPrefix_eq_and_mono cka prng fs Δcka qep l mo r ks v qry esL
    rw [heq hlt]
    exact _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_congr_true _ _ _ fun z hz =>
      ih z.1 z.2 (lt_of_lt_of_le hlt (hmono z hz))

private theorem shiftLe_lookupFLPrefix_regSess {T Sig K I : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType I] [SampleableType K]
    (mo : Mode) (r : ℕ) (ks : ℕ → K) (Ik : I) {s : LState T Sig K I}
    (hle : s.sessions.length ≤ r)
    (hinv : _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo s)
    (hnot_th : ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH)) :
    _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
      (simulateQ lImpl (((lookupFLPrefix r ks Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
        StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (K × ℕ)).run s))
      (fun k_fs => simulateQ lImpl
        (((lookupFLPrefix (r + 1) (Function.update ks r k_fs) Ik >>= fun k =>
          regSess Ik >>= fun idx => pure (k, idx)) :
            StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (K × ℕ)).run s)) := by
  have htab_iff := hinv hnot_th Ik
  simp only [lookupFLPrefix, regSess, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hmem : Ik ∈ s.sessions
  · have hsome : (s.table.lookup Ik).isSome = true := by simpa [hmem] using htab_iff
    obtain ⟨k₀, hlk⟩ := Option.isSome_iff_exists.mp hsome
    simp only [hlk, pure_bind, hmem, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo ((k₀, s.sessions.idxOf Ik), s) hle hinv
  · have hnone : s.table.lookup Ik = none := by
      cases h : s.table.lookup Ik with
      | none => rfl
      | some v => simp [h, hmem] at htab_iff
    simp only [hnone, StateT.run_bind, StateT.run_modify, pure_bind, hmem,
      ↓reduceIte, StateT.run_set, StateT.run_pure, simulateQ_bind,
      simulateQ_lImpl_sampleT_run, simulateQ_pure, bind_assoc]
    by_cases hlen_eq : s.sessions.length = r
    · subst hlen_eq
      simp only [lt_irrefl, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, Function.update_self]
      refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.transition (getH := Prod.snd) mo
        (fun (k : K) => ((k, s.sessions.length),
          { s with table := (Ik, k) :: s.table, sessions := s.sessions ++ [Ik] })) ?_
      intro k; dsimp only; rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_self _
    · have hlt : s.sessions.length < r := Nat.lt_of_le_of_ne hle hlen_eq
      have hlt1 : s.sessions.length < r + 1 := by omega
      simp only [hlt, hlt1, ↓reduceIte, Function.update_of_ne hlen_eq]
      refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.sample_bind mo ($ᵗ K) fun _ _ => ?_
      refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure (getH := Prod.snd) mo
        ((ks s.sessions.length, s.sessions.length),
          { s with table := (Ik, ks s.sessions.length) :: s.table, sessions := s.sessions ++ [Ik] }) ?_
        (_root_.CryptoGames.SM.Construction.AuthL11.tabSessInv_insert mo hinv Ik (ks s.sessions.length))
      dsimp only; rw [List.length_append, List.length_singleton]; omega

private theorem shiftLe_rootLPrefix_regSessOf {KR Sig I K T : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (mo : Mode) (r : ℕ) (ks : ℕ → K)
    (t' : ℕ) (Ik : I) (σ : Sig) {s : LState T Sig K I}
    (hle : s.sessions.length ≤ r)
    (hinv : _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo s) :
    _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
      (simulateQ lImpl (((rootLPrefix prng mo r ks t' Ik σ >>= fun (σ', k, sid) =>
        regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
          StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (Sig × K × Option ℕ)).run s))
      (fun k_fs => simulateQ lImpl
        (((rootLPrefix prng mo (r + 1) (Function.update ks r k_fs) t' Ik σ >>= fun (σ', k, sid) =>
          regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
            StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (Sig × K × Option ℕ)).run s)) := by
  unfold rootLPrefix
  by_cases hgt : mo.tStar < t'
  · simp only [hgt, ↓reduceIte, regSessOf, StateT.run_pure, pure_bind, simulateQ_pure]
    exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure (getH := Prod.snd) mo
      (((prng.up σ Ik).1, (prng.up σ Ik).2, none), s) hle hinv
  · simp only [hgt, ↓reduceIte]
    by_cases heq : t' = mo.tStar
    · subst heq
      simp only [↓reduceIte]
      by_cases hth : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · simp only [hth, ↓reduceIte, regSessOf, regSess, StateT.run_bind, StateT.run_get,
          StateT.run_map, StateT.run_pure, pure_bind, simulateQ_bind,
          simulateQ_lImpl_sampleT_run, simulateQ_pure, bind_assoc]
        have hinv_any : ∀ s' : LState T Sig K I, _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo s' := by
          intro s' hnot; simp only [Bool.and_eq_true, decide_eq_true_eq] at hth; exact False.elim (hnot hth)
        refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.sample_bind mo ($ᵗ I) fun Ir _ => ?_
        by_cases hmem : Ir ∈ s.sessions
        · simp only [hmem, ↓reduceIte, StateT.run_pure]
          refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.sample_bind mo ($ᵗ K) fun k _ => ?_
          exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure (getH := Prod.snd) mo
            (((prng.up σ Ir).1, k, some (s.sessions.idxOf Ir)), s) hle (hinv_any s)
        · simp only [hmem, ↓reduceIte]
          by_cases hlen_eq : s.sessions.length = r
          · subst hlen_eq
            simp only [lt_irrefl, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, Function.update_self]
            refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.transition (getH := Prod.snd) mo
              (fun (k : K) => (((prng.up σ Ir).1, k, some s.sessions.length),
                { s with sessions := s.sessions ++ [Ir] })) ?_
            intro k; dsimp only; rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_self _
          · have hlt : s.sessions.length < r := Nat.lt_of_le_of_ne hle hlen_eq
            have hlt1 : s.sessions.length < r + 1 := by omega
            simp only [hlt, hlt1, ↓reduceIte, Function.update_of_ne hlen_eq]
            refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.sample_bind mo ($ᵗ K) fun _ _ => ?_
            refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure (getH := Prod.snd) mo
              (((prng.up σ Ir).1, ks s.sessions.length, some s.sessions.length),
                { s with sessions := s.sessions ++ [Ir] }) ?_ (hinv_any _)
            dsimp only; rw [List.length_append, List.length_singleton]; omega
      · simp only [hth, Bool.false_eq_true, ↓reduceIte]
        have hnot_th : ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
          intro ⟨h1, h2⟩; simp [h1, h2] at hth
        have hbind : ∀ r' ks', StateT.run (((lookupFLPrefix r' ks' Ik >>= fun k =>
            pure ((prng.up σ Ik).1, k, some Ik)) >>=
            fun x => regSessOf x.2.2 >>= fun idx? => pure (x.1, x.2.1, idx?)) :
              StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (Sig × K × Option ℕ)) s =
          (((lookupFLPrefix r' ks' Ik >>= fun k => regSess Ik >>= fun idx => pure (k, idx)) :
            StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (K × ℕ)).run s >>= fun res =>
              pure (((prng.up σ Ik).1, res.1.1, some res.1.2), res.2)) := by
          intro r' ks'
          simp only [regSessOf, StateT.run_bind, StateT.run_pure, pure_bind,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
        simp only [hbind, simulateQ_bind, simulateQ_pure]
        refine (shiftLe_lookupFLPrefix_regSess mo r ks Ik hle hinv hnot_th).post mo _ ?_
        intro a b hb
        simp only [support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
    · simp only [heq, ↓reduceIte]
      split_ifs
      · simp only [regSessOf, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_bind,
          simulateQ_lImpl_sampleT_run, simulateQ_pure, bind_assoc]
        refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.sample_bind mo ($ᵗ I) fun Ir _ => ?_
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo
          (((prng.up σ Ir).1, (prng.up σ Ir).2, none), s) hle hinv
      · simp only [regSessOf, StateT.run_pure, pure_bind, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo
          (((prng.up σ Ik).1, (prng.up σ Ik).2, none), s) hle hinv

private theorem shiftLe_vSend_prefix {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (r : ℕ) (ks : ℕ → K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : _root_.CryptoGames.SM.Engine.VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (m : M) (pair : Option (M × M)) (rOpt : Option CCoins) {s : LState T Sig K I}
    (hle : s.sessions.length ≤ r)
    (hinv : _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo s) :
    _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
      (simulateQ lImpl ((_root_.CryptoGames.SM.Engine.vSend
        (hooksLocalPrefix cka prng fs mo r ks) ctx P vp m pair rOpt).run s))
      (fun k_fs => simulateQ lImpl ((_root_.CryptoGames.SM.Engine.vSend
        (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r k_fs)) ctx P vp m pair rOpt).run s)) := by
  have hss : ∀ rOpt' : Option CCoins,
      _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
        (simulateQ lImpl (((hooksLocalPrefix (M := M) cka prng fs mo r ks).startSend
          ctx P (vp.tcur + 1) vp.γ vp.root rOpt').run s))
        (fun k_fs => simulateQ lImpl (((hooksLocalPrefix (M := M) cka prng fs mo (r + 1)
          (Function.update ks r k_fs)).startSend ctx P (vp.tcur + 1) vp.γ vp.root rOpt').run s)) := by
    have hsome : ∀ coins : CCoins,
        _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
          (simulateQ lImpl (((hooksLocalPrefix (M := M) cka prng fs mo r ks).startSend
            ctx P (vp.tcur + 1) vp.γ vp.root (some coins)).run s))
          (fun k_fs => simulateQ lImpl (((hooksLocalPrefix (M := M) cka prng fs mo (r + 1)
            (Function.update ks r k_fs)).startSend ctx P (vp.tcur + 1) vp.γ vp.root (some coins)).run s)) := by
      intro coins
      let c := cka.send vp.γ coins
      have hbind : ∀ r' ks',
          ((hooksLocalPrefix (M := M) cka prng fs mo r' ks').startSend
            ctx P (vp.tcur + 1) vp.γ vp.root (some coins)).run s =
          (((rootLPrefix prng mo r' ks' (vp.tcur + 1) c.2.2 vp.root >>= fun (σ', k, sid) =>
            regSessOf sid >>= fun idx? => pure (σ', k, idx?)) :
              StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (Sig × K × Option ℕ)).run s >>=
            fun (res : (Sig × K × Option ℕ) × LState T Sig K I) =>
              pure (some (c.1, c.2.1, res.1.1, (fs.initSender res.1.2.1, res.1.2.2)),
                ({ cache := Function.update res.2.cache (vp.tcur + 1)
                    (some (c.2.1, res.1.1, res.1.2.1, res.1.2.2)),
                   table := res.2.table,
                   sessions := res.2.sessions,
                   lastIdx := res.2.lastIdx } : LState T Sig K I))) := by
        intro r' ks'; simp [c, hooksLocalPrefix, StateT.run_bind, StateT.run_modify]
      simp only [hbind, simulateQ_bind, simulateQ_pure]
      refine (shiftLe_rootLPrefix_regSessOf prng mo r ks (vp.tcur + 1) c.2.2 vp.root hle hinv).post mo _ ?_
      intro a b hb; simp only [support_pure, Set.mem_singleton_iff] at hb; subst hb; exact ⟨rfl, rfl⟩
    intro rOpt'
    cases rOpt' with
    | some c => exact hsome c
    | none =>
      have hnone : ∀ r' ks',
          ((hooksLocalPrefix (M := M) cka prng fs mo r' ks').startSend
            ctx P (vp.tcur + 1) vp.γ vp.root none).run s =
          ((StateT.lift (sampleT CCoins) : StateT _ _ CCoins).run s >>= fun p =>
            ((hooksLocalPrefix (M := M) cka prng fs mo r' ks').startSend
              ctx P (vp.tcur + 1) vp.γ vp.root (some p.1)).run p.2) := fun _ _ => rfl
      rw [hnone r ks, simulateQ_bind, simulateQ_lImpl_sampleT_run]
      simp only [hnone (r + 1), simulateQ_bind, simulateQ_lImpl_sampleT_run, bind_assoc, pure_bind]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.sample_bind mo ($ᵗ CCoins) fun c _ => hsome c
  unfold _root_.CryptoGames.SM.Engine.vSend
  split_ifs
  · simp only [StateT.run_bind, simulateQ_bind]
    refine (hss rOpt).post mo _ ?_
    intro a b hb
    rcases a with ⟨_ | ⟨γ', T', σ', ss⟩, s_ss⟩ <;>
      simp only [hooksLocalPrefix, pure_bind, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hb <;>
      subst hb <;> exact ⟨rfl, rfl⟩
  · simp only [pure_bind, hooksLocalPrefix]
    cases vp.vS <;>
      simp only [StateT.run_pure, simulateQ_pure] <;>
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv

private theorem shiftLe_vRecv_prefix {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (r : ℕ) (ks : ℕ → K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (vp : _root_.CryptoGames.SM.Engine.VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (c : Header T × E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    {s : LState T Sig K I}
    (hle : s.sessions.length ≤ r)
    (hinv : _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo s) :
    _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
      (simulateQ lImpl ((_root_.CryptoGames.SM.Engine.vRecv
        (hooksLocalPrefix cka prng fs mo r ks) ctx P vp c rec).run s))
      (fun k_fs => simulateQ lImpl ((_root_.CryptoGames.SM.Engine.vRecv
        (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r k_fs)) ctx P vp c rec).run s)) := by
  have hsr : ∀ Tn : T,
      _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
        (simulateQ lImpl (((hooksLocalPrefix (M := M) cka prng fs mo r ks).startRecv
          ctx P c.1.1 vp.γ vp.root Tn).run s))
        (fun k_fs => simulateQ lImpl (((hooksLocalPrefix (M := M) cka prng fs mo (r + 1)
          (Function.update ks r k_fs)).startRecv ctx P c.1.1 vp.γ vp.root Tn).run s)) := by
    intro Tn
    have hbranch :
        _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r Prod.snd
          (simulateQ lImpl ((if mo.auth && decide (c.1.1 = mo.tStar) then
            if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
            else do
              let kk := cka.receive vp.γ Tn
              let k' ← lookupFLPrefix r ks kk.2
              let idx ← regSess kk.2
              return some (some (kk.1, (prng.up vp.root kk.2).1, (fs.initReceiver k', some idx)))
          else pure (some none) :
            StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) _).run s))
          (fun k_fs => simulateQ lImpl ((if mo.auth && decide (c.1.1 = mo.tStar) then
            if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
            else do
              let kk := cka.receive vp.γ Tn
              let k' ← lookupFLPrefix (r + 1) (Function.update ks r k_fs) kk.2
              let idx ← regSess kk.2
              return some (some (kk.1, (prng.up vp.root kk.2).1, (fs.initReceiver k', some idx)))
          else pure (some none) :
            StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) _).run s)) := by
      split_ifs with h1 h2
      · simp only [StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      · have hnot_th : ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
          intro ⟨ha, hb⟩; simp [ha, hb] at h2
        set kk := cka.receive vp.γ Tn
        have hbind : ∀ r' ks', ((do
            let k' ← lookupFLPrefix r' ks' kk.2
            let idx ← regSess kk.2
            return some (some (kk.1, (prng.up vp.root kk.2).1, (fs.initReceiver k', some idx))) :
              StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) _).run s) =
          (((lookupFLPrefix r' ks' kk.2 >>= fun k' => regSess kk.2 >>= fun idx => pure (k', idx)) :
            StateT (LState T Sig K I) (_root_.CryptoGames.SM.Engine.TComp nilSpec) (K × ℕ)).run s >>= fun res =>
              pure (some (some (kk.1, (prng.up vp.root kk.2).1, (fs.initReceiver res.1.1, some res.1.2))),
                res.2)) := by
          intro r' ks'; simp [StateT.run_bind]
        simp only [hbind, simulateQ_bind, simulateQ_pure]
        refine (shiftLe_lookupFLPrefix_regSess mo r ks kk.2 hle hinv hnot_th).post mo _ ?_
        intro a b hb; simp only [support_pure, Set.mem_singleton_iff] at hb; subst hb; exact ⟨rfl, rfl⟩
      · simp only [StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    simp only [hooksLocalPrefix, StateT.run_bind, StateT.run_get, pure_bind]
    cases s.cache c.1.1 with
    | none => exact hbranch
    | some val =>
      rcases val with ⟨Tc, σc, k, idx?⟩
      by_cases hTc : Tc = Tn
      · simp only [hTc, ↓reduceIte, StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      · simp only [hTc, ↓reduceIte]; exact hbranch
  unfold _root_.CryptoGames.SM.Engine.vRecv; dsimp only
  split_ifs
  · simp only [StateT.run_pure, simulateQ_pure]
    exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
  · cases c.1.2 with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    | some Tn =>
      simp only [StateT.run_bind, simulateQ_bind]
      refine (hsr Tn).post mo _ ?_
      intro a b hb
      rcases a with ⟨_ | (_ | ⟨γ', σ', rs⟩), s_sr⟩
      · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
      · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
      · simp only [hooksLocalPrefix, pure_bind, Function.update_self] at hb
        cases hfs : fs.receive rs.1 c.1 c.2 with
        | none =>
          simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
        | some out =>
          rcases out with ⟨rs', i, m⟩
          simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
  · simp only [pure_bind, hooksLocalPrefix]
    cases vp.vR c.1.1 with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    | some v0 =>
      dsimp only
      cases hfs : fs.receive v0.1 c.1 c.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      | some out =>
        rcases out with ⟨rs', i, m⟩
        simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv

private theorem shiftLe_stepLPrefix {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (r : ℕ) (ks : ℕ → K)
    (qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ r)
    (hinv : _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo esL.h) :
    _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe mo r (fun z => z.2.h)
      (simulateQ lImpl ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL))
      (fun k_fs => simulateQ lImpl ((implEDFShiftedPaper l
        (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r k_fs))
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)) := by
  rcases qry with n | (((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩)
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, _root_.CryptoGames.SM.Engine.coinsE]
    dsimp only [StateT.lift, StateT.run]
    simp only [lImpl, simulateQ_bind,
      simulateQ_pure]
    refine _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.of_eq mo (fun _ => rfl) ?_
    intro z hz
    rw [mem_support_bind_iff] at hz; obtain ⟨_, _, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    exact ⟨hle, hinv⟩
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      _root_.CryptoGames.SM.Engine.transmitE, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    · cases esL.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      | some s₁ =>
        dsimp only
        split
        · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
            pure_bind, StateT.run_pure, simulateQ_pure]
          exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind]
          refine (shiftLe_vSend_prefix cka prng fs mo r ks s₁ P (s₁.st P) m none r_c hle hinv).post mo _ ?_
          intro a b hb
          rcases a with ⟨_ | ⟨st', c_out⟩, h'⟩ <;>
            simp only [_root_.CryptoGames.SM.Engine.abortE, pure_bind, StateT.run_bind,
              StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb <;>
            subst hb <;> exact ⟨rfl, rfl⟩
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      _root_.CryptoGames.SM.Engine.challE, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    · cases esL.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      | some s₁ =>
        dsimp only
        split
        · simp only [StateT.run_pure, simulateQ_pure]
          exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
        · split
          · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
              pure_bind, StateT.run_pure, simulateQ_pure]
            exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
          · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind]
            refine (shiftLe_vSend_prefix cka prng fs mo r ks s₁ P (s₁.st P) _ (some (m₀, m₁)) r_c hle hinv).post mo _ ?_
            intro a b hb
            rcases a with ⟨_ | ⟨st', c_out⟩, h'⟩ <;>
              simp only [_root_.CryptoGames.SM.Engine.abortE, pure_bind, StateT.run_bind,
                StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb <;>
              subst hb <;> exact ⟨rfl, rfl⟩
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      _root_.CryptoGames.SM.Engine.deliverE, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    · cases esL.g.inTransit P.other c with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      | some rec =>
        dsimp only
        simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind]
        refine (shiftLe_vRecv_prefix cka prng fs mo r ks esL.g P (esL.g.st P) c (some rec) hle hinv).post mo _ ?_
        intro a b hb
        rcases a with ⟨_ | (_ | ⟨st', t', i', m'⟩), h'⟩
        · simp only [_root_.CryptoGames.SM.Engine.abortE, pure_bind, StateT.run_bind,
            StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
        · simp only [] at hb
          split at hb <;>
            simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb <;>
            subst hb <;> exact ⟨rfl, rfl⟩
        · simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix, pure_bind,
            StateT.run_bind, liftH_run, StateT.run_pure, StateT.run_modify, bind_assoc,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
          rcases hb with rfl; exact ⟨rfl, rfl⟩
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      _root_.CryptoGames.SM.Engine.injectE, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind]
      refine (shiftLe_vRecv_prefix cka prng fs mo r ks esL.g P (esL.g.st P) c none hle hinv).post mo _ ?_
      intro a b hb
      rcases a with ⟨_ | (_ | ⟨st', t', i', m'⟩), h'⟩
      · simp only [_root_.CryptoGames.SM.Engine.abortE, pure_bind, StateT.run_bind,
          StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
      · simp only [] at hb
        split at hb
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
        · split at hb
          · simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix, StateT.run_bind,
              liftH_run, StateT.run_pure, StateT.run_modify, bind_assoc, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          · split at hb <;>
              simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb <;>
              subst hb <;> exact ⟨rfl, rfl⟩
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      _root_.CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper,
      StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    · split
      · simp only [_root_.CryptoGames.SM.Engine.abortE, StateT.run_bind, StateT.run_modify,
          pure_bind, StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      · simp only [hooksLocalPrefix, StateT.run_bind, liftH_run, StateT.run_pure, StateT.run_modify,
          pure_bind, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr,
      _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeE,
      StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
    · cases esL.g.inTransit P.other c₁ with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
      | some rec =>
        dsimp only
        split
        · simp only [StateT.run_pure, simulateQ_pure]
          exact _root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.pure mo _ hle hinv
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind]
          refine (shiftLe_vRecv_prefix cka prng fs mo r ks esL.g P
            (esL.g.st P) c₂ none hle hinv).post mo _ ?_
          intro a b hb
          rcases a with ⟨_ | (_ | ⟨st', t', i', m'⟩), h'⟩
          · simp only [_root_.CryptoGames.SM.Engine.abortE, pure_bind, StateT.run_bind,
              StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          · simp only [] at hb
            split at hb
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
            · split at hb
              · simp only [_root_.CryptoGames.SM.Engine.commitE, hooksLocalPrefix, StateT.run_bind,
                  liftH_run, StateT.run_pure, StateT.run_modify, bind_assoc, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
                subst hb; exact ⟨rfl, rfl⟩
              · split at hb <;>
                  simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb <;>
                  subst hb <;> exact ⟨rfl, rfl⟩

private theorem evalDist_runLocPrefix_le_succ {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (r : ℕ) (ks : ℕ → K)
    (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ r)
    (hinv : _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo esL.h) :
    𝒟[simulateQ lImpl ((simulateQ (implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)] {true} ≤
    𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
      simulateQ lImpl ((simulateQ (implEDFShiftedPaper l
        (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r k_fs))
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b =>
    simp
  | query_bind qry cont ih =>
    simp only [simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_bind, bind_assoc]
    refine shiftLe_stepLPrefix cka prng fs Δcka qep l mo r ks qry hle hinv
      (fun z => simulateQ lImpl ((simulateQ (implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) (cont z.1)).run z.2) >>=
        fun w => pure (authOut (2 + Δcka) mo.policy w.2))
      (fun k_fs z => simulateQ lImpl ((simulateQ (implEDFShiftedPaper l
        (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r k_fs))
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) (cont z.1)).run z.2) >>=
        fun w => pure (authOut (2 + Δcka) mo.policy w.2))
      (fun z hlt k_fs => (evalDist_runLocPrefix_eq_of_lt cka prng fs Δcka qep l mo r ks k_fs (cont z.1) z.2 hlt).le)
      (fun z hle' hinv' => ih z.1 hle' hinv')

private theorem localAuthPrefix_step_le {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l t r : ℕ)
    (ht0 : 0 < t) (ks : ℕ → K)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthPrefix cka prng fs lam Δcka qep l (some (l - 1)) t r ks A] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun v =>
          localAuthPrefix cka prng fs lam Δcka qep l (some (l - 1)) t (r + 1) (Function.update ks r v) A]
        {true} := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  have ht_ne : (0 : ℕ) ≠ mo.tStar := Nat.ne_of_lt ht0
  have htH_ne : (0 : ℕ) ≠ mo.tH := by
    simp [mo, Mode.tH, _root_.CryptoGames.SM.Construction.healEpoch]
  have hinit_supp : ∀ z ∈ support (simulateQ lImpl ((initLocal cka prng fs lam mo).run ({} : LState T Sig K I))),
      z.2.sessions.length ≤ r ∧ _root_.CryptoGames.SM.Construction.AuthL11.TabSessInv mo z.2 := by
    intro z hz
    unfold initLocal rootL regSessOf at hz
    have hgt_f : ¬ (mo.tStar < 0) := Nat.not_lt_zero _
    simp only [hgt_f, ht_ne, htH_ne, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind, simulateQ_lImpl_sampleT_run,
      simulateQ_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, _, _, _, rfl⟩ := hz
    exact ⟨Nat.zero_le r, fun _ _ => rfl⟩
  dsimp only [localAuthPrefix]
  refine (_root_.CryptoGames.SM.Construction.AuthL11.ShiftLe.of_eq (K := K) mo (j := r)
      (getH := Prod.snd)
      (mL := simulateQ lImpl ((initLocal cka prng fs lam mo).run ({} : LState T Sig K I)))
      (mF := fun _ => simulateQ lImpl ((initLocal cka prng fs lam mo).run ({} : LState T Sig K I)))
      (fun _ => rfl) hinit_supp)
    (fun z => match z.1 with
      | none => pure false
      | some (vA, vB) =>
        simulateQ lImpl ((simulateQ (implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo r ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) A).run
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := z.2 }) >>=
          fun w => pure (authOut (2 + Δcka) mo.policy w.2))
    (fun v z => match z.1 with
      | none => pure false
      | some (vA, vB) =>
        simulateQ lImpl ((simulateQ (implEDFShiftedPaper l
          (hooksLocalPrefix cka prng fs mo (r + 1) (Function.update ks r v))
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) A).run
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := z.2 }) >>=
          fun w => pure (authOut (2 + Δcka) mo.policy w.2))
    ?_ ?_
  · rintro ⟨_ | ⟨vA, vB⟩, h⟩ hlt v
    · exact le_rfl
    · exact (evalDist_runLocPrefix_eq_of_lt cka prng fs Δcka qep l mo r ks v A _ hlt).le
  · rintro ⟨_ | ⟨vA, vB⟩, h⟩ hle hinv
    · simp
    · exact evalDist_runLocPrefix_le_succ cka prng fs Δcka qep l mo r ks A hle hinv

private theorem localAuthDFShiftedPaper_le_sampleVec {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (k0 : K) (Δcka qep l t : ℕ)
    (ht0 : 0 < t)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (m : ℕ) :
    𝒟[localAuthDFShiftedPaper cka prng fs lam Δcka qep l (some (l - 1)) t A] {true} ≤
      𝒟[sampleVec ($ᵗ K : ProbComp K) k0 m >>= fun ks =>
          localAuthPrefix cka prng fs lam Δcka qep l (some (l - 1)) t m ks A] {true} := by
  induction m with
  | zero =>
    simp only [sampleVec, pure_bind, localAuthPrefix, hooksLocalPrefix_zero_eq,
      localAuthDFShiftedPaper, _root_.CryptoGames.SM.Construction.DeliverForge.runLocDFShiftedPaper]
    exact le_rfl
  | succ m ih =>
    refine ih.trans ?_
    simp only [sampleVec, bind_assoc, pure_bind]
    exact evalDist_bind_mono _ _ _ fun ks _ =>
      localAuthPrefix_step_le cka prng fs lam Δcka qep l t m ht0 ks A

end PrefixKeying
section ShortHorizon
open _root_.CryptoGames.SM.Construction.AuthL11 (hooksLocal evalDist_bind_eq_zero)
open _root_.CryptoGames.SM.Construction.DeliverForge (runLocDFShiftedPaper)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState ReceiveResult
  withPub fromAEADPRG transmitQuery corruptSenderQuery deliverQuery injectQuery pubRedImpl
  transmitImpl corruptSenderImpl deliverImpl injectImpl)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt HState DG SpecialOps hp hInit
  transmitHWith corruptSenderH deliverH injectH)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (WFSeed SyncRM SyncRML syncRML_init mkRState keyAt
  transmit_syncRM transmit_syncRML corruptSender_syncRM
  inject_syncRM_of_not_lookahead inject_syncRML_of_not_lookahead
  injectH_run_of_wfSeed_not_lookahead deliverH_run_of_wfSeed isCompromised_of_wfState_lt
  isCompromised_of_corr_lt_sent transmitH_run_of_wfSeed)
open _root_.CryptoGames.FSAEAD.Thm5On (InTransitOk inTransitOk_hInit inTransitOk_of_transmitH
  inTransitOk_of_corruptSenderH deliver_syncRM_on deliver_syncRML_on
  inTransitOk_of_injectH_not_lookahead inTransitOk_of_injectH_lookahead_none pure_eq_iff)
open _root_.CryptoGames.LibsignalSession (SignalMessageProtoCodec SignalRoundTripShort rustLenBound)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 lIdeal lAead lAeadR
  lChainPRG lPubOf)
open _root_.CryptoGames.LibsignalSM.Proofs.ProstMsgAeadCorrect (lAeadR_correctOn_short_proof
  lPubOf_enc_short_proof)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec)
open _root_.CryptoGames.SM (GameState Config)
open _root_.CryptoGames.SM.Engine (EState VP Hooks HM challE transmitE deliverE injectE
  commitE abortE authOut liftH vRecv)
open _root_.CryptoGames.SM.Construction (FSMultiBook FSMultiSpec Mode mkParties initFSMultiRaw
  rootFSMulti regSessOptMulti sampleT)
open _root_.CryptoGames.SM.Construction.DeliverForge (specDF deliverForgeE corrEShiftedPaper
  afterCorrShifted implEDFShiftedPaper runLocDFShiftedPaper)
private theorem challE_auth_dir1_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep : ℕ) (tL : Option ℕ) (t : ℕ) (P : Party) (m₀ m₁ : M) (rc : Option CCoins)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (challE hk Δ qep (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy (P, m₀, m₁, rc)).run es =
      pure (none, es) := by
  unfold challE
  dsimp only [Mode.cfg, Config.auth]
  simp only [Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp
  · cases es.g.epMgmt Δ qep P rc.isSome <;> simp

private theorem epMgmt_win_eq {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : g.epMgmt Δ qep P bad = some s₁) :
    s₁.win = g.win := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> cases h <;> simp [GameState.leak]

private theorem stepLoc_preserves_win_false_of_qep_lt
    {Γ T I Sig K SS RS M CCoins E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec
      (_root_.CryptoGames.SM.Construction.AuthL11.LState T Sig K I) Γ T Sig SS RS M E CCoins
      Γ Sig (SS × Option ℕ) (RS × Option ℕ))
    (Δ qep maxSkip l : ℕ) (tL : Option ℕ) (t : ℕ) (hqep_lt : qep + 1 < t)
    (qry : (unifSpec + specDF (_root_.CryptoGames.SM.Construction.PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : _root_.CryptoGames.SM.Construction.AuthL11.EStateL Γ T Sig SS RS M E K I)
    (hwin : es.g.win = false) :
    let mo : Mode := ⟨true, tL, t⟩
    ∀ z ∈ support (simulateQ lImpl
      ((implEDFShiftedPaper l hk Δ qep maxSkip mo.cfg mo.policy qry).run es)),
      z.2.g.win = false := by
  intro mo z hz
  rcases qry with n | (((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩)
  · have hcoin : (implEDFShiftedPaper l hk Δ qep maxSkip mo.cfg mo.policy (Sum.inl n)).run es =
        (_root_.CryptoGames.SM.Engine.coinsE n).run es := rfl
    rw [hcoin, simulateQ_lImpl_coinsE_run] at hz
    rw [mem_support_bind_iff] at hz; obtain ⟨_, _, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hwin
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      transmitE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · cases hep : es.g.epMgmt Δ qep P r_c.isSome with
      | none =>
        simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      | some s₁ =>
        have hs₁_win : s₁.win = false := (epMgmt_win_eq hep).trans hwin
        simp only [hep] at hz
        split at hz
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind,
            mem_support_bind_iff] at hz
          obtain ⟨⟨_ | ⟨st', c_out⟩, h'⟩, _, hz⟩ := hz <;>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz <;>
            subst hz
          · exact hwin
          · simp [GameState.record, hs₁_win]
  · dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hz
    rw [challE_auth_dir1_run] at hz
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      deliverE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · cases hit : es.g.inTransit P.other c with
      | none =>
        simp only [hit, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      | some r =>
        have hdw : (mo.cfg : Config M).deliverWin = false := rfl
        simp only [hit, StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind,
          mem_support_bind_iff] at hz
        obtain ⟨⟨_ | (_ | ⟨st', t', i', m'⟩), h'⟩, _, hz⟩ := hz
        · simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · dsimp only at hz
          simp only [hdw, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · dsimp only at hz
          simp only [commitE, StateT.run_bind, liftH_run, bind_assoc, pure_bind,
            simulateQ_bind, mem_support_bind_iff] at hz
          obtain ⟨⟨ok, h''⟩, _, hz⟩ := hz
          rcases ok with _ | st''
          · obtain ⟨_, rfl, hz⟩ := hz
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · obtain ⟨_, rfl, hz⟩ := hz
            simp only [hdw, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; simp [GameState.accept, GameState.delete, hwin]
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      injectE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind,
        mem_support_bind_iff] at hz
      obtain ⟨⟨_ | (_ | ⟨st', t', i', m'⟩), h'⟩, _, hz⟩ := hz
      · simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      · dsimp only at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      · dsimp only at hz
        split at hz
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · rename_i hqt
          split at hz
          · simp only [commitE, StateT.run_bind, liftH_run, bind_assoc, pure_bind,
              simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨⟨ok, h''⟩, _, hz⟩ := hz
            rcases ok with _ | st''
            · obtain ⟨_, rfl, hz⟩ := hz
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwin
            · obtain ⟨_, rfl, hz⟩ := hz
              simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; simp [GameState.accept, GameState.delete, hwin]
          · have hinjf : (mo.cfg : Config M).injectFull t' = false := by
              dsimp only [mo, Mode.cfg, Config.auth, Config.injectFull]
              simp only [↓reduceIte, beq_eq_false_iff_ne]; omega
            simp only [hinjf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · split at hz
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind,
          mem_support_bind_iff] at hz
        obtain ⟨⟨_ | st, h'⟩, _, hz⟩ := hz <;>
          simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz <;>
          subst hz
        · exact hwin
        · simp [afterCorrShifted, GameState.leak, hwin]
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr,
      deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · cases hit : es.g.inTransit P.other c₁ with
      | none =>
        simp only [hit, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      | some r =>
        simp only [hit] at hz
        split at hz
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind,
            mem_support_bind_iff] at hz
          obtain ⟨⟨_ | (_ | ⟨st', t', i', m'⟩), h'⟩, _, hz⟩ := hz
          · simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · dsimp only at hz
            simp only [StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · dsimp only at hz
            split at hz
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwin
            · rename_i hqt
              have hle_qep : ¬ qep + 1 < t' := by
                intro hlt; simp [hlt] at hqt
              split at hz
              · simp only [commitE, StateT.run_bind, liftH_run, bind_assoc, pure_bind,
                  simulateQ_bind, mem_support_bind_iff] at hz
                obtain ⟨⟨ok, h''⟩, _, hz⟩ := hz
                rcases ok with _ | st''
                · obtain ⟨_, rfl, hz⟩ := hz
                  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hwin
                · obtain ⟨_, rfl, hz⟩ := hz
                  simp only [StateT.run_bind, StateT.run_modify, pure_bind,
                    StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; simp [GameState.accept, GameState.delete, hwin]
              · have hinjf : (mo.cfg : Config M).injectFull t' = false := by
                  dsimp only [mo, Mode.cfg, Config.auth, Config.injectFull]
                  simp only [↓reduceIte, beq_eq_false_iff_ne]; omega
                simp only [hinjf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hwin

private theorem evalDist_loc_eq_zero_of_qep_lt
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep l : ℕ) (tL : Option ℕ) (t : ℕ) (hqep_lt : qep + 1 < t)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthDFShiftedPaper cka prng fs lam Δcka qep l tL t A] {true} = 0 := by
  let mo : Mode := ⟨true, tL, t⟩
  let hk := hooksLocal cka prng fs mo
  suffices hloop : ∀ (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
      (es : _root_.CryptoGames.SM.Construction.AuthL11.EStateL Γ T Sig SS RS M E K I),
      es.g.win = false →
      𝒟[simulateQ lImpl
        ((simulateQ (implEDFShiftedPaper l hk (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es) >>=
          fun r => pure (authOut (2 + Δcka) mo.policy r.2)] {true} = 0 by
    unfold localAuthDFShiftedPaper runLocDFShiftedPaper
    refine evalDist_bind_eq_zero _ _ fun z _ => ?_
    rcases z with ⟨_ | ⟨vA, vB⟩, h⟩
    · simp
    · exact hloop A { g := { st := fun | .A => vA | .B => vB, b := false }, h := h } rfl
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro es hwin
    simp [authOut, hwin]
  | query_bind qry cont ih =>
    intro es hwin
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, bind_assoc]
    exact evalDist_bind_eq_zero _ _ fun z hz =>
      ih z.1 z.2 (stepLoc_preserves_win_false_of_qep_lt hk (2 + Δcka) qep fs.maxSkip l tL t hqep_lt qry es hwin z hz)
end ShortHorizon
end Sub123Helpers

namespace Sub4Helpers
set_option linter.unusedSectionVars false
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState ReceiveResult
  transmitQuery corruptSenderQuery deliverQuery injectQuery withPub)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt HState hInit hp DG SpecialOps
  transmitHWith corruptSenderH deliverH injectH)
open _root_.CryptoGames.SM (Config GameState Pos Record RecvResult authLosingConditionsAvoided
  healedBy ltOpt)
open _root_.CryptoGames.SM.Engine (Hooks EState Ctx VP Policy abortE commitE liftH
  vSend vRecv transmitE challE deliverE injectE coinsE authOut)
open _root_.CryptoGames.SM.Construction (Header Mode PartyState healEpoch sampleT realParty mkParties
  FSMultiSpec FSMultiBook FSMultiState
  lookupMultiF regSessMulti regSessOptMulti rootFSMulti hooksFSMulti initFSMultiRaw liftFSMulti)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF specDF deliverForgeE afterCorrShifted inTransit_mem_trans
  corrEShiftedPaper implEDFShiftedPaper localAuthDFShiftedPaper)
open _root_.CryptoGames.SM.Construction.AuthL11 (nilSpec lImpl LState EStateL lookupFL regSess
  regSessOf rootL hooksLocal initLocal eraseSt eraseSt_epoch eraseSt_idx eraseSt_tL eraseSt_trans
  eraseSt_chall eraseSt_comp eraseSt_maxAcc eraseSt_b eraseSt_win eraseSt_leaks eraseSt_corrs
  eraseSt_update_st eraseSt_safeCh eraseSt_safeInj eraseSt_inTransit eraseSt_trivial
  eraseSt_record eraseSt_accept eraseSt_leakDoom eraseSt_corrDoom eraseSt_authOK
  eraseSt_corrAllowedPaper epMgmt_sync corrDoom_true_of_ge
  simulateQ_lImpl_run_lift_sampleT evalDist_bind_mono evalDist_bind_eq_zero)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalRoundTripShort
  maxForwardJumps rustLenBound)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  dummyKey lFS lPubOf lIdeal lAeadR lChainPRG)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift multiSessSpec fwd)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec fsImpl)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (
  LeOne leAdd_of_lhs_zero leAdd_of_le_main leAdd_of_la_one
  leOne_of_lhs_zero leOne_bind leOne_bind_dummy_loc
  lFS_initSender_eq lFS_initReceiver_eq lFS_send_eq lFS_receive_eq
  pubFsMultiImpl simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl
  pubFsMultiImpl_inl_run pubFsMultiImpl_transmit_run pubFsMultiImpl_corruptSender_run
  pubFsMultiImpl_deliver_some_run pubFsMultiImpl_inject_none_run pubFsMultiImpl_inject_some_run
  injectL_lookahead_some_accepted)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt (
  authLosingConditionsAvoided_congr SessHSt SessRState ActiveSessInvAt ActiveSessInv
  activeSessInv_init activeSessInv_to_phase2 activeSessInv_matched_iff
  activeSessInv_corruptSender activeSessInv_transmit activeSessInv_deliver
  activeSessInv_inject_phase2 activeSessInv_inject_phase1)

private abbrev DDHSt (Pt : Type) := _root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt

private theorem lFS_receive_eq_none_of_lPubOf_none {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (rs : RatchetReceiverState (BitVec 256) (BitVec 256))
    (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (hpub : lPubOf protoSignalCodec e.2 = none) :
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs h e = none := by
  rw [lFS_receive_eq, hpub]

private theorem activeSessInv_scorr_false {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf true k ssLoc rsLoc bk sM sL) :
    bk.sCorr = false := by
  rcases hinv with ⟨stR, h⟩
  rw [h.bk_corr, (h.syncRML rfl).uncorr]
  rfl

private theorem healedBy_leak_false {St Msg C : Type}
    {s : GameState St Msg C} {Δ t e_lk : ℕ}
    (hf : healedBy s.tL Δ t = false) :
    healedBy (s.leak e_lk).tL Δ t = false := by
  cases htL : s.tL with
  | none => simp [healedBy, htL] at hf
  | some lk =>
    simp only [GameState.leak, healedBy, _root_.CryptoGames.SM.maxOpt, htL, decide_eq_false_iff_not] at hf ⊢
    omega

private theorem healedBy_epMgmt_false {St Msg C : Type}
    {s s₁ : GameState St Msg C} {Δ qep t : ℕ} {P : Party} {bad : Bool}
    (hf : healedBy s.tL Δ t = false) (h : s.epMgmt Δ qep P bad = some s₁) :
    healedBy s₁.tL Δ t = false := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
  · exact healedBy_leak_false hf
  · exact hf
  · exact hf

private theorem healedBy_afterCorrShifted_false {St Msg C : Type}
    {s : GameState St Msg C} {l Δ t : ℕ} (P : Party)
    (hf : healedBy s.tL Δ t = false) :
    healedBy (afterCorrShifted l s P).tL Δ t = false := by
  unfold afterCorrShifted
  exact healedBy_leak_false hf

private theorem healedBy_afterCorrShifted_at_epoch_false {St Msg C : Type}
    {s : GameState St Msg C} {l Δ t : ℕ} {P : Party}
    (hl : l < t) (hΔ : 1 ≤ Δ) (hep : t ≤ s.epoch P) :
    healedBy (afterCorrShifted l s P).tL Δ t = false := by
  have hnot : ¬ (max (s.epoch .A) (s.epoch .B) = l ∧ s.epoch P + 1 ≤ l) := by omega
  have hge : t ≤ max (s.epoch .A) (s.epoch .B) := by
    cases P <;> simp only [le_max_iff] <;> omega
  unfold afterCorrShifted
  simp only [hnot, ↓reduceIte, GameState.leak, healedBy, _root_.CryptoGames.SM.maxOpt,
    decide_eq_false_iff_not]
  cases s.tL <;> simp <;> omega

private theorem healedBy_false_of_safeCh_false {St Msg C : Type}
    {s : GameState St Msg C} {Δ t : ℕ} {P : Party}
    (hep : s.epoch P = t) (hnsafe : s.safeCh Δ P = false) :
    healedBy s.tL Δ t = false := by
  simpa [GameState.safeCh, hep] using hnsafe

private theorem epMgmt_win_eq {St Msg C : Type}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) : s₁.win = s.win := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl

private theorem liftH_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv T Sv SSv RSv M E HS α : Type}
    (x : _root_.CryptoGames.SM.Engine.HM tspec HS α)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem simulateQ_lImpl_sampleT_run {X σ : Type} [SampleableType X] (s : σ) :
    simulateQ lImpl ((StateT.lift (sampleT X) : StateT σ (_root_.CryptoGames.SM.Engine.TComp nilSpec) X).run s) =
      (($ᵗ X : ProbComp X) >>= fun x => pure (x, s)) :=
  simulateQ_lImpl_run_lift_sampleT s

private theorem simulateQ_inl_sampleT_run {κ σ X : Type} [SampleableType X]
    {G : OracleSpec.{0, 0} κ}
    (impl : QueryImpl (unifSpec + G) (StateT σ ProbComp))
    (hInl : ∀ n s, (impl (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (st : σ) :
    (simulateQ impl (sampleT (tspec := G) X)).run st =
      (($ᵗ X : ProbComp X) >>= fun x => pure (x, st)) := by
  unfold sampleT
  induction ($ᵗ X : ProbComp X) using OracleComp.inductionOn generalizing st with
  | pure x => simp
  | query_bind n k ih =>
    change (simulateQ impl
        ((query (spec := unifSpec + G) (.inl n)) >>= fun u =>
          liftComp (k u) (unifSpec + G))).run st =
      ((query (spec := unifSpec) n >>= k) >>= fun x => pure (x, st))
    rw [simulateQ_bind, StateT.run_bind, simulateQ_HasQuery_query, hInl n st]
    simp only [query_eq_liftM, bind_assoc, pure_bind]
    exact congrArg (liftM (OracleSpec.query (spec := unifSpec) n) >>= ·) (funext fun u => ih u st)

private theorem simulateQ_pubFsMulti_sampleT {Pt : Type} {ℓ : ℕ} {σ X : Type} [SampleableType X]
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (st : (ℕ → Bool) × (ℕ → σ)) :
    (simulateQ (pubFsMultiImpl impl)
      (sampleT (tspec := FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) X)).run st =
      (($ᵗ X : ProbComp X) >>= fun x => pure (x, st)) :=
  simulateQ_inl_sampleT_run (pubFsMultiImpl impl) (pubFsMultiImpl_inl_run impl) st

private theorem simulateQ_pubFsMulti_sampleT_run {Pt : Type} {ℓ : ℕ} {σ HS X : Type} [SampleableType X]
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (s : HS) (st : (ℕ → Bool) × (ℕ → σ)) :
    (simulateQ (pubFsMultiImpl impl)
      ((StateT.lift (sampleT (tspec := FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) X)).run s)).run st =
      (($ᵗ X : ProbComp X) >>= fun x => pure ((x, s), st)) := by
  rw [StateT.run_lift, simulateQ_bind, StateT.run_bind, simulateQ_pubFsMulti_sampleT]
  simp

private theorem simulateQ_pubFsMulti_liftFSMulti_run {Pt : Type} {ℓ : ℕ} {σ RSt K I : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (sIdx : ℕ)
    (q_fs : (_root_.CryptoGames.FSAEAD.spec
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)).Domain)
    (s : FSMultiState Pt RSt K I (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σ)) :
    (simulateQ (pubFsMultiImpl impl)
      ((liftFSMulti sIdx
        (query (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec
          (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256))
          (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (ℕ × LibsignalCiphertextWithSalt32)) (.inr q_fs))).run s)).run st =
      ((pubFsMultiImpl impl (.inr ⟨sIdx, q_fs⟩)).run st >>= fun p => pure ((p.1, s), p.2)) := by
  unfold liftFSMulti
  rw [StateT.run_lift, simulateQ_bind, StateT.run_bind]
  change (do
    let a ← (simulateQ (pubFsMultiImpl impl)
      (query (spec := unifSpec + FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (.inr ⟨sIdx, q_fs⟩))).run st
    (simulateQ (pubFsMultiImpl impl) (pure (a.1, s))).run a.2) = _
  rw [simulateQ_HasQuery_query]
  simp

private theorem list_idxOf_append_new {I : Type} [DecidableEq I] {xs : List I} {x : I}
    (hnot : x ∉ xs) : (xs ++ [x]).idxOf x = xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hne : y ≠ x := fun h => hnot (by simp [h])
    have hnot' : x ∉ ys := fun h => hnot (by simp [h])
    simp [hne, ih hnot']

private theorem list_idxOf_append_mem {I : Type} [DecidableEq I] {xs : List I} {x y : I}
    (hmem : y ∈ xs) : (xs ++ [x]).idxOf y = xs.idxOf y := by
  induction xs with
  | nil => cases hmem
  | cons z zs ih =>
    by_cases hzy : z = y
    · subst hzy; simp
    · rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact absurd rfl hzy
      · simp [hzy, ih hmem']

private theorem party_senderOf_sendsIn (ep : ℕ) : (Party.senderOf ep).sendsIn ep = true := by
  unfold Party.senderOf Party.sendsIn
  split_ifs with h <;> simp_all

private theorem party_senderOf_sendsIn_succ (ep : ℕ) :
    (Party.senderOf ep).sendsIn (ep + 1) = false := by
  unfold Party.senderOf Party.sendsIn
  split_ifs with h <;> simp_all <;> omega

private theorem party_senderOf_sendsIn_add_two (ep : ℕ) :
    (Party.senderOf ep).sendsIn (ep + 2) = true := by
  unfold Party.senderOf Party.sendsIn
  split_ifs with h <;> simp_all

private theorem party_eq_senderOf_of_sendsIn {P : Party} {ep : ℕ} (h : P.sendsIn ep = true) :
    P = Party.senderOf ep := by
  cases P <;> unfold Party.senderOf Party.sendsIn at * <;> split_ifs <;> simp_all

private theorem party_eq_receiverOf_of_not_sendsIn {P : Party} {ep : ℕ} (h : P.sendsIn ep = false) :
    P = Party.receiverOf ep := by
  cases P <;> unfold Party.receiverOf Party.senderOf Party.other Party.sendsIn at * <;>
    split_ifs <;> simp_all

/-- Full per-`(ks, bs)` coupling invariant between `esLoc` (`hooksLocalPrefix`),
`esM` + `tblM` (`hooksFSMulti ... false`), and (when `phase1 = true`) `esL` + `tblL` (`hooksFSMulti ... true`). -/
private structure SyncDir1 {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ) : Prop where
  habortL : esLoc.abort = false
  habortM : esM.abort = false
  habortLa : phase1 = true → esL.abort = false
  hwinL : esLoc.g.win = false
  hwinM : esM.g.win = false
  hwinLa : phase1 = true → esL.g.win = false
  hlf : phase1 = true → esM.h.lfWin = false
  heraseM : eraseSt esLoc.g = eraseSt esM.g
  heraseLa : phase1 = true → esL.g = esM.g
  hh_La : phase1 = true → esL.h = esM.h
  hhealed : healedBy esM.g.tL (2 + Δcka) t = phase1
  hginv : ∀ r ∈ esLoc.g.trans, r.ct.1.1 = r.pos.epoch
  hep_st : ∀ P, esLoc.g.epoch P = (esLoc.g.st P).tcur ∧ (esLoc.g.st P).id = P
  hsessM : esM.h.sessions = esLoc.h.sessions
  hsess_nodup : esLoc.h.sessions.Nodup
  hsess_rem : esLoc.h.sessions.length + rem ≤ q
  hsess_tH : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH →
    (esLoc.g.st (Party.senderOf t)).tcur < t → esLoc.h.sessions = []
  htbl_loc : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
    ∀ Ik, esLoc.h.table.lookup Ik =
      if Ik ∈ esLoc.h.sessions then some (ks (esLoc.h.sessions.idxOf Ik)) else none
  htbl_M : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
    ∀ Ik, (esM.h.table.lookup Ik).isSome = decide (Ik ∈ esLoc.h.sessions)
  hcache : ∀ ep, match esLoc.h.cache ep, esM.h.cache ep with
    | none, none => True
    | some (TcL, σL, kL, idxL?), some (TcM, σM, kM, idxM?) =>
      TcL = TcM ∧ σL = σM ∧ idxL? = idxM? ∧
      match idxL? with
      | none => kL = kM ∧ ep ≠ t
      | some sIdx => ep = t ∧ sIdx < esLoc.h.sessions.length ∧ kL = ks sIdx
    | _, _ => False
  hcache_tcur : (esLoc.g.st (Party.senderOf t)).tcur < t → esLoc.h.cache t = none
  hbook_out : ∀ sIdx, esLoc.h.sessions.length ≤ sIdx → esM.h.book sIdx = none
  htbl_out : ∀ sIdx, esLoc.h.sessions.length ≤ sIdx →
    tblM sIdx = hInit (bs sIdx) (.seed (ks sIdx)) ∧
    (phase1 = true → tblL sIdx = hInit (bs sIdx) (.seed (ks sIdx)))
  hstates : ∃ (ssLoc : ℕ → RatchetSenderState (BitVec 256))
      (rsLoc : ℕ → RatchetReceiverState (BitVec 256) (BitVec 256)),
    (∀ sIdx, sIdx < esLoc.h.sessions.length →
      ActiveSessInv C ℓ encT idOf phase1 (ks sIdx) (ssLoc sIdx) (rsLoc sIdx)
        ((esM.h.book sIdx).getD {}) (tblM sIdx) (tblL sIdx)) ∧
    ((esLoc.g.st (Party.senderOf t)).tcur < t → ∀ sIdx, sIdx < esLoc.h.sessions.length →
      ssLoc sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender (ks sIdx)) ∧
    ((esLoc.g.st (Party.receiverOf t)).tcur < t → ∀ sIdx, sIdx < esLoc.h.sessions.length →
      rsLoc sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver (ks sIdx)) ∧
    (∀ P, (esLoc.g.st P).id = (esM.g.st P).id ∧
      (esLoc.g.st P).tcur = (esM.g.st P).tcur ∧
      (esLoc.g.st P).γ = (esM.g.st P).γ ∧
      (esLoc.g.st P).root = (esM.g.st P).root ∧
      (esLoc.g.st P).curCkaMsg = (esM.g.st P).curCkaMsg ∧
      (match (esLoc.g.st P).vS, (esM.g.st P).vS with
       | none, none => True
       | some (ss, none), some (.inl ssM) => ss = ssM
       | some (ss, some sIdx), some (.inr sIdxM) =>
         sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ ss = ssLoc sIdx ∧
         P = Party.senderOf t ∧
         ((esLoc.g.st P).tcur = t ∨ (esLoc.g.st P).tcur = t + 1) ∧
         (∀ Q sIdx', (esM.g.st Q).vS = some (.inr sIdx') → Q = P ∧ sIdx' = sIdx)
       | _, _ => False) ∧
      (∀ ep, match (esLoc.g.st P).vR ep, (esM.g.st P).vR ep with
       | none, none => True
       | some (rs, none), some (.inl rsM) => rs = rsM ∧ ep ≠ t
       | some (rs, some sIdx), some (.inr sIdxM) =>
         ep = t ∧ sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ rs = rsLoc sIdx ∧
         P = Party.receiverOf t ∧ t ≤ (esLoc.g.st P).tcur
       | _, _ => False))

private theorem initLocal_lImpl_run {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (l t : ℕ) (ht0 : 0 < t) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    simulateQ lImpl ((initLocal cka prng fs lam mo).run ({} : LState Pt (BitVec 256) (BitVec 256) Pt)) =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kr =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kc =>
          let p := prng.up (prng.init kr) lam
          let pLoc := mkParties (T := Pt) (cka.initA kc) (cka.initB kc) p.1
            (fs.initSender p.2, (none : Option ℕ)) (fs.initReceiver p.2, (none : Option ℕ))
          pure (some pLoc, ({} : LState Pt (BitVec 256) (BitVec 256) Pt))) := by
  intro cka prng fs mo
  have ht_ne : (0 : ℕ) ≠ mo.tStar := Nat.ne_of_lt ht0
  have htH_ne : (0 : ℕ) ≠ mo.tH := by simp [mo, Mode.tH, healEpoch]
  have hgt_f : ¬ (mo.tStar < 0) := Nat.not_lt_zero _
  unfold initLocal rootL regSessOf
  simp only [hgt_f, ht_ne, htH_ne, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_lImpl_sampleT_run, simulateQ_pure]

private theorem initFSMultiRaw_pubFsMulti_run {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {σ : Type}
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (l t : ℕ) (ht0 : 0 < t)
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (st : (ℕ → Bool) × (ℕ → σ)) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    (simulateQ (pubFsMultiImpl impl)
      (initFSMultiRaw (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32) cka prng fs lam mo false)).run st =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kr =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun kc =>
          let p := prng.up (prng.init kr) lam
          let pM := mkParties (T := Pt) (cka.initA kc) (cka.initB kc) p.1
            (Sum.inl (fs.initSender p.2) : RatchetSenderState (BitVec 256) ⊕ ℕ)
            (Sum.inl (fs.initReceiver p.2) : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
          pure ({ g := { st := fun P => match P with | .A => pM.1 | .B => pM.2, b := false },
                  h := ({} : FSMultiState Pt (BitVec 256) (BitVec 256) Pt
                    (ℕ × LibsignalCiphertextWithSalt32)) }, st)) := by
  intro cka prng fs mo
  have ht_ne : (0 : ℕ) ≠ mo.tStar := Nat.ne_of_lt ht0
  have htH_ne : (0 : ℕ) ≠ mo.tH := by simp [mo, Mode.tH, healEpoch]
  have hgt_f : ¬ (mo.tStar < 0) := Nat.not_lt_zero _
  unfold initFSMultiRaw rootFSMulti regSessOptMulti
  simp only [hgt_f, ht_ne, htH_ne, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_pubFsMulti_sampleT, simulateQ_pure]
  rfl

private theorem syncDir1_init_state {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (q Δcka l t : ℕ) (ht2 : 2 ≤ t)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (kr kc : BitVec 256) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let p := prng.up (prng.init kr) lam
    let pLoc := mkParties (T := Pt) (cka.initA kc) (cka.initB kc) p.1
      (fs.initSender p.2, (none : Option ℕ)) (fs.initReceiver p.2, (none : Option ℕ))
    let pM := mkParties (T := Pt) (cka.initA kc) (cka.initB kc) p.1
      (Sum.inl (fs.initSender p.2) : RatchetSenderState (BitVec 256) ⊕ ℕ)
      (Sum.inl (fs.initReceiver p.2) : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    let esLoc : EState _ (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt) :=
      { g := { st := fun P => match P with | .A => pLoc.1 | .B => pLoc.2, b := false }, h := {} }
    let esM : EState _ (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)) :=
      { g := { st := fun P => match P with | .A => pM.1 | .B => pM.2, b := false }, h := {} }
    let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
    SyncDir1 C ℓ encT idOf q Δcka l t ks bs true q esLoc esM esM tbl0 tbl0 := by
  intro cka prng fs p pLoc pM esLoc esM tbl0
  refine
    { habortL := rfl
      habortM := rfl
      habortLa := fun _ => rfl
      hwinL := rfl
      hwinM := rfl
      hwinLa := fun _ => rfl
      hlf := fun _ => rfl
      heraseM := rfl
      heraseLa := fun _ => rfl
      hh_La := fun _ => rfl
      hhealed := rfl
      hginv := by intro r hr; cases hr
      hep_st := by intro P; cases P <;> simp [esLoc, pLoc, mkParties]
      hsessM := rfl
      hsess_nodup := List.nodup_nil
      hsess_rem := by simp [esLoc]
      hsess_tH := fun _ _ => rfl
      htbl_loc := fun _ _ => rfl
      htbl_M := fun _ _ => rfl
      hcache := fun _ => by show True; trivial
      hcache_tcur := fun _ => rfl
      hbook_out := fun _ _ => rfl
      htbl_out := fun _ _ => ⟨rfl, fun _ => rfl⟩
      hstates := ⟨fun i => fs.initSender (ks i), fun i => fs.initReceiver (ks i),
        fun sIdx hs => by simp [esLoc] at hs,
        fun _ _ _ => rfl,
        fun _ _ _ => rfl,
        fun P => by
          cases P <;> simp only [esLoc, esM, pLoc, pM, mkParties, true_and]
          · intro ep
            by_cases hep0 : ep = 0
            · subst hep0; simp; omega
            · simp [hep0]
          · intro _; trivial⟩ }

private theorem lookupFLPrefix_regSess_run {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (q : ℕ) (ks : ℕ → BitVec 256) (Ik : Pt)
    (hLoc : LState Pt (BitVec 256) (BitVec 256) Pt)
    (htbl : ∀ Ik', hLoc.table.lookup Ik' =
      if Ik' ∈ hLoc.sessions then some (ks (hLoc.sessions.idxOf Ik')) else none)
    (hlen : hLoc.sessions.length < q) :
    simulateQ lImpl (((lookupFLPrefix q ks Ik >>= fun k =>
        regSess (T := Pt) (Sig := BitVec 256) (K := BitVec 256) Ik >>= fun idx =>
          pure (k, idx))).run hLoc) =
      if Ik ∈ hLoc.sessions then
        pure ((ks (hLoc.sessions.idxOf Ik), hLoc.sessions.idxOf Ik), hLoc)
      else
        (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun _ =>
          pure ((ks hLoc.sessions.length, hLoc.sessions.length),
            { hLoc with table := (Ik, ks hLoc.sessions.length) :: hLoc.table,
                        sessions := hLoc.sessions ++ [Ik] })) := by
  by_cases hmem : Ik ∈ hLoc.sessions
  · have hlk : hLoc.table.lookup Ik = some (ks (hLoc.sessions.idxOf Ik)) := by rw [htbl]; simp [hmem]
    simp [lookupFLPrefix, regSess, hlk, hmem]
  · have hlk : hLoc.table.lookup Ik = none := by rw [htbl]; simp [hmem]
    simp [lookupFLPrefix, regSess, hlk, hmem, hlen]

private theorem lookupMultiF_regSessMulti_run {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (Ik : Pt)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σ))
    (htbl : ∀ Ik', (hM.table.lookup Ik').isSome = decide (Ik' ∈ hM.sessions)) :
    (simulateQ (pubFsMultiImpl impl) (((lookupMultiF
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        (Sig := BitVec 256) (K := BitVec 256) Ik >>= fun _ =>
        regSessMulti Ik)).run hM)).run st =
      if Ik ∈ hM.sessions then
        pure ((hM.sessions.idxOf Ik, hM), st)
      else
        (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun k_draw =>
          pure ((hM.sessions.length,
            { hM with table := (Ik, k_draw) :: hM.table,
                      sessions := hM.sessions ++ [Ik] }), st)) := by
  by_cases hmem : Ik ∈ hM.sessions
  · have his : (hM.table.lookup Ik).isSome = true := by rw [htbl]; simp [hmem]
    cases hlk : hM.table.lookup Ik with
    | none => rw [hlk] at his; cases his
    | some k0 => simp [lookupMultiF, regSessMulti, hlk, hmem]
  · have his : (hM.table.lookup Ik).isSome = false := by rw [htbl]; simp [hmem]
    have hlk : hM.table.lookup Ik = none := Option.not_isSome_iff_eq_none.mp (by simp [his])
    unfold lookupMultiF regSessMulti
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hlk]
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_pubFsMulti_sampleT_run]
    simp [hmem]

private theorem simulateQ_lImpl_coinsE_run {Γv T Sv SSv RSv M E HS : Type}
    (n : ℕ) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    simulateQ lImpl ((coinsE n).run es) =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, es)) := by
  dsimp only [coinsE, StateT.lift, StateT.run]
  simp [lImpl, QueryImpl.add_apply_inl, QueryImpl.id'_apply]

private theorem simulateQ_pubFsMulti_coinsE_run {Pt : Type} {ℓ : ℕ} {σ Γv Sv SSv RSv HS : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (n : ℕ)
    (es : EState (VP Γv Pt Sv SSv RSv) (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (st : (ℕ → Bool) × (ℕ → σ)) :
    (simulateQ (pubFsMultiImpl impl)
      ((coinsE (tspec := FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) n).run es)).run st =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure ((u, es), st)) := by
  dsimp only [coinsE]
  rw [StateT.run_lift, simulateQ_bind, StateT.run_bind]
  change (do
    let a ← (simulateQ (pubFsMultiImpl impl)
      (query (spec := unifSpec + FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) (.inl n))).run st
    (simulateQ (pubFsMultiImpl impl) (pure (a.1, es))).run a.2) = _
  rw [simulateQ_HasQuery_query, pubFsMultiImpl_inl_run]
  simp

private theorem evalDist_pubFsMulti_true_eq_one_of_abort_lfWin
    {KC Γ CCoins Pt I KR RSt σ : Type} {ℓ : ℕ}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (fs : FSAEADScheme (BitVec 256)
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka qep l t : ℕ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT σ ProbComp))
    (oa : SchemeAdversaryDF Γ Pt RSt
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (esL : EState
      (VP Γ Pt RSt
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32)))
    (st : (ℕ → Bool) × (ℕ → σ))
    (habort : esL.abort = true) (hlf : esL.h.lfWin = true) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let inner := (simulateQ (implEDFShiftedPaper l
      (hooksFSMulti cka prng fs Δcka mo false true)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL >>=
      fun z => pure z.2.h.lfWin
    𝒟[Prod.fst <$> (simulateQ (pubFsMultiImpl impl) inner).run st] {true} = 1 := by
  intro mo
  dsimp only
  induction oa using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp [hlf]
  | query_bind qry cont ih =>
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, map_bind]
    rcases qry with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inl]
      rw [simulateQ_pubFsMulti_coinsE_run]
      simp only [bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
      trans ∫⁻ (_ : Fin (n + 1)), (1 : ℝ≥0∞) ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))]
      · exact MeasureTheory.lintegral_congr fun u => by
          simpa only [implEDFShiftedPaper, StateT.run_bind, StateT.run_pure, simulateQ_bind,
            simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind] using ih u st
      · rw [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
    all_goals
      simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        transmitE, challE, deliverE, injectE, corrEShiftedPaper, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, habort, Bool.true_or, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      simpa only [implEDFShiftedPaper, StateT.run_bind, StateT.run_pure, simulateQ_bind,
        simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind] using ih none st

private theorem evalDist_loc_eq_pure_of_win
    {Γ T I Sig K SS RS M CCoins E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (hks : Hooks nilSpec (LState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig (SS × Option ℕ) (RS × Option ℕ))
    (Δcka qep maxSkip l t : ℕ)
    (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (esLoc : EState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) (LState T Sig K I))
    (hwin : esLoc.g.win = true) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let run := simulateQ lImpl
      ((simulateQ (implEDFShiftedPaper l hks (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run esLoc) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)
    𝒟[run] {true} = 𝒟[(pure (authOut (2 + Δcka) mo.policy esLoc) : ProbComp Bool)] {true} := by
  intro mo
  dsimp only
  induction oa using OracleComp.inductionOn with
  | pure b =>
    simp
  | query_bind qry cont ih =>
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, simulateQ_bind, bind_assoc]
    rcases qry with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inl]
      rw [simulateQ_lImpl_coinsE_run]
      simp only [bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
      trans ∫⁻ (_ : Fin (n + 1)), 𝒟[(pure (authOut (2 + Δcka) mo.policy esLoc) : ProbComp Bool)] {true}
          ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))]
      · exact MeasureTheory.lintegral_congr fun u => by
          simpa only [implEDFShiftedPaper, StateT.run_bind, StateT.run_pure, simulateQ_bind,
            simulateQ_pure, bind_assoc, pure_bind] using ih u
      · rw [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
    all_goals
      simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        transmitE, challE, deliverE, injectE, corrEShiftedPaper, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.or_true, Bool.true_or, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      simpa only [implEDFShiftedPaper, StateT.run_bind, StateT.run_pure, simulateQ_bind,
        simulateQ_pure, bind_assoc, pure_bind] using ih none

private theorem evalDist_pubFsMulti_false_eq_pure_of_win
    {KC Γ CCoins Pt I KR RSt σ : Type} {ℓ : ℕ}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (fs : FSAEADScheme (BitVec 256)
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka qep l t : ℕ)
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT σ ProbComp))
    (oa : SchemeAdversaryDF Γ Pt RSt
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (esM : EState
      (VP Γ Pt RSt
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32)))
    (st : (ℕ → Bool) × (ℕ → σ))
    (hwin : esM.g.win = true) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let inner := (simulateQ (implEDFShiftedPaper l
      (hooksFSMulti cka prng fs Δcka mo false false)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esM >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)
    𝒟[Prod.fst <$> (simulateQ (pubFsMultiImpl impl) inner).run st] {true} =
      𝒟[(pure (authOut (2 + Δcka) mo.policy esM) : ProbComp Bool)] {true} := by
  intro mo
  dsimp only
  induction oa using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp
  | query_bind qry cont ih =>
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, map_bind]
    rcases qry with n | (((((⟨P, m, rc⟩ | ⟨P, m₀, m₁, rc⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inl]
      rw [simulateQ_pubFsMulti_coinsE_run]
      simp only [bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
      trans ∫⁻ (_ : Fin (n + 1)), 𝒟[(pure (authOut (2 + Δcka) mo.policy esM) : ProbComp Bool)] {true}
          ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))]
      · exact MeasureTheory.lintegral_congr fun u => by
          simpa only [implEDFShiftedPaper, StateT.run_bind, StateT.run_pure, simulateQ_bind,
            simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind] using ih u st
      · rw [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
    all_goals
      simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        transmitE, challE, deliverE, injectE, corrEShiftedPaper, deliverForgeE,
        StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.or_true, Bool.true_or, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      simpa only [implEDFShiftedPaper, StateT.run_bind, StateT.run_pure, simulateQ_bind,
        simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind] using ih none st

private theorem leAdd_both_win_terminal
    {KC Γ CCoins Pt I KR RSt σ : Type} {ℓ : ℕ}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (fs : FSAEADScheme (BitVec 256)
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka qep l t : ℕ)
    (hks : Hooks nilSpec (LState Pt RSt (BitVec 256) I)
      Γ Pt RSt
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γ RSt
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT σ ProbComp))
    (oa : SchemeAdversaryDF Γ Pt RSt
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (esLoc : EState
      (VP Γ Pt RSt
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt RSt (BitVec 256) I))
    (esM : EState
      (VP Γ Pt RSt
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32)))
    (stM : (ℕ → Bool) × (ℕ → σ)) (cL : ProbComp Bool)
    (hwinL : esLoc.g.win = true) (hwinM : esM.g.win = true)
    (hout : authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esLoc =
      authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esM) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let cLoc := simulateQ lImpl
      ((simulateQ (implEDFShiftedPaper l hks (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esLoc) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)
    let innerM := (simulateQ (implEDFShiftedPaper l
      (hooksFSMulti cka prng fs Δcka mo false false)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esM >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)
    LeAdd cLoc (Prod.fst <$> (simulateQ (pubFsMultiImpl impl) innerM).run stM) cL := by
  intro mo
  dsimp only
  refine leAdd_of_le_main ?_
  unfold LeOne
  rw [evalDist_loc_eq_pure_of_win hks Δcka qep fs.maxSkip l t oa esLoc hwinL,
    evalDist_pubFsMulti_false_eq_pure_of_win cka prng fs Δcka qep l t impl oa esM stM hwinM,
    hout]

private def LocDead {VPt M C HS : Type} (l t : ℕ) (es : EState VPt M C HS) : Prop :=
  es.abort = true ∨ ∃ lk ∈ es.g.leaks, ltOpt (some (l - 1)) lk = true ∧ lk < t

private theorem authOut_eq_false_of_locDead {VPt M C HS : Type} [DecidableEq M]
    (Δ l t : ℕ) (es : EState VPt M C HS) (hdead : LocDead l t es) :
    authOut Δ (⟨true, some (l - 1), t⟩ : Mode).policy es = false := by
  rcases hdead with hab | ⟨lk, hmem, hgt, hlt⟩
  · simp [authOut, hab]
  · have hall : (es.g.leaks.all fun x => !(ltOpt (some (l - 1)) x && decide (x < t))) = false := by
      rw [Bool.eq_false_iff]
      intro hall'
      have hx := List.all_eq_true.mp hall' lk hmem
      simp [hgt, hlt] at hx
    unfold authOut Mode.policy authLosingConditionsAvoided
    rw [hall]
    simp

private theorem epMgmt_mem_leaks {St Msg C : Type} {s s₁ : GameState St Msg C}
    {Δ qep lk : ℕ} {P : Party} {fl : Bool}
    (hmem : lk ∈ s.leaks) (h : s.epMgmt Δ qep P fl = some s₁) :
    lk ∈ s₁.leaks := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
    simp [GameState.leak, hmem]

private theorem stepLoc_preserves_locDead
    {Γ T Sig SS RS M CCoins E HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hks : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γ Sig (SS × Option ℕ) (RS × Option ℕ))
    (Δcka qep maxSkip l t : ℕ)
    (qry : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) HS)
    (hdead : LocDead l t es) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    ∀ z ∈ support (simulateQ lImpl
      ((implEDFShiftedPaper l hks (2 + Δcka) qep maxSkip mo.cfg mo.policy qry).run es)),
      LocDead l t z.2 := by
  intro mo z hz
  rcases hdead with hab | ⟨lk, hmem, hgt, hlt⟩
  · rcases qry with n | (((((q1 | q2) | q3) | q4) | q5) | q6)
    · dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inl] at hz
      rw [simulateQ_lImpl_coinsE_run, mem_support_bind_iff] at hz
      obtain ⟨_, _, hz⟩ := hz; simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hab
    all_goals
      simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        transmitE, challE, deliverE, injectE, corrEShiftedPaper, deliverForgeE,
        hab, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
        pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hab
  · rcases qry with n | (((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩)
    · dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inl] at hz
      rw [simulateQ_lImpl_coinsE_run, mem_support_bind_iff] at hz
      obtain ⟨_, _, hz⟩ := hz; simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        transmitE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
      · cases hep : es.g.epMgmt (2 + Δcka) qep P r_c.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
        | some s₁ =>
          have hlk1 := epMgmt_mem_leaks hmem hep
          simp only [hep] at hz
          split at hz
          · simp only [abortE, StateT.run_bind, StateT.run_modify,
              pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl rfl
          · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨w, _, hz⟩ := hz
            rcases w with ⟨_ | ⟨st', c_out⟩, _⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify,
                StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inl rfl
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inr ⟨lk, by simpa [GameState.record] using hlk1, hgt, hlt⟩
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        challE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
      · cases hep : es.g.epMgmt (2 + Δcka) qep P r_c.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
        | some s₁ =>
          have hlk1 := epMgmt_mem_leaks hmem hep
          simp only [hep] at hz
          split at hz
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
          · split at hz
            · simp only [abortE, StateT.run_bind, StateT.run_modify,
                pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inl rfl
            · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
              obtain ⟨w, _, hz⟩ := hz
              rcases w with ⟨_ | ⟨st', c_out⟩, _⟩
              · simp only [abortE, StateT.run_bind, StateT.run_modify,
                  StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inl rfl
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inr ⟨lk, by simpa [GameState.record] using hlk1, hgt, hlt⟩
    · have hd : (mo.cfg (M := M)).deliverWin = false := rfl
      simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        deliverE, hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
      · cases htr : es.g.inTransit P.other c with
        | none =>
          simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
        | some rec =>
          simp only [htr, StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
          obtain ⟨w, _, hz⟩ := hz
          rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), _⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl rfl
          · dsimp only at hz
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
          · dsimp only at hz
            simp only [commitE, StateT.run_bind, liftH_run,
              bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨u, _, hz⟩ := hz
            rcases u with ⟨_ | new', _⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨x, rfl, hz⟩ := hz
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inl rfl
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨x, rfl, hz⟩ := hz
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inr ⟨lk, by simpa [GameState.accept, GameState.delete] using hmem, hgt, hlt⟩
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        injectE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
      · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
        obtain ⟨w, _, hz⟩ := hz
        rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), _⟩
        · simp only [abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inl rfl
        · dsimp only at hz
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
        · dsimp only at hz
          split at hz
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
          · split at hz
            · simp only [commitE, StateT.run_bind, liftH_run,
                bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
              obtain ⟨u, _, hz⟩ := hz
              rcases u with ⟨_ | new', _⟩
              · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                obtain ⟨x, rfl, hz⟩ := hz
                simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inl rfl
              · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                obtain ⟨x, rfl, hz⟩ := hz
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inr ⟨lk, by simpa [GameState.accept, GameState.delete] using hmem, hgt, hlt⟩
            · split at hz
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
              · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
      · split at hz
        · simp only [abortE, StateT.run_bind, StateT.run_modify,
            pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inl rfl
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
          obtain ⟨w, _, hz⟩ := hz
          rcases w with ⟨_ | stOut, _⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inl rfl
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact Or.inr ⟨lk, by simp [afterCorrShifted, GameState.leak, hmem], hgt, hlt⟩
    · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr,
        deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
      · cases htr : es.g.inTransit P.other c₁ with
        | none =>
          simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
        | some rec =>
          simp only [htr] at hz
          split at hz
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
          · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨w, _, hz⟩ := hz
            rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), _⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify,
                StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inl rfl
            · dsimp only at hz
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
            · dsimp only at hz
              split at hz
              · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
              · split at hz
                · simp only [commitE, StateT.run_bind, liftH_run,
                    bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
                  obtain ⟨u, _, hz⟩ := hz
                  rcases u with ⟨_ | new', _⟩
                  · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    obtain ⟨x, rfl, hz⟩ := hz
                    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    subst hz; exact Or.inl rfl
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    obtain ⟨x, rfl, hz⟩ := hz
                    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    subst hz; exact Or.inr ⟨lk, by simpa [GameState.accept, GameState.delete] using hmem, hgt, hlt⟩
                · split at hz
                  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    subst hz; exact Or.inr ⟨lk, hmem, hgt, hlt⟩

private theorem evalDist_loc_eq_zero_of_dead
    {Γ T Sig SS RS M CCoins E HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hks : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γ Sig (SS × Option ℕ) (RS × Option ℕ))
    (Δcka qep maxSkip l t : ℕ)
    (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (es : EState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) HS)
    (hdead : LocDead l t es) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    𝒟[simulateQ lImpl
      ((simulateQ (implEDFShiftedPaper l hks (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)] {true} = 0 := by
  intro mo
  induction oa using OracleComp.inductionOn generalizing es with
  | pure b =>
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, pure_bind,
      authOut_eq_false_of_locDead (2 + Δcka) l t es hdead]
    simp
  | query_bind qry cont ih =>
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, bind_assoc]
    exact evalDist_bind_eq_zero _ _ fun z hz =>
      ih z.1 z.2 (stepLoc_preserves_locDead hks Δcka qep maxSkip l t qry es hdead z hz)

private theorem stepLoc_win_false_of_qep_lt
    {Γ T Sig SS RS M CCoins E HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hks : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γ Sig (SS × Option ℕ) (RS × Option ℕ))
    (Δcka qep maxSkip l t : ℕ) (hqep_lt : qep + 1 < t)
    (qry : (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) HS)
    (hwin : es.g.win = false) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    ∀ z ∈ support (simulateQ lImpl
      ((implEDFShiftedPaper l hks (2 + Δcka) qep maxSkip mo.cfg mo.policy qry).run es)),
      z.2.g.win = false := by
  intro mo z hz
  rcases qry with n | (((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩)
  · dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inl] at hz
    rw [simulateQ_lImpl_coinsE_run, mem_support_bind_iff] at hz
    obtain ⟨_, _, hz⟩ := hz; simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      transmitE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · cases hep : es.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none =>
        simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      | some s₁ =>
        have hw1 := (epMgmt_win_eq hep).trans hwin
        simp only [hep] at hz
        split at hz
        · simp only [abortE, StateT.run_bind, StateT.run_modify,
            pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
          obtain ⟨w, _, hz⟩ := hz
          rcases w with ⟨_ | ⟨st', c_out⟩, _⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hw1
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      challE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · cases hep : es.g.epMgmt (2 + Δcka) qep P r_c.isSome with
      | none =>
        simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      | some s₁ =>
        have hw1 := (epMgmt_win_eq hep).trans hwin
        simp only [hep] at hz
        split at hz
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · split at hz
          · simp only [abortE, StateT.run_bind, StateT.run_modify,
            pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨w, _, hz⟩ := hz
            rcases w with ⟨_ | ⟨st', c_out⟩, _⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify,
                StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwin
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hw1
  · have hd : (mo.cfg (M := M)).deliverWin = false := rfl
    simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      deliverE, hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · cases htr : es.g.inTransit P.other c with
      | none =>
        simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      | some rec =>
        simp only [htr, StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
        obtain ⟨w, _, hz⟩ := hz
        rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), _⟩
        · simp only [abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · dsimp only at hz
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · dsimp only at hz
          simp only [commitE, StateT.run_bind, liftH_run,
            bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
          obtain ⟨u, _, hz⟩ := hz
          rcases u with ⟨_ | new', _⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            obtain ⟨x, rfl, hz⟩ := hz
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            obtain ⟨x, rfl, hz⟩ := hz
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      injectE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
      obtain ⟨w, _, hz⟩ := hz
      rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), _⟩
      · simp only [abortE, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      · dsimp only at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      · dsimp only at hz
        by_cases hlt_q : qep + 1 < t'
        · simp only [hlt_q, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · have hne : t' ≠ t := by omega
          have hinjF : (mo.cfg (M := M)).injectFull t' = false := by simp [mo, Mode.cfg, Config.auth, hne]
          simp only [hlt_q, hinjF, Bool.false_eq_true, ↓reduceIte] at hz
          split at hz
          · simp only [commitE, StateT.run_bind, liftH_run,
              bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
            obtain ⟨u, _, hz⟩ := hz
            rcases u with ⟨_ | new', _⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨x, rfl, hz⟩ := hz
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwin
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨x, rfl, hz⟩ := hz
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwin
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · split at hz
      · simp only [abortE, StateT.run_bind, StateT.run_modify,
          pure_bind, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
        obtain ⟨w, _, hz⟩ := hz
        rcases w with ⟨_ | stOut, _⟩
        · simp only [abortE, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; simpa [afterCorrShifted, GameState.leak] using hwin
  · simp only [implEDFShiftedPaper, QueryImpl.add_apply_inr,
      deliverForgeE, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · cases htr : es.g.inTransit P.other c₁ with
      | none =>
        simp only [htr, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hwin
      | some rec =>
        simp only [htr] at hz
        split at hz
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hwin
        · simp only [StateT.run_bind, liftH_run, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
          obtain ⟨w, _, hz⟩ := hz
          rcases w with ⟨_ | (_ | ⟨st', t', i', m'⟩), _⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · dsimp only at hz
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hwin
          · dsimp only at hz
            by_cases hbad_ep : (decide (qep + 1 < t') || (t' != rec.pos.epoch)) = true
            · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hwin
            · have hnot_lt : ¬ (qep + 1 < t') := by
                intro hlt; apply hbad_ep; simp [hlt]
              have hne : t' ≠ t := by omega
              have hinjF : (mo.cfg (M := M)).injectFull t' = false := by simp [mo, Mode.cfg, Config.auth, hne]
              simp only [hbad_ep, Bool.false_eq_true, hinjF, ↓reduceIte] at hz
              split at hz
              · simp only [commitE, StateT.run_bind, liftH_run,
                  bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
                obtain ⟨u, _, hz⟩ := hz
                rcases u with ⟨_ | new', _⟩
                · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  obtain ⟨x, rfl, hz⟩ := hz
                  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hwin
                · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  obtain ⟨x, rfl, hz⟩ := hz
                  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hwin
              · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hwin

private theorem evalDist_loc_eq_zero_of_qep_lt
    {Γ T Sig SS RS M CCoins E HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hks : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γ Sig (SS × Option ℕ) (RS × Option ℕ))
    (Δcka qep maxSkip l t : ℕ) (hqep_lt : qep + 1 < t)
    (oa : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (es : EState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) HS)
    (hwin : es.g.win = false) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    𝒟[simulateQ lImpl
      ((simulateQ (implEDFShiftedPaper l hks (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)] {true} = 0 := by
  intro mo
  induction oa using OracleComp.inductionOn generalizing es with
  | pure b =>
    simp [authOut, hwin]
  | query_bind qry cont ih =>
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, bind_assoc]
    exact evalDist_bind_eq_zero _ _ fun z hz =>
      ih z.1 z.2 (stepLoc_win_false_of_qep_lt hks Δcka qep maxSkip l t hqep_lt qry es hwin z hz)

private theorem rootLPrefix_regSessOf_ne_run {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (mo : Mode) (q : ℕ) (ks : ℕ → BitVec 256) (ep : ℕ) (hne : ep ≠ mo.tStar)
    (Ik : Pt) (σ : BitVec 256)
    (hLoc : LState Pt (BitVec 256) (BitVec 256) Pt) :
    simulateQ lImpl (((rootLPrefix (T := Pt) prng mo q ks ep Ik σ >>= fun r =>
        regSessOf r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hLoc) =
      if ep < mo.tStar ∧ mo.tL.isSome ∧ ep = mo.tH then
        (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
          pure (((prng.up σ Ir).1, (prng.up σ Ir).2, none), hLoc))
      else
        pure (((prng.up σ Ik).1, (prng.up σ Ik).2, none), hLoc) := by
  unfold rootLPrefix regSessOf
  by_cases hgt : mo.tStar < ep
  · have hlt : ¬ ep < mo.tStar := by omega
    simp [hgt, hlt]
  · have hlt : ep < mo.tStar := by omega
    simp only [hgt, hne, ↓reduceIte, hlt, true_and]
    by_cases htH : mo.tL.isSome = true ∧ ep = mo.tH
    · rcases htH with ⟨htL, heq⟩
      simp [htL, heq]
    · have hcond : (mo.tL.isSome && decide (ep = mo.tH)) = false := by
        rw [Bool.and_eq_false_iff]; by_cases h1 : mo.tL.isSome = true <;> simp_all
      simp [hcond, htH]

private theorem rootFSMulti_regSessOptMulti_ne_run {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (mo : Mode) (ep : ℕ) (hne : ep ≠ mo.tStar)
    (Ik : Pt) (σ : BitVec 256)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT)) :
    (simulateQ (pubFsMultiImpl impl) (((rootFSMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        prng mo ep Ik σ >>= fun r =>
        regSessOptMulti r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hM)).run st =
      if ep < mo.tStar ∧ mo.tL.isSome ∧ ep = mo.tH then
        (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
          pure ((((prng.up σ Ir).1, (prng.up σ Ir).2, none), hM), st))
      else
        pure ((((prng.up σ Ik).1, (prng.up σ Ik).2, none), hM), st) := by
  unfold rootFSMulti regSessOptMulti
  by_cases hgt : mo.tStar < ep
  · have hlt : ¬ ep < mo.tStar := by omega
    simp [hgt, hlt]
  · have hlt : ep < mo.tStar := by omega
    simp only [hgt, hne, ↓reduceIte, hlt, true_and]
    by_cases htH : mo.tL.isSome = true ∧ ep = mo.tH
    · rcases htH with ⟨htL, heq⟩
      simp only [htL, heq, decide_true, Bool.and_self, and_self, ↓reduceIte, StateT.run_bind,
        bind_assoc, simulateQ_bind, simulateQ_pubFsMulti_sampleT_run, pure_bind, StateT.run_pure,
        simulateQ_pure]
    · have hcond : (mo.tL.isSome && decide (ep = mo.tH)) = false := by
        rw [Bool.and_eq_false_iff]; by_cases h1 : mo.tL.isSome = true <;> simp_all
      simp [hcond, htH]

private theorem rootLPrefix_regSessOf_tStar_tH_run {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (l t q : ℕ) (hq : 0 < q) (ks : ℕ → BitVec 256)
    (htH : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH)
    (Ik : Pt) (σ : BitVec 256)
    (hLoc : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hnil : hLoc.sessions = []) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    simulateQ lImpl (((rootLPrefix (T := Pt) prng mo q ks t Ik σ >>= fun r =>
        regSessOf r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hLoc) =
      (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun _ =>
          pure (((prng.up σ Ir).1, ks 0, some 0), { hLoc with sessions := [Ir] })) := by
  intro mo
  have htH' : mo.tH = t := htH.symm
  unfold rootLPrefix regSessOf regSess
  simp [htH', mo, hnil, hq]

private theorem rootFSMulti_regSessOptMulti_tStar_tH_run {Pt : Type} [DecidableEq Pt]
    [SampleableType Pt] {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (l t : ℕ)
    (htH : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH)
    (Ik : Pt) (σ : BitVec 256)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT))
    (hnil : hM.sessions = []) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    (simulateQ (pubFsMultiImpl impl) (((rootFSMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        prng mo t Ik σ >>= fun r =>
        regSessOptMulti r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hM)).run st =
      (($ᵗ Pt : ProbComp Pt) >>= fun Ir =>
        ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun k_draw =>
          pure ((((prng.up σ Ir).1, k_draw, some 0), { hM with sessions := [Ir] }), st)) := by
  intro mo
  have htStar : mo.tStar = t := rfl
  have htH' : mo.tH = t := htH.symm
  have htLsome : mo.tL.isSome = true := rfl
  unfold rootFSMulti regSessOptMulti regSessMulti
  simp only [htStar, Nat.lt_irrefl, htH', htLsome, decide_true, Bool.and_self, ↓reduceIte,
    StateT.run_bind]
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_pubFsMulti_sampleT_run]
  simp only [bind_assoc, pure_bind]
  congr 1; funext Ir
  rw [simulateQ_bind, StateT.run_bind, simulateQ_pubFsMulti_sampleT_run]
  simp [hnil]

private theorem rootLPrefix_regSessOf_tStar_ne_run {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (l t q : ℕ) (ks : ℕ → BitVec 256)
    (hne_tH : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH)
    (Ik : Pt) (σ : BitVec 256)
    (hLoc : LState Pt (BitVec 256) (BitVec 256) Pt)
    (htbl : ∀ Ik', hLoc.table.lookup Ik' =
      if Ik' ∈ hLoc.sessions then some (ks (hLoc.sessions.idxOf Ik')) else none)
    (hlen : hLoc.sessions.length < q) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    simulateQ lImpl (((rootLPrefix (T := Pt) prng mo q ks t Ik σ >>= fun r =>
        regSessOf r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hLoc) =
      if Ik ∈ hLoc.sessions then
        pure (((prng.up σ Ik).1, ks (hLoc.sessions.idxOf Ik), some (hLoc.sessions.idxOf Ik)), hLoc)
      else
        (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun _ =>
          pure (((prng.up σ Ik).1, ks hLoc.sessions.length, some hLoc.sessions.length),
            { hLoc with table := (Ik, ks hLoc.sessions.length) :: hLoc.table,
                        sessions := hLoc.sessions ++ [Ik] })) := by
  intro mo
  have htStar : mo.tStar = t := rfl
  have hne : t ≠ mo.tH := hne_tH
  have htLsome : mo.tL.isSome = true := rfl
  unfold rootLPrefix regSessOf
  simp only [htStar, Nat.lt_irrefl, hne, htLsome, decide_false, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hmem : Ik ∈ hLoc.sessions
  · have hlk : hLoc.table.lookup Ik = some (ks (hLoc.sessions.idxOf Ik)) := by rw [htbl]; simp [hmem]
    simp [lookupFLPrefix, regSess, hlk, hmem]
  · have hlk : hLoc.table.lookup Ik = none := by rw [htbl]; simp [hmem]
    simp [lookupFLPrefix, regSess, hlk, hmem, hlen]

private theorem rootFSMulti_regSessOptMulti_tStar_ne_run {Pt : Type} [DecidableEq Pt]
    [SampleableType Pt] {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (l t : ℕ)
    (hne_tH : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH)
    (Ik : Pt) (σ : BitVec 256)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT))
    (htbl : ∀ Ik', (hM.table.lookup Ik').isSome = decide (Ik' ∈ hM.sessions)) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    (simulateQ (pubFsMultiImpl impl) (((rootFSMulti
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
        (E := ℕ × LibsignalCiphertextWithSalt32)
        prng mo t Ik σ >>= fun r =>
        regSessOptMulti r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hM)).run st =
      if Ik ∈ hM.sessions then
        pure ((((prng.up σ Ik).1, (hM.table.lookup Ik).getD 0, some (hM.sessions.idxOf Ik)), hM), st)
      else
        (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun k_draw =>
          pure ((((prng.up σ Ik).1, k_draw, some hM.sessions.length),
            { hM with table := (Ik, k_draw) :: hM.table,
                      sessions := hM.sessions ++ [Ik] }), st)) := by
  intro mo
  have htStar : mo.tStar = t := rfl
  have hne : t ≠ mo.tH := hne_tH
  have htLsome : mo.tL.isSome = true := rfl
  unfold rootFSMulti regSessOptMulti
  simp only [htStar, Nat.lt_irrefl, hne, htLsome, decide_false, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hmem : Ik ∈ hM.sessions
  · have his : (hM.table.lookup Ik).isSome = true := by rw [htbl]; simp [hmem]
    cases hlk : hM.table.lookup Ik with
    | none => rw [hlk] at his; cases his
    | some k0 => simp [lookupMultiF, regSessMulti, hlk, hmem]
  · have his : (hM.table.lookup Ik).isSome = false := by rw [htbl]; simp [hmem]
    have hlk : hM.table.lookup Ik = none := Option.not_isSome_iff_eq_none.mp (by simp [his])
    unfold lookupMultiF regSessMulti
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      hlk, bind_assoc]
    rw [simulateQ_bind, StateT.run_bind, simulateQ_pubFsMulti_sampleT_run]
    simp [hmem]

private def Dir1Rel (phase1 : Bool) (cLoc cM cL : ProbComp Bool) : Prop :=
  if phase1 then LeAdd cLoc cM cL else LeOne cLoc cM

private theorem dir1Rel_to_phase2 {phase1 : Bool} {cLoc cM cL : ProbComp Bool}
    (h : LeOne cLoc cM) : Dir1Rel phase1 cLoc cM cL := by
  cases phase1
  · exact h
  · exact leAdd_of_le_main h

private theorem dir1Rel_of_lhs_zero {phase1 : Bool} {cLoc cM cL : ProbComp Bool}
    (h0 : 𝒟[cLoc] {true} = 0) : Dir1Rel phase1 cLoc cM cL := by
  cases phase1
  · exact leOne_of_lhs_zero h0
  · exact leAdd_of_lhs_zero h0

private theorem dir1Rel_bind {α : Type} {phase1 : Bool} (mx : ProbComp α)
    (fLoc fM fL : α → ProbComp Bool)
    (h : ∀ x ∈ support mx, Dir1Rel phase1 (fLoc x) (fM x) (fL x)) :
    Dir1Rel phase1 (mx >>= fLoc) (mx >>= fM) (mx >>= fL) := by
  cases phase1
  · exact leOne_bind mx h
  · exact leAdd_bind mx h

private theorem dir1Rel_bind_dummy_loc {α : Type} {phase1 : Bool} (mx : ProbComp α)
    (cLoc : ProbComp Bool) (fM fL : α → ProbComp Bool)
    (h : ∀ x ∈ support mx, Dir1Rel phase1 cLoc (fM x) (fL x)) :
    Dir1Rel phase1 cLoc (mx >>= fM) (mx >>= fL) := by
  cases phase1
  · exact leOne_bind_dummy_loc mx h
  · exact leAdd_bind_dummy_loc mx h

private theorem dir1Rel_bind_dummy_M {α : Type} [SampleableType α] {phase1 : Bool}
    (fLoc : α → ProbComp Bool) (cM cL : ProbComp Bool)
    (h : ∀ x ∈ support ($ᵗ α : ProbComp α), Dir1Rel phase1 (fLoc x) cM cL) :
    Dir1Rel phase1 (($ᵗ α : ProbComp α) >>= fLoc) cM cL := by
  have h1 := dir1Rel_bind ($ᵗ α : ProbComp α) fLoc (fun _ => cM) (fun _ => cL) h
  cases phase1
  · unfold Dir1Rel LeOne at h1 ⊢
    rwa [OracleComp.evalDist_bind_const ($ᵗ α : ProbComp α) cM] at h1
  · unfold Dir1Rel LeAdd at h1 ⊢
    rwa [OracleComp.evalDist_bind_const ($ᵗ α : ProbComp α) cM,
      OracleComp.evalDist_bind_const ($ᵗ α : ProbComp α) cL] at h1

private theorem dir1Rel_mono_phase {phase1 phase1' : Bool} (himp : phase1' = true → phase1 = true)
    {cLoc cM cL cL' : ProbComp Bool} (hL : phase1' = true → cL = cL')
    (h : Dir1Rel phase1' cLoc cM cL') : Dir1Rel phase1 cLoc cM cL := by
  cases phase1'
  · exact dir1Rel_to_phase2 h
  · rw [himp rfl, hL rfl]; exact h

private theorem activeSessInv_mono_phase {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {phase1 phase1' : Bool} (himp : phase1' = true → phase1 = true)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL sL' : SessHSt Pt ℓ}
    (hL_eq : phase1' = true → sL' = sL)
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc bk sM sL) :
    ActiveSessInv C ℓ encT idOf phase1' k ssLoc rsLoc bk sM sL' := by
  cases phase1'
  · cases phase1
    · rcases hinv with ⟨stR, h⟩
      exact ⟨stR, { h with syncRML := fun hp1 => Bool.noConfusion hp1 }⟩
    · exact activeSessInv_to_phase2 C ℓ encT idOf hinv
  · rw [← himp rfl, hL_eq rfl]; exact hinv

private theorem dir1Rel_both_win_terminal
    {KC Γ CCoins Pt I KR RSt σ : Type} {ℓ : ℕ}
    [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (fs : FSAEADScheme (BitVec 256)
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka qep l t : ℕ) (phase1 : Bool)
    (hks : Hooks nilSpec (LState Pt RSt (BitVec 256) I)
      Γ Pt RSt
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γ RSt
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
    (impl : QueryImpl
      (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT σ ProbComp))
    (oa : SchemeAdversaryDF Γ Pt RSt
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (esLoc : EState
      (VP Γ Pt RSt
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt RSt (BitVec 256) I))
    (esM : EState
      (VP Γ Pt RSt
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32)))
    (stM : (ℕ → Bool) × (ℕ → σ)) (cL : ProbComp Bool)
    (hwinL : esLoc.g.win = true) (hwinM : esM.g.win = true)
    (hout : authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esLoc =
      authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esM) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let cLoc := simulateQ lImpl
      ((simulateQ (implEDFShiftedPaper l hks (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esLoc) >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)
    let innerM := (simulateQ (implEDFShiftedPaper l
      (hooksFSMulti cka prng fs Δcka mo false false)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esM >>=
      fun z => pure (authOut (2 + Δcka) mo.policy z.2)
    Dir1Rel phase1 cLoc (Prod.fst <$> (simulateQ (pubFsMultiImpl impl) innerM).run stM) cL := by
  intro mo
  dsimp only
  refine dir1Rel_to_phase2 ?_
  unfold LeOne
  rw [evalDist_loc_eq_pure_of_win hks Δcka qep fs.maxSkip l t oa esLoc hwinL,
    evalDist_pubFsMulti_false_eq_pure_of_win cka prng fs Δcka qep l t impl oa esM stM hwinM,
    hout]

private theorem lastLeakGuessAdmissible_dir1 (Δcka l t : ℕ)
    (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka)) :
    _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka)
      (⟨true, some (l - 1), t⟩ : Mode).tL (⟨true, some (l - 1), t⟩ : Mode).tStar = true := by
  simp only [_root_.CryptoGames.SM.lastLeakGuessAdmissible, healedBy, decide_eq_true_eq]
  omega

private theorem fsSend_dir1_inr {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka l t : ℕ) (phase1 : Bool)
    (ctxM : Ctx (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (hepoch : ctxM.epoch P = t)
    (hhealed : healedBy ctxM.tL (2 + Δcka) t = phase1)
    (sIdx : ℕ) (hdr : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (hshort : pm.1.shortB = true)
    (k : BitVec 256) (ssLoc : RatchetSenderState (BitVec 256))
    (rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc
      ((hM.book sIdx).getD {}) (tblM sIdx) (tblL sIdx)) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let o := fs.send ssLoc hdr pm
    ∃ (bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)) (sM' sL' : SessHSt Pt ℓ),
      let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
      (simulateQ (pubFsMultiImpl (impl false))
        (((hooksFSMulti cka prng fs Δcka mo false false).fsSend
          ctxM P t (.inr sIdx) hdr pm none).run hM)).run (fun _ => false, tblM) =
        pure ((some (.inr sIdx, o.2), hM'), (fun _ => false, Function.update tblM sIdx sM')) ∧
      (phase1 = true →
        (simulateQ (pubFsMultiImpl (impl true))
          (((hooksFSMulti cka prng fs Δcka mo false true).fsSend
            ctxM P t (.inr sIdx) hdr pm none).run hM)).run (fun _ => false, tblL) =
          pure ((some (.inr sIdx, o.2), hM'), (fun _ => false, Function.update tblL sIdx sL'))) ∧
      ActiveSessInv C ℓ encT idOf phase1 k o.1 rsLoc bk' sM' sL' := by
  intro cka prng fs mo impl o
  cases phase1 with
  | true =>
    have hsafe : ctxM.safeCh (2 + Δcka) P = true := by
      cases hs : ctxM.safeCh (2 + Δcka) P
      · have hf := healedBy_false_of_safeCh_false hepoch hs
        rw [hhealed] at hf; cases hf
      · rfl
    rcases activeSessInv_transmit C hrt ℓ hℓ encT idOf hinv hdr pm hshort with
      ⟨sM', sL', htrM, htrL, hinv'⟩
    let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
      { (hM.book sIdx).getD {} with
        fsCount := ((hM.book sIdx).getD {}).fsCount + 1
        fsTrans := (((hM.book sIdx).getD {}).fsCount + 1, hdr, o.2) ::
          ((hM.book sIdx).getD {}).fsTrans }
    refine ⟨bk', sM', sL', ?_, fun _ => ?_, hinv'⟩
    · dsimp only [hooksFSMulti]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hsafe, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
      erw [simulateQ_pubFsMulti_liftFSMulti_run,
        pubFsMultiImpl_transmit_run C ℓ encT idOf false sIdx hdr pm tblM htrM]
      simp [bk', o, fs]
    · dsimp only [hooksFSMulti]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hsafe, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
      erw [simulateQ_pubFsMulti_liftFSMulti_run,
        pubFsMultiImpl_transmit_run C ℓ encT idOf true sIdx hdr pm tblL (htrL rfl)]
      simp [bk', o, fs]
  | false =>
    by_cases hc1 : (!(ctxM.safeCh (2 + Δcka) P) && !((hM.book sIdx).getD {}).sCorr) = true
    · rcases activeSessInv_corruptSender C ℓ encT idOf hinv with ⟨sM1, hcorrM, hinv1⟩
      rcases activeSessInv_transmit C hrt ℓ hℓ encT idOf hinv1 hdr pm hshort with
        ⟨sM', sL', htrM, _, hinv'⟩
      let bk1 : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
        { (hM.book sIdx).getD {} with sCorr := true }
      let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
        { bk1 with fsCount := bk1.fsCount + 1, fsTrans := (bk1.fsCount + 1, hdr, o.2) :: bk1.fsTrans }
      refine ⟨bk', sM', sL', ?_, fun hp1 => Bool.noConfusion hp1, hinv'⟩
      dsimp only [hooksFSMulti]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hc1, ↓reduceIte,
        Bool.false_eq_true, simulateQ_bind]
      erw [simulateQ_pubFsMulti_liftFSMulti_run,
        pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tblM hcorrM]
      erw [bind_assoc, pure_bind, pure_bind]
      dsimp only
      simp only [StateT.run_bind, StateT.run_modify, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
      erw [simulateQ_pubFsMulti_liftFSMulti_run,
        pubFsMultiImpl_transmit_run C ℓ encT idOf false sIdx hdr pm
          (Function.update tblM sIdx sM1) (by simpa [Function.update_self] using htrM)]
      simp [Function.update_idem, bk', bk1, o, fs]
    · rcases activeSessInv_transmit C hrt ℓ hℓ encT idOf hinv hdr pm hshort with
        ⟨sM', sL', htrM, _, hinv'⟩
      let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
        { (hM.book sIdx).getD {} with
          fsCount := ((hM.book sIdx).getD {}).fsCount + 1
          fsTrans := (((hM.book sIdx).getD {}).fsCount + 1, hdr, o.2) ::
            ((hM.book sIdx).getD {}).fsTrans }
      refine ⟨bk', sM', sL', ?_, fun hp1 => Bool.noConfusion hp1, hinv'⟩
      dsimp only [hooksFSMulti]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hc1, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
      erw [simulateQ_pubFsMulti_liftFSMulti_run,
        pubFsMultiImpl_transmit_run C ℓ encT idOf false sIdx hdr pm tblM htrM]
      simp [bk', o, fs]

private theorem hdr_ct_beq_eq_decide {Pt : Type} [DecidableEq Pt]
    {inst : BEq (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))}
    [@LawfulBEq (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) inst]
    (x y : Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) :
    @BEq.beq _ inst x y = decide (x = y) :=
  Bool.eq_iff_iff.2 (by simp [@beq_iff_eq _ inst _])

private theorem fsRecv_dir1_inr {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka l t : ℕ) (phase1 : Bool)
    (ctxM : Ctx (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (hhealed : healedBy ctxM.tL (2 + Δcka) t = phase1)
    (sIdx : ℕ) (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (k : BitVec 256) (ssLoc : RatchetSenderState (BitVec 256))
    (rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc
      ((hM.book sIdx).getD {}) (tblM sIdx) (tblL sIdx)) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    (phase1 = true ∧ ∃ sL',
      (simulateQ (pubFsMultiImpl (impl true))
        (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv
          ctxM P t (.inr sIdx) hdr e rec?).run hM)).run (fun _ => false, tblL) =
        pure ((none, { hM with lfWin := true }), (fun _ => false, Function.update tblL sIdx sL'))) ∨
    ∃ (hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
      (tblM' tblL' : ℕ → SessHSt Pt ℓ),
      hM'.sessions = hM.sessions ∧ hM'.cache = hM.cache ∧ hM'.table = hM.table ∧
      hM'.lfWin = hM.lfWin ∧
      (∀ j, j ≠ sIdx → hM'.book j = hM.book j ∧ tblM' j = tblM j ∧
        (phase1 = true → tblL' j = tblL j)) ∧
      match fs.receive rsLoc hdr e with
      | none =>
        (simulateQ (pubFsMultiImpl (impl false))
          (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv
            ctxM P t (.inr sIdx) hdr e rec?).run hM)).run (fun _ => false, tblM) =
          pure ((some none, hM'), (fun _ => false, tblM')) ∧
        (phase1 = true →
          (simulateQ (pubFsMultiImpl (impl true))
            (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv
              ctxM P t (.inr sIdx) hdr e rec?).run hM)).run (fun _ => false, tblL) =
            pure ((some none, hM'), (fun _ => false, tblL'))) ∧
        ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc
          ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL' sIdx)
      | some (rsLoc', idxOut, pmOut) =>
        (simulateQ (pubFsMultiImpl (impl false))
          (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv
            ctxM P t (.inr sIdx) hdr e rec?).run hM)).run (fun _ => false, tblM) =
          pure ((some (some (.inr sIdx, idxOut, pmOut)), hM'), (fun _ => false, tblM')) ∧
        (phase1 = true →
          (simulateQ (pubFsMultiImpl (impl true))
            (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv
              ctxM P t (.inr sIdx) hdr e rec?).run hM)).run (fun _ => false, tblL) =
            pure ((some (some (.inr sIdx, idxOut, pmOut)), hM'), (fun _ => false, tblL'))) ∧
        ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc'
          ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL' sIdx) := by
  intro cka prng fs mo impl
  let bk := (hM.book sIdx).getD {}
  cases hmatch : ((hM.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e)) with
  | some mEntry =>
    have hmatch_dec : ((hM.book sIdx).getD {}).fsTrans.find? (fun x => decide (x.2 = (hdr, e))) =
        some mEntry := by simpa only [hdr_ct_beq_eq_decide] using hmatch
    right
    rcases activeSessInv_deliver C hD hrt ℓ hℓ encT idOf hinv hdr e hmatch with ⟨p, hp_pub, hdel⟩
    cases hrec : fs.receive rsLoc hdr e with
    | none =>
      dsimp only [fs] at hrec; rw [hrec] at hdel
      rcases hdel with ⟨sM', sL', hdelM, hdelL, hinv'⟩
      refine ⟨hM, Function.update tblM sIdx sM', Function.update tblL sIdx sL',
        rfl, rfl, rfl, rfl,
        fun j hj => ⟨rfl, Function.update_of_ne hj _ _, fun _ => Function.update_of_ne hj _ _⟩, ?_⟩
      simp only [Function.update_self]
      refine ⟨?_, fun hp1 => ?_, hinv'⟩
      · dsimp only [hooksFSMulti]
        simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
          pure_bind, hmatch_dec, Option.isNone_some, Bool.false_and, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, Option.isSome_some, simulateQ_bind]
        erw [simulateQ_pubFsMulti_liftFSMulti_run,
          pubFsMultiImpl_deliver_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hp_pub tblM hdelM]
        simp [withPub]
      · dsimp only [hooksFSMulti]
        simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
          pure_bind, hmatch_dec, Option.isNone_some, Bool.false_and, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, Option.isSome_some, simulateQ_bind]
        erw [simulateQ_pubFsMulti_liftFSMulti_run,
          pubFsMultiImpl_deliver_some_run C ℓ encT idOf true sIdx hdr e.1 e.2 p hp_pub tblL
            (hdelL hp1)]
        simp [withPub]
    | some rim =>
      rcases rim with ⟨rsLoc', idxOut, pmOut⟩
      dsimp only [fs] at hrec; rw [hrec] at hdel
      rcases hdel with ⟨hm1, sM', sL', hdelM, hdelL, hp_eq, hinv'⟩
      have hpm : (p, pmOut.2) = pmOut := Prod.ext hp_eq.symm rfl
      let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
        { bk with fsTrans := bk.fsTrans.filter (·.1 != mEntry.1) }
      let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
      refine ⟨hM', Function.update tblM sIdx sM', Function.update tblL sIdx sL',
        rfl, rfl, rfl, rfl,
        fun j hj => ⟨Function.update_of_ne hj _ _, Function.update_of_ne hj _ _,
          fun _ => Function.update_of_ne hj _ _⟩, ?_⟩
      simp only [hM', Function.update_self, Option.getD_some]
      refine ⟨?_, fun hp1 => ?_, hinv'⟩
      · dsimp only [hooksFSMulti]
        simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
          pure_bind, hmatch_dec, Option.isNone_some, Bool.false_and, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, Option.isSome_some, simulateQ_bind]
        erw [simulateQ_pubFsMulti_liftFSMulti_run,
          pubFsMultiImpl_deliver_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hp_pub tblM hdelM]
        simp [withPub, hpm, bk', bk]
      · dsimp only [hooksFSMulti]
        simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
          pure_bind, hmatch_dec, Option.isNone_some, Bool.false_and, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, Option.isSome_some, simulateQ_bind]
        erw [simulateQ_pubFsMulti_liftFSMulti_run,
          pubFsMultiImpl_deliver_some_run C ℓ encT idOf true sIdx hdr e.1 e.2 p hp_pub tblL
            (hdelL hp1)]
        simp [withPub, hpm, bk', bk]
  | none =>
    have hmatch_dec : ((hM.book sIdx).getD {}).fsTrans.find? (fun x => decide (x.2 = (hdr, e))) =
        none := by simpa only [hdr_ct_beq_eq_decide] using hmatch
    cases phase1 with
    | true =>
      cases hpub : lPubOf protoSignalCodec e.2 with
      | none =>
        right
        have hrec : fs.receive rsLoc hdr e = none :=
          lFS_receive_eq_none_of_lPubOf_none C ℓ encT idOf rsLoc hdr e hpub
        refine ⟨hM, tblM, tblL, rfl, rfl, rfl, rfl,
          fun _ _ => ⟨rfl, rfl, fun _ => rfl⟩, ?_⟩
        simp only [hrec]
        refine ⟨?_, fun _ => ?_, hinv⟩
        · dsimp only [hooksFSMulti]
          simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
            pure_bind, hmatch_dec, Option.isSome_none, hhealed, Bool.not_true,
            Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
          erw [simulateQ_pubFsMulti_liftFSMulti_run,
            pubFsMultiImpl_inject_none_run C ℓ encT idOf false sIdx hdr e.1 e.2 hpub tblM]
          simp
        · dsimp only [hooksFSMulti]
          simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
            pure_bind, hmatch_dec, Option.isNone_none, Option.isSome_none, hhealed, Bool.not_true,
            Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
          erw [simulateQ_pubFsMulti_liftFSMulti_run,
            pubFsMultiImpl_inject_none_run C ℓ encT idOf true sIdx hdr e.1 e.2 hpub tblL]
          simp
      | some p =>
        rcases activeSessInv_inject_phase1 C ℓ encT idOf hinv hdr e hmatch p hpub with
          ⟨msg, sL', hscorr_f, hlt_cnt, hinjL⟩ | hinj
        · left
          refine ⟨rfl, sL', ?_⟩
          dsimp only [hooksFSMulti]
          simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
            pure_bind, hmatch_dec, Option.isNone_none, Option.isSome_none, hhealed, Bool.not_true,
            Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
          erw [simulateQ_pubFsMulti_liftFSMulti_run,
            pubFsMultiImpl_inject_some_run C ℓ encT idOf true sIdx hdr e.1 e.2 p hpub tblL hinjL]
          simp [withPub, hscorr_f, hlt_cnt]
        · right
          cases hrec : fs.receive rsLoc hdr e with
          | none =>
            dsimp only [fs] at hrec; rw [hrec] at hinj
            rcases hinj with ⟨sM', sL', hinjM, hinjL, hinv'⟩
            refine ⟨hM, Function.update tblM sIdx sM', Function.update tblL sIdx sL',
              rfl, rfl, rfl, rfl,
              fun j hj => ⟨rfl, Function.update_of_ne hj _ _, fun _ => Function.update_of_ne hj _ _⟩, ?_⟩
            simp only [Function.update_self]
            refine ⟨?_, fun _ => ?_, hinv'⟩
            · dsimp only [hooksFSMulti]
              simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
                pure_bind, hmatch_dec, Option.isSome_none, hhealed,
                Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                simulateQ_bind]
              erw [simulateQ_pubFsMulti_liftFSMulti_run,
                pubFsMultiImpl_inject_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hpub tblM hinjM]
              simp [withPub]
            · dsimp only [hooksFSMulti]
              simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
                pure_bind, hmatch_dec, Option.isNone_none, Option.isSome_none, hhealed,
                Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                simulateQ_bind]
              erw [simulateQ_pubFsMulti_liftFSMulti_run,
                pubFsMultiImpl_inject_some_run C ℓ encT idOf true sIdx hdr e.1 e.2 p hpub tblL hinjL]
              simp [withPub]
          | some rim =>
            rcases rim with ⟨rsLoc', idxOut, pmOut⟩
            dsimp only [fs] at hrec; rw [hrec] at hinj
            rcases hinj with ⟨sM', sL', hinjM, hinjL, hle_cnt, hp_eq, hinv'⟩
            have hpm : (p, pmOut.2) = pmOut := Prod.ext hp_eq.symm rfl
            have hcondL : (!((hM.book sIdx).getD {}).sCorr &&
                decide (((hM.book sIdx).getD {}).fsCount < idxOut)) = false := by
              cases hsc : ((hM.book sIdx).getD {}).sCorr
              · have hle := hle_cnt hsc
                simp [Nat.not_lt_of_ge hle]
              · rfl
            let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
              { bk with fsTrans := bk.fsTrans.filter (·.1 != idxOut) }
            let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
            refine ⟨hM', Function.update tblM sIdx sM', Function.update tblL sIdx sL',
              rfl, rfl, rfl, rfl,
              fun j hj => ⟨Function.update_of_ne hj _ _, Function.update_of_ne hj _ _,
                fun _ => Function.update_of_ne hj _ _⟩, ?_⟩
            simp only [hM', Function.update_self, Option.getD_some]
            refine ⟨?_, fun _ => ?_, hinv'⟩
            · dsimp only [hooksFSMulti]
              simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
                pure_bind, hmatch_dec, Option.isSome_none, hhealed,
                Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                simulateQ_bind]
              erw [simulateQ_pubFsMulti_liftFSMulti_run,
                pubFsMultiImpl_inject_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hpub tblM hinjM]
              simp [withPub, hpm, bk', bk]
            · dsimp only [hooksFSMulti]
              simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
                pure_bind, hmatch_dec, Option.isNone_none, Option.isSome_none, hhealed,
                Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                simulateQ_bind]
              erw [simulateQ_pubFsMulti_liftFSMulti_run,
                pubFsMultiImpl_inject_some_run C ℓ encT idOf true sIdx hdr e.1 e.2 p hpub tblL hinjL]
              cases hsc : ((hM.book sIdx).getD {}).sCorr
              · have hle := hle_cnt hsc
                simp [withPub, hpm, hsc,
                  Nat.not_lt_of_ge hle, bk', bk]
              · simp [withPub, hpm, hsc, bk', bk]
    | false =>
      right
      cases hsc : ((hM.book sIdx).getD {}).sCorr with
      | false =>
        rcases activeSessInv_corruptSender C ℓ encT idOf hinv with ⟨sM1, hcorrM, hinv1⟩
        let bk1 : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) := { bk with sCorr := true }
        let hM1 := { hM with book := Function.update hM.book sIdx (some bk1) }
        have hsc1 : bk1.sCorr = true := rfl
        have hmatch1 : bk1.fsTrans.find? (fun x => x.2 == (hdr, e)) = none := hmatch
        cases hpub : lPubOf protoSignalCodec e.2 with
        | none =>
          have hrec : fs.receive rsLoc hdr e = none :=
            lFS_receive_eq_none_of_lPubOf_none C ℓ encT idOf rsLoc hdr e hpub
          refine ⟨hM1, Function.update tblM sIdx sM1, tblL, rfl, rfl, rfl, rfl,
            fun j hj => ⟨Function.update_of_ne hj _ _, Function.update_of_ne hj _ _,
              fun hp1 => Bool.noConfusion hp1⟩, ?_⟩
          simp only [hrec, hM1, Function.update_self, Option.getD_some]
          refine ⟨?_, fun hp1 => Bool.noConfusion hp1, hinv1⟩
          dsimp only [hooksFSMulti]
          simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get, pure_bind, hmatch_dec,
            Option.isNone_none, hhealed, hsc, Bool.not_false, Bool.true_and, Bool.false_eq_true,
            ↓reduceIte, simulateQ_bind]
          erw [simulateQ_pubFsMulti_liftFSMulti_run,
            pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tblM hcorrM]
          erw [bind_assoc, pure_bind, pure_bind]
          dsimp only
          simp only [StateT.run_bind, StateT.run_modify,
            pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.isSome_none, simulateQ_bind]
          erw [simulateQ_pubFsMulti_liftFSMulti_run,
            pubFsMultiImpl_inject_none_run C ℓ encT idOf false sIdx hdr e.1 e.2 hpub
              (Function.update tblM sIdx sM1)]
          simp [bk1, bk]
        | some p =>
          have hinj := activeSessInv_inject_phase2 C ℓ encT idOf hinv1 hsc1 hdr e hmatch1 p hpub
          cases hrec : fs.receive rsLoc hdr e with
          | none =>
            dsimp only [fs] at hrec; rw [hrec] at hinj
            rcases hinj with ⟨sM', hinjM, hinv'⟩
            refine ⟨hM1, Function.update tblM sIdx sM', tblL, rfl, rfl, rfl, rfl,
              fun j hj => ⟨Function.update_of_ne hj _ _, Function.update_of_ne hj _ _,
                fun hp1 => Bool.noConfusion hp1⟩, ?_⟩
            simp only [hM1, Function.update_self, Option.getD_some]
            refine ⟨?_, fun hp1 => Bool.noConfusion hp1, hinv'⟩
            dsimp only [hooksFSMulti]
            simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get, pure_bind, hmatch_dec,
              Option.isNone_none, hhealed, hsc, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, simulateQ_bind]
            erw [simulateQ_pubFsMulti_liftFSMulti_run,
              pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tblM hcorrM]
            erw [bind_assoc, pure_bind, pure_bind]
            dsimp only
            simp only [StateT.run_bind, StateT.run_modify,
              pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Option.isSome_none, simulateQ_bind]
            erw [simulateQ_pubFsMulti_liftFSMulti_run,
              pubFsMultiImpl_inject_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hpub
                (Function.update tblM sIdx sM1) (by simpa [Function.update_self] using hinjM)]
            simp [withPub, Function.update_idem, bk1, bk]
          | some rim =>
            rcases rim with ⟨rsLoc', idxOut, pmOut⟩
            dsimp only [fs] at hrec; rw [hrec] at hinj
            rcases hinj with ⟨sM', hinjM, hp_eq, hinv'⟩
            have hpm : (p, pmOut.2) = pmOut := Prod.ext hp_eq.symm rfl
            let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
              { bk1 with fsTrans := bk1.fsTrans.filter (·.1 != idxOut) }
            let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
            refine ⟨hM', Function.update tblM sIdx sM', tblL, rfl, rfl, rfl, rfl,
              fun j hj => ⟨Function.update_of_ne hj _ _, Function.update_of_ne hj _ _,
                fun hp1 => Bool.noConfusion hp1⟩, ?_⟩
            simp only [hM', Function.update_self, Option.getD_some]
            refine ⟨?_, fun hp1 => Bool.noConfusion hp1, hinv'⟩
            dsimp only [hooksFSMulti]
            simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get, pure_bind, hmatch_dec,
              Option.isNone_none, hhealed, hsc, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, simulateQ_bind]
            erw [simulateQ_pubFsMulti_liftFSMulti_run,
              pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tblM hcorrM]
            erw [bind_assoc, pure_bind, pure_bind]
            dsimp only
            simp only [StateT.run_bind, StateT.run_modify,
              pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Option.isSome_none, simulateQ_bind]
            erw [simulateQ_pubFsMulti_liftFSMulti_run,
              pubFsMultiImpl_inject_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hpub
                (Function.update tblM sIdx sM1) (by simpa [Function.update_self] using hinjM)]
            simp [withPub, hpm, Function.update_idem, bk', bk1, bk]
      | true =>
        cases hpub : lPubOf protoSignalCodec e.2 with
        | none =>
          have hrec : fs.receive rsLoc hdr e = none :=
            lFS_receive_eq_none_of_lPubOf_none C ℓ encT idOf rsLoc hdr e hpub
          refine ⟨hM, tblM, tblL, rfl, rfl, rfl, rfl,
            fun _ _ => ⟨rfl, rfl, fun hp1 => Bool.noConfusion hp1⟩, ?_⟩
          simp only [hrec]
          refine ⟨?_, fun hp1 => Bool.noConfusion hp1, hinv⟩
          dsimp only [hooksFSMulti]
          simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
            pure_bind, hmatch_dec, Option.isNone_none, Option.isSome_none, hsc, Bool.not_true,
            Bool.and_false, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
          erw [simulateQ_pubFsMulti_liftFSMulti_run,
            pubFsMultiImpl_inject_none_run C ℓ encT idOf false sIdx hdr e.1 e.2 hpub tblM]
          simp
        | some p =>
          have hinj := activeSessInv_inject_phase2 C ℓ encT idOf hinv hsc hdr e hmatch p hpub
          cases hrec : fs.receive rsLoc hdr e with
          | none =>
            dsimp only [fs] at hrec; rw [hrec] at hinj
            rcases hinj with ⟨sM', hinjM, hinv'⟩
            refine ⟨hM, Function.update tblM sIdx sM', tblL, rfl, rfl, rfl, rfl,
              fun j hj => ⟨rfl, Function.update_of_ne hj _ _, fun hp1 => Bool.noConfusion hp1⟩, ?_⟩
            simp only [Function.update_self]
            refine ⟨?_, fun hp1 => Bool.noConfusion hp1, hinv'⟩
            dsimp only [hooksFSMulti]
            simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
              pure_bind, hmatch_dec, Option.isNone_none, Option.isSome_none, hsc, Bool.not_true,
              Bool.and_false, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
            erw [simulateQ_pubFsMulti_liftFSMulti_run,
              pubFsMultiImpl_inject_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hpub tblM hinjM]
            simp [withPub]
          | some rim =>
            rcases rim with ⟨rsLoc', idxOut, pmOut⟩
            dsimp only [fs] at hrec; rw [hrec] at hinj
            rcases hinj with ⟨sM', hinjM, hp_eq, hinv'⟩
            have hpm : (p, pmOut.2) = pmOut := Prod.ext hp_eq.symm rfl
            let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
              { bk with fsTrans := bk.fsTrans.filter (·.1 != idxOut) }
            let hM' := { hM with book := Function.update hM.book sIdx (some bk') }
            refine ⟨hM', Function.update tblM sIdx sM', tblL, rfl, rfl, rfl, rfl,
              fun j hj => ⟨Function.update_of_ne hj _ _, Function.update_of_ne hj _ _,
                fun hp1 => Bool.noConfusion hp1⟩, ?_⟩
            simp only [hM', Function.update_self, Option.getD_some]
            refine ⟨?_, fun hp1 => Bool.noConfusion hp1, hinv'⟩
            dsimp only [hooksFSMulti]
            simp only [hdr_ct_beq_eq_decide, StateT.run_bind, StateT.run_get,
              pure_bind, hmatch_dec, Option.isNone_none, Option.isSome_none, hsc, Bool.not_true,
              Bool.and_false, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
            erw [simulateQ_pubFsMulti_liftFSMulti_run,
              pubFsMultiImpl_inject_some_run C ℓ encT idOf false sIdx hdr e.1 e.2 p hpub tblM hinjM]
            simp [withPub, hpm, bk', bk]

private theorem evalDist_loc_eq_zero_of_rem_zero
    {Γ T Sig SS RS M CCoins E HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hks : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γ Sig (SS × Option ℕ) (RS × Option ℕ))
    (Δcka qep maxSkip l t : ℕ)
    {α : Type} (oa : _root_.CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF
      (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (hq : MakesAtMostQueriesDF oa 0)
    (es : EState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) HS)
    (hwin : es.g.win = false)
    (post : α × EState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) HS → ProbComp Bool)
    (hpost : ∀ a es', es'.g.win = false → 𝒟[post (a, es')] {true} = 0) :
    let mo : Mode := ⟨true, some (l - 1), t⟩
    𝒟[simulateQ lImpl
      ((simulateQ (implEDFShiftedPaper l hks (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es) >>= post]
      {true} = 0 := by
  intro mo
  induction oa using OracleComp.inductionOn generalizing es with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hpost a es hwin
  | query_bind q k ih =>
    rcases q with n | q_game
    · rw [MakesAtMostQueriesDF, isQueryBoundP_query_bind_iff] at hq
      rw [simulateQ_query_bind]
      dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        implEDFShiftedPaper, QueryImpl.add_apply_inl]
      rw [StateT.run_bind, simulateQ_bind, simulateQ_lImpl_coinsE_run, bind_assoc]
      refine evalDist_bind_eq_zero _ _ fun u hu => ?_
      rw [mem_support_bind_iff] at hu
      rcases hu with ⟨v, _, hv⟩
      simp only [support_pure, Set.mem_singleton_iff] at hv
      subst hv
      have hq_k : MakesAtMostQueriesDF (k v) 0 := by
        rcases hq with ⟨_, hk⟩
        simpa [MakesAtMostQueriesDF] using hk v
      exact ih v hq_k es hwin
    · simp [MakesAtMostQueriesDF, isQueryBoundP_query_bind_iff] at hq

private theorem step_coinsE_dir1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (_hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esL tblM tblL)
    (n : unifSpec.Domain)
    (kLoc : unifSpec.Range n → _ → ProbComp Bool)
    (kM kL : unifSpec.Range n → _ → ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hk : ∀ u,
      Dir1Rel phase1 (kLoc u esLoc) (kM u esM (fun _ => false, tblM))
        (kL u esL (fun _ => false, tblL))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inl n)).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inl n)).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inl n)).run esL)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) := by
  intro cka prng fs mo impl
  dsimp only [implEDFShiftedPaper, QueryImpl.add_apply_inl]
  rw [simulateQ_lImpl_coinsE_run, simulateQ_pubFsMulti_coinsE_run, simulateQ_pubFsMulti_coinsE_run]
  simp only [bind_assoc, pure_bind]
  exact dir1Rel_bind _ _ _ _ fun u _ => hk u

private theorem step_challE_dir1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (r_c : Option (BitVec 256))
    (kLoc : Option (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) → _ → ProbComp Bool)
    (kM kL : Option (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) → _ →
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hk : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esL tblM tblL →
      Dir1Rel phase1 (kLoc none esLoc) (kM none esM (fun _ => false, tblM))
        (kL none esL (fun _ => false, tblL))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain :=
      .inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r_c))))))
    Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) := by
  intro cka prng fs mo impl qry
  have hsync' : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esL tblM tblL :=
    { hsync with hsess_rem := by have := hsync.hsess_rem; omega }
  have hchall : ∀ ep, (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn ep = false :=
    fun _ => rfl
  have hloc : simulateQ lImpl
      ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
      pure (none, esLoc) := by
    simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      challE, hsync.habortL, hsync.hwinL, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    cases esLoc.g.epMgmt (2 + Δcka) qep P r_c.isSome <;>
      simp [hchall, StateT.run_pure, simulateQ_pure]
  have hM_run : (simulateQ (pubFsMultiImpl (impl false))
      ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
        (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run (fun _ => false, tblM) =
      pure ((none, esM), (fun _ => false, tblM)) := by
    simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      challE, hsync.habortM, hsync.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    cases esM.g.epMgmt (2 + Δcka) qep P r_c.isSome <;>
      simp [hchall, StateT.run_pure, simulateQ_pure]
  rw [hloc, hM_run, pure_bind, pure_bind]
  cases phase1 with
  | false => exact hk hsync'
  | true =>
    have hL_run : (simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run (fun _ => false, tblL) =
        pure ((none, esL), (fun _ => false, tblL)) := by
      simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        challE, hsync.habortLa rfl, hsync.hwinLa rfl, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind]
      cases esL.g.epMgmt (2 + Δcka) qep P r_c.isSome <;>
        simp [hchall, StateT.run_pure, simulateQ_pure]
    rw [hL_run, pure_bind]
    exact hk hsync'

private theorem afterCorrShifted_props {StL StR Msg C : Type}
    (l : ℕ) (gL : GameState StL Msg C) (gR : GameState StR Msg C) (P : Party)
    (he : eraseSt gL = eraseSt gR) :
    (afterCorrShifted l gL P).win = gL.win ∧
    (afterCorrShifted l gL P).st = gL.st ∧
    (afterCorrShifted l gL P).epoch = gL.epoch ∧
    (afterCorrShifted l gL P).trans = gL.trans ∧
    eraseSt (afterCorrShifted l gL P) = eraseSt (afterCorrShifted l gR P) := by
  have he_ep : gL.epoch = gR.epoch := congrArg GameState.epoch he
  unfold afterCorrShifted
  rw [he_ep]
  split_ifs <;>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩ <;>
    (rcases gL with ⟨st1, b1, win1, ep1, idx1, tL1, tr1, ch1, cp1, ma1, lk1, cr1⟩
     rcases gR with ⟨st2, b2, win2, ep2, idx2, tL2, tr2, ch2, cp2, ma2, lk2, cr2⟩
     simp only [eraseSt, GameState.mk.injEq] at he
     rcases he with ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
     rfl)

private theorem step_corrE_dir1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ) (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party)
    (kLoc : Option (Fig8St Pt) → _ → ProbComp Bool)
    (kM kL : Option (Fig8St Pt) → _ → ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hdead : ∀ res esLoc', LocDead l t esLoc' → 𝒟[kLoc res esLoc'] {true} = 0)
    (hk : ∀ res phase1' esLoc' esM' esL' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem esLoc' esM' esL' tblM' tblL' →
      Dir1Rel phase1' (kLoc res esLoc') (kM res esM' (fun _ => false, tblM'))
        (kL res esL' (fun _ => false, tblL'))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain :=
      .inr (.inl (.inr P))
    Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) := by
  intro cka prng fs mo impl qry
  have hall_eq : esLoc.g.corrAllowedPaper P = esM.g.corrAllowedPaper P :=
    eraseSt_corrAllowedPaper hsync.heraseM P
  cases hallow : esM.g.corrAllowedPaper P with
  | false =>
    have hsync' : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esL tblM tblL :=
      { hsync with hsess_rem := by have := hsync.hsess_rem; omega }
    have hloc : simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
        pure (none, esLoc) := by
      simp [qry, implEDFShiftedPaper, corrEShiftedPaper, hsync.habortL, hsync.hwinL,
        hall_eq, hallow, StateT.run_pure, simulateQ_pure]
    have hM_run : (simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run (fun _ => false, tblM) =
        pure ((none, esM), (fun _ => false, tblM)) := by
      simp [qry, implEDFShiftedPaper, corrEShiftedPaper, hsync.habortM, hsync.hwinM,
        hallow, StateT.run_pure, simulateQ_pure]
    rw [hloc, hM_run, pure_bind, pure_bind]
    cases phase1 with
    | false => exact hk none false esLoc esM esL tblM tblL hsync'
    | true =>
      have hL_run : (simulateQ (pubFsMultiImpl (impl true))
          ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run (fun _ => false, tblL) =
          pure ((none, esL), (fun _ => false, tblL)) := by
        simp [qry, implEDFShiftedPaper, corrEShiftedPaper, hsync.habortLa rfl,
          hsync.heraseLa rfl, hallow, StateT.run_pure, simulateQ_pure]
      rw [hL_run, pure_bind]
      exact hk none true esLoc esM esL tblM tblL hsync'
  | true =>
    let s₁Loc := afterCorrShifted l esLoc.g P
    let s₁M := afterCorrShifted l esM.g P
    rcases afterCorrShifted_props l esLoc.g esM.g P hsync.heraseM with
      ⟨hwin1L, hst1L, hep1L, htr1L, herase1⟩
    rcases afterCorrShifted_props l esM.g esLoc.g P hsync.heraseM.symm with
      ⟨hwin1M, hst1M, hep1M, htr1M, _⟩
    have hdoom_eq :
        (mo.policy.leakDoom esLoc.g s₁Loc || mo.policy.corrDoom esLoc.g P) =
        (mo.policy.leakDoom esM.g s₁M || mo.policy.corrDoom esM.g P) := by
      rw [eraseSt_leakDoom hsync.heraseM herase1, eraseSt_corrDoom hsync.heraseM]
    cases hdoom : (mo.policy.leakDoom esM.g s₁M || mo.policy.corrDoom esM.g P) with
    | true =>
      have hloc : simulateQ lImpl
          ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
          pure (none, { esLoc with abort := true }) := by
        simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          corrEShiftedPaper, hsync.habortL, hsync.hwinL, hall_eq, hallow,
          Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
        change simulateQ lImpl
          ((if (mo.policy.leakDoom esLoc.g s₁Loc || mo.policy.corrDoom esLoc.g P) = true then
              abortE >>= fun _ => pure none
            else _).run esLoc) = _
        rw [hdoom_eq, hdoom]
        simp [abortE, StateT.run_modify, simulateQ_pure]
      rw [hloc, pure_bind]
      exact dir1Rel_of_lhs_zero (hdead none _ (Or.inl rfl))
    | false =>
      have hcorr_f : mo.policy.corrDoom esM.g P = false := by
        revert hdoom; cases mo.policy.leakDoom esM.g s₁M <;> simp
      rcases hsync.hstates with ⟨ssLoc, rsLoc, hact, hss_init, hrs_init, hvp⟩
      rcases hvp P with ⟨hidP, htcurP, hγP, hrootP, hcurP, hvSP, hvRP⟩
      have hno_inr : ∀ ep, ∀ sIdx', (esM.g.st P).vR ep ≠ some (.inr sIdx') := by
        intro ep sIdx' hvr
        have hvp_ep := hvRP ep
        rw [hvr] at hvp_ep
        cases hvRL : (esLoc.g.st P).vR ep with
        | none => rw [hvRL] at hvp_ep; exact hvp_ep
        | some p =>
          rcases p with ⟨rs, _ | idxL⟩
          · rw [hvRL] at hvp_ep; exact hvp_ep
          · rw [hvRL] at hvp_ep
            dsimp only at hvp_ep
            have hP_rec : P = Party.receiverOf t := hvp_ep.2.2.2.2.1
            have htle : t ≤ esM.g.epoch P := by
              have h1 := hvp_ep.2.2.2.2.2
              have h2 : esLoc.g.epoch P = esM.g.epoch P :=
                congrFun (eraseSt_epoch hsync.heraseM) P
              rw [← h2, (hsync.hep_st P).1]; exact h1
            have hc_true : mo.policy.corrDoom esM.g P = true := by
              subst hP_rec
              exact corrDoom_true_of_ge (Δcka := Δcka) (mo := mo) rfl
                (lastLeakGuessAdmissible_dir1 Δcka l t ht3 hl) esM.g htle
            rw [hcorr_f] at hc_true; cases hc_true
      have hvRM_cases : ∀ ep,
          ((esLoc.g.st P).vR ep = none ∧ (esM.g.st P).vR ep = none) ∨
          ∃ rs, (esLoc.g.st P).vR ep = some (rs, none) ∧ (esM.g.st P).vR ep = some (.inl rs) := by
        intro ep
        have hvp_ep := hvRP ep
        cases hvRL : (esLoc.g.st P).vR ep with
        | none =>
          cases hvRM : (esM.g.st P).vR ep with
          | none => exact Or.inl ⟨rfl, rfl⟩
          | some _ => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
        | some pL =>
          rcases pL with ⟨rsL, _ | idxL⟩
          · cases hvRM : (esM.g.st P).vR ep with
            | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
            | some s =>
              rcases s with rsM | idxM
              · rw [hvRL, hvRM] at hvp_ep; dsimp only at hvp_ep
                exact Or.inr ⟨rsL, rfl, congrArg (some ∘ Sum.inl) hvp_ep.1.symm⟩
              · exact False.elim (hno_inr ep idxM hvRM)
          · cases hvRM : (esM.g.st P).vR ep with
            | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
            | some s =>
              rcases s with _ | idxM
              · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
              · exact False.elim (hno_inr ep idxM hvRM)
      cases hvSL : (esLoc.g.st P).vS with
      | none =>
        have hvSM : (esM.g.st P).vS = none := by
          cases hm : (esM.g.st P).vS with
          | none => rfl
          | some _ => rw [hvSL, hm] at hvSP; cases hvSP
        let stOut := realParty (esLoc.g.st P) (esLoc.g.st P).γ (esLoc.g.st P).root
          (none : Option (RatchetSenderState (BitVec 256)))
          (fun ep => ((esLoc.g.st P).vR ep).map Prod.fst)
        let phase1' := healedBy s₁M.tL (2 + Δcka) t
        have hp_imp : phase1' = true → phase1 = true := by
          intro hp1'
          cases hp1 : phase1
          · have hf := healedBy_afterCorrShifted_false (l := l) P
              (hsync.hhealed.trans hp1)
            dsimp only [phase1', s₁M] at hp1'
            rw [hf] at hp1'; cases hp1'
          · rfl
        have hloc : simulateQ lImpl
            ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
            pure (some stOut, { esLoc with g := s₁Loc }) := by
          simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
            corrEShiftedPaper, hsync.habortL, hsync.hwinL, hall_eq, hallow,
            Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
          change simulateQ lImpl
            ((if (mo.policy.leakDoom esLoc.g s₁Loc || mo.policy.corrDoom esLoc.g P) = true then
                abortE >>= fun _ => pure none
              else _).run esLoc) = _
          rw [hdoom_eq, hdoom]
          simp [hooksLocalPrefix, hvSL, stOut, s₁Loc, hsync.habortL,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
        have hM_run : (simulateQ (pubFsMultiImpl (impl false))
            ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run (fun _ => false, tblM) =
            pure ((some stOut, { esM with g := s₁M }), (fun _ => false, tblM)) := by
          simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
            corrEShiftedPaper, hsync.habortM, hsync.hwinM, hallow,
            Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
          change (simulateQ (pubFsMultiImpl (impl false))
            ((if (mo.policy.leakDoom esM.g s₁M || mo.policy.corrDoom esM.g P) = true then
                abortE >>= fun _ => pure none
              else _).run esM)).run (fun _ => false, tblM) = _
          rw [hdoom]
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftH_run, simulateQ_bind]
          dsimp only [hooksFSMulti]
          rcases hvRM_cases mo.tStar with ⟨_, hvRt⟩ | ⟨_, _, hvRt⟩ <;>
          · simp only [hvSM, hvRt, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure, s₁M, hsync.habortM]
            refine congrArg pure (Prod.ext (Prod.ext (congrArg some ?_) rfl) rfl)
            simp only [realParty, stOut, hidP, htcurP, hγP, hrootP, hcurP]
            congr 1; funext ep; rcases hvRM_cases ep with ⟨h1, h2⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
        rw [hloc, hM_run, pure_bind, pure_bind]
        have hsync' : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem
            { esLoc with g := s₁Loc } { esM with g := s₁M } { esL with g := s₁M } tblM tblL :=
          { habortL := hsync.habortL
            habortM := hsync.habortM
            habortLa := fun hp1' => hsync.habortLa (hp_imp hp1')
            hwinL := hwin1L.trans hsync.hwinL
            hwinM := hwin1M.trans hsync.hwinM
            hwinLa := fun _ => hwin1M.trans hsync.hwinM
            hlf := fun hp1' => hsync.hlf (hp_imp hp1')
            heraseM := herase1
            heraseLa := fun _ => rfl
            hh_La := fun hp1' => hsync.hh_La (hp_imp hp1')
            hhealed := rfl
            hginv := by dsimp only; rw [htr1L]; exact hsync.hginv
            hep_st := fun Q => by dsimp only; rw [hep1L, hst1L]; exact hsync.hep_st Q
            hsessM := hsync.hsessM
            hsess_nodup := hsync.hsess_nodup
            hsess_rem := by dsimp only; have := hsync.hsess_rem; omega
            hsess_tH := by dsimp only; rw [hst1L]; exact hsync.hsess_tH
            htbl_loc := hsync.htbl_loc
            htbl_M := hsync.htbl_M
            hcache := hsync.hcache
            hcache_tcur := by dsimp only; rw [hst1L]; exact hsync.hcache_tcur
            hbook_out := hsync.hbook_out
            htbl_out := fun sIdx hs => ⟨(hsync.htbl_out sIdx hs).1,
              fun hp1' => (hsync.htbl_out sIdx hs).2 (hp_imp hp1')⟩
            hstates := ⟨ssLoc, rsLoc,
              fun sIdx hs => activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact sIdx hs),
              by dsimp only; rw [hst1L]; exact hss_init,
              by dsimp only; rw [hst1L]; exact hrs_init,
              fun Q => by dsimp only; rw [hst1L, hst1M]; exact hvp Q⟩ }
        refine dir1Rel_mono_phase hp_imp (fun hp1' => ?_) (hk (some stOut) phase1' _ _ _ _ _ hsync')
        have hp1 := hp_imp hp1'
        have hL_run : (simulateQ (pubFsMultiImpl (impl true))
            ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run (fun _ => false, tblL) =
            pure ((some stOut, { esL with g := s₁M }), (fun _ => false, tblL)) := by
          have hesLg := hsync.heraseLa hp1
          simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
            corrEShiftedPaper, hsync.habortLa hp1, hesLg, hsync.hwinM, hallow,
            Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
          change (simulateQ (pubFsMultiImpl (impl true))
            ((if (mo.policy.leakDoom esM.g s₁M || mo.policy.corrDoom esM.g P) = true then
                abortE >>= fun _ => pure none
              else _).run esL)).run (fun _ => false, tblL) = _
          rw [hdoom]
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftH_run, simulateQ_bind]
          dsimp only [hooksFSMulti]
          rcases hvRM_cases mo.tStar with ⟨_, hvRt⟩ | ⟨_, _, hvRt⟩ <;>
          · simp only [hesLg, hvSM, hvRt, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure, s₁M, hsync.habortLa hp1]
            refine congrArg pure (Prod.ext (Prod.ext (congrArg some ?_) rfl) rfl)
            simp only [realParty, stOut, hidP, htcurP, hγP, hrootP, hcurP]
            congr 1; funext ep; rcases hvRM_cases ep with ⟨h1, h2⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
        rw [hL_run, pure_bind]
      | some pS =>
        rcases pS with ⟨ss, _ | sIdx⟩
        · have hvSM : (esM.g.st P).vS = some (.inl ss) := by
            cases hm : (esM.g.st P).vS with
            | none => rw [hvSL, hm] at hvSP; cases hvSP
            | some x =>
              rcases x with ssM | idxM
              · rw [hvSL, hm] at hvSP; simp [hvSP]
              · rw [hvSL, hm] at hvSP; cases hvSP
          let stOut := realParty (esLoc.g.st P) (esLoc.g.st P).γ (esLoc.g.st P).root (some ss)
            (fun ep => ((esLoc.g.st P).vR ep).map Prod.fst)
          let phase1' := healedBy s₁M.tL (2 + Δcka) t
          have hp_imp : phase1' = true → phase1 = true := by
            intro hp1'
            cases hp1 : phase1
            · have hf := healedBy_afterCorrShifted_false (l := l) P
                (hsync.hhealed.trans hp1)
              dsimp only [phase1', s₁M] at hp1'
              rw [hf] at hp1'; cases hp1'
            · rfl
          have hloc : simulateQ lImpl
              ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
                (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
              pure (some stOut, { esLoc with g := s₁Loc }) := by
            simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
              corrEShiftedPaper, hsync.habortL, hsync.hwinL, hall_eq, hallow,
              Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
            change simulateQ lImpl
              ((if (mo.policy.leakDoom esLoc.g s₁Loc || mo.policy.corrDoom esLoc.g P) = true then
                  abortE >>= fun _ => pure none
                else _).run esLoc) = _
            rw [hdoom_eq, hdoom]
            simp [hooksLocalPrefix, hvSL, stOut, s₁Loc, hsync.habortL,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
          have hM_run : (simulateQ (pubFsMultiImpl (impl false))
              ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
                (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run (fun _ => false, tblM) =
              pure ((some stOut, { esM with g := s₁M }), (fun _ => false, tblM)) := by
            simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
              corrEShiftedPaper, hsync.habortM, hsync.hwinM, hallow,
              Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
            change (simulateQ (pubFsMultiImpl (impl false))
              ((if (mo.policy.leakDoom esM.g s₁M || mo.policy.corrDoom esM.g P) = true then
                  abortE >>= fun _ => pure none
                else _).run esM)).run (fun _ => false, tblM) = _
            rw [hdoom]
            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftH_run, simulateQ_bind]
            dsimp only [hooksFSMulti]
            rcases hvRM_cases mo.tStar with ⟨_, hvRt⟩ | ⟨_, _, hvRt⟩ <;>
            · simp only [hvSM, hvRt, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, simulateQ_pure, s₁M, hsync.habortM]
              refine congrArg pure (Prod.ext (Prod.ext (congrArg some ?_) rfl) rfl)
              simp only [realParty, stOut, hidP, htcurP, hγP, hrootP, hcurP]
              congr 1; funext ep; rcases hvRM_cases ep with ⟨h1, h2⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
          rw [hloc, hM_run, pure_bind, pure_bind]
          have hsync' : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem
              { esLoc with g := s₁Loc } { esM with g := s₁M } { esL with g := s₁M } tblM tblL :=
            { habortL := hsync.habortL
              habortM := hsync.habortM
              habortLa := fun hp1' => hsync.habortLa (hp_imp hp1')
              hwinL := hwin1L.trans hsync.hwinL
              hwinM := hwin1M.trans hsync.hwinM
              hwinLa := fun _ => hwin1M.trans hsync.hwinM
              hlf := fun hp1' => hsync.hlf (hp_imp hp1')
              heraseM := herase1
              heraseLa := fun _ => rfl
              hh_La := fun hp1' => hsync.hh_La (hp_imp hp1')
              hhealed := rfl
              hginv := by dsimp only; rw [htr1L]; exact hsync.hginv
              hep_st := fun Q => by dsimp only; rw [hep1L, hst1L]; exact hsync.hep_st Q
              hsessM := hsync.hsessM
              hsess_nodup := hsync.hsess_nodup
              hsess_rem := by dsimp only; have := hsync.hsess_rem; omega
              hsess_tH := by dsimp only; rw [hst1L]; exact hsync.hsess_tH
              htbl_loc := hsync.htbl_loc
              htbl_M := hsync.htbl_M
              hcache := hsync.hcache
              hcache_tcur := by dsimp only; rw [hst1L]; exact hsync.hcache_tcur
              hbook_out := hsync.hbook_out
              htbl_out := fun sIdx hs => ⟨(hsync.htbl_out sIdx hs).1,
                fun hp1' => (hsync.htbl_out sIdx hs).2 (hp_imp hp1')⟩
              hstates := ⟨ssLoc, rsLoc,
                fun sIdx hs => activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact sIdx hs),
                by dsimp only; rw [hst1L]; exact hss_init,
                by dsimp only; rw [hst1L]; exact hrs_init,
                fun Q => by dsimp only; rw [hst1L, hst1M]; exact hvp Q⟩ }
          refine dir1Rel_mono_phase hp_imp (fun hp1' => ?_) (hk (some stOut) phase1' _ _ _ _ _ hsync')
          have hp1 := hp_imp hp1'
          have hL_run : (simulateQ (pubFsMultiImpl (impl true))
              ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
                (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run (fun _ => false, tblL) =
              pure ((some stOut, { esL with g := s₁M }), (fun _ => false, tblL)) := by
            have hesLg := hsync.heraseLa hp1
            simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
              corrEShiftedPaper, hsync.habortLa hp1, hesLg, hsync.hwinM, hallow,
              Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
            change (simulateQ (pubFsMultiImpl (impl true))
              ((if (mo.policy.leakDoom esM.g s₁M || mo.policy.corrDoom esM.g P) = true then
                  abortE >>= fun _ => pure none
                else _).run esL)).run (fun _ => false, tblL) = _
            rw [hdoom]
            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftH_run, simulateQ_bind]
            dsimp only [hooksFSMulti]
            rcases hvRM_cases mo.tStar with ⟨_, hvRt⟩ | ⟨_, _, hvRt⟩ <;>
            · simp only [hesLg, hvSM, hvRt, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, simulateQ_pure, s₁M, hsync.habortLa hp1]
              refine congrArg pure (Prod.ext (Prod.ext (congrArg some ?_) rfl) rfl)
              simp only [realParty, stOut, hidP, htcurP, hγP, hrootP, hcurP]
              congr 1; funext ep; rcases hvRM_cases ep with ⟨h1, h2⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
          rw [hL_run, pure_bind]
        · have hvSM_ex : (esM.g.st P).vS = some (.inr sIdx) ∧
              sIdx < esLoc.h.sessions.length ∧ ss = ssLoc sIdx ∧
              ((esLoc.g.st P).tcur = t ∨ (esLoc.g.st P).tcur = t + 1) := by
            cases hm : (esM.g.st P).vS with
            | none => rw [hvSL, hm] at hvSP; cases hvSP
            | some x =>
              rcases x with ssM | idxM
              · rw [hvSL, hm] at hvSP; cases hvSP
              · rw [hvSL, hm] at hvSP
                exact ⟨by rw [hvSP.1], hvSP.2.1, hvSP.2.2.1, hvSP.2.2.2.2.1⟩
          rcases hvSM_ex with ⟨hvSM, hs_lt, hss_eq, htcur_or⟩
          have htle : t ≤ esM.g.epoch P := by
            have h2 : esLoc.g.epoch P = esM.g.epoch P :=
              congrFun (eraseSt_epoch hsync.heraseM) P
            rw [← h2, (hsync.hep_st P).1]; omega
          have hhealed_f : healedBy s₁M.tL (2 + Δcka) t = false :=
            healedBy_afterCorrShifted_at_epoch_false (by omega) (by omega) htle
          have hinv0 : ActiveSessInv C ℓ encT idOf false (ks sIdx) (ssLoc sIdx) (rsLoc sIdx)
              ((esM.h.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) :=
            activeSessInv_mono_phase C ℓ encT idOf (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)
              (hact sIdx hs_lt)
          rcases activeSessInv_corruptSender C ℓ encT idOf hinv0 with ⟨sM', hcorrM, hinv'⟩
          let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
            { (esM.h.book sIdx).getD {} with sCorr := true }
          let hM' := { esM.h with book := Function.update esM.h.book sIdx (some bk') }
          let stOut := realParty (esLoc.g.st P) (esLoc.g.st P).γ (esLoc.g.st P).root
            (some (ssLoc sIdx)) (fun ep => ((esLoc.g.st P).vR ep).map Prod.fst)
          have hloc : simulateQ lImpl
              ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
                (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
              pure (some stOut, { esLoc with g := s₁Loc }) := by
            simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
              corrEShiftedPaper, hsync.habortL, hsync.hwinL, hall_eq, hallow,
              Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
            change simulateQ lImpl
              ((if (mo.policy.leakDoom esLoc.g s₁Loc || mo.policy.corrDoom esLoc.g P) = true then
                  abortE >>= fun _ => pure none
                else _).run esLoc) = _
            rw [hdoom_eq, hdoom]
            simp [hooksLocalPrefix, hvSL, hss_eq, stOut, s₁Loc, hsync.habortL,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]
          have hM_run : (simulateQ (pubFsMultiImpl (impl false))
              ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
                (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run (fun _ => false, tblM) =
              pure ((some stOut, { esM with g := s₁M, h := hM' }),
                (fun _ => false, Function.update tblM sIdx sM')) := by
            simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
              corrEShiftedPaper, hsync.habortM, hsync.hwinM, hallow,
              Bool.or_self, Bool.not_true, StateT.run_bind, StateT.run_get, pure_bind]
            change (simulateQ (pubFsMultiImpl (impl false))
              ((if (mo.policy.leakDoom esM.g s₁M || mo.policy.corrDoom esM.g P) = true then
                  abortE >>= fun _ => pure none
                else _).run esM)).run (fun _ => false, tblM) = _
            rw [hdoom]
            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftH_run, simulateQ_bind]
            dsimp only [hooksFSMulti]
            simp only [hvSM, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind]
            erw [simulateQ_pubFsMulti_liftFSMulti_run,
              pubFsMultiImpl_corruptSender_run C ℓ encT idOf sIdx tblM hcorrM]
            erw [bind_assoc, pure_bind, pure_bind]
            dsimp only
            rcases hvRM_cases mo.tStar with ⟨_, hvRt⟩ | ⟨_, _, hvRt⟩ <;>
            · simp only [hvRt, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, simulateQ_pure, hM', bk', s₁M, hsync.habortM]
              refine congrArg pure (Prod.ext (Prod.ext (congrArg some ?_) rfl) rfl)
              simp only [realParty, stOut, hidP, htcurP, hγP, hrootP, hcurP]
              congr 1; funext ep; rcases hvRM_cases ep with ⟨h1, h2⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
          rw [hloc, hM_run, pure_bind, pure_bind]
          refine dir1Rel_to_phase2 ?_
          have hsync' : SyncDir1 C ℓ encT idOf q Δcka l t ks bs false rem
              { esLoc with g := s₁Loc } { esM with g := s₁M, h := hM' } esL
              (Function.update tblM sIdx sM') tblL :=
            { habortL := hsync.habortL
              habortM := hsync.habortM
              habortLa := fun h => Bool.noConfusion h
              hwinL := hwin1L.trans hsync.hwinL
              hwinM := hwin1M.trans hsync.hwinM
              hwinLa := fun h => Bool.noConfusion h
              hlf := fun h => Bool.noConfusion h
              heraseM := herase1
              heraseLa := fun h => Bool.noConfusion h
              hh_La := fun h => Bool.noConfusion h
              hhealed := hhealed_f
              hginv := by dsimp only; rw [htr1L]; exact hsync.hginv
              hep_st := fun Q => by dsimp only; rw [hep1L, hst1L]; exact hsync.hep_st Q
              hsessM := hsync.hsessM
              hsess_nodup := hsync.hsess_nodup
              hsess_rem := by dsimp only; have := hsync.hsess_rem; omega
              hsess_tH := by dsimp only; rw [hst1L]; exact hsync.hsess_tH
              htbl_loc := hsync.htbl_loc
              htbl_M := hsync.htbl_M
              hcache := hsync.hcache
              hcache_tcur := by dsimp only; rw [hst1L]; exact hsync.hcache_tcur
              hbook_out := fun j hj => by
                dsimp only at hj
                have hne : j ≠ sIdx := by omega
                dsimp only [hM']; rw [Function.update_of_ne hne]; exact hsync.hbook_out j hj
              htbl_out := fun j hj => by
                dsimp only at hj
                have hne : j ≠ sIdx := by omega
                exact ⟨(Function.update_of_ne hne _ _).trans (hsync.htbl_out j hj).1,
                  fun h => Bool.noConfusion h⟩
              hstates := ⟨ssLoc, rsLoc,
                fun j hj => by
                  by_cases hjeq : j = sIdx
                  · subst hjeq
                    simpa [hM', bk', Function.update_self] using hinv'
                  · dsimp only [hM']
                    rw [Function.update_of_ne hjeq, Function.update_of_ne hjeq]
                    exact activeSessInv_mono_phase C ℓ encT idOf (fun h => Bool.noConfusion h)
                      (fun h => Bool.noConfusion h) (hact j hj),
                by dsimp only; rw [hst1L]; exact hss_init,
                by dsimp only; rw [hst1L]; exact hrs_init,
                fun Q => by dsimp only; rw [hst1L, hst1M]; exact hvp Q⟩ }
          exact hk (some stOut) false _ _ _ _ _ hsync'


private theorem makesAtMostQueriesDF_inl_step {St Msg Coins C : Type}
    (n : unifSpec.Domain)
    (mx : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Range (Sum.inl n) →
      OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) Bool)
    (rem : ℕ)
    (h : MakesAtMostQueriesDF
      (Bind.bind
        (m := OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C))
        (liftM (OracleSpec.query
          (spec := unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C)
          (Sum.inl n))) mx) rem) :
    ∀ u, MakesAtMostQueriesDF (mx u) rem := by
  unfold MakesAtMostQueriesDF at h ⊢
  rw [_root_.OracleComp.isQueryBoundP_query_bind_iff] at h
  intro u
  simpa using h.2 u

private theorem makesAtMostQueriesDF_inr_zero {St Msg Coins C : Type}
    (q_game : (_root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Domain)
    (mx : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Range (Sum.inr q_game) →
      OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) Bool)
    (h : MakesAtMostQueriesDF
      (Bind.bind
        (m := OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C))
        (liftM (OracleSpec.query
          (spec := unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C)
          (Sum.inr q_game))) mx) 0) :
    False := by
  unfold MakesAtMostQueriesDF at h
  rw [_root_.OracleComp.isQueryBoundP_query_bind_iff] at h
  rcases h.1 with h1 | h2
  · simp at h1
  · omega

private theorem makesAtMostQueriesDF_inr_succ {St Msg Coins C : Type}
    (q_game : (_root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Domain)
    (mx : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Range (Sum.inr q_game) →
      OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) Bool)
    (rem : ℕ)
    (h : MakesAtMostQueriesDF
      (Bind.bind
        (m := OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C))
        (liftM (OracleSpec.query
          (spec := unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C)
          (Sum.inr q_game))) mx) (rem + 1)) :
    ∀ u, MakesAtMostQueriesDF (mx u) rem := by
  unfold MakesAtMostQueriesDF at h ⊢
  rw [_root_.OracleComp.isQueryBoundP_query_bind_iff] at h
  intro u
  simpa using h.2 u

private theorem badSendMsgDF_query_bind_step {St Msg Coins C : Type} (ok : Msg → Bool)
    (qy : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Domain)
    (mx : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Range qy →
      OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) Bool)
    (h : SendMsgsOkDF ok
      (Bind.bind
        (m := OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C))
        (liftM (OracleSpec.query qy)) mx)) :
    _root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF
      (St := St) (Coins := Coins) (C := C) ok qy = false ∧
      ∀ u, SendMsgsOkDF ok (mx u) := by
  unfold SendMsgsOkDF at h ⊢
  rw [_root_.OracleComp.isQueryBoundP_query_bind_iff] at h
  rcases h with ⟨hq0, hmx⟩
  have hbf : _root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF
      (St := St) (Coins := Coins) (C := C) ok qy = false :=
    Bool.eq_false_iff.mpr (hq0.resolve_right (by omega))
  refine ⟨hbf, fun u => ?_⟩
  have hu := hmx u
  simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hu
  exact hu

private theorem implEDFShiftedPaperGen_false_eq {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (l : ℕ) (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip tStar : ℕ) (cfg : Config M) (π : Policy) :
    _root_.CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen false l hk
      Δ qep maxSkip tStar cfg π =
    implEDFShiftedPaper l hk Δ qep maxSkip cfg π := by
  funext qry
  rcases qry with n | (((((q1 | q2) | q3) | q4) | q5) | q6) <;> rfl

private theorem epMgmt_props {StL StR Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (Δ qep : ℕ) (gL : GameState StL Msg C) (gR : GameState StR Msg C) (P : Party) (bad : Bool)
    (he : eraseSt gL = eraseSt gR) :
    (gL.epMgmt Δ qep P bad = none ∧ gR.epMgmt Δ qep P bad = none) ∨
    ∃ s₁L s₁R,
      gL.epMgmt Δ qep P bad = some s₁L ∧
      gR.epMgmt Δ qep P bad = some s₁R ∧
      eraseSt s₁L = eraseSt s₁R ∧
      s₁L.st = gL.st ∧ s₁R.st = gR.st ∧
      s₁L.win = gL.win ∧ s₁R.win = gR.win ∧
      s₁L.trans = gL.trans ∧
      (if P.sendsIn (gL.epoch P + 1) then
        s₁L.epoch = Function.update gL.epoch P (gL.epoch P + 1) ∧
        s₁R.epoch = Function.update gR.epoch P (gR.epoch P + 1)
      else
        s₁L = gL ∧ s₁R = gR) := by
  have hep := eraseSt_epoch he
  have htL := eraseSt_tL he
  unfold GameState.epMgmt GameState.safeCh
  rw [hep, htL]
  by_cases hs : P.sendsIn (gR.epoch P + 1) = true
  · simp only [hs, ↓reduceIte]
    by_cases hq : qep < gR.epoch P + 1
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      right
      refine ⟨_, _, rfl, rfl, ?_⟩
      split_ifs <;> simp [GameState.leak, eraseSt, hep, eraseSt_idx he, htL,
        eraseSt_trans he, eraseSt_chall he, eraseSt_comp he, eraseSt_maxAcc he,
        eraseSt_b he, eraseSt_win he, eraseSt_leaks he, eraseSt_corrs he]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hq : qep < gR.epoch P
    · simp [hq]
    · simp [hq, he, eraseSt_win he]

private theorem startSend_loc_none_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} (cka : CKAScheme (BitVec 256) (DDHSt Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (mo : Mode) (q : ℕ) (ks : ℕ → BitVec 256)
    (ctx : Ctx (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (γ : DDHSt Pt) (σ : BitVec 256)
    (hLoc : LState Pt (BitVec 256) (BitVec 256) Pt) :
    simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).startSend ctx P ep γ σ none).run hLoc) =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun coins =>
        simulateQ lImpl
          (((hooksLocalPrefix cka prng fs mo q ks).startSend ctx P ep γ σ (some coins)).run hLoc)) := by
  dsimp only [hooksLocalPrefix]
  simp only [StateT.run_bind, simulateQ_bind, simulateQ_lImpl_sampleT_run, bind_assoc, pure_bind]

private theorem startSend_fsm_none_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    (cka : CKAScheme (BitVec 256) (DDHSt Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (γ : DDHSt Pt) (σ : BitVec 256)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT)) :
    (simulateQ (pubFsMultiImpl impl)
      (((hooksFSMulti cka prng fs Δcka mo false la).startSend ctx P ep γ σ none).run hM)).run st =
      (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun coins =>
        (simulateQ (pubFsMultiImpl impl)
          (((hooksFSMulti cka prng fs Δcka mo false la).startSend ctx P ep γ σ (some coins)).run hM)).run st) := by
  dsimp only [hooksFSMulti]
  simp only [StateT.run_bind, simulateQ_bind, simulateQ_pubFsMulti_sampleT_run, bind_assoc,
    pure_bind, StateT.run_pure, simulateQ_pure]

private theorem startSend_loc_some_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} (cka : CKAScheme (BitVec 256) (DDHSt Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (mo : Mode) (q : ℕ) (ks : ℕ → BitVec 256)
    (ctx : Ctx (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (γ : DDHSt Pt) (σ : BitVec 256) (coins : BitVec 256)
    (hLoc : LState Pt (BitVec 256) (BitVec 256) Pt) :
    simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).startSend ctx P ep γ σ (some coins)).run hLoc) =
      (simulateQ lImpl (((rootLPrefix (T := Pt) prng mo q ks ep (cka.send γ coins).2.2 σ >>= fun r =>
          regSessOf r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hLoc) >>= fun w =>
        let c := cka.send γ coins
        pure (some (c.1, c.2.1, w.1.1, (fs.initSender w.1.2.1, w.1.2.2)),
          { w.2 with cache := Function.update w.2.cache ep (some (c.2.1, w.1.1, w.1.2.1, w.1.2.2)) })) := by
  dsimp only [hooksLocalPrefix]
  simp only [StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, bind_assoc,
    simulateQ_bind, simulateQ_pure]

private theorem startSend_fsm_some_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    (cka : CKAScheme (BitVec 256) (DDHSt Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (γ : DDHSt Pt) (σ : BitVec 256) (coins : BitVec 256)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT)) :
    (simulateQ (pubFsMultiImpl impl)
      (((hooksFSMulti cka prng fs Δcka mo false la).startSend ctx P ep γ σ (some coins)).run hM)).run st =
      ((simulateQ (pubFsMultiImpl impl) (((rootFSMulti
          (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (T := Pt) (M := LibsignalMsgPublicPart × Plain ℓ)
          (E := ℕ × LibsignalCiphertextWithSalt32)
          prng mo ep (cka.send γ coins).2.2 σ >>= fun r =>
          regSessOptMulti r.2.2 >>= fun idx? => pure (r.1, r.2.1, idx?))).run hM)).run st >>= fun w =>
        let c := cka.send γ coins
        let ssv : RatchetSenderState (BitVec 256) ⊕ ℕ :=
          match w.1.1.2.2 with
          | none => .inl (fs.initSender w.1.1.2.1)
          | some sIdx => .inr sIdx
        pure ((some (c.1, c.2.1, w.1.1.1, ssv),
          { w.1.2 with cache := Function.update w.1.2.cache ep (some (c.2.1, w.1.1.1, w.1.1.2.1, w.1.1.2.2)) }),
          w.2)) := by
  dsimp only [hooksFSMulti]
  simp only [StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, bind_assoc,
    simulateQ_bind, simulateQ_pure]
  congr 1

private theorem syncDir1_record {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 phase1' : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (s₁Loc : GameState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
    (s₁M : GameState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))
    (herase1 : eraseSt s₁Loc = eraseSt s₁M)
    (hst1L : s₁Loc.st = esLoc.g.st) (hst1M : s₁M.st = esM.g.st)
    (hwin1L : s₁Loc.win = false) (hwin1M : s₁M.win = false)
    (htr1L : s₁Loc.trans = esLoc.g.trans)
    (hep1_other : ∀ Q, Q ≠ P → s₁Loc.epoch Q = esLoc.g.epoch Q)
    (hhealed1 : healedBy s₁M.tL (2 + Δcka) t = phase1')
    (ssLoc rsLoc : ℕ → _)
    (hvp : ∀ Q, (esLoc.g.st Q).id = (esM.g.st Q).id ∧
      (esLoc.g.st Q).tcur = (esM.g.st Q).tcur ∧
      (esLoc.g.st Q).γ = (esM.g.st Q).γ ∧
      (esLoc.g.st Q).root = (esM.g.st Q).root ∧
      (esLoc.g.st Q).curCkaMsg = (esM.g.st Q).curCkaMsg ∧
      (match (esLoc.g.st Q).vS, (esM.g.st Q).vS with
       | none, none => True
       | some (ss, none), some (.inl ssM) => ss = ssM
       | some (ss, some sIdx), some (.inr sIdxM) =>
         sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ ss = ssLoc sIdx ∧
         Q = Party.senderOf t ∧
         ((esLoc.g.st Q).tcur = t ∨ (esLoc.g.st Q).tcur = t + 1) ∧
         (∀ R sIdx', (esM.g.st R).vS = some (.inr sIdx') → R = Q ∧ sIdx' = sIdx)
       | _, _ => False) ∧
      (∀ ep, match (esLoc.g.st Q).vR ep, (esM.g.st Q).vR ep with
       | none, none => True
       | some (rs, none), some (.inl rsM) => rs = rsM ∧ ep ≠ t
       | some (rs, some sIdx), some (.inr sIdxM) =>
         ep = t ∧ sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ rs = rsLoc sIdx ∧
         Q = Party.receiverOf t ∧ t ≤ (esLoc.g.st Q).tcur
       | _, _ => False))
    (vpL' : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
    (vpM' : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (c_out : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (hLoc' : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM' tblL' : ℕ → SessHSt Pt ℓ)
    (ssLoc' : ℕ → RatchetSenderState (BitVec 256))
    (rsLoc' : ℕ → RatchetReceiverState (BitVec 256) (BitVec 256))
    (hc_ep : c_out.1.1 = s₁Loc.epoch P)
    (hvpL_ep : vpL'.tcur = s₁Loc.epoch P ∧ vpL'.id = P)
    (hvp_ge : (esLoc.g.st P).tcur ≤ vpL'.tcur)
    (hlf' : phase1' = true → hM'.lfWin = false)
    (hsessM' : hM'.sessions = hLoc'.sessions)
    (hsess_nodup' : hLoc'.sessions.Nodup)
    (hsess_rem' : hLoc'.sessions.length + rem ≤ q)
    (hlen_le : esLoc.h.sessions.length ≤ hLoc'.sessions.length)
    (hsess_tH' : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH →
      (Function.update esLoc.g.st P vpL' (Party.senderOf t)).tcur < t → hLoc'.sessions = [])
    (htbl_loc' : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, hLoc'.table.lookup Ik =
        if Ik ∈ hLoc'.sessions then some (ks (hLoc'.sessions.idxOf Ik)) else none)
    (htbl_M' : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, (hM'.table.lookup Ik).isSome = decide (Ik ∈ hM'.sessions))
    (hcache' : ∀ ep, match hLoc'.cache ep, hM'.cache ep with
      | none, none => True
      | some (TcL, σL, kL, idxL?), some (TcM, σM, kM, idxM?) =>
        TcL = TcM ∧ σL = σM ∧ idxL? = idxM? ∧
        match idxL? with
        | none => kL = kM ∧ ep ≠ t
        | some sIdx => ep = t ∧ sIdx < hLoc'.sessions.length ∧ kL = ks sIdx
      | _, _ => False)
    (hcache_tcur' : (Function.update esLoc.g.st P vpL' (Party.senderOf t)).tcur < t → hLoc'.cache t = none)
    (hbook_out' : ∀ sIdx, hLoc'.sessions.length ≤ sIdx → hM'.book sIdx = none)
    (htbl_out' : ∀ sIdx, hLoc'.sessions.length ≤ sIdx →
      tblM' sIdx = hInit (bs sIdx) (.seed (ks sIdx)) ∧
      (phase1' = true → tblL' sIdx = hInit (bs sIdx) (.seed (ks sIdx))))
    (hact' : ∀ sIdx, sIdx < hLoc'.sessions.length →
      ActiveSessInv C ℓ encT idOf phase1' (ks sIdx) (ssLoc' sIdx) (rsLoc' sIdx)
        ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL' sIdx))
    (hss_init' : (Function.update esLoc.g.st P vpL' (Party.senderOf t)).tcur < t →
      ∀ sIdx, sIdx < hLoc'.sessions.length →
        ssLoc' sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender (ks sIdx))
    (hrs_init' : (Function.update esLoc.g.st P vpL' (Party.receiverOf t)).tcur < t →
      ∀ sIdx, sIdx < hLoc'.sessions.length →
        rsLoc' sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver (ks sIdx))
    (hrs_keep : ∀ j, j < esLoc.h.sessions.length → rsLoc' j = rsLoc j)
    (hss_keep_or_sender : (P = Party.senderOf t) ∨
      ((∀ j, j < esLoc.h.sessions.length → ssLoc' j = ssLoc j) ∧
       (∀ idx', vpM'.vS ≠ some (.inr idx'))))
    (hvpP_fields : vpL'.id = vpM'.id ∧ vpL'.tcur = vpM'.tcur ∧ vpL'.γ = vpM'.γ ∧
      vpL'.root = vpM'.root ∧ vpL'.curCkaMsg = vpM'.curCkaMsg ∧
      vpL'.vR = (esLoc.g.st P).vR ∧ vpM'.vR = (esM.g.st P).vR)
    (hvpP_vS : match vpL'.vS, vpM'.vS with
      | none, none => True
      | some (ss, none), some (.inl ssM) => ss = ssM
      | some (ss, some sIdx), some (.inr sIdxM) =>
        sIdx = sIdxM ∧ sIdx < hLoc'.sessions.length ∧ ss = ssLoc' sIdx ∧
        P = Party.senderOf t ∧ (vpL'.tcur = t ∨ vpL'.tcur = t + 1)
      | _, _ => False) :
    let recL : _root_.CryptoGames.SM.Record _ _ :=
      ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, c_out⟩
    let recM : _root_.CryptoGames.SM.Record _ _ :=
      ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, c_out⟩
    SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem
      { g := s₁Loc.record (2 + Δcka) P vpL' recL false, h := hLoc', abort := false }
      { g := s₁M.record (2 + Δcka) P vpM' recM false, h := hM', abort := false }
      { g := s₁M.record (2 + Δcka) P vpM' recM false, h := hM', abort := false }
      tblM' tblL' := by
  intro recL recM
  have hrec_eq : recL = recM := by
    simp only [recL, recM, eraseSt_epoch herase1, eraseSt_idx herase1]
  refine
    { habortL := rfl
      habortM := rfl
      habortLa := fun _ => rfl
      hwinL := by simp [GameState.record, hwin1L]
      hwinM := by simp [GameState.record, hwin1M]
      hwinLa := fun _ => by simp [GameState.record, hwin1M]
      hlf := hlf'
      heraseM := by rw [hrec_eq]; exact eraseSt_record herase1 (2 + Δcka) P vpL' vpM' recM false
      heraseLa := fun _ => rfl
      hh_La := fun _ => rfl
      hhealed := by simpa [GameState.record] using hhealed1
      hginv := by
        intro r hr
        simp only [GameState.record, htr1L, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hc_ep
        · exact hsync.hginv r hr
      hep_st := fun Q => by
        simp only [GameState.record, hst1L]
        by_cases hQP : Q = P
        · subst hQP; simp [Function.update_self, hvpL_ep.1, hvpL_ep.2]
        · simp [Function.update_of_ne hQP, hep1_other Q hQP, hsync.hep_st Q]
      hsessM := hsessM'
      hsess_nodup := hsess_nodup'
      hsess_rem := hsess_rem'
      hsess_tH := by simpa [GameState.record, hst1L] using hsess_tH'
      htbl_loc := htbl_loc'
      htbl_M := by dsimp only; rw [← hsessM']; exact htbl_M'
      hcache := hcache'
      hcache_tcur := by simpa [GameState.record, hst1L] using hcache_tcur'
      hbook_out := hbook_out'
      htbl_out := htbl_out'
      hstates := ⟨ssLoc', rsLoc', hact',
        by simpa [GameState.record, hst1L] using hss_init',
        by simpa [GameState.record, hst1L] using hrs_init',
        fun Q => ?_⟩ }
  simp only [GameState.record, hst1L, hst1M]
  by_cases hQP : Q = P
  · subst hQP
    simp only [Function.update_self]
    refine ⟨hvpP_fields.1, hvpP_fields.2.1, hvpP_fields.2.2.1, hvpP_fields.2.2.2.1,
      hvpP_fields.2.2.2.2.1, ?_, ?_⟩
    · cases hvSL' : vpL'.vS with
      | none =>
        cases hvSM' : vpM'.vS with
        | none => trivial
        | some _ => rw [hvSL', hvSM'] at hvpP_vS; exact False.elim hvpP_vS
      | some pS =>
        rcases pS with ⟨ss, _ | sIdx⟩
        · cases hvSM' : vpM'.vS with
          | none => rw [hvSL', hvSM'] at hvpP_vS; exact False.elim hvpP_vS
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL', hvSM'] at hvpP_vS; exact hvpP_vS
            · rw [hvSL', hvSM'] at hvpP_vS; exact False.elim hvpP_vS
        · cases hvSM' : vpM'.vS with
          | none => rw [hvSL', hvSM'] at hvpP_vS; exact False.elim hvpP_vS
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL', hvSM'] at hvpP_vS; exact False.elim hvpP_vS
            · rw [hvSL', hvSM'] at hvpP_vS
              dsimp only at hvpP_vS
              refine ⟨hvpP_vS.1, hvpP_vS.2.1, hvpP_vS.2.2.1, hvpP_vS.2.2.2.1, hvpP_vS.2.2.2.2, ?_⟩
              intro R idx' hR
              by_cases hRQ : R = Q
              · subst hRQ
                simp only [Function.update_self, hvSM', Option.some.injEq, Sum.inr.injEq] at hR
                exact ⟨rfl, hR.symm.trans hvpP_vS.1.symm⟩
              · simp only [Function.update_of_ne hRQ] at hR
                have hvSR := (hvp R).2.2.2.2.2.1
                rw [hR] at hvSR
                cases hvSLR : (esLoc.g.st R).vS with
                | none => rw [hvSLR] at hvSR; exact False.elim hvSR
                | some pR =>
                  rcases pR with ⟨ssR, _ | idxR⟩
                  · rw [hvSLR] at hvSR; exact False.elim hvSR
                  · rw [hvSLR] at hvSR
                    dsimp only at hvSR
                    exact False.elim (hRQ (hvSR.2.2.2.1.trans hvpP_vS.2.2.2.1.symm))
    · intro ep
      rw [hvpP_fields.2.2.2.2.2.1, hvpP_fields.2.2.2.2.2.2]
      have hvp_ep := (hvp Q).2.2.2.2.2.2 ep
      cases hvRL : (esLoc.g.st Q).vR ep with
      | none =>
        cases hvRM : (esM.g.st Q).vR ep with
        | none => trivial
        | some _ => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
      | some pL =>
        rcases pL with ⟨rs, _ | sIdx⟩
        · cases hvRM : (esM.g.st Q).vR ep with
          | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
          | some x =>
            rcases x with rsM | idxM
            · rw [hvRL, hvRM] at hvp_ep; exact hvp_ep
            · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
        · cases hvRM : (esM.g.st Q).vR ep with
          | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
          | some x =>
            rcases x with rsM | idxM
            · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
            · rw [hvRL, hvRM] at hvp_ep
              dsimp only at hvp_ep ⊢
              exact ⟨hvp_ep.1, hvp_ep.2.1, lt_of_lt_of_le hvp_ep.2.2.1 hlen_le,
                hvp_ep.2.2.2.1.trans (hrs_keep sIdx hvp_ep.2.2.1).symm,
                hvp_ep.2.2.2.2.1, le_trans hvp_ep.2.2.2.2.2 hvp_ge⟩
  · simp only [Function.update_of_ne hQP]
    rcases hvp Q with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
    · cases hvSL : (esLoc.g.st Q).vS with
      | none =>
        cases hvSM : (esM.g.st Q).vS with
        | none => trivial
        | some _ => rw [hvSL, hvSM] at h6; exact False.elim h6
      | some pS =>
        rcases pS with ⟨ss, _ | sIdx⟩
        · cases hvSM : (esM.g.st Q).vS with
          | none => rw [hvSL, hvSM] at h6; exact False.elim h6
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL, hvSM] at h6; exact h6
            · rw [hvSL, hvSM] at h6; exact False.elim h6
        · cases hvSM : (esM.g.st Q).vS with
          | none => rw [hvSL, hvSM] at h6; exact False.elim h6
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL, hvSM] at h6; exact False.elim h6
            · rw [hvSL, hvSM] at h6
              dsimp only at h6 ⊢
              rcases hss_keep_or_sender with hPs | ⟨hss_keep, hno_inr⟩
              · exact False.elim (hQP (h6.2.2.2.1.trans hPs.symm))
              · refine ⟨h6.1, lt_of_lt_of_le h6.2.1 hlen_le,
                  h6.2.2.1.trans (hss_keep sIdx h6.2.1).symm,
                  h6.2.2.2.1, h6.2.2.2.2.1, ?_⟩
                intro R idx' hR
                by_cases hRP : R = P
                · subst hRP
                  simp only [Function.update_self] at hR
                  exact False.elim (hno_inr idx' hR)
                · simp only [Function.update_of_ne hRP] at hR
                  exact h6.2.2.2.2.2 R idx' hR
    · intro ep
      have hvp_ep := h7 ep
      cases hvRL : (esLoc.g.st Q).vR ep with
      | none =>
        cases hvRM : (esM.g.st Q).vR ep with
        | none => trivial
        | some _ => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
      | some pL =>
        rcases pL with ⟨rs, _ | sIdx⟩
        · cases hvRM : (esM.g.st Q).vR ep with
          | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
          | some x =>
            rcases x with rsM | idxM
            · rw [hvRL, hvRM] at hvp_ep; exact hvp_ep
            · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
        · cases hvRM : (esM.g.st Q).vR ep with
          | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
          | some x =>
            rcases x with rsM | idxM
            · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
            · rw [hvRL, hvRM] at hvp_ep
              dsimp only at hvp_ep ⊢
              exact ⟨hvp_ep.1, hvp_ep.2.1, lt_of_lt_of_le hvp_ep.2.2.1 hlen_le,
                hvp_ep.2.2.2.1.trans (hrs_keep sIdx hvp_ep.2.2.1).symm,
                hvp_ep.2.2.2.2.1, hvp_ep.2.2.2.2.2⟩

private theorem step_transmitE_dir1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ) (hq_pos : 0 < q) (_ht3 : 2 + Δcka ≤ t) (_hl : l = t - (1 + Δcka))
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (hshort : m.1.shortB = true)
    (r_c : Option (BitVec 256))
    (kLoc : Option (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) → _ → ProbComp Bool)
    (kM kL : Option (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) → _ →
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hdead : ∀ res esLoc', LocDead l t esLoc' → 𝒟[kLoc res esLoc'] {true} = 0)
    (hk : ∀ res phase1' esLoc' esM' esL' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem esLoc' esM' esL' tblM' tblL' →
      Dir1Rel phase1' (kLoc res esLoc') (kM res esM' (fun _ => false, tblM'))
        (kL res esL' (fun _ => false, tblL'))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain :=
      .inr (.inl (.inl (.inl (.inl (.inl (P, m, r_c))))))
    Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) := by
  intro cka prng fs mo impl qry
  rcases epMgmt_props (2 + Δcka) qep esLoc.g esM.g P r_c.isSome hsync.heraseM with
    ⟨hepL, hepM⟩ | ⟨s₁Loc, s₁M, hepL, hepM, herase1, hst1L, hst1M, hwin1L, hwin1M, htr1L, hep_if⟩
  · have hsync' : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esL tblM tblL :=
      { hsync with hsess_rem := by have := hsync.hsess_rem; omega }
    have hloc : simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
        pure (none, esLoc) := by
      simp [qry, implEDFShiftedPaper, transmitE, hsync.habortL, hsync.hwinL, hepL,
        StateT.run_pure, simulateQ_pure]
    have hM_run : (simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run (fun _ => false, tblM) =
        pure ((none, esM), (fun _ => false, tblM)) := by
      simp [qry, implEDFShiftedPaper, transmitE, hsync.habortM, hsync.hwinM, hepM,
        StateT.run_pure, simulateQ_pure]
    rw [hloc, hM_run, pure_bind, pure_bind]
    cases phase1 with
    | false => exact hk none false esLoc esM esL tblM tblL hsync'
    | true =>
      have hL_run : (simulateQ (pubFsMultiImpl (impl true))
          ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run (fun _ => false, tblL) =
          pure ((none, esL), (fun _ => false, tblL)) := by
        simp [qry, implEDFShiftedPaper, transmitE, hsync.habortLa rfl,
          hsync.heraseLa rfl, hepM, StateT.run_pure, simulateQ_pure]
      rw [hL_run, pure_bind]
      exact hk none true esLoc esM esL tblM tblL hsync'
  · have hwin1L_f : s₁Loc.win = false := hwin1L.trans hsync.hwinL
    have hwin1M_f : s₁M.win = false := hwin1M.trans hsync.hwinM
    have hld_eq : mo.policy.leakDoom esLoc.g s₁Loc = mo.policy.leakDoom esM.g s₁M :=
      eraseSt_leakDoom hsync.heraseM herase1 mo.policy
    cases hld : mo.policy.leakDoom esM.g s₁M with
    | true =>
      have hloc : simulateQ lImpl
          ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
          pure (none, { esLoc with abort := true }) := by
        simp [qry, implEDFShiftedPaper, transmitE, hsync.habortL, hsync.hwinL, hepL,
          hld_eq, hld, abortE, StateT.run_modify, simulateQ_pure]
      rw [hloc, pure_bind]
      exact dir1Rel_of_lhs_zero (hdead none _ (Or.inl rfl))
    | false =>
      let phase1' := healedBy s₁M.tL (2 + Δcka) t
      have hp_imp : phase1' = true → phase1 = true := by
        intro hp1'
        cases hp1 : phase1
        · have hf := healedBy_epMgmt_false (hsync.hhealed.trans hp1) hepM
          dsimp only [phase1'] at hp1'
          rw [hf] at hp1'; cases hp1'
        · rfl
      refine dir1Rel_mono_phase (cL' := (simulateQ (pubFsMultiImpl (impl true))
          ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run
            { g := esM.g, h := esM.h, abort := false })).run
          (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) hp_imp
        (fun hp1' => by
          have hp1 := hp_imp hp1'
          have hgL := hsync.heraseLa hp1
          have hhL := hsync.hh_La hp1
          have habL := hsync.habortLa hp1
          have hesL_eq : esL = { g := esM.g, h := esM.h, abort := false } := by
            cases esL; dsimp only at hgL hhL habL; subst hgL hhL habL; rfl
          rw [hesL_eq]) ?_
      rcases hsync.hstates with ⟨ssLoc, rsLoc, hact, hss_init, hrs_init, hvp⟩
      rcases hvp P with ⟨hidP, htcurP, hγP, hrootP, hcurP, hvSP, hvRP⟩
      have hidL : (esLoc.g.st P).id = P := (hsync.hep_st P).2
      have hidM : (esM.g.st P).id = P := hidP.symm.trans hidL
      have htcur_ep : (esLoc.g.st P).tcur = esLoc.g.epoch P := (hsync.hep_st P).1.symm
      have hloc_step : simulateQ lImpl
          ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) =
          (simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
              s₁Loc P (esLoc.g.st P) m none r_c).run esLoc.h) >>= fun w =>
            match w.1 with
            | none => pure (none, { esLoc with h := w.2, abort := true })
            | some (st', c_out) =>
              pure (some c_out,
                { g := s₁Loc.record (2 + Δcka) P st'
                    ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, c_out⟩ false,
                  h := w.2, abort := false })) := by
        simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          transmitE, hsync.habortL, hsync.hwinL, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, pure_bind, hepL, hld_eq, hld, liftH_run, hst1L,
          bind_assoc, simulateQ_bind]
        congr 1; funext w
        rcases w with ⟨_ | ⟨st', c_out⟩, h'⟩ <;>
          simp [abortE, StateT.run_modify, simulateQ_pure]
      have hFM_step : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
          (simulateQ (pubFsMultiImpl (impl la))
            ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false la)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run
              { g := esM.g, h := esM.h, abort := false })).run (fun _ => false, tbl) =
          ((simulateQ (pubFsMultiImpl (impl la))
              ((vSend (hooksFSMulti cka prng fs Δcka mo false la)
                s₁M P (esM.g.st P) m none r_c).run esM.h)).run (fun _ => false, tbl) >>= fun w =>
            match w.1.1 with
            | none => pure ((none, { g := esM.g, h := w.1.2, abort := true }), w.2)
            | some (st', c_out) =>
              pure ((some c_out,
                { g := s₁M.record (2 + Δcka) P st'
                    ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, c_out⟩ false,
                  h := w.1.2, abort := false }), w.2)) := by
        intro la tbl
        simp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          transmitE, hsync.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, pure_bind, hepM, hld, liftH_run, hst1M,
          bind_assoc, simulateQ_bind]
        congr 1; funext w
        rcases w with ⟨⟨_ | ⟨st', c_out⟩, h'⟩, st_tbl⟩ <;>
          simp [abortE, StateT.run_modify, StateT.run_pure, simulateQ_pure]
      have hesM_self : esM = { g := esM.g, h := esM.h, abort := false } := by
        have habM := hsync.habortM
        cases esM; dsimp only at habM; subst habM; rfl
      rw [hloc_step, hesM_self, hFM_step false tblM, hFM_step true tblL,
        bind_assoc, bind_assoc, bind_assoc]
      by_cases hsend : P.sendsIn (esLoc.g.epoch P + 1) = true
      · simp only [hsend, ↓reduceIte] at hep_if
        rcases hep_if with ⟨hep1L, hep1M⟩
        let ep := (esLoc.g.st P).tcur + 1
        have hep_eq : esLoc.g.epoch P + 1 = ep := by dsimp only [ep]; rw [htcur_ep]
        have hs1L_epP : s₁Loc.epoch P = ep := by rw [hep1L, Function.update_self, hep_eq]
        have hs1M_epP : s₁M.epoch P = ep := by
          rw [hep1M, Function.update_self, ← congrFun (eraseSt_epoch hsync.heraseM) P, hep_eq]
        have hep1_other : ∀ Q, Q ≠ P → s₁Loc.epoch Q = esLoc.g.epoch Q := fun Q hQP => by
          rw [hep1L, Function.update_of_ne hQP]
        have hsendL : (esLoc.g.st P).id.sendsIn ((esLoc.g.st P).tcur + 1) = true := by
          rw [hidL, htcur_ep]; exact hsend
        have hsendM : (esM.g.st P).id.sendsIn ep = true := by
          dsimp only [ep]; rw [hidM, htcur_ep]; exact hsend
        have hvSend_loc : ∀ rOpt,
            simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
              s₁Loc P (esLoc.g.st P) m none rOpt).run esLoc.h) =
            (simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).startSend
                s₁Loc P ep (esLoc.g.st P).γ (esLoc.g.st P).root rOpt).run esLoc.h) >>= fun u =>
              match u.1 with
              | none => pure (none, u.2)
              | some (γ', T', σ', ssv) =>
                let o := fs.send ssv.1 (ep, some T') m
                pure (some ({ esLoc.g.st P with
                    tcur := ep, γ := γ', curCkaMsg := some T', root := σ',
                    vS := some (o.1, ssv.2) },
                  ((ep, some T'), o.2)), u.2)) := by
          intro rOpt
          unfold vSend
          simp only [hsendL, ↓reduceIte, StateT.run_bind, simulateQ_bind]
          congr 1; funext u
          rcases u with ⟨_ | ⟨γ', T', σ', ssv⟩, h'⟩
          · simp [StateT.run_pure, simulateQ_pure]
          · simp [hooksLocalPrefix, ep, StateT.run_pure, pure_bind, simulateQ_pure]
        have hvSend_fsm : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ) rOpt,
            (simulateQ (pubFsMultiImpl (impl la)) ((vSend (hooksFSMulti cka prng fs Δcka mo false la)
              s₁M P (esM.g.st P) m none rOpt).run esM.h)).run (fun _ => false, tbl) =
            ((simulateQ (pubFsMultiImpl (impl la)) (((hooksFSMulti cka prng fs Δcka mo false la).startSend
                s₁M P ep (esLoc.g.st P).γ (esLoc.g.st P).root rOpt).run esM.h)).run (fun _ => false, tbl) >>= fun u =>
              match u.1.1 with
              | none => pure ((none, u.1.2), u.2)
              | some (γ', T', σ', ssv) =>
                ((simulateQ (pubFsMultiImpl (impl la))
                  (((hooksFSMulti cka prng fs Δcka mo false la).fsSend
                    s₁M P ep ssv (ep, some T') m none).run u.1.2)).run u.2 >>= fun v =>
                  match v.1.1 with
                  | none => pure ((none, v.1.2), v.2)
                  | some (ssv', e_out) =>
                    pure ((some ({ esM.g.st P with
                        tcur := ep, γ := γ', curCkaMsg := some T', root := σ',
                        vS := some ssv' },
                      ((ep, some T'), e_out)), v.1.2), v.2))) := by
          intro la tbl rOpt
          unfold vSend
          have htcurM : (esM.g.st P).tcur + 1 = ep := by dsimp only [ep]; rw [← htcurP]
          simp only [htcurM, hsendM, ↓reduceIte, ← hγP, ← hrootP,
            StateT.run_bind, simulateQ_bind]
          congr 1; funext u
          rcases u with ⟨⟨_ | ⟨γ', T', σ', ssv⟩, h'⟩, st_tbl⟩
          · simp [StateT.run_pure, simulateQ_pure]
          · simp only [pure_bind, StateT.run_bind, simulateQ_bind]
            congr 1; funext v
            rcases v with ⟨⟨_ | ⟨ssv', e_out⟩, h''⟩, st_tbl'⟩ <;>
              simp [StateT.run_pure, simulateQ_pure]
        suffices hcoins : ∀ coins : BitVec 256,
            Dir1Rel phase1'
              (simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
                  s₁Loc P (esLoc.g.st P) m none (some coins)).run esLoc.h) >>= fun w =>
                (match w.1 with
                | none => pure (none, { esLoc with h := w.2, abort := true })
                | some (st', c_out) =>
                  pure (some c_out,
                    { g := s₁Loc.record (2 + Δcka) P st'
                        ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, c_out⟩ false,
                      h := w.2, abort := false })) >>= fun z => kLoc z.1 z.2)
              ((simulateQ (pubFsMultiImpl (impl false))
                  ((vSend (hooksFSMulti cka prng fs Δcka mo false false)
                    s₁M P (esM.g.st P) m none (some coins)).run esM.h)).run (fun _ => false, tblM) >>= fun w =>
                (match w.1.1 with
                | none => pure ((none, { g := esM.g, h := w.1.2, abort := true }), w.2)
                | some (st', c_out) =>
                  pure ((some c_out,
                    { g := s₁M.record (2 + Δcka) P st'
                        ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, c_out⟩ false,
                      h := w.1.2, abort := false }), w.2)) >>= fun z => kM z.1.1 z.1.2 z.2)
              ((simulateQ (pubFsMultiImpl (impl true))
                  ((vSend (hooksFSMulti cka prng fs Δcka mo false true)
                    s₁M P (esM.g.st P) m none (some coins)).run esM.h)).run (fun _ => false, tblL) >>= fun w =>
                (match w.1.1 with
                | none => pure ((none, { g := esM.g, h := w.1.2, abort := true }), w.2)
                | some (st', c_out) =>
                  pure ((some c_out,
                    { g := s₁M.record (2 + Δcka) P st'
                        ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, c_out⟩ false,
                      h := w.1.2, abort := false }), w.2)) >>= fun z => kL z.1.1 z.1.2 z.2) by
          cases r_c with
          | some coins => exact hcoins coins
          | none =>
            have hvL_none : simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
                s₁Loc P (esLoc.g.st P) m none none).run esLoc.h) =
                (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun coins =>
                  simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
                    s₁Loc P (esLoc.g.st P) m none (some coins)).run esLoc.h)) := by
              rw [hvSend_loc none, startSend_loc_none_eq, bind_assoc]
              congr 1; funext coins; rw [hvSend_loc (some coins)]
            have hvM_none : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
                (simulateQ (pubFsMultiImpl (impl la)) ((vSend (hooksFSMulti cka prng fs Δcka mo false la)
                  s₁M P (esM.g.st P) m none none).run esM.h)).run (fun _ => false, tbl) =
                (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun coins =>
                  (simulateQ (pubFsMultiImpl (impl la)) ((vSend (hooksFSMulti cka prng fs Δcka mo false la)
                    s₁M P (esM.g.st P) m none (some coins)).run esM.h)).run (fun _ => false, tbl)) := by
              intro la tbl
              rw [hvSend_fsm la tbl none, startSend_fsm_none_eq, bind_assoc]
              congr 1; funext coins; rw [hvSend_fsm la tbl (some coins)]
            rw [hvL_none, hvM_none false tblM, hvM_none true tblL,
              bind_assoc, bind_assoc, bind_assoc]
            exact dir1Rel_bind ($ᵗ (BitVec 256)) _ _ _ fun coins _ => hcoins coins
        intro coins
        rw [hvSend_loc, hvSend_fsm false tblM, hvSend_fsm true tblL,
          startSend_loc_some_eq, startSend_fsm_some_eq, startSend_fsm_some_eq]
        let c := cka.send (esLoc.g.st P).γ coins
        by_cases hep_t : ep = t
        · have hP_send : P = Party.senderOf t := by
            apply party_eq_senderOf_of_sendsIn
            rw [← hep_t, ← hep_eq]; exact hsend
          have htcur_lt : (esLoc.g.st (Party.senderOf t)).tcur < t := by
            rw [← hP_send]; omega
          by_cases htH : mo.tStar = mo.tH
          · have hnilL : esLoc.h.sessions = [] := hsync.hsess_tH htH htcur_lt
            have hnilM : esM.h.sessions = [] := hsync.hsessM.trans hnilL
            subst hep_t
            rw [rootLPrefix_regSessOf_tStar_tH_run prng l ep q hq_pos ks htH c.2.2 (esLoc.g.st P).root esLoc.h hnilL,
              rootFSMulti_regSessOptMulti_tStar_tH_run (impl false) prng l ep htH c.2.2 (esLoc.g.st P).root esM.h _ hnilM,
              rootFSMulti_regSessOptMulti_tStar_tH_run (impl true) prng l ep htH c.2.2 (esLoc.g.st P).root esM.h _ hnilM]
            simp only [bind_assoc, pure_bind]
            refine dir1Rel_bind ($ᵗ Pt) _ _ _ fun Ir _ => ?_
            refine dir1Rel_bind ($ᵗ (BitVec 256)) _ _ _ fun k_draw _ => ?_
            let σ' := (prng.up (esLoc.g.st P).root Ir).1
            let hdr : Header Pt := (ep, some c.2.1)
            let o := fs.send (fs.initSender (ks 0)) hdr m
            let hLoc1 : LState Pt (BitVec 256) (BitVec 256) Pt :=
              { esLoc.h with sessions := [Ir], cache := Function.update esLoc.h.cache ep (some (c.2.1, σ', ks 0, some 0))  }
            let hM1 : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
              { esM.h with sessions := [Ir], cache := Function.update esM.h.cache ep (some (c.2.1, σ', k_draw, some 0))  }
            have hbk0 : (hM1.book 0).getD {} = {} := by
              have hb := hsync.hbook_out 0 (by simp [hnilL])
              simp [hM1, hb]
            have htbl0 := hsync.htbl_out 0 (by simp [hnilL])
            have hinv0 : ActiveSessInv C ℓ encT idOf phase1' (ks 0)
                (fs.initSender (ks 0)) (fs.initReceiver (ks 0))
                ((hM1.book 0).getD {}) (tblM 0) (tblL 0) := by
              rw [hbk0, htbl0.1]
              cases hp1' : phase1'
              · exact activeSessInv_to_phase2 C ℓ encT idOf
                  (activeSessInv_init C ℓ encT idOf true (ks 0) (bs 0))
              · rw [htbl0.2 (hp_imp hp1')]
                exact activeSessInv_init C ℓ encT idOf true (ks 0) (bs 0)
            rcases fsSend_dir1_inr C hrt ℓ hℓ Dh encPt encT idOf Δcka l ep phase1'
                s₁M P hs1M_epP rfl 0 hdr m hshort (ks 0)
                (fs.initSender (ks 0)) (fs.initReceiver (ks 0)) hM1 tblM tblL hinv0 with
              ⟨bk', sM', sL', hfsM, hfsL, hinv'⟩
            change Dir1Rel phase1' _ _ _
            dsimp (config := { zetaDelta := true }) only at hfsM hfsL ⊢
            rw [hfsM]
            simp only [pure_bind]
            let hM' := { hM1 with book := Function.update hM1.book 0 (some bk') }
            let vpL' : VP _ _ _ _ _ :=
              { esLoc.g.st P with
                tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                root := σ', vS := some (o.1, some 0) }
            let vpM' : VP _ _ _ _ _ :=
              { esM.g.st P with
                tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                root := σ', vS := some (Sum.inr 0 : RatchetSenderState (BitVec 256) ⊕ ℕ) }
            have hsync' := syncDir1_record C ℓ encT idOf q Δcka l ep ks bs phase1 phase1' rem
              esLoc esM esL tblM tblL hsync P m s₁Loc s₁M herase1 hst1L hst1M hwin1L_f hwin1M_f
              htr1L hep1_other rfl ssLoc rsLoc hvp vpL' vpM' (hdr, o.2) hLoc1 hM'
              (Function.update tblM 0 sM') (Function.update tblL 0 sL')
              (Function.update ssLoc 0 o.1) (Function.update rsLoc 0 (fs.initReceiver (ks 0)))
              hs1L_epP.symm ⟨hs1L_epP.symm, hidL⟩ (Nat.le_succ _)
              (fun hp1' => hsync.hlf (hp_imp hp1'))
              rfl (List.nodup_singleton Ir) (by simp [hLoc1]; have := hsync.hsess_rem; omega) (by simp [hnilL])
              (fun _ hlt => by rw [← hP_send, Function.update_self] at hlt; dsimp only [vpL'] at hlt; omega)
              (fun hne => False.elim (hne htH))
              (fun hne => False.elim (hne htH))
              (fun ep' => by
                by_cases heq : ep' = ep
                · subst heq; simp [hLoc1, hM', hM1]
                · dsimp only [hLoc1, hM', hM1]
                  rw [Function.update_of_ne heq, Function.update_of_ne heq]
                  have hc := hsync.hcache ep'
                  cases hcL : esLoc.h.cache ep' with
                  | none =>
                    cases hcM : esM.h.cache ep' with
                    | none => trivial
                    | some _ => rw [hcL, hcM] at hc; exact False.elim hc
                  | some qL =>
                    rcases qL with ⟨TcL, σL, kL, _ | idxL⟩
                    · cases hcM : esM.h.cache ep' with
                      | none => rw [hcL, hcM] at hc; exact False.elim hc
                      | some qM => rcases qM with ⟨TcM, σM, kM, idxM?⟩; rw [hcL, hcM] at hc; exact hc
                    · cases hcM : esM.h.cache ep' with
                      | none => rw [hcL, hcM] at hc; exact False.elim hc
                      | some qM =>
                        rcases qM with ⟨TcM, σM, kM, idxM?⟩
                        rw [hcL, hcM] at hc; dsimp only at hc
                        exact False.elim (heq hc.2.2.2.1))
              (fun hlt => by rw [← hP_send, Function.update_self] at hlt; dsimp only [vpL'] at hlt; omega)
              (fun j hj => by
                have hne : j ≠ 0 := by simp [hLoc1] at hj; omega
                dsimp only [hM', hM1]; rw [Function.update_of_ne hne]
                exact hsync.hbook_out j (by simp [hnilL]))
              (fun j hj => by
                have hne : j ≠ 0 := by simp [hLoc1] at hj; omega
                refine ⟨(Function.update_of_ne hne _ _).trans (hsync.htbl_out j (by simp [hnilL])).1,
                  fun hp1' => (Function.update_of_ne hne _ _).trans ((hsync.htbl_out j (by simp [hnilL])).2 (hp_imp hp1'))⟩)
              (fun j hj => by
                have hj0 : j = 0 := by simp [hLoc1] at hj; omega
                subst hj0
                simpa [hM', Function.update_self] using hinv')
              (fun hlt => by rw [← hP_send, Function.update_self] at hlt; dsimp only [vpL'] at hlt; omega)
              (fun _ j hj => by
                have hj0 : j = 0 := by simp [hLoc1] at hj; omega
                subst hj0; simp [fs])
              (fun j hj => by simp [hnilL] at hj)
              (Or.inl hP_send)
              ⟨hidP, rfl, rfl, rfl, rfl, rfl, rfl⟩
              (by simp [vpL', vpM', hLoc1, hP_send])
            cases hp1' : phase1' with
            | false =>
              rw [hp1'] at hsync'
              exact dir1Rel_to_phase2 (hk (some (hdr, o.2)) false _ _ _ _ _ hsync')
            | true =>
              rw [hfsL hp1']
              simp only [pure_bind]
              rw [hp1'] at hsync'
              dsimp (config := { zetaDelta := true }) only at hp1'
              rw [hp1']
              exact hk (some (hdr, o.2)) true _ _ _ _ _ hsync'
          · have hlen_lt : esLoc.h.sessions.length < q := by have := hsync.hsess_rem; omega
            subst hep_t
            rw [rootLPrefix_regSessOf_tStar_ne_run prng l ep q ks htH c.2.2 (esLoc.g.st P).root
                esLoc.h (hsync.htbl_loc htH) hlen_lt,
              rootFSMulti_regSessOptMulti_tStar_ne_run (impl false) prng l ep htH c.2.2 (esLoc.g.st P).root
                esM.h _ (by simpa only [hsync.hsessM] using hsync.htbl_M htH),
              rootFSMulti_regSessOptMulti_tStar_ne_run (impl true) prng l ep htH c.2.2 (esLoc.g.st P).root
                esM.h _ (by simpa only [hsync.hsessM] using hsync.htbl_M htH)]
            rw [hsync.hsessM]
            by_cases hmem : c.2.2 ∈ esLoc.h.sessions
            · simp only [hmem, ↓reduceIte, pure_bind]
              let sIdx := esLoc.h.sessions.idxOf c.2.2
              have hs_lt : sIdx < esLoc.h.sessions.length := List.idxOf_lt_length_of_mem hmem
              have hss_eq : ssLoc sIdx = fs.initSender (ks sIdx) := hss_init htcur_lt sIdx hs_lt
              let σ' := (prng.up (esLoc.g.st P).root c.2.2).1
              let kM_val := (esM.h.table.lookup c.2.2).getD 0
              let hdr : Header Pt := (ep, some c.2.1)
              let o := fs.send (fs.initSender (ks sIdx)) hdr m
              let hLoc1 : LState Pt (BitVec 256) (BitVec 256) Pt :=
                { esLoc.h with cache := Function.update esLoc.h.cache ep (some (c.2.1, σ', ks sIdx, some sIdx)) }
              let hM1 : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                { esM.h with cache := Function.update esM.h.cache ep (some (c.2.1, σ', kM_val, some sIdx)) }
              have hinv0 : ActiveSessInv C ℓ encT idOf phase1' (ks sIdx)
                  (fs.initSender (ks sIdx)) (rsLoc sIdx) ((hM1.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) := by
                rw [← hss_eq]
                exact activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact sIdx hs_lt)
              rcases fsSend_dir1_inr C hrt ℓ hℓ Dh encPt encT idOf Δcka l ep phase1'
                  s₁M P hs1M_epP rfl sIdx hdr m hshort (ks sIdx)
                  (fs.initSender (ks sIdx)) (rsLoc sIdx) hM1 tblM tblL hinv0 with
                ⟨bk', sM', sL', hfsM, hfsL, hinv'⟩
              change Dir1Rel phase1' _ _ _
              dsimp (config := { zetaDelta := true }) only at hfsM hfsL ⊢
              rw [hfsM]
              simp only [pure_bind]
              let hM' := { hM1 with book := Function.update hM1.book sIdx (some bk') }
              let vpL' : VP _ _ _ _ _ :=
                { esLoc.g.st P with
                  tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                  root := σ', vS := some (o.1, some sIdx) }
              let vpM' : VP _ _ _ _ _ :=
                { esM.g.st P with
                  tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                  root := σ', vS := some (Sum.inr sIdx : RatchetSenderState (BitVec 256) ⊕ ℕ) }
              have hsync' := syncDir1_record C ℓ encT idOf q Δcka l ep ks bs phase1 phase1' rem
                esLoc esM esL tblM tblL hsync P m s₁Loc s₁M herase1 hst1L hst1M hwin1L_f hwin1M_f
                htr1L hep1_other rfl ssLoc rsLoc hvp vpL' vpM' (hdr, o.2) hLoc1 hM'
                (Function.update tblM sIdx sM') (Function.update tblL sIdx sL')
                (Function.update ssLoc sIdx o.1) rsLoc
                hs1L_epP.symm ⟨hs1L_epP.symm, hidL⟩ (Nat.le_succ _)
                (fun hp1' => hsync.hlf (hp_imp hp1'))
                hsync.hsessM hsync.hsess_nodup (by dsimp only [hLoc1]; have := hsync.hsess_rem; omega) le_rfl
                (fun heq => False.elim (htH heq))
                hsync.htbl_loc (fun hne => by dsimp only [hM', hM1]; simpa only [hsync.hsessM] using hsync.htbl_M hne)
                (fun ep' => by
                  by_cases heq : ep' = ep
                  · subst heq; simp [hLoc1, hM', hM1, hs_lt]
                  · dsimp only [hLoc1, hM', hM1]
                    rw [Function.update_of_ne heq, Function.update_of_ne heq]
                    exact hsync.hcache ep')
                (fun hlt => by rw [← hP_send, Function.update_self] at hlt; dsimp only [vpL'] at hlt; omega)
                (fun j hj => by
                  have hne : j ≠ sIdx := by dsimp only [hLoc1] at hj; omega
                  dsimp only [hM', hM1]; rw [Function.update_of_ne hne]
                  exact hsync.hbook_out j hj)
                (fun j hj => by
                  have hne : j ≠ sIdx := by dsimp only [hLoc1] at hj; omega
                  exact ⟨(Function.update_of_ne hne _ _).trans (hsync.htbl_out j hj).1,
                    fun hp1' => (Function.update_of_ne hne _ _).trans ((hsync.htbl_out j hj).2 (hp_imp hp1'))⟩)
                (fun j hj => by
                  by_cases hjeq : j = sIdx
                  · subst hjeq; simpa [hM', Function.update_self] using hinv'
                  · dsimp only [hM', hM1]
                    rw [Function.update_of_ne hjeq, Function.update_of_ne hjeq, Function.update_of_ne hjeq,
                      Function.update_of_ne hjeq]
                    exact activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact j hj))
                (fun hlt => by rw [← hP_send, Function.update_self] at hlt; dsimp only [vpL'] at hlt; omega)
                (fun hlt => by
                  have hlt0 : (esLoc.g.st (Party.receiverOf ep)).tcur < ep := by
                    by_cases hPR : Party.receiverOf ep = P
                    · rw [hPR] at hlt ⊢; simp only [Function.update_self, vpL'] at hlt; omega
                    · simpa [Function.update_of_ne hPR] using hlt
                  exact hrs_init hlt0)
                (fun _ _ => rfl)
                (Or.inl hP_send)
                ⟨hidP, rfl, rfl, rfl, rfl, rfl, rfl⟩
                (by simp [vpL', vpM', hLoc1, hs_lt, hP_send])
              cases hp1' : phase1' with
              | false =>
                rw [hp1'] at hsync'
                exact dir1Rel_to_phase2 (hk (some (hdr, o.2)) false _ _ _ _ _ hsync')
              | true =>
                rw [hfsL hp1']
                simp only [pure_bind]
                rw [hp1'] at hsync'
                dsimp (config := { zetaDelta := true }) only at hp1'
                rw [hp1']
                exact hk (some (hdr, o.2)) true _ _ _ _ _ hsync'
            · simp only [hmem, ↓reduceIte, bind_assoc, pure_bind]
              refine dir1Rel_bind ($ᵗ (BitVec 256)) _ _ _ fun k_draw _ => ?_
              let sIdx := esLoc.h.sessions.length
              let σ' := (prng.up (esLoc.g.st P).root c.2.2).1
              let hdr : Header Pt := (ep, some c.2.1)
              let o := fs.send (fs.initSender (ks sIdx)) hdr m
              let hLoc1 : LState Pt (BitVec 256) (BitVec 256) Pt :=
                { esLoc.h with table := (c.2.2, ks sIdx) :: esLoc.h.table, sessions := esLoc.h.sessions ++ [c.2.2], cache := Function.update esLoc.h.cache ep (some (c.2.1, σ', ks sIdx, some sIdx))  }
              let hM1 : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                { esM.h with table := (c.2.2, k_draw) :: esM.h.table, sessions := esLoc.h.sessions ++ [c.2.2], cache := Function.update esM.h.cache ep (some (c.2.1, σ', k_draw, some sIdx))  }
              have hbk0 : (hM1.book sIdx).getD {} = {} := by
                have hb := hsync.hbook_out sIdx le_rfl
                simp [hM1, hb]
              have htbl0 := hsync.htbl_out sIdx le_rfl
              have hinv0 : ActiveSessInv C ℓ encT idOf phase1' (ks sIdx)
                  (fs.initSender (ks sIdx)) (fs.initReceiver (ks sIdx))
                  ((hM1.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) := by
                rw [hbk0, htbl0.1]
                cases hp1' : phase1'
                · exact activeSessInv_to_phase2 C ℓ encT idOf
                    (activeSessInv_init C ℓ encT idOf true (ks sIdx) (bs sIdx))
                · rw [htbl0.2 (hp_imp hp1')]
                  exact activeSessInv_init C ℓ encT idOf true (ks sIdx) (bs sIdx)
              rcases fsSend_dir1_inr C hrt ℓ hℓ Dh encPt encT idOf Δcka l ep phase1'
                  s₁M P hs1M_epP rfl sIdx hdr m hshort (ks sIdx)
                  (fs.initSender (ks sIdx)) (fs.initReceiver (ks sIdx)) hM1 tblM tblL hinv0 with
                ⟨bk', sM', sL', hfsM, hfsL, hinv'⟩
              change Dir1Rel phase1' _ _ _
              dsimp (config := { zetaDelta := true }) only at hfsM hfsL ⊢
              rw [hfsM]
              simp only [pure_bind]
              let hM' := { hM1 with book := Function.update hM1.book sIdx (some bk') }
              let vpL' : VP _ _ _ _ _ :=
                { esLoc.g.st P with
                  tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                  root := σ', vS := some (o.1, some sIdx) }
              let vpM' : VP _ _ _ _ _ :=
                { esM.g.st P with
                  tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                  root := σ', vS := some (Sum.inr sIdx : RatchetSenderState (BitVec 256) ⊕ ℕ) }
              have hnodup' : (esLoc.h.sessions ++ [c.2.2]).Nodup :=
                List.nodup_append.mpr ⟨hsync.hsess_nodup, List.nodup_singleton _,
                  fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact hmem hx⟩
              have hsync' := syncDir1_record C ℓ encT idOf q Δcka l ep ks bs phase1 phase1' rem
                esLoc esM esL tblM tblL hsync P m s₁Loc s₁M herase1 hst1L hst1M hwin1L_f hwin1M_f
                htr1L hep1_other rfl ssLoc rsLoc hvp vpL' vpM' (hdr, o.2) hLoc1 hM'
                (Function.update tblM sIdx sM') (Function.update tblL sIdx sL')
                (Function.update ssLoc sIdx o.1) (Function.update rsLoc sIdx (fs.initReceiver (ks sIdx)))
                hs1L_epP.symm ⟨hs1L_epP.symm, hidL⟩ (Nat.le_succ _)
                (fun hp1' => hsync.hlf (hp_imp hp1'))
                rfl hnodup'
                (by simp [hLoc1]; have := hsync.hsess_rem; omega)
                (by simp [hLoc1])
                (fun heq => False.elim (htH heq))
                (fun _ Ik => by
                  dsimp only [hLoc1]
                  by_cases hIk : Ik = c.2.2
                  · subst hIk
                    simp [list_idxOf_append_new hmem, sIdx]
                  · have hne_beq : (Ik == c.2.2) = false := beq_eq_false_iff_ne.mpr hIk
                    simp only [List.lookup_cons, hne_beq, hsync.htbl_loc htH Ik]
                    by_cases hmIk : Ik ∈ esLoc.h.sessions
                    · simp [hmIk, list_idxOf_append_mem hmIk]
                    · simp [hmIk, hIk])
                (fun _ Ik => by
                  dsimp only [hM', hM1]
                  by_cases hIk : Ik = c.2.2
                  · subst hIk; simp
                  · have hne_beq : (Ik == c.2.2) = false := beq_eq_false_iff_ne.mpr hIk
                    simp only [List.lookup_cons, hne_beq, hsync.htbl_M htH Ik]
                    by_cases hmIk : Ik ∈ esLoc.h.sessions <;> simp [hmIk, hIk])
                (fun ep' => by
                  by_cases heq : ep' = ep
                  · subst heq; simp [hLoc1, hM', hM1, sIdx]
                  · dsimp only [hLoc1, hM', hM1]
                    rw [Function.update_of_ne heq, Function.update_of_ne heq]
                    have hc := hsync.hcache ep'
                    cases hcL : esLoc.h.cache ep' with
                    | none =>
                      cases hcM : esM.h.cache ep' with
                      | none => trivial
                      | some _ => rw [hcL, hcM] at hc; exact False.elim hc
                    | some qL =>
                      rcases qL with ⟨TcL, σL, kL, _ | idxL⟩
                      · cases hcM : esM.h.cache ep' with
                        | none => rw [hcL, hcM] at hc; exact False.elim hc
                        | some qM => rcases qM with ⟨TcM, σM, kM, idxM?⟩; rw [hcL, hcM] at hc; exact hc
                      · cases hcM : esM.h.cache ep' with
                        | none => rw [hcL, hcM] at hc; exact False.elim hc
                        | some qM =>
                          rcases qM with ⟨TcM, σM, kM, idxM?⟩
                          rw [hcL, hcM] at hc; dsimp only at hc
                          exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
                            by simp; omega, hc.2.2.2.2.2⟩)
                (fun hlt => by rw [← hP_send, Function.update_self] at hlt; dsimp only [vpL'] at hlt; omega)
                (fun j hj => by
                  have hne : j ≠ sIdx := by simp [hLoc1] at hj; omega
                  dsimp only [hM', hM1]; rw [Function.update_of_ne hne]
                  exact hsync.hbook_out j (by simp [hLoc1] at hj; omega))
                (fun j hj => by
                  have hne : j ≠ sIdx := by simp [hLoc1] at hj; omega
                  have hj0 : esLoc.h.sessions.length ≤ j := by simp [hLoc1] at hj; omega
                  exact ⟨(Function.update_of_ne hne _ _).trans (hsync.htbl_out j hj0).1,
                    fun hp1' => (Function.update_of_ne hne _ _).trans ((hsync.htbl_out j hj0).2 (hp_imp hp1'))⟩)
                (fun j hj => by
                  by_cases hjeq : j = sIdx
                  · subst hjeq; simpa [hM', Function.update_self] using hinv'
                  · have hj_lt : j < esLoc.h.sessions.length := by simp [hLoc1] at hj; omega
                    dsimp only [hM', hM1]
                    rw [Function.update_of_ne hjeq, Function.update_of_ne hjeq,
                      Function.update_of_ne hjeq, Function.update_of_ne hjeq, Function.update_of_ne hjeq]
                    exact activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact j hj_lt))
                (fun hlt => by rw [← hP_send, Function.update_self] at hlt; dsimp only [vpL'] at hlt; omega)
                (fun hlt j hj => by
                  have hlt0 : (esLoc.g.st (Party.receiverOf ep)).tcur < ep := by
                    by_cases hPR : Party.receiverOf ep = P
                    · rw [hPR] at hlt ⊢; simp only [Function.update_self, vpL'] at hlt; omega
                    · simpa [Function.update_of_ne hPR] using hlt
                  by_cases hjeq : j = sIdx
                  · subst hjeq; simp [fs]
                  · have hj_lt : j < esLoc.h.sessions.length := by simp [hLoc1] at hj; omega
                    rw [Function.update_of_ne hjeq]
                    exact hrs_init hlt0 j hj_lt)
                (fun j hj => Function.update_of_ne (by dsimp only [sIdx]; omega) _ _)
                (Or.inl hP_send)
                ⟨hidP, rfl, rfl, rfl, rfl, rfl, rfl⟩
                (by simp [vpL', vpM', hLoc1, sIdx, hP_send])
              cases hp1' : phase1' with
              | false =>
                rw [hp1'] at hsync'
                exact dir1Rel_to_phase2 (hk (some (hdr, o.2)) false _ _ _ _ _ hsync')
              | true =>
                rw [hfsL hp1']
                simp only [pure_bind]
                rw [hp1'] at hsync'
                dsimp (config := { zetaDelta := true }) only at hp1'
                rw [hp1']
                exact hk (some (hdr, o.2)) true _ _ _ _ _ hsync'
        · -- Subcase A1: ep ≠ t
          rw [rootLPrefix_regSessOf_ne_run prng mo q ks ep hep_t c.2.2 (esLoc.g.st P).root esLoc.h,
            rootFSMulti_regSessOptMulti_ne_run (impl false) prng mo ep hep_t c.2.2 (esLoc.g.st P).root esM.h _,
            rootFSMulti_regSessOptMulti_ne_run (impl true) prng mo ep hep_t c.2.2 (esLoc.g.st P).root esM.h _]
          suffices hA1 : ∀ (σ' k : BitVec 256),
              let o := fs.send (fs.initSender k) (ep, some c.2.1) m
              let hLoc1 : LState Pt (BitVec 256) (BitVec 256) Pt :=
                { esLoc.h with cache := Function.update esLoc.h.cache ep (some (c.2.1, σ', k, none)) }
              let hM1 : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32) :=
                { esM.h with cache := Function.update esM.h.cache ep (some (c.2.1, σ', k, none)) }
              let vpL' : VP _ _ _ _ _ :=
                { esLoc.g.st P with
                  tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                  root := σ', vS := some (o.1, none) }
              let vpM' : VP _ _ _ _ _ :=
                { esM.g.st P with
                  tcur := ep, γ := c.1, curCkaMsg := some c.2.1,
                  root := σ', vS := some (.inl o.1) }
              Dir1Rel phase1'
                (kLoc (some ((ep, some c.2.1), o.2))
                  { g := s₁Loc.record (2 + Δcka) P vpL'
                      ⟨⟨P, s₁Loc.epoch P, s₁Loc.idx P + 1⟩, m, ((ep, some c.2.1), o.2)⟩ false,
                    h := hLoc1, abort := false })
                (kM (some ((ep, some c.2.1), o.2))
                  { g := s₁M.record (2 + Δcka) P vpM'
                      ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ((ep, some c.2.1), o.2)⟩ false,
                    h := hM1, abort := false } (fun _ => false, tblM))
                (kL (some ((ep, some c.2.1), o.2))
                  { g := s₁M.record (2 + Δcka) P vpM'
                      ⟨⟨P, s₁M.epoch P, s₁M.idx P + 1⟩, m, ((ep, some c.2.1), o.2)⟩ false,
                    h := hM1, abort := false } (fun _ => false, tblL)) by
            split_ifs
            · simp only [bind_assoc, pure_bind]
              refine dir1Rel_bind ($ᵗ Pt) _ _ _ fun Ir _ => ?_
              dsimp only [hooksFSMulti]
              simp only [StateT.run_pure, simulateQ_pure, pure_bind]
              exact hA1 (prng.up (esLoc.g.st P).root Ir).1 (prng.up (esLoc.g.st P).root Ir).2
            · dsimp only [hooksFSMulti]
              simp only [StateT.run_pure, simulateQ_pure, pure_bind]
              exact hA1 (prng.up (esLoc.g.st P).root c.2.2).1 (prng.up (esLoc.g.st P).root c.2.2).2
          intro σ' k o hLoc1 hM1 vpL' vpM'
          have htcur_mono : ∀ Q, (esLoc.g.st Q).tcur ≤ (Function.update esLoc.g.st P vpL' Q).tcur := by
            intro Q
            by_cases hQP : Q = P
            · subst hQP; simp [Function.update_self, vpL', ep]
            · simp [Function.update_of_ne hQP]
          have hsync' := syncDir1_record C ℓ encT idOf q Δcka l t ks bs phase1 phase1' rem
            esLoc esM esL tblM tblL hsync P m s₁Loc s₁M herase1 hst1L hst1M hwin1L_f hwin1M_f
            htr1L hep1_other rfl ssLoc rsLoc hvp vpL' vpM' ((ep, some c.2.1), o.2) hLoc1 hM1
            tblM tblL ssLoc rsLoc
            hs1L_epP.symm ⟨hs1L_epP.symm, hidL⟩ (Nat.le_succ _)
            (fun hp1' => hsync.hlf (hp_imp hp1'))
            hsync.hsessM hsync.hsess_nodup (by dsimp only [hLoc1]; have := hsync.hsess_rem; omega) le_rfl
            (fun heq hlt => hsync.hsess_tH heq (lt_of_le_of_lt (htcur_mono _) hlt))
            hsync.htbl_loc (fun hne => by dsimp only [hM1]; simpa only [hsync.hsessM] using hsync.htbl_M hne)
            (fun ep' => by
              by_cases heq : ep' = ep
              · subst heq; simp [hLoc1, hM1, hep_t]
              · dsimp only [hLoc1, hM1]
                rw [Function.update_of_ne heq, Function.update_of_ne heq]
                exact hsync.hcache ep')
            (fun hlt => by
              dsimp only [hLoc1]
              rw [Function.update_of_ne (Ne.symm hep_t)]
              exact hsync.hcache_tcur (lt_of_le_of_lt (htcur_mono _) hlt))
            hsync.hbook_out
            (fun j hj => ⟨(hsync.htbl_out j hj).1, fun hp1' => (hsync.htbl_out j hj).2 (hp_imp hp1')⟩)
            (fun j hj => activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact j hj))
            (fun hlt => hss_init (lt_of_le_of_lt (htcur_mono _) hlt))
            (fun hlt => hrs_init (lt_of_le_of_lt (htcur_mono _) hlt))
            (fun _ _ => rfl)
            (Or.inr ⟨fun _ _ => rfl, by simp [vpM']⟩)
            ⟨hidP, rfl, rfl, rfl, rfl, rfl, rfl⟩
            (by simp [vpL', vpM'])
          exact hk (some ((ep, some c.2.1), o.2)) phase1' _ _ _ _ _ hsync'
      · -- Case B: P.sendsIn (esLoc.g.epoch P + 1) = false
        have hsend_f : P.sendsIn (esLoc.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsend
        simp only [hsend_f, Bool.false_eq_true, ↓reduceIte] at hep_if
        rcases hep_if with ⟨rfl, rfl⟩
        have hsendL_f : (esLoc.g.st P).id.sendsIn ((esLoc.g.st P).tcur + 1) = false := by
          rw [hidL, htcur_ep]; exact hsend_f
        have hsendM_f : (esM.g.st P).id.sendsIn ((esM.g.st P).tcur + 1) = false := by
          rw [hidM, ← htcurP, htcur_ep]; exact hsend_f
        let hdr : Header Pt := ((esLoc.g.st P).tcur, (esLoc.g.st P).curCkaMsg)
        have hhdrM : ((esM.g.st P).tcur, (esM.g.st P).curCkaMsg) = hdr := by
          simp [hdr, htcurP, hcurP]
        cases hvSL : (esLoc.g.st P).vS with
        | none =>
          have hvSM : (esM.g.st P).vS = none := by
            cases hm : (esM.g.st P).vS with
            | none => rfl
            | some _ => rw [hvSL, hm] at hvSP; exact False.elim hvSP
          have hvL_run : simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
              esLoc.g P (esLoc.g.st P) m none r_c).run esLoc.h) =
              pure (some (esLoc.g.st P, (hdr, default)), esLoc.h) := by
            unfold vSend
            simp [hsendL_f, hvSL, hdr, StateT.run_pure, simulateQ_pure]
          have hvM_run : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
              (simulateQ (pubFsMultiImpl (impl la)) ((vSend (hooksFSMulti cka prng fs Δcka mo false la)
                esM.g P (esM.g.st P) m none r_c).run esM.h)).run (fun _ => false, tbl) =
              pure ((some (esM.g.st P, (hdr, default)), esM.h), (fun _ => false, tbl)) := by
            intro la tbl
            unfold vSend
            simp [hsendM_f, hvSM, hhdrM, StateT.run_pure, simulateQ_pure]
          rw [hvL_run, hvM_run false tblM, hvM_run true tblL]
          simp only [pure_bind]
          have hupdL : Function.update esLoc.g.st P (esLoc.g.st P) = esLoc.g.st :=
            Function.update_eq_self P esLoc.g.st
          have hsync' := syncDir1_record C ℓ encT idOf q Δcka l t ks bs phase1 phase1' rem
            esLoc esM esL tblM tblL hsync P m esLoc.g esM.g hsync.heraseM rfl rfl
            hsync.hwinL hsync.hwinM rfl (fun _ _ => rfl) rfl ssLoc rsLoc hvp
            (esLoc.g.st P) (esM.g.st P) (hdr, default) esLoc.h esM.h tblM tblL ssLoc rsLoc
            htcur_ep ⟨htcur_ep, hidL⟩ le_rfl
            (fun hp1' => hsync.hlf (hp_imp hp1'))
            hsync.hsessM hsync.hsess_nodup (by have := hsync.hsess_rem; omega) le_rfl
            (by rw [hupdL]; exact hsync.hsess_tH)
            hsync.htbl_loc (fun hne => by simpa only [hsync.hsessM] using hsync.htbl_M hne) hsync.hcache
            (by rw [hupdL]; exact hsync.hcache_tcur)
            hsync.hbook_out
            (fun j hj => ⟨(hsync.htbl_out j hj).1, fun hp1' => (hsync.htbl_out j hj).2 (hp_imp hp1')⟩)
            (fun j hj => activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact j hj))
            (by rw [hupdL]; exact hss_init)
            (by rw [hupdL]; exact hrs_init)
            (fun _ _ => rfl)
            (Or.inr ⟨fun _ _ => rfl, by simp [hvSM]⟩)
            ⟨hidP, htcurP, hγP, hrootP, hcurP, rfl, rfl⟩
            (by simp [hvSL, hvSM])
          exact hk (some (hdr, default)) phase1' _ _ _ _ _ hsync'
        | some pS =>
          rcases pS with ⟨ss, _ | sIdx⟩
          · have hvSM : (esM.g.st P).vS = some (.inl ss) := by
              cases hm : (esM.g.st P).vS with
              | none => rw [hvSL, hm] at hvSP; exact False.elim hvSP
              | some x =>
                rcases x with ssM | idxM
                · rw [hvSL, hm] at hvSP; simp [hvSP]
                · rw [hvSL, hm] at hvSP; exact False.elim hvSP
            let o := fs.send ss hdr m
            let vpL' := { esLoc.g.st P with vS := some (o.1, (none : Option ℕ)) }
            let vpM' := { esM.g.st P with vS := some (Sum.inl o.1 : RatchetSenderState (BitVec 256) ⊕ ℕ) }
            have hvL_run : simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
                esLoc.g P (esLoc.g.st P) m none r_c).run esLoc.h) =
                pure (some (vpL', (hdr, o.2)), esLoc.h) := by
              unfold vSend
              simp [hsendL_f, hvSL, hooksLocalPrefix, hdr, o, vpL',
                StateT.run_pure, pure_bind, simulateQ_pure]
            have hvM_run : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
                (simulateQ (pubFsMultiImpl (impl la)) ((vSend (hooksFSMulti cka prng fs Δcka mo false la)
                  esM.g P (esM.g.st P) m none r_c).run esM.h)).run (fun _ => false, tbl) =
                pure ((some (vpM', (hdr, o.2)), esM.h), (fun _ => false, tbl)) := by
              intro la tbl
              unfold vSend
              dsimp only [hooksFSMulti]
              simp [hsendM_f, hvSM, hhdrM, o, vpM', StateT.run_pure,
                pure_bind, simulateQ_pure]
            rw [hvL_run, hvM_run false tblM, hvM_run true tblL]
            simp only [pure_bind]
            have htcur_same : ∀ Q, (Function.update esLoc.g.st P vpL' Q).tcur = (esLoc.g.st Q).tcur := by
              intro Q; by_cases hQP : Q = P
              · subst hQP; simp [vpL']
              · simp [Function.update_of_ne hQP]
            have hsync' := syncDir1_record C ℓ encT idOf q Δcka l t ks bs phase1 phase1' rem
              esLoc esM esL tblM tblL hsync P m esLoc.g esM.g hsync.heraseM rfl rfl
              hsync.hwinL hsync.hwinM rfl (fun _ _ => rfl) rfl ssLoc rsLoc hvp
              vpL' vpM' (hdr, o.2) esLoc.h esM.h tblM tblL ssLoc rsLoc
              htcur_ep ⟨htcur_ep, hidL⟩ le_rfl
              (fun hp1' => hsync.hlf (hp_imp hp1'))
              hsync.hsessM hsync.hsess_nodup (by have := hsync.hsess_rem; omega) le_rfl
              (fun heq hlt => hsync.hsess_tH heq (by rwa [htcur_same] at hlt))
              hsync.htbl_loc (fun hne => by simpa only [hsync.hsessM] using hsync.htbl_M hne) hsync.hcache
              (fun hlt => hsync.hcache_tcur (by rwa [htcur_same] at hlt))
              hsync.hbook_out
              (fun j hj => ⟨(hsync.htbl_out j hj).1, fun hp1' => (hsync.htbl_out j hj).2 (hp_imp hp1')⟩)
              (fun j hj => activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact j hj))
              (fun hlt => hss_init (by rwa [htcur_same] at hlt))
              (fun hlt => hrs_init (by rwa [htcur_same] at hlt))
              (fun _ _ => rfl)
              (Or.inr ⟨fun _ _ => rfl, by simp [vpM']⟩)
              ⟨hidP, htcurP, hγP, hrootP, hcurP, rfl, rfl⟩
              (by simp [vpL', vpM'])
            exact hk (some (hdr, o.2)) phase1' _ _ _ _ _ hsync'
          · have hvSM_ex : (esM.g.st P).vS = some (.inr sIdx) ∧
                sIdx < esLoc.h.sessions.length ∧ ss = ssLoc sIdx ∧
                P = Party.senderOf t ∧
                ((esLoc.g.st P).tcur = t ∨ (esLoc.g.st P).tcur = t + 1) := by
              cases hm : (esM.g.st P).vS with
              | none => rw [hvSL, hm] at hvSP; exact False.elim hvSP
              | some x =>
                rcases x with ssM | idxM
                · rw [hvSL, hm] at hvSP; exact False.elim hvSP
                · rw [hvSL, hm] at hvSP; dsimp only at hvSP
                  exact ⟨by rw [hvSP.1], hvSP.2.1, hvSP.2.2.1, hvSP.2.2.2.1, hvSP.2.2.2.2.1⟩
            rcases hvSM_ex with ⟨hvSM, hs_lt, hss_eq, hP_send, htcur_or⟩
            have htcur_eq_t : (esLoc.g.st P).tcur = t := by
              rcases htcur_or with h | h
              · exact h
              · exfalso
                have hs2 := party_senderOf_sendsIn_add_two t
                rw [← htcur_ep, h, hP_send] at hsend_f
                rw [hsend_f] at hs2; cases hs2
            have hepochM_t : esM.g.epoch P = t := by
              rw [← congrFun (eraseSt_epoch hsync.heraseM) P, ← htcur_ep, htcur_eq_t]
            let o := fs.send (ssLoc sIdx) hdr m
            let vpL' := { esLoc.g.st P with vS := some (o.1, some sIdx) }
            let vpM' := { esM.g.st P with vS := some (Sum.inr sIdx : RatchetSenderState (BitVec 256) ⊕ ℕ) }
            have hvL_run : simulateQ lImpl ((vSend (hooksLocalPrefix cka prng fs mo q ks)
                esLoc.g P (esLoc.g.st P) m none r_c).run esLoc.h) =
                pure (some (vpL', (hdr, o.2)), esLoc.h) := by
              unfold vSend
              simp [hsendL_f, hvSL, hss_eq, hooksLocalPrefix, hdr, o, vpL',
                StateT.run_pure, pure_bind, simulateQ_pure]
            have hvM_unfold : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
                (simulateQ (pubFsMultiImpl (impl la)) ((vSend (hooksFSMulti cka prng fs Δcka mo false la)
                  esM.g P (esM.g.st P) m none r_c).run esM.h)).run (fun _ => false, tbl) =
                ((simulateQ (pubFsMultiImpl (impl la))
                  (((hooksFSMulti cka prng fs Δcka mo false la).fsSend
                    esM.g P t (.inr sIdx) hdr m none).run esM.h)).run (fun _ => false, tbl) >>= fun v =>
                  match v.1.1 with
                  | none => pure ((none, v.1.2), v.2)
                  | some (ssv', e_out) =>
                    pure ((some ({ esM.g.st P with vS := some ssv' }, (hdr, e_out)), v.1.2), v.2)) := by
              intro la tbl
              unfold vSend
              have htcurM_t : (esM.g.st P).tcur = t := htcurP.symm.trans htcur_eq_t
              have hsendM_f' : (esM.g.st P).id.sendsIn (t + 1) = false := by
                simpa [htcurM_t] using hsendM_f
              have hhdr_eq : (t, (esM.g.st P).curCkaMsg) = hdr := by
                rw [← htcurM_t, hhdrM]
              simp only [htcurM_t, hsendM_f', Bool.false_eq_true, ↓reduceIte, hvSM, hhdr_eq,
                StateT.run_bind, simulateQ_bind, pure_bind]
              congr 1; funext v
              rcases v with ⟨⟨_ | ⟨ssv', e_out⟩, h''⟩, st_tbl'⟩ <;>
                simp [StateT.run_pure, simulateQ_pure]
            have hinv0 : ActiveSessInv C ℓ encT idOf phase1' (ks sIdx)
                (ssLoc sIdx) (rsLoc sIdx) ((esM.h.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) :=
              activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact sIdx hs_lt)
            rcases fsSend_dir1_inr C hrt ℓ hℓ Dh encPt encT idOf Δcka l t phase1'
                esM.g P hepochM_t rfl sIdx hdr m hshort (ks sIdx)
                (ssLoc sIdx) (rsLoc sIdx) esM.h tblM tblL hinv0 with
              ⟨bk', sM', sL', hfsM, hfsL, hinv'⟩
            rw [hvL_run, hvM_unfold false tblM, hvM_unfold true tblL]
            simp only [bind_assoc, pure_bind]
            dsimp (config := { zetaDelta := true }) only at hfsM hfsL ⊢
            rw [hfsM]
            simp only [pure_bind]
            let hM' := { esM.h with book := Function.update esM.h.book sIdx (some bk') }
            have htcur_same : ∀ Q, (Function.update esLoc.g.st P vpL' Q).tcur = (esLoc.g.st Q).tcur := by
              intro Q; by_cases hQP : Q = P
              · subst hQP; simp [vpL']
              · simp [Function.update_of_ne hQP]
            have hsync' := syncDir1_record C ℓ encT idOf q Δcka l t ks bs phase1 phase1' rem
              esLoc esM esL tblM tblL hsync P m esLoc.g esM.g hsync.heraseM rfl rfl
              hsync.hwinL hsync.hwinM rfl (fun _ _ => rfl) rfl ssLoc rsLoc hvp
              vpL' vpM' (hdr, o.2) esLoc.h hM'
              (Function.update tblM sIdx sM') (Function.update tblL sIdx sL')
              (Function.update ssLoc sIdx o.1) rsLoc
              htcur_ep ⟨htcur_ep, hidL⟩ le_rfl
              (fun hp1' => hsync.hlf (hp_imp hp1'))
              hsync.hsessM hsync.hsess_nodup (by have := hsync.hsess_rem; omega) le_rfl
              (fun heq hlt => hsync.hsess_tH heq (by rwa [htcur_same] at hlt))
              hsync.htbl_loc (fun hne => by dsimp only [hM']; simpa only [hsync.hsessM] using hsync.htbl_M hne) hsync.hcache
              (fun hlt => hsync.hcache_tcur (by rwa [htcur_same] at hlt))
              (fun j hj => by
                have hne : j ≠ sIdx := by omega
                dsimp only [hM']; rw [Function.update_of_ne hne]; exact hsync.hbook_out j hj)
              (fun j hj => by
                have hne : j ≠ sIdx := by omega
                exact ⟨(Function.update_of_ne hne _ _).trans (hsync.htbl_out j hj).1,
                  fun hp1' => (Function.update_of_ne hne _ _).trans ((hsync.htbl_out j hj).2 (hp_imp hp1'))⟩)
              (fun j hj => by
                by_cases hjeq : j = sIdx
                · subst hjeq; simpa [hM', Function.update_self] using hinv'
                · dsimp only [hM']
                  rw [Function.update_of_ne hjeq, Function.update_of_ne hjeq,
                    Function.update_of_ne hjeq, Function.update_of_ne hjeq]
                  exact activeSessInv_mono_phase C ℓ encT idOf hp_imp (fun _ => rfl) (hact j hj))
              (fun hlt => by rw [htcur_same, ← hP_send, htcur_eq_t] at hlt; omega)
              (fun hlt => hrs_init (by rwa [htcur_same] at hlt))
              (fun _ _ => rfl)
              (Or.inl hP_send)
              ⟨hidP, htcurP, hγP, hrootP, hcurP, rfl, rfl⟩
              ⟨rfl, hs_lt, (Function.update_self sIdx o.1 ssLoc).symm, hP_send, Or.inl htcur_eq_t⟩
            cases hp1' : phase1' with
            | false =>
              rw [hp1'] at hsync'
              exact dir1Rel_to_phase2 (hk (some (hdr, o.2)) false _ _ _ _ _ hsync')
            | true =>
              rw [hfsL hp1']
              simp only [pure_bind]
              rw [hp1'] at hsync'
              dsimp (config := { zetaDelta := true }) only at hp1'
              try rw [hp1']
              exact hk (some (hdr, o.2)) true _ _ _ _ _ hsync'

private theorem accept_update_st_self {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) (st' : St) (pos : _root_.CryptoGames.SM.Pos) :
    { s.accept P st' pos with st := Function.update (s.accept P st' pos).st P st' } =
      s.accept P st' pos := by
  suffices hst : Function.update (s.accept P st' pos).st P st' = (s.accept P st' pos).st by
    rw [hst]
  funext Q; by_cases h : Q = P <;> simp [GameState.accept, GameState.delete, h]

private theorem commitE_trivial_run {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (hcom : ∀ s₁ P old new, hk.commit s₁ P old new = pure (some new))
    (s : Ctx Γv T Sv SSv RSv M E) (P : Party) (old new : VP Γv T Sv SSv RSv)
    (pos : _root_.CryptoGames.SM.Pos)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (commitE hk s P old new pos).run es = pure (some (s.accept P new pos), es) := by
  unfold commitE
  simp only [StateT.run_bind, liftH_run, hcom, StateT.run_pure, pure_bind, accept_update_st_self]

private theorem inTransit_props {St Msg C : Type} [DecidableEq C]
    {s : GameState St Msg C} {Q : Party} {c : C} {r : Record Msg C}
    (h : s.inTransit Q c = some r) :
    r ∈ s.trans ∧ r.ct = c := by
  unfold GameState.inTransit at h
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  exact ⟨hmem, hpred.2⟩

private theorem syncDir1_lastIdx_rem {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ) (lastIdx' : Option ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL) :
    SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
      { esLoc with h := { esLoc.h with lastIdx := lastIdx' } } esM esM tblM tblL :=
  { habortL := hsync.habortL
    habortM := hsync.habortM
    habortLa := fun _ => hsync.habortM
    hwinL := hsync.hwinL
    hwinM := hsync.hwinM
    hwinLa := fun _ => hsync.hwinM
    hlf := hsync.hlf
    heraseM := hsync.heraseM
    heraseLa := fun _ => rfl
    hh_La := fun _ => rfl
    hhealed := hsync.hhealed
    hginv := hsync.hginv
    hep_st := hsync.hep_st
    hsessM := hsync.hsessM
    hsess_nodup := hsync.hsess_nodup
    hsess_rem := by dsimp only; have := hsync.hsess_rem; omega
    hsess_tH := hsync.hsess_tH
    htbl_loc := hsync.htbl_loc
    htbl_M := hsync.htbl_M
    hcache := hsync.hcache
    hcache_tcur := hsync.hcache_tcur
    hbook_out := hsync.hbook_out
    htbl_out := hsync.htbl_out
    hstates := hsync.hstates }

private theorem syncDir1_accept {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (ep : ℕ) (pos : _root_.CryptoGames.SM.Pos)
    (hpos_ep : pos.epoch = ep)
    (hsend_f : P.sendsIn ep = false)
    (hep_le : ep ≤ (esLoc.g.st P).tcur + 1)
    (ssLoc rsLoc : ℕ → _)
    (hvp : ∀ Q, (esLoc.g.st Q).id = (esM.g.st Q).id ∧
      (esLoc.g.st Q).tcur = (esM.g.st Q).tcur ∧
      (esLoc.g.st Q).γ = (esM.g.st Q).γ ∧
      (esLoc.g.st Q).root = (esM.g.st Q).root ∧
      (esLoc.g.st Q).curCkaMsg = (esM.g.st Q).curCkaMsg ∧
      (match (esLoc.g.st Q).vS, (esM.g.st Q).vS with
       | none, none => True
       | some (ss, none), some (.inl ssM) => ss = ssM
       | some (ss, some sIdx), some (.inr sIdxM) =>
         sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ ss = ssLoc sIdx ∧
         Q = Party.senderOf t ∧
         ((esLoc.g.st Q).tcur = t ∨ (esLoc.g.st Q).tcur = t + 1) ∧
         (∀ R sIdx', (esM.g.st R).vS = some (.inr sIdx') → R = Q ∧ sIdx' = sIdx)
       | _, _ => False) ∧
      (∀ ep', match (esLoc.g.st Q).vR ep', (esM.g.st Q).vR ep' with
       | none, none => True
       | some (rs, none), some (.inl rsM) => rs = rsM ∧ ep' ≠ t
       | some (rs, some sIdx), some (.inr sIdxM) =>
         ep' = t ∧ sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ rs = rsLoc sIdx ∧
         Q = Party.receiverOf t ∧ t ≤ (esLoc.g.st Q).tcur
       | _, _ => False))
    (vpL' : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
    (vpM' : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (rsvL' : RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ)
    (rsvM' : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
    (hLoc' : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM' tblL' : ℕ → SessHSt Pt ℓ)
    (ssLoc' : ℕ → RatchetSenderState (BitVec 256))
    (rsLoc' : ℕ → RatchetReceiverState (BitVec 256) (BitVec 256))
    (hvpL_ep : vpL'.tcur = max (esLoc.g.st P).tcur ep ∧ vpL'.id = P)
    (hlf' : phase1 = true → hM'.lfWin = false)
    (hsessM' : hM'.sessions = hLoc'.sessions)
    (hsess_nodup' : hLoc'.sessions.Nodup)
    (hsess_rem' : hLoc'.sessions.length + rem ≤ q)
    (hlen_le : esLoc.h.sessions.length ≤ hLoc'.sessions.length)
    (hsess_tH' : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH →
      (Function.update esLoc.g.st P vpL' (Party.senderOf t)).tcur < t → hLoc'.sessions = [])
    (htbl_loc' : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, hLoc'.table.lookup Ik =
        if Ik ∈ hLoc'.sessions then some (ks (hLoc'.sessions.idxOf Ik)) else none)
    (htbl_M' : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, (hM'.table.lookup Ik).isSome = decide (Ik ∈ hM'.sessions))
    (hcache' : ∀ ep', match hLoc'.cache ep', hM'.cache ep' with
      | none, none => True
      | some (TcL, σL, kL, idxL?), some (TcM, σM, kM, idxM?) =>
        TcL = TcM ∧ σL = σM ∧ idxL? = idxM? ∧
        match idxL? with
        | none => kL = kM ∧ ep' ≠ t
        | some sIdx => ep' = t ∧ sIdx < hLoc'.sessions.length ∧ kL = ks sIdx
      | _, _ => False)
    (hcache_tcur' : (Function.update esLoc.g.st P vpL' (Party.senderOf t)).tcur < t → hLoc'.cache t = none)
    (hbook_out' : ∀ sIdx, hLoc'.sessions.length ≤ sIdx → hM'.book sIdx = none)
    (htbl_out' : ∀ sIdx, hLoc'.sessions.length ≤ sIdx →
      tblM' sIdx = hInit (bs sIdx) (.seed (ks sIdx)) ∧
      (phase1 = true → tblL' sIdx = hInit (bs sIdx) (.seed (ks sIdx))))
    (hact' : ∀ sIdx, sIdx < hLoc'.sessions.length →
      ActiveSessInv C ℓ encT idOf phase1 (ks sIdx) (ssLoc' sIdx) (rsLoc' sIdx)
        ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL' sIdx))
    (hss_init' : (Function.update esLoc.g.st P vpL' (Party.senderOf t)).tcur < t →
      ∀ sIdx, sIdx < hLoc'.sessions.length →
        ssLoc' sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender (ks sIdx))
    (hrs_init' : (Function.update esLoc.g.st P vpL' (Party.receiverOf t)).tcur < t →
      ∀ sIdx, sIdx < hLoc'.sessions.length →
        rsLoc' sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver (ks sIdx))
    (hss_keep : ∀ j, j < esLoc.h.sessions.length → ssLoc' j = ssLoc j)
    (hrs_keep_ne_t : ep ≠ t → ∀ j, j < esLoc.h.sessions.length → rsLoc' j = rsLoc j)
    (hvpP_fields : vpL'.id = vpM'.id ∧ vpL'.tcur = vpM'.tcur ∧ vpL'.γ = vpM'.γ ∧
      vpL'.root = vpM'.root ∧ vpL'.curCkaMsg = vpM'.curCkaMsg ∧
      vpL'.vS = (esLoc.g.st P).vS ∧ vpM'.vS = (esM.g.st P).vS ∧
      vpL'.vR = Function.update (esLoc.g.st P).vR ep (some rsvL') ∧
      vpM'.vR = Function.update (esM.g.st P).vR ep (some rsvM'))
    (hvpP_vR_ep : match rsvL', rsvM' with
      | (rs, none), .inl rsM => rs = rsM ∧ ep ≠ t
      | (rs, some sIdx), .inr sIdxM =>
        ep = t ∧ sIdx = sIdxM ∧ sIdx < hLoc'.sessions.length ∧ rs = rsLoc' sIdx ∧
        P = Party.receiverOf t ∧ t ≤ vpL'.tcur
      | _, _ => False) :
    SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
      { g := esLoc.g.accept P vpL' pos, h := hLoc', abort := false }
      { g := esM.g.accept P vpM' pos, h := hM', abort := false }
      { g := esM.g.accept P vpM' pos, h := hM', abort := false }
      tblM' tblL' := by
  have hvSM_all : ∀ R, (Function.update esM.g.st P vpM' R).vS = (esM.g.st R).vS := by
    intro R; by_cases hRP : R = P
    · subst hRP; simp [hvpP_fields.2.2.2.2.2.2.1]
    · simp [Function.update_of_ne hRP]
  refine
    { habortL := rfl
      habortM := rfl
      habortLa := fun _ => rfl
      hwinL := by simp [GameState.accept, GameState.delete, hsync.hwinL]
      hwinM := by simp [GameState.accept, GameState.delete, hsync.hwinM]
      hwinLa := fun _ => by simp [GameState.accept, GameState.delete, hsync.hwinM]
      hlf := hlf'
      heraseM := eraseSt_accept hsync.heraseM P vpL' vpM' pos
      heraseLa := fun _ => rfl
      hh_La := fun _ => rfl
      hhealed := by simpa [GameState.accept, GameState.delete] using hsync.hhealed
      hginv := by
        intro r hr
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        exact hsync.hginv r hr.1
      hep_st := fun Q => by
        simp only [GameState.accept, GameState.delete]
        by_cases hQP : Q = P
        · subst hQP
          simp [Function.update_self, (hsync.hep_st Q).1, hpos_ep, hvpL_ep.1, hvpL_ep.2]
        · simp [Function.update_of_ne hQP, hsync.hep_st Q]
      hsessM := hsessM'
      hsess_nodup := hsess_nodup'
      hsess_rem := hsess_rem'
      hsess_tH := by simpa [GameState.accept, GameState.delete] using hsess_tH'
      htbl_loc := htbl_loc'
      htbl_M := by dsimp only; rw [← hsessM']; exact htbl_M'
      hcache := hcache'
      hcache_tcur := by simpa [GameState.accept, GameState.delete] using hcache_tcur'
      hbook_out := hbook_out'
      htbl_out := htbl_out'
      hstates := ⟨ssLoc', rsLoc', hact',
        by simpa [GameState.accept, GameState.delete] using hss_init',
        by simpa [GameState.accept, GameState.delete] using hrs_init',
        fun Q => ?_⟩ }
  simp only [GameState.accept, GameState.delete]
  by_cases hQP : Q = P
  · subst hQP
    simp only [Function.update_self]
    refine ⟨hvpP_fields.1, hvpP_fields.2.1, hvpP_fields.2.2.1, hvpP_fields.2.2.2.1,
      hvpP_fields.2.2.2.2.1, ?_, ?_⟩
    · rw [hvpP_fields.2.2.2.2.2.1, hvpP_fields.2.2.2.2.2.2.1]
      have h6 := (hvp Q).2.2.2.2.2.1
      cases hvSL : (esLoc.g.st Q).vS with
      | none =>
        cases hvSM : (esM.g.st Q).vS with
        | none => trivial
        | some _ => rw [hvSL, hvSM] at h6; exact False.elim h6
      | some pS =>
        rcases pS with ⟨ss, _ | sIdx⟩
        · cases hvSM : (esM.g.st Q).vS with
          | none => rw [hvSL, hvSM] at h6; exact False.elim h6
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL, hvSM] at h6; exact h6
            · rw [hvSL, hvSM] at h6; exact False.elim h6
        · cases hvSM : (esM.g.st Q).vS with
          | none => rw [hvSL, hvSM] at h6; exact False.elim h6
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL, hvSM] at h6; exact False.elim h6
            · rw [hvSL, hvSM] at h6
              dsimp only at h6 ⊢
              have htcur_new : vpL'.tcur = t ∨ vpL'.tcur = t + 1 := by
                rw [hvpL_ep.1]
                rcases h6.2.2.2.2.1 with ht0 | ht1
                · rw [ht0] at hep_le ⊢; omega
                · rw [ht1] at hep_le ⊢
                  have hne2 : ep ≠ t + 2 := by
                    intro he2
                    have hs2 := party_senderOf_sendsIn_add_two t
                    rw [← h6.2.2.2.1, ← he2, hsend_f] at hs2
                    cases hs2
                  omega
              refine ⟨h6.1, lt_of_lt_of_le h6.2.1 hlen_le,
                h6.2.2.1.trans (hss_keep sIdx h6.2.1).symm,
                h6.2.2.2.1, htcur_new, ?_⟩
              intro R idx' hR
              rw [hvSM_all R] at hR
              exact h6.2.2.2.2.2 R idx' hR
    · intro ep'
      rw [hvpP_fields.2.2.2.2.2.2.2.1, hvpP_fields.2.2.2.2.2.2.2.2]
      by_cases heq : ep' = ep
      · subst heq
        simp only [Function.update_self]
        rcases rsvL' with ⟨rs, _ | sIdx⟩ <;> rcases rsvM' with rsM | idxM
        · exact hvpP_vR_ep
        · exact False.elim hvpP_vR_ep
        · exact False.elim hvpP_vR_ep
        · exact hvpP_vR_ep
      · simp only [Function.update_of_ne heq]
        have hvp_ep := (hvp Q).2.2.2.2.2.2 ep'
        cases hvRL : (esLoc.g.st Q).vR ep' with
        | none =>
          cases hvRM : (esM.g.st Q).vR ep' with
          | none => trivial
          | some _ => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
        | some pL =>
          rcases pL with ⟨rs, _ | sIdx⟩
          · cases hvRM : (esM.g.st Q).vR ep' with
            | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
            | some x =>
              rcases x with rsM | idxM
              · rw [hvRL, hvRM] at hvp_ep; exact hvp_ep
              · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
          · cases hvRM : (esM.g.st Q).vR ep' with
            | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
            | some x =>
              rcases x with rsM | idxM
              · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
              · rw [hvRL, hvRM] at hvp_ep
                dsimp only at hvp_ep ⊢
                have hne_t : ep ≠ t := by intro ht; exact heq (hvp_ep.1.trans ht.symm)
                exact ⟨hvp_ep.1, hvp_ep.2.1, lt_of_lt_of_le hvp_ep.2.2.1 hlen_le,
                  hvp_ep.2.2.2.1.trans (hrs_keep_ne_t hne_t sIdx hvp_ep.2.2.1).symm,
                  hvp_ep.2.2.2.2.1, by rw [hvpL_ep.1]; exact le_trans hvp_ep.2.2.2.2.2 (le_max_left _ _)⟩
  · simp only [Function.update_of_ne hQP]
    rcases hvp Q with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
    · cases hvSL : (esLoc.g.st Q).vS with
      | none =>
        cases hvSM : (esM.g.st Q).vS with
        | none => trivial
        | some _ => rw [hvSL, hvSM] at h6; exact False.elim h6
      | some pS =>
        rcases pS with ⟨ss, _ | sIdx⟩
        · cases hvSM : (esM.g.st Q).vS with
          | none => rw [hvSL, hvSM] at h6; exact False.elim h6
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL, hvSM] at h6; exact h6
            · rw [hvSL, hvSM] at h6; exact False.elim h6
        · cases hvSM : (esM.g.st Q).vS with
          | none => rw [hvSL, hvSM] at h6; exact False.elim h6
          | some x =>
            rcases x with ssM | idxM
            · rw [hvSL, hvSM] at h6; exact False.elim h6
            · rw [hvSL, hvSM] at h6
              dsimp only at h6 ⊢
              refine ⟨h6.1, lt_of_lt_of_le h6.2.1 hlen_le,
                h6.2.2.1.trans (hss_keep sIdx h6.2.1).symm,
                h6.2.2.2.1, h6.2.2.2.2.1, ?_⟩
              intro R idx' hR
              rw [hvSM_all R] at hR
              exact h6.2.2.2.2.2 R idx' hR
    · intro ep'
      have hvp_ep := h7 ep'
      cases hvRL : (esLoc.g.st Q).vR ep' with
      | none =>
        cases hvRM : (esM.g.st Q).vR ep' with
        | none => trivial
        | some _ => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
      | some pL =>
        rcases pL with ⟨rs, _ | sIdx⟩
        · cases hvRM : (esM.g.st Q).vR ep' with
          | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
          | some x =>
            rcases x with rsM | idxM
            · rw [hvRL, hvRM] at hvp_ep; exact hvp_ep
            · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
        · cases hvRM : (esM.g.st Q).vR ep' with
          | none => rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
          | some x =>
            rcases x with rsM | idxM
            · rw [hvRL, hvRM] at hvp_ep; exact False.elim hvp_ep
            · rw [hvRL, hvRM] at hvp_ep
              dsimp only at hvp_ep ⊢
              by_cases hep_t : ep = t
              · have hPr : P = Party.receiverOf t := by
                  apply party_eq_receiverOf_of_not_sendsIn
                  rw [← hep_t, hsend_f]
                exact False.elim (hQP (hvp_ep.2.2.2.2.1.trans hPr.symm))
              · exact ⟨hvp_ep.1, hvp_ep.2.1, lt_of_lt_of_le hvp_ep.2.2.1 hlen_le,
                  hvp_ep.2.2.2.1.trans (hrs_keep_ne_t hep_t sIdx hvp_ep.2.2.1).symm,
                  hvp_ep.2.2.2.2.1, hvp_ep.2.2.2.2.2⟩

private theorem vRecv_guard_true_loc_eq {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    (hk : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec? : Option (Record M (Header T × E)))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true) :
    simulateQ lImpl ((liftH (vRecv hk ctx P s c rec?)).run es) = pure (some none, es) := by
  rw [liftH_run]; unfold vRecv
  simp [hg]

private theorem vRecv_guard_true_fsm_eq {Pt : Type} {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    {Γ Sig CCoins HS Γv Sv SSv RSv : Type}
    (hk : Hooks (FSMultiSpec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      HS Γ Pt Sig (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv Pt Sv SSv RSv (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (s : VP Γv Pt Sv SSv RSv)
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (es : EState (VP Γv Pt Sv SSv RSv) (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (st : (ℕ → Bool) × (ℕ → σT))
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true) :
    (simulateQ (pubFsMultiImpl impl) ((liftH (vRecv hk ctx P s c rec?)).run es)).run st =
      pure ((some none, es), st) := by
  rw [liftH_run]; unfold vRecv
  simp [hg]

private theorem vRecv_succ_none_loc_eq {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    (hk : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (ep : ℕ) (e : E) (rec? : Option (Record M (Header T × E)))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (hg : (s.id.sendsIn ep || decide (s.tcur + 1 < ep)) = false)
    (hsucc : ep = s.tcur + 1) :
    simulateQ lImpl ((liftH (vRecv hk ctx P s ((ep, none), e) rec?)).run es) =
      pure (some none, es) := by
  let _ := hg; subst ep; rw [liftH_run]; unfold vRecv
  simp

private theorem vRecv_succ_none_fsm_eq {Pt : Type} {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    {Γ Sig CCoins HS Γv Sv SSv RSv : Type}
    (hk : Hooks (FSMultiSpec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      HS Γ Pt Sig (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv Pt Sv SSv RSv (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (s : VP Γv Pt Sv SSv RSv)
    (ep : ℕ) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (es : EState (VP Γv Pt Sv SSv RSv) (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (st : (ℕ → Bool) × (ℕ → σT))
    (hg : (s.id.sendsIn ep || decide (s.tcur + 1 < ep)) = false)
    (hsucc : ep = s.tcur + 1) :
    (simulateQ (pubFsMultiImpl impl) ((liftH (vRecv hk ctx P s ((ep, none), e) rec?)).run es)).run st =
      pure ((some none, es), st) := by
  let _ := hg; subst ep; rw [liftH_run]; unfold vRecv
  simp

private theorem vRecv_succ_some_loc_eq {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    (hk : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (ep : ℕ) (Tn : T) (e : E) (rec? : Option (Record M (Header T × E)))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (hg : (s.id.sendsIn ep || decide (s.tcur + 1 < ep)) = false)
    (hsucc : ep = s.tcur + 1) :
    simulateQ lImpl ((liftH (vRecv hk ctx P s ((ep, some Tn), e) rec?)).run es) =
      (simulateQ lImpl ((hk.startRecv ctx P ep s.γ s.root Tn).run es.h) >>= fun p =>
        match p.1 with
        | none => pure (none, { es with h := p.2 })
        | some none => pure (some none, { es with h := p.2 })
        | some (some (γ', σ', rs)) =>
          simulateQ lImpl ((hk.fsRecv ctx P ep rs (ep, some Tn) e rec?).run p.2) >>= fun q =>
            match q.1 with
            | none => pure (none, { es with h := q.2 })
            | some none => pure (some none, { es with h := q.2 })
            | some (some (v', i', m')) =>
              pure (some (some (
                { s with tcur := ep, γ := γ', root := σ', vR := Function.update s.vR ep (some v') },
                ep, i', m')), { es with h := q.2 })) := by
  subst ep
  rw [liftH_run]
  unfold vRecv
  simp only [hg, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, bind_assoc,
    simulateQ_bind]
  congr 1; funext p
  rcases p with ⟨_ | _ | ⟨γ', σ', rs⟩, h1⟩
  · simp [StateT.run_pure, simulateQ_pure]
  · simp [StateT.run_pure, simulateQ_pure]
  · simp only [pure_bind, Function.update_self, StateT.run_bind,
      bind_assoc, simulateQ_bind]
    congr 1; funext q
    rcases q with ⟨_ | _ | ⟨v', i', m'⟩, h2⟩
    · simp [StateT.run_pure, simulateQ_pure]
    · simp [StateT.run_pure, simulateQ_pure]
    · have hupd : Function.update (Function.update s.vR (s.tcur + 1) (some rs)) (s.tcur + 1) (some v') =
          Function.update s.vR (s.tcur + 1) (some v') := by
        funext x; by_cases hx : x = s.tcur + 1 <;> simp [hx]
      simp [StateT.run_pure, simulateQ_pure, hupd]

private theorem vRecv_succ_some_fsm_eq {Pt : Type} {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    {Γ Sig CCoins HS Γv Sv SSv RSv : Type}
    (hk : Hooks (FSMultiSpec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      HS Γ Pt Sig (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv Pt Sv SSv RSv (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (s : VP Γv Pt Sv SSv RSv)
    (ep : ℕ) (Tn : Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (es : EState (VP Γv Pt Sv SSv RSv) (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (st : (ℕ → Bool) × (ℕ → σT))
    (hg : (s.id.sendsIn ep || decide (s.tcur + 1 < ep)) = false)
    (hsucc : ep = s.tcur + 1) :
    (simulateQ (pubFsMultiImpl impl) ((liftH (vRecv hk ctx P s ((ep, some Tn), e) rec?)).run es)).run st =
      ((simulateQ (pubFsMultiImpl impl) ((hk.startRecv ctx P ep s.γ s.root Tn).run es.h)).run st >>= fun p =>
        match p.1.1 with
        | none => pure ((none, { es with h := p.1.2 }), p.2)
        | some none => pure ((some none, { es with h := p.1.2 }), p.2)
        | some (some (γ', σ', rs)) =>
          (simulateQ (pubFsMultiImpl impl)
            ((hk.fsRecv ctx P ep rs (ep, some Tn) e rec?).run p.1.2)).run p.2 >>= fun q =>
            match q.1.1 with
            | none => pure ((none, { es with h := q.1.2 }), q.2)
            | some none => pure ((some none, { es with h := q.1.2 }), q.2)
            | some (some (v', i', m')) =>
              pure ((some (some (
                { s with tcur := ep, γ := γ', root := σ', vR := Function.update s.vR ep (some v') },
                ep, i', m')), { es with h := q.1.2 }), q.2)) := by
  subst ep
  rw [liftH_run]
  unfold vRecv
  simp only [hg, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, bind_assoc,
    simulateQ_bind]
  congr 1; funext p
  rcases p with ⟨⟨_ | _ | ⟨γ', σ', rs⟩, h1⟩, st1⟩
  · simp [StateT.run_pure, simulateQ_pure]
  · simp [StateT.run_pure, simulateQ_pure]
  · simp only [pure_bind, Function.update_self, StateT.run_bind,
      bind_assoc, simulateQ_bind]
    congr 1; funext q
    rcases q with ⟨⟨_ | _ | ⟨v', i', m'⟩, h2⟩, st2⟩
    · simp [StateT.run_pure, simulateQ_pure]
    · simp [StateT.run_pure, simulateQ_pure]
    · have hupd : Function.update (Function.update s.vR (s.tcur + 1) (some rs)) (s.tcur + 1) (some v') =
          Function.update s.vR (s.tcur + 1) (some v') := by
        funext x; by_cases hx : x = s.tcur + 1 <;> simp [hx]
      simp [StateT.run_pure, simulateQ_pure, hupd]

private theorem vRecv_le_loc_eq {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    (hk : Hooks nilSpec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv T Sv SSv RSv M E) (P : Party) (s : VP Γv T Sv SSv RSv)
    (c : Header T × E) (rec? : Option (Record M (Header T × E)))
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = false)
    (hnsucc : c.1.1 ≠ s.tcur + 1) :
    simulateQ lImpl ((liftH (vRecv hk ctx P s c rec?)).run es) =
      match s.vR c.1.1 with
      | none => pure (some none, es)
      | some rs =>
        simulateQ lImpl ((hk.fsRecv ctx P c.1.1 rs c.1 c.2 rec?).run es.h) >>= fun q =>
          match q.1 with
          | none => pure (none, { es with h := q.2 })
          | some none => pure (some none, { es with h := q.2 })
          | some (some (v', i', m')) =>
            pure (some (some ({ s with vR := Function.update s.vR c.1.1 (some v') },
              c.1.1, i', m')), { es with h := q.2 }) := by
  rw [liftH_run]; unfold vRecv
  simp only [hg, Bool.false_eq_true, ↓reduceIte, hnsucc, pure_bind]
  cases hv : s.vR c.1.1 with
  | none => simp
  | some rs =>
    simp only [StateT.run_bind, bind_assoc, simulateQ_bind]
    refine bind_congr fun q => ?_
    rcases q with ⟨_ | _ | ⟨v', i', m'⟩, h2⟩ <;> simp

private theorem vRecv_le_fsm_eq {Pt : Type} {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    {Γ Sig CCoins HS Γv Sv SSv RSv : Type}
    (hk : Hooks (FSMultiSpec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      HS Γ Pt Sig (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γv Sv SSv RSv)
    (ctx : Ctx Γv Pt Sv SSv RSv (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (s : VP Γv Pt Sv SSv RSv)
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (es : EState (VP Γv Pt Sv SSv RSv) (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (st : (ℕ → Bool) × (ℕ → σT))
    (hg : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = false)
    (hnsucc : c.1.1 ≠ s.tcur + 1) :
    (simulateQ (pubFsMultiImpl impl) ((liftH (vRecv hk ctx P s c rec?)).run es)).run st =
      match s.vR c.1.1 with
      | none => pure ((some none, es), st)
      | some rs =>
        (simulateQ (pubFsMultiImpl impl) ((hk.fsRecv ctx P c.1.1 rs c.1 c.2 rec?).run es.h)).run st >>= fun q =>
          match q.1.1 with
          | none => pure ((none, { es with h := q.1.2 }), q.2)
          | some none => pure ((some none, { es with h := q.1.2 }), q.2)
          | some (some (v', i', m')) =>
            pure ((some (some ({ s with vR := Function.update s.vR c.1.1 (some v') },
              c.1.1, i', m')), { es with h := q.1.2 }), q.2) := by
  rw [liftH_run]; unfold vRecv
  simp only [hg, Bool.false_eq_true, ↓reduceIte, hnsucc, pure_bind]
  cases hv : s.vR c.1.1 with
  | none => simp
  | some rs =>
    simp only [StateT.run_bind, bind_assoc, simulateQ_bind]
    refine bind_congr fun q => ?_
    rcases q with ⟨⟨_ | _ | ⟨v', i', m'⟩, h2⟩, st2⟩ <;> simp

private theorem syncDir1_esL_eq_esM {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {ℓ : ℕ} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {q Δcka l t : ℕ} {ks : ℕ → BitVec 256} {bs : ℕ → Bool}
    {phase1 : Bool} {rem : ℕ}
    {esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt)}
    {esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))}
    {tblM tblL : ℕ → SessHSt Pt ℓ}
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esL tblM tblL)
    (hp1 : phase1 = true) : esL = esM := by
  cases esL; cases esM
  simp only [EState.mk.injEq]
  exact ⟨hsync.heraseLa hp1, hsync.hh_La hp1, (hsync.habortLa hp1).trans hsync.habortM.symm⟩

private theorem syncDir1_unchanged_g {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ) (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (ssLoc : ℕ → RatchetSenderState (BitVec 256))
    (rsLoc : ℕ → RatchetReceiverState (BitVec 256) (BitVec 256))
    (hvp : ∀ Q, (esLoc.g.st Q).id = (esM.g.st Q).id ∧
      (esLoc.g.st Q).tcur = (esM.g.st Q).tcur ∧
      (esLoc.g.st Q).γ = (esM.g.st Q).γ ∧
      (esLoc.g.st Q).root = (esM.g.st Q).root ∧
      (esLoc.g.st Q).curCkaMsg = (esM.g.st Q).curCkaMsg ∧
      (match (esLoc.g.st Q).vS, (esM.g.st Q).vS with
       | none, none => True
       | some (ss, none), some (.inl ssM) => ss = ssM
       | some (ss, some sIdx), some (.inr sIdxM) =>
         sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ ss = ssLoc sIdx ∧
         Q = Party.senderOf t ∧
         ((esLoc.g.st Q).tcur = t ∨ (esLoc.g.st Q).tcur = t + 1) ∧
         (∀ R sIdx', (esM.g.st R).vS = some (.inr sIdx') → R = Q ∧ sIdx' = sIdx)
       | _, _ => False) ∧
      (∀ ep', match (esLoc.g.st Q).vR ep', (esM.g.st Q).vR ep' with
       | none, none => True
       | some (rs, none), some (.inl rsM) => rs = rsM ∧ ep' ≠ t
       | some (rs, some sIdx), some (.inr sIdxM) =>
         ep' = t ∧ sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ rs = rsLoc sIdx ∧
         Q = Party.receiverOf t ∧ t ≤ (esLoc.g.st Q).tcur
       | _, _ => False))
    (hLoc' : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hM' : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (tblM' tblL' : ℕ → SessHSt Pt ℓ)
    (ssLoc' : ℕ → RatchetSenderState (BitVec 256))
    (rsLoc' : ℕ → RatchetReceiverState (BitVec 256) (BitVec 256))
    (hlf' : phase1 = true → hM'.lfWin = false)
    (hsessM' : hM'.sessions = hLoc'.sessions)
    (hsess_nodup' : hLoc'.sessions.Nodup)
    (hsess_rem' : hLoc'.sessions.length + rem ≤ q)
    (hlen_le : esLoc.h.sessions.length ≤ hLoc'.sessions.length)
    (hsess_tH' : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH →
      (esLoc.g.st (Party.senderOf t)).tcur < t → hLoc'.sessions = [])
    (htbl_loc' : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, hLoc'.table.lookup Ik =
        if Ik ∈ hLoc'.sessions then some (ks (hLoc'.sessions.idxOf Ik)) else none)
    (htbl_M' : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, (hM'.table.lookup Ik).isSome = decide (Ik ∈ hLoc'.sessions))
    (hcache' : ∀ ep', match hLoc'.cache ep', hM'.cache ep' with
      | none, none => True
      | some (TcL, σL, kL, idxL?), some (TcM, σM, kM, idxM?) =>
        TcL = TcM ∧ σL = σM ∧ idxL? = idxM? ∧
        match idxL? with
        | none => kL = kM ∧ ep' ≠ t
        | some sIdx => ep' = t ∧ sIdx < hLoc'.sessions.length ∧ kL = ks sIdx
      | _, _ => False)
    (hcache_tcur' : (esLoc.g.st (Party.senderOf t)).tcur < t → hLoc'.cache t = none)
    (hbook_out' : ∀ sIdx, hLoc'.sessions.length ≤ sIdx → hM'.book sIdx = none)
    (htbl_out' : ∀ sIdx, hLoc'.sessions.length ≤ sIdx →
      tblM' sIdx = hInit (bs sIdx) (.seed (ks sIdx)) ∧
      (phase1 = true → tblL' sIdx = hInit (bs sIdx) (.seed (ks sIdx))))
    (hact' : ∀ sIdx, sIdx < hLoc'.sessions.length →
      ActiveSessInv C ℓ encT idOf phase1 (ks sIdx) (ssLoc' sIdx) (rsLoc' sIdx)
        ((hM'.book sIdx).getD {}) (tblM' sIdx) (tblL' sIdx))
    (hss_init' : (esLoc.g.st (Party.senderOf t)).tcur < t →
      ∀ sIdx, sIdx < hLoc'.sessions.length →
        ssLoc' sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender (ks sIdx))
    (hrs_init' : (esLoc.g.st (Party.receiverOf t)).tcur < t →
      ∀ sIdx, sIdx < hLoc'.sessions.length →
        rsLoc' sIdx = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver (ks sIdx))
    (hss_keep : ∀ j, j < esLoc.h.sessions.length → ssLoc' j = ssLoc j)
    (hrs_keep : ∀ j, j < esLoc.h.sessions.length → rsLoc' j = rsLoc j) :
    SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
      { esLoc with h := hLoc' } { esM with h := hM' } { esM with h := hM' } tblM' tblL' := by
  refine
    { habortL := hsync.habortL
      habortM := hsync.habortM
      habortLa := fun _ => hsync.habortM
      hwinL := hsync.hwinL
      hwinM := hsync.hwinM
      hwinLa := fun _ => hsync.hwinM
      hlf := hlf'
      heraseM := hsync.heraseM
      heraseLa := fun _ => rfl
      hh_La := fun _ => rfl
      hhealed := hsync.hhealed
      hginv := hsync.hginv
      hep_st := hsync.hep_st
      hsessM := hsessM'
      hsess_nodup := hsess_nodup'
      hsess_rem := hsess_rem'
      hsess_tH := hsess_tH'
      htbl_loc := htbl_loc'
      htbl_M := htbl_M'
      hcache := hcache'
      hcache_tcur := hcache_tcur'
      hbook_out := hbook_out'
      htbl_out := htbl_out'
      hstates := ⟨ssLoc', rsLoc', hact', hss_init', hrs_init', fun Q => ?_⟩ }
  refine ⟨(hvp Q).1, (hvp Q).2.1, (hvp Q).2.2.1, (hvp Q).2.2.2.1, (hvp Q).2.2.2.2.1, ?_, ?_⟩
  · have hvS := (hvp Q).2.2.2.2.2.1
    cases hvSL : (esLoc.g.st Q).vS with
    | none =>
      cases hvSM : (esM.g.st Q).vS <;> (rw [hvSL, hvSM] at hvS; exact hvS)
    | some pL =>
      rcases pL with ⟨ss, _ | sIdx⟩
      · cases hvSM : (esM.g.st Q).vS with
        | none => rw [hvSL, hvSM] at hvS; exact False.elim hvS
        | some x =>
          rcases x with ssM | idxM <;> (rw [hvSL, hvSM] at hvS; exact hvS)
      · cases hvSM : (esM.g.st Q).vS with
        | none => rw [hvSL, hvSM] at hvS; exact False.elim hvS
        | some x =>
          rcases x with ssM | idxM
          · rw [hvSL, hvSM] at hvS; exact False.elim hvS
          · rw [hvSL, hvSM] at hvS; dsimp only at hvS ⊢
            exact ⟨hvS.1, lt_of_lt_of_le hvS.2.1 hlen_le,
              hvS.2.2.1.trans (hss_keep sIdx hvS.2.1).symm, hvS.2.2.2⟩
  · intro ep'
    have hvR := (hvp Q).2.2.2.2.2.2 ep'
    cases hvRL : (esLoc.g.st Q).vR ep' with
    | none =>
      cases hvRM : (esM.g.st Q).vR ep' <;> (rw [hvRL, hvRM] at hvR; exact hvR)
    | some pL =>
      rcases pL with ⟨rs, _ | sIdx⟩
      · cases hvRM : (esM.g.st Q).vR ep' with
        | none => rw [hvRL, hvRM] at hvR; exact False.elim hvR
        | some x =>
          rcases x with rsM | idxM <;> (rw [hvRL, hvRM] at hvR; exact hvR)
      · cases hvRM : (esM.g.st Q).vR ep' with
        | none => rw [hvRL, hvRM] at hvR; exact False.elim hvR
        | some x =>
          rcases x with rsM | idxM
          · rw [hvRL, hvRM] at hvR; exact False.elim hvR
          · rw [hvRL, hvRM] at hvR; dsimp only at hvR ⊢
            exact ⟨hvR.1, hvR.2.1, lt_of_lt_of_le hvR.2.2.1 hlen_le,
              hvR.2.2.2.1.trans (hrs_keep sIdx hvR.2.2.1).symm, hvR.2.2.2.2⟩

private theorem startRecv_hit_loc_eq {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode) (q : ℕ) (ks : ℕ → K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig) (Tn Tc : T) (σc : Sig) (k : K) (idx? : Option ℕ)
    (hLoc : LState T Sig K I)
    (hc : hLoc.cache ep = some (Tc, σc, k, idx?)) (hTc : Tc = Tn) :
    simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).startRecv ctx P ep γ σ Tn).run hLoc) =
      pure (some (some ((cka.receive γ Tn).1, σc, (fs.initReceiver k, idx?))), hLoc) := by
  dsimp only [hooksLocalPrefix]
  simp [hc, hTc, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]

private theorem startRecv_hit_fsm_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    {KC Γ CCoins KR : Type} [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt Pt) (prng : PRFPRNG KR (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ Pt (BitVec 256) (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (γ : Γ) (σ : BitVec 256) (Tn Tc : Pt) (σc k : BitVec 256) (idx? : Option ℕ)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT))
    (hc : hM.cache ep = some (Tc, σc, k, idx?)) (hTc : Tc = Tn) :
    (simulateQ (pubFsMultiImpl impl)
      (((hooksFSMulti cka prng fs Δcka mo false la).startRecv ctx P ep γ σ Tn).run hM)).run st =
      pure ((some (some ((cka.receive γ Tn).1, σc,
        match idx? with
        | none => .inl (fs.initReceiver k)
        | some sIdx => .inr sIdx)), hM), st) := by
  dsimp only [hooksFSMulti]
  cases idx? <;> simp [hc, hTc, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]

private theorem startRecv_miss_ne_loc_eq {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l t q : ℕ) (ks : ℕ → K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig) (Tn : T)
    (hLoc : LState T Sig K I)
    (hmiss : ∀ σc k idx?, hLoc.cache ep ≠ some (Tn, σc, k, idx?))
    (hne : ep ≠ t) :
    simulateQ lImpl
      (((hooksLocalPrefix cka prng fs ⟨true, some (l - 1), t⟩ q ks).startRecv ctx P ep γ σ Tn).run hLoc) =
      pure (some none, hLoc) := by
  dsimp only [hooksLocalPrefix]
  rcases hc : hLoc.cache ep with _ | ⟨Tc, σc, k, idx?⟩
  · simp [hc, hne, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
  · have hTc : Tc ≠ Tn := fun heq => hmiss σc k idx? (heq ▸ hc)
    simp [hc, hTc, hne, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]

private theorem startRecv_miss_ne_fsm_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    {KC Γ CCoins KR : Type} [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt Pt) (prng : PRFPRNG KR (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka l t : ℕ) (la : Bool)
    (ctx : Ctx Γ Pt (BitVec 256) (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (ep : ℕ) (γ : Γ) (σ : BitVec 256) (Tn : Pt)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT))
    (hmiss : ∀ σc k idx?, hM.cache ep ≠ some (Tn, σc, k, idx?))
    (hne : ep ≠ t) :
    (simulateQ (pubFsMultiImpl impl)
      (((hooksFSMulti cka prng fs Δcka ⟨true, some (l - 1), t⟩ false la).startRecv
        ctx P ep γ σ Tn).run hM)).run st =
      pure ((some none, hM), st) := by
  dsimp only [hooksFSMulti]
  rcases hc : hM.cache ep with _ | ⟨Tc, σc, k, idx?⟩
  · simp [hc, hne, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
  · have hTc : Tc ≠ Tn := fun heq => hmiss σc k idx? (heq ▸ hc)
    simp [hc, hTc, hne, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]

private theorem startRecv_miss_tH_loc_eq {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l t q : ℕ) (ks : ℕ → K)
    (ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (γ : Γ) (σ : Sig) (Tn : T)
    (hLoc : LState T Sig K I)
    (hmiss : ∀ σc k idx?, hLoc.cache t ≠ some (Tn, σc, k, idx?))
    (htH : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH) :
    simulateQ lImpl
      (((hooksLocalPrefix cka prng fs ⟨true, some (l - 1), t⟩ q ks).startRecv ctx P t γ σ Tn).run hLoc) =
      pure (none, hLoc) := by
  have htH' : (⟨true, some (l - 1), t⟩ : Mode).tH = t := htH.symm
  dsimp only [hooksLocalPrefix]
  rcases hc : hLoc.cache t with _ | ⟨Tc, σc, k, idx?⟩
  · simp [hc, htH', StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
  · have hTc : Tc ≠ Tn := fun heq => hmiss σc k idx? (heq ▸ hc)
    simp [hc, hTc, htH', StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]

private theorem startRecv_miss_ne_tH_loc_eq {KC Γ CCoins Pt KR SS RS M E : Type}
    [DecidableEq Pt] [SampleableType CCoins] [SampleableType Pt]
    (cka : CKAScheme KC Γ CCoins Pt Pt) (prng : PRFPRNG KR (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) SS RS (Header Pt) M E) (l t q : ℕ) (ks : ℕ → BitVec 256)
    (ctx : Ctx Γ Pt (BitVec 256) (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (γ : Γ) (σ : BitVec 256) (Tn : Pt)
    (hLoc : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hmiss : ∀ σc k idx?, hLoc.cache t ≠ some (Tn, σc, k, idx?))
    (htH : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH)
    (htbl : ∀ Ik', hLoc.table.lookup Ik' =
      if Ik' ∈ hLoc.sessions then some (ks (hLoc.sessions.idxOf Ik')) else none)
    (hlen : hLoc.sessions.length < q) :
    let kk := cka.receive γ Tn
    simulateQ lImpl
      (((hooksLocalPrefix cka prng fs ⟨true, some (l - 1), t⟩ q ks).startRecv ctx P t γ σ Tn).run hLoc) =
      if kk.2 ∈ hLoc.sessions then
        pure (some (some (kk.1, (prng.up σ kk.2).1,
          (fs.initReceiver (ks (hLoc.sessions.idxOf kk.2)), some (hLoc.sessions.idxOf kk.2)))), hLoc)
      else
        (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun _ =>
          pure (some (some (kk.1, (prng.up σ kk.2).1,
            (fs.initReceiver (ks hLoc.sessions.length), some hLoc.sessions.length))),
            { hLoc with table := (kk.2, ks hLoc.sessions.length) :: hLoc.table, sessions := hLoc.sessions ++ [kk.2] })) := by
  dsimp only
  have hne : t ≠ (⟨true, some (l - 1), t⟩ : Mode).tH := htH
  have hon_none : simulateQ lImpl
      (((hooksLocalPrefix cka prng fs ⟨true, some (l - 1), t⟩ q ks).startRecv ctx P t γ σ Tn).run hLoc) =
      simulateQ lImpl ((do
        let kk := cka.receive γ Tn
        let k' ← lookupFLPrefix q ks kk.2
        let idx ← regSess kk.2
        pure (some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx))))).run hLoc) := by
    dsimp only [hooksLocalPrefix]
    rcases hc : hLoc.cache t with _ | ⟨Tc, σc, k, idx?⟩
    · simp [hc, hne, StateT.run_bind, StateT.run_get]
    · have hTc : Tc ≠ Tn := fun heq => hmiss σc k idx? (heq ▸ hc)
      simp [hc, hTc, hne, StateT.run_bind, StateT.run_get]
  rw [hon_none]
  by_cases hmem : (cka.receive γ Tn).2 ∈ hLoc.sessions
  · have hlk : hLoc.table.lookup (cka.receive γ Tn).2 =
        some (ks (hLoc.sessions.idxOf (cka.receive γ Tn).2)) := by
      rw [htbl]; simp [hmem]
    simp [lookupFLPrefix, regSess, hlk, hmem]
  · have hlk : hLoc.table.lookup (cka.receive γ Tn).2 = none := by rw [htbl]; simp [hmem]
    simp [lookupFLPrefix, regSess, hlk, hmem, hlen]

private theorem startRecv_miss_ne_tH_fsm_eq {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    {ℓ : ℕ} {σT : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σT ProbComp))
    {KC Γ CCoins KR : Type} [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt Pt) (prng : PRFPRNG KR (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (Δcka l t : ℕ) (la : Bool)
    (ctx : Ctx Γ Pt (BitVec 256) (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party) (γ : Γ) (σ : BitVec 256) (Tn : Pt)
    (hM : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (st : (ℕ → Bool) × (ℕ → σT))
    (hmiss : ∀ σc k idx?, hM.cache t ≠ some (Tn, σc, k, idx?))
    (htH : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH)
    (htbl : ∀ Ik', (hM.table.lookup Ik').isSome = decide (Ik' ∈ hM.sessions)) :
    let kk := cka.receive γ Tn
    (simulateQ (pubFsMultiImpl impl)
      (((hooksFSMulti cka prng fs Δcka ⟨true, some (l - 1), t⟩ false la).startRecv
        ctx P t γ σ Tn).run hM)).run st =
      if kk.2 ∈ hM.sessions then
        pure ((some (some (kk.1, (prng.up σ kk.2).1, .inr (hM.sessions.idxOf kk.2))), hM), st)
      else
        (($ᵗ (BitVec 256) : ProbComp (BitVec 256)) >>= fun k_draw =>
          pure ((some (some (kk.1, (prng.up σ kk.2).1, .inr hM.sessions.length)),
            { hM with table := (kk.2, k_draw) :: hM.table, sessions := hM.sessions ++ [kk.2] }), st)) := by
  dsimp only
  have hne : t ≠ (⟨true, some (l - 1), t⟩ : Mode).tH := htH
  have hon_none : (simulateQ (pubFsMultiImpl impl)
      (((hooksFSMulti cka prng fs Δcka ⟨true, some (l - 1), t⟩ false la).startRecv
        ctx P t γ σ Tn).run hM)).run st =
      (simulateQ (pubFsMultiImpl impl) ((do
        let kk := cka.receive γ Tn
        let k' ← lookupMultiF kk.2
        let idx ← regSessMulti kk.2
        pure (some (some (kk.1, (prng.up σ kk.2).1,
          (Sum.inr idx : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))))).run hM)).run st := by
    dsimp only [hooksFSMulti]
    rcases hc : hM.cache t with _ | ⟨Tc, σc, k, idx?⟩
    · simp [hc, hne, StateT.run_bind, StateT.run_get]
    · have hTc : Tc ≠ Tn := fun heq => hmiss σc k idx? (heq ▸ hc)
      simp [hc, hTc, hne, StateT.run_bind, StateT.run_get]
  rw [hon_none]
  by_cases hmem : (cka.receive γ Tn).2 ∈ hM.sessions
  · have his : (hM.table.lookup (cka.receive γ Tn).2).isSome = true := by rw [htbl]; simp [hmem]
    cases hlk : hM.table.lookup (cka.receive γ Tn).2 with
    | none => rw [hlk] at his; cases his
    | some k0 => simp [lookupMultiF, regSessMulti, hlk, hmem]
  · have his : (hM.table.lookup (cka.receive γ Tn).2).isSome = false := by rw [htbl]; simp [hmem]
    have hlk : hM.table.lookup (cka.receive γ Tn).2 = none := Option.not_isSome_iff_eq_none.mp (by simp [his])
    unfold lookupMultiF regSessMulti
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hlk, bind_assoc]
    rw [simulateQ_bind, StateT.run_bind, simulateQ_pubFsMulti_sampleT_run]
    simp [hmem]

private theorem fsRecv_inr_vRecv_tail_cps {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (ssLoc : ℕ → RatchetSenderState (BitVec 256))
    (rsLoc : ℕ → RatchetReceiverState (BitVec 256) (BitVec 256))
    (hvp : ∀ Q, (esLoc.g.st Q).id = (esM.g.st Q).id ∧
      (esLoc.g.st Q).tcur = (esM.g.st Q).tcur ∧
      (esLoc.g.st Q).γ = (esM.g.st Q).γ ∧
      (esLoc.g.st Q).root = (esM.g.st Q).root ∧
      (esLoc.g.st Q).curCkaMsg = (esM.g.st Q).curCkaMsg ∧
      (match (esLoc.g.st Q).vS, (esM.g.st Q).vS with
       | none, none => True
       | some (ss, none), some (.inl ssM) => ss = ssM
       | some (ss, some sIdx), some (.inr sIdxM) =>
         sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ ss = ssLoc sIdx ∧
         Q = Party.senderOf t ∧
         ((esLoc.g.st Q).tcur = t ∨ (esLoc.g.st Q).tcur = t + 1) ∧
         (∀ R sIdx', (esM.g.st R).vS = some (.inr sIdx') → R = Q ∧ sIdx' = sIdx)
       | _, _ => False) ∧
      (∀ ep', match (esLoc.g.st Q).vR ep', (esM.g.st Q).vR ep' with
       | none, none => True
       | some (rs, none), some (.inl rsM) => rs = rsM ∧ ep' ≠ t
       | some (rs, some sIdx), some (.inr sIdxM) =>
         ep' = t ∧ sIdx = sIdxM ∧ sIdx < esLoc.h.sessions.length ∧ rs = rsLoc sIdx ∧
         Q = Party.receiverOf t ∧ t ≤ (esLoc.g.st Q).tcur
       | _, _ => False))
    (P : Party) (hsend_f : P.sendsIn t = false) (ht_le : t ≤ (esLoc.g.st P).tcur + 1)
    (Topt : Option Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (vpBaseL : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
    (vpBaseM : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (hvpBase_ep : vpBaseL.tcur = max (esLoc.g.st P).tcur t ∧ vpBaseL.id = P)
    (hvpBase_fields : vpBaseL.id = vpBaseM.id ∧ vpBaseL.tcur = vpBaseM.tcur ∧
      vpBaseL.γ = vpBaseM.γ ∧ vpBaseL.root = vpBaseM.root ∧
      vpBaseL.curCkaMsg = vpBaseM.curCkaMsg ∧
      vpBaseL.vS = (esLoc.g.st P).vS ∧ vpBaseM.vS = (esM.g.st P).vS)
    (sIdx : ℕ) (rs0 : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hLoc1 : LState Pt (BitVec 256) (BitVec 256) Pt)
    (hM1 : FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
    (ssLoc1 : ℕ → RatchetSenderState (BitVec 256))
    (rsLoc1 : ℕ → RatchetReceiverState (BitVec 256) (BitVec 256))
    (hs_lt : sIdx < hLoc1.sessions.length)
    (hrs0 : rs0 = rsLoc1 sIdx)
    (hlf1 : phase1 = true → hM1.lfWin = false)
    (hsessM1 : hM1.sessions = hLoc1.sessions)
    (hsess_nodup1 : hLoc1.sessions.Nodup)
    (hsess_rem1 : hLoc1.sessions.length + rem ≤ q)
    (hlen_le1 : esLoc.h.sessions.length ≤ hLoc1.sessions.length)
    (hsess_tH1 : (⟨true, some (l - 1), t⟩ : Mode).tStar = (⟨true, some (l - 1), t⟩ : Mode).tH →
      (esLoc.g.st (Party.senderOf t)).tcur < t → hLoc1.sessions = [])
    (htbl_loc1 : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, hLoc1.table.lookup Ik =
        if Ik ∈ hLoc1.sessions then some (ks (hLoc1.sessions.idxOf Ik)) else none)
    (htbl_M1 : (⟨true, some (l - 1), t⟩ : Mode).tStar ≠ (⟨true, some (l - 1), t⟩ : Mode).tH →
      ∀ Ik, (hM1.table.lookup Ik).isSome = decide (Ik ∈ hLoc1.sessions))
    (hcache1 : ∀ ep', match hLoc1.cache ep', hM1.cache ep' with
      | none, none => True
      | some (TcL, σL, kL, idxL?), some (TcM, σM, kM, idxM?) =>
        TcL = TcM ∧ σL = σM ∧ idxL? = idxM? ∧
        match idxL? with
        | none => kL = kM ∧ ep' ≠ t
        | some sIdx' => ep' = t ∧ sIdx' < hLoc1.sessions.length ∧ kL = ks sIdx'
      | _, _ => False)
    (hcache_tcur1 : (esLoc.g.st (Party.senderOf t)).tcur < t → hLoc1.cache t = none)
    (hbook_out1 : ∀ j, hLoc1.sessions.length ≤ j → hM1.book j = none)
    (htbl_out1 : ∀ j, hLoc1.sessions.length ≤ j →
      tblM j = hInit (bs j) (.seed (ks j)) ∧
      (phase1 = true → tblL j = hInit (bs j) (.seed (ks j))))
    (hact1 : ∀ j, j < hLoc1.sessions.length →
      ActiveSessInv C ℓ encT idOf phase1 (ks j) (ssLoc1 j) (rsLoc1 j)
        ((hM1.book j).getD {}) (tblM j) (tblL j))
    (hss_init1 : (esLoc.g.st (Party.senderOf t)).tcur < t →
      ∀ j, j < hLoc1.sessions.length →
        ssLoc1 j = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender (ks j))
    (hrs_init1 : (esLoc.g.st (Party.receiverOf t)).tcur < t →
      ∀ j, j < hLoc1.sessions.length →
        rsLoc1 j = (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver (ks j))
    (hss_keep1 : ∀ j, j < esLoc.h.sessions.length → ssLoc1 j = ssLoc j)
    (hrs_keep1 : ∀ j, j < esLoc.h.sessions.length → rsLoc1 j = rsLoc j)
    (fLoc : _ → ProbComp Bool)
    (fM fL : (_ × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) → ProbComp Bool)
    (habort_lf : phase1 = true → ∀ hM' tblL', hM'.lfWin = true →
      𝒟[fL ((none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblL'))] {true} = 1)
    (hrej : ∀ hLoc' hM' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
        { esLoc with h := hLoc' } { esM with h := hM' } { esM with h := hM' } tblM' tblL' →
      Dir1Rel phase1
        (fLoc (some none, { esLoc with h := hLoc' }))
        (fM ((some none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblM')))
        (fL ((some none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblL'))))
    (hacc : ∀ vpL' vpM' i' m' hLoc' hM' tblM' tblL',
      (∀ pos : Pos, pos.epoch = t →
        SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
          { g := esLoc.g.accept P vpL' pos, h := hLoc', abort := false }
          { g := esM.g.accept P vpM' pos, h := hM', abort := false }
          { g := esM.g.accept P vpM' pos, h := hM', abort := false }
          tblM' tblL') →
      Dir1Rel phase1
        (fLoc (some (some (vpL', t, i', m')), { esLoc with h := hLoc' }))
        (fM ((some (some (vpM', t, i', m')), { esM with h := hM' }), (fun (_ : ℕ) => false, tblM')))
        (fL ((some (some (vpM', t, i', m')), { esM with h := hM' }), (fun (_ : ℕ) => false, tblL')))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    Dir1Rel phase1
      ((simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).fsRecv
          esLoc.g P t (rs0, some sIdx) (t, Topt) e rec?).run hLoc1) >>= fun q0 =>
        match q0.1 with
        | none => pure (none, { esLoc with h := q0.2 })
        | some none => pure (some none, { esLoc with h := q0.2 })
        | some (some (v', i', m')) =>
          pure (some (some ({ vpBaseL with vR := Function.update (esLoc.g.st P).vR t (some v') },
            t, i', m')), { esLoc with h := q0.2 })) >>= fLoc)
      (((simulateQ (pubFsMultiImpl (impl false)) (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv
          esM.g P t (.inr sIdx) (t, Topt) e rec?).run hM1)).run (fun _ => false, tblM) >>= fun q0 =>
        match q0.1.1 with
        | none => pure ((none, { esM with h := q0.1.2 }), q0.2)
        | some none => pure ((some none, { esM with h := q0.1.2 }), q0.2)
        | some (some (v', i', m')) =>
          pure ((some (some ({ vpBaseM with vR := Function.update (esM.g.st P).vR t (some v') },
            t, i', m')), { esM with h := q0.1.2 }), q0.2)) >>= fM)
      (((simulateQ (pubFsMultiImpl (impl true)) (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv
          esM.g P t (.inr sIdx) (t, Topt) e rec?).run hM1)).run (fun _ => false, tblL) >>= fun q0 =>
        match q0.1.1 with
        | none => pure ((none, { esM with h := q0.1.2 }), q0.2)
        | some none => pure ((some none, { esM with h := q0.1.2 }), q0.2)
        | some (some (v', i', m')) =>
          pure ((some (some ({ vpBaseM with vR := Function.update (esM.g.st P).vR t (some v') },
            t, i', m')), { esM with h := q0.1.2 }), q0.2)) >>= fL) := by
  intro cka prng fs mo impl
  have hP_recv : P = Party.receiverOf t := party_eq_receiverOf_of_not_sendsIn hsend_f
  have hP_ne_send : P ≠ Party.senderOf t := by
    intro heq; rw [heq, party_senderOf_sendsIn] at hsend_f; cases hsend_f
  have hinv0 : ActiveSessInv C ℓ encT idOf phase1 (ks sIdx)
      (ssLoc1 sIdx) rs0 ((hM1.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) := by
    rw [hrs0]; exact hact1 sIdx hs_lt
  rcases fsRecv_dir1_inr C hD hrt ℓ hℓ Dh encPt encT idOf Δcka l t phase1
      esM.g P hsync.hhealed sIdx (t, Topt) e rec? (ks sIdx)
      (ssLoc1 sIdx) rs0 hM1 tblM tblL hinv0 with
    ⟨hp1, sL', hfsL⟩ | ⟨hM', tblM', tblL', hsess_eq, hcache_eq, htbl_eq, hlf_eq, hother, hres⟩
  · subst hp1
    apply leAdd_of_la_one
    dsimp (config := { zetaDelta := true }) only at hfsL ⊢
    rw [bind_assoc, hfsL]
    simp only [pure_bind]
    exact habort_lf rfl { hM1 with lfWin := true } (Function.update tblL sIdx sL') rfl
  · cases hrcv : fs.receive rs0 (t, Topt) e with
    | none =>
      rw [hrcv] at hres
      rcases hres with ⟨hfsM, hfsL, hinv'⟩
      have hloc_run : simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).fsRecv
          esLoc.g P t (rs0, some sIdx) (t, Topt) e rec?).run hLoc1) =
          pure (some none, hLoc1) := by
        dsimp only [hooksLocalPrefix]
        simp [hrcv, StateT.run_pure, simulateQ_pure]
      have hsync_rej := syncDir1_unchanged_g C ℓ encT idOf q Δcka l t ks bs phase1 rem
        esLoc esM esL tblM tblL hsync ssLoc rsLoc hvp
        hLoc1 hM' tblM' tblL' ssLoc1 rsLoc1
        (fun hp1 => hlf_eq.trans (hlf1 hp1))
        (hsess_eq.trans hsessM1) hsess_nodup1 hsess_rem1 hlen_le1 hsess_tH1
        htbl_loc1 (fun hne Ik => by rw [htbl_eq]; exact htbl_M1 hne Ik)
        (fun ep' => by rw [hcache_eq]; exact hcache1 ep')
        hcache_tcur1
        (fun j hj => by
          have hne : j ≠ sIdx := by omega
          rw [(hother j hne).1]; exact hbook_out1 j hj)
        (fun j hj => by
          have hne : j ≠ sIdx := by omega
          exact ⟨(hother j hne).2.1.trans (htbl_out1 j hj).1,
            fun hp1 => ((hother j hne).2.2 hp1).trans ((htbl_out1 j hj).2 hp1)⟩)
        (fun j hj => by
          by_cases hjeq : j = sIdx
          · subst hjeq; rw [← hrs0]; exact hinv'
          · rw [(hother j hjeq).1, (hother j hjeq).2.1]
            exact activeSessInv_mono_phase C ℓ encT idOf id
              (fun hp1 => (hother j hjeq).2.2 hp1) (hact1 j hj))
        hss_init1 hrs_init1 hss_keep1 hrs_keep1
      rw [bind_assoc, hloc_run]
      simp only [pure_bind]
      dsimp (config := { zetaDelta := true }) only at hfsM ⊢
      rw [bind_assoc, hfsM]
      simp only [pure_bind]
      refine dir1Rel_mono_phase id (fun hp1 => ?_) (hrej hLoc1 hM' tblM' tblL' hsync_rej)
      have hfsL' := hfsL hp1
      dsimp (config := { zetaDelta := true }) only at hfsL' ⊢
      rw [bind_assoc, hfsL']
      simp only [pure_bind]
    | some trio =>
      rcases trio with ⟨rs', i', m'⟩
      rw [hrcv] at hres
      rcases hres with ⟨hfsM, hfsL, hinv'⟩
      let hLoc' := { hLoc1 with lastIdx := some sIdx }
      let vpL' := { vpBaseL with vR := Function.update (esLoc.g.st P).vR t (some (rs', some sIdx)) }
      let vpM' := { vpBaseM with vR := Function.update (esM.g.st P).vR t (some (.inr sIdx)) }
      have hloc_run : simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).fsRecv
          esLoc.g P t (rs0, some sIdx) (t, Topt) e rec?).run hLoc1) =
          pure (some (some ((rs', some sIdx), i', m')), hLoc') := by
        dsimp only [hooksLocalPrefix]
        simp [hrcv, hLoc', StateT.run_modify, simulateQ_pure]
      have hcom_sync : ∀ pos : Pos, pos.epoch = t →
          SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
            { g := esLoc.g.accept P vpL' pos, h := hLoc', abort := false }
            { g := esM.g.accept P vpM' pos, h := hM', abort := false }
            { g := esM.g.accept P vpM' pos, h := hM', abort := false }
            tblM' tblL' := by
        intro pos hpos_ep
        have hvpL_ep : vpL'.tcur = max (esLoc.g.st P).tcur t ∧ vpL'.id = P := hvpBase_ep
        have ht_le_vpL : t ≤ vpL'.tcur := by rw [hvpL_ep.1]; exact Nat.le_max_right _ _
        have hsender_tcur : (Function.update esLoc.g.st P vpL' (Party.senderOf t)).tcur =
            (esLoc.g.st (Party.senderOf t)).tcur := by
          rw [Function.update_of_ne hP_ne_send.symm]
        exact syncDir1_accept C ℓ encT idOf q Δcka l t ks bs phase1 rem
          esLoc esM esL tblM tblL hsync P t pos hpos_ep hsend_f ht_le
          ssLoc rsLoc hvp vpL' vpM' (rs', some sIdx) (.inr sIdx)
          hLoc' hM' tblM' tblL' ssLoc1 (Function.update rsLoc1 sIdx rs')
          hvpL_ep
          (fun hp1 => hlf_eq.trans (hlf1 hp1))
          (hsess_eq.trans hsessM1) hsess_nodup1 hsess_rem1 hlen_le1
          (fun heq hlt => hsess_tH1 heq (by rwa [hsender_tcur] at hlt))
          htbl_loc1
          (fun hne Ik => by rw [htbl_eq, hsess_eq, hsessM1]; exact htbl_M1 hne Ik)
          (fun ep' => by rw [hcache_eq]; exact hcache1 ep')
          (fun hlt => hcache_tcur1 (by rwa [hsender_tcur] at hlt))
          (fun j hj => by
            have hne : j ≠ sIdx := by dsimp only [hLoc'] at hj; omega
            rw [(hother j hne).1]; exact hbook_out1 j hj)
          (fun j hj => by
            have hne : j ≠ sIdx := by dsimp only [hLoc'] at hj; omega
            exact ⟨(hother j hne).2.1.trans (htbl_out1 j hj).1,
              fun hp1 => ((hother j hne).2.2 hp1).trans ((htbl_out1 j hj).2 hp1)⟩)
          (fun j hj => by
            by_cases hjeq : j = sIdx
            · subst hjeq; simpa [Function.update_self] using hinv'
            · rw [Function.update_of_ne hjeq, (hother j hjeq).1, (hother j hjeq).2.1]
              exact activeSessInv_mono_phase C ℓ encT idOf id
                (fun hp1 => (hother j hjeq).2.2 hp1) (hact1 j hj))
          (fun hlt => hss_init1 (by rwa [hsender_tcur] at hlt))
          (fun hlt => by
            rw [← hP_recv, Function.update_self] at hlt
            exact False.elim (Nat.not_lt.mpr ht_le_vpL hlt))
          hss_keep1
          (fun hne => False.elim (hne rfl))
          ⟨hvpBase_fields.1, hvpBase_fields.2.1, hvpBase_fields.2.2.1, hvpBase_fields.2.2.2.1,
            hvpBase_fields.2.2.2.2.1, hvpBase_fields.2.2.2.2.2.1, hvpBase_fields.2.2.2.2.2.2,
            rfl, rfl⟩
          ⟨rfl, rfl, hs_lt, (Function.update_self sIdx rs' rsLoc1).symm, hP_recv, ht_le_vpL⟩
      rw [bind_assoc, hloc_run]
      simp only [pure_bind]
      dsimp (config := { zetaDelta := true }) only at hfsM ⊢
      rw [bind_assoc, hfsM]
      simp only [pure_bind]
      refine dir1Rel_mono_phase id (fun hp1 => ?_)
        (hacc vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom_sync)
      have hfsL' := hfsL hp1
      dsimp (config := { zetaDelta := true }) only at hfsL' ⊢
      rw [bind_assoc, hfsL']
      simp only [pure_bind]

private theorem fsRecv_inl_vRecv_tail_cps {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (ep : ℕ) (hne_t : ep ≠ t)
    (hsend_f : P.sendsIn ep = false) (hep_le : ep ≤ (esLoc.g.st P).tcur + 1)
    (Topt : Option Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (rs0 : RatchetReceiverState (BitVec 256) (BitVec 256))
    (vpBaseL : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) × Option ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
    (vpBaseM : VP (DDHSt Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (hvpBase_ep : vpBaseL.tcur = max (esLoc.g.st P).tcur ep ∧ vpBaseL.id = P)
    (hvpBase_fields : vpBaseL.id = vpBaseM.id ∧ vpBaseL.tcur = vpBaseM.tcur ∧
      vpBaseL.γ = vpBaseM.γ ∧ vpBaseL.root = vpBaseM.root ∧
      vpBaseL.curCkaMsg = vpBaseM.curCkaMsg ∧
      vpBaseL.vS = (esLoc.g.st P).vS ∧ vpBaseM.vS = (esM.g.st P).vS)
    (fLoc : _ → ProbComp Bool)
    (fM fL : (_ × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) → ProbComp Bool)
    (hrej : ∀ hLoc' hM' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
        { esLoc with h := hLoc' } { esM with h := hM' } { esM with h := hM' } tblM' tblL' →
      Dir1Rel phase1
        (fLoc (some none, { esLoc with h := hLoc' }))
        (fM ((some none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblM')))
        (fL ((some none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblL'))))
    (hacc : ∀ vpL' vpM' i' m' hLoc' hM' tblM' tblL',
      (∀ pos : _root_.CryptoGames.SM.Pos, pos.epoch = ep →
        SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
          { g := esLoc.g.accept P vpL' pos, h := hLoc', abort := false }
          { g := esM.g.accept P vpM' pos, h := hM', abort := false }
          { g := esM.g.accept P vpM' pos, h := hM', abort := false }
          tblM' tblL') →
      (ep ≠ t →
        SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
          { esLoc with h := hLoc' } { esM with h := hM' } { esM with h := hM' } tblM' tblL') →
      Dir1Rel phase1
        (fLoc (some (some (vpL', ep, i', m')), { esLoc with h := hLoc' }))
        (fM ((some (some (vpM', ep, i', m')), { esM with h := hM' }), (fun (_ : ℕ) => false, tblM')))
        (fL ((some (some (vpM', ep, i', m')), { esM with h := hM' }), (fun (_ : ℕ) => false, tblL')))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    Dir1Rel phase1
      ((simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).fsRecv
          esLoc.g P ep (rs0, none) (ep, Topt) e rec?).run esLoc.h) >>= fun q0 =>
        match q0.1 with
        | none => pure (none, { esLoc with h := q0.2 })
        | some none => pure (some none, { esLoc with h := q0.2 })
        | some (some (v', i', m')) =>
          pure (some (some ({ vpBaseL with vR := Function.update (esLoc.g.st P).vR ep (some v') },
            ep, i', m')), { esLoc with h := q0.2 })) >>= fLoc)
      (((simulateQ (pubFsMultiImpl (impl false)) (((hooksFSMulti cka prng fs Δcka mo false false).fsRecv
          esM.g P ep (.inl rs0) (ep, Topt) e rec?).run esM.h)).run (fun _ => false, tblM) >>= fun q0 =>
        match q0.1.1 with
        | none => pure ((none, { esM with h := q0.1.2 }), q0.2)
        | some none => pure ((some none, { esM with h := q0.1.2 }), q0.2)
        | some (some (v', i', m')) =>
          pure ((some (some ({ vpBaseM with vR := Function.update (esM.g.st P).vR ep (some v') },
            ep, i', m')), { esM with h := q0.1.2 }), q0.2)) >>= fM)
      (((simulateQ (pubFsMultiImpl (impl true)) (((hooksFSMulti cka prng fs Δcka mo false true).fsRecv
          esM.g P ep (.inl rs0) (ep, Topt) e rec?).run esM.h)).run (fun _ => false, tblL) >>= fun q0 =>
        match q0.1.1 with
        | none => pure ((none, { esM with h := q0.1.2 }), q0.2)
        | some none => pure ((some none, { esM with h := q0.1.2 }), q0.2)
        | some (some (v', i', m')) =>
          pure ((some (some ({ vpBaseM with vR := Function.update (esM.g.st P).vR ep (some v') },
            ep, i', m')), { esM with h := q0.1.2 }), q0.2)) >>= fL) := by
  intro cka prng fs mo impl
  rcases hsync.hstates with ⟨ssLoc, rsLoc, hact, hss_init, hrs_init, hvp⟩
  cases hrcv : fs.receive rs0 (ep, Topt) e with
  | none =>
    have hloc_run : simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).fsRecv
        esLoc.g P ep (rs0, none) (ep, Topt) e rec?).run esLoc.h) =
        pure (some none, esLoc.h) := by
      dsimp only [hooksLocalPrefix]
      simp [hrcv, StateT.run_pure, simulateQ_pure]
    have hfsm_run : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
        (simulateQ (pubFsMultiImpl (impl la)) (((hooksFSMulti cka prng fs Δcka mo false la).fsRecv
          esM.g P ep (.inl rs0) (ep, Topt) e rec?).run esM.h)).run (fun _ => false, tbl) =
        pure ((some none, esM.h), (fun _ => false, tbl)) := by
      intro la tbl
      dsimp only [hooksFSMulti]
      simp [hrcv, StateT.run_pure, simulateQ_pure]
    rw [bind_assoc, hloc_run, bind_assoc, hfsm_run false tblM, bind_assoc, hfsm_run true tblL]
    simp only [pure_bind]
    exact hrej esLoc.h esM.h tblM tblL
      (syncDir1_lastIdx_rem C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc.h.lastIdx
        esLoc esM esL tblM tblL hsync)
  | some trio =>
    rcases trio with ⟨rs', i', m'⟩
    let hLoc' := { esLoc.h with lastIdx := (none : Option ℕ) }
    let vpL' := { vpBaseL with vR := Function.update (esLoc.g.st P).vR ep (some (rs', none)) }
    let vpM' := { vpBaseM with vR := Function.update (esM.g.st P).vR ep (some (.inl rs')) }
    have hloc_run : simulateQ lImpl (((hooksLocalPrefix cka prng fs mo q ks).fsRecv
        esLoc.g P ep (rs0, none) (ep, Topt) e rec?).run esLoc.h) =
        pure (some (some ((rs', none), i', m')), hLoc') := by
      dsimp only [hooksLocalPrefix]
      simp [hrcv, hLoc', StateT.run_modify, simulateQ_pure]
    have hfsm_run : ∀ (la : Bool) (tbl : ℕ → SessHSt Pt ℓ),
        (simulateQ (pubFsMultiImpl (impl la)) (((hooksFSMulti cka prng fs Δcka mo false la).fsRecv
          esM.g P ep (.inl rs0) (ep, Topt) e rec?).run esM.h)).run (fun _ => false, tbl) =
        pure ((some (some (.inl rs', i', m')), esM.h), (fun _ => false, tbl)) := by
      intro la tbl
      dsimp only [hooksFSMulti]
      simp [hrcv, StateT.run_pure, simulateQ_pure]
    have htcur_mono : ∀ Q, (esLoc.g.st Q).tcur ≤ (Function.update esLoc.g.st P vpL' Q).tcur := by
      intro Q
      by_cases hQP : Q = P
      · subst hQP
        simp only [Function.update_self]
        have h1 : vpL'.tcur = max (esLoc.g.st Q).tcur ep := hvpBase_ep.1
        rw [h1]; exact Nat.le_max_left _ _
      · simp [Function.update_of_ne hQP]
    have hcom_sync : ∀ pos : _root_.CryptoGames.SM.Pos, pos.epoch = ep →
        SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
          { g := esLoc.g.accept P vpL' pos, h := hLoc', abort := false }
          { g := esM.g.accept P vpM' pos, h := esM.h, abort := false }
          { g := esM.g.accept P vpM' pos, h := esM.h, abort := false }
          tblM tblL := by
      intro pos hpos_ep
      exact syncDir1_accept C ℓ encT idOf q Δcka l t ks bs phase1 rem
        esLoc esM esL tblM tblL hsync P ep pos hpos_ep hsend_f hep_le
        ssLoc rsLoc hvp vpL' vpM' (rs', none) (.inl rs')
        hLoc' esM.h tblM tblL ssLoc rsLoc
        hvpBase_ep hsync.hlf hsync.hsessM hsync.hsess_nodup
        (by dsimp only [hLoc']; have := hsync.hsess_rem; omega)
        le_rfl
        (fun heq hlt => hsync.hsess_tH heq (Nat.lt_of_le_of_lt (htcur_mono _) hlt))
        hsync.htbl_loc
        (fun hne Ik => by rw [hsync.hsessM]; exact hsync.htbl_M hne Ik)
        hsync.hcache
        (fun hlt => hsync.hcache_tcur (Nat.lt_of_le_of_lt (htcur_mono _) hlt))
        hsync.hbook_out hsync.htbl_out hact
        (fun hlt => hss_init (Nat.lt_of_le_of_lt (htcur_mono _) hlt))
        (fun hlt => hrs_init (Nat.lt_of_le_of_lt (htcur_mono _) hlt))
        (fun _ _ => rfl) (fun _ _ _ => rfl)
        ⟨hvpBase_fields.1, hvpBase_fields.2.1, hvpBase_fields.2.2.1, hvpBase_fields.2.2.2.1,
          hvpBase_fields.2.2.2.2.1, hvpBase_fields.2.2.2.2.2.1, hvpBase_fields.2.2.2.2.2.2,
          rfl, rfl⟩
        ⟨rfl, hne_t⟩
    rw [bind_assoc, hloc_run, bind_assoc, hfsm_run false tblM, bind_assoc, hfsm_run true tblL]
    simp only [pure_bind]
    exact hacc vpL' vpM' i' m' hLoc' esM.h tblM tblL hcom_sync
      (fun _ => syncDir1_lastIdx_rem C ℓ encT idOf q Δcka l t ks bs phase1 rem none
        esLoc esM esL tblM tblL hsync)

private theorem dir1Rel_bind_congr {α α' β β' γ γ' : Type} {phase1 : Bool}
    {mA : ProbComp α} {gA gA' : α → ProbComp α'} {fLoc : α' → ProbComp Bool}
    {mB : ProbComp β} {gB gB' : β → ProbComp β'} {fM : β' → ProbComp Bool}
    {mC : ProbComp γ} {gC gC' : γ → ProbComp γ'} {fL : γ' → ProbComp Bool}
    (hA : ∀ x, gA x = gA' x) (hB : ∀ x, gB x = gB' x) (hC : ∀ x, gC x = gC' x)
    (h : Dir1Rel phase1 ((mA >>= gA') >>= fLoc) ((mB >>= gB') >>= fM) ((mC >>= gC') >>= fL)) :
    Dir1Rel phase1 ((mA >>= gA) >>= fLoc) ((mB >>= gB) >>= fM) ((mC >>= gC) >>= fL) := by
  have h1 : gA = gA' := funext hA
  have h2 : gB = gB' := funext hB
  have h3 : gC = gC' := funext hC
  subst h1; subst h2; subst h3; exact h

private theorem vRecv_dir1_cps {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka l t : ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec? : Option (Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (fLoc : _ → ProbComp Bool)
    (fM fL : (_ × ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ))) → ProbComp Bool)
    (habort_loc : ∀ hLoc', 𝒟[fLoc (none, { esLoc with h := hLoc' })] {true} = 0)
    (habort_lf : phase1 = true → ∀ hM' tblL', hM'.lfWin = true →
      𝒟[fL ((none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblL'))] {true} = 1)
    (hrej : ∀ hLoc' hM' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
        { esLoc with h := hLoc' } { esM with h := hM' } { esM with h := hM' } tblM' tblL' →
      Dir1Rel phase1
        (fLoc (some none, { esLoc with h := hLoc' }))
        (fM ((some none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblM')))
        (fL ((some none, { esM with h := hM' }), (fun (_ : ℕ) => false, tblL'))))
    (hacc : ∀ vpL' vpM' i' m' hLoc' hM' tblM' tblL',
      (∀ pos : _root_.CryptoGames.SM.Pos, pos.epoch = c.1.1 →
        SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
          { g := esLoc.g.accept P vpL' pos, h := hLoc', abort := false }
          { g := esM.g.accept P vpM' pos, h := hM', abort := false }
          { g := esM.g.accept P vpM' pos, h := hM', abort := false }
          tblM' tblL') →
      (c.1.1 ≠ t →
        SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem
          { esLoc with h := hLoc' } { esM with h := hM' } { esM with h := hM' } tblM' tblL') →
      Dir1Rel phase1
        (fLoc (some (some (vpL', c.1.1, i', m')), { esLoc with h := hLoc' }))
        (fM ((some (some (vpM', c.1.1, i', m')), { esM with h := hM' }), (fun (_ : ℕ) => false, tblM')))
        (fL ((some (some (vpM', c.1.1, i', m')), { esM with h := hM' }), (fun (_ : ℕ) => false, tblL')))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    Dir1Rel phase1
      (simulateQ lImpl ((liftH (vRecv (hooksLocalPrefix cka prng fs mo q ks)
          esLoc.g P (esLoc.g.st P) c rec?)).run esLoc) >>= fLoc)
      ((simulateQ (pubFsMultiImpl (impl false))
          ((liftH (vRecv (hooksFSMulti cka prng fs Δcka mo false false)
            esM.g P (esM.g.st P) c rec?)).run esM)).run (fun _ => false, tblM) >>= fM)
      ((simulateQ (pubFsMultiImpl (impl true))
          ((liftH (vRecv (hooksFSMulti cka prng fs Δcka mo false true)
            esM.g P (esM.g.st P) c rec?)).run esM)).run (fun _ => false, tblL) >>= fL) := by
  intro cka prng fs mo impl
  have hsync_rem : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esM tblM tblL :=
    syncDir1_lastIdx_rem C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc.h.lastIdx
      esLoc esM esL tblM tblL hsync
  rcases hsync.hstates with ⟨ssLoc, rsLoc, hact, hss_init, hrs_init, hvp⟩
  rcases hvp P with ⟨hid_eq, htcur_eq, hγ_eq, hroot_eq, hcka_eq, hvS_P, hvR_P⟩
  have hidL : (esLoc.g.st P).id = P := (hsync.hep_st P).2
  cases hgL : ((esLoc.g.st P).id.sendsIn c.1.1 || decide ((esLoc.g.st P).tcur + 1 < c.1.1)) with
  | true =>
    have hgM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = true := by
      rw [← hid_eq, ← htcur_eq]; exact hgL
    rw [vRecv_guard_true_loc_eq _ _ _ _ _ _ _ hgL,
      vRecv_guard_true_fsm_eq _ _ _ _ _ _ _ _ _ hgM,
      vRecv_guard_true_fsm_eq _ _ _ _ _ _ _ _ _ hgM]
    simp only [pure_bind]
    exact hrej esLoc.h esM.h tblM tblL hsync_rem
  | false =>
    have hgM : ((esM.g.st P).id.sendsIn c.1.1 || decide ((esM.g.st P).tcur + 1 < c.1.1)) = false := by
      rw [← hid_eq, ← htcur_eq]; exact hgL
    have hsend_f : P.sendsIn c.1.1 = false := by
      rw [← hidL]; exact (Bool.or_eq_false_iff.mp hgL).1
    have hep_le : c.1.1 ≤ (esLoc.g.st P).tcur + 1 :=
      Nat.le_of_not_lt (decide_eq_false_iff_not.mp (Bool.or_eq_false_iff.mp hgL).2)
    by_cases hsuccL : c.1.1 = (esLoc.g.st P).tcur + 1
    · have hsuccM : c.1.1 = (esM.g.st P).tcur + 1 := by rw [← htcur_eq]; exact hsuccL
      rcases c with ⟨⟨ep, _ | Tn⟩, e⟩
      · dsimp only at hgL hgM hsend_f hep_le hsuccL hsuccM hacc ⊢
        rw [vRecv_succ_none_loc_eq _ _ _ _ _ _ _ _ hgL hsuccL,
          vRecv_succ_none_fsm_eq _ _ _ _ _ _ _ _ _ _ hgM hsuccM,
          vRecv_succ_none_fsm_eq _ _ _ _ _ _ _ _ _ _ hgM hsuccM]
        simp only [pure_bind]
        exact hrej esLoc.h esM.h tblM tblL hsync_rem
      · dsimp only at hgL hgM hsend_f hep_le hsuccL hsuccM hacc ⊢
        rw [vRecv_succ_some_loc_eq _ _ _ _ _ _ _ _ _ hgL hsuccL,
          vRecv_succ_some_fsm_eq _ _ _ _ _ _ _ _ _ _ _ hgM hsuccM,
          vRecv_succ_some_fsm_eq _ _ _ _ _ _ _ _ _ _ _ hgM hsuccM]
        have hc_rel := hsync.hcache ep
        by_cases hhit : ∃ σc kL idxL?, esLoc.h.cache ep = some (Tn, σc, kL, idxL?)
        · rcases hhit with ⟨σc, kL, idxL?, hcL⟩
          rcases hcM : esM.h.cache ep with _ | ⟨TcM, σM, kM, idxM?⟩
          · rw [hcL, hcM] at hc_rel; exact False.elim hc_rel
          · rw [hcL, hcM] at hc_rel
            rcases hc_rel with ⟨hTcM, hσM, hidxM, hrest⟩
            subst TcM; subst σM; subst idxM?
            rw [bind_assoc, startRecv_hit_loc_eq cka prng fs mo q ks esLoc.g P ep
                (esLoc.g.st P).γ (esLoc.g.st P).root Tn Tn σc kL idxL? esLoc.h hcL rfl,
              bind_assoc, startRecv_hit_fsm_eq (impl false) cka prng fs Δcka mo false esM.g P ep
                (esM.g.st P).γ (esM.g.st P).root Tn Tn σc kM idxL? esM.h (fun _ => false, tblM) hcM rfl,
              bind_assoc, startRecv_hit_fsm_eq (impl true) cka prng fs Δcka mo true esM.g P ep
                (esM.g.st P).γ (esM.g.st P).root Tn Tn σc kM idxL? esM.h (fun _ => false, tblL) hcM rfl]
            simp only [pure_bind, ← hγ_eq]
            rcases idxL? with _ | sIdx
            · rcases hrest with ⟨hk_eq, hne_t⟩
              subst kM
              dsimp only
              refine dir1Rel_bind_congr
                (fun ⟨q1, h2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                (fsRecv_inl_vRecv_tail_cps C ℓ Dh encPt encT idOf q Δcka l t ks bs
                  phase1 rem esLoc esM esL tblM tblL hsync P ep hne_t hsend_f hep_le
                  (some Tn) e rec? (fs.initReceiver kL)
                  { esLoc.g.st P with tcur := ep, γ := (cka.receive (esLoc.g.st P).γ Tn).1, root := σc }
                  { esM.g.st P with tcur := ep, γ := (cka.receive (esLoc.g.st P).γ Tn).1, root := σc }
                  ⟨by dsimp only; omega, hidL⟩
                  ⟨hid_eq, rfl, rfl, rfl, hcka_eq, rfl, rfl⟩
                  fLoc fM fL hrej hacc)
            · rcases hrest with ⟨hep_t, hs_lt, hk_eq⟩
              subst hep_t
              dsimp only
              have hP_recv : P = Party.receiverOf ep := party_eq_receiverOf_of_not_sendsIn hsend_f
              have hlt_recv : (esLoc.g.st (Party.receiverOf ep)).tcur < ep := by
                rw [← hP_recv]; omega
              have hrs0 : fs.initReceiver kL = rsLoc sIdx := by
                rw [hk_eq, hrs_init hlt_recv sIdx hs_lt]
              refine dir1Rel_bind_congr
                (fun ⟨q1, h2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                (fsRecv_inr_vRecv_tail_cps C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka l ep ks bs
                  phase1 rem esLoc esM esL tblM tblL hsync ssLoc rsLoc hvp
                  P hsend_f hep_le (some Tn) e rec?
                  { esLoc.g.st P with tcur := ep, γ := (cka.receive (esLoc.g.st P).γ Tn).1, root := σc }
                  { esM.g.st P with tcur := ep, γ := (cka.receive (esLoc.g.st P).γ Tn).1, root := σc }
                  ⟨by dsimp only; omega, hidL⟩
                  ⟨hid_eq, rfl, rfl, rfl, hcka_eq, rfl, rfl⟩
                  sIdx (fs.initReceiver kL) esLoc.h esM.h ssLoc rsLoc hs_lt hrs0
                  hsync.hlf hsync.hsessM hsync.hsess_nodup
                  (by have := hsync.hsess_rem; omega) le_rfl hsync.hsess_tH
                  hsync.htbl_loc hsync.htbl_M hsync.hcache hsync.hcache_tcur
                  hsync.hbook_out hsync.htbl_out hact hss_init hrs_init
                  (fun _ _ => rfl) (fun _ _ => rfl)
                  fLoc fM fL habort_lf hrej
                  (fun vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom =>
                    hacc vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom (fun hne => False.elim (hne rfl))))
        · have hmissL : ∀ σc k idx?, esLoc.h.cache ep ≠ some (Tn, σc, k, idx?) :=
            fun σc k idx? hc => hhit ⟨σc, k, idx?, hc⟩
          have hmissM : ∀ σc k idx?, esM.h.cache ep ≠ some (Tn, σc, k, idx?) := by
            intro σc k idx? hcM
            rcases hcL : esLoc.h.cache ep with _ | ⟨TcL, σL, kL, idxL?⟩
            · rw [hcL, hcM] at hc_rel; exact hc_rel
            · rw [hcL, hcM] at hc_rel; exact hhit ⟨σL, kL, idxL?, hc_rel.1 ▸ hcL⟩
          by_cases hep_t : ep = t
          · subst hep_t
            by_cases htH : mo.tStar = mo.tH
            · rw [bind_assoc, startRecv_miss_tH_loc_eq cka prng fs l ep q ks esLoc.g P
                  (esLoc.g.st P).γ (esLoc.g.st P).root Tn esLoc.h hmissL htH]
              simp only [pure_bind]
              exact dir1Rel_of_lhs_zero (habort_loc esLoc.h)
            · have hlen_lt : esLoc.h.sessions.length < q := by have := hsync.hsess_rem; omega
              have htblM_htH : ∀ Ik', (esM.h.table.lookup Ik').isSome = decide (Ik' ∈ esM.h.sessions) := by
                simpa only [hsync.hsessM] using hsync.htbl_M htH
              rw [bind_assoc, startRecv_miss_ne_tH_loc_eq cka prng fs l ep q ks esLoc.g P
                  (esLoc.g.st P).γ (esLoc.g.st P).root Tn esLoc.h hmissL htH
                  (hsync.htbl_loc htH) hlen_lt,
                bind_assoc, startRecv_miss_ne_tH_fsm_eq (impl false) cka prng fs Δcka l ep false
                  esM.g P (esM.g.st P).γ (esM.g.st P).root Tn esM.h (fun _ => false, tblM)
                  hmissM htH htblM_htH,
                bind_assoc, startRecv_miss_ne_tH_fsm_eq (impl true) cka prng fs Δcka l ep true
                  esM.g P (esM.g.st P).γ (esM.g.st P).root Tn esM.h (fun _ => false, tblL)
                  hmissM htH htblM_htH]
              simp only [← hγ_eq, ← hroot_eq, hsync.hsessM]
              let kk := cka.receive (esLoc.g.st P).γ Tn
              have hP_recv : P = Party.receiverOf ep := party_eq_receiverOf_of_not_sendsIn hsend_f
              have hlt_recv : (esLoc.g.st (Party.receiverOf ep)).tcur < ep := by
                rw [← hP_recv]; omega
              by_cases hmem : kk.2 ∈ esLoc.h.sessions
              · simp only [kk, hmem, ↓reduceIte, pure_bind]
                let sIdx := esLoc.h.sessions.idxOf kk.2
                have hs_lt : sIdx < esLoc.h.sessions.length := List.idxOf_lt_length_of_mem hmem
                have hrs0 : fs.initReceiver (ks sIdx) = rsLoc sIdx :=
                  (hrs_init hlt_recv sIdx hs_lt).symm
                refine dir1Rel_bind_congr
                  (fun ⟨q1, h2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                  (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                  (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                  (fsRecv_inr_vRecv_tail_cps C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka l ep ks bs
                    phase1 rem esLoc esM esL tblM tblL hsync ssLoc rsLoc hvp
                    P hsend_f hep_le (some Tn) e rec?
                    { esLoc.g.st P with tcur := ep, γ := kk.1, root := (prng.up (esLoc.g.st P).root kk.2).1 }
                    { esM.g.st P with tcur := ep, γ := kk.1, root := (prng.up (esLoc.g.st P).root kk.2).1 }
                    ⟨by dsimp only; omega, hidL⟩
                    ⟨hid_eq, rfl, rfl, rfl, hcka_eq, rfl, rfl⟩
                    sIdx (fs.initReceiver (ks sIdx)) esLoc.h esM.h ssLoc rsLoc hs_lt hrs0
                    hsync.hlf hsync.hsessM hsync.hsess_nodup
                    (by have := hsync.hsess_rem; omega) le_rfl hsync.hsess_tH
                    hsync.htbl_loc hsync.htbl_M hsync.hcache hsync.hcache_tcur
                    hsync.hbook_out hsync.htbl_out hact hss_init hrs_init
                    (fun _ _ => rfl) (fun _ _ => rfl)
                    fLoc fM fL habort_lf hrej
                    (fun vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom =>
                      hacc vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom (fun hne => False.elim (hne rfl))))
              · simp only [kk, hmem, ↓reduceIte, bind_assoc]
                refine dir1Rel_bind ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) _ _ _ (fun k_draw _ => ?_)
                simp only [pure_bind]
                let sIdx := esLoc.h.sessions.length
                let hLoc1 : LState Pt (BitVec 256) (BitVec 256) Pt :=
                  { esLoc.h with table := (kk.2, ks sIdx) :: esLoc.h.table,
                                 sessions := esLoc.h.sessions ++ [kk.2] }
                let hM1 : FSMultiState Pt (BitVec 256) (BitVec 256) Pt
                    (ℕ × LibsignalCiphertextWithSalt32) :=
                  { esM.h with table := (kk.2, k_draw) :: esM.h.table,
                               sessions := esLoc.h.sessions ++ [kk.2] }
                let ssLoc1 := Function.update ssLoc sIdx (fs.initSender (ks sIdx))
                let rsLoc1 := Function.update rsLoc sIdx (fs.initReceiver (ks sIdx))
                have hnodup1 : hLoc1.sessions.Nodup :=
                  List.nodup_append.mpr ⟨hsync.hsess_nodup, List.nodup_singleton _,
                    fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact hmem hx⟩
                have hbk0 : (hM1.book sIdx).getD {} = {} := by
                  have hb := hsync.hbook_out sIdx le_rfl
                  simp [hM1, hb]
                have htbl0 := hsync.htbl_out sIdx le_rfl
                have hinv_new : ActiveSessInv C ℓ encT idOf phase1 (ks sIdx)
                    (fs.initSender (ks sIdx)) (fs.initReceiver (ks sIdx))
                    ((hM1.book sIdx).getD {}) (tblM sIdx) (tblL sIdx) := by
                  rw [hbk0, htbl0.1]
                  cases hp1 : phase1
                  · exact activeSessInv_to_phase2 C ℓ encT idOf
                      (activeSessInv_init C ℓ encT idOf true (ks sIdx) (bs sIdx))
                  · rw [htbl0.2 hp1]
                    exact activeSessInv_init C ℓ encT idOf true (ks sIdx) (bs sIdx)
                refine dir1Rel_bind_congr
                  (fun ⟨q1, h2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                  (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                  (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
                  (fsRecv_inr_vRecv_tail_cps C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka l ep ks bs
                    phase1 rem esLoc esM esL tblM tblL hsync ssLoc rsLoc hvp
                    P hsend_f hep_le (some Tn) e rec?
                    { esLoc.g.st P with tcur := ep, γ := kk.1, root := (prng.up (esLoc.g.st P).root kk.2).1 }
                    { esM.g.st P with tcur := ep, γ := kk.1, root := (prng.up (esLoc.g.st P).root kk.2).1 }
                    ⟨by dsimp only; omega, hidL⟩
                    ⟨hid_eq, rfl, rfl, rfl, hcka_eq, rfl, rfl⟩
                    sIdx (fs.initReceiver (ks sIdx)) hLoc1 hM1 ssLoc1 rsLoc1
                    (by simp [hLoc1, sIdx])
                    (by simp [rsLoc1])
                    hsync.hlf rfl hnodup1
                    (by simp [hLoc1]; have := hsync.hsess_rem; omega)
                    (by simp [hLoc1])
                    (fun heq => False.elim (htH heq))
                    (fun _ Ik => by
                      dsimp only [hLoc1]
                      by_cases hIk : Ik = kk.2
                      · subst hIk; simp [list_idxOf_append_new hmem, sIdx]
                      · have hne_beq : (Ik == kk.2) = false := beq_eq_false_iff_ne.mpr hIk
                        simp only [List.lookup_cons, hne_beq, hsync.htbl_loc htH Ik]
                        by_cases hmIk : Ik ∈ esLoc.h.sessions
                        · simp [hmIk, list_idxOf_append_mem hmIk]
                        · simp [hmIk, hIk])
                    (fun _ Ik => by
                      dsimp only [hM1, hLoc1]
                      by_cases hIk : Ik = kk.2
                      · subst hIk; simp
                      · have hne_beq : (Ik == kk.2) = false := beq_eq_false_iff_ne.mpr hIk
                        simp only [List.lookup_cons, hne_beq, hsync.htbl_M htH Ik]
                        by_cases hmIk : Ik ∈ esLoc.h.sessions <;> simp [hmIk, hIk])
                    (fun ep' => by
                      dsimp only [hLoc1, hM1]
                      have hc := hsync.hcache ep'
                      cases hcL' : esLoc.h.cache ep' with
                      | none =>
                        cases hcM' : esM.h.cache ep' with
                        | none => trivial
                        | some _ => rw [hcL', hcM'] at hc; exact False.elim hc
                      | some qL =>
                        rcases qL with ⟨TcL, σL, kL, _ | idxL⟩
                        · cases hcM' : esM.h.cache ep' with
                          | none => rw [hcL', hcM'] at hc; exact False.elim hc
                          | some qM => rcases qM with ⟨TcM, σM, kM, idxM?⟩; rw [hcL', hcM'] at hc; exact hc
                        · cases hcM' : esM.h.cache ep' with
                          | none => rw [hcL', hcM'] at hc; exact False.elim hc
                          | some qM =>
                            rcases qM with ⟨TcM, σM, kM, idxM?⟩
                            rw [hcL', hcM'] at hc; dsimp only at hc
                            exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
                              by simp; omega, hc.2.2.2.2.2⟩)
                    hsync.hcache_tcur
                    (fun j hj => hsync.hbook_out j (by simp [hLoc1] at hj; omega))
                    (fun j hj => hsync.htbl_out j (by simp [hLoc1] at hj; omega))
                    (fun j hj => by
                      by_cases hjeq : j = sIdx
                      · subst hjeq; simpa [ssLoc1, rsLoc1] using hinv_new
                      · have hj_lt : j < esLoc.h.sessions.length := by simp [hLoc1] at hj; omega
                        simpa [ssLoc1, rsLoc1, Function.update_of_ne hjeq, hM1] using hact j hj_lt)
                    (fun hlt j hj => by
                      by_cases hjeq : j = sIdx
                      · subst hjeq; exact Function.update_self sIdx _ ssLoc
                      · have hj_lt : j < esLoc.h.sessions.length := by simp [hLoc1] at hj; omega
                        simpa [ssLoc1, Function.update_of_ne hjeq] using hss_init hlt j hj_lt)
                    (fun hlt j hj => by
                      by_cases hjeq : j = sIdx
                      · subst hjeq; exact Function.update_self sIdx _ rsLoc
                      · have hj_lt : j < esLoc.h.sessions.length := by simp [hLoc1] at hj; omega
                        simpa [rsLoc1, Function.update_of_ne hjeq] using hrs_init hlt j hj_lt)
                    (fun j hj => Function.update_of_ne (by dsimp only [sIdx]; omega) _ _)
                    (fun j hj => Function.update_of_ne (by dsimp only [sIdx]; omega) _ _)
                    fLoc fM fL habort_lf hrej
                    (fun vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom =>
                      hacc vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom (fun hne => False.elim (hne rfl))))
          · rw [bind_assoc, startRecv_miss_ne_loc_eq cka prng fs l t q ks esLoc.g P ep
                (esLoc.g.st P).γ (esLoc.g.st P).root Tn esLoc.h hmissL hep_t,
              bind_assoc, startRecv_miss_ne_fsm_eq (impl false) cka prng fs Δcka l t false
                esM.g P ep (esM.g.st P).γ (esM.g.st P).root Tn esM.h (fun _ => false, tblM)
                hmissM hep_t,
              bind_assoc, startRecv_miss_ne_fsm_eq (impl true) cka prng fs Δcka l t true
                esM.g P ep (esM.g.st P).γ (esM.g.st P).root Tn esM.h (fun _ => false, tblL)
                hmissM hep_t]
            simp only [pure_bind]
            exact hrej esLoc.h esM.h tblM tblL hsync_rem
    · have hnsuccM : c.1.1 ≠ (esM.g.st P).tcur + 1 := by rw [← htcur_eq]; exact hsuccL
      have hep_le_tcur : c.1.1 ≤ (esLoc.g.st P).tcur := by omega
      rw [vRecv_le_loc_eq _ _ _ _ _ _ _ hgL hsuccL,
        vRecv_le_fsm_eq _ _ _ _ _ _ _ _ _ hgM hnsuccM,
        vRecv_le_fsm_eq _ _ _ _ _ _ _ _ _ hgM hnsuccM]
      have hvR_ep := hvR_P c.1.1
      rcases hvRL : (esLoc.g.st P).vR c.1.1 with _ | ⟨rs, _ | sIdx⟩
      · rcases hvRM : (esM.g.st P).vR c.1.1 with _ | _
        · simp only [pure_bind]
          exact hrej esLoc.h esM.h tblM tblL hsync_rem
        · rw [hvRL, hvRM] at hvR_ep; exact False.elim hvR_ep
      · rcases hvRM : (esM.g.st P).vR c.1.1 with _ | ⟨rsM | sIdxM⟩
        · rw [hvRL, hvRM] at hvR_ep; exact False.elim hvR_ep
        · rw [hvRL, hvRM] at hvR_ep
          rcases hvR_ep with ⟨hrs_eq, hne_t⟩
          subst rsM
          rcases c with ⟨⟨ep, Topt⟩, e⟩
          dsimp only at hne_t hsend_f hep_le hep_le_tcur hacc ⊢
          refine dir1Rel_bind_congr
            (fun ⟨q1, h2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
            (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
            (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
            (fsRecv_inl_vRecv_tail_cps C ℓ Dh encPt encT idOf q Δcka l t ks bs
              phase1 rem esLoc esM esL tblM tblL hsync P ep hne_t hsend_f hep_le
              Topt e rec? rs (esLoc.g.st P) (esM.g.st P)
              ⟨(Nat.max_eq_left hep_le_tcur).symm, hidL⟩
              ⟨hid_eq, htcur_eq, hγ_eq, hroot_eq, hcka_eq, rfl, rfl⟩
              fLoc fM fL hrej hacc)
        · rw [hvRL, hvRM] at hvR_ep; exact False.elim hvR_ep
      · rcases hvRM : (esM.g.st P).vR c.1.1 with _ | ⟨rsM | sIdxM⟩
        · rw [hvRL, hvRM] at hvR_ep; exact False.elim hvR_ep
        · rw [hvRL, hvRM] at hvR_ep; exact False.elim hvR_ep
        · rw [hvRL, hvRM] at hvR_ep
          rcases hvR_ep with ⟨hep_t, hs_eq, hs_lt, hrs_eq, _, ht_le_tcur⟩
          subst sIdxM
          rcases c with ⟨⟨ep, Topt⟩, e⟩
          dsimp only at hep_t hsend_f hep_le ht_le_tcur hacc ⊢
          subst hep_t
          refine dir1Rel_bind_congr
            (fun ⟨q1, h2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
            (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
            (fun ⟨⟨q1, h2⟩, st2⟩ => by rcases q1 with _ | _ | ⟨v', i', m'⟩ <;> rfl)
            (fsRecv_inr_vRecv_tail_cps C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka l ep ks bs
              phase1 rem esLoc esM esL tblM tblL hsync ssLoc rsLoc hvp
              P hsend_f hep_le Topt e rec? (esLoc.g.st P) (esM.g.st P)
              ⟨(Nat.max_eq_left ht_le_tcur).symm, hidL⟩
              ⟨hid_eq, htcur_eq, hγ_eq, hroot_eq, hcka_eq, rfl, rfl⟩
              sIdx rs esLoc.h esM.h ssLoc rsLoc hs_lt hrs_eq
              hsync.hlf hsync.hsessM hsync.hsess_nodup
              (by have := hsync.hsess_rem; omega) le_rfl hsync.hsess_tH
              hsync.htbl_loc hsync.htbl_M hsync.hcache hsync.hcache_tcur
              hsync.hbook_out hsync.htbl_out hact hss_init hrs_init
              (fun _ _ => rfl) (fun _ _ => rfl)
              fLoc fM fL habort_lf hrej
              (fun vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom =>
                hacc vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom (fun hne => False.elim (hne rfl))))

private theorem step_deliverE_dir1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (kLoc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → _ → ProbComp Bool)
    (kM kL : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → _ →
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hdead : ∀ res esLoc', LocDead l t esLoc' → 𝒟[kLoc res esLoc'] {true} = 0)
    (hlf_term : phase1 = true → ∀ esL' tblL', esL'.abort = true → esL'.h.lfWin = true →
      𝒟[kL none esL' (fun _ => false, tblL')] {true} = 1)
    (hk : ∀ res phase1' esLoc' esM' esL' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem esLoc' esM' esL' tblM' tblL' →
      Dir1Rel phase1' (kLoc res esLoc') (kM res esM' (fun _ => false, tblM'))
        (kL res esL' (fun _ => false, tblL'))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain :=
      .inr (.inl (.inl (.inl (.inr (P, c)))))
    Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) := by
  intro cka prng fs mo impl qry
  suffices Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) by
    exact dir1Rel_mono_phase id (fun hp1 => by rw [syncDir1_esL_eq_esM hsync hp1]) this
  have hsync_rem : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esM tblM tblL :=
    syncDir1_lastIdx_rem C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc.h.lastIdx
      esLoc esM esL tblM tblL hsync
  have htr_eq : esLoc.g.inTransit P.other c = esM.g.inTransit P.other c :=
    eraseSt_inTransit hsync.heraseM P.other c
  dsimp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
  unfold deliverE
  cases htrM : esM.g.inTransit P.other c with
  | none =>
    have htrL : esLoc.g.inTransit P.other c = none := htr_eq.trans htrM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habortL, hsync.hwinL,
      hsync.habortM, hsync.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htrL, htrM,
      StateT.run_pure, simulateQ_pure]
    exact hk none phase1 esLoc esM esM tblM tblL hsync_rem
  | some r =>
    have htrL : esLoc.g.inTransit P.other c = some r := htr_eq.trans htrM
    rcases inTransit_props htrL with ⟨hrmem, hrct⟩
    have hpos_ep : r.pos.epoch = c.1.1 := by
      rw [← hsync.hginv r hrmem, hrct]
    have hchall_eq : esLoc.g.chall = esM.g.chall := eraseSt_chall hsync.heraseM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habortL, hsync.hwinL,
      hsync.habortM, hsync.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htrL, htrM,
      simulateQ_bind, bind_assoc]
    refine vRecv_dir1_cps C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka l t ks bs phase1 rem
      esLoc esM esL tblM tblL hsync P c (some r) _ _ _
      (fun hLoc' => ?_) (fun hp1 hM' tblL' hlf' => ?_)
      (fun hLoc' hM' tblM' tblL' hsync_rej => ?_)
      (fun vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom_sync _ => ?_)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure]
      exact hdead none { esLoc with h := hLoc', abort := true } (Or.inl rfl)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure]
      exact hlf_term hp1 { esM with h := hM', abort := true } tblL' rfl hlf'
    · have hdw : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).deliverWin = false := rfl
      simp only [hdw, Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
        simulateQ_pure, pure_bind]
      exact hk (some .rejected) phase1 _ _ _ tblM' tblL' hsync_rej
    · have hdw : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).deliverWin = false := rfl
      have hcomL := commitE_trivial_run (hooksLocalPrefix cka prng fs mo q ks)
        (fun _ _ _ new => rfl) esLoc.g P (esLoc.g.st P) vpL' r.pos { esLoc with h := hLoc' }
      have hcomM0 := commitE_trivial_run (hooksFSMulti cka prng fs Δcka mo false false)
        (fun _ _ _ new => rfl) esM.g P (esM.g.st P) vpM' r.pos { esM with h := hM' }
      have hcomM1 := commitE_trivial_run (hooksFSMulti cka prng fs Δcka mo false true)
        (fun _ _ _ new => rfl) esM.g P (esM.g.st P) vpM' r.pos { esM with h := hM' }
      simp only [StateT.run_bind, hcomL, hcomM0, hcomM1, pure_bind, hdw, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, StateT.run_modify, StateT.run_pure, simulateQ_pure,
        hchall_eq]
      have habL : EState.mk (esLoc.g.accept P vpL' r.pos) hLoc' esLoc.abort =
          EState.mk (esLoc.g.accept P vpL' r.pos) hLoc' false := by
        rw [hsync.habortL]
      have habM : EState.mk (esM.g.accept P vpM' r.pos) hM' esM.abort =
          EState.mk (esM.g.accept P vpM' r.pos) hM' false := by
        rw [hsync.habortM]
      rw [habL, habM]
      exact hk (some (.accepted c.1.1 i' (if esM.g.chall.contains r.pos then none else some m')))
        phase1 _ _ _ tblM' tblL' (hcom_sync r.pos hpos_ep)

private theorem step_injectE_dir1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ) (ht_qep : t ≤ qep + 1)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (kLoc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → _ → ProbComp Bool)
    (kM kL : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → _ →
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hdead : ∀ res esLoc', LocDead l t esLoc' → 𝒟[kLoc res esLoc'] {true} = 0)
    (hlf_term : phase1 = true → ∀ esL' tblL', esL'.abort = true → esL'.h.lfWin = true →
      𝒟[kL none esL' (fun _ => false, tblL')] {true} = 1)
    (hwin_term : ∀ res esLoc' esM' tblM' cL',
      esLoc'.g.win = true → esM'.g.win = true →
      authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esLoc' =
        authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esM' →
      Dir1Rel phase1 (kLoc res esLoc') (kM res esM' (fun _ => false, tblM')) cL')
    (hk : ∀ res phase1' esLoc' esM' esL' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem esLoc' esM' esL' tblM' tblL' →
      Dir1Rel phase1' (kLoc res esLoc') (kM res esM' (fun _ => false, tblM'))
        (kL res esL' (fun _ => false, tblL'))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain :=
      .inr (.inl (.inl (.inr (P, c))))
    Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) := by
  intro cka prng fs mo impl qry
  suffices Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) by
    exact dir1Rel_mono_phase id (fun hp1 => by rw [syncDir1_esL_eq_esM hsync hp1]) this
  have hsync_rem : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esM tblM tblL :=
    syncDir1_lastIdx_rem C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc.h.lastIdx
      esLoc esM esL tblM tblL hsync
  have hg_eq : ((esLoc.g.inTransit P.other c).isSome || !(esLoc.g.safeInj (2 + Δcka))) =
      ((esM.g.inTransit P.other c).isSome || !(esM.g.safeInj (2 + Δcka))) := by
    rw [eraseSt_inTransit hsync.heraseM P.other c, eraseSt_safeInj hsync.heraseM (2 + Δcka)]
  dsimp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
  unfold injectE
  cases hguardM : ((esM.g.inTransit P.other c).isSome || !(esM.g.safeInj (2 + Δcka))) with
  | true =>
    have hguardL : ((esLoc.g.inTransit P.other c).isSome || !(esLoc.g.safeInj (2 + Δcka))) = true :=
      hg_eq.trans hguardM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habortL, hsync.hwinL,
      hsync.habortM, hsync.hwinM, Bool.false_or, hguardL, hguardM, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact hk none phase1 esLoc esM esM tblM tblL hsync_rem
  | false =>
    have hguardL : ((esLoc.g.inTransit P.other c).isSome || !(esLoc.g.safeInj (2 + Δcka))) = false :=
      hg_eq.trans hguardM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habortL, hsync.hwinL,
      hsync.habortM, hsync.hwinM, Bool.false_or, hguardL, hguardM, Bool.false_eq_true, ↓reduceIte,
      simulateQ_bind, bind_assoc]
    refine vRecv_dir1_cps C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka l t ks bs phase1 rem
      esLoc esM esL tblM tblL hsync P c none _ _ _
      (fun hLoc' => ?_) (fun hp1 hM' tblL' hlf' => ?_)
      (fun hLoc' hM' tblM' tblL' hsync_rej => ?_)
      (fun vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom_sync hne_sync => ?_)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure]
      exact hdead none { esLoc with h := hLoc', abort := true } (Or.inl rfl)
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure]
      exact hlf_term hp1 { esM with h := hM', abort := true } tblL' rfl hlf'
    · simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact hk (some .rejected) phase1 _ _ _ tblM' tblL' hsync_rej
    · by_cases hgt : qep + 1 < c.1.1
      · have hne : c.1.1 ≠ t := by omega
        simp only [hgt, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
        exact hk (some .rejected) phase1 _ _ _ tblM' tblL' (hne_sync hne)
      · let pos : _root_.CryptoGames.SM.Pos := ⟨P.other, c.1.1, i'⟩
        have htriv_eq : esLoc.g.trivial (2 + Δcka) pos = esM.g.trivial (2 + Δcka) pos :=
          eraseSt_trivial hsync.heraseM (2 + Δcka) pos
        simp only [hgt, ↓reduceIte]
        cases htrivM : esM.g.trivial (2 + Δcka) pos with
        | true =>
          have htrivL : esLoc.g.trivial (2 + Δcka) pos = true := htriv_eq.trans htrivM
          have hcomL := commitE_trivial_run (hooksLocalPrefix cka prng fs mo q ks)
            (fun _ _ _ new => rfl) esLoc.g P (esLoc.g.st P) vpL' pos { esLoc with h := hLoc' }
          have hcomM0 := commitE_trivial_run (hooksFSMulti cka prng fs Δcka mo false false)
            (fun _ _ _ new => rfl) esM.g P (esM.g.st P) vpM' pos { esM with h := hM' }
          have hcomM1 := commitE_trivial_run (hooksFSMulti cka prng fs Δcka mo false true)
            (fun _ _ _ new => rfl) esM.g P (esM.g.st P) vpM' pos { esM with h := hM' }
          simp only [pos, htrivL, ↓reduceIte, StateT.run_bind, hcomL, hcomM0, hcomM1,
            pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
          have habL : EState.mk (esLoc.g.accept P vpL' pos) hLoc' esLoc.abort =
              EState.mk (esLoc.g.accept P vpL' pos) hLoc' false := by
            rw [hsync.habortL]
          have habM : EState.mk (esM.g.accept P vpM' pos) hM' esM.abort =
              EState.mk (esM.g.accept P vpM' pos) hM' false := by
            rw [hsync.habortM]
          rw [habL, habM]
          exact hk (some (.accepted c.1.1 i' (some m'))) phase1 _ _ _ tblM' tblL'
            (hcom_sync pos rfl)
        | false =>
          have htrivL : esLoc.g.trivial (2 + Δcka) pos = false := htriv_eq.trans htrivM
          simp only [pos, htrivL, Bool.false_eq_true, ↓reduceIte]
          by_cases hep_t : c.1.1 = t
          · have hinjF : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).injectFull c.1.1 = true := by
              simp [mo, Mode.cfg, Config.auth, hep_t]
            simp only [hinjF, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure]
            refine hwin_term (some .rejected)
              { g := { esLoc.g with win := true }, h := hLoc', abort := esLoc.abort }
              { g := { esM.g with win := true }, h := hM', abort := esM.abort }
              tblM' _ rfl rfl ?_
            have her_win : eraseSt { esLoc.g with win := true } = eraseSt { esM.g with win := true } := by
              have h := hsync.heraseM
              simp [eraseSt, eraseSt_epoch h, eraseSt_idx h, eraseSt_tL h, eraseSt_trans h,
                eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h, eraseSt_b h,
                eraseSt_leaks h, eraseSt_corrs h]
            simp [authOut, hsync.habortL, hsync.habortM, Mode.policy,
              eraseSt_authOK her_win (2 + Δcka) (some (l - 1)) t]
          · have hinjF : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).injectFull c.1.1 = false := by
              simp [mo, Mode.cfg, Config.auth, hep_t]
            simp only [hinjF, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              pure_bind]
            exact hk (some .rejected) phase1 _ _ _ tblM' tblL' (hne_sync hep_t)

private theorem step_deliverForgeE_dir1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ) (ht_qep : t ≤ qep + 1)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (phase1 : Bool) (rem : ℕ)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 (rem + 1) esLoc esM esL tblM tblL)
    (P : Party) (c₁ c₂ : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (kLoc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → _ → ProbComp Bool)
    (kM kL : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) → _ →
      ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool)
    (hdead : ∀ res esLoc', LocDead l t esLoc' → 𝒟[kLoc res esLoc'] {true} = 0)
    (hlf_term : phase1 = true → ∀ esL' tblL', esL'.abort = true → esL'.h.lfWin = true →
      𝒟[kL none esL' (fun _ => false, tblL')] {true} = 1)
    (hwin_term : ∀ res esLoc' esM' tblM' cL',
      esLoc'.g.win = true → esM'.g.win = true →
      authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esLoc' =
        authOut (2 + Δcka) (⟨true, some (l - 1), t⟩ : Mode).policy esM' →
      Dir1Rel phase1 (kLoc res esLoc') (kM res esM' (fun _ => false, tblM')) cL')
    (hk : ∀ res phase1' esLoc' esM' esL' tblM' tblL',
      SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1' rem esLoc' esM' esL' tblM' tblL' →
      Dir1Rel phase1' (kLoc res esLoc') (kM res esM' (fun _ => false, tblM'))
        (kL res esL' (fun _ => false, tblL'))) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let qry : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF
        (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain :=
      .inr (.inr (P, c₁, c₂))
    Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esL)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) := by
  intro cka prng fs mo impl qry
  suffices Dir1Rel phase1
      (simulateQ lImpl
        ((implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esLoc) >>=
        fun z => kLoc z.1 z.2)
      ((simulateQ (pubFsMultiImpl (impl false))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblM) >>= fun z => kM z.1.1 z.1.2 z.2)
      ((simulateQ (pubFsMultiImpl (impl true))
        ((implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy qry).run esM)).run
        (fun _ => false, tblL) >>= fun z => kL z.1.1 z.1.2 z.2) by
    exact dir1Rel_mono_phase id (fun hp1 => by rw [syncDir1_esL_eq_esM hsync hp1]) this
  have hsync_rem : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esM tblM tblL :=
    syncDir1_lastIdx_rem C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc.h.lastIdx
      esLoc esM esL tblM tblL hsync
  have htr1_eq : esLoc.g.inTransit P.other c₁ = esM.g.inTransit P.other c₁ :=
    eraseSt_inTransit hsync.heraseM P.other c₁
  dsimp only [qry, implEDFShiftedPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
  unfold deliverForgeE
  cases htr1M : esM.g.inTransit P.other c₁ with
  | none =>
    have htr1L : esLoc.g.inTransit P.other c₁ = none := htr1_eq.trans htr1M
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habortL, hsync.hwinL,
      hsync.habortM, hsync.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr1L, htr1M,
      StateT.run_pure, simulateQ_pure]
    exact hk none phase1 esLoc esM esM tblM tblL hsync_rem
  | some r =>
    have htr1L : esLoc.g.inTransit P.other c₁ = some r := htr1_eq.trans htr1M
    rcases inTransit_props htr1L with ⟨hrmem, hrct⟩
    have hg2_eq : ((esLoc.g.inTransit P.other c₂).isSome || esLoc.g.comp.contains r.pos || (c₁.1 != c₂.1)) =
        ((esM.g.inTransit P.other c₂).isSome || esM.g.comp.contains r.pos || (c₁.1 != c₂.1)) := by
      rw [eraseSt_inTransit hsync.heraseM P.other c₂, eraseSt_comp hsync.heraseM]
    cases hg2M : ((esM.g.inTransit P.other c₂).isSome || esM.g.comp.contains r.pos || (c₁.1 != c₂.1)) with
    | true =>
      have hg2L : ((esLoc.g.inTransit P.other c₂).isSome || esLoc.g.comp.contains r.pos || (c₁.1 != c₂.1)) = true :=
        hg2_eq.trans hg2M
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habortL, hsync.hwinL,
        hsync.habortM, hsync.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr1L, htr1M,
        hg2L, hg2M, StateT.run_pure, simulateQ_pure]
      exact hk none phase1 esLoc esM esM tblM tblL hsync_rem
    | false =>
      have hg2L : ((esLoc.g.inTransit P.other c₂).isSome || esLoc.g.comp.contains r.pos || (c₁.1 != c₂.1)) = false :=
        hg2_eq.trans hg2M
      have hc12 : c₁.1 = c₂.1 := beq_iff_eq.mp (by
        have h := (Bool.or_eq_false_iff.mp hg2M).2
        simpa [bne] using h)
      have hpos_ep : (c₂.1.1 != r.pos.epoch) = false := by
        have heq : c₂.1.1 = r.pos.epoch := by
          rw [← hc12, ← hrct, hsync.hginv r hrmem]
        simp [heq]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hsync.habortL, hsync.hwinL,
        hsync.habortM, hsync.hwinM, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htr1L, htr1M,
        hg2L, hg2M, simulateQ_bind, bind_assoc]
      refine vRecv_dir1_cps C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka l t ks bs phase1 rem
        esLoc esM esL tblM tblL hsync P c₂ none _ _ _
        (fun hLoc' => ?_) (fun hp1 hM' tblL' hlf' => ?_)
        (fun hLoc' hM' tblM' tblL' hsync_rej => ?_)
        (fun vpL' vpM' i' m' hLoc' hM' tblM' tblL' hcom_sync hne_sync => ?_)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure]
        exact hdead none { esLoc with h := hLoc', abort := true } (Or.inl rfl)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure]
        exact hlf_term hp1 { esM with h := hM', abort := true } tblL' rfl hlf'
      · simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        exact hk (some .rejected) phase1 _ _ _ tblM' tblL' hsync_rej
      · simp only [hpos_ep, Bool.or_false]
        by_cases hgt : qep + 1 < c₂.1.1
        · have hne : c₂.1.1 ≠ t := by omega
          simp only [hgt, decide_true, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          exact hk (some .rejected) phase1 _ _ _ tblM' tblL' (hne_sync hne)
        · let pos : _root_.CryptoGames.SM.Pos := ⟨P.other, c₂.1.1, i'⟩
          have htriv_eq : esLoc.g.trivial (2 + Δcka) pos = esM.g.trivial (2 + Δcka) pos :=
            eraseSt_trivial hsync.heraseM (2 + Δcka) pos
          simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases htrivM : esM.g.trivial (2 + Δcka) pos with
          | true =>
            have htrivL : esLoc.g.trivial (2 + Δcka) pos = true := htriv_eq.trans htrivM
            have hcomL := commitE_trivial_run (hooksLocalPrefix cka prng fs mo q ks)
              (fun _ _ _ new => rfl) esLoc.g P (esLoc.g.st P) vpL' pos { esLoc with h := hLoc' }
            have hcomM0 := commitE_trivial_run (hooksFSMulti cka prng fs Δcka mo false false)
              (fun _ _ _ new => rfl) esM.g P (esM.g.st P) vpM' pos { esM with h := hM' }
            have hcomM1 := commitE_trivial_run (hooksFSMulti cka prng fs Δcka mo false true)
              (fun _ _ _ new => rfl) esM.g P (esM.g.st P) vpM' pos { esM with h := hM' }
            simp only [pos, htrivL, ↓reduceIte, StateT.run_bind, hcomL, hcomM0, hcomM1,
              pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
            have habL : EState.mk (esLoc.g.accept P vpL' pos) hLoc' esLoc.abort =
                EState.mk (esLoc.g.accept P vpL' pos) hLoc' false := by
              rw [hsync.habortL]
            have habM : EState.mk (esM.g.accept P vpM' pos) hM' esM.abort =
                EState.mk (esM.g.accept P vpM' pos) hM' false := by
              rw [hsync.habortM]
            rw [habL, habM]
            exact hk (some (.accepted c₂.1.1 i' (some m'))) phase1 _ _ _ tblM' tblL'
              (hcom_sync pos rfl)
          | false =>
            have htrivL : esLoc.g.trivial (2 + Δcka) pos = false := htriv_eq.trans htrivM
            simp only [pos, htrivL, Bool.false_eq_true, ↓reduceIte]
            by_cases hep_t : c₂.1.1 = t
            · have hinjF : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).injectFull c₂.1.1 = true := by
                simp [mo, Mode.cfg, Config.auth, hep_t]
              simp only [hinjF, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, simulateQ_pure]
              refine hwin_term (some .rejected)
                { g := { esLoc.g with win := true }, h := hLoc', abort := esLoc.abort }
                { g := { esM.g with win := true }, h := hM', abort := esM.abort }
                tblM' _ rfl rfl ?_
              have her_win : eraseSt { esLoc.g with win := true } = eraseSt { esM.g with win := true } := by
                have h := hsync.heraseM
                simp [eraseSt, eraseSt_epoch h, eraseSt_idx h, eraseSt_tL h, eraseSt_trans h,
                  eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h, eraseSt_b h,
                  eraseSt_leaks h, eraseSt_corrs h]
              simp [authOut, hsync.habortL, hsync.habortM, Mode.policy,
                eraseSt_authOK her_win (2 + Δcka) (some (l - 1)) t]
            · have hinjF : (mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).injectFull c₂.1.1 = false := by
                simp [mo, Mode.cfg, Config.auth, hep_t]
              simp only [hinjF, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
                pure_bind]
              exact hk (some .rejected) phase1 _ _ _ tblM' tblL' (hne_sync hep_t)

private theorem fst_map_simulateQ_pubFsMulti_bind {Pt σ α : Type} {ℓ : ℕ}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT σ ProbComp))
    (m : _root_.CryptoGames.SM.Engine.TComp
      (FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) α)
    (f : α → Bool) (st : (ℕ → Bool) × (ℕ → σ)) :
    Prod.fst <$> (simulateQ (pubFsMultiImpl impl) (m >>= fun z => pure (f z))).run st =
      ((simulateQ (pubFsMultiImpl impl) m).run st >>= fun p => pure (f p.1)) := by
  simp [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind]

private theorem simulateQ_dir1Rel {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (_hinj : Function.Injective encT) (_hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey)
    (q Δcka qep l t : ℕ) (hq_pos : 0 < q) (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (ht_qep : t ≤ qep + 1)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (oa : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (rem : ℕ) (hq : MakesAtMostQueriesDF oa rem)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) oa)
    (phase1 : Bool)
    (esLoc : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) × Option ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) × Option ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (LState Pt (BitVec 256) (BitVec 256) Pt))
    (esM esL : EState
      (VP (DDHSt Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256) ⊕ ℕ)
        (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32)))
    (tblM tblL : ℕ → SessHSt Pt ℓ)
    (hsync : SyncDir1 C ℓ encT idOf q Δcka l t ks bs phase1 rem esLoc esM esL tblM tblL) :
    let cka := dhScheme Dh
    let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let mo : Mode := ⟨true, some (l - 1), t⟩
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    Dir1Rel phase1
      (simulateQ lImpl
        ((simulateQ (implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esLoc) >>=
        fun z => pure (authOut (2 + Δcka) mo.policy z.2))
      ((simulateQ (pubFsMultiImpl (impl false))
        ((simulateQ (implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esM)).run
        (fun _ => false, tblM) >>= fun z => pure (authOut (2 + Δcka) mo.policy z.1.2))
      ((simulateQ (pubFsMultiImpl (impl true))
        ((simulateQ (implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL)).run
        (fun _ => false, tblL) >>= fun z => pure z.1.2.h.lfWin) := by
  intro cka prng fs mo impl
  induction oa using OracleComp.inductionOn generalizing rem phase1 esLoc esM esL tblM tblL with
  | pure a =>
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, pure_bind]
    exact dir1Rel_of_lhs_zero (by simp [authOut, hsync.hwinL])
  | query_bind qry k ih =>
    rcases badSendMsgDF_query_bind_step (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      qry k hsh with ⟨hbad_f, hsh_k⟩
    let kLoc : _ → _ → ProbComp Bool := fun res es' =>
      simulateQ lImpl
        ((simulateQ (implEDFShiftedPaper l (hooksLocalPrefix cka prng fs mo q ks)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) (k res)).run es') >>=
        fun z => pure (authOut (2 + Δcka) mo.policy z.2)
    let kM : _ → _ → ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool := fun res es' st' =>
      (simulateQ (pubFsMultiImpl (impl false))
        ((simulateQ (implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false false)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) (k res)).run es')).run st' >>=
        fun z => pure (authOut (2 + Δcka) mo.policy z.1.2)
    let kL : _ → _ → ((ℕ → Bool) × (ℕ → SessHSt Pt ℓ)) → ProbComp Bool := fun res es' st' =>
      (simulateQ (pubFsMultiImpl (impl true))
        ((simulateQ (implEDFShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false true)
          (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) (k res)).run es')).run st' >>=
        fun z => pure z.1.2.h.lfWin
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, bind_assoc,
      simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, bind_assoc]
    rcases qry with n | q_game
    · have hq_u := makesAtMostQueriesDF_inl_step n k rem hq
      exact step_coinsE_dir1 C ℓ Dh encPt encT idOf q Δcka qep l t ks bs phase1 rem
        esLoc esM esL tblM tblL hsync n kLoc kM kL
        (fun u => ih u rem (hq_u u) (hsh_k u) phase1 esLoc esM esL tblM tblL hsync)
    · cases rem with
      | zero =>
        exact False.elim (makesAtMostQueriesDF_inr_zero q_game k hq)
      | succ rem' =>
        have hq_u := makesAtMostQueriesDF_inr_succ q_game k rem' hq
        rcases q_game with ((((⟨P, m, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c₁, c₂⟩
        · have hok : atomicShortPubB m.1 = true := by
            simpa [_root_.CryptoVerification.LibsignalSession.HeadlineV1.badSendMsgDF] using hbad_f
          have hshort : m.1.shortB = true := atomicShortPubB_imp_shortB hok
          exact step_transmitE_dir1 C hrt ℓ hℓ Dh encPt encT idOf q Δcka qep l t
            hq_pos ht3 hl ks bs phase1 rem' esLoc esM esL tblM tblL hsync P m hshort r_c kLoc kM kL
            (fun res esLoc' hd => evalDist_loc_eq_zero_of_dead
              (hooksLocalPrefix cka prng fs mo q ks) Δcka qep fs.maxSkip l t (k res) esLoc' hd)
            (fun res phase1' esLoc' esM' esL' tblM' tblL' hsync' =>
              ih res rem' (hq_u res) (hsh_k res) phase1' esLoc' esM' esL' tblM' tblL' hsync')
        · exact step_challE_dir1 C ℓ Dh encPt encT idOf q Δcka qep l t ks bs phase1 rem'
            esLoc esM esL tblM tblL hsync P m₀ m₁ r_c kLoc kM kL
            (fun hsync' => ih none rem' (hq_u none) (hsh_k none) phase1 esLoc esM esL tblM tblL hsync')
        · exact step_deliverE_dir1 C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka qep l t
            ks bs phase1 rem' esLoc esM esL tblM tblL hsync P c kLoc kM kL
            (fun res esLoc' hd => evalDist_loc_eq_zero_of_dead
              (hooksLocalPrefix cka prng fs mo q ks) Δcka qep fs.maxSkip l t (k res) esLoc' hd)
            (fun _ esL' tblL' hab hlf => by
              have h1 := evalDist_pubFsMulti_true_eq_one_of_abort_lfWin cka prng fs Δcka qep l t
                (impl true) (k none) esL' (fun _ => false, tblL') hab hlf
              dsimp only at h1
              rwa [fst_map_simulateQ_pubFsMulti_bind] at h1)
            (fun res phase1' esLoc' esM' esL' tblM' tblL' hsync' =>
              ih res rem' (hq_u res) (hsh_k res) phase1' esLoc' esM' esL' tblM' tblL' hsync')
        · exact step_injectE_dir1 C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka qep l t ht_qep
            ks bs phase1 rem' esLoc esM esL tblM tblL hsync P c kLoc kM kL
            (fun res esLoc' hd => evalDist_loc_eq_zero_of_dead
              (hooksLocalPrefix cka prng fs mo q ks) Δcka qep fs.maxSkip l t (k res) esLoc' hd)
            (fun _ esL' tblL' hab hlf => by
              have h1 := evalDist_pubFsMulti_true_eq_one_of_abort_lfWin cka prng fs Δcka qep l t
                (impl true) (k none) esL' (fun _ => false, tblL') hab hlf
              dsimp only at h1
              rwa [fst_map_simulateQ_pubFsMulti_bind] at h1)
            (fun res esLoc' esM' tblM' cL' hwL hwM hout => by
              have h1 := dir1Rel_both_win_terminal cka prng fs Δcka qep l t phase1
                (hooksLocalPrefix cka prng fs mo q ks) (impl false) (k res)
                esLoc' esM' (fun _ => false, tblM') cL' hwL hwM hout
              dsimp only at h1
              rwa [fst_map_simulateQ_pubFsMulti_bind] at h1)
            (fun res phase1' esLoc' esM' esL' tblM' tblL' hsync' =>
              ih res rem' (hq_u res) (hsh_k res) phase1' esLoc' esM' esL' tblM' tblL' hsync')
        · exact step_corrE_dir1 C ℓ Dh encPt encT idOf q Δcka qep l t ht3 hl
            ks bs phase1 rem' esLoc esM esL tblM tblL hsync P kLoc kM kL
            (fun res esLoc' hd => evalDist_loc_eq_zero_of_dead
              (hooksLocalPrefix cka prng fs mo q ks) Δcka qep fs.maxSkip l t (k res) esLoc' hd)
            (fun res phase1' esLoc' esM' esL' tblM' tblL' hsync' =>
              ih res rem' (hq_u res) (hsh_k res) phase1' esLoc' esM' esL' tblM' tblL' hsync')
        · exact step_deliverForgeE_dir1 C hD hrt ℓ hℓ Dh encPt encT idOf q Δcka qep l t ht_qep
            ks bs phase1 rem' esLoc esM esL tblM tblL hsync P c₁ c₂ kLoc kM kL
            (fun res esLoc' hd => evalDist_loc_eq_zero_of_dead
              (hooksLocalPrefix cka prng fs mo q ks) Δcka qep fs.maxSkip l t (k res) esLoc' hd)
            (fun _ esL' tblL' hab hlf => by
              have h1 := evalDist_pubFsMulti_true_eq_one_of_abort_lfWin cka prng fs Δcka qep l t
                (impl true) (k none) esL' (fun _ => false, tblL') hab hlf
              dsimp only at h1
              rwa [fst_map_simulateQ_pubFsMulti_bind] at h1)
            (fun res esLoc' esM' tblM' cL' hwL hwM hout => by
              have h1 := dir1Rel_both_win_terminal cka prng fs Δcka qep l t phase1
                (hooksLocalPrefix cka prng fs mo q ks) (impl false) (k res)
                esLoc' esM' (fun _ => false, tblM') cL' hwL hwM hout
              dsimp only at h1
              rwa [fst_map_simulateQ_pubFsMulti_bind] at h1)
            (fun res phase1' esLoc' esM' esL' tblM' tblL' hsync' =>
              ih res rem' (hq_u res) (hsh_k res) phase1' esLoc' esM' esL' tblM' tblL' hsync')

private theorem localAuthPrefix_dir1_leAdd_pubFs
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep l t : ℕ) (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (ht_qep : t ≤ qep + 1)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let cka0 := dhScheme Dh
    let prng0 := CryptoGames.Ratchet.rootPRNG C.F encPt
    let fs0 := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
    LeAdd
      (localAuthPrefix cka0 prng0 fs0 lam Δcka qep l (some (l - 1)) t q ks A)
      (Prod.fst <$> (simulateQ (pubFsMultiImpl (impl false))
        (_root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2.redFSAuthDFShiftedPaperMulti
          cka0 prng0 fs0 lam Δcka qep l t false A)).run ((fun _ => false), tbl0))
      (Prod.fst <$> (simulateQ (pubFsMultiImpl (impl true))
        (_root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2.redFSAuthDFShiftedPaperMulti
          cka0 prng0 fs0 lam Δcka qep l t true A)).run ((fun _ => false), tbl0)) := by
  intro cka0 prng0 fs0 impl tbl0
  have ht0 : 0 < t := by omega
  have ht2 : 2 ≤ t := by omega
  have hℓ_rust : ℓ + 16 < rustLenBound := by
    unfold rustLenBound; omega
  have hrt : SignalRoundTripShort protoSignalCodec :=
    _root_.CryptoVerification.LibsignalSession.signalRoundTripShort_proto
  unfold localAuthPrefix
  dsimp only
  rw [initLocal_lImpl_run C ℓ Dh encPt encT idOf lam l t ht0]
  by_cases hq0 : q = 0
  · subst hq0
    refine leAdd_of_lhs_zero ?_
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_eq_zero _ _ fun kr _ => evalDist_bind_eq_zero _ _ fun kc _ => ?_
    exact evalDist_loc_eq_zero_of_rem_zero _ Δcka qep fs0.maxSkip l t A hq _ rfl _
      (fun _ _ hw => by simp [authOut, hw])
  · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
    unfold _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2.redFSAuthDFShiftedPaperMulti
      _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2.redFSAuthDFShiftedPaperMultiGen
      _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2.runFSMultiDFShiftedPaper
    simp only [Bool.not_true, ↓reduceIte, implEDFShiftedPaperGen_false_eq]
    rw [fst_map_simulateQ_pubFsMulti_bind, fst_map_simulateQ_pubFsMulti_bind]
    simp only [simulateQ_bind, StateT.run_bind]
    erw [initFSMultiRaw_pubFsMulti_run C ℓ Dh encPt encT idOf lam l t ht0 (impl false) (fun _ => false, tbl0),
      initFSMultiRaw_pubFsMulti_run C ℓ Dh encPt encT idOf lam l t ht0 (impl true) (fun _ => false, tbl0)]
    simp only [bind_assoc, pure_bind]
    refine leAdd_bind _ fun kr _ => leAdd_bind _ fun kc _ => ?_
    have hsync0 := syncDir1_init_state C ℓ Dh encPt encT idOf lam q Δcka l t ht2 ks bs kr kc
    exact simulateQ_dir1Rel C hD hrt ℓ hℓ_rust Dh encPt encT hinj hdum idOf
      q Δcka qep l t hq_pos ht3 hl ht_qep ks bs A q hq hsh true _ _ _ tbl0 tbl0 hsync0

end Sub4Helpers

/-! ### Sub-Lemmas -/

/-- Sub-lemma 1 (Short-horizon zero bound): When `qep + 1 < t` (with `2 ≤ t`), neither party
can advance to target epoch `t`, so `Config.auth t` never sets `win = true`. -/
private theorem evalDist_localAuthDFShiftedPaper_eq_zero_of_qep_lt
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep l : ℕ) (tL : Option ℕ) (t : ℕ)
    (ht2 : 2 ≤ t) (hqep_lt : qep + 1 < t)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthDFShiftedPaper cka prng fs lam Δcka qep l tL t A] {true} = 0 := by
  let _ := ht2; exact Sub123Helpers.evalDist_loc_eq_zero_of_qep_lt cka prng fs lam Δcka qep l tL t hqep_lt A

/-- Sub-lemma 2 (Lazy-to-eager session-key prefix hybrid): Pre-sampling `m` uniform session
keys `ks ← sampleVec ($ᵗ K) k0 m` and feeding the first `m` target-epoch sessions from `ks`
upper-bounds `localAuthDFShiftedPaper`. -/
private theorem localAuthDFShiftedPaper_le_sampleVec
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (k0 : K) (Δcka qep l t : ℕ)
    (ht2 : 2 ≤ t)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (m : ℕ) :
    𝒟[localAuthDFShiftedPaper cka prng fs lam Δcka qep l (some (l - 1)) t A] {true} ≤
      𝒟[sampleVec ($ᵗ K : ProbComp K) k0 m >>= fun ks =>
          localAuthPrefix cka prng fs lam Δcka qep l (some (l - 1)) t m ks A] {true} := by
  exact Sub123Helpers.localAuthDFShiftedPaper_le_sampleVec cka prng fs lam k0 Δcka qep l t (by omega) A m

/-- Sub-lemma 3 (Multi-session `sessOffRange q` bound): Under `2 ≤ t` and
`MakesAtMostQueriesDF A q`, `redFSAuthDFShiftedPaperMulti` never queries session index `≥ q`. -/
private theorem redFSAuthDFShiftedPaperMulti_offRange
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep l t : ℕ) (ht2 : 2 ≤ t) (la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFShiftedPaperMulti cka prng fs lam Δcka qep l t la A).IsQueryBoundP
      (fun u => sessOffRange q u = true) 0 := by
  exact Sub123Helpers.redFSAuthDFShiftedPaperMulti_offRange cka prng fs lam q Δcka qep l t (by omega) la A hq

/-- Sub-lemma 4 (Per-`(ks, bs)` eager-keyed `LeAdd` simulation coupling): Couples
`localAuthPrefix ... q ks A` to the `la = false` + `la = true` `pubFsMultiImpl` executions of
`redFSAuthDFShiftedPaperMulti` when `t ≤ qep + 1`. -/
private theorem localAuthPrefix_dir1_leAdd_pubFs
    {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep l t : ℕ) (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (ht_qep : t ≤ qep + 1)
    (ks : ℕ → BitVec 256) (bs : ℕ → Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let cka0 := dhScheme Dh
    let prng0 := rootPRNG C.F encPt
    let fs0 := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    let impl := fun la => fsImpl (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps (hp 0 0 la)
    let tbl0 : ℕ → SessHSt Pt ℓ := fun i => hInit (bs i) (.seed (ks i))
    LeAdd
      (localAuthPrefix cka0 prng0 fs0 lam Δcka qep l (some (l - 1)) t q ks A)
      (Prod.fst <$> (simulateQ (pubFsMultiImpl (impl false))
        (redFSAuthDFShiftedPaperMulti cka0 prng0 fs0 lam Δcka qep l t false A)).run ((fun _ => false), tbl0))
      (Prod.fst <$> (simulateQ (pubFsMultiImpl (impl true))
        (redFSAuthDFShiftedPaperMulti cka0 prng0 fs0 lam Δcka qep l t true A)).run ((fun _ => false), tbl0)) := by
  exact Sub4Helpers.localAuthPrefix_dir1_leAdd_pubFs C Dh hD encPt encT hinj hdum idOf lam hℓ
    q Δcka qep l t ht3 hl ht_qep ks bs A hq hsh

/-! ### Glue Theorem (`localAuthDFShiftedPaper_le_multiSessRealWinProb_split`) -/

/-- Glue theorem for `SessionAuthMultiRealShiftedDir1.localAuthDFShiftedPaper_le_multiSessRealWinProb`. -/
theorem localAuthDFShiftedPaper_le_multiSessRealWinProb_split
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep l t : ℕ) (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedPaperMulti (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t la A)
    𝒟[localAuthDFShiftedPaper (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l (some (l - 1)) t A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  intro Adv
  have ht2 : 2 ≤ t := by omega
  by_cases hqep_lt : qep + 1 < t
  · rw [evalDist_localAuthDFShiftedPaper_eq_zero_of_qep_lt (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l (some (l - 1)) t ht2 hqep_lt A]
    simp
  · have ht_qep : t ≤ qep + 1 := Nat.le_of_not_lt hqep_lt
    refine le_multiSessRealWinProb_of_perKey C ℓ encT idOf Adv
      (localAuthDFShiftedPaper (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l (some (l - 1)) t A)
      (fun ks => localAuthPrefix (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l (some (l - 1)) t q ks A)
      q 0
      (localAuthDFShiftedPaper_le_sampleVec (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 0 Δcka qep l t ht2 A q)
      (fun la => ?_)
      (fun ks bs => ?_)
    · apply multiSessPubToAD_offRange
      exact redFSAuthDFShiftedPaperMulti_offRange (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep l t ht2 la A hq
    · dsimp only [Adv]
      rw [simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl,
        simulateQ_sessLift_multiSessPubToAD_eq_pubFsMultiImpl]
      exact localAuthPrefix_dir1_leAdd_pubFs C Dh hD encPt encT hinj hdum idOf lam hℓ
        q Δcka qep l t ht3 hl ht_qep ks bs A hq hsh

end

end Computational.Proofs.E2E.SessionAuthMultiRealShiftedDir1Split

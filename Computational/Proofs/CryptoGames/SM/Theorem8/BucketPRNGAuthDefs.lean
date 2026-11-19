/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.GameProofDefs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedCKA -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedPRNG -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.ReductionDsl.Notation
import VCVio.OracleComp.EvalDist.Measure

/-!
# Stage-2 `canon`-Bucket Multi-Epoch PRNG Hybrid and Bucket-Wide FS-AEAD Split (`Critic S2`)

Mirrors the ascending `t`-hybrid PRNG architecture (`t ∈ Finset.Ico (healEpoch tL) (qep + 2)`)
onto standard `SM` (`4`-oracle `SM.spec`, `DEV-SM6` `corrAllowed`), resolving both `Critic S2`
(hoisting `+ 8 * macForgeryTerm C q` outside `∑ t` by keeping the game `tL`-bucketed through the
entire PRNG hybrid before splitting once per `tL` bucket into `Main_bucket` + `ForgedHdr_bucket`)
and the `corr(P)` / post-leak coupling invariant (`postLeak` + `corrRoot` `PRFPRNG.corrQuery`):

1. **Shallow `canon`-bucket CKA & multi-epoch PRNG hybrid (`redCKAAuthBucket`,
   `redPRNGAuthBucketHybrid`, `localAuthBucket`)**:
   - `postLeak tL ctx` checks whether `ctx.tL` already exceeds `tL` (`ltOpt tL cur`); once `true`,
     every future epoch `t0 > cur > tL` is deterministically excluded from winning bucket `tL` by
     `authLosingConditionsAvoided`, so both `redPRNGAuthBucketHybrid` and `localAuthBucket` step
     locally via `prng.up` (`0` `PRFPRNG` queries, `0` random-table lookups).
   - `reveal` resolves `vp.root` via `corrRoot : Option (ℕ × Sig)`; if `vp.root = none` at
     `e = vp.tcur ≥ healEpoch tL` while `!postLeak tL ctx`, `corrRoot.isNone`, and
     `e = max (ctx.epoch .A) (ctx.epoch .B)`, it calls `PRFPRNG.corrQuery` (`1` query), stores
     `corrRoot := some (e, σOut)` so the peer party also recovers `σOut` upon delivering epoch `e`
     or advancing to `e + 1`, and `afterCorr` sets `postLeak = true` so zero further `PRFPRNG`
     queries occur.
2. **Bucket-wide `Main_bucket` + `ForgedHdr_bucket` split (`localAuthBucketMain`,
   `localAuthBucketForgedHdr`, `redFSAuthMultiBucketProg`)**:
   - Splits `localAuthBucket` once per `tL` bucket into honest-header (`gMain = true`, external
     session `sIdx = t0 - healEpoch tL` for `j = 0`) and forged-header (`gMain = false`, external
     session `sIdx = (L - 1) * (t0 - healEpoch tL) + localIdx` for `1 ≤ j ≤ q`), enabling
     `SessionAuthBridge` to discharge `+ 4 + 4 = + 8 * macForgeryTerm C q` per `tL` bucket.
3. **Costed `ReductionDsl` programs (`redPRNGAuthBucketHybridProg`, `redFSAuthMultiBucketProg`)**:
   - `totalQueries = 2 + q * 2`, `PotOK` `min (2 + 2 * q) (q + 3)`, and evaluation bridges for
     `Bundles.fig8RedsInst.{redPRNGAuth, redFSAuth}`.-/

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs

public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec
open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp CostedReduction)
open scoped _root_.Computational.Proofs.ReductionDsl.Notation
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme SMScheme)
open _root_.CryptoGames.CKA (CKASamp CKAOp ckaHdrTy ckaHdrCtTy ckaPsTy)
open _root_.CryptoGames.PRFPRNG
  (PRNGTag FSHdrTag prngSig prngOps prngIface fsaeadHeaderAdIface fsHdrRrEnc prngSamplers
   prngSMCodec)
open _root_.CryptoGames.SM
  (Config GameState Pos Record RecvResult
   MakesAtMostQueries admissibleLastLeakGuesses authLosingConditionsAvoided
   healedBy lastLeakGuessAdmissible ltOpt ltOptE maxN orE isSomeE pGet senderOfE validGuessE
   spec)
open _root_.CryptoGames.SM.Engine
  (VP Ctx HM EState EM Hooks HooksC HooksVRInv ConfigEC Policy
   mkPartiesE realPartyE
   vpTblTy cRecTy cRecMsg hdrCtEqE cSafeChE cGsTy esTy esG esH esAbort esMk esSetG
   cGsSt cGsEpoch cGsIdx cGsTL cGsWin cGsSetWin cGsInitE
   cEpMgmtE cRecordE cCorrAllowedE cAfterCorrE cAuthOKE optNatLit
   vpΓ vpRoot vpVS vpVR vpTcurNat
   vSend vSendC deliverE deliverEC injectE injectEC
   eval_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState healEpoch realParty mkParties sampleT
   SchemeAdversary CKAState hooksCKA initCKA scheme
   prngHsTy prngVpTy abortedPartiesE bucketAuthCfgEC)

/-! ## 1. Shallow `canon`-Bucket CKA, Multi-Epoch PRNG Hybrid, and Post-PRNG Local Game -/

section ShallowBucketAuth

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

/-- `true` once `ctx.tL` records a leak strictly after `tL` (`ltOpt tL cur`). Because `DEV-SM3`
maintains `ctx.tL = max? ctx.leaks`, any epoch started after `postLeak tL ctx = true` satisfies
`tWin > cur > tL` and is deterministically excluded by `authLosingConditionsAvoided`. -/
@[expose] def postLeak {St Msg C : Type} (tL : Option ℕ) (ctx : GameState St Msg C) : Bool :=
  match ctx.tL with
  | none => false
  | some cur => ltOpt tL cur

/-- Hooks of Stage-2 `canon`-bucket `redCKAAuthBucket` (`rfl`-compatible with `Theorem8`). -/
@[expose] def hooksCKABucket [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) :
    Hooks ( _root_.CryptoGames.CKA.spec Γ CCoins T I) (CKAState T I) Γ T Sig SS RS M E CCoins
      (Option Γ) Sig SS RS :=
  { hooksCKA cka prng fs Δcka ⟨true, tL, 0⟩ with
    startRecv := fun _ _ t γv σ Tn => do
      let honest := match (← get).cache t with
        | some (Tc, Ik) => if Tc = Tn then some Ik else none
        | none => none
      match honest with
      | some Ik =>
        let p := prng.up σ Ik
        return some (some (γv.map fun γ => (cka.receive γ Tn).1, p.1, fs.initReceiver p.2))
      | none =>
        if lastLeakGuessAdmissible (2 + Δcka) tL t then
          match γv with
          | some γ =>
            let k := cka.receive γ Tn
            let p := prng.up σ k.2
            return some (some (some k.1, p.1, fs.initReceiver p.2))
          | none => return none
        else return some none }

/-- Authenticity `Config` for Stage-2 `canon`-bucket reductions at `tL`. -/
@[expose] def bucketAuthCfg (Δcka : ℕ) (tL : Option ℕ) : Config M where
  deliverWin := false
  injectFull := fun t' => lastLeakGuessAdmissible (2 + Δcka) tL t'
  challAllowedIn := fun _ => false
  challMsg := fun _ => none

/-- State of `runCKAAuthBucket`: engine state paired with first winning `inject` epoch `winEp`. -/
abbrev CKABucketEState (Γ T Sig SS RS M E I : Type) :=
  EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) × Option ℕ

/-- Oracle dispatcher of `redCKAAuthBucket` (`rfl`-compatible with `Theorem8.implCKABucket`). -/
@[expose] def implCKABucket [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) :
    QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (_root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I)) :=
  let hk := hooksCKABucket cka prng fs Δcka tL
  let cfg := bucketAuthCfg (M := M) Δcka tL
  let i₀ : QueryImpl unifSpec
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (_root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I)) :=
    fun n => StateT.lift (query (spec := unifSpec + _root_.CryptoGames.CKA.spec Γ CCoins T I) (.inl n))
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (_root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I)) :=
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
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (_root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I)) :=
    fun _ => pure none
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (_root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I)) :=
    fun x => do
      let (es0, winEp0) ← get
      let (out, es') ← StateT.lift ((deliverE hk fs.maxSkip cfg x).run es0)
      set (es', winEp0)
      return out
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (_root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I)) :=
    fun x => do
      let (es0, winEp0) ← get
      let wasWin := es0.g.win
      let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg x).run es0)
      let winEp' := if !wasWin && es'.g.win then some x.2.1.1 else winEp0
      set (es', winEp')
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (_root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I)) :=
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

/-- Engine run of Stage-2 `canon`-bucket `redCKAAuthBucket`. -/
@[expose] def runCKAAuthBucket [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    _root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I
      (Option (Bool × CKABucketEState Γ T Sig SS RS M E I)) := do
  let (vs, h) ← (initCKA cka prng fs lam ⟨true, tL, 0⟩).run {}
  match vs with
  | none => return none
  | some (vA, vB) =>
    let g : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let res ← (simulateQ (implCKABucket cka prng fs Δcka qep tL) A).run ({ g, h }, none)
    return some res

/-- Stage-2 `canon`-bucket CKA authenticity reduction `redCKAAuthBucket`. -/
@[expose] def redCKAAuthBucket [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    _root_.CryptoGames.CKA.Adversary Γ CCoins T I :=
  show _root_.CryptoGames.CKA.AdversaryComp Γ CCoins T I Bool from do
    match ← runCKAAuthBucket cka prng fs lam Δcka qep tL A with
    | none => return false
    | some (_, es, winEp) =>
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

/-! ### Multi-Epoch `canon`-Bucket PRNG Hybrid (`redPRNGAuthBucketHybrid`) -/

/-- Hook state for `hooksPRNGBucketAuthHybrid`: honest-send cache, per-epoch lazy random tables
`fTable t0 : List (I × K)` for already-hybridized epochs `healEpoch tL ≤ t0 < t`, and optional
leaked root `(eC, σC)` recorded on the first `corr(P)` at `eC ≥ healEpoch tL`. -/
structure PRNGBucketAuthState (T Sig K I : Type) where
  cache : ℕ → Option (T × Option Sig × K) := fun _ => none
  fTable : ℕ → List (I × K) := fun _ => []
  corrRoot : Option (ℕ × Sig) := none

/-- Resolve `σv` at epoch `ep` using `h.corrRoot` when `σv = none`. -/
@[expose] def resolveCorrRoot (h : PRNGBucketAuthState T Sig K I) (ep : ℕ) (σv : Option Sig) :
    Option Sig :=
  match σv with
  | some σ => some σ
  | none =>
    match h.corrRoot with
    | some (eC, σC) => if ep == eC then some σC else none
    | none => none

/-- Lift a `PRFPRNG` oracle computation into `HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)`. -/
@[expose] def liftPBucketAuth {α : Type} (x : PRFPRNG.AdversaryComp Sig I K α) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) α :=
  StateT.lift x

/-- Lazily sample `F_{t0}(ik)` inside `HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)`. -/
@[expose] def lookupPRNGBucketAuthF [DecidableEq I] [SampleableType K] (t0 : ℕ) (ik : I) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) K := do
  let tb0 := (← get).fTable t0
  match tb0.lookup ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with fTable := Function.update s.fTable t0 ((ik, k) :: tb0) }
    return k

/-- Root-RNG step of epoch `t0` in the `canon`-bucket ascending `t`-hybrid PRNG reduction. -/
@[expose] def rootPRNGBucketAuthHybrid [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t t0 : ℕ) (pl : Bool)
    (ik0 : I) (σv0 : Option Sig) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I) (Option (Option Sig × K)) := do
  let h0 ← get
  let tH := healEpoch tL
  let σv := resolveCorrRoot h0 (t0 - 1) σv0
  if t < t0 then
    match σv with
    | none => return none
    | some σ =>
      let p := prng.up σ ik0
      return some (some p.1, p.2)
  else if pl || h0.corrRoot.isSome then
    match σv with
    | some σ =>
      let p := prng.up σ ik0
      return some (some p.1, p.2)
    | none =>
      match ← liftPBucketAuth (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
      | none => return none
      | some σOut =>
        modify fun s => { s with corrRoot := some (t0 - 1, σOut) }
        let p := prng.up σOut ik0
        return some (some p.1, p.2)
  else if t0 = t then
    if tL.isSome && t0 = tH then
      match ← liftPBucketAuth (PRFPRNG.challPrngQuery (State := Sig) (Input := I) (Output := K) none) with
      | none => return none
      | some kOut =>
        match ← liftPBucketAuth (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
        | none => return none
        | some σOut => return some (some σOut, kOut)
    else
      match ← liftPBucketAuth (PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) ik0) with
      | none => return none
      | some (σOut, kOut) => return some (some σOut, kOut)
  else if !(t0 < tH) then
    if tL.isSome && t0 = tH then
      match ← liftPBucketAuth (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) none) with
      | none => return none
      | some _ =>
        let kRand ← StateT.lift (sampleT K)
        return some (none, kRand)
    else
      match ← liftPBucketAuth (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) (some ik0)) with
      | none => return none
      | some _ =>
        let kRand ← lookupPRNGBucketAuthF t0 ik0
        return some (none, kRand)
  else
    match ← liftPBucketAuth (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) (some ik0)) with
    | none => return none
    | some kOut =>
      match ← liftPBucketAuth (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
      | none => return none
      | some σOut => return some (some σOut, kOut)

/-- Hooks of the `canon`-bucket ascending `t`-hybrid PRNG reduction (`redPRNGAuthBucketHybrid`). -/
@[expose] def hooksPRNGBucketAuthHybrid [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS where
  startSend ctx _ t0 γ0 σv0 r0 := do
    let pl := postLeak tL ctx
    let coins ← match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ0 coins
    match ← rootPRNGBucketAuthHybrid prng tL t t0 pl c.2.2 σv0 with
    | none => return none
    | some (σ', kVal) =>
      modify fun s => { s with cache := Function.update s.cache t0 (some (c.2.1, σ', kVal)) }
      return some (c.1, c.2.1, σ', fs.initSender kVal)
  startRecv ctx _ t0 γ0 σv0 tn0 := do
    let tH := healEpoch tL
    let pl := postLeak tL ctx
    let h0 ← get
    let honest := match h0.cache t0 with
      | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
      | none => none
    match honest with
    | some (σc, kVal) =>
      let σc' := resolveCorrRoot h0 t0 σc
      return some (some ((cka.receive γ0 tn0).1, σc', fs.initReceiver kVal))
    | none =>
      if !(qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 then
        if tL.isSome && t0 = tH then
          return none
        else if pl || h0.corrRoot.isSome || t < t0 then
          match resolveCorrRoot h0 (t0 - 1) σv0 with
          | none => return none
          | some σ =>
            let kk := cka.receive γ0 tn0
            let p := prng.up σ kk.2
            return some (some (kk.1, some p.1, fs.initReceiver p.2))
        else if t0 = t then
          let kk := cka.receive γ0 tn0
          match ← liftPBucketAuth (PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
          | none => return none
          | some (σOut, kOut) =>
            return some (some (kk.1, some σOut, fs.initReceiver kOut))
        else if !(t0 < tH) then
          let kk := cka.receive γ0 tn0
          let kOut ← lookupPRNGBucketAuthF t0 kk.2
          return some (some (kk.1, none, fs.initReceiver kOut))
        else
          return some none
      else
        return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ _ _ new := pure (some new)
  reveal ctx _ vp := do
    let tH := healEpoch tL
    let e := vp.tcur
    let eMax := max (ctx.epoch .A) (ctx.epoch .B)
    let pl := postLeak tL ctx
    let h0 ← get
    match resolveCorrRoot h0 e vp.root with
    | some σ =>
      if !(e < tH) && h0.corrRoot.isNone then
        modify fun s => { s with corrRoot := some (e, σ) }
      return some (realParty vp vp.γ σ vp.vS vp.vR)
    | none =>
      if !pl && h0.corrRoot.isNone && !(e < tH) && (e == eMax) then
        match ← liftPBucketAuth (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
        | none => return none
        | some σOut =>
          modify fun s => { s with corrRoot := some (e, σOut) }
          return some (realParty vp vp.γ σOut vp.vS vp.vR)
      else
        return none

/-- Initial party states for `redPRNGAuthBucketHybrid`. -/
@[expose] def initPRNGBucketAuthHybrid [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (tL : Option ℕ) (t : ℕ) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      (Option (VP Γ T (Option Sig) SS RS × VP Γ T (Option Sig) SS RS)) := do
  let kc ← StateT.lift (sampleT KC)
  match ← rootPRNGBucketAuthHybrid prng tL t 0 false lam none with
  | none => return none
  | some (σv, kVal) =>
    return some (mkParties (cka.initA kc) (cka.initB kc) σv
      (fs.initSender kVal) (fs.initReceiver kVal))

/-- State of `runPRNGAuthBucketHybrid`: engine state paired with `winEp : Option ℕ`. -/
abbrev PRNGBucketAuthEState (Γ T Sig SS RS M E K I : Type) :=
  EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I) × Option ℕ

/-- Pure check whether header `hdr` at epoch `hdr.1` carries the cached honest CKA public value. -/
@[expose] def isHonestHdrPRNGBucket [DecidableEq T]
    (h : PRNGBucketAuthState T Sig K I) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _, _), some Tn => Tc == Tn
  | _, _ => false

/-- Honest-header (`forgedMode = false`, `Main`) variant of `hooksPRNGBucketAuthHybrid`: rejects
forged CKA headers (`honest = none` returns `some none`, aborting `none` at `tH` when `tL.isSome`)
without issuing `PRFPRNG.challPrfQuery`, so `sp.prf` is never set while `eMax = t` and subsequent
`corr` at `e = eMax = t` can query `PRFPRNG.corrQuery`. -/
@[expose] def hooksPRNGBucketAuthMain [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS :=
  { hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t with
    startRecv := fun _ _ t0 γ0 _ tn0 => do
      let tH := healEpoch tL
      let h0 ← get
      let honest := match h0.cache t0 with
        | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
        | none => none
      match honest with
      | some (σc, kVal) =>
        let σc' := resolveCorrRoot h0 t0 σc
        return some (some ((cka.receive γ0 tn0).1, σc', fs.initReceiver kVal))
      | none =>
        if !(qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
            (tL.isSome && decide (t0 = tH)) then
          return none
        else
          return some none }

/-- Forged-header (`forgedMode = true`, `ForgedHdr`) variant of `hooksPRNGBucketAuthHybrid`: aborts
on `reveal` whenever `!(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)`
(since `afterCorr` leaks `eMax ≥ healEpoch tL > tL`, dooming any future new-epoch `inject` under
`safeInj (2 + Δcka)`), avoiding `PRFPRNG.corrQuery` when `sp.prf = true`. -/
@[expose] def hooksPRNGBucketAuthForgedHdr [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS :=
  { hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t with
    reveal := fun ctx _ vp => do
      if !(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL) then
        return none
      else
        match vp.root with
        | some σ => return some (realParty vp vp.γ σ vp.vS vp.vR)
        | none => return none }

/-- Generic oracle dispatcher for `runPRNGAuthBucketHybrid{,Main,ForgedHdr}`. When
`onlyNewForged = true` (`ForgedHdr`), `winEp` is recorded only when the first winning `inject`
is at a new epoch `x.2.1.1 = (es0.g.st x.1).tcur + 1` with `!isHonestHdrPRNGBucket es0.h x.2.1`. -/
@[expose] def implPRNGBucketAuthGen [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onlyNewForged : Bool) :
    QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
  let cfg := bucketAuthCfg (M := M) Δcka tL
  let i₀ : QueryImpl unifSpec
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
    fun n => StateT.lift (query (spec := unifSpec + PRFPRNG.spec Sig I K) (.inl n))
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
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
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
    fun _ => pure none
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
    fun x => do
      let (es0, winEp0) ← get
      let (out, es') ← StateT.lift ((deliverE hk maxSkip cfg x).run es0)
      set (es', winEp0)
      return out
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
    fun x => do
      let (es0, winEp0) ← get
      let wasWin := es0.g.win
      let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg x).run es0)
      let isNewForged :=
        decide (x.2.1.1 = (es0.g.st x.1).tcur + 1) && !isHonestHdrPRNGBucket es0.h x.2.1
      let winEp' :=
        if !wasWin && es'.g.win && (!onlyNewForged || isNewForged) then some x.2.1.1 else winEp0
      set (es', winEp')
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
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

/-- Unsplit oracle dispatcher retained for `HooksVRInv` / `hooksPRNGBucketAuthHybrid` lemmas. -/
@[expose] def implPRNGBucketAuth [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (PRNGBucketAuthEState Γ T Sig SS RS M E K I) (PRFPRNG.AdversaryComp Sig I K)) :=
  implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t)
    Δcka qep fs.maxSkip tL false

/-- Generic engine run for `redPRNGAuthBucketHybrid{,Main,ForgedHdr}`. -/
@[expose] def runPRNGAuthBucketHybridGen [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (onlyNewForged : Bool)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.AdversaryComp Sig I K (Option (Bool × PRNGBucketAuthEState Γ T Sig SS RS M E K I)) := do
  let (vs, h) ← (initPRNGBucketAuthHybrid cka prng fs lam tL t).run {}
  match vs with
  | none => return none
  | some (vA, vB) =>
    let g : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let res ← (simulateQ (implPRNGBucketAuthGen hk Δcka qep fs.maxSkip tL onlyNewForged) A).run
      ({ g, h }, none)
    return some res

/-- Unsplit engine run retained for `hooksPRNGBucketAuthHybrid` evaluation lemmas. -/
@[expose] def runPRNGAuthBucketHybrid [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.AdversaryComp Sig I K (Option (Bool × PRNGBucketAuthEState Γ T Sig SS RS M E K I)) :=
  runPRNGAuthBucketHybridGen cka prng fs (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t)
    lam Δcka qep tL t false A

/-- Honest-header (`forgedMode = false`, `Main`) Stage-2 `canon`-bucket PRNG hybrid reduction. -/
@[expose] def redPRNGAuthBucketHybridMain [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    match ← runPRNGAuthBucketHybridGen cka prng fs
        (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t) lam Δcka qep tL t false A with
    | none => return false
    | some (_, es, winEp) =>
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

/-- Forged-header (`forgedMode = true`, `ForgedHdr`) Stage-2 `canon`-bucket PRNG hybrid reduction. -/
@[expose] def redPRNGAuthBucketHybridForgedHdr [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    match ← runPRNGAuthBucketHybridGen cka prng fs
        (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t) lam Δcka qep tL t true A with
    | none => return false
    | some (_, es, winEp) =>
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

/-- Coin-averaged (`forgedMode ← sampleT Bool`) Stage-2 `canon`-bucket ascending `t`-hybrid
PRF-PRNG reduction (`fig8.redPRNGAuth tL t`). -/
@[expose] def redPRNGAuthBucketHybrid [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    let forgedMode ← sampleT Bool
    if forgedMode then
      redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL t A
    else
      redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL t A

/-! ### Post-PRNG Local `canon`-Bucket Game (`localAuthBucket`, `Main`, `ForgedHdr`) -/

/-- Hook state for the post-PRNG `canon`-bucket local game (`localAuthBucket`). -/
structure LocalBucketAuthState (T Sig K I : Type) where
  cache : ℕ → Option (T × Sig × K) := fun _ => none
  fTable : ℕ → List (I × K) := fun _ => []

/-- Lazily sample `F_{t0}(ik)` inside `HM _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I)`. -/
@[expose] def lookupLocalBucketAuthF [DecidableEq I] [SampleableType K] (t0 : ℕ) (ik : I) :
    HM _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I) K := do
  let tb0 := (← get).fTable t0
  match tb0.lookup ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with fTable := Function.update s.fTable t0 ((ik, k) :: tb0) }
    return k

/-- Root-RNG step of `localAuthBucket`: once `pl` (`postLeak tL ctx`) holds or `t0 > qep + 1` or
`t0 < healEpoch tL`, steps locally via `prng.up`; for `healEpoch tL ≤ t0 ≤ qep + 1` while `!pl`,
draws `k` from `fTable t0` (uniform `$ᵗ K` with fresh `$ᵗ I` at `tH` when `tL.isSome`). -/
@[expose] def rootLocalBucketAuth [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (qep : ℕ) (tL : Option ℕ) (t0 : ℕ) (pl : Bool)
    (ik0 : I) (σ0 : Sig) :
    HM _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I) (Sig × K) := do
  let tH := healEpoch tL
  let pIk := prng.up σ0 ik0
  if pl || qep + 1 < t0 then
    return (pIk.1, pIk.2)
  else if tL.isSome && t0 = tH then
    let ir ← StateT.lift (sampleT I)
    let kSample ← StateT.lift (sampleT K)
    return ((prng.up σ0 ir).1, kSample)
  else if !(t0 < tH) then
    let kLookup ← lookupLocalBucketAuthF t0 ik0
    return (pIk.1, kLookup)
  else
    return (pIk.1, pIk.2)

/-- Hooks of the post-PRNG `canon`-bucket local game (`localAuthBucket`). -/
@[expose] def hooksLocalBucketAuth [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) :
    Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS where
  startSend ctx _ t0 γ0 σ0 r0 := do
    let pl := postLeak tL ctx
    let coins ← match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ0 coins
    let (σ', kVal) ← rootLocalBucketAuth prng qep tL t0 pl c.2.2 σ0
    modify fun s => { s with cache := Function.update s.cache t0 (some (c.2.1, σ', kVal)) }
    return some (c.1, c.2.1, σ', fs.initSender kVal)
  startRecv ctx _ t0 γ0 σ0 tn0 := do
    let tH := healEpoch tL
    let pl := postLeak tL ctx
    let honest := match (← get).cache t0 with
      | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
      | none => none
    match honest with
    | some (σc, kVal) =>
      return some (some ((cka.receive γ0 tn0).1, σc, fs.initReceiver kVal))
    | none =>
      if !(qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 then
        if tL.isSome && t0 = tH then
          return none
        else if pl then
          let kk := cka.receive γ0 tn0
          let p := prng.up σ0 kk.2
          return some (some (kk.1, p.1, fs.initReceiver p.2))
        else if !(t0 < tH) then
          let kk := cka.receive γ0 tn0
          let kOut ← lookupLocalBucketAuthF t0 kk.2
          return some (some (kk.1, (prng.up σ0 kk.2).1, fs.initReceiver kOut))
        else
          return some none
      else
        return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := pure (some (realParty vp vp.γ vp.root vp.vS vp.vR))

/-- Honest-header (`Main`) variant of `hooksLocalBucketAuth`: rejects forged CKA headers
(`honest = none` returns `some none`, aborting `none` at `tH` when `tL.isSome`). -/
@[expose] def hooksLocalBucketAuthMain [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) :
    Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS :=
  { hooksLocalBucketAuth cka prng fs Δcka qep tL with
    startRecv := fun _ _ t0 γ0 _ tn0 => do
      let tH := healEpoch tL
      let honest := match (← get).cache t0 with
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
          return some none }

/-- Forged-header (`ForgedHdr`) variant of `hooksLocalBucketAuth`: aborts on `reveal` whenever
`!(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)`, matching
`hooksPRNGBucketAuthForgedHdr` at `t = qep + 1`. -/
@[expose] def hooksLocalBucketAuthForgedHdr [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) :
    Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS :=
  { hooksLocalBucketAuth cka prng fs Δcka qep tL with
    reveal := fun ctx _ vp =>
      if !(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL) then
        pure none
      else
        pure (some (realParty vp vp.γ vp.root vp.vS vp.vR)) }

/-- Initial party states for `localAuthBucket{,Main,ForgedHdr}`. -/
@[expose] def initLocalBucketAuth [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep : ℕ) (tL : Option ℕ) :
    HM _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I)
      (Option (VP Γ T Sig SS RS × VP Γ T Sig SS RS)) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ0, k0) ← rootLocalBucketAuth prng qep tL 0 false lam (prng.init kr)
  return some (mkParties (cka.initA kc) (cka.initB kc) σ0
    (fs.initSender k0) (fs.initReceiver k0))

/-- State of `localAuthBucket{,Main,ForgedHdr}`. -/
abbrev LocalBucketAuthEState (Γ T Sig SS RS M E K I : Type) :=
  EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I) × Option ℕ

/-- Pure check whether header `hdr` at epoch `hdr.1` carries the cached honest CKA public value. -/
@[expose] def isHonestHdrLocalBucket [DecidableEq T]
    (h : LocalBucketAuthState T Sig K I) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _, _), some Tn => Tc == Tn
  | _, _ => false

/-- Oracle dispatcher for `localAuthBucketMain` (`hk = hooksLocalBucketAuthMain`,
`onlyNewForged = false`) and `localAuthBucketForgedHdr` (`hk = hooksLocalBucketAuthForgedHdr`,
`onlyNewForged = true`). -/
@[expose] def implLocalBucketAuthGen [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec (LocalBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onlyNewForged : Bool) :
    QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (LocalBucketAuthEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec))) :=
  let cfg := bucketAuthCfg (M := M) Δcka tL
  let i₀ : QueryImpl unifSpec
      (StateT (LocalBucketAuthEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec))) :=
    fun n => StateT.lift (query (spec := unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) (.inl n))
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (LocalBucketAuthEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec))) :=
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
      (StateT (LocalBucketAuthEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec))) :=
    fun _ => pure none
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (LocalBucketAuthEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec))) :=
    fun x => do
      let (es0, winEp0) ← get
      let (out, es') ← StateT.lift ((deliverE hk maxSkip cfg x).run es0)
      set (es', winEp0)
      return out
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (LocalBucketAuthEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec))) :=
    fun x => do
      let (es0, winEp0) ← get
      let wasWin := es0.g.win
      let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg x).run es0)
      let isNewForged :=
        decide (x.2.1.1 = (es0.g.st x.1).tcur + 1) && !isHonestHdrLocalBucket es0.h x.2.1
      let winEp' :=
        if !wasWin && es'.g.win && (!onlyNewForged || isNewForged) then some x.2.1.1 else winEp0
      set (es', winEp')
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (StateT (LocalBucketAuthEState Γ T Sig SS RS M E K I)
        (OracleComp (unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec))) :=
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

/-- Unsplit post-PRNG local `canon`-bucket authenticity game (`ProbComp Bool`). -/
@[expose] def localAuthBucket [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool :=
  simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
    let (vs, h) ← (initLocalBucketAuth cka prng fs lam qep tL).run {}
    match vs with
    | none => return false
    | some (vA, vB) =>
      let g : Ctx Γ T Sig SS RS M E :=
        { st := fun P => match P with | .A => vA | .B => vB, b := false }
      let (_, es, winEp) ←
        (simulateQ (implLocalBucketAuthGen (hooksLocalBucketAuth cka prng fs Δcka qep tL)
          Δcka qep fs.maxSkip tL false) A).run ({ g, h }, none)
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

/-- Honest-header (`Main`) post-PRNG local `canon`-bucket game (`t = qep + 1, b = true` endpoint of
`redPRNGAuthBucketHybridMain`). -/
@[expose] def localAuthBucketMain [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool :=
  simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
    let (vs, h) ← (initLocalBucketAuth cka prng fs lam qep tL).run {}
    match vs with
    | none => return false
    | some (vA, vB) =>
      let g : Ctx Γ T Sig SS RS M E :=
        { st := fun P => match P with | .A => vA | .B => vB, b := false }
      let (_, es, winEp) ←
        (simulateQ (implLocalBucketAuthGen (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
          Δcka qep fs.maxSkip tL false) A).run ({ g, h }, none)
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

/-- Forged-header (`ForgedHdr`) post-PRNG local `canon`-bucket game (`t = qep + 1, b = true`
endpoint of `redPRNGAuthBucketHybridForgedHdr`). -/
@[expose] def localAuthBucketForgedHdr [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool :=
  simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
    let (vs, h) ← (initLocalBucketAuth cka prng fs lam qep tL).run {}
    match vs with
    | none => return false
    | some (vA, vB) =>
      let g : Ctx Γ T Sig SS RS M E :=
        { st := fun P => match P with | .A => vA | .B => vB, b := false }
      let (_, es, winEp) ←
        (simulateQ (implLocalBucketAuthGen (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
          Δcka qep fs.maxSkip tL true) A).run ({ g, h }, none)
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

/-- Unsplit sender-parity post-PRNG local `(tL, par)`-bucket game. -/
@[expose] def localAuthBucketPar [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool :=
  simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
    let (vs, h) ← (initLocalBucketAuth cka prng fs lam qep tL).run {}
    match vs with
    | none => return false
    | some (vA, vB) =>
      let g : Ctx Γ T Sig SS RS M E :=
        { st := fun P => match P with | .A => vA | .B => vB, b := false }
      let (_, es, winEp) ←
        (simulateQ (implLocalBucketAuthGen (hooksLocalBucketAuth cka prng fs Δcka qep tL)
          Δcka qep fs.maxSkip tL false) A).run ({ g, h }, none)
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g &&
          (decide (Party.senderOf tWin == .A) == par))

/-- Honest-header (`Main`, `gMain = true`) sender-parity post-PRNG local `(tL, par)`-bucket game. -/
@[expose] def localAuthBucketMainPar [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool :=
  simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
    let (vs, h) ← (initLocalBucketAuth cka prng fs lam qep tL).run {}
    match vs with
    | none => return false
    | some (vA, vB) =>
      let g : Ctx Γ T Sig SS RS M E :=
        { st := fun P => match P with | .A => vA | .B => vB, b := false }
      let (_, es, winEp) ←
        (simulateQ (implLocalBucketAuthGen (hooksLocalBucketAuthMain cka prng fs Δcka qep tL)
          Δcka qep fs.maxSkip tL false) A).run ({ g, h }, none)
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g &&
          (decide (Party.senderOf tWin == .A) == par))

/-- Forged-header (`ForgedHdr`, `gMain = false`) sender-parity post-PRNG local `(tL, par)`-bucket
game. -/
@[expose] def localAuthBucketForgedHdrPar [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool :=
  simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
    let (vs, h) ← (initLocalBucketAuth cka prng fs lam qep tL).run {}
    match vs with
    | none => return false
    | some (vA, vB) =>
      let g : Ctx Γ T Sig SS RS M E :=
        { st := fun P => match P with | .A => vA | .B => vB, b := false }
      let (_, es, winEp) ←
        (simulateQ (implLocalBucketAuthGen (hooksLocalBucketAuthForgedHdr cka prng fs Δcka qep tL)
          Δcka qep fs.maxSkip tL true) A).run ({ g, h }, none)
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g &&
          (decide (Party.senderOf tWin == .A) == par))

end ShallowBucketAuth

/-! ## 3. Costed `ReductionDsl` Programs: `redPRNGAuthBucketHybridProg` & `redFSAuthMultiBucketProg` -/

section CostedBucketAuth

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E

/-- Entry type `I × K` of `fTable` in `prngSig`. -/
@[expose, reducible] def pbaTableEntryTy : Ty S :=
  .prod (.base .i) (.base .k)

/-- Hook state type for `hooksPRNGBucketAuthC`: `cache × fTable × corrRoot` where
`corrRoot : .opt (.prod .nat (.base .sig))`. -/
@[expose, reducible] def prngBucketAuthHsTy : Ty S :=
  .prod (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    (.prod (.tbl (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
      (.opt (.prod .nat (.base .sig))))

/-- Engine state type `esTy prngVpTy prngBucketAuthHsTy`. -/
@[expose, reducible] def prngBucketAuthEsTy : Ty S :=
  esTy (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (@prngBucketAuthHsTy KC Γ CCoins T I KR RSt K SS RS M E)

/-- Reduction state type `(prngBucketAuthEsTy, Option ℕ)` recording `winEp`. -/
@[expose, reducible] def prngBucketAuthRedEsTy : Ty S :=
  .prod (@prngBucketAuthEsTy KC Γ CCoins T I KR RSt K SS RS M E) (.opt .nat)

/-- Coin-averaged Stage-2 reduction state type `(prngBucketAuthRedEsTy, Bool)` recording
`(es, winEp)` and `forgedMode` (`false = Main`, `true = ForgedHdr`). -/
@[expose, reducible] def prngBucketAuthStage2RedEsTy : Ty S :=
  .prod (@prngBucketAuthRedEsTy KC Γ CCoins T I KR RSt K SS RS M E) .bool

/-- Multi-session target interface into
`unifSpec + OracleSpec.sigma (fun _ : ℕ => FSAEAD.spec SS RS (Header T) M E)` over `prngSig`
(`rfl`-identical to `CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface`). -/
@[expose, reducible] def fsaeadMultiBucketIface
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    Iface S (unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) where
  fwdU n :=
    query (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ => _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E))
      (.inl n)
  uCost := 1
  Tag := FSHdrTag
  dom := fun g =>
    .prod .nat ((fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).dom g)
  cod := fun g =>
    (fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).cod g
  enc := fun
    | .tr, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl x))))⟩
    | .ch, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inl (.inl (.inr x))))⟩
    | .cs, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inl (.inr x)))⟩
    | .cr, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inr x))⟩
    | .dl, (sIdx, x) => .inr ⟨sIdx, .inl (.inr x)⟩
    | .ij, (sIdx, x) => .inr ⟨sIdx, .inr x⟩
  dec := fun
    | .tr, _, u => u
    | .ch, _, u => u
    | .cs, _, u => u
    | .cr, _, u => u
    | .dl, _, u => Option.map fsHdrRrEnc u
    | .ij, _, u => Option.map fsHdrRrEnc u
  qCost := fun _ => 1
  smp := prngSamplers sampKR sampKC sampCCoins sampI sampK

/-- Cache entry type `T × RSt × K × Option ℕ` for multi-session `hooksFSMultiBucketAuthC`. -/
@[expose, reducible] def fsMultiBucketCacheEntryTy : Ty S :=
  .prod (.base .t) (.prod (.base .sig) (.prod (.base .k) (.opt .nat)))

/-- In-transit record entry `ℕ × Header T × E` for multi-session `hooksFSMultiBucketAuthC`. -/
@[expose, reducible] def fsMultiBucketTransEntryTy : Ty S :=
  .prod .nat (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)

/-- Per-session bookkeeping `sCorr × fsCount × fsTrans` for multi-session `hooksFSMultiBucketAuthC`. -/
@[expose, reducible] def fsMultiBucketSessBookTy : Ty S :=
  .prod .bool (.prod .nat (.list (@fsMultiBucketTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))

/-- Hook state type `cache × tableTbl × sessionsTbl × book × lfWin` for `hooksFSMultiBucketAuthC`. -/
@[expose, reducible] def fsMultiBucketHsTy : Ty S :=
  .prod (.tbl (.opt (@fsMultiBucketCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (.prod (.tbl (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
      (.prod (.tbl (.list (.base .i)))
        (.prod (.tbl (.opt (@fsMultiBucketSessBookTy KC Γ CCoins T I KR RSt K SS RS M E))) .bool)))

/-- Virtual party state type (`ssV = SS ⊕ ℕ`, `rsV = RS ⊕ ℕ`) for `hooksFSMultiBucketAuthC`. -/
@[expose, reducible] def fsMultiBucketVpTy : Ty S :=
  @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat)

/-- Reduction state type `(esTy fsMultiBucketVpTy fsMultiBucketHsTy, Option ℕ)` for `redFSAuthMultiBucketProg`. -/
@[expose, reducible] def fsMultiBucketRedEsTy : Ty S :=
  .prod (esTy (@fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (@fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)) (.opt .nat)

/-- Encode `PRNGBucketAuthState T RSt K I` into `prngBucketAuthHsTy.denote`. -/
@[expose] def prngBucketAuthHsEnc (h : PRNGBucketAuthState T RSt K I) :
    (@prngBucketAuthHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (h.cache, (h.fTable, h.corrRoot))

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "IIM" =>
  @fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaHsTy" => @prngBucketAuthHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaVpTy" => @prngVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaEsTy" => @prngBucketAuthEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaRedEsTy" => @prngBucketAuthRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaStage2RedEsTy" => @prngBucketAuthStage2RedEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" => @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => @fsMultiBucketSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "transEntryTy" => @fsMultiBucketTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E

/-- `postLeak` expression in `ReductionDsl`: `O(1)` check on `cGsTL ctxE`. -/
@[expose] def postLeakBucketE {O : Ops S} {vpT : Ty S} {Γ'} (tL : Option ℕ)
    (ctxE : Expr O Γ' (cGsTy vpT)) : Expr O Γ' .bool :=
  rdslExpr =>
    match cGsTL ctxE with
    | none => false
    | some cur => ltOptE (optNatLit (raw tL)) cur

@[expose] def pbaHsCache {O : Ops S} {Γ'} (h : Expr O Γ' pbaHsTy) :
    Expr O Γ' (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E) := .fst h

@[expose] def pbaHsFTbl {O : Ops S} {Γ'} (h : Expr O Γ' pbaHsTy) :
    Expr O Γ' (.tbl (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) := .fst (.snd h)

@[expose] def pbaHsCorrRoot {O : Ops S} {Γ'} (h : Expr O Γ' pbaHsTy) :
    Expr O Γ' (.opt (.prod .nat (.base .sig))) := .snd (.snd h)

@[expose] def pbaHsEmptyE {O : Ops S} {Γ'} : Expr O Γ' pbaHsTy :=
  .pair (.tconst .none) (.pair (.tconst .nil) .none)

@[expose] def pbaHsSetCache {O : Ops S} {Γ'} (h : Expr O Γ' pbaHsTy)
    (c : Expr O Γ' (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)) : Expr O Γ' pbaHsTy :=
  .pair c (.snd h)

@[expose] def pbaHsSetFTblAt {O : Ops S} {Γ'} (h : Expr O Γ' pbaHsTy)
    (t0 : Expr O Γ' .nat)
    (tb : Expr O Γ' (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    Expr O Γ' pbaHsTy :=
  .pair (pbaHsCache h) (.pair (.tset (pbaHsFTbl h) t0 tb) (pbaHsCorrRoot h))

@[expose] def pbaHsSetCorrRoot {O : Ops S} {Γ'} (h : Expr O Γ' pbaHsTy)
    (cr : Expr O Γ' (.opt (.prod .nat (.base .sig)))) : Expr O Γ' pbaHsTy :=
  .pair (pbaHsCache h) (.pair (pbaHsFTbl h) cr)

/-- Costed `resolveCorrRoot`: resolves `σvE` at epoch `epE` via `pbaHsCorrRoot hE`. -/
@[expose] def resolveCorrRootE {O : Ops S} {Γ'}
    (hE : Expr O Γ' pbaHsTy) (epE : Expr O Γ' .nat) (σvE : Expr O Γ' (.opt (.base .sig))) :
    Expr O Γ' (.opt (.base .sig)) :=
  rdslExpr =>
    letE (hE, epE, σvE) fun (h0, ep0, σv0) =>
      match σv0 with
      | some σ => some σ
      | none =>
        match pbaHsCorrRoot h0 with
        | none => none
        | some (eC, σC) => if ep0 == eC then some σC else none

/-- Bounded association-list lookup `tbl.lookup Ik` on `List (I × K)`. -/
@[expose] def pbaTableLookupE (L : ℕ) {Γ'}
    (tblE : Expr OO Γ' (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' (.opt (.base .k)) :=
  rdslExpr =>
    letE (tblE, ikE) fun (tbl0, ik0) =>
      foldrB L tbl0 none fun (ikEntry, kEntry) acc =>
        if Expr.op (O := OO) CKAOp.eqI (ik0, ikEntry) then some kEntry else acc

/-- Costed `lookupPRNGBucketAuthF` bounded by association-list cap `L`. -/
@[expose] def lookupPRNGBucketAuthFC (L : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) :
    Comp OO II Γ' (.prod (.base .k) pbaHsTy) :=
  rdsl do
    (h0, t0, ik0) ← return (hE, tE, ikE)
    let tb0 := tget (pbaHsFTbl h0) t0
    match pbaTableLookupE L tb0 ik0 with
    | some k => return (k, h0)
    | none =>
      k ← sample (O := OO) (I := II) CKASamp.k ()
      return (k, pbaHsSetFTblAt h0 t0 ((ik0, k) :: tb0))

/-- Costed `rootPRNGBucketAuthHybrid`. -/
@[expose] def rootPRNGBucketAuthHybridC (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (tE : Expr OO Γ' .nat)
    (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i))
    (σvE : Expr OO Γ' (.opt (.base .sig))) :
    Comp OO II Γ' (.prod (.opt (.prod (.opt (.base .sig)) (.base .k))) pbaHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, t0, pl0, ik0, σv0) ← return (hE, tE, plE, ikE, σvE)
    let σv := resolveCorrRootE h0 (t0 - 1) σv0
    if nat t < t0 then
      match σv with
      | none => return (none, h0)
      | some σ =>
        let p := Expr.op (O := OO) CKAOp.prngUp (σ, ik0)
        return (some (some p.1, p.2), h0)
    else if orE pl0 (isSomeE (pbaHsCorrRoot h0)) then
      match σv with
      | some σ =>
        let p := Expr.op (O := OO) CKAOp.prngUp (σ, ik0)
        return (some (some p.1, p.2), h0)
      | none =>
        σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
        match σOpt with
        | none => return (none, h0)
        | some σOut =>
          let h1 := pbaHsSetCorrRoot h0 (some (t0 - 1, σOut))
          let p := Expr.op (O := OO) CKAOp.prngUp (σOut, ik0)
          return (some (some p.1, p.2), h1)
    else if t0 == nat t then
      if bool tL.isSome && (t0 == nat tH) then
        kOpt ← query (O := OO) (I := II) PRNGTag.challPrng none
        match kOpt with
        | none => return (none, h0)
        | some kOut =>
          σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
          match σOpt with
          | none => return (none, h0)
          | some σOut => return (some (some σOut, kOut), h0)
      else
        skOpt ← query (O := OO) (I := II) PRNGTag.challPrf ik0
        match skOpt with
        | none => return (none, h0)
        | some (σOut, kOut) => return (some (some σOut, kOut), h0)
    else if !(t0 < nat tH) then
      if bool tL.isSome && (t0 == nat tH) then
        pOpt ← query (O := OO) (I := II) PRNGTag.process none
        match pOpt with
        | none => return (none, h0)
        | some _ =>
          kRand ← sample (O := OO) (I := II) CKASamp.k ()
          return (some (none, kRand), h0)
      else
        pOpt ← query (O := OO) (I := II) PRNGTag.process (some ik0)
        match pOpt with
        | none => return (none, h0)
        | some _ =>
          (kRand, h1) ← lookupPRNGBucketAuthFC L h0 t0 ik0
          return (some (none, kRand), h1)
    else
      pOpt ← query (O := OO) (I := II) PRNGTag.process (some ik0)
      match pOpt with
      | none => return (none, h0)
      | some kOut =>
        σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
        match σOpt with
        | none => return (none, h0)
        | some σOut => return (some (some σOut, kOut), h0)

/-- Costed `startSend` for `hooksPRNGBucketAuthC`. -/
@[expose] def prngBucketAuthStartSendC (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig)))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO II Γ'
      (.prod (.opt (.prod (.base .γ)
        (.prod (.base .t) (.prod (.opt (.base .sig)) (.base .ss)))))
        pbaHsTy) :=
  rdsl do
    (h0, ctx0, t0, γ0, σv0, r0) ← return (hE, ctxE, tE, γE, σvE, rE)
    let pl0 := postLeakBucketE (raw tL) ctx0
    coins ←
      match r0 with
      | none => sample (O := OO) (I := II) CKASamp.ccoins ()
      | some c => return c
    let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ0, coins)
    (stepOpt, h1) ← rootPRNGBucketAuthHybridC L tL t h0 t0 pl0 cOut.2.2 σv0
    match stepOpt with
    | none => return (none, h1)
    | some (σ', kVal) =>
      let tMsg := cOut.2.1
      let cache' := tset (pbaHsCache h1) t0 (some (tMsg, σ', kVal))
      let h2 := pbaHsSetCache h1 cache'
      let ss := Expr.op (O := OO) CKAOp.fsInitSender kVal
      return (some (cOut.1, tMsg, σ', ss), h2)

/-- Costed `startRecv` for `hooksPRNGBucketAuthC`. -/
@[expose] def prngBucketAuthStartRecvC (L Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .rs)))))
        pbaHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, t0, γ0, σv0, tn0) ← return (hE, ctxE, tE, γE, σvE, tnE)
    let pl0 := postLeakBucketE (raw tL) ctx0
    let honest :=
      match tget (pbaHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if !(nat (qep + 1) < t0) && validGuessE (raw (2 + Δcka)) (optNatLit (raw tL)) t0 then
        if bool tL.isSome && (t0 == nat tH) then
          return (none, h0)
        else if orE pl0 (orE (isSomeE (pbaHsCorrRoot h0)) (nat t < t0)) then
          match resolveCorrRootE h0 (t0 - 1) σv0 with
          | none => return (none, h0)
          | some σ =>
            let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
            let p := Expr.op (O := OO) CKAOp.prngUp (σ, kk.2)
            let rs := Expr.op (O := OO) CKAOp.fsInitReceiver p.2
            return (some (some (kk.1, some p.1, rs)), h0)
        else if t0 == nat t then
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          skOpt ← query (O := OO) (I := II) PRNGTag.challPrf kk.2
          match skOpt with
          | none => return (none, h0)
          | some (σOut, kOut) =>
            let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kOut
            return (some (some (kk.1, some σOut, rs)), h0)
        else if !(t0 < nat tH) then
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          (kOut, h1) ← lookupPRNGBucketAuthFC L h0 t0 kk.2
          let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kOut
          return (some (some (kk.1, none, rs)), h1)
        else
          return (some none, h0)
      else
        return (some none, h0)
    | some (σc, kVal) =>
      let σc' := resolveCorrRootE h0 t0 σc
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kVal
      return (some (some (γ', σc', rs)), h0)

@[expose] def prngBucketAuthFsSendC {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss))
    (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (_pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO II Γ' (.prod (.opt (.prod (.base .ss) (.base .ct))) pbaHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) CKAOp.fsSend (ssE, hdrE, mE)), hE)

@[expose] def prngBucketAuthFsRecvC (B : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (_recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .rs) (.prod .nat (.base .msg))))) pbaHsTy) :=
  rdsl do
    return (some (Expr.op (O := OO) (CKAOp.fsReceive B) (rsE, hdrE, eE)), hE)

@[expose] def prngBucketAuthCommitC {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (_oldE newE : Expr OO Γ' pbaVpTy) :
    Comp OO II Γ' (.prod (.opt pbaVpTy) pbaHsTy) :=
  rdsl do
    return (some newE, hE)

/-- Costed `reveal` for `hooksPRNGBucketAuthC`: resolves `vpRoot` via `corrRoot`, or queries
`PRNGTag.corr ()` (`1` query) when `vpRoot = none` at `e = eMax ≥ healEpoch tL` before `postLeak`. -/
@[expose] def prngBucketAuthRevealC (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' pbaVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) pbaHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, vp0) ← return (hE, ctxE, vpE)
    let e := vpTcurNat vp0
    let epAB := cGsEpoch ctx0
    let eMax := maxN epAB.1 epAB.2
    let pl0 := postLeakBucketE (raw tL) ctx0
    match resolveCorrRootE h0 e (vpRoot vp0) with
    | some σ =>
      let h1 :=
        if !(e < nat tH) && !(isSomeE (pbaHsCorrRoot h0)) then
          pbaHsSetCorrRoot h0 (some (e, σ))
        else h0
      return (some (realPartyE vp0 (vpΓ vp0) σ (vpVS vp0) (vpVR vp0)), h1)
    | none =>
      if !pl0 && !(isSomeE (pbaHsCorrRoot h0)) && !(e < nat tH) && (e == eMax) then
        σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
        match σOpt with
        | none => return (none, h0)
        | some σOut =>
          let h1 := pbaHsSetCorrRoot h0 (some (e, σOut))
          return (some (realPartyE vp0 (vpΓ vp0) σOut (vpVS vp0) (vpVR vp0)), h1)
      else
        return (none, h0)

/-- Costed `HooksC` bundle for `redPRNGAuthBucketHybridProg` (base / `ForgedHdr` `startRecv` + `Main` `reveal`). -/
@[expose] def hooksPRNGBucketAuthC (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) pbaHsTy where
  startSend := prngBucketAuthStartSendC L tL t
  startRecv := prngBucketAuthStartRecvC L Δcka qep tL t
  fsSend := prngBucketAuthFsSendC
  fsRecv := prngBucketAuthFsRecvC B
  commit := prngBucketAuthCommitC
  reveal := prngBucketAuthRevealC tL

/-- Costed check whether `hdrE` matches the honest sender's cached CKA header in `pbaHsCache hE`. -/
@[expose] def isHonestHdrPRNGBucketE {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (hdrE : Expr OO Γ' hdrTy) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (hE, hdrE) fun (h0, hdr0) =>
      match hdr0.2 with
      | none => false
      | some tn0 =>
        match tget (pbaHsCache h0) hdr0.1 with
        | none => false
        | some (tCached, _) => Expr.op (O := OO) CKAOp.eqT (tCached, tn0)

/-- Costed `Main`-mode `startRecv`: accepts cached honest CKA headers (`0` target queries) and
rejects forged CKA headers (aborting at `tL.isSome && t0 == healEpoch tL` when admissible). -/
@[expose] def prngBucketAuthMainStartRecvC (Δcka qep : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (_ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (_σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .rs)))))
        pbaHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, t0, γ0, tn0) ← return (hE, tE, γE, tnE)
    let honest :=
      match tget (pbaHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if !(nat (qep + 1) < t0) && validGuessE (raw (2 + Δcka)) (optNatLit (raw tL)) t0 &&
          (bool tL.isSome && (t0 == nat tH)) then
        return (none, h0)
      else
        return (some none, h0)
    | some (σc, kVal) =>
      let σc' := resolveCorrRootE h0 t0 σc
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kVal
      return (some (some (γ', σc', rs)), h0)

/-- Costed `ForgedHdr`-mode `reveal` (`0` target queries): aborts whenever `!(vp.tcur < healEpoch tL)`
or `!(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)`. -/
@[expose] def prngBucketAuthForgedHdrRevealC (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (_pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' pbaVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) pbaHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, vp0) ← return (hE, ctxE, vpE)
    let e := vpTcurNat vp0
    let epAB := cGsEpoch ctx0
    let eMax := maxN epAB.1 epAB.2
    if orE (!(e < nat tH)) (!(eMax < nat tH)) then
      return (none, h0)
    else
      match vpRoot vp0 with
      | some σ => return (some (realPartyE vp0 (vpΓ vp0) σ (vpVS vp0) (vpVR vp0)), h0)
      | none => return (none, h0)

/-- Costed `HooksC` bundle for `Main` mode (`forgedMode = false`). -/
@[expose] def hooksPRNGBucketAuthMainC (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) pbaHsTy :=
  { hooksPRNGBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep tL t with
    startRecv := prngBucketAuthMainStartRecvC Δcka qep tL }

/-- Costed `HooksC` bundle for `ForgedHdr` mode (`forgedMode = true`). -/
@[expose] def hooksPRNGBucketAuthForgedHdrC (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) pbaHsTy :=
  { hooksPRNGBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep tL t with
    reveal := prngBucketAuthForgedHdrRevealC tL }

/-- Costed initial `EState` construction for `redPRNGAuthBucketHybridProg`. -/
@[expose] def initPRNGBucketAuthEStateC (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (bE : Expr OO Γ' .bool) : Comp OO II Γ' pbaEsTy :=
  rdsl do
    b0 ← return bE
    kc ← sample (O := OO) (I := II) CKASamp.kc ()
    (stepOpt, h1) ← rootPRNGBucketAuthHybridC L tL t pbaHsEmptyE 0 false
      (Expr.op (O := OO) CKAOp.lamI ()) none
    match stepOpt with
    | none =>
      let parties :=
        abortedPartiesE
          (Expr.op (O := OO) CKAOp.ckaInitA kc)
          (Expr.op (O := OO) CKAOp.ckaInitB kc)
      let g0 := cGsInitE parties.1 parties.2 b0
      return (esMk g0 h1 true)
    | some (σv, kVal) =>
      let parties :=
        mkPartiesE
          (Expr.op (O := OO) CKAOp.ckaInitA kc)
          (Expr.op (O := OO) CKAOp.ckaInitB kc) σv
          (Expr.op (O := OO) CKAOp.fsInitSender kVal)
          (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
      let g0 := cGsInitE parties.1 parties.2 b0
      return (esMk g0 h1 false)

/-- Costed Stage-2 `canon`-bucket ascending `t`-hybrid `redPRNGAuthBucketHybrid` program
over `SM.spec`, `prngOps`, `prngIface`, and `prngSMCodec` (`fig8RedsInst.redPRNGAuth`),
coin-averaging `Main` (`forgedMode = false`) and `ForgedHdr` (`forgedMode = true`) via `CKASamp.bit`. -/
@[expose] def redPRNGAuthBucketHybridProg (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := pbaStage2RedEsTy
  init := rdsl [_] do
    forgedMode ← sample (O := OO) (I := II) CKASamp.bit ()
    es ← initPRNGBucketAuthEStateC L tL t false
    return ((), ((es, none), forgedMode))
  handle := rdsl [st, q] do
    (es0, winEp0, forgedMode, q0) ← return (st.1.1, st.1.2, st.2, q)
    if forgedMode then
      match q0 with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (.inl (.inl (.inl none))), ((es0, winEp0), forgedMode))
        else
          match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (.inl (.inl (.inl none))), ((es0, winEp0), forgedMode))
          | some s1 =>
            (res, h') ← vSendC (raw (hooksPRNGBucketAuthForgedHdrC L B Δcka qep tL t))
              (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (.inl (.inl (.inl none))), ((esMk (esG es0) h' true, winEp0), forgedMode))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
              return (.inl (.inl (.inl (.inl (some ct)))),
                ((esMk g' h' (esAbort es0), winEp0), forgedMode))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (.inl (.inl (.inr none))), ((es0, winEp0), forgedMode))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC (raw (hooksPRNGBucketAuthForgedHdrC L B Δcka qep tL t))
          L maxSkip (raw (bucketAuthCfgEC Δcka tL)) es0 x
        return (.inl (.inl (.inr out)), ((es', winEp0), forgedMode))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        let isNewForged :=
          (x.2.1.1 == vpTcurNat (pGet (cGsSt (esG es0)) x.1) + 1) &&
            !(isHonestHdrPRNGBucketE (esH es0) x.2.1)
        (out, es') ← injectEC (raw (hooksPRNGBucketAuthForgedHdrC L B Δcka qep tL t))
          L (raw (2 + Δcka)) qep (raw (bucketAuthCfgEC Δcka tL)) es0 x
        let winEp' := if !wasWin && cGsWin (esG es') && isNewForged then some x.2.1.1 else winEp0
        return (.inl (.inr out), ((es', winEp'), forgedMode))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0))) then
          return (.inr none, ((es0, winEp0), forgedMode))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← prngBucketAuthForgedHdrRevealC tL (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inr none, ((esMk s0 h' true, winEp0), forgedMode))
          | some stOut =>
            return (.inr (some stOut), ((esMk s1 h' (esAbort es0), winEp0), forgedMode))
    else
      match q0 with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (.inl (.inl (.inl none))), ((es0, winEp0), forgedMode))
        else
          match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (.inl (.inl (.inl none))), ((es0, winEp0), forgedMode))
          | some s1 =>
            (res, h') ← vSendC (raw (hooksPRNGBucketAuthMainC L B Δcka qep tL t))
              (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (.inl (.inl (.inl none))), ((esMk (esG es0) h' true, winEp0), forgedMode))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
              return (.inl (.inl (.inl (.inl (some ct)))),
                ((esMk g' h' (esAbort es0), winEp0), forgedMode))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (.inl (.inl (.inr none))), ((es0, winEp0), forgedMode))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC (raw (hooksPRNGBucketAuthMainC L B Δcka qep tL t))
          L maxSkip (raw (bucketAuthCfgEC Δcka tL)) es0 x
        return (.inl (.inl (.inr out)), ((es', winEp0), forgedMode))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        (out, es') ← injectEC (raw (hooksPRNGBucketAuthMainC L B Δcka qep tL t))
          L (raw (2 + Δcka)) qep (raw (bucketAuthCfgEC Δcka tL)) es0 x
        let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
        return (.inl (.inr out), ((es', winEp'), forgedMode))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0))) then
          return (.inr none, ((es0, winEp0), forgedMode))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← prngBucketAuthRevealC tL (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inr none, ((esMk s0 h' true, winEp0), forgedMode))
          | some stOut =>
            return (.inr (some stOut), ((esMk s1 h' (esAbort es0), winEp0), forgedMode))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1.1, st.1.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      return ((!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0))

/-! ### Costed Multi-Session `FSAEAD` `canon`-Bucket Reduction (`redFSAuthMultiBucketProg`) -/

@[expose] def mbHsCache {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy) :
    Expr O Γ' (.tbl (.opt (@fsMultiBucketCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :=
  .fst h

@[expose] def mbHsTableTbl {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy) :
    Expr O Γ' (.tbl (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :=
  .fst (.snd h)

@[expose] def mbHsSessionsTbl {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy) :
    Expr O Γ' (.tbl (.list (.base .i))) :=
  .fst (.snd (.snd h))

@[expose] def mbHsBook {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy) :
    Expr O Γ' (.tbl (.opt mBookTy)) :=
  .fst (.snd (.snd (.snd h)))

@[expose] def mbHsLfWin {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy) :
    Expr O Γ' .bool :=
  .snd (.snd (.snd (.snd h)))

@[expose] def mbHsMk {O : Ops S} {Γ'}
    (ca : Expr O Γ' (.tbl (.opt (@fsMultiBucketCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))))
    (tb : Expr O Γ' (.tbl (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))))
    (se : Expr O Γ' (.tbl (.list (.base .i))))
    (bk : Expr O Γ' (.tbl (.opt mBookTy)))
    (lw : Expr O Γ' .bool) : Expr O Γ' mbHsTy :=
  .pair ca (.pair tb (.pair se (.pair bk lw)))

@[expose] def mbHsSetCache {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy)
    (ca : Expr O Γ' (.tbl (.opt (@fsMultiBucketCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    Expr O Γ' mbHsTy :=
  mbHsMk ca (mbHsTableTbl h) (mbHsSessionsTbl h) (mbHsBook h) (mbHsLfWin h)

@[expose] def mbHsSetTableAt {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy)
    (t0 : Expr O Γ' .nat)
    (tb : Expr O Γ' (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    Expr O Γ' mbHsTy :=
  mbHsMk (mbHsCache h) (.tset (mbHsTableTbl h) t0 tb)
    (mbHsSessionsTbl h) (mbHsBook h) (mbHsLfWin h)

@[expose] def mbHsSetSessionsAt {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy)
    (t0 : Expr O Γ' .nat)
    (se : Expr O Γ' (.list (.base .i))) : Expr O Γ' mbHsTy :=
  mbHsMk (mbHsCache h) (mbHsTableTbl h) (.tset (mbHsSessionsTbl h) t0 se) (mbHsBook h) (mbHsLfWin h)

@[expose] def mbHsSetBookAt {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy)
    (sIdx : Expr O Γ' .nat) (entry : Expr O Γ' mBookTy) : Expr O Γ' mbHsTy :=
  mbHsMk (mbHsCache h) (mbHsTableTbl h) (mbHsSessionsTbl h)
    (.tset (mbHsBook h) sIdx (.some entry)) (mbHsLfWin h)

@[expose] def mbHsGetBookAt {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy)
    (sIdx : Expr O Γ' .nat) : Expr O Γ' mBookTy :=
  rdslExpr =>
    match tget (mbHsBook h) sIdx with
    | none => (false, (0, []))
    | some b => b

@[expose] def mbHsSetLfWin {O : Ops S} {Γ'} (h : Expr O Γ' mbHsTy) (lw : Expr O Γ' .bool) :
    Expr O Γ' mbHsTy :=
  mbHsMk (mbHsCache h) (mbHsTableTbl h) (mbHsSessionsTbl h) (mbHsBook h) lw

@[expose] def mbHsEmptyE {O : Ops S} {Γ'} : Expr O Γ' mbHsTy :=
  mbHsMk (.tconst .none) (.tconst .nil) (.tconst .nil) (.tconst .none) (.bool false)

/-- Lazy per-epoch random-table lookup on `mbHsTy` bounded by association-list cap `L`. -/
@[expose] def lookupMultiBucketFC (L : ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) :
    Comp OO IIM Γ' (.prod (.base .k) mbHsTy) :=
  rdsl do
    (h0, t0, ik0) ← return (hE, tE, ikE)
    let tb0 := tget (mbHsTableTbl h0) t0
    match pbaTableLookupE L tb0 ik0 with
    | none =>
      kNew ← sample (O := OO) (I := IIM) CKASamp.k ()
      return (kNew, mbHsSetTableAt h0 t0 ((ik0, kNew) :: tb0))
    | some kFound =>
      return (kFound, h0)

@[expose] def sessionsMemBucketE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i)))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' .bool :=
  rdslExpr =>
    letE (sesE, ikE) fun (ses0, ik0) =>
      foldrB L ses0 false fun x acc =>
        orE (Expr.op (O := OO) CKAOp.eqI (x, ik0)) acc

@[expose] def sessionsIdxOfBucketE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i)))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' .nat :=
  rdslExpr =>
    letE (sesE, ikE) fun (ses0, ik0) =>
      foldrB L ses0 0 fun x acc =>
        if Expr.op (O := OO) CKAOp.eqI (x, ik0) then 0 else acc + 1

@[expose] def sessionsLenBucketE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i))) :
    Expr OO Γ' .nat :=
  rdslExpr =>
    foldrB L sesE 0 fun _ acc => acc + 1

@[expose] def sessionsAppendOneBucketE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i)))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' (.list (.base .i)) :=
  rdslExpr =>
    foldrB L sesE [ikE] fun x acc => x :: acc

/-- Registers session `ikE` at epoch `tE` under stride `L` (`L = q + 1`, giving external session
index `sIdx = L * (t0 - healEpoch tL) + localIdx + off` where `off = 0` for `gMain = true` (`j = 0`)
and `off = 1` for `gMain = false` (`1 ≤ j ≤ q < L`)). -/
@[expose] def regSessMultiBucketE (L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' (.prod .nat mbHsTy) :=
  let tH : ℕ := healEpoch tL
  let off : ℕ := if gMain then 0 else 1
  rdslExpr =>
    letE (hE, tE, ikE) fun (h0, t0, ik0) =>
      let ses0 := tget (mbHsSessionsTbl h0) t0
      if sessionsMemBucketE L ses0 ik0 then
        (L * (t0 - nat tH) + sessionsIdxOfBucketE L ses0 ik0 + nat off, h0)
      else
        (L * (t0 - nat tH) + sessionsLenBucketE L ses0 + nat off,
          mbHsSetSessionsAt h0 t0 (sessionsAppendOneBucketE L ses0 ik0))

@[expose] def regSessOptMultiBucketE (L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat)
    (sidE : Expr OO Γ' (.opt (.base .i))) :
    Expr OO Γ' (.prod (.opt .nat) mbHsTy) :=
  rdslExpr =>
    letE (hE, tE, sidE) fun (h0, t0, sid0) =>
      match sid0 with
      | none => (none, h0)
      | some ik =>
        let p := regSessMultiBucketE L (raw gMain) (raw tL) h0 t0 ik
        (some p.1, p.2)

/-- Epoch admissibility predicate for `(tL, par)`-bucket authenticity in standard `SM`:
`validGuessE (2 + Δcka) tL t0` and sender parity `(Party.senderOf t0 == .A) == par`. -/
@[expose] def validGuessBucketParAuthE {O : Ops S} (Δcka : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (tE : Expr O Γ' .nat) : Expr O Γ' .bool :=
  rdslExpr =>
    validGuessE (raw (2 + Δcka)) (optNatLit (raw tL)) tE &&
      (if bool par then !(senderOfE tE) else senderOfE tE)

/-- Root-RNG step of `redFSAuthMultiBucketProg`: mirrors `rootLocalBucketAuth` and returns
`(σ', kVal, sid)` where `sid = some _` iff `!pl0 && t0 ≤ qep + 1` and `t0` is admissible for
`(tL, par)`. -/
@[expose] def rootFSMultiBucketAuthC (L Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (tE : Expr OO Γ' .nat)
    (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i))
    (σE : Expr OO Γ' (.base .sig)) :
    Comp OO IIM Γ'
      (.prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, t0, pl0, ik0, σ0) ← return (hE, tE, plE, ikE, σE)
    let pIk := Expr.op (O := OO) CKAOp.prngUp (σ0, ik0)
    if orE pl0 (nat (qep + 1) < t0) then
      return ((pIk.1, pIk.2, none), h0)
    else if validGuessBucketParAuthE Δcka (raw tL) (raw par) t0 then
      if bool tL.isSome && (t0 == nat tH) then
        ir ← sample (O := OO) (I := IIM) CKASamp.i ()
        kSample ← sample (O := OO) (I := IIM) CKASamp.k ()
        let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
        return ((pIr.1, kSample, some ir), h0)
      else
        (kLookup, h1) ← lookupMultiBucketFC L h0 t0 ik0
        return ((pIk.1, kLookup, some ik0), h1)
    else if bool tL.isSome && (t0 == nat tH) then
      ir ← sample (O := OO) (I := IIM) CKASamp.i ()
      kSample ← sample (O := OO) (I := IIM) CKASamp.k ()
      let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
      return ((pIr.1, kSample, none), h0)
    else if !(t0 < nat tH) then
      (kLookup, h1) ← lookupMultiBucketFC L h0 t0 ik0
      return ((pIk.1, kLookup, none), h1)
    else
      return ((pIk.1, pIk.2, none), h0)

/-- Costed `startSend` for `hooksFSMultiBucketAuthC`: registers honest epochs `t0` of parity `par`
at `sIdx := L * (t0 - healEpoch tL) + 0` (`gMain = true`, `j = 0`) or
`sIdx := L * (t0 - healEpoch tL) + (localIdx + 1)` (`gMain = false`, `1 ≤ j ≤ q`) while
`!postLeak`, keeping opposite-parity and post-leak epochs local (`.inl`). -/
@[expose] def fsMultiBucketAuthStartSendC (L Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO IIM Γ'
      (.prod (.opt (.prod (.base .γ)
        (.prod (.base .t) (.prod (.base .sig) (.sum (.base .ss) .nat)))))
        mbHsTy) :=
  rdsl do
    (h0, ctx0, t0, γ0, σ0, r0) ← return (hE, ctxE, tE, γE, σE, rE)
    let pl0 := postLeakBucketE (raw tL) ctx0
    coins ←
      match r0 with
      | none => sample (O := OO) (I := IIM) CKASamp.ccoins ()
      | some c => return c
    let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ0, coins)
    ((σ', kVal, sid), h1) ← rootFSMultiBucketAuthC L Δcka qep tL par h0 t0 pl0 cOut.2.2 σ0
    let regP := regSessOptMultiBucketE L (raw gMain) (raw tL) h1 t0 sid
    let optIdx := regP.1
    let h2 := regP.2
    let tMsg := cOut.2.1
    let cache' := tset (mbHsCache h2) t0 (some (tMsg, σ', kVal, optIdx))
    let h3 := mbHsSetCache h2 cache'
    let ssv : Expr OO _ (.sum (.base .ss) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitSender kVal)
      | some sIdx => .inr sIdx
    return (some (cOut.1, tMsg, σ', ssv), h3)

/-- Costed check whether `hdrE` matches the honest sender's cached CKA header in `mbHsCache hE`. -/
@[expose] def isHonestHdrMultiBucketE {Γ'}
    (hE : Expr OO Γ' mbHsTy) (hdrE : Expr OO Γ' hdrTy) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (hE, hdrE) fun (h0, hdr0) =>
      match hdr0.2 with
      | none => false
      | some tn0 =>
        match tget (mbHsCache h0) hdr0.1 with
        | none => false
        | some (tCached, _) => Expr.op (O := OO) CKAOp.eqT (tCached, tn0)

/-- Costed `startRecv` for `hooksFSMultiBucketAuthC`: in `Main` (`gMain = true`) rejects forged CKA
headers (`0` queries); in `ForgedHdr` (`gMain = false`) registers forged CKA headers in parity-`par`
epochs at `sIdx := L * (t0 - healEpoch tL) + (localIdx + 1)` (`1 ≤ localIdx + 1 ≤ q < L`) when
`!postLeak`, while simulating opposite-parity and post-leak epochs locally (`.inl`). -/
@[expose] def fsMultiBucketAuthStartRecvC (L Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.base .sig) (.sum (.base .rs) .nat)))))
        mbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, t0, γ0, σ0, tn0) ← return (hE, ctxE, tE, γE, σE, tnE)
    let pl0 := postLeakBucketE (raw tL) ctx0
    let honest :=
      match tget (mbHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if bool gMain then
        if !(nat (qep + 1) < t0) && validGuessE (raw (2 + Δcka)) (optNatLit (raw tL)) t0 &&
            (bool tL.isSome && (t0 == nat tH)) then
          return (none, h0)
        else
          return (some none, h0)
      else if !(nat (qep + 1) < t0) && validGuessE (raw (2 + Δcka)) (optNatLit (raw tL)) t0 then
        if bool tL.isSome && (t0 == nat tH) then
          return (none, h0)
        else if pl0 then
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          let p := Expr.op (O := OO) CKAOp.prngUp (σ0, kk.2)
          let rs := Expr.op (O := OO) CKAOp.fsInitReceiver p.2
          return (some (some (kk.1, p.1, .inl rs)), h0)
        else if validGuessBucketParAuthE Δcka (raw tL) (raw par) t0 then
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          (_k', h1) ← lookupMultiBucketFC L h0 t0 kk.2
          let regP := regSessMultiBucketE L (raw false) (raw tL) h1 t0 kk.2
          let sIdx := regP.1
          let h2 := regP.2
          let σ' := (Expr.op (O := OO) CKAOp.prngUp (σ0, kk.2)).1
          return (some (some (kk.1, σ', .inr sIdx)), h2)
        else if !(t0 < nat tH) then
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          (k', h1) ← lookupMultiBucketFC L h0 t0 kk.2
          let σ' := (Expr.op (O := OO) CKAOp.prngUp (σ0, kk.2)).1
          let rs := Expr.op (O := OO) CKAOp.fsInitReceiver k'
          return (some (some (kk.1, σ', .inl rs)), h1)
        else
          return (some none, h0)
      else
        return (some none, h0)
    | some (σc, kVal, optIdx) =>
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rsv : Expr OO _ (.sum (.base .rs) .nat) :=
        match optIdx with
        | none => .inl (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
        | some sIdx => .inr sIdx
      return (some (some (γ', σc, rsv)), h0)

@[expose] def fsTransFindBucketE (L : ℕ) {Γ'}
    (trE : Expr OO Γ' (.list transEntryTy))
    (hcE : Expr OO Γ' hdrCtTy) :
    Expr OO Γ' (.opt transEntryTy) :=
  rdslExpr =>
    letE (trE, hcE) fun (tr0, hc0) =>
      findB L tr0 fun x => hdrCtEqE x.2 hc0

@[expose] def fsTransFilterBucketE (L : ℕ) {Γ'}
    (trE : Expr OO Γ' (.list transEntryTy))
    (dropE : Expr OO Γ' .nat) :
    Expr OO Γ' (.list transEntryTy) :=
  rdslExpr =>
    letE (trE, dropE) fun (tr0, drop0) =>
      foldrB L tr0 [] fun x acc =>
        if !(x.1 == drop0) then x :: acc else acc

@[expose] def fsMultiBucketAuthFsSendC (Δcka : ℕ) (_la : Bool) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.sum (.base .ss) .nat))
    (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO IIM Γ' (.prod (.opt (.prod (.sum (.base .ss) .nat) (.base .ct))) mbHsTy) :=
  rdsl do
    (h0, ctx0, p0, ssv0, hdr0, m0, pair0) ← return (hE, ctxE, pE, ssvE, hdrE, mE, pairE)
    match ssv0 with
    | .inl ss =>
      let o := Expr.op (O := OO) CKAOp.fsSend (ss, hdr0, m0)
      return (some (.inl o.1, o.2), h0)
    | .inr sIdx =>
      let bk := mbHsGetBookAt h0 sIdx
      let sCorr := bk.1
      let cnt := bk.2.1
      let trs := bk.2.2
      (ok, h1) ←
        if !(cSafeChE (raw (2 + Δcka)) ctx0 p0) && !sCorr then
          csOpt ← query (O := OO) (I := IIM) FSHdrTag.cs (sIdx, ())
          match csOpt with
          | none => return (false, h0)
          | some _ => return (true, mbHsSetBookAt h0 sIdx (true, (cnt, trs)))
        else
          return (true, h0)
      if !ok then
        return (none, h1)
      else
        ctOpt ←
          match pair0 with
          | none => query (O := OO) (I := IIM) FSHdrTag.tr (sIdx, (hdr0, m0))
          | some mPair => query (O := OO) (I := IIM) FSHdrTag.ch (sIdx, (hdr0, mPair))
        match ctOpt with
        | none => return (none, h1)
        | some ct =>
          let bk1 := mbHsGetBookAt h1 sIdx
          let cnt' := bk1.2.1 + 1
          let tr' := (cnt', hdr0, ct) :: bk1.2.2
          return (some (.inr sIdx, ct), mbHsSetBookAt h1 sIdx (bk1.1, (cnt', tr')))

@[expose] def fsMultiBucketAuthFsRecvC (L B : ℕ) (la : Bool) (Δcka : ℕ := 1) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.sum (.base .rs) .nat) (.prod .nat (.base .msg))))) mbHsTy) :=
  rdsl do
    (h0, ctx0, t0, rsv0, hdr0, e0, rec0) ← return (hE, ctxE, tE, rsvE, hdrE, eE, recE)
    match rsv0 with
    | .inl rs =>
      match Expr.op (O := OO) (CKAOp.fsReceive B) (rs, hdr0, e0) with
      | none => return (some none, h0)
      | some (rs', idxMsg) =>
        return (some (some (.inl rs', idxMsg)), h0)
    | .inr sIdx =>
      let bk0 := mbHsGetBookAt h0 sIdx
      let sCorr0 := bk0.1
      let trs0 := bk0.2.2
      let matched := fsTransFindBucketE L trs0 (hdr0, e0)
      (ok, h1) ←
        match matched with
        | some _ => return (true, h0)
        | none =>
          if !(_root_.CryptoGames.SM.healedByE (cGsTL ctx0) (raw (2 + Δcka)) t0) && !sCorr0 then
            csOpt ← query (O := OO) (I := IIM) FSHdrTag.cs (sIdx, ())
            match csOpt with
            | none => return (false, h0)
            | some _ => return (true, mbHsSetBookAt h0 sIdx (true, bk0.2))
          else
            return (true, h0)
      if !ok then
        return (none, h1)
      else
        resOpt ←
          match matched with
          | none => query (O := OO) (I := IIM) FSHdrTag.ij (sIdx, (hdr0, e0))
          | some _ => query (O := OO) (I := IIM) FSHdrTag.dl (sIdx, (hdr0, e0))
        match resOpt with
        | none => return (none, h1)
        | some resSum =>
          match resSum with
          | .inl _ => return (some none, h1)
          | .inr (msgIdx, mo') =>
            let bk1 := mbHsGetBookAt h1 sIdx
            let sCorr1 := bk1.1
            let cnt1 := bk1.2.1
            let trs1 := bk1.2.2
            let isLookaheadInj :=
              match matched with
              | none => (!sCorr1) && (cnt1 < msgIdx)
              | some _ => false
            if bool la && isLookaheadInj then
              return (none, mbHsSetLfWin h1 true)
            else
              let drop :=
                match matched with
                | none => msgIdx
                | some entry => entry.1
              let trs' := fsTransFilterBucketE L trs1 drop
              let h4 := mbHsSetBookAt h1 sIdx (sCorr1, (cnt1, trs'))
              let outE :=
                match mo' with
                | none =>
                  match rec0 with
                  | none => none
                  | some r => some (some (.inr sIdx, msgIdx, cRecMsg r))
                | some msg => some (some (.inr sIdx, msgIdx, msg))
              return (outE, h4)

@[expose] def fsMultiBucketAuthCommitC {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (_ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (_oldE newE : Expr OO Γ' mVpTy) :
    Comp OO IIM Γ' (.prod (.opt mVpTy) mbHsTy) :=
  rdsl do
    return (some newE, hE)

/-- Loop builder for `[L - 1, ..., 0]` via `.iter L` (`O(bits L)` AST size). -/
@[expose] def rangeListBucketC (L : ℕ) {Γ' : List (Ty S)} : Comp OO IIM Γ' (.list .nat) :=
  .bind
    (.iter L (.pair (.nat 0) .nil)
      (.ret (.pair (.add (.fst .v0) (.nat 1)) (.cons (.fst .v0) (.snd .v0)))))
    (.ret (.snd .v0))

@[expose] def isExtMultiBucketEntryE {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) :
    Expr OO Γ' .bool :=
  rdslExpr =>
    match entryE with
    | none => false
    | some sumV =>
      match sumV with
      | .inl _ => false
      | .inr _ => true

@[expose] def anyExtMultiBucketVRE (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) :
    Expr OO Γ' .bool :=
  rdslExpr =>
    letE (vRE, rngE) fun (vR0, rng0) =>
      foldrB L rng0 false fun t acc =>
        if isExtMultiBucketEntryE (tget vR0 t) then true else acc

@[expose] def unliftMultiBucketEntryE {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) :
    Expr OO Γ' (.opt (.base .rs)) :=
  rdslExpr =>
    match entryE with
    | none => none
    | some sumV =>
      match sumV with
      | .inl rs => some rs
      | .inr _ => none

@[expose] def unliftMultiBucketVRE (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) :
    Expr OO Γ' (.tbl (.opt (.base .rs))) :=
  rdslExpr =>
    letE (vRE, rngE) fun (vR0, rng0) =>
      foldrB L rng0 (tconst none) fun t acc =>
        tset acc t (unliftMultiBucketEntryE (tget vR0 t))

@[expose] def fsMultiBucketAuthRevealC (L : ℕ) (gMain _la : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' mVpTy) :
    Comp OO IIM Γ' (.prod (.opt psTy) mbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, vp0) ← return (hE, ctxE, vpE)
    let e := vpTcurNat vp0
    let epAB := cGsEpoch ctx0
    let eMax := maxN epAB.1 epAB.2
    if !(bool gMain) && orE (!(e < nat tH)) (!(eMax < nat tH)) then
      return (none, h0)
    else
      (ssOptOpt, h1) ←
        match vpVS vp0 with
        | none => return (some none, h0)
        | some ssv =>
          match ssv with
          | .inl ss => return (some (some ss), h0)
          | .inr sIdx =>
            csOpt ← query (O := OO) (I := IIM) FSHdrTag.cs (sIdx, ())
            match csOpt with
            | none => return (none, h0)
            | some ss =>
              let bk0 := mbHsGetBookAt h0 sIdx
              return (some (some ss), mbHsSetBookAt h0 sIdx (true, bk0.2))
      match ssOptOpt with
      | none => return (none, h1)
      | some ssReal =>
        rng ← rangeListBucketC L
        if anyExtMultiBucketVRE L (vpVR vp0) rng then
          return (none, h1)
        else
          let vR' := unliftMultiBucketVRE L (vpVR vp0) rng
          return (some (realPartyE vp0 (vpΓ vp0) (vpRoot vp0) ssReal vR'), h1)

/-- Costed multi-session `(tL, par)`-bucket `HooksC` bundle for `redFSAuthMultiBucketProg`,
parameterized by `gMain : Bool` (`true = Main` honest-header mode, `false = ForgedHdr` mode). -/
@[expose] def hooksFSMultiBucketAuthC (L B Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) :
    HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) mbHsTy where
  startSend := fsMultiBucketAuthStartSendC L Δcka qep gMain tL par
  startRecv := fsMultiBucketAuthStartRecvC L Δcka qep gMain tL par
  fsSend := fsMultiBucketAuthFsSendC Δcka la
  fsRecv := fsMultiBucketAuthFsRecvC L B la Δcka
  commit := fsMultiBucketAuthCommitC
  reveal := fsMultiBucketAuthRevealC L gMain la tL

/-- Costed initialization for `redFSAuthMultiBucketProg`: only `gMain = true` (`Main` mode) can
register epoch `0` at `sIdx = 0` (`j = 0`); `gMain = false` (`ForgedHdr` mode) always simulates
epoch `0` locally (`.inl`) since receiver `startRecv` only runs at `t0 = vp.tcur + 1 ≥ 1`. -/
@[expose] def initFSMultiBucketAuthEStateC (L Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'}
    (bE : Expr OO Γ' .bool) :
    Comp OO IIM Γ' (esTy mVpTy mbHsTy) :=
  rdsl do
    b0 ← return bE
    kr ← sample (O := OO) (I := IIM) CKASamp.kr ()
    kc ← sample (O := OO) (I := IIM) CKASamp.kc ()
    ((σ, kVal, sid), h1) ←
      rootFSMultiBucketAuthC L Δcka qep tL par mbHsEmptyE 0 false
        (Expr.op (O := OO) CKAOp.lamI ())
        (Expr.op (O := OO) CKAOp.prngInit kr)
    let regP : Expr OO _ (.prod (.opt .nat) mbHsTy) :=
      raw (if gMain then regSessOptMultiBucketE L true tL h1 (.nat 0) sid else .pair .none h1)
    let optIdx := regP.1
    let h2 := regP.2
    let ssv0 : Expr OO _ (.sum (.base .ss) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitSender kVal)
      | some sIdx => .inr sIdx
    let rsv0 : Expr OO _ (.sum (.base .rs) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
      | some sIdx => .inr sIdx
    let pAB := mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA kc)
      (Expr.op (O := OO) CKAOp.ckaInitB kc)
      σ ssv0 rsv0
    return (esMk (cGsInitE (vpT := mVpTy) pAB.1 pAB.2 b0) h2 false)

/-- Stage-2 `(tL, par)`-bucket multi-session `redFSAuth` program over `SM.spec`, `prngOps`,
`fsaeadMultiBucketIface`, and `prngSMCodec`, parameterized by `gMain : Bool` (`true = Main`
honest-header mode at `j = 0`, `false = ForgedHdr` forged-header mode at `1 ≤ j ≤ q`) and
`la : Bool` (`true =` lookahead forgery win flag), registering up to `L = q + 1` sessions per
parity-`par` epoch `t ≥ healEpoch tL` at external session index `sIdx = L * (t - healEpoch tL) + j`. -/
@[expose] def redFSAuthMultiBucketProg (L B Δcka qep maxSkip : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (par : Bool) :
    CostedReduction OO IIM
      (spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := @fsMultiBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
  init := rdsl [_] do
    es ← initFSMultiBucketAuthEStateC L Δcka qep gMain tL par false
    return ((), (es, none))
  handle := rdsl [st, qArg] do
    (es0, winEp0, q0) ← return (st.1, st.2, qArg)
    match q0 with
    | .inl (.inl (.inl (.inl x))) =>
      (p0, m0, r0) ← return x
      if orE (esAbort es0) (cGsWin (esG es0)) then
        return (.inl (.inl (.inl (.inl none))), (es0, winEp0))
      else
        match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
        | none => return (.inl (.inl (.inl (.inl none))), (es0, winEp0))
        | some s1 =>
          (res, h') ← vSendC (raw (hooksFSMultiBucketAuthC L B Δcka qep gMain tL par la))
            (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
          match res with
          | none =>
            return (.inl (.inl (.inl (.inl none))), (esMk (esG es0) h' true, winEp0))
          | some (st', ct) =>
            let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
            let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
            return (.inl (.inl (.inl (.inl (some ct)))), (esMk g' h' (esAbort es0), winEp0))
    | .inl (.inl (.inl (.inr _))) =>
      return (.inl (.inl (.inl (.inr none))), (es0, winEp0))
    | .inl (.inl (.inr x)) =>
      (out, es') ← deliverEC (raw (hooksFSMultiBucketAuthC L B Δcka qep gMain tL par la))
        L maxSkip (raw (bucketAuthCfgEC Δcka tL)) es0 x
      return (.inl (.inl (.inr out)), (es', winEp0))
    | .inl (.inr x) =>
      let wasWin := cGsWin (esG es0)
      let isNewForged :=
        (x.2.1.1 == vpTcurNat (pGet (cGsSt (esG es0)) x.1) + 1) &&
          !(isHonestHdrMultiBucketE (esH es0) x.2.1)
      (out, es') ← injectEC (raw (hooksFSMultiBucketAuthC L B Δcka qep gMain tL par la))
        L (raw (2 + Δcka)) qep (raw (bucketAuthCfgEC Δcka tL)) es0 x
      let winEp' :=
        if !wasWin && cGsWin (esG es') && orE (bool gMain) isNewForged then
          some x.2.1.1
        else winEp0
      return (.inl (.inr out), (es', winEp'))
    | .inr p0 =>
      let s0 := esG es0
      if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0))) then
        return (.inr none, (es0, winEp0))
      else
        let s1 := cAfterCorrE (raw L) s0 p0
        (res, h') ← fsMultiBucketAuthRevealC L gMain la tL (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match res with
        | none => return (.inr none, (esMk s0 h' true, winEp0))
        | some stOut =>
          return (.inr (some stOut), (esMk s1 h' (esAbort es0), winEp0))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    if bool la then
      return (mbHsLfWin (esH es0))
    else
      match winEp0 with
      | none => return false
      | some tWin =>
        return (((!(esAbort es0) && cGsWin (esG es0)) &&
          cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0)) &&
          (if bool par then !(senderOfE tWin) else senderOfE tWin))

end CostedBucketAuth

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs

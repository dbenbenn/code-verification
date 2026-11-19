/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperCKA -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.ReductionDsl.Notation
import VCVio.OracleComp.EvalDist.Measure

/-!
# Stage-2 `(tL, par)` Bucket Ascending `t`-Hybrid PRF-PRNG Reduction (`[B7]` × `[B8]`, Piece `(B)`)

Bridges `CKA.branch cka Δcka (healEpoch tL) true (redCKAAuthDF{,Paper}Bucket ...)` to the
`(tL, par)`-bucket random-root-table local game (`localAuthDF{,Paper}Bucket`), where active bucket
epochs `healEpoch tL ≤ t0 ≤ qep + 1` draw message-key seeds from lazy `F_{t0}(ik)` (`$ᵗ K` with
`$ᵗ I` at `tH` when `tL.isSome`) while inactive epochs, `σ`, and post-leak epochs step via `prng.up`,
tracking stopping epoch `lc : Option ℕ` across `t ∈ Finset.Ico (healEpoch tL) (qep + 2)`.-/

public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

/-! ## 1. Shallow `(tL, par)` Bucket Ascending `t`-Hybrid PRNG Reduction and Local Root-RF Game -/

namespace CryptoGames.SM.Construction.DeliverForge

section ShallowBucketPRNG

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

/-- `true` once `ctx.tL` records a leak strictly after `tL` (`ltOpt tL cur`). -/
@[expose] def postLeak {St Msg C : Type} (tL : Option ℕ) (ctx : GameState St Msg C) : Bool :=
  match ctx.tL with
  | none => false
  | some cur => ltOpt tL cur

/-- Hook state for `hooksPRNGBucketHybrid`: honest-send cache, per-epoch lazy random tables
`fTable t0 : List (I × K)` for already-hybridized active bucket epochs `healEpoch tL ≤ t0 < t`,
optional leaked root `(eC, σC)` recorded on the first `corr` / post-leak query at
`eC ≥ healEpoch tL`, and stopping epoch `lc : Option ℕ` recording the first epoch at or after
`healEpoch tL` where root confidentiality stops. -/
structure PRNGBucketState (T Sig K I : Type) where
  cache : ℕ → Option (T × Option Sig × K) := fun _ => none
  fTable : ℕ → List (I × K) := fun _ => []
  corrRoot : Option (ℕ × Sig) := none
  lc : Option ℕ := none

/-- Generic-`Δbucket` Stage-2 `(tL, par)` bucket membership (`inStage2Bucket` when
`Δbucket = 3 + Δcka`). -/
@[expose] def inStage2BucketGen (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) : Bool :=
  lastLeakGuessAdmissible Δbucket tL t && (partyPar (Party.senderOf t) == par)

/-- Resolve `σv` at epoch `ep` using `h.corrRoot` when `σv = none`. -/
@[expose] def resolveCorrRoot (h : PRNGBucketState T Sig K I) (ep : ℕ) (σv : Option Sig) :
    Option Sig :=
  match σv with
  | some σ => some σ
  | none =>
    match h.corrRoot with
    | some (eC, σC) => if ep == eC then some σC else none
    | none => none

/-- Lift a `PRFPRNG` oracle computation into `HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)`. -/
@[expose] def liftPBucket {α : Type} (x : PRFPRNG.AdversaryComp Sig I K α) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) α :=
  StateT.lift x

/-- Lazily sample `F_{t0}(ik)` inside `HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)`. -/
@[expose] def lookupPRNGBucketF [DecidableEq I] [SampleableType K] (t0 : ℕ) (ik : I) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) K := do
  let tb0 := (← get).fTable t0
  match tb0.lookup ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with fTable := Function.update s.fTable t0 ((ik, k) :: tb0) }
    return k

/-- Root-RNG step of epoch `t0` in the `(tL, par)` bucket ascending `t`-hybrid PRNG reduction. -/
@[expose] def rootPRNGBucketHybrid [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t t0 : ℕ) (pl : Bool)
    (ik0 : I) (σv0 : Option Sig) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I) (Option (Option Sig × K)) := do
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
      match ← liftPBucket (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
      | none => return none
      | some σOut =>
        modify fun s => { s with corrRoot := some (t0 - 1, σOut) }
        let p := prng.up σOut ik0
        return some (some p.1, p.2)
  else if t0 = t then
    if tL.isSome && t0 = tH then
      match ← liftPBucket (PRFPRNG.challPrngQuery (State := Sig) (Input := I) (Output := K) none) with
      | none => return none
      | some kOut =>
        match ← liftPBucket (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
        | none => return none
        | some σOut => return some (some σOut, kOut)
    else if inStage2BucketGen Δbucket tL par t0 then
      match ← liftPBucket (PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) ik0) with
      | none => return none
      | some (σOut, kOut) => return some (some σOut, kOut)
    else
      match ← liftPBucket (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) (some ik0)) with
      | none => return none
      | some kOut =>
        match ← liftPBucket (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
        | none => return none
        | some σOut => return some (some σOut, kOut)
  else if !(t0 < tH) then
    if tL.isSome && t0 = tH then
      match ← liftPBucket (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) none) with
      | none => return none
      | some _ =>
        let kRand ← StateT.lift (sampleT K)
        return some (none, kRand)
    else if inStage2BucketGen Δbucket tL par t0 then
      match ← liftPBucket (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) (some ik0)) with
      | none => return none
      | some _ =>
        let kRand ← lookupPRNGBucketF t0 ik0
        return some (none, kRand)
    else
      match ← liftPBucket (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) (some ik0)) with
      | none => return none
      | some kOut => return some (none, kOut)
  else
    match ← liftPBucket (PRFPRNG.processQuery (State := Sig) (Input := I) (Output := K) (some ik0)) with
    | none => return none
    | some kOut =>
      match ← liftPBucket (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
      | none => return none
      | some σOut => return some (some σOut, kOut)

/-- Generalized `(tL, par)` bucket ascending `t`-hybrid PRNG hooks parameterized by explicit
bucket healing threshold `Δbucket` (`3 + Δcka` when `Δbucket` is specialized). -/
@[expose] def hooksPRNGBucketHybridGen [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS where
  startSend ctx _ t0 γ0 σv0 r0 := do
    let tH := healEpoch tL
    let pl := postLeak tL ctx
    let h0 ← get
    if pl && h0.lc.isNone && tH < t0 then
      modify fun s => { s with lc := some (t0 - 1) }
    let coins ← match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ0 coins
    match ← rootPRNGBucketHybrid prng Δbucket tL par t t0 pl c.2.2 σv0 with
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
      if !(qep + 1 < t0) && (lastLeakGuessAdmissible Δbucket tL t0 && (partyPar (Party.senderOf t0) == par)) then
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
          match ← liftPBucket (PRFPRNG.challPrfQuery (State := Sig) (Input := I) (Output := K) kk.2) with
          | none => return none
          | some (σOut, kOut) =>
            return some (some (kk.1, some σOut, fs.initReceiver kOut))
        else if !(t0 < tH) then
          let kk := cka.receive γ0 tn0
          let kOut ← lookupPRNGBucketF t0 kk.2
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
      if !pl && h0.lc.isNone && !(e < tH) then
        modify fun s => { s with lc := some e }
      return some (realParty vp vp.γ σ vp.vS vp.vR)
    | none =>
      if !pl && h0.corrRoot.isNone && !(e < tH) && (e == eMax) then
        match ← liftPBucket (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
        | none => return none
        | some σOut =>
          modify fun s => { s with corrRoot := some (e, σOut) }
          if h0.lc.isNone then
            modify fun s => { s with lc := some e }
          return some (realParty vp vp.γ σOut vp.vS vp.vR)
      else
        return none

/-- Stage-2 `(tL, par)` bucket ascending `t`-hybrid PRNG hooks at `Δbucket = 3 + Δcka`. -/
abbrev hooksPRNGBucketHybrid [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  hooksPRNGBucketHybridGen cka prng fs (3 + Δcka) qep tL par t

/-- Initial party states for `redPRNGAuthDF{,Paper}BucketHybrid`: samples CKA key `kc` and runs
`rootPRNGBucketHybrid` at epoch `0` on `lam`. -/
@[expose] def initPRNGBucketHybrid [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      (Option (VP Γ T (Option Sig) SS RS × VP Γ T (Option Sig) SS RS)) := do
  let kc ← StateT.lift (sampleT KC)
  match ← rootPRNGBucketHybrid prng Δbucket tL par t 0 false lam none with
  | none => return none
  | some (σv, kVal) =>
    return some (mkParties (cka.initA kc) (cka.initB kc) σv
      (fs.initSender kVal) (fs.initReceiver kVal))

/-- Stage-2 `(tL, par)` bucket ascending `t`-hybrid PRF-PRNG reduction (`B_prng_u`, non-paper
`corrAllowed`). -/
@[expose] def redPRNGAuthDFBucketHybrid [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    let r ← engRunDFBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t) {} false A
    return match r with
      | none => false
      | some (_, st) => authOutBucket (2 + Δcka) tL st

/-- Paper bucket authenticity outcome gated by stopping epoch `lc` (`lc.all (t ≤ ·)`). -/
@[expose] def authOutBucketPaperAt {VPt Msg C T' Sig' K' I' : Type}
    [DecidableEq Msg] [DecidableEq C]
    (Δ : ℕ) (tL : Option ℕ) (t : ℕ)
    (st : EState VPt Msg C (PRNGBucketState T' Sig' K' I') × Option ℕ) : Bool :=
  authOutBucketPaper Δ tL st &&
    match st.1.h.lc with
    | none => true
    | some e => decide (t ≤ e)

/-- Stage-2 `(tL, par)` bucket ascending `t`-hybrid PRF-PRNG reduction under `corrAllowedPaper`
with hooks at `t` and stopping-gated output `authOutBucketPaperAt (2 + Δcka) tL tOut st`. -/
@[expose] def redPRNGAuthDFPaperBucketHybridAt [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t tOut : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    let r ← engRunDFPaperBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t) {} false A
    return match r with
      | none => false
      | some (_, st) => authOutBucketPaperAt (2 + Δcka) tL tOut st

/-- Stage-2 `(tL, par)` bucket ascending `t`-hybrid PRF-PRNG reduction (`B_prng_u`, paper
`corrAllowedPaper`). -/
@[expose] def redPRNGAuthDFPaperBucketHybrid [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  redPRNGAuthDFPaperBucketHybridAt cka prng fs lam Δcka qep tL par t t A

/-- Stage-2 `(tL, par)` bucket ascending `t`-hybrid PRF-PRNG reduction harvesting the stopping slice
`st.1.h.lc = some t`. -/
@[expose] def redPRNGAuthDFPaperBucketHybridLcEq [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    let r ← engRunDFPaperBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t) {} false A
    return match r with
      | none => false
      | some (_, st) => authOutBucketPaper (2 + Δcka) tL st && decide (st.1.h.lc = some t)

/-! ### Post-PRNG Local `(tL, par)` Bucket Game (`localAuthDF{,Paper}Bucket`) -/

/-- Hook state for the post-PRNG `(tL, par)` bucket local game (`localAuthDF{,Paper}Bucket`),
matching the real-FSAEAD (`b = false`) world of `rootFSMultiDFBucketC` / `redFSAuthDFMultiBucketProg`:
every active bucket epoch `t0` with `healEpoch tL ≤ t0 ≤ qep + 1` while `!postLeak` draws `k` from
lazy random function `fTable t0` (`$ᵗ K` with fresh `$ᵗ I` at `tH` when `tL.isSome`), while inactive
epochs, `σ`, and post-leak epochs step locally via `prng.up`, tracking stopping epoch `lc`. -/
structure LocalBucketState (T Sig K I : Type) where
  cache : ℕ → Option (T × Sig × K) := fun _ => none
  fTable : ℕ → List (I × K) := fun _ => []
  lc : Option ℕ := none

/-- Lazily sample `F_{t0}(ik)` in `HM AuthL11.nilSpec (LocalBucketState T Sig K I)`. -/
@[expose] def lookupLocalBucketF [DecidableEq I] [SampleableType K] (t0 : ℕ) (ik : I) :
    HM AuthL11.nilSpec (LocalBucketState T Sig K I) K := do
  let tb0 := (← get).fTable t0
  match tb0.lookup ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with fTable := Function.update s.fTable t0 ((ik, k) :: tb0) }
    return k

/-- Root-RNG step of epoch `t0` in `localAuthDF{,Paper}Bucket` (matching `rootFSMultiDFBucketC`). -/
@[expose] def rootLocalBucket [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : Sig) :
    HM AuthL11.nilSpec (LocalBucketState T Sig K I) (Sig × K) := do
  let tH := healEpoch tL
  let pIk := prng.up σ0 ik0
  if pl || qep + 1 < t0 then
    return (pIk.1, pIk.2)
  else if tL.isSome && t0 = tH then
    let ir ← StateT.lift (sampleT I)
    let kSample ← StateT.lift (sampleT K)
    return ((prng.up σ0 ir).1, kSample)
  else if inStage2BucketGen Δbucket tL par t0 then
    let kLookup ← lookupLocalBucketF t0 ik0
    return (pIk.1, kLookup)
  else
    return (pIk.1, pIk.2)

/-- Hooks for `localAuthDF{,Paper}Bucket` (matching `hooksFSMultiDFBucketC` before FS session lift). -/
@[expose] def hooksLocalBucket [DecidableEq T] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :
    Hooks AuthL11.nilSpec (LocalBucketState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS where
  startSend ctx _ t0 γ0 σ0 r0 := do
    let tH := healEpoch tL
    let pl := postLeak tL ctx
    let h0 ← get
    if pl && h0.lc.isNone && tH < t0 then
      modify fun s => { s with lc := some (t0 - 1) }
    let coins ← match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ0 coins
    let (σ', kVal) ← rootLocalBucket prng (3 + Δcka) qep tL par t0 pl c.2.2 σ0
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
      if !(qep + 1 < t0) && inStage2Bucket Δcka tL par t0 then
        if tL.isSome && t0 = tH then
          return none
        else if pl then
          let kk := cka.receive γ0 tn0
          let p := prng.up σ0 kk.2
          return some (some (kk.1, p.1, fs.initReceiver p.2))
        else
          let kk := cka.receive γ0 tn0
          let k' ← lookupLocalBucketF t0 kk.2
          return some (some (kk.1, (prng.up σ0 kk.2).1, fs.initReceiver k'))
      else
        return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ _ _ new := pure (some new)
  reveal ctx _ vp := do
    let tH := healEpoch tL
    let e := vp.tcur
    let pl := postLeak tL ctx
    let h0 ← get
    if !pl && h0.lc.isNone && !(e < tH) then
      modify fun s => { s with lc := some e }
    return some (realParty vp vp.γ vp.root vp.vS vp.vR)

/-- Initial party states for `localAuthDF{,Paper}Bucket` (matching `initFSMultiDFBucketEStateC`). -/
@[expose] def initLocalBucket [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) :
    HM AuthL11.nilSpec (LocalBucketState T Sig K I)
      (Option (VP Γ T Sig SS RS × VP Γ T Sig SS RS)) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ, kVal) ← rootLocalBucket prng Δbucket qep tL par 0 false lam (prng.init kr)
  return some (mkParties (cka.initA kc) (cka.initB kc) σ
    (fs.initSender kVal) (fs.initReceiver kVal))

/-- Post-PRNG local `(tL, par)` bucket game (non-paper `corrAllowed`). -/
@[expose] def localAuthDFBucket [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    (engRunDFBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) => authOutBucket (2 + Δcka) tL st

/-- Post-PRNG local `(tL, par)` bucket game (paper `corrAllowedPaper`). -/
@[expose] def localAuthDFPaperBucket [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    (engRunDFPaperBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) => authOutBucketPaper (2 + Δcka) tL st

/-- Post-PRNG local `(tL, par)` bucket game restricted to stopping-epoch slice `st.1.h.lc = lcOpt`. -/
@[expose] def localAuthDFPaperBucketLcEq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (lcOpt : Option ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    (engRunDFPaperBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) => authOutBucketPaper (2 + Δcka) tL st && decide (st.1.h.lc = lcOpt)


/-- Generic `Finset.Ico` telescope helper over `PRFPRNG` hybrids `a .. a + k`. -/
theorem prng_ico_telescope [DecidableEq I]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (B : ℕ → PRFPRNG.Adversary Sig I K)
    (a k : ℕ)
    (hStep : ∀ t, a ≤ t → t < a + k →
      𝒟[PRFPRNG.branch prng true (B t)] {true} ≤ 𝒟[PRFPRNG.branch prng false (B (t + 1))] {true}) :
    𝒟[PRFPRNG.branch prng false (B a)] {true} ≤
      (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
      𝒟[PRFPRNG.branch prng true (B (a + k))] {true} := by
  have hOne : ∀ t, 𝒟[PRFPRNG.branch prng false (B t)] {true} ≤
      PRFPRNG.advantage prng (B t) + 𝒟[PRFPRNG.branch prng true (B t)] {true} := fun t => by
    rw [PRFPRNG.advantage_eq_boolDist, Measure.boolDist_comm, add_comm (Measure.boolDist _ _)]
    exact Measure.apply_true_le_add_boolDist _ _
  induction k with
  | zero =>
    rw [Nat.add_zero, Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]
    exact hOne a
  | succ k ih =>
    have ih' := ih (fun t ht1 ht2 => hStep t ht1 (by omega))
    have hNext : 𝒟[PRFPRNG.branch prng true (B (a + k))] {true} ≤
        PRFPRNG.advantage prng (B (a + k + 1)) +
        𝒟[PRFPRNG.branch prng true (B (a + k + 1))] {true} :=
      (hStep (a + k) (by omega) (by omega)).trans (hOne (a + k + 1))
    have hSum : ∑ t ∈ Finset.Ico a (a + (k + 1) + 1), PRFPRNG.advantage prng (B t) =
        (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
        PRFPRNG.advantage prng (B (a + k + 1)) := by
      have heq : a + (k + 1) + 1 = (a + k + 1) + 1 := by omega
      rw [heq, Finset.sum_Ico_succ_top (by omega)]
    rw [hSum, add_assoc]
    exact ih'.trans (add_le_add le_rfl hNext)

/-! ### Split `Main` (`gMain = true`) / `ForgedHdr` (`gMain = false`) & Parity-Slot Packed Definitions -/

/-- Whether epoch `t0` is active in `rootPRNGBucketHybrid` for `(Δbucket, tL, par)`:
either `tL.isSome && t0 = healEpoch tL`, or `inStage2BucketGen Δbucket tL par t0`. -/
@[expose] def isActiveBucketEpoch (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) : Bool :=
  (tL.isSome && decide (t0 = healEpoch tL)) || inStage2BucketGen Δbucket tL par t0

/-- Parity-slot mode selector for `t`: `true` (`Main`) when `t > healEpoch tL` is an inactive
successor of an active epoch `t - 1`; `false` (`ForgedHdr`) otherwise. -/
@[expose] def bucketSlotIsMain (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) : Bool :=
  !isActiveBucketEpoch Δbucket tL par t && decide (healEpoch tL < t) &&
    isActiveBucketEpoch Δbucket tL par (t - 1)

/-- Decoded hybrid target epoch `t0` for slot `t`: `t - 1` when `bucketSlotIsMain` (`Main` mode),
`t` otherwise (`ForgedHdr` mode). -/
@[expose] def bucketSlotEpoch (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) : ℕ :=
  if bucketSlotIsMain Δbucket tL par t then t - 1 else t

/-- Pure check whether header `hdr` at epoch `hdr.1` carries the cached honest CKA public value. -/
@[expose] def isHonestHdrPRNGBucket [DecidableEq T]
    (h : PRNGBucketState T Sig K I) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _, _), some Tn => Tc == Tn
  | _, _ => false

/-- Pure check whether header `hdr` at epoch `hdr.1` carries the cached honest CKA public value
in `LocalBucketState`. -/
@[expose] def isHonestHdrLocalBucket [DecidableEq T]
    (h : LocalBucketState T Sig K I) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _, _), some Tn => Tc == Tn
  | _, _ => false

/-- Mode-parameterized `withWinEpDF` wrapper: when `gMain = true` (`Main`), identical to
`withWinEpDF (fun c => c.1.1) (fun es => es.g.win)`; when `gMain = false` (`ForgedHdr`), records
`winEp` only when the first winning query is an `inject` at `c.1.1 = epOf (es0.g.st P) + 1` with
`!isHonestHdr es0.h c.1`. -/
@[expose] def withWinEpDFMode {M' : Type → Type} [Monad M']
    {St Msg Coins T' E' VPt HS : Type}
    (gMain : Bool) (isHonestHdr : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS) M')) :
    QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS × Option ℕ) M') :=
  if gMain then
    withWinEpDF (fun c => c.1.1) (fun es => es.g.win) impl
  else
    fun q => StateT.mk fun ⟨es0, winEp0⟩ => do
      let wasWin := es0.g.win
      let (r, es') ← (impl q).run es0
      let winEp' :=
        if !wasWin && es'.g.win then
          match q with
          | .inr (.inl (.inl (.inr (P, c)))) =>
            if decide (c.1.1 = epOf (es0.g.st P) + 1) && !isHonestHdr es0.h c.1 then
              some c.1.1
            else
              winEp0
          | _ => winEp0
        else
          winEp0
      pure (r, (es', winEp'))

/-- Mode-parameterized 6-oracle `DeliverForgePaper` bucket engine implementation on
`EState × Option ℕ` (`rfl` equal to `implEDFPaperBucket` when `gMain = true`). -/
@[expose] def implEDFPaperBucketMode {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (isHonest : HS → Header T → Bool) :
    QueryImpl (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × Option ℕ) (TComp tspec)) :=
  withWinEpDFMode gMain isHonest (fun vp => vp.tcur) (implEDFPaperBucketRaw hk Δ qep maxSkip cfg)

/-- Mode-parameterized paper bucket engine runner (`rfl` equal to `engRunDFPaperBucket` when `gMain = true`). -/
@[expose] def engRunDFPaperBucketMode {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv Sv SSv RSv : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (isHonest : HS → Header T → Bool)
    (init : HM tspec HS (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv))) (h₀ : HS)
    (b : Bool) (A : AdversaryDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) :
    TComp tspec (Option (Bool × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × Option ℕ))) := do
  let (vs, h) ← init.run h₀
  match vs with
  | none => return none
  | some (vA, vB) =>
    let g : Ctx Γv T Sv SSv RSv M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := b }
    let res ←
      (simulateQ (implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest) A).run
        ({ g := g, h := h }, none)
    return some res

/-- Honest-header (`gMain = true`, `Main`) variant of `hooksPRNGBucketHybridGen`:
rejects forged CKA headers (`honest = none` returns `some none`, or `none` at `tH` when `tL.isSome`)
without issuing `PRFPRNG.challPrfQuery`, keeping `reveal` identical to `hooksPRNGBucketHybridGen`. -/
@[expose] def hooksPRNGBucketMainGen [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS :=
  { hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t with
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
        if !(qep + 1 < t0) && inStage2BucketGen Δbucket tL par t0 &&
            (tL.isSome && decide (t0 = tH)) then
          return none
        else
          return some none }

/-- Honest-header (`gMain = true`, `Main`) Stage-2 `(tL, par)` bucket PRNG hooks at `Δbucket = 3 + Δcka`. -/
abbrev hooksPRNGBucketMain [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  hooksPRNGBucketMainGen cka prng fs (3 + Δcka) qep tL par t

/-- Compatibility alias for `hooksPRNGBucketMain`. -/
abbrev hooksPRNGBucketDFMain [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  hooksPRNGBucketMain cka prng fs Δcka qep tL par t

/-- Forged-header (`gMain = false`, `ForgedHdr`) variant of `hooksPRNGBucketHybridGen`:
aborts on `reveal` whenever `!(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)`
(since `afterCorrPaper` leaks `≥ healEpoch tL - 1 > tL`, dooming any future `safeInj` new-epoch `inject`),
avoiding `PRFPRNG.corrQuery` when `sp.prf = true`. -/
@[expose] def hooksPRNGBucketForgedHdrGen [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    Hooks (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS :=
  { hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t with
    reveal := fun ctx _ vp => do
      if !(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL) then
        return none
      else
        match vp.root with
        | some σ => return some (realParty vp vp.γ σ vp.vS vp.vR)
        | none => return none }

/-- Forged-header (`gMain = false`, `ForgedHdr`) Stage-2 `(tL, par)` bucket PRNG hooks at `Δbucket = 3 + Δcka`. -/
abbrev hooksPRNGBucketForgedHdr [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  hooksPRNGBucketForgedHdrGen cka prng fs (3 + Δcka) qep tL par t

/-- Honest-header (`Main`, `gMain = true`) Stage-2 `(tL, par)` bucket PRNG reduction at hybrid `t0`,
gated by stopping epoch `lc` (`authOutBucketPaperAt (2 + Δcka) tL t0`). -/
@[expose] def redPRNGAuthDFPaperBucketMain [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    let r ← engRunDFPaperBucket (hooksPRNGBucketMain cka prng fs Δcka qep tL par t0)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t0) {} false A
    return match r with
      | none => false
      | some (_, st) => authOutBucketPaperAt (2 + Δcka) tL t0 st

/-- Compatibility alias for `redPRNGAuthDFPaperBucketMain`. -/
abbrev redPRNGAuthDFPaperBucketHybridMain [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A

/-- Forged-header (`ForgedHdr`, `gMain = false`) Stage-2 `(tL, par)` bucket PRNG reduction at hybrid `t0`. -/
@[expose] def redPRNGAuthDFPaperBucketForgedHdr [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    let r ← engRunDFPaperBucketMode (hooksPRNGBucketForgedHdr cka prng fs Δcka qep tL par t0)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrPRNGBucket
      (initPRNGBucketHybrid cka prng fs lam (3 + Δcka) tL par t0) {} false A
    return match r with
      | none => false
      | some (_, st) => authOutBucketPaper (2 + Δcka) tL st

/-- Compatibility alias for `redPRNGAuthDFPaperBucketForgedHdr`. -/
abbrev redPRNGAuthDFPaperBucketHybridForgedHdr [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A

/-- Mode-dispatched (`gMain : Bool`) Stage-2 `(tL, par)` bucket PRNG reduction at hybrid `t0`. -/
@[expose] def redPRNGAuthDFPaperBucketSplit [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  if gMain then
    redPRNGAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par t0 A
  else
    redPRNGAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par t0 A

/-- Parity-slot packed Stage-2 `(tL, par)` bucket PRNG reduction (`1 * B_prng_u` at slot `t`):
runs `Main` at `t - 1` on inactive successor slots `bucketSlotIsMain (3 + Δcka) tL par t = true`,
and `ForgedHdr` at `t` otherwise. -/
@[expose] def redPRNGAuthDFPaperBucketPacked [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  redPRNGAuthDFPaperBucketSplit cka prng fs lam Δcka qep tL par
    (bucketSlotIsMain (3 + Δcka) tL par t)
    (bucketSlotEpoch (3 + Δcka) tL par t) A

/-- Honest-header (`Main`) variant of `hooksLocalBucket`: rejects forged CKA headers in `startRecv`,
keeping `reveal` identical to `hooksLocalBucket`. -/
@[expose] def hooksLocalBucketMain [DecidableEq T] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :
    Hooks AuthL11.nilSpec (LocalBucketState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS :=
  { hooksLocalBucket cka prng fs Δcka qep tL par with
    startRecv := fun _ _ t0 γ0 _ tn0 => do
      let tH := healEpoch tL
      let honest := match (← get).cache t0 with
        | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
        | none => none
      match honest with
      | some (σc, kVal) =>
        return some (some ((cka.receive γ0 tn0).1, σc, fs.initReceiver kVal))
      | none =>
        if !(qep + 1 < t0) && inStage2Bucket Δcka tL par t0 &&
            (tL.isSome && decide (t0 = tH)) then
          return none
        else
          return some none }

/-- Compatibility alias for `hooksLocalBucketMain`. -/
abbrev hooksLocalBucketDFMain [DecidableEq T] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :=
  hooksLocalBucketMain cka prng fs Δcka qep tL par

/-- Forged-header (`ForgedHdr`) variant of `hooksLocalBucket`: aborts in `reveal` whenever
`!(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)`. -/
@[expose] def hooksLocalBucketForgedHdr [DecidableEq T] [DecidableEq I] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) :
    Hooks AuthL11.nilSpec (LocalBucketState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS :=
  { hooksLocalBucket cka prng fs Δcka qep tL par with
    reveal := fun ctx _ vp =>
      if !(vp.tcur < healEpoch tL) || !(max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL) then
        pure none
      else
        pure (some (realParty vp vp.γ vp.root vp.vS vp.vR)) }

/-- Post-PRNG local `(tL, par)` bucket game for `Main` (`gMain = true`, honest-header wins). -/
@[expose] def localAuthDFPaperBucketMain [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    (engRunDFPaperBucket (hooksLocalBucketMain cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) => authOutBucketPaper (2 + Δcka) tL st

/-- Post-PRNG local `(tL, par)` bucket `Main` (`gMain = true`) game restricted to stopping-epoch
slice `st.1.h.lc = lcOpt`. -/
@[expose] def localAuthDFPaperBucketMainLcEq [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (lcOpt : Option ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    (engRunDFPaperBucket (hooksLocalBucketMain cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) => authOutBucketPaper (2 + Δcka) tL st && decide (st.1.h.lc = lcOpt)

/-- Post-PRNG local `(tL, par)` bucket game for `ForgedHdr` (`gMain = false`, new forged-header wins). -/
@[expose] def localAuthDFPaperBucketForgedHdr [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ AuthL11.lImpl
    (engRunDFPaperBucketMode (hooksLocalBucketForgedHdr cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) false isHonestHdrLocalBucket
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) => authOutBucketPaper (2 + Δcka) tL st

/-- Mode-dispatched (`gMain : Bool`) post-PRNG local `(tL, par)` bucket game. -/
@[expose] def localAuthDFPaperBucketSplit [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par gMain : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool :=
  if gMain then
    localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A
  else
    localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A

/-- Alias for `localAuthDFPaperBucketSplit` with `(gMain : Bool)` before `(tL : Option ℕ) (par : Bool)`. -/
abbrev localAuthDFPaperBucketMode [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool :=
  localAuthDFPaperBucketSplit cka prng fs lam Δcka qep tL par gMain A

end ShallowBucketPRNG

end CryptoGames.SM.Construction.DeliverForge


/-! ## 2. Costed `ReductionDsl` Programs `redPRNGAuthDF{,Paper}BucketHybridProg` -/

namespace CryptoGames.SM.Construction

open ReductionDsl
open scoped Computational.Proofs.ReductionDsl.Notation
open CryptoGames.SM.Engine

section HooksPRNGBucketCDF

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E

/-- Hook state type for `hooksPRNGBucketParPaperC`: `cache × fTable × corrRoot` where
`corrRoot : .opt (.prod .nat (.base .sig))`. -/
@[expose, reducible] def prngBucketHsTy : Ty S :=
  .prod (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    (.prod (.tbl (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
      (.prod (.opt (.prod .nat (.base .sig))) (.opt .nat)))

/-- Engine state type `esTy prngVpTy prngBucketHsTy`. -/
@[expose, reducible] def prngBucketEsTy : Ty S :=
  esTy (@prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (@prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)

/-- Reduction state type `(prngBucketEsTy, Option ℕ)` recording `winEp`. -/
@[expose, reducible] def prngBucketRedEsTy : Ty S :=
  .prod (@prngBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E) (.opt .nat)

/-- Encode `DeliverForge.PRNGBucketState T RSt K I` into `prngBucketHsTy.denote`. -/
@[expose] def prngBucketHsEnc (h : DeliverForge.PRNGBucketState T RSt K I) :
    (@prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (h.cache, (h.fTable, (h.corrRoot, h.lc)))

variable {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbHsTy" => @prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbVpTy" => @prngVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbEsTy" => @prngBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbRedEsTy" => @prngBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E

/-- `postLeak` expression in `ReductionDsl`: `O(1)` check on `cGsTL ctxE`. -/
@[expose] def postLeakBucketE {O : Ops S} {vpT : Ty S} {Γ'} (tL : Option ℕ)
    (ctxE : Expr O Γ' (cGsTy vpT)) : Expr O Γ' .bool :=
  rdslExpr =>
    match cGsTL ctxE with
    | none => false
    | some cur => ltOptE (optNatLit (raw tL)) cur

@[expose] def prngBucketHsCache {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy) :
    Expr O Γ' (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E) := .fst h

@[expose] def prngBucketHsFTbl {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy) :
    Expr O Γ' (.tbl (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) := .fst (.snd h)

@[expose] def prngBucketHsCorrRoot {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy) :
    Expr O Γ' (.opt (.prod .nat (.base .sig))) := .fst (.snd (.snd h))

@[expose] def prngBucketHsLc {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy) :
    Expr O Γ' (.opt .nat) := .snd (.snd (.snd h))

@[expose] def prngBucketHsEmptyE {O : Ops S} {Γ'} : Expr O Γ' pbHsTy :=
  .pair (.tconst .none) (.pair (.tconst .nil) (.pair .none .none))

@[expose] def prngBucketHsSetCache {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy)
    (c' : Expr O Γ' (@prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)) : Expr O Γ' pbHsTy :=
  .pair c' (.snd h)

@[expose] def prngBucketHsSetFTblAt {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy) (tE : Expr O Γ' .nat)
    (tb' : Expr O Γ' (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    Expr O Γ' pbHsTy :=
  .pair (prngBucketHsCache h)
    (.pair (.tset (prngBucketHsFTbl h) tE tb') (.pair (prngBucketHsCorrRoot h) (prngBucketHsLc h)))

@[expose] def prngBucketHsSetCorrRoot {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy)
    (cr : Expr O Γ' (.opt (.prod .nat (.base .sig)))) : Expr O Γ' pbHsTy :=
  .pair (prngBucketHsCache h) (.pair (prngBucketHsFTbl h) (.pair cr (prngBucketHsLc h)))

@[expose] def prngBucketHsSetLc {O : Ops S} {Γ'} (h : Expr O Γ' pbHsTy)
    (lc' : Expr O Γ' (.opt .nat)) : Expr O Γ' pbHsTy :=
  .pair (prngBucketHsCache h) (.pair (prngBucketHsFTbl h) (.pair (prngBucketHsCorrRoot h) lc'))

/-- Costed `resolveCorrRoot`: resolves `σvE` at epoch `epE` via `prngBucketHsCorrRoot hE`. -/
@[expose] def resolveCorrRootE {O : Ops S} {Γ'}
    (hE : Expr O Γ' pbHsTy) (epE : Expr O Γ' .nat) (σvE : Expr O Γ' (.opt (.base .sig))) :
    Expr O Γ' (.opt (.base .sig)) :=
  rdslExpr =>
    letE (hE, epE, σvE) fun (h0, ep0, σv0) =>
      match σv0 with
      | some σ => some σ
      | none =>
        match prngBucketHsCorrRoot h0 with
        | none => none
        | some (eC, σC) => if ep0 == eC then some σC else none

/-- Costed lazy random-table lookup `F_{t0}(ik0)` bounded by `L` (`0` `PRNGTag` queries; samples
`CKASamp.k` on a cache miss). -/
@[expose] def lookupPRNGBucketFC (L : ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) :
    Comp OO II Γ' (.prod (.base .k) pbHsTy) :=
  rdsl do
    (h0, t0, ik0) ← return (hE, tE, ikE)
    let tb0 := tget (prngBucketHsFTbl h0) t0
    match tableLookupE L tb0 ik0 with
    | none =>
      kNew ← sample (O := OO) (I := II) CKASamp.k ()
      return (kNew, prngBucketHsSetFTblAt h0 t0 ((ik0, kNew) :: tb0))
    | some kFound =>
      return (kFound, h0)

/-- Costed `rootPRNGBucketHybrid` across the epoch regimes (`t0 > t`, `pl || corrRoot.isSome`,
`t0 == t`, `tH ≤ t0 < t`, `t0 < tH`). -/
@[expose] def rootPRNGBucketHybridC (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σvE : Expr OO Γ' (.opt (.base .sig))) :
    Comp OO II Γ' (.prod (.opt (.prod (.opt (.base .sig)) (.base .k))) pbHsTy) :=
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
    else if orE pl0 (isSomeE (prngBucketHsCorrRoot h0)) then
      match σv with
      | none =>
        σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
        match σOpt with
        | none => return (none, h0)
        | some σOut =>
          let h1 := prngBucketHsSetCorrRoot h0 (some (t0 - 1, σOut))
          let p := Expr.op (O := OO) CKAOp.prngUp (σOut, ik0)
          return (some (some p.1, p.2), h1)
      | some σ =>
        let p := Expr.op (O := OO) CKAOp.prngUp (σ, ik0)
        return (some (some p.1, p.2), h0)
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
      else if validGuessBucketParPaperE (raw Δbucket) (raw tL) (raw par) t0 then
        skOpt ← query (O := OO) (I := II) PRNGTag.challPrf ik0
        match skOpt with
        | none => return (none, h0)
        | some (σOut, kOut) => return (some (some σOut, kOut), h0)
      else
        stepOpt ← prngProcessCorrC (some ik0)
        return (stepOpt, h0)
    else if !(t0 < nat tH) then
      if bool tL.isSome && (t0 == nat tH) then
        kProc ← query (O := OO) (I := II) PRNGTag.process none
        match kProc with
        | none => return (none, h0)
        | some _ =>
          kRand ← sample (O := OO) (I := II) CKASamp.k ()
          return (some (none, kRand), h0)
      else if validGuessBucketParPaperE (raw Δbucket) (raw tL) (raw par) t0 then
        kProc ← query (O := OO) (I := II) PRNGTag.process (some ik0)
        match kProc with
        | none => return (none, h0)
        | some _ =>
          (kRand, h1) ← lookupPRNGBucketFC L h0 t0 ik0
          return (some (none, kRand), h1)
      else
        kProc ← query (O := OO) (I := II) PRNGTag.process (some ik0)
        match kProc with
        | none => return (none, h0)
        | some kOut => return (some (none, kOut), h0)
    else
      stepOpt ← prngProcessCorrC (some ik0)
      return (stepOpt, h0)

/-- Costed `startSend` for `hooksPRNGBucketParPaperC`. -/
@[expose] def prngBucketStartSendC (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy)) (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO II Γ'
      (.prod (.opt (.prod (.base .γ) (.prod (.base .t) (.prod (.opt (.base .sig)) (.base .ss)))))
        pbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, t0, γ0, σv0, r0) ← return (hE, ctxE, tE, γE, σvE, rE)
    let pl0 := postLeakBucketE (raw tL) ctx0
    let hLc :=
      if pl0 && !(isSomeE (prngBucketHsLc h0)) && (nat tH < t0) then
        prngBucketHsSetLc h0 (some (t0 - 1))
      else h0
    coins ←
      match r0 with
      | none => sample (O := OO) (I := II) CKASamp.ccoins ()
      | some c => return c
    let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ0, coins)
    (stepOpt, h1) ← rootPRNGBucketHybridC L Δbucket tL par t hLc t0 pl0 cOut.2.2 σv0
    match stepOpt with
    | none => return (none, h1)
    | some (σ', kVal) =>
      let tMsg := cOut.2.1
      let cache' := tset (prngBucketHsCache h1) t0 (some (tMsg, σ', kVal))
      let h2 := prngBucketHsSetCache h1 cache'
      let ss := Expr.op (O := OO) CKAOp.fsInitSender kVal
      return (some (cOut.1, tMsg, σ', ss), h2)

/-- Costed `startRecv` for `hooksPRNGBucketParPaperC`. -/
@[expose] def prngBucketStartRecvC (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy)) (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .rs)))))
        pbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, t0, γ0, σv0, tn0) ← return (hE, ctxE, tE, γE, σvE, tnE)
    let pl0 := postLeakBucketE (raw tL) ctx0
    let honest :=
      match tget (prngBucketHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if !(nat (qep + 1) < t0) && validGuessBucketParPaperE (raw Δbucket) (raw tL) (raw par) t0 then
        if bool tL.isSome && (t0 == nat tH) then
          return (none, h0)
        else if orE pl0 (orE (isSomeE (prngBucketHsCorrRoot h0)) (nat t < t0)) then
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
          (kOut, h1) ← lookupPRNGBucketFC L h0 t0 kk.2
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

@[expose] def prngBucketFsSendC {Γ'}
    (hE : Expr OO Γ' pbHsTy) (_ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (_pE : Expr OO Γ' .bool) (_tE : Expr OO Γ' .nat)
    (ssE : Expr OO Γ' (.base .ss)) (hdrE : Expr OO Γ' hdrTy) (mE : Expr OO Γ' (.base .msg))
    (_pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO II Γ' (.prod (.opt (.prod (.base .ss) (.base .ct))) pbHsTy) :=
  rdsl do return (some (Expr.op (O := OO) CKAOp.fsSend (ssE, hdrE, mE)), hE)

@[expose] def prngBucketFsRecvC (B : ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (_ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (_pE : Expr OO Γ' .bool) (_tE : Expr OO Γ' .nat)
    (rsE : Expr OO Γ' (.base .rs)) (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct))
    (_recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO II Γ' (.prod (.opt (.opt (.prod (.base .rs) (.prod .nat (.base .msg))))) pbHsTy) :=
  rdsl do return (some (Expr.op (O := OO) (CKAOp.fsReceive B) (rsE, hdrE, eE)), hE)

@[expose] def prngBucketCommitC {Γ'}
    (hE : Expr OO Γ' pbHsTy) (_ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (_pE : Expr OO Γ' .bool) (_oldE newE : Expr OO Γ' pbVpTy) :
    Comp OO II Γ' (.prod (.opt pbVpTy) pbHsTy) :=
  rdsl do return (some newE, hE)

/-- Costed `reveal` for `hooksPRNGBucketParPaperC`: resolves `vpRoot` via `corrRoot`, or queries
`PRNGTag.corr ()` (`1` query) when `vpRoot = none` at `e = eMax ≥ healEpoch tL` before `postLeak`. -/
@[expose] def prngBucketRevealC (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (_pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) pbHsTy) :=
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
        if !(e < nat tH) && !(isSomeE (prngBucketHsCorrRoot h0)) then
          prngBucketHsSetCorrRoot h0 (some (e, σ))
        else h0
      let h2 :=
        if !pl0 && !(isSomeE (prngBucketHsLc h0)) && !(e < nat tH) then
          prngBucketHsSetLc h1 (some e)
        else h1
      return (some (realPartyE vp0 (vpΓ vp0) σ (vpVS vp0) (vpVR vp0)), h2)
    | none =>
      if !pl0 && !(isSomeE (prngBucketHsCorrRoot h0)) && !(e < nat tH) && (e == eMax) then
        σOpt ← query (O := OO) (I := II) PRNGTag.corr ()
        match σOpt with
        | none => return (none, h0)
        | some σOut =>
          let h1 := prngBucketHsSetCorrRoot h0 (some (e, σOut))
          let h2 :=
            if !(isSomeE (prngBucketHsLc h0)) then
              prngBucketHsSetLc h1 (some e)
            else h1
          return (some (realPartyE vp0 (vpΓ vp0) σOut (vpVS vp0) (vpVR vp0)), h2)
      else
        return (none, h0)

/-- Costed `HooksC` bundle for `(tL, par)` bucket ascending `t`-hybrid PRNG reductions. -/
@[expose] def hooksPRNGBucketParPaperC (L B Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) pbHsTy where
  startSend := prngBucketStartSendC L Δbucket tL par t
  startRecv := prngBucketStartRecvC L Δbucket qep tL par t
  fsSend := prngBucketFsSendC
  fsRecv := prngBucketFsRecvC B
  commit := prngBucketCommitC
  reveal := prngBucketRevealC tL

/-- Costed initial `EState` construction for `redPRNGAuthDF{,Paper}BucketHybridProg`. -/
@[expose] def initPRNGBucketHybridEStateC (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (bE : Expr OO Γ' .bool) : Comp OO II Γ' pbEsTy :=
  rdsl do
    b0 ← return bE
    kc ← sample (O := OO) (I := II) CKASamp.kc ()
    (stepOpt, h1) ← rootPRNGBucketHybridC L Δbucket tL par t prngBucketHsEmptyE 0 false
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

/-- Generalized costed Stage-2 `(tL, par)` bucket ascending `t`-hybrid PRF-PRNG reduction
(non-paper `cCorrAllowedE`), parameterized by explicit `Δbucket`. -/
@[expose] def redPRNGAuthDFBucketHybridProgGen (L B Δcka Δbucket qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := pbRedEsTy
  init := rdsl [_] do
    es ← initPRNGBucketHybridEStateC L Δbucket tL par t false
    return ((), (es, none))
  handle := rdsl [st, q] do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← vSendC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
              (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (inl (inl (inl (inl none)))),
                (esMk (esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))),
                (esMk g' h' (esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
          L maxSkip (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        (out, es') ← injectEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
          L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← prngBucketRevealC (raw tL) (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
    | .inr x =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← deliverForgeEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
        L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
      let winEp' := if !wasWin && cGsWin (esG es') then some x.2.2.1.1 else winEp0
      return (.inr out, (es', winEp'))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      return ((!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0))

/-- Costed Stage-2 `(tL, par)` bucket ascending `t`-hybrid `redPRNGAuthDFBucketHybrid` program
(`B_prng_u` for non-paper authenticity over `SM.specDF`) at `Δbucket := 3 + Δcka`. -/
abbrev redPRNGAuthDFBucketHybridProg (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  redPRNGAuthDFBucketHybridProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka (3 + Δcka) qep maxSkip tL par t

/-- Generalized costed Stage-2 `(tL, par)` bucket ascending `t`-hybrid PRF-PRNG reduction
(paper `cCorrAllowedPaperE`), parameterized by explicit `Δbucket`. -/
@[expose] def redPRNGAuthDFPaperBucketHybridProgGen (L B Δcka Δbucket qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := pbRedEsTy
  init := rdsl [_] do
    es ← initPRNGBucketHybridEStateC L Δbucket tL par t false
    return ((), (es, none))
  handle := rdsl [st, q] do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← vSendC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
              (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (inl (inl (inl (inl none)))),
                (esMk (esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))),
                (esMk g' h' (esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
          L maxSkip (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        (out, es') ← injectEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
          L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedPaperE (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← prngBucketRevealC (raw tL) (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
    | .inr x =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← deliverForgeEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
        L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
      let winEp' := if !wasWin && cGsWin (esG es') then some x.2.2.1.1 else winEp0
      return (.inr out, (es', winEp'))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      let lcOK :=
        match prngBucketHsLc (esH es0) with
        | none => true
        | some e => !(e < nat t)
      return (((!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0)) && lcOK)

/-- Costed Stage-2 `(tL, par)` bucket ascending `t`-hybrid `redPRNGAuthDFPaperBucketHybrid` program
(`B_prng_u` for paper authenticity over `SM.specDF`) at `Δbucket := 3 + Δcka`. -/
abbrev redPRNGAuthDFPaperBucketHybridProg (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  redPRNGAuthDFPaperBucketHybridProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka (3 + Δcka) qep maxSkip tL par t

/-! ### 3. Syntactic Query Equalities, `PotOK` `min (2 + 2*q) (q + 3)` Bounds, and Advantage Bridges -/

@[simp] theorem lookupPRNGBucketFC_queries (L : ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) :
    (lookupPRNGBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE tE ikE).queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [lookupPRNGBucketFC, Comp.queries]

@[simp] theorem rootPRNGBucketHybridC_queries (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ'} (hE : Expr OO Γ' pbHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σvE : Expr OO Γ' (.opt (.base .sig))) :
    (rootPRNGBucketHybridC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t hE tE plE ikE σvE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [rootPRNGBucketHybridC, prngProcessCorrC, Comp.queries]

@[simp] theorem prngBucketStartSendC_queries (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ'} (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (prngBucketStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t hE ctxE pE tE γE σvE rE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [prngBucketStartSendC, Comp.queries]

@[simp] theorem prngBucketStartRecvC_queries (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) {Γ'} (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t)) :
    (prngBucketStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket qep tL par t hE ctxE pE tE γE σvE tnE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [prngBucketStartRecvC, Comp.queries]

@[simp] theorem prngBucketRevealC_queries (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbVpTy) :
    (prngBucketRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [prngBucketRevealC, Comp.queries]

@[simp] theorem initPRNGBucketHybridEStateC_queries (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) {Γ'} (bE : Expr OO Γ' .bool) :
    (initPRNGBucketHybridEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t bE).queries (fun _ => 1) (fun _ => 0) = 2 := by
  simp [initPRNGBucketHybridEStateC, Comp.queries]

@[simp] theorem redPRNGAuthDFBucketHybridProgGen_totalQueries
    (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ) :
    (redPRNGAuthDFBucketHybridProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip tL par t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  simp [CostedReduction.totalQueries, redPRNGAuthDFBucketHybridProgGen, deliverEC, injectEC,
    deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
    hooksPRNGBucketParPaperC, prngBucketFsSendC, prngBucketFsRecvC, prngBucketCommitC, Comp.queries]

@[simp] theorem redPRNGAuthDFBucketHybridProg_totalQueries
    (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ) :
    (redPRNGAuthDFBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL par t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 :=
  redPRNGAuthDFBucketHybridProgGen_totalQueries L B Δcka (3 + Δcka) qep maxSkip tL par t q

@[simp] theorem redPRNGAuthDFPaperBucketHybridProgGen_totalQueries
    (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ) :
    (redPRNGAuthDFPaperBucketHybridProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip tL par t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  simp [CostedReduction.totalQueries, redPRNGAuthDFPaperBucketHybridProgGen, deliverEC, injectEC,
    deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
    hooksPRNGBucketParPaperC, prngBucketFsSendC, prngBucketFsRecvC, prngBucketCommitC, Comp.queries]

@[simp] theorem redPRNGAuthDFPaperBucketHybridProg_totalQueries
    (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ) :
    (redPRNGAuthDFPaperBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL par t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 :=
  redPRNGAuthDFPaperBucketHybridProgGen_totalQueries L B Δcka (3 + Δcka) qep maxSkip tL par t q

/-! ### 4. Costed Split `Main` / `ForgedHdr` and Parity-Slot Packed `ReductionDsl` Programs -/

/-- Costed check whether `hdrE` matches the honest sender's cached CKA header in `prngBucketHsCache hE`. -/
@[expose] def isHonestHdrPRNGBucketE {Γ'}
    (hE : Expr OO Γ' pbHsTy) (hdrE : Expr OO Γ' hdrTy) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (hE, hdrE) fun (h0, hdr0) =>
      match hdr0.2 with
      | none => false
      | some tn0 =>
        match tget (prngBucketHsCache h0) hdr0.1 with
        | none => false
        | some (tCached, _) => Expr.op (O := OO) CKAOp.eqT (tCached, tn0)

/-- Costed `startRecv` for `Main` (`gMain = true`): rejects forged headers (`0` `PRNGTag` queries). -/
@[expose] def prngBucketStartRecvMainC (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (_ctxE : Expr OO Γ' (cGsTy pbVpTy)) (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (_σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .rs)))))
        pbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, t0, γ0, tn0) ← return (hE, tE, γE, tnE)
    let honest :=
      match tget (prngBucketHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if !(nat (qep + 1) < t0) && validGuessBucketParPaperE (raw Δbucket) (raw tL) (raw par) t0 &&
          (bool tL.isSome && (t0 == nat tH)) then
        return (none, h0)
      else
        return (some none, h0)
    | some (σc, kVal) =>
      let σc' := resolveCorrRootE h0 t0 σc
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rs := Expr.op (O := OO) CKAOp.fsInitReceiver kVal
      return (some (some (γ', σc', rs)), h0)

/-- Mode-parameterized costed `startRecv` (`gMain = true` → `Main`, `gMain = false` → `ForgedHdr`). -/
@[expose] def prngBucketStartRecvSplitC (L Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool)
    (t0 : ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .rs)))))
        pbHsTy) :=
  if gMain then
    prngBucketStartRecvMainC Δbucket qep tL par hE ctxE pE tE γE σvE tnE
  else
    prngBucketStartRecvC L Δbucket qep tL par t0 hE ctxE pE tE γE σvE tnE

/-- Costed `reveal` for `Main` (`gMain = true`): aborts on `Q_par` corruptions at `e ≥ healEpoch tL`
or `.A` at `e = 0` when `par = false`, otherwise delegates to `prngBucketRevealC`. -/
@[expose] def prngBucketRevealMainC (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) pbHsTy) :=
  let tH : ℕ := healEpoch tL
  rdsl do
    (h0, ctx0, p0, vp0) ← return (hE, ctxE, pE, vpE)
    let e := vpTcurNat vp0
    let badMainCorr :=
      !(e < nat tH) && orE (if bool par then !p0 else p0) ((e == nat 0) && bool (!par))
    if badMainCorr then
      return (none, h0)
    else
      prngBucketRevealC (raw tL) h0 ctx0 p0 vp0

/-- Costed `reveal` for `ForgedHdr` (`gMain = false`): aborts whenever
`!(e < healEpoch tL) || !(eMax < healEpoch tL)` (`0` `PRNGTag` queries). -/
@[expose] def prngBucketRevealForgedHdrC (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (_pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) pbHsTy) :=
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
      | none => return (none, h0)
      | some σ =>
        return (some (realPartyE vp0 (vpΓ vp0) σ (vpVS vp0) (vpVR vp0)), h0)

/-- Mode-parameterized costed `reveal` (`gMain = true` → `prngBucketRevealC`, `gMain = false` → `ForgedHdr`). -/
@[expose] def prngBucketRevealSplitC (tL : Option ℕ) (_par gMain : Bool) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbVpTy) :
    Comp OO II Γ' (.prod (.opt psTy) pbHsTy) :=
  if gMain then
    prngBucketRevealC tL hE ctxE pE vpE
  else
    prngBucketRevealForgedHdrC tL hE ctxE pE vpE

/-- Mode-parameterized costed `HooksC` bundle (`gMain = true` → `Main`, `gMain = false` → `ForgedHdr`). -/
@[expose] def hooksPRNGBucketSplitPaperC (L B Δbucket qep : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t0 : ℕ) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) pbHsTy where
  startSend := prngBucketStartSendC L Δbucket tL par t0
  startRecv := prngBucketStartRecvSplitC L Δbucket qep tL par gMain t0
  fsSend := prngBucketFsSendC
  fsRecv := prngBucketFsRecvC B
  commit := prngBucketCommitC
  reveal := prngBucketRevealSplitC tL par gMain

/-- Generalized mode-parameterized costed Stage-2 `(tL, par)` bucket PRNG reduction
(`gMain = true` → `Main`, `gMain = false` → `ForgedHdr`) at hybrid `t0`. -/
@[expose] def redPRNGAuthDFPaperBucketSplitProgGen (L B Δcka Δbucket qep maxSkip : ℕ)
    (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := pbRedEsTy
  init := rdsl [_] do
    es ← initPRNGBucketHybridEStateC L Δbucket tL par t0 false
    return ((), (es, none))
  handle := rdsl [st, q] do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if orE (esAbort es0) (cGsWin (esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← vSendC (raw (hooksPRNGBucketSplitPaperC L B Δbucket qep tL par gMain t0))
              (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (inl (inl (inl (inl none)))),
                (esMk (esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
              let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))),
                (esMk g' h' (esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← deliverEC (raw (hooksPRNGBucketSplitPaperC L B Δbucket qep tL par gMain t0))
          L maxSkip (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := cGsWin (esG es0)
        let isNewForged :=
          (x.2.1.1 == vpTcurNat (pGet (cGsSt (esG es0)) x.1) + 1) &&
            !(isHonestHdrPRNGBucketE (esH es0) x.2.1)
        (out, es') ← injectEC (raw (hooksPRNGBucketSplitPaperC L B Δbucket qep tL par gMain t0))
          L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
        let winEp' :=
          if !wasWin && cGsWin (esG es') && orE (bool gMain) isNewForged then
            some x.2.1.1
          else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := esG es0
        if orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedPaperE (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := cAfterCorrE (raw L) s0 p0
          (res, h') ← prngBucketRevealSplitC (raw tL) (raw par) (raw gMain)
            (esH es0) s0 p0 (pGet (cGsSt s0) p0)
          match res with
          | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
    | .inr x =>
      let wasWin := cGsWin (esG es0)
      (out, es') ← deliverForgeEC (raw (hooksPRNGBucketSplitPaperC L B Δbucket qep tL par gMain t0))
        L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
      let winEp' :=
        if !wasWin && cGsWin (esG es') && bool gMain then some x.2.2.1.1 else winEp0
      return (.inr out, (es', winEp'))
  finish := rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      let lcOK :=
        if bool gMain then
          match prngBucketHsLc (esH es0) with
          | none => true
          | some e => !(e < nat t0)
        else
          true
      return (((!(esAbort es0) && cGsWin (esG es0)) &&
        cAuthOKE (raw L) (raw (2 + Δcka)) (optNatLit (raw tL)) tWin (esG es0)) && lcOK)

/-- Mode-parameterized costed Stage-2 `(tL, par)` bucket PRNG reduction at `Δbucket := 3 + Δcka`. -/
abbrev redPRNGAuthDFPaperBucketSplitProg (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ) :=
  redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka (3 + Δcka) qep maxSkip tL par gMain t0

/-- Parity-slot packed generalized costed Stage-2 `(tL, par)` bucket PRNG reduction (`1 * B_prng_u`
at slot `t`), dispatching via `bucketSlotIsMain` and `bucketSlotEpoch`. -/
@[expose] def redPRNGAuthDFPaperBucketPackedProgGen (L B Δcka Δbucket qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip tL par
    (DeliverForge.bucketSlotIsMain Δbucket tL par t)
    (DeliverForge.bucketSlotEpoch Δbucket tL par t)

/-- Parity-slot packed costed Stage-2 `(tL, par)` bucket PRNG reduction (`1 * B_prng_u`) at
`Δbucket := 3 + Δcka`. -/
abbrev redPRNGAuthDFPaperBucketPackedProg (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) :=
  redPRNGAuthDFPaperBucketPackedProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka (3 + Δcka) qep maxSkip tL par t

@[simp] theorem prngBucketStartRecvMainC_queries (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t)) :
    (prngBucketStartRecvMainC (ckaReceive := ckaReceive) (fsInitReceiver := fsInitReceiver)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δbucket qep tL par hE ctxE pE tE γE σvE tnE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngBucketStartRecvMainC, Comp.queries]

@[simp] theorem prngBucketRevealMainC_queries (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbVpTy) :
    (prngBucketRevealMainC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL par hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [prngBucketRevealMainC, Comp.queries]

@[simp] theorem prngBucketRevealForgedHdrC_queries (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbHsTy) (ctxE : Expr OO Γ' (cGsTy pbVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbVpTy) :
    (prngBucketRevealForgedHdrC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngBucketRevealForgedHdrC, Comp.queries]

@[simp] theorem redPRNGAuthDFPaperBucketSplitProgGen_totalQueries
    (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 q : ℕ) :
    (redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip tL par gMain t0).totalQueries
      (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  cases gMain <;>
    simp [CostedReduction.totalQueries, redPRNGAuthDFPaperBucketSplitProgGen, deliverEC, injectEC,
      deliverForgeEC, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
      hooksPRNGBucketSplitPaperC, prngBucketStartRecvSplitC, prngBucketRevealSplitC,
      prngBucketFsSendC, prngBucketFsRecvC, prngBucketCommitC, Comp.queries]

@[simp] theorem redPRNGAuthDFPaperBucketPackedProgGen_totalQueries
    (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ) :
    (redPRNGAuthDFPaperBucketPackedProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip tL par t).totalQueries
      (fun _ => 1) (fun _ => 0) q = 2 + q * 2 :=
  redPRNGAuthDFPaperBucketSplitProgGen_totalQueries L B Δcka Δbucket qep maxSkip tL par _ _ q

@[simp] theorem redPRNGAuthDFPaperBucketPackedProg_totalQueries
    (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ) :
    (redPRNGAuthDFPaperBucketPackedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL par t).totalQueries
      (fun _ => 1) (fun _ => 0) q = 2 + q * 2 :=
  redPRNGAuthDFPaperBucketPackedProgGen_totalQueries L B Δcka (3 + Δcka) qep maxSkip tL par t q

end HooksPRNGBucketCDF

end CryptoGames.SM.Construction

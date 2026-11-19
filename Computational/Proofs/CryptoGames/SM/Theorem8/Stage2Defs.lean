/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions

/-!
# Shared Stage-2 Authenticity Reduction Definitions for Theorem 8 (`SM/Theorem8.lean`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Shared definitions for the Stage-2 `canon`-bucket CKA authenticity reduction (`hooksCKABucket`,
`bucketAuthCfg`, `CKABucketEState`, `implCKABucket`, `runCKAAuthBucket`, `redCKAAuthBucket`) and
coin-averaged PRF-PRNG authenticity reductions (`hooksPRNGMain`, `isHonestHdrPRNG`,
`implPRNGForgedHdr`, `redPRNGAuthMain`, `redPRNGAuthForgedHdr`, `redPRNGAuthStage2`).-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

section Stage2Auth

/-- Hooks of Stage-2 `canon`-bucket `redCKAAuthBucket`: accepts forged CKA headers in any epoch
`t0` admissible for bucket `tL` (`lastLeakGuessAdmissible (2 + Δcka) tL t0`) when `γ` is local,
aborting if `γ` is still external. -/
@[expose] def hooksCKABucket (tL : Option ℕ) :
    Engine.Hooks (CKA.spec Γ CCoins T I) (CKAState T I) Γ T Sig SS RS M E CCoins
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

/-- Authenticity `Config` for Stage-2 `canon`-bucket `redCKAAuthBucket` at `tL`. -/
@[expose] def bucketAuthCfg (tL : Option ℕ) : Config M where
  deliverWin := false
  injectFull := fun t' => lastLeakGuessAdmissible (2 + Δcka) tL t'
  challAllowedIn := fun _ => false
  challMsg := fun _ => none

/-- State of `runCKAAuthBucket`: engine state paired with the recorded winning epoch `winEp`. -/
abbrev CKABucketEState (Γ T Sig SS RS M E I : Type) :=
  Engine.EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) × Option ℕ

/-- Oracle dispatcher of `redCKAAuthBucket` (matching `redCKAAuthBucketProg.handle`): runs
`hooksCKABucket` without `tStar`-specific `leakDoom`/`corrDoom` checks and records the first
winning `inject` epoch in `winEp`. -/
@[expose] def implCKABucket (tL : Option ℕ) :
    QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (CKA.AdversaryComp Γ CCoins T I)) :=
  let hk := hooksCKABucket cka prng fs Δcka tL
  let cfg := bucketAuthCfg (M := M) Δcka tL
  let i₀ : QueryImpl unifSpec
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (CKA.AdversaryComp Γ CCoins T I)) :=
    fun n => StateT.lift (query (spec := unifSpec + CKA.spec Γ CCoins T I) (.inl n))
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (CKA.AdversaryComp Γ CCoins T I)) :=
    fun ⟨P, m, r⟩ => do
      let (es0, winEp0) ← get
      if es0.abort || es0.g.win then return none
      match es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => return none
      | some s₁ =>
        let (res, h') ← StateT.lift ((Engine.vSend hk s₁ P (s₁.st P) m none r).run es0.h)
        match res with
        | none =>
          set ({ es0 with h := h', abort := true }, winEp0)
          return none
        | some (st', ct) =>
          let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
          set ({ es0 with g := s₁.record (2 + Δcka) P st' recE false, h := h' }, winEp0)
          return some ct
  let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (CKA.AdversaryComp Γ CCoins T I)) :=
    fun _ => pure none
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (CKA.AdversaryComp Γ CCoins T I)) :=
    fun x => do
      let (es0, winEp0) ← get
      let (out, es') ← StateT.lift ((Engine.deliverE hk fs.maxSkip cfg x).run es0)
      set (es', winEp0)
      return out
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (CKA.AdversaryComp Γ CCoins T I)) :=
    fun x => do
      let (es0, winEp0) ← get
      let wasWin := es0.g.win
      let (out, es') ← StateT.lift ((Engine.injectE hk (2 + Δcka) qep cfg x).run es0)
      let winEp' := if !wasWin && es'.g.win then some x.2.1.1 else winEp0
      set (es', winEp')
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (StateT (CKABucketEState Γ T Sig SS RS M E I) (CKA.AdversaryComp Γ CCoins T I)) :=
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
@[expose] def runCKAAuthBucket (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.AdversaryComp Γ CCoins T I
      (Option (Bool × CKABucketEState Γ T Sig SS RS M E I)) := do
  let (vs, h) ← (initCKA cka prng fs lam ⟨true, tL, 0⟩).run {}
  match vs with
  | none => return none
  | some (vA, vB) =>
    let g : Engine.Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let res ← (simulateQ (implCKABucket cka prng fs Δcka qep tL) A).run ({ g, h }, none)
    return some res

/-- Stage-2 `canon`-bucket CKA authenticity reduction `redCKAAuthBucket` (`tL : Option ℕ`),
matching `redCKAAuthBucketProg`. -/
@[expose] def redCKAAuthBucket (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from do
  match ← runCKAAuthBucket cka prng fs lam Δcka qep tL A with
  | none => return false
  | some (_, es, winEp) =>
    match winEp with
    | none => return false
    | some tWin =>
      return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

/-- Hooks of Stage-2 `G_main` (`forgedMode = false`) in `redPRNGAuthStage2`: rejects forged CKA
headers (`honest = none`) without querying `challPrf`. -/
@[expose] def hooksPRNGMain (mo : Mode) :
    Engine.Hooks (PRFPRNG.spec Sig I K) (PRNGState T Sig K) Γ T Sig SS RS M E CCoins
      Γ (Option Sig) SS RS :=
  { hooksPRNG cka prng fs mo with
    startRecv := fun _ _ t γ _ Tn => do
      let honest := match (← get).cache t with
        | some (Tc, σc, k) => if Tc = Tn then some (σc, k) else none
        | none => none
      match honest with
      | some (σc, k) => return some (some ((cka.receive γ Tn).1, σc, fs.initReceiver k))
      | none => return some none }

/-- Pure check whether header `hdr` at epoch `hdr.1` carries the cached honest CKA public value. -/
@[expose] def isHonestHdrPRNG (h : PRNGState T Sig K) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _, _), some Tn => Tc == Tn
  | _, _ => false

/-- Oracle dispatcher of the `forgedMode = true` (`G_forgedHdr`) branch of `redPRNGAuthStage2`:
runs `hooksPRNG` and suppresses wins caused by an honest CKA header on `inject`. -/
@[expose] def implPRNGForgedHdr (mo : Mode) :
    QueryImpl (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (Engine.EM (PRFPRNG.spec Sig I K) Γ T (Option Sig) SS RS M E (PRNGState T Sig K)) :=
  let hk := hooksPRNG cka prng fs mo
  let i₀ : QueryImpl unifSpec
      (Engine.EM (PRFPRNG.spec Sig I K) Γ T (Option Sig) SS RS M E (PRNGState T Sig K)) :=
    Engine.coinsE
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (Engine.EM (PRFPRNG.spec Sig I K) Γ T (Option Sig) SS RS M E (PRNGState T Sig K)) :=
    Engine.transmitE hk (2 + Δcka) qep mo.policy
  let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
      (Engine.EM (PRFPRNG.spec Sig I K) Γ T (Option Sig) SS RS M E (PRNGState T Sig K)) :=
    Engine.challE hk (2 + Δcka) qep mo.cfg mo.policy
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (Engine.EM (PRFPRNG.spec Sig I K) Γ T (Option Sig) SS RS M E (PRNGState T Sig K)) :=
    Engine.deliverE hk fs.maxSkip mo.cfg
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (RecvResult M))
      (Engine.EM (PRFPRNG.spec Sig I K) Γ T (Option Sig) SS RS M E (PRNGState T Sig K)) :=
    fun x => do
      let es0 : Engine.EState (Engine.VP Γ T (Option Sig) SS RS) M (Header T × E)
        (PRNGState T Sig K) ← get
      let wasWin := es0.g.win
      let out ← Engine.injectE hk (2 + Δcka) qep mo.cfg x
      let es' : Engine.EState (Engine.VP Γ T (Option Sig) SS RS) M (Header T × E)
        (PRNGState T Sig K) ← get
      if !wasWin && es'.g.win && isHonestHdrPRNG es0.h x.2.1 then
        set { es' with g := { es'.g with win := false } }
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (Engine.EM (PRFPRNG.spec Sig I K) Γ T (Option Sig) SS RS M E (PRNGState T Sig K)) :=
    Engine.corrE hk mo.policy
  HAdd.hAdd i₀ (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

/-- Honest-header (`forgedMode = false`) branch of `redPRNGAuthStage2`. -/
@[expose] def redPRNGAuthMain (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
  let mo : Mode := ⟨true, tL, t⟩
  match ← Engine.engRun (hooksPRNGMain cka prng fs mo) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy (initPRNG cka prng fs lam mo) {} false A with
  | none => return false
  | some (_, es) => return Engine.authOut (2 + Δcka) mo.policy es

/-- Forged-header (`forgedMode = true`) branch of `redPRNGAuthStage2`. -/
@[expose] def redPRNGAuthForgedHdr (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← (initPRNG cka prng fs lam mo).run {}
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Engine.Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    let (_, es) ← (simulateQ (implPRNGForgedHdr cka prng fs Δcka qep mo) A).run { g, h }
    return Engine.authOut (2 + Δcka) mo.policy es

/-- Stage-2 coin-averaged (`main` / `forgedHdr`) PRF-PRNG authenticity reduction
`redPRNGAuthStage2` at `(tL, t)`, matching `redPRNGAuthStage2Prog`. -/
@[expose] def redPRNGAuthStage2 (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
  let forgedMode ← sampleT Bool
  if forgedMode then
    redPRNGAuthForgedHdr cka prng fs lam Δcka qep tL t A
  else
    redPRNGAuthMain cka prng fs lam Δcka qep tL t A

end Stage2Auth

end CryptoGames.SM.Construction

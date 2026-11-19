/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions

/-!
# Shared Stage-2 Switch-Back Definitions for Theorem 12 (`SM/Theorem12.lean`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Shared definitions for the Stage-2 switch-back privacy reductions (`privAllGame`, `redCKAPrivU`,
`redFSPrivUni`, `redFSPrivUniCoin`) and internal hybrid reductions (`runCKAUUni`,
`redCKAPrivUUniAt`, `redCKAPrivUUniAll`) used across `SM/Theorem12/Stage2*.lean` and
`SM/Theorem12.lean`.-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM

section PrivAll

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
  [SampleableType Key] [SampleableType Coins]

/-- Unified (`tL`-free) privacy game at challenge epoch `t`: runs `Config.priv t` on a uniform bit
`b` and outputs `b == b'` whenever `canon t s` is an admissible last-leak guess for `(Δ, t)`, or a
fresh coin otherwise. -/
@[expose] def privAllGame (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', s) ← run sm Δ qep (Config.priv t) b A
  if lastLeakGuessAdmissible Δ (canon t s) t then return (b == b')
  else $ᵗ Bool

/-- Advantage (`boolBias`) of `A` in the unified (`tL`-free) privacy game `privAllGame` at epoch
`t`. -/
@[expose] noncomputable def privAllAdvantage (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[privAllGame sm Δ qep t A].boolBias

end PrivAll

end CryptoGames.SM

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

section Stage2SwitchBack

/-- Hook state for `redCKAPrivU`: CKA cache plus the uniform epoch-`tStar` FS-AEAD key sampled at
`startSend` of epoch `tStar`. -/
abbrev CKAUState (T I K : Type) := CKAState T I × Option K

/-- Update the CKA cache inside `CKAUState`. -/
@[expose] def cacheCU {T I K : Type} (t : ℕ) (x : T × I) :
    Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K) Unit :=
  modify fun s => ({ s.1 with cache := Function.update s.1.cache t (some x) }, s.2)

/-- Hooks of Stage-2 switch-back `redCKAPrivU`: identical to `hooksCKA`, except at `startSend` of
epoch `mo.tStar` a fresh uniform FS-AEAD key `kU ← $ᵗ K` is sampled and cached for the matching
honest receiver transition while the root state still advances via `(prng.up σ Ik).1`. -/
@[expose] def hooksCKAU (mo : Mode) :
    Engine.Hooks (CKA.spec Γ CCoins T I) (CKAUState T I K) Γ T Sig SS RS M E CCoins
      (Option Γ) Sig SS RS where
  startSend _ P t γv σ r := do
    let s0 ← get
    match γv with
    | some γ =>
      let coins ← match r with
        | some c => pure c
        | none => StateT.lift (sampleT CCoins)
      let c := cka.send γ coins
      cacheCU t (c.2.1, c.2.2)
      let p := prng.up σ c.2.2
      let (kEpoch, kOpt1) ←
        if t = mo.tStar then do
          let kU ← StateT.lift (sampleT K)
          pure (kU, some kU)
        else pure (p.2, s0.2)
      modify fun s => (s.1, kOpt1)
      return some (some c.1, c.2.1, p.1, fs.initSender kEpoch)
    | none =>
      let ans ← match r with
        | some c => StateT.lift (CKA.sendWithAdversaryCoinsQuery P c)
        | none =>
          if t = mo.tH then StateT.lift (CKA.challQuery P) else StateT.lift (CKA.sendQuery P)
      match ans with
      | none => return none
      | some (T', Ik) =>
        cacheCU t (T', Ik)
        let p := prng.up σ Ik
        let (kEpoch, kOpt1) ←
          if t = mo.tStar then do
            let kU ← StateT.lift (sampleT K)
            pure (kU, some kU)
          else pure (p.2, s0.2)
        modify fun s => (s.1, kOpt1)
        if mo.tH + Δcka ≤ t then
          match ← StateT.lift (CKA.corrQuery P) with
          | none => return none
          | some γ => return some (some γ, T', p.1, fs.initSender kEpoch)
        else return some (none, T', p.1, fs.initSender kEpoch)
  startRecv _ _ t γv σ Tn := do
    let s0 ← get
    let honest := match s0.1.cache t with
      | some (Tc, Ik) => if Tc = Tn then some Ik else none
      | none => none
    match honest with
    | some Ik =>
      let p := prng.up σ Ik
      let kEpoch :=
        if t = mo.tStar then
          match s0.2 with
          | none => p.2
          | some kU => kU
        else p.2
      return some (some (γv.map fun γ => (cka.receive γ Tn).1, p.1, fs.initReceiver kEpoch))
    | none =>
      if mo.auth && t = mo.tStar then
        match γv with
        | some γ =>
          let k := cka.receive γ Tn
          let p := prng.up σ k.2
          return some (some (some k.1, p.1, fs.initReceiver p.2))
        | none => return none
      else return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ P old new := do
    if old.tcur < new.tcur && old.γ.isNone then
      match ← StateT.lift (CKA.receiveQuery P) with
      | none => return none
      | some () =>
        if mo.tH + Δcka ≤ new.tcur then
          match ← StateT.lift (CKA.corrQuery P) with
          | none => return none
          | some γ => return some { new with γ := some γ }
        else return some new
    else return some new
  reveal _ P vp := do
    let γ? ← match vp.γ with
      | some γ => pure (some γ)
      | none => StateT.lift (CKA.corrQuery P)
    match γ? with
    | none => return none
    | some γ => return some (realParty vp γ vp.root vp.vS vp.vR)

/-- Initial state of `redCKAPrivU`: lifts `initCKA` into `CKAUState` with `kOpt = none`. -/
@[expose] def initCKAU (mo : Mode) :
    Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K)
      (Option (PartyState (Option Γ) T Sig SS RS × PartyState (Option Γ) T Sig SS RS)) := fun s => do
  let (vs, h') ← (initCKA cka prng fs lam mo).run s.1
  pure (vs, (h', none))

/-- Engine run of `redCKAPrivU` with engine bit `b`. -/
@[expose] def runCKAU (mo : Mode) (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.AdversaryComp Γ CCoins T I
      (Option (Bool × Engine.EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)
        (CKAUState T I K))) :=
  Engine.engRun (hooksCKAU cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
    (initCKAU cka prng fs lam mo) ({}, none) b A

/-- Stage-2 switch-back privacy CKA reduction `redCKAPrivU`: switches the CKA key at
`healEpoch tL` back from uniform to real while keeping challenge epoch `t`'s honest FS-AEAD key
uniform (`$ᵗ K`). -/
@[expose] def redCKAPrivU (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from do
  let b ← sampleT Bool
  match ← runCKAU cka prng fs lam Δcka qep ⟨false, tL, t⟩ b A with
  | none => sampleT Bool
  | some (b', es) => Engine.privOut (2 + Δcka) ⟨false, tL, t⟩ b b' es

/-- Unified (`tL`-free) engine policy for privacy at challenge epoch `t`: aborts on leaks `l` with
`t - (2 + Δcka) < l < t` (inadmissible pre-`t` leaks) or `t ≤ l` before `senderOf t` enters `t`. -/
@[expose] def polUni12 (Δcka t : ℕ) : Engine.Policy :=
  ⟨false, if 2 + Δcka ≤ t then some (t - (2 + Δcka)) else none, t⟩

/-- Unified (`tL`-free) privacy validity check at finish: `!es.abort` and
`lastLeakGuessAdmissible Δ (canon t es.g) t`. -/
@[expose] def privValidUni {VPt M C HS : Type} (Δ t : ℕ) (es : Engine.EState VPt M C HS) : Bool :=
  !es.abort && lastLeakGuessAdmissible Δ (canon t es.g) t

/-- Engine run of Stage-2 `tL`-free `redFSPrivUni` / `redFSPrivUniCoin` with engine bit `b`:
uses `hooksFS` at `⟨false, none, t⟩` (real CKA at all epochs, external FS-AEAD session at epoch `t`)
under the unified policy `polUni12 Δcka t`. -/
@[expose] def runFSUni (t : ℕ) (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × Engine.EState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E)
        (FSState T Sig K I SS RS E))) :=
  Engine.engRun (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0) (2 + Δcka) qep fs.maxSkip
    (Config.priv t) (polUni12 Δcka t) (initFS cka prng fs lam ⟨false, none, t⟩ 0) {} b A

/-- Stage-2 `tL`-free FS-AEAD privacy reduction `redFSPrivUni` at challenge epoch `t`: outputs the
SM adversary's guess on valid runs (`privValidUni (2 + Δcka) t es`) and a fresh coin otherwise. -/
@[expose] def redFSPrivUni (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  match ← runFSUni cka prng fs lam Δcka qep t false A with
  | none => sampleT Bool
  | some (b', es) => if privValidUni (2 + Δcka) t es then pure b' else sampleT Bool

/-- Stage-2 `tL`-free FS-AEAD coin reduction `redFSPrivUniCoin` at challenge epoch `t`: runs
`runFSUni` and outputs a fresh coin, so its FS-AEAD advantage is the probability of an FS-AEAD `win`
(accepted forgery in the challenge epoch-`t` session). -/
@[expose] def redFSPrivUniCoin (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← runFSUni cka prng fs lam Δcka qep t false A
  sampleT Bool

/-- Engine run of `hooksCKAU` at `⟨false, none, t⟩` under the unified policy `polUni12 Δcka t`. -/
@[expose] def runCKAUUni (t : ℕ) (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.AdversaryComp Γ CCoins T I
      (Option (Bool × Engine.EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)
        (CKAUState T I K))) :=
  Engine.engRun (hooksCKAU cka prng fs Δcka ⟨false, none, t⟩) (2 + Δcka) qep fs.maxSkip
    (Config.priv t) (polUni12 Δcka t) (initCKAU cka prng fs lam ⟨false, none, t⟩) ({}, none) b A

/-- `runCKAUUni` post-processed with the single-bucket `privOut (2 + Δcka) ⟨false, tL, t⟩`. -/
@[expose] def redCKAPrivUUniAt (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) : CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from do
  let b ← sampleT Bool
  match ← runCKAUUni cka prng fs lam Δcka qep t b A with
  | none => sampleT Bool
  | some (b', es) => Engine.privOut (2 + Δcka) ⟨false, tL, t⟩ b b' es

/-- `runCKAUUni` post-processed with the unified (`tL`-free) `privValidUni (2 + Δcka) t`. -/
@[expose] def redCKAPrivUUniAll (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) : CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from do
  let b ← sampleT Bool
  match ← runCKAUUni cka prng fs lam Δcka qep t b A with
  | none => sampleT Bool
  | some (b', es) =>
    if privValidUni (2 + Δcka) t es then pure (b == b') else sampleT Bool

end Stage2SwitchBack

end CryptoGames.SM.Construction

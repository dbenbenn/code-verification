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
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2Aux
import Computational.Proofs.ReductionDsl.Notation

/-!
# Stage-2 Multi-Session FS-AEAD Reductions & Bounds for Shifted `DeliverForge` (`B1` & `B2`, `[B7]`)

Defines `redFSAuthDFShiftedPaperMultiGenProg`, `redFSAuthDFShiftedPaperMultiProg`, and
`redFSAuthDFShiftedDir2PaperMultiProg` over `fsaeadMultiHeaderAdIface`, together with query bounds
and evaluation bridges.-/

public section

set_option autoImplicit false

open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2Aux (simulateQ_implECDFShiftedPaper_fsMulti_eq)
open CryptoGames (AEADScheme CKAScheme FSAEADScheme PRFPRNG)
open CryptoGames.CKA (ckaSMQDF)
open CryptoGames.PRFPRNG (prngOps prngSMCodecDF prngSig)
open CryptoGames.SM.Construction (FSMultiSpec FSMultiState Header Mode PartyState finishFSMultiE fsClamp fsHdrDecWt fsMultiEsTy fsaeadMultiHeaderAdIface hooksFSMulti hooksFSMultiC initFSMultiEStateC initFSMultiRaw)
open CryptoGames.SM.Engine (EState TComp VP authOut challEC commitEC corrECShiftedPaper deliverEC deliverForgeEC deliverForgeECB1 deliverForgeECGen implECDFShiftedPaperGen implECShiftedPaperGen injectEC injectECB1 injectECGen modeCfgEC transmitEC vRecvC vRecvStep1C vSendC vSendStep1C)
open ReductionDsl (CostedReduction Expr handlerImpl)

namespace Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2

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

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "mEsTy" => fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E

/-- Costed Stage-2 multi-session shifted paper FS-AEAD reduction parameterized by `authH la : Bool`.
When `authH = true`, models `B2` (`DeliverForgePaperShifted`, `mo = ⟨true, some (l - 1), tStar⟩`);
when `authH = false` and `Δcka = 0`, models `B1` (`DeliverForgeDir2PaperShifted`,
`mo = ⟨false, some (l - 1), tStar⟩`, `b1 = true`, `mo' = ⟨true, some (l - 1), tStar⟩`). -/
@[expose] def redFSAuthDFShiftedPaperMultiGenProg
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) :
    CostedReduction OO IIM (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool where
  σ := mEsTy
  init := rdsl [_] do
    es ← initFSMultiEStateC L (raw ⟨authH, some (l - 1), tStar⟩) false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFShiftedPaperGen (raw (!authH))
      (raw (hooksFSMultiC L B Δcka ⟨authH, some (l - 1), tStar⟩ false la))
      L l (raw (2 + Δcka)) qep maxSkip tStar
      (raw (modeCfgEC OO ⟨true, some (l - 1), tStar⟩))
      (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return (finishFSMultiE L (raw (2 + Δcka)) (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) la st)

local notation "redFSMultiGen" =>
  redFSAuthDFShiftedPaperMultiGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)

/-- Costed Stage-2 multi-session `redFSAuthDFShiftedPaper` program (`B2`, `authH = true`). -/
abbrev redFSAuthDFShiftedPaperMultiProg
    (L B Δcka qep maxSkip l tStar : ℕ) (la : Bool) :
    CostedReduction OO IIM (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  redFSMultiGen L B Δcka qep maxSkip l tStar true la

/-- Costed Stage-2 multi-session `redFSAuthDFShiftedDir2Paper` program (`B1`, `Δcka = 0, authH = false`). -/
abbrev redFSAuthDFShiftedDir2PaperMultiProg
    (L B qep maxSkip l tStar : ℕ) (la : Bool) :
    CostedReduction OO IIM (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  redFSMultiGen L B 0 qep maxSkip l tStar false la

@[simp] theorem implECDFShiftedPaper_hooksFSMultiC_queries (b1 : Bool)
    (L B l Δcka qep maxSkip tStar : ℕ) (mo mo' : Mode) (gMain la : Bool) {Γ'}
    (es : Expr OO Γ' mEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen b1 (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      L l (2 + Δcka) qep maxSkip tStar (modeCfgEC OO mo') mo'.policy es q).queries
      (fun _ => 1) (fun _ => 0) = if la then 1 else 2 := by
  cases b1 <;> cases la <;>
    simp [implECDFShiftedPaperGen, implECShiftedPaperGen, transmitEC, challEC,
      deliverEC, injectECGen, injectEC, injectECB1, corrECShiftedPaper, deliverForgeECGen,
      deliverForgeEC, deliverForgeECB1, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
      hooksFSMultiC, CryptoGames.SM.Construction.fsMultiCommitC,
      CryptoGames.SM.Construction.fsMultiRevealC, ReductionDsl.Comp.queries]

@[simp] theorem implECDFShiftedPaper_hooksFSMultiC_decQueries (b1 : Bool)
    (L B l Δcka qep maxSkip tStar : ℕ) (mo mo' : Mode) (gMain la : Bool) {Γ'}
    (es : Expr OO Γ' mEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen b1 (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      L l (2 + Δcka) qep maxSkip tStar (modeCfgEC OO mo') mo'.policy es q).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  cases b1 <;> cases la <;>
    simp [implECDFShiftedPaperGen, implECShiftedPaperGen, transmitEC, challEC,
      deliverEC, injectECGen, injectEC, injectECB1, corrECShiftedPaper, deliverForgeECGen,
      deliverForgeEC, deliverForgeECB1, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
      hooksFSMultiC, CryptoGames.SM.Construction.fsMultiFsRecvC,
      CryptoGames.SM.Construction.fsMultiCommitC, CryptoGames.SM.Construction.fsMultiRevealC,
      CryptoGames.SM.Construction.fsHdrDecWt, ReductionDsl.Comp.queries]

@[simp] theorem redFSAuthDFShiftedPaperMultiGenProg_totalQueries_eq
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) (q : ℕ) :
    (redFSMultiGen L B Δcka qep maxSkip l tStar authH la).totalQueries
      (fun _ => 1) (fun _ => 0) q = q * (if la then 1 else 2) := by
  simp [ReductionDsl.CostedReduction.totalQueries, redFSAuthDFShiftedPaperMultiGenProg,
    initFSMultiEStateC, ReductionDsl.Comp.queries]

theorem redFSAuthDFShiftedPaperMultiGenProg_totalQueries
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) (q : ℕ) :
    (redFSMultiGen L B Δcka qep maxSkip l tStar authH la).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q * 2 := by
  rw [redFSAuthDFShiftedPaperMultiGenProg_totalQueries_eq]
  (cases la <;> simp); omega

@[simp] theorem redFSAuthDFShiftedPaperMultiGenProg_totalDecQueries
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) (q : ℕ) :
    (redFSMultiGen L B Δcka qep maxSkip l tStar authH la).totalQueries
      fsHdrDecWt (fun _ => 0) q = q := by
  simp [ReductionDsl.CostedReduction.totalQueries, redFSAuthDFShiftedPaperMultiGenProg,
    initFSMultiEStateC, ReductionDsl.Comp.queries]

/-- Shallow Stage-2 multi-session shifted paper runner over `FSMultiSpec`. -/
@[expose] def runFSMultiDFShiftedPaper
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (l Δcka qep tStar : ℕ)
    (mo mo' : Mode) (la b : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E)
      (Bool × EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
        (FSMultiState T RSt K I E)) := do
  let es₀ ← initFSMultiRaw cka prng fs lam mo b
  (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
    (hooksFSMulti cka prng fs Δcka mo false la) (2 + Δcka) qep fs.maxSkip tStar mo'.cfg mo'.policy)
    A).run es₀

/-- Shallow Stage-2 multi-session shifted paper FS-AEAD reduction (`authH la : Bool`). -/
@[expose] def redFSAuthDFShiftedPaperMultiGen
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l tStar : ℕ)
    (authH la : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool := do
  let (_, es) ← runFSMultiDFShiftedPaper (!authH) cka prng fs lam l Δcka qep tStar
    ⟨authH, some (l - 1), tStar⟩ ⟨true, some (l - 1), tStar⟩ la false A
  return (if la then es.h.lfWin else authOut (2 + Δcka) (⟨true, some (l - 1), tStar⟩ : Mode).policy es)

/-- Shallow Stage-2 multi-session `B2` (`authH = true`) shifted paper FS-AEAD reduction. -/
abbrev redFSAuthDFShiftedPaperMulti
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l tStar : ℕ) (la : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool :=
  redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l tStar true la A

/-- Shallow Stage-2 multi-session `B1` (`Δcka = 0, authH = false`) shifted paper FS-AEAD reduction. -/
abbrev redFSAuthDFShiftedDir2PaperMulti
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l tStar : ℕ) (la : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool :=
  redFSAuthDFShiftedPaperMultiGen cka prng fs lam 0 qep l tStar false la A



/-- Evaluation bridge for `redFSAuthDFShiftedPaperMultiGenProg` on `fsClamp B fs`. -/
theorem redFSAuthDFShiftedPaperMultiGenProg_eval_clamp
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L B B_q Δcka qep l tStar : ℕ) (authH la : Bool)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSMultiGen L B Δcka qep fs.maxSkip l tStar authH la).eval (fun _ => A) () =
      redFSAuthDFShiftedPaperMultiGen cka prng (fsClamp B fs) lam Δcka qep l tStar authH la A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have hInit := CryptoGames.SM.Construction.initFSMultiEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨authH, some (l - 1), tStar⟩ (.bool false)
    (ReductionDsl.Env.cons (t := (.unit : ReductionDsl.Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthDFShiftedPaperMultiGenProg CostedReduction.impl
    redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  dsimp only
  rw [CryptoGames.SM.Engine.eval_bind, hInit]
  simp only [bind_map_left, CryptoGames.SM.Engine.eval_ret, Expr.eval, Expr.v0,
    ReductionDsl.Env.get_cons_zero, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSMultiRaw cka prng (fsClamp B fs) lam ⟨authH, some (l - 1), tStar⟩ false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := CryptoGames.SM.Construction.initFSMultiRaw_inv cka prng (fsClamp B fs) lam
    ⟨authH, some (l - 1), tStar⟩ false hqB hB1 hBB es₀ hes₀
  have ⟨hSim, hPost⟩ := simulateQ_implECDFShiftedPaper_fsMulti_eq (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC) (!authH) cka prng (fsClamp B fs) L B B_q l (2 + Δcka)
    Δcka qep tStar ⟨authH, some (l - 1), tStar⟩ ⟨true, some (l - 1), tStar⟩ false la
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend heqT heqI heqM heqE hDefaultE
    hSampCCoins hSampI hSampK (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [Expr.v0] at hSim; rw [hms] at hSim; rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨bOut, es'⟩ hmem => ?_
  have ⟨hInv', _⟩ := hPost (bOut, es') hmem
  have hFin := CryptoGames.SM.Construction.finishFSMultiE_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L B_q (2 + Δcka) (⟨true, some (l - 1), tStar⟩ : Mode).policy la .v0
    (ReductionDsl.Env.cons (CryptoGames.SM.Engine.esEnc
        (CryptoGames.SM.Construction.fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins)
          (I := I) (KR := KR) (K := K) (M := M) (E := E))
        (CryptoGames.SM.Construction.fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins)
          (KR := KR) (SS := SS) (RS := RS) (M := M)) es')
      (ReductionDsl.Env.cons (t := (.bool : ReductionDsl.Ty S)) bOut .nil))
    es' hInv'.sm (by simp [Expr.v0, Expr.eval])
  dsimp only [Prod.map, id, Expr.v0] at hFin ⊢; rw [hFin]
section FsClampMultiHelpers

set_option linter.unusedSectionVars false
open _root_.CryptoGames.SM (Config)
open _root_.CryptoGames.SM.Construction (FSVROkMultiStep hooksFSMulti_vrInv_fromAEADPRG
  mkParties vRecv_fsClamp_multi_eq)
open _root_.CryptoGames.SM.Construction.DeliverForge (corrEShiftedPaper deliverForgeE deliverForgeEB1
  implEDFShiftedPaperGen injectEB1)
open _root_.CryptoGames.SM.Engine (Policy RSReach SMEngineInv SMVRInv challE coinsE deliverE deliverForgeEGen
  implEDFShiftedPaper_inv implEDFShiftedPaper_vrInv injectE injectEGen run_liftH_bind transmitE)
private theorem implEDFShiftedPaper_fsClamp_multi_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK))
    (maxSkip B B_q q l Δ Δcka qep tStar : ℕ) (cfg : Config M) (π : Policy)
    (mo : Mode) (gMain la : Bool) (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K ⊕ ℕ)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiState T RSt K I (ℕ × C)))
    (t : (CryptoGames.SM.specDF (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q (q + 1) es.g) : (implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (fsClamp B (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
        Δ qep maxSkip tStar cfg π (.inr t)).run es = (implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        Δ qep maxSkip tStar cfg π (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE CryptoGames.SM.Engine.vSend hooksFSMulti fsClamp; rfl
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es = (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    unfold challE CryptoGames.SM.Engine.vSend hooksFSMulti fsClamp; rfl
  · change (deliverE _ maxSkip cfg (P, c)).run es = (deliverE _ maxSkip cfg (P, c)).run es
    unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind]
        rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
          es.g P (es.g.st P) c (some r) es.h (hVR P)]; rfl
  · cases b1
    · change (injectE _ Δ qep cfg (P, c)).run es = (injectE _ Δ qep cfg (P, c)).run es
      unfold injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
      · simp [href]
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
        rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
          es.g P (es.g.st P) c none es.h (hVR P)]; rfl
    · change (injectEB1 _ qep tStar cfg (P, c)).run es = (injectEB1 _ qep tStar cfg (P, c)).run es
      unfold injectEB1; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
      · simp [href]
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
        rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
          es.g P (es.g.st P) c none es.h (hVR P)]; rfl
  · change (corrEShiftedPaper l _ π P).run es = (corrEShiftedPaper l _ π P).run es
    unfold corrEShiftedPaper hooksFSMulti fsClamp; rfl
  · cases b1
    · change (deliverForgeE _ Δ qep cfg (P, c, c')).run es = (deliverForgeE _ Δ qep cfg (P, c, c')).run es
      unfold deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win)
      · simp [hab]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases htr : es.g.inTransit P.other c with _ | r
        · rfl
        · dsimp only; split_ifs
          · rfl
          · simp only [run_liftH_bind]
            rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
              es.g P (es.g.st P) c' none es.h (hVR P)]; rfl
    · change (deliverForgeEB1 _ qep tStar cfg (P, c, c')).run es = (deliverForgeEB1 _ qep tStar cfg (P, c, c')).run es
      unfold deliverForgeEB1; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win)
      · simp [hab]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases htr : es.g.inTransit P.other c with _ | r
        · rfl
        · dsimp only; split_ifs
          · rfl
          · simp only [run_liftH_bind]
            rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
              es.g P (es.g.st P) c' none es.h (hVR P)]; rfl
private theorem simulateQ_implEDFShiftedPaper_fsClamp_multi_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK))
    (maxSkip L B B_q l Δ Δcka qep tStar : ℕ) (cfg : Config M) (π : Policy)
    (mo : Mode) (gMain la : Bool) (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + CryptoGames.SM.specDF
      (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
        (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))) α} {q : ℕ}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.specDF
      (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
        (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C)))) q)
    (es : EState (VP Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K ⊕ ℕ)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiState T RSt K I (ℕ × C)))
    (hInv : SMEngineInv L B_q q es.g) (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q q es.g) :
    (simulateQ (implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (fsClamp B (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
        Δ qep maxSkip tStar cfg π) oa).run es = (simulateQ (implEDFShiftedPaperGen b1 l
        (hooksFSMulti cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        Δ qep maxSkip tStar cfg π) oa).run es := by
  let impl1 := implEDFShiftedPaperGen b1 l
    (hooksFSMulti cka prng (fsClamp B (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
    Δ qep maxSkip tStar cfg π
  let impl2 := implEDFShiftedPaperGen b1 l
    (hooksFSMulti cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
    Δ qep maxSkip tStar cfg π
  change (simulateQ impl1 oa).run es = (simulateQ impl2 oa).run es
  induction oa using OracleComp.inductionOn generalizing q es with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa; rcases hoa with ⟨hq0, hmx⟩
    rw [simulateQ_bind, simulateQ_query, StateT.run_bind, simulateQ_bind, simulateQ_query, StateT.run_bind]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rcases qy with n | t_df
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hInl1 : (impl1 (.inl n)).run es = (coinsE n).run es := rfl
      have hInl2 : (impl2 (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, _, rfl⟩ := hmem; exact ih u (hmx u) _ hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hStep : (impl1 (.inr t_df)).run es = (impl2 (.inr t_df)).run es :=
        implEDFShiftedPaper_fsClamp_multi_eq b1 cka prng ae G maxSkip B B_q q' l Δ Δcka qep
          tStar cfg π mo gMain la hB es t_df hVR
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      exact ih u (hmx u) es'
        (implEDFShiftedPaper_inv b1 (hooksFSMulti cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka mo gMain la) l cfg π es t_df hInv (u, es') hmem)
        (implEDFShiftedPaper_vrInv b1 (hooksFSMulti cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
          Δcka mo gMain la) (hooksFSMulti_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka mo gMain la)
          l cfg π es t_df hInv hVR (u, es') hmem)
end FsClampMultiHelpers

/-- `fsClamp B` removal for `redFSAuthDFShiftedPaperMultiGen` on `FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFShiftedPaperMultiGen_fsClamp_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep l tStar : ℕ) (lam : I) (authH la : Bool)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    redFSAuthDFShiftedPaperMultiGen cka prng (fsClamp B (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka qep l tStar authH la A =
      redFSAuthDFShiftedPaperMultiGen cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep l tStar authH la A := by
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.specDF
      (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
        (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C)))) qAdv := by
    refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  have hInitEq : initFSMultiRaw cka prng (fsClamp B (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      lam ⟨authH, some (l - 1), tStar⟩ false =
      initFSMultiRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
        lam ⟨authH, some (l - 1), tStar⟩ false := rfl
  have hms1 : (fsClamp B (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)).maxSkip = maxSkip := rfl
  have hms2 : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  simp only [bind_assoc, hInitEq, hms1, hms2]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have ⟨hInv₀, hVR₀⟩ : CryptoGames.SM.Engine.SMEngineInv L B_q qAdv es₀.g ∧
      CryptoGames.SM.Engine.SMVRInv (CryptoGames.SM.Construction.FSVROkMultiStep maxSkip) B_q qAdv es₀.g := by
    unfold initFSMultiRaw at hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kr, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kc, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨optIdx, h₂⟩, _, hes₀⟩ := hes₀
    simp only [support_pure, Set.mem_singleton_iff] at hes₀; subst hes₀
    refine ⟨(CryptoGames.SM.Engine.SMEngineInv.init _ false hB1 hBB).mono hqB, fun P t₀ v hv => ?_⟩
    cases P <;> simp only [CryptoGames.SM.Construction.mkParties] at hv
    · by_cases ht0 : t₀ = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv; subst hv
        rcases optIdx with _ | sIdx
        · exact (CryptoGames.SM.Engine.RSReach.init ae G maxSkip k).mono (Nat.zero_le _)
        · trivial
      · simp [ht0] at hv
    · cases hv
  rw [simulateQ_implEDFShiftedPaper_fsClamp_multi_eq (!authH) cka prng ae G maxSkip L B B_q l
    (2 + Δcka) Δcka qep tStar (⟨true, some (l - 1), tStar⟩ : Mode).cfg
    (⟨true, some (l - 1), tStar⟩ : Mode).policy ⟨authH, some (l - 1), tStar⟩ false la hFsB hA'
    es₀ hInv₀ hVR₀]
/-- Combined evaluation + `fsClamp` removal bridge for `redFSAuthDFShiftedPaperMultiGenProg` on
`FSAEAD.fromAEADPRG`. -/
theorem redFSAuthDFShiftedPaperMultiGenProg_eval_fromAEADPRG {MK C : Type}
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → CryptoGames.FSAEAD.RatchetSenderState K}
    {fsInitReceiver : K → CryptoGames.FSAEAD.RatchetReceiverState K MK}
    {fsSend : CryptoGames.FSAEAD.RatchetSenderState K → Header T → M →
      CryptoGames.FSAEAD.RatchetSenderState K × (ℕ × C)}
    {fsReceive : CryptoGames.FSAEAD.RatchetReceiverState K MK → Header T → (ℕ × C) →
      Option (CryptoGames.FSAEAD.RatchetReceiverState K MK × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : (ℕ × C) → (ℕ × C) → Bool}
    {lam : I} {defaultE : ℕ × C}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep l tStar : ℕ) (authH la : Bool)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).initSender)
    (hFsInitR : fsInitReceiver = (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).initReceiver)
    (hFsSend : fsSend = (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).send)
    (hFsRecv : fsReceive = (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthDFShiftedPaperMultiGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip l tStar authH la).eval (fun _ => A) () =
      redFSAuthDFShiftedPaperMultiGen cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep l tStar authH la A := by
  have heqE' : eqE = fun x1 x2 : ℕ × C => @BEq.beq (ℕ × C) instBEqOfDecidableEq x1 x2 := by
    cases heqE
    funext ⟨a1, c1⟩ ⟨a2, c2⟩
    by_cases ha : a1 = a2 <;> by_cases hc : c1 = c2 <;> simp [BEq.beq, ha, hc]
  have h1 := redFSAuthDFShiftedPaperMultiGenProg_eval_clamp (lam := lam) cka prng
    (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka qep l tStar authH la
    hInitA hInitB hSend hRecv hPrngInit hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE' hDefaultE hSampKR hSampKC hSampCCoins hSampI hSampK
    hB1 hBB A qAdv hA hqB
  have hms : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms] at h1
  exact h1.trans (redFSAuthDFShiftedPaperMultiGen_fsClamp_fromAEADPRG cka prng ae G maxSkip
    L B B_q Δcka qep l tStar lam authH la hFsB hB1 hBB A qAdv hA hqB)
end HooksFSMultiCDFShiftedPaper

end Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2

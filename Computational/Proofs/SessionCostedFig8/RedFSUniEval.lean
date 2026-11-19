/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedPRNG

public section

set_option autoImplicit false

open CryptoGames (CKAScheme FSAEADScheme PRFPRNG)
open CryptoGames.CKA (ckaSamplers)
open CryptoGames.PRFPRNG (fsaeadHeaderAdIface prngOps prngSMCodec prngSamplers prngSig)
open CryptoGames.SM (and_eval letE_eval not_eval validGuessE_eval)
open CryptoGames.SM.Construction (FSEngineInv FSHBounded FSState Header Mode PartyState SchemeAdversary fsClamp fsHsEnc hooksFS hooksFSC hooksFSC_agrees hooksFSL implE_fs_inv implE_hooksFSL_eq implUniEC initFS initFSEStateC_eval initFSRaw initFSRaw_inv polUni12 privValidUni privValidUniE redFSPrivUni redFSPrivUniCoin redFSPrivUniCoinProg redFSPrivUniProg redFsPolUni runFSUni sampleT)
open CryptoGames.SM.Engine (EState VP cCanonE_eval coinsE engRun esAbort esEnc esG eval_bind eval_ite eval_ret implE modeCfgEC modeCfgEC_agrees rdec_implEC_eval vpTblEnc)

namespace Computational.Proofs.SessionCostedFig8.RedFSUniEval

open OracleComp OracleSpec

section AbstractUniFS

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_fs" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_fs" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II_fs" =>
  fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK

theorem runFSUni_eq_bind_initFSRaw
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep t : ℕ) (b : Bool)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    runFSUni cka prng fs lam Δcka qep t b A =
      (do
        let es₀ ← initFSRaw cka prng fs lam ⟨false, none, t⟩ 0 b
        let res ←
          (simulateQ (implE (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
            (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Config.priv t) (polUni12 Δcka t)) A).run es₀
        pure (some res)) := by
  unfold runFSUni engRun initFS initFSRaw
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun ⟨⟨_, _, _⟩, _⟩ => bind_congr fun ⟨_, _⟩ => rfl

theorem privValidUniE_eval
    {Γ'} (L Δ t : ℕ)
    (es' : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (hLeaks : es'.g.leaks.length ≤ L)
    (ρ : ReductionDsl.Env Γ') :
    let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
      (γvT := .base .γ) (svT := .base .sig)
      (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
    (privValidUniE
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L Δ t .v0).eval
      (ReductionDsl.Env.cons (esEnc vpE fsHsEnc es') ρ) =
    privValidUni Δ t es' := by
  intro vpE
  unfold privValidUniE privValidUni
  rw [letE_eval]
  simp only [and_eval, not_eval, validGuessE_eval]
  have hAb :
      (esAbort (O' := OO_fs) .v0).eval
        (ReductionDsl.Env.cons ((.v0 : ReductionDsl.Expr OO_fs _ _).eval
          (ReductionDsl.Env.cons (esEnc vpE fsHsEnc es') ρ))
          (ReductionDsl.Env.cons (esEnc vpE fsHsEnc es') ρ)) = es'.abort := rfl
  have hCan := cCanonE_eval (vpEncFn := vpE) (O' := OO_fs) L (.nat t) (esG .v0)
    (ReductionDsl.Env.cons ((.v0 : ReductionDsl.Expr OO_fs _ _).eval
      (ReductionDsl.Env.cons (esEnc vpE fsHsEnc es') ρ))
      (ReductionDsl.Env.cons (esEnc vpE fsHsEnc es') ρ))
    es'.g hLeaks rfl
  rw [hAb, hCan]
  rfl

private theorem simulateQ_implUniEC_abs_fs_eq_inv
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep i : ℕ)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', idx, m) => (rs', min idx B, m)) =
        fs.receive rs hdr e) :
    let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
      (γvT := .base .γ) (svT := .base .sig)
      (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)))
        qAdv →
      ∀ (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
          (FSState T RSt K I SS RS E)),
        FSEngineInv L B_q qAdv es →
        ((simulateQ
            (ReductionDsl.handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
              (implUniEC
                (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive)
                (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive)
                (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK)
                L B Δcka qep fs.maxSkip i .v0 .v1)) oa).run
            (esEnc vpE fsHsEnc es) =
          (Prod.map id (esEnc vpE fsHsEnc) <$>
            (simulateQ (implE (hooksFS cka prng fs Δcka ⟨false, none, i⟩ 0)
              (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Config.priv i) (polUni12 Δcka i)) oa).run es)) ∧
        (∀ res ∈ support ((simulateQ (implE (hooksFS cka prng fs Δcka ⟨false, none, i⟩ 0)
              (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Config.priv i) (polUni12 Δcka i)) oa).run es),
            FSEngineInv L B_q 0 res.2) := by
  intro vpE
  let mo₀ : Mode := ⟨false, none, i⟩
  have hCfg : mo₀.cfg (M := M) = CryptoGames.SM.Config.priv i := rfl
  have hHk := hooksFSC_agrees
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka mo₀ 0 hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqE hSampCCoins hSampI hSampK hFsRecvB
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hres
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres
    exact CryptoGames.SM.Construction.FSEngineInv.mono (Nat.zero_le _) hInv
  | query_bind q mx ih =>
    intro qAdv hq es hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    cases q with
    | inl n =>
      have hCoinL :
          ((ReductionDsl.handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implUniEC
              (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive)
              (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
              (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka qep fs.maxSkip i .v0 .v1)) (.inl n)).run
            (esEnc vpE fsHsEnc es) =
          (fun u => (u, esEnc vpE fsHsEnc es)) <$>
            query (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        simp [ReductionDsl.handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (implE (hooksFS cka prng fs Δcka mo₀ 0) (2 + Δcka) qep fs.maxSkip
            (CryptoGames.SM.Config.priv i) (polUni12 Δcka i) (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        change (coinsE n).run es = _
        simp [coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      refine ⟨?_, ?_⟩
      · rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
          hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
        exact bind_congr fun u => (ih u (hq.2 u) es hInv).1
      · intro res hres
        rw [OracleComp.run_simulateQ_query_bind, hCoinR, bind_map_left, mem_support_bind_iff] at hres
        obtain ⟨u, _, hres⟩ := hres
        exact (ih u (hq.2 u) es hInv).2 res hres
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [ReductionDsl.isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins
            (Header T × E))) m := by
        intro u; simpa [ReductionDsl.isGameQuery] using hq.2 u
      have hHB : FSHBounded L es.h := hInv.toFSHBounded
      let codec0 := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E
      let ρ₀ := ReductionDsl.Env.cons (esEnc vpE fsHsEnc es)
        (ReductionDsl.Env.cons (codec0.qenc t) .nil)
      have hStep :
          ((ReductionDsl.handlerImpl (C := codec0)
            (implUniEC
              (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive)
              (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
              (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka qep fs.maxSkip i .v0 .v1)) (.inr t)).run
            (esEnc vpE fsHsEnc es) =
          Prod.map id (esEnc vpE fsHsEnc) <$>
            (implE (hooksFS cka prng fs Δcka mo₀ 0) (2 + Δcka) qep fs.maxSkip
              (CryptoGames.SM.Config.priv i) (polUni12 Δcka i) (.inr t)).run es := by
        have hStepL := rdec_implEC_eval hDefaultE
          fsHsEnc (FSHBounded L)
          (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka mo₀ 0)
          (hooksFSL cka prng fs L Δcka mo₀ 0) hHk
          L (2 + Δcka) qep fs.maxSkip
          (modeCfgEC OO_fs mo₀)
          mo₀.cfg (modeCfgEC_agrees mo₀)
          heqT heqM heqE (polUni12 Δcka i) .v0 .v1 ρ₀
          es t hHB hInv.sm.toBoundedEngine (fun _ _ _ _ => trivial) rfl rfl
        rw [implE_hooksFSL_eq cka prng fs L (2 + Δcka) qep fs.maxSkip
          mo₀.cfg (polUni12 Δcka i) Δcka mo₀ 0 es t hInv.vR_none_of_le_L, hCfg] at hStepL
        unfold implUniEC
        dsimp only [vpE, codec0, ρ₀, mo₀, redFsPolUni, polUni12] at hStepL ⊢
        simp only [ReductionDsl.handlerImpl, StateT.run_mk, prngSMCodec, ← hStepL,
          map_eq_bind_pure_comp, Function.comp_def]
      refine ⟨?_, ?_⟩
      · rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
          hStep, bind_map_left, map_bind]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_
        have hInv₁ := implE_fs_inv cka prng fs (CryptoGames.SM.Config.priv i) (polUni12 Δcka i)
          Δcka mo₀ 0 es t hInv (u, es₁) hmem
        exact (ih u (hqm u) es₁ hInv₁).1
      · intro res hres
        rw [OracleComp.run_simulateQ_query_bind, mem_support_bind_iff] at hres
        obtain ⟨⟨u, es₁⟩, hmem, hres⟩ := hres
        have hInv₁ := implE_fs_inv cka prng fs (CryptoGames.SM.Config.priv i) (polUni12 Δcka i)
          Δcka mo₀ 0 es t hInv (u, es₁) hmem
        exact (ih u (hqm u) es₁ hInv₁).2 res hres

theorem redFSPrivUniProg_eval_clamp_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep i : ℕ)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSPrivUniProg
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip i).eval (fun _ => A) () =
      redFSPrivUni cka prng (fsClamp B fs) lam Δcka qep i A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)))
      qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have hBit : ∀ {Γ'} (ρ' : ReductionDsl.Env Γ'),
      (@ReductionDsl.Comp.sample _ _ _ OO_fs II_fs _ CryptoGames.CKA.CKASamp.bit .unit).eval ρ' =
        (sampleT Bool : CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E Bool) := by
    intro Γ' ρ'
    simp only [ReductionDsl.Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
    exact CryptoGames.SM.Engine.RedPRNG.liftP_eq_liftM II_fs (fun _ => rfl) ($ᵗ Bool)
  have hInit := initFSEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs)
    hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨false, none, i⟩ 0 (.bool false)
    (ReductionDsl.Env.cons (t := (.unit : ReductionDsl.Ty S_fs)) () .nil)
  unfold ReductionDsl.CostedReduction.eval redFSPrivUniProg ReductionDsl.CostedReduction.impl
    redFSPrivUni
  dsimp only
  rw [eval_bind, hInit, runFSUni_eq_bind_initFSRaw]
  simp only [bind_map_left, eval_ret, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
    ReductionDsl.Env.get_cons_zero, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSRaw cka prng (fsClamp B fs) lam ⟨false, none, i⟩ 0 false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (fsClamp B fs)
    lam ⟨false, none, i⟩ 0 false hqB hB1 hBB es₀ hes₀
  obtain ⟨hSim, hSimInv⟩ := simulateQ_implUniEC_abs_fs_eq_inv
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep i
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [ReductionDsl.Expr.v0] at hSim
  rw [hms] at hSim
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  have hInv' := hSimInv (b', es') hes'
  have hLeaks : es'.g.leaks.length ≤ L := hInv'.sm.toBoundedEngine.leaks_le
  have hPV := privValidUniE_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L (2 + Δcka) i es' hLeaks
    (ReductionDsl.Env.cons (t := (.bool : ReductionDsl.Ty S_fs)) b' .nil)
  dsimp only [Prod.map, id, ReductionDsl.Expr.v0] at hPV ⊢
  rw [eval_ite, hPV]
  split_ifs
  · rfl
  · exact hBit _

theorem redFSPrivUniCoinProg_eval_clamp_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep i : ℕ)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSPrivUniCoinProg
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip i).eval (fun _ => A) () =
      redFSPrivUniCoin cka prng (fsClamp B fs) lam Δcka qep i A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)))
      qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have hBit : ∀ {Γ'} (ρ' : ReductionDsl.Env Γ'),
      (@ReductionDsl.Comp.sample _ _ _ OO_fs II_fs _ CryptoGames.CKA.CKASamp.bit .unit).eval ρ' =
        (sampleT Bool : CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E Bool) := by
    intro Γ' ρ'
    simp only [ReductionDsl.Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
    exact CryptoGames.SM.Engine.RedPRNG.liftP_eq_liftM II_fs (fun _ => rfl) ($ᵗ Bool)
  have hInit := initFSEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs)
    hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨false, none, i⟩ 0 (.bool false)
    (ReductionDsl.Env.cons (t := (.unit : ReductionDsl.Ty S_fs)) () .nil)
  unfold ReductionDsl.CostedReduction.eval redFSPrivUniCoinProg ReductionDsl.CostedReduction.impl
    redFSPrivUniCoin
  dsimp only
  rw [eval_bind, hInit, runFSUni_eq_bind_initFSRaw]
  simp only [bind_map_left, eval_ret, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0,
    ReductionDsl.Env.get_cons_zero, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSRaw cka prng (fsClamp B fs) lam ⟨false, none, i⟩ 0 false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (fsClamp B fs)
    lam ⟨false, none, i⟩ 0 false hqB hB1 hBB es₀ hes₀
  obtain ⟨hSim, _⟩ := simulateQ_implUniEC_abs_fs_eq_inv
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep i
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [ReductionDsl.Expr.v0] at hSim
  rw [hms] at hSim
  rw [hSim, bind_map_left]
  exact bind_congr fun _ => hBit _

end AbstractUniFS

end Computational.Proofs.SessionCostedFig8.RedFSUniEval

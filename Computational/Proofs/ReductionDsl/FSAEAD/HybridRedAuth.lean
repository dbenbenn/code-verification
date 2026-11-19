/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SimRel
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Tables
import Computational.Proofs.GameHop.StateSim
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out -- proof-setup: allow-public-import

public section

/-!
# Soundness and Query Bounds for `prgRedAuthProg` and `multiRedAuthProg`

Proves evaluation soundness (`prgRedAuthProg_eval`, `multiRedAuthProg_eval`) and OT-CCA query
bounds (`multiRedAuthProg_queries`) for the output-returning hybrid reductions with
`finish := hybFinishAuthC ae G kPRG kAEAD`, mirroring `HybridRedBase.run1_eval2_eq_simulateQ`
and combining the shared first-stage query bound `multiRedProg_eval1_queries` with second-stage
`eval2_queryBound`.
-/

set_option autoImplicit false

namespace CryptoGames.FSAEAD.Thm5.Costed

open ReductionDsl CryptoGames.FSAEAD.Costed CryptoGames.PRG.Costed CryptoGames.OTCCA.Costed
open OracleComp OracleSpec

variable {CK MK AD M C : Type}

local notation "HSig" => fsSig CK MK AD Unit M C
local notation "HT" => Ty HSig

local notation "HSamp" =>
  unifSamplers (S := HSig) fsStateSampleSort (fun _ => 1)

local notation "hybOps" ae:arg G:arg kPRG:arg kAEAD:arg =>
  Ops.sum
    (prgOps (S := HSig) (Ty.prod Ty.nat (bt FSort.ss)) (Ty.prod (bt FSort.ss) (bt FSort.rs))
      (fun pw => PRGScheme.gen (G (Prod.fst pw)) (Prod.snd pw)) kPRG)
    (otccaOps (S := HSig) (bt FSort.rs) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ad)
      (bt FSort.msg) (bt FSort.ct) ae kAEAD Ty.unit (fun _ => ()))

local notation "prgRedZeroIface" ideal:arg kIdeal:arg =>
  Iface.withSamp
    (Iface.withSamp (prgIface HSig)
      (idealSamplers (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ct) ideal kIdeal))
    HSamp

local notation "multiRedIface" ideal:arg kIdeal:arg =>
  Iface.withSamp
    (otccaIface (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.msg) (bt FSort.ct)
      ideal kIdeal)
    HSamp

local notation "recTy'" => recTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "kcTy'" => kcTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "slotTy'" => slotTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "hsTy'" => hsTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "stTy'" => stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)


section TwoStageAuthSim

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]

omit [SampleableType MK] [SampleableType CK] [MonadLiftT ProbComp (OracleComp T)] in
private theorem hybFinishAuthC_eval {I : Iface HSig T}
    (b' : Bool) (y : Unit) (s : HSt CK MK AD M C) :
    (hybFinishAuthC (I := I) ae G kPRG kAEAD).eval
      (.cons (encSt s) (.cons b' (.cons y .nil))) =
    pure (Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit b' s.1) :=
  rfl

set_option maxHeartbeats 400000 in
private theorem run1_eval2_auth_eq_simulateQ
    {I₀ : Iface HSig T}
    (_hliftP : ∀ {α : Type} (p : ProbComp α), I₀.liftP p = (liftM p : OracleComp T α))
    {rIn : Ty HSig}
    (initC : Comp (hybOps ae G kPRG kAEAD)
      (I₀.withSamp HSamp) [rIn] (.prod .unit stTy'))
    (maxSkip q mSlot fuel₂ : ℕ) (P : Params) (_ht : P.t = some 0)
    (ideal : ℕ × AD → ProbComp C)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps ae G kPRG kAEAD)
          (I₀.withSamp HSamp) Δ (bt .ct))
    (_hIdeal : SampleIdealRel ae G kPRG kAEAD sampleIdeal ideal)
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps ae G kPRG kAEAD)
          (I₀.withSamp HSamp) Δ (bt .ct)))
    (specialDec : Option (∀ {Δ},
      Expr (hybOps ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps ae G kPRG kAEAD)
          (I₀.withSamp HSamp) Δ (.opt (bt .msg))))
    (ops : Option (SpecialOps AD M C (OracleComp T)))
    (_hEnc : SpecialEncRel ae G kPRG kAEAD specialEnc ops)
    (_hDec : SpecialDecRel ae G kPRG kAEAD specialDec ops)
    (oa : OracleComp (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
      AD M (ℕ × C)) Bool) :
    let R : TwoStageCostedReduction (hybOps ae G kPRG kAEAD)
        (I₀.withSamp HSamp)
        (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
        ratchetCodec rIn .unit .bool .unit .unit .bool :=
      { σ := stTy'
        π := .unit
        init := initC
        handlePre := hybHandlePreC ae G kPRG kAEAD maxSkip q P.j mSlot P.la
          sampleIdeal specialEnc specialDec
        chDone := hybChDoneC ae G kPRG kAEAD
        resume := hybResumeC ae G kPRG kAEAD maxSkip q P.la
        handlePost := hybHandlePostC ae G kPRG kAEAD
        finish := hybFinishAuthC ae G kPRG kAEAD }
    ∀ {m n fuel₁ : ℕ} {s : HSt CK MK AD M C},
      oa.IsQueryBoundP (fun x => x.isRight = true) m →
      HInv maxSkip n s.1 →
      n + m ≤ q →
      m ≤ fuel₁ →
      m ≤ fuel₂ + 1 →
      (do
        let mid ← R.run1 false oa fuel₁ (encSt s)
        R.eval2 mid () fuel₂ false) =
      (do
        let z ← (simulateQ (multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
          oa).run s
        pure (Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit z.1 z.2.1)) := by
  intro R
  induction oa using OracleComp.inductionOn with
  | pure b' =>
    intro m n fuel₁ s _ _ _ _ _
    simp only [TwoStageCostedReduction.run1, construct_pure, pure_bind,
      TwoStageCostedReduction.eval2, simulateQ_pure, StateT.run_pure]
    exact hybFinishAuthC_eval ae G kPRG kAEAD b' () s
  | query_bind t mx ih =>
    intro m n fuel₁ s hb hI hq hm1 hm2
    rw [isQueryBoundP_query_bind_iff] at hb
    rcases t with u | t
    · have hfwd : (I₀.withSamp HSamp).fwdU u =
          (liftM (query (spec := unifSpec) u : ProbComp (Fin (u + 1))) :
            OracleComp T (Fin (u + 1))) := by
        simpa [Iface.withSamp, Iface.liftP, simulateQ_query] using
          _hliftP (query (spec := unifSpec) u)
      simp only [TwoStageCostedReduction.run1, construct_query_bind, R, hfwd, bind_assoc,
        simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
      change _ = (((multiImplWith (m := OracleComp T) ideal ae G maxSkip P mSlot (DG G) ops)
        (Sum.inl u)).run s >>= _)
      rw [multiImplWith_inl_run ae G maxSkip mSlot P ideal ops u s, bind_map_left]
      exact bind_congr fun v => ih v (by simpa using hb.2 v) hI hq hm1 hm2
    · have hm_pos : 0 < m := hb.1.resolve_left (by simp)
      cases fuel₁ with
      | zero => omega
      | succ f₁ =>
        have hn : n ≤ q := by omega
        have hIq : HInv maxSkip q s.1 := hI.mono hn
        have hsent : s.1.lastSentIdx ≤ q := hIq.sent_le
        have hrecv : s.1.receiverIdx ≤ (maxSkip + 1) * q := hIq.recv_le
        have htr : s.1.inTransit.length ≤ q := hIq.transit_len
        have hch : s.1.challengesInTransit.length ≤ q := hIq.chal_len
        have hks : s.1.lastSentIdx ≤ s.1.keys.length := hIq.keys_sent
        have hkr : s.1.receiverIdx ≤ s.1.keys.length := hIq.keys_recv
        have hpres := multiImplWith_inv ideal ae G P mSlot (DG G) ops (Sum.inr t) s hI
        simp only [Sum.isRight, ↓reduceIte] at hpres
        simp only [TwoStageCostedReduction.run1, construct_query_bind, bind_assoc,
          simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind]
        rw [show R.handlePre.eval (.cons (encSt s) (.cons (ratchetCodec.qenc t) .nil)) =
          (hybHandlePreC ae G kPRG kAEAD maxSkip q P.j mSlot P.la
            sampleIdeal specialEnc specialDec).eval
            (.cons (encSt s) (.cons (ratchetCodec.qenc t) .nil)) from rfl]
        rcases t with (((((⟨a, msg⟩ | ⟨a, m₀, m₁⟩) | ⟨⟩) | ⟨⟩) | ⟨a, i, e⟩) | ⟨a, i, e⟩)
        · -- 1. transmit
          change _ = ((multiTransmitHWith ideal ae G P mSlot (DG G) ops (a, msg)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.eval, Env.get, bind_assoc, pure_bind]
          rw [transmitBody_eval ae G kPRG kAEAD _hliftP _ maxSkip mSlot P _ht
            ideal sampleIdeal _hIdeal specialEnc ops _hEnc a msg s hks, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        · -- 2. challenge
          change _ = ((multiChallengeHWith ideal ae G P mSlot (DG G) ops (a, m₀, m₁)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, bind_assoc, pure_bind]
          rw [challengeBody_eval ae G kPRG kAEAD _hliftP _ maxSkip mSlot P _ht
            ideal sampleIdeal _hIdeal specialEnc ops _hEnc a m₀ m₁ s hks, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        · -- 3. corruptSender
          change _ = ((corruptSenderH G P ()).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v3, Expr.eval, Env.get, bind_assoc, pure_bind]
          change ((corruptSenderBody ae G kPRG kAEAD q P.la).eval _ >>= fun x =>
            R.run1 false (mx (Option.map rssDec x.1)) f₁ x.2 >>= fun mid =>
            R.eval2 mid () fuel₂ false) = _
          rw [bind_map_fst _ (Option.map rssDec)
              (fun v s' => R.run1 false (mx v) f₁ s' >>= fun mid => R.eval2 mid () fuel₂ false),
            corruptSenderBody_eval ae G kPRG kAEAD _hliftP _ q P s hsent, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        · -- 4. corruptReceiver (stays in first stage on bad = true; pauses and resumes on bad = false)
          change _ = ((corruptReceiverH G P ()).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval, orE, cond_true_left,
            hsEnded, hsChalls, Expr.v0, Expr.v1, Expr.v4, Expr.eval, Env.get,
            encSt_fst, encHS_ended, encHS_challs, decide_pos_length_eq_not_isEmpty,
            ← Bool.or_assoc, anyUncompInTransitE_eval, anyUncompInTransitBody_eval _ q s.1 htr]
          by_cases hbad :
              ((s.1.ended || !s.1.challengesInTransit.isEmpty) ||
                s.1.inTransit.any (fun r => !s.1.isCompromised r.idx)) = true
          · have hcr_bad :
                (corruptReceiverH (m := OracleComp T) (AD := AD) (M := M) (C := C) (MK := MK)
                  G P ()).run s = pure (none, s) := by
              rcases s with ⟨h, sl⟩
              have hbad' : ((h.ended || !h.challengesInTransit.isEmpty) ||
                  h.inTransit.any (fun r => !h.isCompromised r.idx)) = true := hbad
              simp only [corruptReceiverH, getH, onH, StateT.run_bind, StateT.run_mk,
                StateT.run_get, StateT.run_pure, map_pure, pure_bind, hbad', ↓reduceIte]
            simp only [hbad, ↓reduceIte, pure_bind, hcr_bad]
            exact ih none (by simpa using hb.2 none) (hI.mono (Nat.le_succ n))
              (by omega) (by omega) (by omega)
          · have hbadF :
                ((s.1.ended || !s.1.challengesInTransit.isEmpty) ||
                  s.1.inTransit.any (fun r => !s.1.isCompromised r.idx)) = false :=
              Bool.eq_false_iff.mpr hbad
            have hres_eq : R.resume = hybResumeC ae G kPRG kAEAD maxSkip q P.la := rfl
            simp only [hbadF, Bool.false_eq_true, ↓reduceIte, pure_bind,
              TwoStageCostedReduction.eval2, hres_eq, hybResumeC]
            try rw [bind_assoc]
            let env2 : Env (S := HSig) [.unit, .unit] :=
              .cons (t := .unit) () (.cons (t := .unit) () .nil)
            let kPost := fun ans s' =>
              runFuel (C := ratchetCodec)
                (hybHandlePostC (I := I₀.withSamp HSamp) ae G kPRG kAEAD)
                false (mx ans) fuel₂ s' >>=
              fun bs => (hybFinishAuthC (I := I₀.withSamp HSamp) ae G kPRG kAEAD).eval
                (.cons bs.2 (.cons (t := .bool) bs.1 (.cons (t := .unit) () .nil)))
            refine (bind_map_fst
              ((corruptReceiverResumeBody (I₀ := I₀) ae G kPRG kAEAD maxSkip q P.la).eval
                (.cons (encSt s) env2))
              ((ratchetCodec (CK := CK) (MK := MK) (AD := AD) (Pub := Unit) (M := M) (C := C)).rdec
                (Sum.inl (Sum.inl (Sum.inr ()))))
              kPost).trans ?_
            have hres_eval := corruptReceiverResumeBody_eval ae G kPRG kAEAD _hliftP env2
              maxSkip q P s hbadF hsent hrecv hIq.skipped_sorted hIq.skipped_pos
              (fun i hi => (hIq.skipped_le i hi).trans hIq.recv_le)
            refine (congrArg (· >>= fun y => kPost y.1 y.2) hres_eval).trans ?_
            rw [bind_map_left]
            dsimp only [kPost]
            refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
            have hz_end : z.2.1.ended = true := corruptReceiverH_ended_of_good G P s hbadF z hz
            rcases z with ⟨ans, s'⟩
            dsimp only [Prod.map, id_eq] at hz_end ⊢
            rw [runFuel_handlePost_eq_simulateQ ae G kPRG kAEAD _hliftP maxSkip mSlot P ideal ops
              false (mx ans) (by simpa using hb.2 ans) (by omega) hz_end, bind_map_left]
            refine bind_congr fun ⟨b'', s''⟩ => ?_
            exact hybFinishAuthC_eval ae G kPRG kAEAD b'' () s''
        · -- 5. deliver
          change _ = ((multiDeliverH ae G maxSkip P mSlot (DG G) ops (a, i, e)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v5, Expr.eval, Env.get, bind_assoc, pure_bind]
          change ((deliverBody ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval _ >>=
            fun x => R.run1 false (mx (Option.map rrDecM x.1)) f₁ x.2 >>= fun mid =>
            R.eval2 mid () fuel₂ false) = _
          rw [bind_map_fst _ (Option.map rrDecM)
              (fun v s' => R.run1 false (mx v) f₁ s' >>= fun mid => R.eval2 mid () fuel₂ false),
            deliverBody_eval ae G kPRG kAEAD _hliftP _ maxSkip q mSlot P _ht
              specialDec ops _hDec a i e s hkr htr hch, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)
        · -- 6. inject
          change _ = ((multiInjectH ae G maxSkip P mSlot (DG G) ops (a, i, e)).run s >>= _)
          simp only [hybHandlePreC, ratchetCodec, Comp.eval,
            Expr.v0, Expr.v1, Expr.v5, Expr.eval, Env.get, bind_assoc, pure_bind]
          change ((injectBody ae G kPRG kAEAD maxSkip q P.j mSlot P.la specialDec).eval _ >>=
            fun x => R.run1 false (mx (Option.map rrDecM x.1)) f₁ x.2 >>= fun mid =>
            R.eval2 mid () fuel₂ false) = _
          rw [bind_map_fst _ (Option.map rrDecM)
              (fun v s' => R.run1 false (mx v) f₁ s' >>= fun mid => R.eval2 mid () fuel₂ false),
            injectBody_eval ae G kPRG kAEAD _hliftP _ maxSkip q mSlot P _ht
              specialDec ops _hDec a i e s hkr htr hch, bind_map_left]
          refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
          exact ih z.1 (by simpa using hb.2 z.1) (hpres z hz) (by omega) (by omega) (by omega)

end TwoStageAuthSim


section TopLevel

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  (ideal : ℕ × AD → ProbComp C) (kIdeal : ℕ)

open CryptoVerification.LibsignalSession (evalTwoStage1)
open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
  (advBit hRunOut multiRunOut cumulativeChainPrgReductionOut multiSlotOtccaReductionOut)


/-- Soundness of `prgRedAuthProg`: on any `q`-query ratchet adversary `A`,
`evalTwoStage1 (prgRedAuthProg ...) q false` evaluates to `cumulativeChainPrgReductionOut ... advBit`. -/
theorem prgRedAuthProg_eval (q maxSkip j : ℕ)
    (A : RatchetAdversary CK MK AD M C)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)))
      q)
    (mt : CK × MK) :
    evalTwoStage1 (prgRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip j)
        q false (fun _ => A) mt =
      cumulativeChainPrgReductionOut ideal ae G maxSkip j advBit A mt := by
  dsimp only [evalTwoStage1]
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      (Iface.withSamp (prgIface HSig)
        (idealSamplers (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ct)
          ideal kIdeal)).liftP p = (liftM p : ProbComp α) := fun p => by
    rw [liftP_withSamp, prgIface_liftP]
  have hIdeal : SampleIdealRel (T := unifSpec) (I := prgRedZeroIface ideal kIdeal)
      ae G kPRG kAEAD
      (fun ia =>
        Comp.sample (O := hybOps ae G kPRG kAEAD)
          (I := prgRedZeroIface ideal kIdeal)
          (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
      ideal := by
    intro Δ ρ' ia
    dsimp only [Comp.eval, liftP_withSamp, samp_withSamp_inl, samp_withSamp_inr, idealSamplers]
    exact prgIface_liftP (S := HSig) _
  let R : TwoStageCostedReduction (hybOps ae G kPRG kAEAD)
      (prgRedZeroIface ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec (.prod (bt .ss) (bt .rs)) .unit .bool .unit .unit .bool :=
    { σ := stTy
      π := .unit
      init := (prgRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip j).init
      handlePre := hybHandlePreC ae G kPRG kAEAD maxSkip q
        (hp (j / 2) 0 (isLookaheadHop j)).j 0 (hp (j / 2) 0 (isLookaheadHop j)).la
        (fun ia =>
          Comp.sample (O := hybOps ae G kPRG kAEAD)
            (I := prgRedZeroIface ideal kIdeal)
            (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
        none none
      chDone := hybChDoneC ae G kPRG kAEAD
      resume := hybResumeC ae G kPRG kAEAD maxSkip q (hp (j / 2) 0 (isLookaheadHop j)).la
      handlePost := hybHandlePostC ae G kPRG kAEAD
      finish := hybFinishAuthC ae G kPRG kAEAD }
  have hsim := fun (b : Bool) =>
    run1_eval2_auth_eq_simulateQ ae G kPRG kAEAD hliftP
      (prgRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip j).init
      maxSkip q 0 q (hp (j / 2) 0 (isLookaheadHop j)) rfl
      ideal _ hIdeal none none none trivial trivial A
      (m := q) (n := 0) (fuel₁ := q) (s := hInit b (.mat (j / 2) mt))
      (isQueryBoundP_isRight_of_isGameQuery hA) (HInv.init b) (by omega) (by omega) (by omega)
  have hinitC :
      R.init.eval (.cons (t := .prod (bt .ss) (bt .rs)) mt .nil) =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        pure ((), encSt (hInit b (.mat (j / 2) mt)))) := by
    simp only [R, prgRedAuthProg, Comp.eval, Expr.v0, Expr.v1, Expr.eval, Env.get,
      liftP_withSamp, prgIface_liftP]
    dsimp only [Iface.withSamp, Samplers.sum, unifSamplers, Sum.elim]
    refine bind_congr fun b => ?_
    have hsk : (fun _ : ℕ => false) = encSkipped [] := by funext x; rfl
    simp [Env.get, encSt, encSlot, encHS, encKc, hInit, hsk]
  rw [eval1_bind_eval2_ret_unit (prgRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip j) rfl]
  change (do
    let (a, s) ← R.init.eval (.cons (t := .prod (bt .ss) (bt .rs)) mt .nil)
    let m ← R.run1 false A q s
    R.eval2 m () q false) = _
  rw [hinitC]
  simp only [cumulativeChainPrgReductionOut, hRunOut, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [← multiImplWith_zero_none ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G) rfl]
  exact hsim b

/-- Soundness of `multiRedAuthProg`: on any `q`-query ratchet adversary `A`,
`evalTwoStage1 (multiRedAuthProg ...) q false` evaluates to `multiSlotOtccaReductionOut ... advBit`. -/
theorem multiRedAuthProg_eval (q maxSkip N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)))
      q) :
    evalTwoStage1 (multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la)
        q false (fun _ => A) () =
      multiSlotOtccaReductionOut ideal ae G maxSkip N la advBit A := by
  dsimp only [evalTwoStage1]
  have hliftP : ∀ {α : Type} (p : ProbComp α),
      (otccaIface (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.msg)
        (bt FSort.ct) ideal kIdeal).liftP p =
        (liftM p : OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) α) :=
    fun p => otccaIface_liftP _ _ _ ideal kIdeal p
  have hIdeal : SampleIdealRel
      (T := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
      (I := multiRedIface ideal kIdeal)
      ae G kPRG kAEAD
      (fun ia =>
        Comp.sample (O := hybOps ae G kPRG kAEAD)
          (I := multiRedIface ideal kIdeal)
          (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
      ideal := by
    intro Δ ρ' ia
    dsimp only [Comp.eval, liftP_withSamp, samp_withSamp_inl, otccaIface, idealSamplers]
    exact otccaIface_liftP _ _ _ ideal kIdeal _
  have hEnc : SpecialEncRel
      (T := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
      (I := multiRedIface ideal kIdeal)
      ae G kPRG kAEAD
      (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
      (some (otOpsWith ideal)) := by
    intro Δ ρ' iam
    dsimp only [otSpecialEncC, otOpsWith, callC, Comp.eval, Expr.v0, Expr.v1, Expr.eval, Env.get]
    change ((id <$> (query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
        (Sum.inr (Sum.inl (iam.eval ρ'))) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (Option C))) >>= _) = _
    rw [id_map]
    refine bind_congr fun r => ?_
    cases r with
    | none => exact otccaIface_liftP _ _ _ ideal kIdeal _
    | some c => rfl
  have hDec : SpecialDecRel
      (T := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
      (I := multiRedIface ideal kIdeal)
      ae G kPRG kAEAD
      (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
      (some (otOpsWith ideal)) := by
    intro Δ ρ' iae
    change id <$> (query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
        (Sum.inr (Sum.inr (iae.eval ρ'))) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (Option M)) =
      (query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)
        (Sum.inr (Sum.inr (iae.eval ρ'))) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (Option M))
    exact id_map _
  let R : TwoStageCostedReduction (hybOps ae G kPRG kAEAD)
      (multiRedIface ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec .unit .unit .bool .unit .unit .bool :=
    { σ := stTy
      π := .unit
      init := (multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).init
      handlePre := hybHandlePreC ae G kPRG kAEAD maxSkip q
        (hp N 0 la).j N (hp N 0 la).la
        (fun ia =>
          Comp.sample (O := hybOps ae G kPRG kAEAD)
            (I := multiRedIface ideal kIdeal)
            (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
        (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
        (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
      chDone := hybChDoneC ae G kPRG kAEAD
      resume := hybResumeC ae G kPRG kAEAD maxSkip q (hp N 0 la).la
      handlePost := hybHandlePostC ae G kPRG kAEAD
      finish := hybFinishAuthC ae G kPRG kAEAD }
  have hsim := fun (b : Bool) =>
    run1_eval2_auth_eq_simulateQ ae G kPRG kAEAD hliftP
      (multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).init
      maxSkip q N q (hp N 0 la) rfl
      ideal _ hIdeal
      (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
      (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
      (some (otOpsWith ideal)) hEnc hDec A
      (m := q) (n := 0) (fuel₁ := q) (s := hInit b .unknown)
      (isQueryBoundP_isRight_of_isGameQuery hA) (HInv.init b) (by omega) (by omega) (by omega)
  have hinitC :
      R.init.eval (.cons (t := .unit) () .nil) =
      (do
        let b ← (liftM ($ᵗ Bool) :
          OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) Bool)
        pure ((), encSt (hInit b .unknown))) := by
    simp only [R, multiRedAuthProg, Comp.eval, Expr.v0, Expr.eval,
      liftP_withSamp]
    dsimp only [Iface.withSamp, Samplers.sum, unifSamplers, Sum.elim]
    rw [otccaIface_liftP]
    refine bind_congr fun b => ?_
    have hsk : (fun _ : ℕ => false) = encSkipped [] := by funext x; rfl
    simp [Env.get, encSt, encSlot, encHS, encKc, hInit, hsk]
  rw [eval1_bind_eval2_ret_unit (multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la) rfl]
  change (do
    let (a, s) ← R.init.eval (.cons (t := .unit) () .nil)
    let m ← R.run1 false A q s
    R.eval2 m () q false) = _
  rw [hinitC]
  simp only [multiSlotOtccaReductionOut, multiRunOut, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  exact hsim b

private theorem multiRedAuthProg_eval1_queries (q maxSkip N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    ((multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval1
      (fun _ => A) () q false).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C)) q := by
  have h := (multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval1_queryBound
    (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [Iface.withSamp, otccaIface, isGameQuery])
    (fun _ => A) () q false
  refine h.mono (le_of_eq ?_)
  simp [multiRedAuthProg, hybHandlePreC, hybChDoneC, transmitBody, challengeBody, corruptSenderBody,
    deliverBody, injectBody, receiveBody, genUpToC, genUpToBody, genStepKcBody,
    encIdxBody, decIdxBody, prependNewSkippedBody, senderKeyBody, revealBody,
    chainFromC, chainFromBody, otSpecialEncC, otSpecialDecC, callC, Comp.queries]

private theorem multiRedAuthProg_eval2_queries (q maxSkip N : ℕ) (la : Bool)
    (m : Mid (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      Bool Unit (stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)).denote Unit) :
    ((multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval2 m () q false).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C)) 0 := by
  have h := (multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la).eval2_queryBound
    (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [Iface.withSamp, otccaIface, isGameQuery])
    m () q false
  refine h.mono (le_of_eq ?_)
  simp [multiRedAuthProg, hybResumeC, hybHandlePostC, hybFinishAuthC, corruptReceiverResumeBody,
    corruptReceiverDBody, senderKeyBody, revealBody, chainFromC, chainFromBody,
    callC, Comp.queries]

/-- `multiRedAuthProg` makes at most `q` OT-CCA oracle queries when `A` makes at most `q`
ratchet queries. -/
theorem multiRedAuthProg_queries (q maxSkip N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C)
    (hA : A.IsQueryBoundP
      (isGameQuery (G := spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)))
      q) :
    (evalTwoStage1 (multiRedAuthProg ae G kPRG kAEAD ideal kIdeal q maxSkip N la)
      q false (fun _ => A) ()).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × AD) M C)) q := by
  let _ := hA
  simpa [evalTwoStage1] using isQueryBoundP_bind
    (multiRedAuthProg_eval1_queries ae G kPRG kAEAD ideal kIdeal q maxSkip N la A)
    (fun pm _ => multiRedAuthProg_eval2_queries ae G kPRG kAEAD ideal kIdeal q maxSkip N la pm.2)


end TopLevel

end CryptoGames.FSAEAD.Thm5.Costed

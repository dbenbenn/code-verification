/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Defs
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import VCVio.OracleComp.EvalDist.Measure

/-!
# Pointwise Stage-2 `canon`-Bucket Lemma 9 (`SM/Theorem8/Stage2Bucket.lean`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

section BucketProof

set_option linter.unusedSectionVars false

open Engine CryptoGames.SM.Construction.AuthL9

local notation "ASpecB" =>
  unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

private def bucketTStar (Δcka : ℕ) (tL : Option ℕ) : ℕ :=
  match tL with
  | none => 0
  | some l => l + 3 + Δcka

private theorem bucketTStar_admissible (Δcka : ℕ) (tL : Option ℕ) :
    lastLeakGuessAdmissible (2 + Δcka) tL (bucketTStar Δcka tL) = true := by
  cases tL with
  | none => rfl
  | some l => dsimp only [bucketTStar]; simp only [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq]; omega

private theorem vSend_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ) :
    vSend (hooksCKABucket cka prng fs Δcka tL) =
      vSend (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩) := rfl

private theorem commitE_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ) :
    commitE (hooksCKABucket cka prng fs Δcka tL) =
      commitE (hooksCKA cka prng fs Δcka ⟨true, tL, tStar⟩) := rfl

private theorem initCKA_zero_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (tL : Option ℕ) (tStar : ℕ) :
    initCKA cka prng fs lam ⟨true, tL, 0⟩ = initCKA cka prng fs lam ⟨true, tL, tStar⟩ := rfl

private theorem startRecv_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ)
    (ctx : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)) (P : Party) (t : ℕ)
    (γv : Option Γ) (σ : Sig) (Tn : T) :
    (hooksCKABucket cka prng fs Δcka tL).startRecv ctx P t γv σ Tn =
      (hooksCKA cka prng fs Δcka
        ⟨true, tL, if lastLeakGuessAdmissible (2 + Δcka) tL t then t else t + 1⟩).startRecv
        ctx P t γv σ Tn := by
  ext h; simp only [hooksCKABucket, hooksCKA, StateT.run_bind, StateT.run_get, pure_bind]
  cases h.cache t with
  | none =>
    cases hb : lastLeakGuessAdmissible (2 + Δcka) tL t
    · simp
    · simp; rfl
  | some pair =>
    rcases pair with ⟨Tc, Ik⟩
    by_cases hTc : Tc = Tn
    · simp [hTc]
    · cases hb : lastLeakGuessAdmissible (2 + Δcka) tL t
      · simp [hTc]
      · simp [hTc]; rfl

private theorem vRecv_hooksCKABucket_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (vp : PartyState (Option Γ) T Sig SS RS) (c : Header T × E)
    (rec : Option (Record M (Header T × E))) :
    vRecv (hooksCKABucket cka prng fs Δcka tL) ctx P vp c rec =
      vRecv (hooksCKA cka prng fs Δcka
        ⟨true, tL, if lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 then c.1.1 else c.1.1 + 1⟩)
        ctx P vp c rec := by
  unfold vRecv
  by_cases h1 : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : c.1.1 = vp.tcur + 1
    · simp only [h2, ↓reduceIte, startRecv_hooksCKABucket_eq]; rfl
    · simp only [h2, ↓reduceIte]; rfl

private def queryTargetEpoch : (ASpecB).Domain → Option ℕ → Option ℕ
  | .inr (.inl (.inr ⟨_, c⟩)), _ => some c.1.1
  | _, winEp => winEp

private abbrev fullImplBucket (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) :
    QueryImpl ASpecB
      (StateT (_root_.CryptoGames.SM.BucketAuthBridge.BucketState
        (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (_root_.CryptoGames.SM.BucketAuthBridge.BucketState
      (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) +
    _root_.CryptoGames.SM.BucketAuthBridge.bucketOracleImpl
      (scheme cka prng fs lam) (2 + Δcka) qep tL

private theorem fullImplBucket_run_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : (ASpecB).Domain)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) (winEp : Option ℕ) :
    ((fullImplBucket cka prng fs lam Δcka qep tL t).run (s, winEp)) =
      ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) +
        oracleImpl (scheme cka prng fs lam) (2 + Δcka) qep (bucketAuthCfg Δcka tL)) t).run s >>=
        fun res => pure (res.1,
          (res.2, if !s.win && res.2.win then queryTargetEpoch t winEp else winEp))) := by
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · simp [fullImplBucket, queryTargetEpoch]
  · simp [fullImplBucket, _root_.CryptoGames.SM.BucketAuthBridge.bucketOracleImpl,
      _root_.CryptoGames.SM.BucketAuthBridge.liftGameStep, oracleImpl, queryTargetEpoch,
      StateT.run_mk]
  · simp [fullImplBucket, _root_.CryptoGames.SM.BucketAuthBridge.bucketOracleImpl,
      _root_.CryptoGames.SM.BucketAuthBridge.bucketCfg,
      _root_.CryptoGames.SM.BucketAuthBridge.liftGameStep, oracleImpl, bucketAuthCfg,
      queryTargetEpoch, StateT.run_mk]
  · simp [fullImplBucket, _root_.CryptoGames.SM.BucketAuthBridge.bucketOracleImpl,
      _root_.CryptoGames.SM.BucketAuthBridge.bucketCfg,
      _root_.CryptoGames.SM.BucketAuthBridge.liftGameStep, oracleImpl, bucketAuthCfg,
      queryTargetEpoch, StateT.run_mk]
  · dsimp only [fullImplBucket, _root_.CryptoGames.SM.BucketAuthBridge.bucketOracleImpl,
      _root_.CryptoGames.SM.BucketAuthBridge.bucketInjectImpl, oracleImpl, injectImpl,
      bucketAuthCfg, queryTargetEpoch, QueryImpl.add_apply]
    rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only
    split_ifs with hcond
    · simp
    · have hw_f : s.win = false := by
        cases h : s.win
        · rfl
        · simp [h] at hcond
      cases hrcv : (scheme cka prng fs lam).receive (s.st P) c with
      | none => simp [hw_f]
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcv
        subst ht'
        dsimp only
        split_ifs with hqep htriv hfull <;> simp [GameState.accept, GameState.delete, hw_f]
  · simp [fullImplBucket, _root_.CryptoGames.SM.BucketAuthBridge.bucketOracleImpl,
      _root_.CryptoGames.SM.BucketAuthBridge.liftGameStep, oracleImpl, queryTargetEpoch,
      StateT.run_mk]

private def transmitEBucket {Γv Sv SSv RSv HS : Type} {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) (Δ qep : ℕ) :
    QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  fun ⟨P, m, r⟩ => do
    let es ← get
    if es.abort || es.g.win then return none
    match es.g.epMgmt Δ qep P r.isSome with
    | none => return none
    | some s₁ =>
      match ← liftH (vSend hk s₁ P (s₁.st P) m none r) with
      | none => abortE; return none
      | some (st', ct) =>
        let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
        modify fun s => { s with g := s₁.record Δ P st' recE false }
        return some ct

private def challEBucket {Γv Sv SSv RSv HS : Type} {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    (_hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) :
    QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  fun _ => pure none

private def corrEBucket {Γv Sv SSv RSv HS : Type} {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) :
    QueryImpl (Party →ₒ Option (PartyState Γ T Sig SS RS))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  fun P => do
    let es ← get
    if es.abort || es.g.win || !(es.g.corrAllowed P) then return none
    let s₁ := es.g.afterCorr P
    match ← liftH (hk.reveal es.g P (es.g.st P)) with
    | none => abortE; return none
    | some stOut =>
      modify fun s => { s with g := s₁ }
      return some stOut

private def implEBucketRaw {Γv Sv SSv RSv HS : Type} {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) :
    QueryImpl ASpecB (EM tspec Γv T Sv SSv RSv M E HS) :=
  (coinsE : QueryImpl unifSpec (EM tspec Γv T Sv SSv RSv M E HS)) +
    (transmitEBucket hk Δ qep + challEBucket hk +
      deliverE hk maxSkip cfg + injectE hk Δ qep cfg + corrEBucket hk)

private theorem implCKABucket_run_eq (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : (ASpecB).Domain)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ) :
    ((implCKABucket cka prng fs Δcka qep tL t).run (es, winEp)) =
      ((implEBucketRaw (hooksCKABucket cka prng fs Δcka tL)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL) t).run es >>=
        fun res => pure (res.1,
          (res.2, if !es.g.win && res.2.g.win then queryTargetEpoch t winEp else winEp))) := by
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [implCKABucket, implEBucketRaw, QueryImpl.add_apply, coinsE, queryTargetEpoch]
    simp [StateT.run_lift]
  · dsimp only [implCKABucket, implEBucketRaw, QueryImpl.add_apply, transmitEBucket, queryTargetEpoch]
    simp only [ite_self, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hcond
    · simp
    · cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp
      | some s₁ =>
        dsimp only
        rw [StateT.run_bind, StateT.run_lift, StateT.run_bind, liftH_run]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun ⟨res, h'⟩ => ?_
        cases res with
        | none => simp [abortE]
        | some val => rcases val with ⟨st', ct⟩; simp
  · dsimp only [implCKABucket, implEBucketRaw, QueryImpl.add_apply, challEBucket, queryTargetEpoch]
    simp
  · dsimp only [implCKABucket, implEBucketRaw, QueryImpl.add_apply, queryTargetEpoch]
    simp [StateT.run_lift]
  · dsimp only [implCKABucket, implEBucketRaw, QueryImpl.add_apply, queryTargetEpoch]
    simp [StateT.run_lift]
  · dsimp only [implCKABucket, implEBucketRaw, QueryImpl.add_apply, corrEBucket, queryTargetEpoch]
    simp only [ite_self, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hcond
    · simp
    · rw [StateT.run_bind, StateT.run_lift, StateT.run_bind, liftH_run]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun ⟨res, h'⟩ => ?_
      cases res <;> simp [abortE]

private def DoomedAll {St : Type} (Δcka : ℕ) (tL : Option ℕ)
    (s : GameState St M (Header T × E)) : Prop :=
  ∀ tWin, lastLeakGuessAdmissible (2 + Δcka) tL tWin = true → DoomedAuth tL tWin s

private def DoomedBucket {St : Type} (Δcka : ℕ) (tL : Option ℕ)
    (sw : GameState St M (Header T × E) × Option ℕ) : Prop :=
  if sw.1.win then ∃ tWin, sw.2 = some tWin ∧ DoomedAuth tL tWin sw.1
  else DoomedAll Δcka tL sw.1

private theorem doomedBucket_not_win {St : Type} (Δcka : ℕ) (tL : Option ℕ)
    (sw : GameState St M (Header T × E) × Option ℕ) (hd : DoomedBucket Δcka tL sw) :
    (match sw.2 with
      | none => false
      | some tWin => sw.1.win && authLosingConditionsAvoided (2 + Δcka) tL tWin sw.1) = false := by
  unfold DoomedBucket at hd
  cases hw : sw.1.win
  · cases sw.2 <;> simp
  · simp only [hw, ↓reduceIte] at hd
    obtain ⟨tWin, hsw2, hda⟩ := hd; rw [hsw2]
    simpa [hw] using @doomedAuth_not_win St M (Header T × E) _ inferInstance (2 + Δcka) tL tWin sw.1 hda

private theorem epMgmt_win_eq {St : Type} {Δ qep : ℕ} {s s₁ : GameState St M (Header T × E)}
    {P : Party} {bad : Bool} (hep : s.epMgmt Δ qep P bad = some s₁) : s₁.win = s.win := by
  unfold GameState.epMgmt at hep; split_ifs at hep <;> (injection hep with hep; subst hep; rfl)

private theorem doomedBucket_step
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : (ASpecB).Domain)
    {sw sw' : GameState (PartyState Γ T Sig SS RS) M (Header T × E) × Option ℕ}
    {u : (ASpecB).Range t} (hd : DoomedBucket Δcka tL sw)
    (hmem : (u, sw') ∈ support ((fullImplBucket cka prng fs lam Δcka qep tL t).run sw)) :
    DoomedBucket Δcka tL sw' := by
  rcases sw with ⟨s, winEp⟩
  rw [fullImplBucket_run_eq, MonadAttach.mem_support_bind] at hmem
  rcases hmem with ⟨⟨u₀, s'⟩, h₁, h₂⟩
  simp only [support_pure, Set.mem_singleton_iff] at h₂
  injection h₂ with hu hsw'; subst hu hsw'
  have unchanged : s' = s → DoomedBucket Δcka tL
      (s', if (!s.win && s'.win) = true then queryTargetEpoch t winEp else winEp) := by
    intro hs'; rw [hs']; have hwf : (!s.win && s.win) = false := by cases s.win <;> rfl
    simpa [hwf] using hd
  have hΔ : 0 < 2 + Δcka := by omega
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [QueryImpl.add_apply, QueryImpl.liftTarget, QueryImpl.ofLift] at h₁
    exact unchanged (mem_support_liftProb h₁).2
  · dsimp only [QueryImpl.add_apply, oracleImpl, transmitImpl] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁; dsimp only at h₁
    split_ifs at h₁ with hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      exact unchanged h₁.2
    · have hw_f : s.win = false := Bool.eq_false_iff.mpr hw
      have hd0 : DoomedAll Δcka tL s := by simpa [DoomedBucket, hw_f] using hd
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at h₁
      rcases h₁ with ⟨⟨⟨coins, bad⟩, s₀⟩, h₀, h₁⟩
      rw [(mem_support_liftProb h₀).2] at h₁; dsimp only at h₁
      cases hep : s.epMgmt (2 + Δcka) qep P bad with
      | none =>
        rw [hep] at h₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        exact unchanged h₁.2
      | some s₁ =>
        rw [hep] at h₁
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff] at h₁
        rcases h₁ with ⟨_, hs'⟩; subst hs'
        have hw1 : s₁.win = false := (epMgmt_win_eq hep).trans hw_f
        have hrec_w : (s₁.record (2 + Δcka) P ((scheme cka prng fs lam).send (s₁.st P) m coins).1
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ((scheme cka prng fs lam).send (s₁.st P) m coins).2⟩
            false).win = false := by simp [GameState.record, hw1]
        simp only [DoomedBucket, hrec_w, Bool.false_eq_true, ↓reduceIte]
        intro tWin hb
        exact @doomedAuth_record _ M (Header T × E) _ _ _ hΔ tL tWin s₁ P _ _ false rfl
          (@doomedAuth_epMgmt _ M (Header T × E) _ _ _ _ tL tWin s s₁ P bad (hd0 tWin hb) hep)
  · dsimp only [QueryImpl.add_apply, oracleImpl, challImpl, bucketAuthCfg] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁; dsimp only at h₁
    by_cases hw : s.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
      injection h₁ with _ hs'; exact unchanged hs'
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at h₁
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at h₁
      rcases h₁ with ⟨⟨⟨coins, bad⟩, s₀⟩, h₀, h₁⟩
      rw [(mem_support_liftProb h₀).2] at h₁; dsimp only at h₁
      cases hep : s.epMgmt (2 + Δcka) qep P bad
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
        injection h₁ with _ hs'; exact unchanged hs'
      · simp only [hep, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at h₁
        injection h₁ with _ hs'; exact unchanged hs'
  · dsimp only [QueryImpl.add_apply, oracleImpl, deliverImpl, bucketAuthCfg] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁; dsimp only at h₁
    split_ifs at h₁ with hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
      injection h₁ with _ hs'; exact unchanged hs'
    · have hw_f : s.win = false := Bool.eq_false_iff.mpr hw
      have hd0 : DoomedAll Δcka tL s := by simpa [DoomedBucket, hw_f] using hd
      cases hin : s.inTransit P.other c with
      | none =>
        rw [hin] at h₁; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
        injection h₁ with _ hs'; exact unchanged hs'
      | some rec =>
        rw [hin] at h₁
        cases hrcv : (scheme cka prng fs lam).receive (s.st P) c with
        | none =>
          rw [hrcv] at h₁
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at h₁
          injection h₁ with _ hs'; exact unchanged hs'
        | some res =>
          rcases res with ⟨st', t', i', m'⟩; rw [hrcv] at h₁
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_set, pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
          injection h₁ with _ hs'; subst hs'
          have hacc_w : (s.accept P st' rec.pos).win = false := by
            simp [GameState.accept, GameState.delete, hw_f]
          simp only [DoomedBucket, hacc_w, Bool.false_eq_true, ↓reduceIte]
          exact fun tWin hb => @doomedAuth_accept _ M (Header T × E) _ _ tL tWin s P st' rec.pos (hd0 tWin hb)
  · dsimp only [QueryImpl.add_apply, oracleImpl, injectImpl, bucketAuthCfg] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁; dsimp only at h₁
    split_ifs at h₁ with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      exact unchanged h₁.2
    · have hw_f : s.win = false := by cases h : s.win <;> simp_all
      have hd0 : DoomedAll Δcka tL s := by simpa [DoomedBucket, hw_f] using hd
      cases hrcv : (scheme cka prng fs lam).receive (s.st P) c with
      | none =>
        rw [hrcv] at h₁
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        exact unchanged h₁.2
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcv; subst ht'
        rw [hrcv] at h₁; dsimp only at h₁
        split_ifs at h₁ with hqep htriv hfull
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
          exact unchanged h₁.2
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at h₁
          rcases h₁ with ⟨_, hs'⟩; subst hs'
          have hacc_w : (s.accept P st' ⟨P.other, c.1.1, i'⟩).win = false := by
            simp [GameState.accept, GameState.delete, hw_f]
          simp only [DoomedBucket, hacc_w, Bool.false_eq_true, ↓reduceIte]
          exact fun tWin hb => @doomedAuth_accept _ M (Header T × E) _ _ tL tWin s P st'
            ⟨P.other, c.1.1, i'⟩ (hd0 tWin hb)
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff] at h₁
          rcases h₁ with ⟨_, hs'⟩; subst hs'
          simp only [DoomedBucket, hw_f, Bool.not_false, Bool.true_and, ↓reduceIte, queryTargetEpoch]
          refine ⟨c.1.1, rfl, ?_⟩
          rcases hd0 c.1.1 hfull with h1 | h2 | h3 | h4
          · exact Or.inl h1
          · exact False.elim (htriv (@doomed2_trivial_tStar _ M (Header T × E) _ _ _ _ hΔ s h2
              ⟨P.other, c.1.1, i'⟩ rfl))
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4))
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
          exact unchanged h₁.2
  · dsimp only [QueryImpl.add_apply, oracleImpl, corrImpl] at h₁
    rw [StateT.run_bind, StateT.run_get, pure_bind] at h₁; dsimp only at h₁
    split_ifs at h₁ with hcond
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
      exact unchanged h₁.2
    · have hw_f : s.win = false := by cases h : s.win <;> simp_all
      have hd0 : DoomedAll Δcka tL s := by simpa [DoomedBucket, hw_f] using hd
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff] at h₁
      rcases h₁ with ⟨_, hs'⟩; subst hs'
      have hcorr_w : (s.afterCorr P).win = false := by simp [GameState.afterCorr, GameState.leak, hw_f]
      simp only [DoomedBucket, hcorr_w, Bool.false_eq_true, ↓reduceIte]
      exact fun tWin hb => @doomedAuth_afterCorr _ M (Header T × E) _ _ tL tWin s P (hd0 tWin hb)

private theorem doomedBucket_simulateQ
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ)
    {α : Type} (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {sw sw' : GameState (PartyState Γ T Sig SS RS) M (Header T × E) × Option ℕ} {a : α},
      DoomedBucket Δcka tL sw →
      (a, sw') ∈ support
        ((simulateQ (fullImplBucket cka prng fs lam Δcka qep tL) oa).run sw) →
      DoomedBucket Δcka tL sw' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sw sw' a' hd hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.ext_iff.mp hmem with ⟨_, rfl⟩
    exact hd
  | query_bind t k ih =>
    intro sw sw' a' hd hmem
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨u, sw₁⟩, h₁, h₂⟩
    exact ih u (doomedBucket_step cka prng fs lam Δcka qep tL t hd h₁) h₂

private theorem abort_simulateQ_bucket
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    {S : Type} (tImpl : QueryImpl (CKA.spec Γ CCoins T I) (StateT S ProbComp))
    {α : Type} (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {ew ew' : CKABucketEState Γ T Sig SS RS M E I} {sc sc' : S} {a : α},
      ew.1.abort = true →
      ((a, ew'), sc') ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + tImpl)
        ((simulateQ (implCKABucket cka prng fs Δcka qep tL) oa).run ew)).run sc) →
      ew'.1.abort = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro ew ew' sc sc' a' hab hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.ext_iff.mp hmem with ⟨h1, _⟩
    rcases Prod.ext_iff.mp h1 with ⟨_, rfl⟩
    exact hab
  | query_bind t k ih =>
    intro ⟨es, winEp⟩ ew' sc sc' a' hab hmem
    dsimp only at hab
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨⟨u, ew₁⟩, sc₁⟩, h₁, h₂⟩
    rw [implCKABucket_run_eq] at h₁
    simp only [simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h₁
    rcases h₁ with ⟨⟨⟨u₀, es₁⟩, sc₀⟩, hraw, h_eq⟩
    injection h_eq with h_pair hsc
    injection h_pair with hu hew
    subst hsc hu hew
    have hab₁ : es₁.abort = true := by
      rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
      · dsimp only [implEBucketRaw, QueryImpl.add_apply, coinsE] at hraw
        simp only [StateT.run_lift, simulateQ_bind, QueryImpl.liftTarget,
          simulateQ_pure, StateT.run_bind, StateT.run_pure, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hraw
        rcases hraw with ⟨_, _, ⟨_, rfl⟩, _⟩
        exact hab
      · dsimp only [implEBucketRaw, QueryImpl.add_apply, transmitEBucket] at hraw
        simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hraw
        rw [hraw.1.2]; exact hab
      · dsimp only [implEBucketRaw, QueryImpl.add_apply, challEBucket] at hraw
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
          Prod.ext_iff] at hraw
        rw [hraw.1.2]; exact hab
      all_goals
        dsimp only [implEBucketRaw, QueryImpl.add_apply, deliverE, injectE, corrEBucket] at hraw
        simp only [hab, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hraw
        rw [hraw.1.2]; exact hab
    exact ih u hab₁ h₂

private theorem doomedAll_of_corr_nonlocal_gt
    {cka : CKAScheme KC Γ CCoins T I} {Δcka : ℕ} {tL : Option ℕ} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL (bucketTStar Δcka tL) s es sc)
    (hw : es.g.win = false)
    (htL : tL = some l) {P : Party} (hloc : es.g.epoch P < l + 2 + Δcka)
    (hnall : sc.allowCorr (healEpoch (some l)) = false) :
    DoomedAll Δcka tL (s.afterCorr P) := by
  subst htL
  intro tWin hb
  have hs_w : Sync9 cka Δcka (some l) tWin s es sc := { hs with valid := hb }
  by_cases hd :
      ((Policy.mk true (some l) tWin).leakDoom es.g (es.g.afterCorr P) ||
        (Policy.mk true (some l) tWin).corrDoom es.g P) = true
  · exact hs_w.doomed_of_corr_doom hw hd
  · rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hd) with ⟨hld, hcd⟩
    have hall := hs_w.allowCorr_of_corr rfl hloc hld hcd
    exact absurd hall (by simpa [healEpoch] using hnall)

private theorem doomedAll_of_sendBad_gt
    {cka : CKAScheme KC Γ CCoins T I} {Δcka qep : ℕ} {tL : Option ℕ} {l : ℕ}
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL (bucketTStar Δcka tL) s es sc)
    (hw : es.g.win = false)
    (htL : tL = some l) {P : Party} (hloc : es.g.epoch P < l + 2 + Δcka)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    {s₁ : GameState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)}
    (hep : es.g.epMgmt (2 + Δcka) qep P true = some s₁)
    (hgt : l < es.g.epoch P + 1)
    (st' : PartyState Γ T Sig SS RS) (m : M) (c : Header T × E) :
    DoomedAll Δcka tL
      ((realGS sc s₁).record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ false) := by
  subst htL
  intro tWin hb
  have hs_w : Sync9 cka Δcka (some l) tWin s es sc := { hs with valid := hb }
  by_cases hld : (Policy.mk true (some l) tWin).leakDoom es.g s₁ = true
  · exact hs_w.doomed_of_leakDoom_epMgmt hw hep hld st' m c false
  · exact hs_w.doomed4_of_sendBad_gt rfl hloc hsend hep (Bool.eq_false_iff.mpr hld) hgt st' m c false

private def runLBucket (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) {α : Type}
    (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (sw : GameState (PartyState Γ T Sig SS RS) M (Header T × E) × Option ℕ) : ProbComp Bool :=
  ((simulateQ (fullImplBucket cka prng fs lam Δcka qep tL) oa).run sw) >>=
    fun res => pure (match res.2.2 with
      | none => false
      | some tWin => res.2.1.win && authLosingConditionsAvoided (2 + Δcka) tL tWin res.2.1)

private def authOutBucket (Δ : ℕ) (tL : Option ℕ)
    (ew : CKABucketEState Γ T Sig SS RS M E I) : Bool :=
  match ew.2 with
  | none => false
  | some tWin => !ew.1.abort && ew.1.g.win && authLosingConditionsAvoided Δ tL tWin ew.1.g

private def runRBucket (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) {α : Type}
    (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (ew : CKABucketEState Γ T Sig SS RS M E I)
    (sc : CKA.GameState Γ T) : ProbComp Bool :=
  ((simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
      CKA.oracleImpl cka Δcka (healEpoch tL))
    ((simulateQ (implCKABucket cka prng fs Δcka qep tL) oa).run ew)).run sc) >>=
    fun res => pure (authOutBucket (2 + Δcka) tL res.1.2)

private theorem runLBucket_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep : ℕ) (tL : Option ℕ) {α : Type} (t : (ASpecB).Domain)
    (k : (ASpecB).Range t →
      AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) (winEp : Option ℕ) :
    runLBucket cka prng fs lam Δcka qep tL (query (spec := ASpecB) t >>= k) (s, winEp) =
      ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) +
        oracleImpl (scheme cka prng fs lam) (2 + Δcka) qep (bucketAuthCfg Δcka tL)) t).run s >>=
        fun res => runLBucket cka prng fs lam Δcka qep tL (k res.1)
          (res.2, if !s.win && res.2.win then queryTargetEpoch t winEp else winEp)) := by
  simp [runLBucket, StateT.run_bind, fullImplBucket_run_eq]

private theorem runRBucket_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) {α : Type} (t : (ASpecB).Domain)
    (k : (ASpecB).Range t →
      AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ) (sc : CKA.GameState Γ T) :
    runRBucket cka prng fs Δcka qep tL (query (spec := ASpecB) t >>= k) (es, winEp) sc =
      (((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
          CKA.oracleImpl cka Δcka (healEpoch tL))
        ((implEBucketRaw (hooksCKABucket cka prng fs Δcka tL)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL) t).run es)).run sc) >>=
        fun res => runRBucket cka prng fs Δcka qep tL (k res.1.1)
          (res.1.2, if !es.g.win && res.1.2.g.win then queryTargetEpoch t winEp else winEp)
          res.2) := by
  simp [runRBucket, StateT.run_bind, implCKABucket_run_eq, simulateQ_bind]

private theorem evalDist_runLBucket_eq_pure_false_of_doomedBucket
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) {α : Type}
    (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (sw : GameState (PartyState Γ T Sig SS RS) M (Header T × E) × Option ℕ)
    (hdb : DoomedBucket Δcka tL sw) :
    𝒟[runLBucket cka prng fs lam Δcka qep tL oa sw] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨a, sw'⟩ hmem
  dsimp only
  rw [doomedBucket_not_win Δcka tL sw'
    (doomedBucket_simulateQ cka prng fs lam Δcka qep tL oa hdb hmem)]

private theorem evalDist_runLBucket_eq_pure_false_of_doomedAll
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) {α : Type}
    (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)) (winEp : Option ℕ)
    (hd : DoomedAll Δcka tL s) (hw : s.win = false) :
    𝒟[runLBucket cka prng fs lam Δcka qep tL oa (s, winEp)] =
      𝒟[(pure false : ProbComp Bool)] :=
  evalDist_runLBucket_eq_pure_false_of_doomedBucket cka prng fs lam Δcka qep tL oa (s, winEp)
    (by simp [DoomedBucket, hw, hd])

private theorem evalDist_runRBucket_eq_pure_false_of_abort
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) {α : Type}
    (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ) (sc : CKA.GameState Γ T) (hab : es.abort = true) :
    𝒟[runRBucket cka prng fs Δcka qep tL oa (es, winEp) sc] =
      𝒟[(pure false : ProbComp Bool)] := by
  apply evalDist_bind_eq_pure_false
  rintro ⟨⟨a, ew'⟩, sc'⟩ hmem
  have hab' : ew'.1.abort = true :=
    abort_simulateQ_bucket cka prng fs Δcka qep tL
      (CKA.oracleImpl cka Δcka (healEpoch tL)) oa hab hmem
  cases ew' with
  | mk es' winEp' =>
    dsimp only at hab'
    cases winEp' <;> simp [authOutBucket, hab']

private theorem runLBucket_eq_runRBucket_of_sync
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) {α : Type}
    (oa : AdversaryComp (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9 cka Δcka tL (bucketTStar Δcka tL) s es sc) (winEp : Option ℕ) :
    𝒟[runLBucket cka prng fs lam Δcka qep tL oa (s, winEp)] =
      𝒟[runRBucket cka prng fs Δcka qep tL oa (es, winEp) sc] := by
  induction oa using OracleComp.inductionOn generalizing s es sc winEp with
  | pure a =>
    simp only [runLBucket, runRBucket, simulateQ_pure, StateT.run_pure, pure_bind]
    cases winEp with
    | none => rfl
    | some tWin =>
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hok : authLosingConditionsAvoided (2 + Δcka) tL tWin s =
          authLosingConditionsAvoided (2 + Δcka) tL tWin es.g := by
        rw [hs.s_eq]; rfl
      simp [authOutBucket, hs.no_abort, hwin, hok]
  | query_bind t k ih =>
    change 𝒟[runLBucket cka prng fs lam Δcka qep tL (query (spec := ASpecB) t >>= k)
        (s, winEp)] =
      𝒟[runRBucket cka prng fs Δcka qep tL (query (spec := ASpecB) t >>= k)
        (es, winEp) sc]
    rw [runLBucket_query_bind, runRBucket_query_bind]
    let contL : (ASpecB).Range t × GameState (PartyState Γ T Sig SS RS) M (Header T × E) →
        ProbComp Bool :=
      fun res => runLBucket cka prng fs lam Δcka qep tL (k res.1)
        (res.2, if !s.win && res.2.win then queryTargetEpoch t winEp else winEp)
    let contR :
        ((ASpecB).Range t ×
          EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)) ×
          CKA.GameState Γ T → ProbComp Bool :=
      fun res => runRBucket cka prng fs Δcka qep tL (k res.1.1)
        (res.1.2, if !es.g.win && res.1.2.g.win then queryTargetEpoch t winEp else winEp)
        res.2
    change 𝒟[(((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState (PartyState Γ T Sig SS RS) M (Header T × E)) ProbComp) +
        oracleImpl (scheme cka prng fs lam) (2 + Δcka) qep (bucketAuthCfg Δcka tL)) t).run s >>=
          contL] =
      𝒟[((simulateQ
          ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) +
            CKA.oracleImpl cka Δcka (healEpoch tL))
          ((implEBucketRaw (hooksCKABucket cka prng fs Δcka tL)
            (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL) t).run es)).run sc) >>= contR]
    have ih' : ∀ u {s' es' sc'}, Sync9 cka Δcka tL (bucketTStar Δcka tL) s' es' sc' →
        𝒟[contL (u, s')] = 𝒟[contR ((u, es'), sc')] := by
      intro u s' es' sc' hs'
      dsimp only [contL, contR]
      have hw0 : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hw1 : s'.win = es'.g.win := by rw [hs'.s_eq]; rfl
      rw [hw0, hw1]
      exact ih u hs' _
    have hdoomed : ∀ u {s'}, DoomedAll Δcka tL s' → s'.win = false →
        𝒟[contL (u, s')] = 𝒟[(pure false : ProbComp Bool)] :=
      fun u _ hd hw' => evalDist_runLBucket_eq_pure_false_of_doomedAll
        cka prng fs lam Δcka qep tL (k u) _ _ hd hw'
    have habort : ∀ u
        {es' : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)} {sc'},
        es'.abort = true → 𝒟[contR ((u, es'), sc')] = 𝒟[(pure false : ProbComp Bool)] :=
      fun u _ _ hab => evalDist_runRBucket_eq_pure_false_of_abort
        cka prng fs Δcka qep tL (k u) _ _ _ hab
    let tS := bucketTStar Δcka tL
    rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · dsimp only [QueryImpl.add_apply, implEBucketRaw]
      exact step_coins cka n (fun u => ih' u hs)
    · dsimp only [QueryImpl.add_apply, oracleImpl, implEBucketRaw]
      by_cases hw : es.g.win = true
      · have hwin : s.win = true := by rw [hs.s_eq]; exact hw
        dsimp only [transmitImpl, transmitEBucket]
        simp [hs.no_abort, hw, hwin, ih' none hs]
      · have hw_f : es.g.win = false := Bool.eq_false_iff.mpr hw
        rw [transmitImpl_run_eq cka prng fs lam Δcka qep tL tS hs hw_f]
        dsimp only [transmitEBucket]
        rw [vSend_hooksCKABucket_eq cka prng fs Δcka tL tS]
        simp only [hs.no_abort, hw_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
        cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, OracleComp.evalDist_bind_const]
          exact ih' none hs
        | some s₁ =>
          have hs₁_st : s₁.st = es.g.st := by
            unfold GameState.epMgmt at hep
            split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
          have hs₁_win : s₁.win = false := by
            rw [(hs.epMgmt_tL_inv hep).1, hw_f]
          simp only [hs₁_st]
          by_cases hsend : P.sendsIn (es.g.epoch P + 1) = true
          · have hq : ¬qep < es.g.epoch P + 1 := by
              intro hq; simp [GameState.epMgmt, hsend, hq] at hep
            have hs₁_ep : s₁.epoch P = es.g.epoch P + 1 := by
              unfold GameState.epMgmt at hep
              simp only [hsend, hq, ↓reduceIte] at hep
              split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
            have hs₁_idx : s₁.idx P = 0 := by
              unfold GameState.epMgmt at hep
              simp only [hsend, hq, ↓reduceIte] at hep
              split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
            have hsend_eq := fun coins =>
              send_new_eq cka prng fs Δcka tL tS (m := m) (coins := coins) hs hsend
            dsimp only at hsend_eq
            by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
            · have hvR := vSend_new_local cka prng fs Δcka tL tS
                (m := m) (r := r) (s₁ := s₁) hs hsend hloc
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
              simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
              refine evalDist_bind_congr _ _ _ fun coins => ?_
              rw [hsend_eq coins]
              exact ih' _ (hs.sync9_send_new prng fs hsend hep coins m false)
            · have hloc_f : isLocal tL Δcka (es.g.epoch P) = false := Bool.eq_false_iff.mpr hloc
              obtain ⟨l, htL⟩ : ∃ l, tL = some l := by
                cases h : tL
                · simp [isLocal, h] at hloc_f
                · exact ⟨_, rfl⟩
              have hloc' : es.g.epoch P < l + 2 + Δcka := by simpa [isLocal, htL] using hloc_f
              cases r with
              | none =>
                have hvR := vSend_new_nonlocal_none cka prng fs Δcka tL tS
                  (m := m) (s₁ := s₁) hs hsend hloc_f
                rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
                refine evalDist_bind_congr _ _ _ fun coins => ?_
                rw [hsend_eq coins]
                exact ih' _ (hs.sync9_send_new prng fs hsend hep coins m false)
              | some coins =>
                by_cases hle : es.g.epoch P + 1 ≤ l
                · have hvR := vSend_new_nonlocal_some_le cka prng fs Δcka tL tS
                    (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hle
                  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                  simp only [pure_bind, hs₁_ep, hs₁_idx]
                  rw [hsend_eq coins]
                  exact ih' _ (hs.sync9_send_new prng fs hsend hep coins m false)
                · have hgt : l < es.g.epoch P + 1 := by omega
                  have hvR := vSend_new_nonlocal_some_gt cka prng fs Δcka tL tS
                    (m := m) (coins := coins) (s₁ := s₁) hs htL hsend hloc_f hgt
                  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
                  simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                    StateT.run_pure, simulateQ_pure]
                  have hR := habort none (es' := { es with abort := true })
                    (sc' := sc) rfl
                  have hdAll := doomedAll_of_sendBad_gt hs hw_f htL hloc' hsend hep hgt
                    (send cka prng fs (s.st P) m coins).1 m (send cka prng fs (s.st P) m coins).2
                  have hL := hdoomed (some (send cka prng fs (s.st P) m coins).2) hdAll
                    (by simp [GameState.record, realGS, hs₁_win])
                  exact hL.trans hR.symm
          · have hnsend : P.sendsIn (es.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsend
            have hs₁_eq : s₁ = es.g := by
              unfold GameState.epMgmt at hep
              simp only [hnsend, Bool.false_eq_true, ↓reduceIte] at hep
              split_ifs at hep
              injection hep with hep
              exact hep.symm
            subst hs₁_eq
            obtain ⟨hsendL, hsendR⟩ :=
              vSend_same_epoch cka prng fs Δcka tL tS (m := m) (r := r) hs hnsend
            have hreal_eq : realGS sc es.g = s := hs.s_eq.symm
            rw [StateT.run_bind, hsendR]
            simp only [hsendL, hreal_eq, pure_bind, OracleComp.evalDist_bind_const]
            exact ih' _ (hs.sync9_send_same hnsend _ m _ false)
    · dsimp only [QueryImpl.add_apply, oracleImpl, implEBucketRaw, challImpl, challEBucket,
        bucketAuthCfg]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, simulateQ_pure]
      by_cases hw : s.win = true
      · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
        exact ih' none hs
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.or_true]
        cases r with
        | none =>
          simp only [samIfNec, StateT.run_monadLift, monadLift_self,
            StateT.run_bind, bind_assoc, pure_bind]
          cases s.epMgmt (2 + Δcka) qep P false <;>
            simp [StateT.run_pure, OracleComp.evalDist_bind_const, ih' none hs]
        | some c =>
          simp only [samIfNec, StateT.run_monadLift, monadLift_self,
            StateT.run_bind, pure_bind]
          cases s.epMgmt (2 + Δcka) qep P true <;>
            simp [StateT.run_pure, ih' none hs]
    · dsimp only [QueryImpl.add_apply, oracleImpl, implEBucketRaw, deliverImpl, deliverE,
        bucketAuthCfg]
      simp only [vRecv_hooksCKABucket_eq, commitE_hooksCKABucket_eq cka prng fs Δcka tL tS]
      let t_eff := if lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 then c.1.1 else c.1.1 + 1
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
      have hch_eq : s.chall = es.g.chall := by rw [hs.s_eq]; rfl
      simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, StateT.run_bind, StateT.run_get,
        pure_bind]
      by_cases hw : es.g.win = true
      · simp [hw, ih' none hs]
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        cases hin : es.g.inTransit P.other c with
        | none => simp [ih' none hs]
        | some rec =>
          simp only []
          obtain ⟨hmem, hsnd, hct⟩ := mem_trans_of_inTransit hin
          obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.trans_inv rec hmem
          have hpos_c : rec.pos.epoch = c.1.1 := by rw [← hct, ht_ep]
          have hnsend : P.sendsIn c.1.1 = false := by
            have h1 : P.other.sendsIn c.1.1 = true := by rw [← hpos_c, ← hsnd]; exact hsnd_sends
            rw [sendsIn_other, Bool.not_eq_true'] at h1; exact h1
          have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
            have hle_o : c.1.1 ≤ es.g.epoch P.other := by rw [← hpos_c, ← hsnd]; exact hle_snd
            have hle2 := hs.epoch_le P.other; rw [Party.other_other] at hle2; omega
          by_cases hstep : c.1.1 = es.g.epoch P + 1
          · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
              hs.epoch_eq_of_deliver_step hmem hsnd (by rw [hct]; exact hstep)
            obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ := hs.cka_step P heq_other
            have hcT : c.1.2 = some T_t := by
              rw [← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
            have hcache' : es.h.cache c.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
            obtain ⟨hrcvL, hrcvR⟩ := vRecv_new_honest cka prng fs Δcka tL t_eff
              (rec := some rec) hs hnsend hstep hcT hcache' hI
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
            simp only [pure_bind]
            cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
            | none => simp [ih' (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              have hpos_ep : rec.pos.epoch = es.g.epoch P + 1 := by omega
              have hnsend_pos : P.sendsIn rec.pos.epoch = false := by rwa [hpos_c]
              have hcom := commitE_new cka prng fs Δcka tL tS
                (prng.up (es.g.st P).root I_t).1
                (Function.update (es.g.st P).vR c.1.1 (some v'))
                hs hpos_ep heq_other T_t hl_msg
              have hsync := hs.sync9_accept_new
                (prng.up (es.g.st P).root I_t).1
                (Function.update (es.g.st P).vR c.1.1 (some v'))
                hpos_ep heq_other hnsend_pos T_t hagr
              dsimp only at hcom hsync
              rw [hpos_c] at hcom hsync
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
              exact ih' _ hsync
          · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
            obtain ⟨hrcvL, hrcvR⟩ := vRecv_same_epoch cka prng fs Δcka tL t_eff
              (rec := some rec) hs hnsend hle_P
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, hrcvR]
            simp only [pure_bind]
            cases hv : (es.g.st P).vR c.1.1 with
            | none => simp [ih' (some .rejected) hs]
            | some v =>
              simp only []
              cases hfs : fs.receive v c.1 c.2 with
              | none => simp [ih' (some .rejected) hs]
              | some val =>
                rcases val with ⟨v', i', m'⟩
                have hpos_le : rec.pos.epoch ≤ es.g.epoch P := by omega
                have hcom := commitE_same cka prng fs Δcka tL tS (P := P)
                  (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                  (pos := rec.pos) (es := es) (sc := sc) rfl
                have hsync := hs.sync9_accept_same
                  (Function.update (es.g.st P).vR c.1.1 (some v')) hpos_le
                simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                  simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure, hch_eq]
                exact ih' _ hsync
    · dsimp only [QueryImpl.add_apply, oracleImpl, implEBucketRaw, injectImpl, injectE,
        bucketAuthCfg]
      simp only [vRecv_hooksCKABucket_eq, commitE_hooksCKABucket_eq cka prng fs Δcka tL tS]
      let t_eff := if lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 then c.1.1 else c.1.1 + 1
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.s_eq]; rfl
      have hsafe_eq : s.safeInj (2 + Δcka) = es.g.safeInj (2 + Δcka) := by rw [hs.s_eq]; rfl
      have htriv_eq : ∀ pos, s.trivial (2 + Δcka) pos = es.g.trivial (2 + Δcka) pos :=
        fun pos => by rw [hs.s_eq]; rfl
      simp only [hs.no_abort, Bool.false_or, hwin, hin_eq, hsafe_eq,
        StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hcond : (es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
      · simp [hcond, ih' none hs]
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        have hsafe : es.g.safeInj (2 + Δcka) = true := by cases h : es.g.safeInj (2 + Δcka) <;> simp_all
        by_cases hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
        · obtain ⟨hrcvL, hrcvR⟩ := vRecv_guard_true cka prng fs Δcka tL t_eff (rec := none) hs hguard
          dsimp only [scheme]; rw [hrcvL, StateT.run_bind, hrcvR]; simp [ih' (some .rejected) hs]
        · have hnsend : P.sendsIn c.1.1 = false := by cases h : P.sendsIn c.1.1 <;> simp_all
          have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by simp [hnsend] at hguard; omega
          by_cases hstep : c.1.1 = es.g.epoch P + 1
          · have htriv_f : ∀ i', es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false :=
              fun i' => hs.trivial_false_of_safeInj (P := P) hsafe (by dsimp; omega)
            cases hc2 : c.1.2 with
            | none =>
              obtain ⟨hrcvL, hrcvR⟩ := vRecv_new_none cka prng fs Δcka tL t_eff (rec := none) hs hnsend hstep hc2
              dsimp only [scheme]; rw [hrcvL, StateT.run_bind, hrcvR]; simp [ih' (some .rejected) hs]
            | some Tn =>
              by_cases hhon_ex : ∃ I_t, es.h.cache c.1.1 = some (Tn, I_t)
              · rcases hhon_ex with ⟨I_t, hcache'⟩
                have hle_max : c.1.1 ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
                  by_contra hgt; have hnone := hs.cache_gt c.1.1 (by omega)
                  rw [hnone] at hcache'; nomatch hcache'
                have heq_other : es.g.epoch P + 1 = es.g.epoch P.other := by
                  have hle2 := hs.epoch_le P.other; rw [Party.other_other] at hle2
                  cases P <;> simp [Party.other] at hle_max hstep hle2 ⊢ <;> omega
                obtain ⟨T_t, I_t', hcache_step, _, _, hI, _⟩ := hs.cka_step P heq_other
                rw [← heq_other, ← hstep, hcache'] at hcache_step
                injection hcache_step with hpair; injection hpair with hT_eq hI_eq; subst hT_eq hI_eq
                obtain ⟨hrcvL, hrcvR⟩ :=
                  vRecv_new_honest cka prng fs Δcka tL t_eff (rec := none) hs hnsend hstep hc2 hcache' hI
                dsimp only [scheme]; rw [hrcvL, StateT.run_bind, hrcvR]; simp only [pure_bind]
                cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
                | none => simp [ih' (some .rejected) hs]
                | some val =>
                  rcases val with ⟨v', i', m'⟩
                  simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
                  by_cases hqep : qep + 1 < c.1.1
                  · simp [hqep, ih' (some .rejected) hs]
                  · simp only [hqep, ↓reduceIte]
                    by_cases hfull : lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 = true
                    · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                        StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                      exact ih' (some .rejected) (hs.sync9_win true)
                    · simp [hfull, ih' (some .rejected) hs]
              · have hhon : ∀ Tc Ik, es.h.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn := by
                  intro Tc Ik hca heq; subst heq; exact hhon_ex ⟨Ik, hca⟩
                by_cases hb : lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 = true
                · have hs_c : Sync9 cka Δcka tL c.1.1 s es sc := { hs with valid := hb }
                  by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
                  · obtain ⟨hrcvL, hrcvR⟩ :=
                      vRecv_new_dishonest_tStar_local cka prng fs Δcka tL c.1.1 (rec := none)
                        hs_c hnsend hstep hc2 hhon rfl hloc
                    dsimp only [scheme]; simp only [hb, ↓reduceIte]
                    rw [hrcvL, StateT.run_bind, hrcvR]; simp only [pure_bind]
                    cases hfs : fs.receive
                        (fs.initReceiver (prng.up (es.g.st P).root (cka.receive (s.st P).γ Tn).2).2)
                        c.1 c.2 with
                    | none => simp [ih' (some .rejected) hs]
                    | some val =>
                      rcases val with ⟨v', i', m'⟩
                      simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
                      by_cases hqep : qep + 1 < c.1.1
                      · simp [hqep, ih' (some .rejected) hs]
                      · simp only [hqep, ↓reduceIte, hb, StateT.run_bind, StateT.run_set,
                          StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                        exact ih' (some .rejected) (hs.sync9_win true)
                  · have hloc_f : isLocal tL Δcka (es.g.epoch P) = false := Bool.eq_false_iff.mpr hloc
                    have hd4 : Doomed4 tL s :=
                      (hs_c.doomed4_or_local_of_safeInj_tStar (P := P) hsafe (by omega)).resolve_left hloc
                    have hw_s : s.win = false := by rw [hwin]; cases h : es.g.win <;> simp_all
                    have hdAll : DoomedAll Δcka tL s := fun _ _ => Or.inr (Or.inr (Or.inr hd4))
                    have hrcvR := vRecv_new_dishonest_tStar_nonlocal cka prng fs Δcka tL c.1.1
                      (rec := none) hs_c hnsend hstep hc2 hhon rfl hloc_f
                    simp only [hb, ↓reduceIte]; rw [StateT.run_bind, hrcvR]
                    simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify,
                      StateT.run_pure, simulateQ_pure]
                    have hR := habort none (es' := { es with abort := true }) (sc' := sc) rfl
                    dsimp only [scheme]
                    cases hrcvL : receive cka prng fs (s.st P) c with
                    | none =>
                      simp only [StateT.run_pure, pure_bind]
                      exact (hdoomed (some .rejected) hdAll hw_s).trans hR.symm
                    | some res =>
                      rcases res with ⟨st', t', i', m'⟩
                      have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcvL; subst ht'
                      simp only [htriv_eq, htriv_f, hb, Bool.false_eq_true, ↓reduceIte]
                      by_cases hqep : qep + 1 < c.1.1
                      · simp only [hqep, ↓reduceIte, StateT.run_pure, pure_bind]
                        exact (hdoomed (some .rejected) hdAll hw_s).trans hR.symm
                      · simp only [hqep, ↓reduceIte, StateT.run_bind, StateT.run_set,
                          pure_bind, StateT.run_pure]
                        have hL : 𝒟[contL (some .rejected, { s with win := true })] =
                            𝒟[(pure false : ProbComp Bool)] := by
                          dsimp only [contL, queryTargetEpoch]
                          simp only [hw_s, Bool.not_false, Bool.true_and, ↓reduceIte]
                          exact evalDist_runLBucket_eq_pure_false_of_doomedBucket
                            cka prng fs lam Δcka qep tL (k (some .rejected))
                            ({ s with win := true }, some c.1.1)
                            (by simp [DoomedBucket]; exact Or.inr (Or.inr (Or.inr hd4)))
                        exact hL.trans hR.symm
                · have hb_f : lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 = false :=
                    Bool.eq_false_iff.mpr hb
                  have hne_eff : c.1.1 ≠ t_eff := by simp [t_eff, hb_f]
                  have hrcvR := vRecv_new_dishonest_ne cka prng fs Δcka tL t_eff (rec := none)
                    hs hnsend hstep hc2 hhon hne_eff
                  rw [StateT.run_bind, hrcvR]; simp only [pure_bind, StateT.run_pure, simulateQ_pure]
                  dsimp only [scheme]
                  cases hrcvL : receive cka prng fs (s.st P) c with
                  | none => simp [ih' (some .rejected) hs]
                  | some res =>
                    rcases res with ⟨st', t', i', m'⟩
                    have ht' : t' = c.1.1 := receive_t_eq cka prng fs hrcvL; subst ht'
                    simp only [htriv_eq, htriv_f, hb_f, Bool.false_eq_true, ↓reduceIte]
                    by_cases hqep : qep + 1 < c.1.1 <;> simp [hqep, ih' (some .rejected) hs]
          · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
            obtain ⟨hrcvL, hrcvR⟩ := vRecv_same_epoch cka prng fs Δcka tL t_eff (rec := none) hs hnsend hle_P
            dsimp only [scheme]; rw [hrcvL, StateT.run_bind, hrcvR]; simp only [pure_bind]
            cases hv : (es.g.st P).vR c.1.1 with
            | none => simp [ih' (some .rejected) hs]
            | some v =>
              simp only []
              cases hfs : fs.receive v c.1 c.2 with
              | none => simp [ih' (some .rejected) hs]
              | some val =>
                rcases val with ⟨v', i', m'⟩; simp only []
                by_cases hqep : qep + 1 < c.1.1
                · simp [hqep, ih' (some .rejected) hs]
                · simp only [hqep, ↓reduceIte, htriv_eq]
                  by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
                  · have hcom := commitE_same cka prng fs Δcka tL tS (P := P)
                      (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                      (pos := ⟨P.other, c.1.1, i'⟩) (es := es) (sc := sc) rfl
                    have hsync := hs.sync9_accept_same
                      (Function.update (es.g.st P).vR c.1.1 (some v'))
                      (pos := ⟨P.other, c.1.1, i'⟩) hle_P
                    simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                      StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify, simulateQ_pure]
                    exact ih' _ hsync
                  · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                    by_cases hfull : lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 = true
                    · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                        StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                      exact ih' (some .rejected) (hs.sync9_win true)
                    · simp [hfull, ih' (some .rejected) hs]
    · dsimp only [QueryImpl.add_apply, oracleImpl, implEBucketRaw, corrImpl, corrEBucket]
      have hwin : s.win = es.g.win := by rw [hs.s_eq]; rfl
      have hca : s.corrAllowed P = es.g.corrAllowed P := by rw [hs.s_eq]; rfl
      simp only [hs.no_abort, Bool.false_or, hwin, hca, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hguard : (es.g.win || !es.g.corrAllowed P) = true
      · simp [hguard, ih' none hs]
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hwin_f : es.g.win = false := by cases hw : es.g.win <;> simp_all
        have hγ := hs.γ_eq P
        by_cases hloc : isLocal tL Δcka (es.g.epoch P) = true
        · simp only [hloc, ↓reduceIte] at hγ
          have hst_eq : realParty (es.g.st P) (s.st P).γ (es.g.st P).root (es.g.st P).vS
              (es.g.st P).vR = s.st P := by rw [hs.s_eq]; rfl
          simp only [hooksCKABucket, hooksCKA, liftH_run, StateT.run_bind, StateT.run_pure,
            StateT.run_modify, StateT.run_set, simulateQ_pure, hγ, pure_bind, hst_eq]
          exact ih' (some (s.st P)) (hs.sync9_corr P)
        · simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hγ
          rcases htL : tL with _ | l
          · simp [isLocal, htL] at hloc
          · have hloc' : es.g.epoch P < l + 2 + Δcka := by simp [isLocal, htL] at hloc; exact hloc
            have hfin_f : sc.finished Δcka (healEpoch (some l)) P = false := by
              unfold CKA.GameState.finished
              rw [decide_eq_false_iff_not, hs.sc_epoch l htL P]; simp only [healEpoch]; omega
            by_cases hall : sc.allowCorr (healEpoch (some l)) = true
            · have hst_eq : realParty (es.g.st P) (sc.st P) (es.g.st P).root (es.g.st P).vS
                  (es.g.st P).vR = s.st P := by rw [hs.s_eq]; simp [realGS, realVP, realParty, hγ]
              simp only [hooksCKABucket, hooksCKA, hγ, liftH_run, liftC, CKA.corrQuery,
                StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
                QueryImpl.add_apply, CKA.oracleImpl, CKA.corrImpl, hall, Bool.true_or,
                ↓reduceIte, StateT.run_get, pure_bind, StateT.run_pure, simulateQ_pure,
                StateT.run_modify, StateT.run_set, bind_assoc, hst_eq]
              exact ih' (some (s.st P)) (hs.sync9_corr P)
            · have hall_f : sc.allowCorr (healEpoch (some l)) = false := Bool.eq_false_iff.mpr hall
              simp only [hooksCKABucket, hooksCKA, hγ, liftH_run, liftC, CKA.corrQuery,
                StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_query_eq,
                QueryImpl.add_apply, CKA.oracleImpl, CKA.corrImpl, hall_f, hfin_f, Bool.or_self,
                Bool.false_eq_true, ↓reduceIte, StateT.run_get, pure_bind, StateT.run_pure,
                simulateQ_pure, abortE, StateT.run_modify, StateT.run_set, bind_assoc]
              have hR := habort none (es' := { es with abort := true }) (sc' := sc) rfl
              have hdAll := doomedAll_of_corr_nonlocal_gt hs hwin_f htL hloc' hall_f
              have hL := hdoomed (some (s.st P)) hdAll
                (by rw [hs.s_eq]; simp [GameState.afterCorr, GameState.leak, realGS, hwin_f])
              exact hL.trans hR.symm

private theorem bucketAuthGame_eq_runLBucket
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (tL : Option ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
        (scheme cka prng fs lam) (2 + Δcka) qep tL A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLBucket cka prng fs lam Δcka qep tL A
          (initState (scheme cka prng fs lam) (kr, kc) false, none)) := by
  unfold _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
    _root_.CryptoGames.SM.BucketAuthBridge.bucketRun runLBucket fullImplBucket
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]
  exact bind_congr fun _ => bind_congr fun _ => bind_congr fun ⟨_, _, _⟩ => rfl

end BucketProof

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

section Stage2Auth

/-- Pointwise Stage-2 `canon`-bucket Lemma 9 at bucket `tL`. -/
theorem lemma9_bucket_at (hc : cka.Correct) (tL : Option ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthAdvantage
        (scheme cka prng fs lam) (2 + Δcka) qep tL A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuthBucket cka prng fs lam Δcka qep tL A)] {true} := by
  apply le_of_eq
  unfold _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthAdvantage
  rw [bucketAuthGame_eq_runLBucket]
  congr 1
  have hvg := bucketTStar_admissible Δcka tL
  cases htL : tL with
  | none =>
    subst htL
    unfold CKA.branch redCKAAuthBucket runCKAAuthBucket
    rw [initCKA_zero_eq cka prng fs lam none (bucketTStar Δcka none)]
    unfold initCKA
    simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
      pure_bind, bind_assoc, simulateQ_bind, AuthL9.simulateQ_sampleT_run, map_bind]
    symm
    refine (evalDist_bind_congr ($ᵗ KC) _
      (fun _ => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLBucket cka prng fs lam Δcka qep none A
          (initState (scheme cka prng fs lam) (kr, kc) false, none)) ?_).trans ?_
    · intro kc_ext
      refine evalDist_bind_congr _ _ _ fun kr => evalDist_bind_congr _ _ _ fun kc => ?_
      symm
      refine (runLBucket_eq_runRBucket_of_sync cka prng fs lam Δcka qep none A
        (AuthL9.sync9_init_none cka prng fs lam Δcka (bucketTStar Δcka none) hc hvg kr kc kc_ext)
        none).trans ?_
      dsimp only [runRBucket]
      refine congrArg (fun c => 𝒟[c]) (bind_congr fun ⟨⟨_, _, winEp⟩, _⟩ => ?_)
      cases winEp <;> simp [authOutBucket]
    · exact OracleComp.evalDist_bind_const ($ᵗ KC) _
  | some l =>
    subst htL
    unfold CKA.branch redCKAAuthBucket runCKAAuthBucket
    rw [initCKA_zero_eq cka prng fs lam (some l) (bucketTStar Δcka (some l))]
    unfold initCKA
    simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_pure,
      pure_bind, bind_assoc, simulateQ_bind, AuthL9.simulateQ_sampleT_run, map_bind]
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
    refine evalDist_bind_congr _ _ _ fun kc => evalDist_bind_congr _ _ _ fun kr => ?_
    refine (runLBucket_eq_runRBucket_of_sync cka prng fs lam Δcka qep (some l) A
      (AuthL9.Sync9.sync9_init prng fs lam hc hvg kr kc) none).trans ?_
    dsimp only [runRBucket]
    refine congrArg (fun c => 𝒟[c]) (bind_congr fun ⟨⟨_, _, winEp⟩, _⟩ => ?_)
    cases winEp <;> simp [authOutBucket]

end Stage2Auth

end CryptoGames.SM.Construction

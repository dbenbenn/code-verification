/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
public import Computational.Proofs.CryptoGames.SM.GameProofDefs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedCKA -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedPRNG -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aStep
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aSplit
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bMain
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bForgedHdr
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2c
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthEval
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

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth

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


export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak hooksCKABucket bucketAuthCfg CKABucketEState implCKABucket)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (runCKAAuthBucket PRNGBucketAuthState resolveCorrRoot liftPBucketAuth lookupPRNGBucketAuthF)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (rootPRNGBucketAuthHybrid hooksPRNGBucketAuthHybrid initPRNGBucketAuthHybrid PRNGBucketAuthEState isHonestHdrPRNGBucket)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (hooksPRNGBucketAuthMain hooksPRNGBucketAuthForgedHdr implPRNGBucketAuthGen implPRNGBucketAuth runPRNGAuthBucketHybridGen)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (runPRNGAuthBucketHybrid redPRNGAuthBucketHybridMain redPRNGAuthBucketHybridForgedHdr redPRNGAuthBucketHybrid LocalBucketAuthState)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (lookupLocalBucketAuthF rootLocalBucketAuth hooksLocalBucketAuth hooksLocalBucketAuthMain hooksLocalBucketAuthForgedHdr)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (initLocalBucketAuth LocalBucketAuthEState isHonestHdrLocalBucket implLocalBucketAuthGen localAuthBucket)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (localAuthBucketMain localAuthBucketForgedHdr localAuthBucketPar localAuthBucketMainPar localAuthBucketForgedHdrPar)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (pbaTableEntryTy prngBucketAuthHsTy prngBucketAuthEsTy prngBucketAuthRedEsTy prngBucketAuthStage2RedEsTy)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (fsaeadMultiBucketIface fsMultiBucketCacheEntryTy fsMultiBucketTransEntryTy fsMultiBucketSessBookTy fsMultiBucketHsTy)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (fsMultiBucketVpTy fsMultiBucketRedEsTy prngBucketAuthHsEnc postLeakBucketE pbaHsCache)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (pbaHsFTbl pbaHsCorrRoot pbaHsEmptyE pbaHsSetCache pbaHsSetFTblAt)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (pbaHsSetCorrRoot resolveCorrRootE pbaTableLookupE lookupPRNGBucketAuthFC rootPRNGBucketAuthHybridC)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (prngBucketAuthStartSendC prngBucketAuthStartRecvC prngBucketAuthFsSendC prngBucketAuthFsRecvC prngBucketAuthCommitC)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (prngBucketAuthRevealC hooksPRNGBucketAuthC isHonestHdrPRNGBucketE prngBucketAuthMainStartRecvC prngBucketAuthForgedHdrRevealC)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (hooksPRNGBucketAuthMainC hooksPRNGBucketAuthForgedHdrC initPRNGBucketAuthEStateC redPRNGAuthBucketHybridProg mbHsCache)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (mbHsTableTbl mbHsSessionsTbl mbHsBook mbHsLfWin mbHsMk)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (mbHsSetCache mbHsSetTableAt mbHsSetSessionsAt mbHsSetBookAt mbHsGetBookAt)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (mbHsSetLfWin mbHsEmptyE lookupMultiBucketFC sessionsMemBucketE sessionsIdxOfBucketE)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (sessionsLenBucketE sessionsAppendOneBucketE regSessMultiBucketE regSessOptMultiBucketE validGuessBucketParAuthE)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (rootFSMultiBucketAuthC fsMultiBucketAuthStartSendC isHonestHdrMultiBucketE fsMultiBucketAuthStartRecvC fsTransFindBucketE)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (fsTransFilterBucketE fsMultiBucketAuthFsSendC fsMultiBucketAuthFsRecvC fsMultiBucketAuthCommitC rangeListBucketC)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (isExtMultiBucketEntryE anyExtMultiBucketVRE unliftMultiBucketEntryE unliftMultiBucketVRE fsMultiBucketAuthRevealC)
export Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (hooksFSMultiBucketAuthC initFSMultiBucketAuthEStateC redFSAuthMultiBucketProg)

/-! ## 1. Shallow `canon`-Bucket CKA, Multi-Epoch PRNG Hybrid, and Post-PRNG Local Game -/

section ShallowBucketAuth

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}


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


/-! ## 2. Shallow Hop-2 Base, Adjacent-Hybrid Step, Top, Telescoped, and Parity-Split Theorems -/

/-- Generic `Finset.Ico` telescope helper over `PRFPRNG` hybrids `a .. a + k`. -/
theorem prng_ico_telescope [SampleableType KR] [SampleableType I] [SampleableType K] [DecidableEq I]
    (prng : PRFPRNG KR Sig I K)
    (B : ℕ → PRFPRNG.Adversary Sig I K)
    (a k : ℕ)
    (hStep : ∀ t, a ≤ t → t < a + k →
      𝒟[PRFPRNG.branch prng true (B t)] {true} ≤ 𝒟[PRFPRNG.branch prng false (B (t + 1))] {true}) :
    𝒟[PRFPRNG.branch prng false (B a)] {true} ≤
      (∑ t ∈ Finset.Ico a (a + k + 1), PRFPRNG.advantage prng (B t)) +
      𝒟[PRFPRNG.branch prng true (B (a + k))] {true} := by
  have hOne : ∀ t, 𝒟[PRFPRNG.branch prng false (B t)] {true} ≤
      PRFPRNG.advantage prng (B t) + 𝒟[PRFPRNG.branch prng true (B t)] {true} := fun t => by
    rw [PRFPRNG.advantage_eq_boolDist, MeasureTheory.Measure.boolDist_comm,
      add_comm (MeasureTheory.Measure.boolDist _ _)]
    exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _
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

open _root_.CryptoGames.SM.Engine (TComp) in
private theorem simulateQ_liftM_unif_bucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl tspec (StateT St ProbComp)) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM mx : TComp tspec α) =
    StateT.lift mx := by
  ext st
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
    (liftM mx : TComp tspec α)).run st = (mx >>= fun a => pure (a, st))
  rw [← liftComp_eq_liftM]
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t0 r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t0) : TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t0)) : TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT St ProbComp)
          (QueryImpl.ofLift unifSpec ProbComp) + impl)
          (.inl t0)) : StateT St ProbComp (unifSpec.Range t0))).run st =
        ((liftM (OracleSpec.query t0) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

private theorem simulateQ_sampleT_run_bucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT St ProbComp)) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  rw [simulateQ_liftM_unif_bucket]
  rfl

/-- Twice the win probability of coin-averaged `redPRNGAuthBucketHybrid` in `PRFPRNG.branch prng b`
equals the sum of the win probabilities of `Main` (`forgedMode = false`) and `ForgedHdr`
(`forgedMode = true`). -/
theorem two_mul_branch_redPRNGAuthBucketHybrid
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (b : Bool) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    2 * 𝒟[PRFPRNG.branch prng b
        (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)] {true} =
      𝒟[PRFPRNG.branch prng b
          (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL t A)] {true} +
        𝒟[PRFPRNG.branch prng b
          (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL t A)] {true} := by
  have hEq :
      𝒟[PRFPRNG.branch prng b (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)] =
        𝒟[($ᵗ Bool : ProbComp Bool) >>= fun forgedMode =>
          if forgedMode then
            PRFPRNG.branch prng b (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL t A)
          else
            PRFPRNG.branch prng b (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL t A)] := by
    unfold PRFPRNG.branch redPRNGAuthBucketHybrid
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind,
      simulateQ_sampleT_run_bucket, map_bind, bind_assoc, pure_bind]
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ Bool)]
    refine evalDist_bind_congr ($ᵗ Bool) _ _ fun forgedMode => ?_
    cases forgedMode <;> rfl
  rw [hEq, evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
    MeasureTheory.lintegral_fintype]
  have hfalse : 𝒟[($ᵗ Bool : ProbComp Bool)] {false} = 1 / 2 := by simp
  have htrue : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 1 / 2 := by simp
  rw [Fintype.sum_bool, htrue, hfalse]
  simp only [ite_true, Bool.false_eq_true, ite_false, one_div]
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm 2 (𝒟[_] {true}), mul_assoc,
    mul_comm 2 (𝒟[_] {true}), mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one, mul_one, add_comm]

/-- Hop 2a (base, `t = healEpoch tL`): ideal CKA (`b = true`) on `redCKAAuthBucket` is bounded
by the sum of real PRNG (`b = false`) on `Main` and `ForgedHdr` at `t = healEpoch tL`. -/
theorem cka_branch_true_redCKAAuthBucket_le_main_add_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (tL : Option ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[_root_.CryptoGames.CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthBucket cka prng fs lam Δcka qep tL A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
          (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} +
        𝒟[PRFPRNG.branch prng false
          (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} := by
  let _ := hc
  exact (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aStep.cka_branch_true_redCKAAuthBucket_le_unsplit
      cka prng fs lam Δcka qep tL A).trans
    (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aSplit.unsplit_prng_false_le_main_add_forgedHdr
      cka prng fs lam Δcka qep tL A)

/-- **Hop 2a (`2 *` coin-averaged form)**: ideal CKA (`b = true`) on `redCKAAuthBucket` is bounded
by `2 * 𝒟[PRFPRNG.branch prng false (redPRNGAuthBucketHybrid ... (healEpoch tL) A)] {true}`. -/
theorem cka_branch_true_redCKAAuthBucket_le_two_mul_prng_false
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (tL : Option ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[_root_.CryptoGames.CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthBucket cka prng fs lam Δcka qep tL A)] {true} ≤
      2 * 𝒟[PRFPRNG.branch prng false
        (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} := by
  rw [two_mul_branch_redPRNGAuthBucketHybrid]
  exact cka_branch_true_redCKAAuthBucket_le_main_add_forgedHdr cka prng fs lam Δcka qep hc tL A

/-- Hop 2b (`Main` adjacent-epoch step): ideal PRNG (`b = true`) on `Main` at epoch `t` is
bounded by real PRNG (`b = false`) on `Main` at epoch `t + 1` for `healEpoch tL ≤ t < qep + 1`. -/
theorem prng_branch_true_redPRNGAuthBucketHybridMain_le_succ_false
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (htLo : healEpoch tL ≤ t) (htHi : t < qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL (t + 1) A)] {true} := by
  exact Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bMain.prng_branch_true_redPRNGAuthBucketHybridMain_le_succ_false_impl
    cka prng fs lam Δcka qep tL t htLo htHi A

/-- Hop 2b (`ForgedHdr` adjacent-epoch step): ideal PRNG (`b = true`) on `ForgedHdr` at epoch
`t` is bounded by real PRNG (`b = false`) on `ForgedHdr` at epoch `t + 1` for
`healEpoch tL ≤ t < qep + 1`. -/
theorem prng_branch_true_redPRNGAuthBucketHybridForgedHdr_le_succ_false
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (htLo : healEpoch tL ≤ t) (htHi : t < qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL (t + 1) A)] {true} := by
  exact Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2bForgedHdr.prng_branch_true_redPRNGAuthBucketHybridForgedHdr_le_succ_false_impl
    cka prng fs lam Δcka qep tL t htLo htHi A

/-- Hop 2b (coin-averaged adjacent-epoch step): ideal PRNG (`b = true`) at epoch `t` is bounded
by real PRNG (`b = false`) at epoch `t + 1` for `healEpoch tL ≤ t < qep + 1`. -/
theorem prng_branch_true_redPRNGAuthBucketHybrid_le_succ_false
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (htLo : healEpoch tL ≤ t) (htHi : t < qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (t + 1) A)] {true} := by
  rw [← ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    two_mul_branch_redPRNGAuthBucketHybrid, two_mul_branch_redPRNGAuthBucketHybrid]
  exact add_le_add
    (prng_branch_true_redPRNGAuthBucketHybridMain_le_succ_false cka prng fs lam Δcka qep tL t htLo htHi A)
    (prng_branch_true_redPRNGAuthBucketHybridForgedHdr_le_succ_false cka prng fs lam Δcka qep tL t htLo htHi A)

/-- Hop 2c (`Main` top, `t = qep + 1`): ideal PRNG (`b = true`) on `Main` at `t = qep + 1` is
bounded by `localAuthBucketMain`. -/
theorem prng_branch_true_redPRNGAuthBucketHybridMain_top_le_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL (qep + 1) A)] {true} ≤
      𝒟[localAuthBucketMain cka prng fs lam Δcka qep tL A] {true} := by
  exact Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2c.prng_branch_true_redPRNGAuthBucketHybridMain_top_le_local_impl
    cka prng fs lam Δcka qep tL htH A

/-- Hop 2c (`ForgedHdr` top, `t = qep + 1`): ideal PRNG (`b = true`) on `ForgedHdr` at
`t = qep + 1` is bounded by `localAuthBucketForgedHdr`. -/
theorem prng_branch_true_redPRNGAuthBucketHybridForgedHdr_top_le_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL (qep + 1) A)] {true} ≤
      𝒟[localAuthBucketForgedHdr cka prng fs lam Δcka qep tL A] {true} := by
  exact Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2c.prng_branch_true_redPRNGAuthBucketHybridForgedHdr_top_le_local_impl
    cka prng fs lam Δcka qep tL htH A

/-- **Hop 2c (`2 *` coin-averaged top, `t = qep + 1`)**: `2 *` ideal PRNG (`b = true`) at
`t = qep + 1` is bounded by `localAuthBucketMain + localAuthBucketForgedHdr`. -/
theorem two_mul_prng_branch_true_redPRNGAuthBucketHybrid_top_le_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (htH : healEpoch tL ≤ qep + 1)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    2 * 𝒟[PRFPRNG.branch prng true
        (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (qep + 1) A)] {true} ≤
      𝒟[localAuthBucketMain cka prng fs lam Δcka qep tL A] {true} +
        𝒟[localAuthBucketForgedHdr cka prng fs lam Δcka qep tL A] {true} := by
  rw [two_mul_branch_redPRNGAuthBucketHybrid]
  exact add_le_add
    (prng_branch_true_redPRNGAuthBucketHybridMain_top_le_local cka prng fs lam Δcka qep tL htH A)
    (prng_branch_true_redPRNGAuthBucketHybridForgedHdr_top_le_local cka prng fs lam Δcka qep tL htH A)

/-- Telescoped Hop 2 (`canon`-bucket coin-averaged PRNG hybrid): bounds
`CKA.branch true (redCKAAuthBucket)` by the `Finset.Ico (healEpoch tL) (qep + 2)` sum of
`2 * PRFPRNG.advantage` on `redPRNGAuthBucketHybrid` plus `localAuthBucketMain` and
`localAuthBucketForgedHdr`. -/
theorem cka_branch_true_redCKAAuthBucket_le_sum_two_mul_prng_add_local
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (tL : Option ℕ)
    (htL : tL ∈ admissibleLastLeakGuesses (2 + Δcka) (qep + 1))
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[_root_.CryptoGames.CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthBucket cka prng fs lam Δcka qep tL A)] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        2 * PRFPRNG.advantage prng
          (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)) +
      𝒟[localAuthBucketMain cka prng fs lam Δcka qep tL A] {true} +
      𝒟[localAuthBucketForgedHdr cka prng fs lam Δcka qep tL A] {true} := by
  have htH : healEpoch tL ≤ qep + 1 := by
    rcases tL with _ | l
    · simp [healEpoch]
    · simp only [admissibleLastLeakGuesses, Finset.mem_insert, reduceCtorEq, Finset.mem_image,
        Finset.mem_range, Option.some.injEq, exists_eq_right, false_or] at htL
      simp only [healEpoch]; omega
  have hBase := cka_branch_true_redCKAAuthBucket_le_two_mul_prng_false
    cka prng fs lam Δcka qep hc tL A
  set k := qep + 1 - healEpoch tL
  have hk1 : healEpoch tL + k = qep + 1 := by omega
  have hk2 : healEpoch tL + k + 1 = qep + 2 := by omega
  have hTel := prng_ico_telescope prng
    (fun t => redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)
    (healEpoch tL) k
    (fun t ht1 ht2 => prng_branch_true_redPRNGAuthBucketHybrid_le_succ_false
      cka prng fs lam Δcka qep tL t ht1 (by omega) A)
  rw [hk2, hk1] at hTel
  have hTel2 :
      2 * 𝒟[PRFPRNG.branch prng false
          (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} ≤
        (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
          2 * PRFPRNG.advantage prng
            (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)) +
        2 * 𝒟[PRFPRNG.branch prng true
          (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (qep + 1) A)] {true} := by
    calc 2 * 𝒟[PRFPRNG.branch prng false
            (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true}
        ≤ 2 * ((∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
              PRFPRNG.advantage prng
                (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)) +
            𝒟[PRFPRNG.branch prng true
              (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (qep + 1) A)] {true}) :=
          mul_le_mul_of_nonneg_left hTel zero_le
      _ = (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
            2 * PRFPRNG.advantage prng
              (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A)) +
          2 * 𝒟[PRFPRNG.branch prng true
            (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (qep + 1) A)] {true} := by
          rw [mul_add, Finset.mul_sum]
  have hTop := two_mul_prng_branch_true_redPRNGAuthBucketHybrid_top_le_local
    cka prng fs lam Δcka qep tL htH A
  rw [add_assoc]
  exact hBase.trans (hTel2.trans (add_le_add le_rfl hTop))

private theorem evalDist_bind_le_add {α : Type} (p : ProbComp α)
    (F G₁ G₂ : α → ProbComp Bool)
    (h : ∀ a, 𝒟[F a] {true} ≤ 𝒟[G₁ a] {true} + 𝒟[G₂ a] {true}) :
    𝒟[p >>= F] {true} ≤ 𝒟[p >>= G₁] {true} + 𝒟[p >>= G₂] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
    calc ∫⁻ u, 𝒟[r u >>= F] {true} ∂𝒟[query t]
        ≤ ∫⁻ u, (𝒟[r u >>= G₁] {true} + 𝒟[r u >>= G₂] {true}) ∂𝒟[query t] :=
          MeasureTheory.lintegral_mono ih
      _ = (∫⁻ u, 𝒟[r u >>= G₁] {true} ∂𝒟[query t]) +
          (∫⁻ u, 𝒟[r u >>= G₂] {true} ∂𝒟[query t]) :=
          MeasureTheory.lintegral_add_left Measurable.of_discrete _

private theorem evalDist_bind_two_mul_eq_add {α : Type} (p : ProbComp α)
    (F G₁ G₂ : α → ProbComp Bool)
    (h : ∀ a, 2 * 𝒟[F a] {true} = 𝒟[G₁ a] {true} + 𝒟[G₂ a] {true}) :
    2 * 𝒟[p >>= F] {true} = 𝒟[p >>= G₁] {true} + 𝒟[p >>= G₂] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
    rw [← MeasureTheory.lintegral_const_mul 2 Measurable.of_discrete]
    simp_rw [ih]
    exact MeasureTheory.lintegral_add_left Measurable.of_discrete _

/-- Bucket-wide post-PRNG sender-parity split (`par = false` + `par = true`) for `localAuthBucket`. -/
theorem localAuthBucket_le_par_false_add_true
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthBucket cka prng fs lam Δcka qep tL A] {true} ≤
      𝒟[localAuthBucketPar cka prng fs lam Δcka qep tL false A] {true} +
      𝒟[localAuthBucketPar cka prng fs lam Δcka qep tL true A] {true} := by
  dsimp only [localAuthBucket, localAuthBucketPar]
  simp only [simulateQ_bind]
  refine evalDist_bind_le_add _ _ _ _ fun ⟨vs, h⟩ => ?_
  cases vs with
  | none => simp [simulateQ_pure]
  | some vp =>
    rcases vp with ⟨vA, vB⟩
    simp only [simulateQ_bind]
    refine evalDist_bind_le_add _ _ _ _ fun ⟨_, es, winEp⟩ => ?_
    cases winEp with
    | none => simp [simulateQ_pure]
    | some tWin =>
      simp only [simulateQ_pure]
      cases (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g) <;>
        cases decide (Party.senderOf tWin == .A) <;> simp

/-- Bucket-wide post-PRNG sender-parity split (`par = false` + `par = true`) for
`localAuthBucketMain`. -/
theorem localAuthBucketMain_le_par_false_add_true
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthBucketMain cka prng fs lam Δcka qep tL A] {true} ≤
      𝒟[localAuthBucketMainPar cka prng fs lam Δcka qep tL false A] {true} +
      𝒟[localAuthBucketMainPar cka prng fs lam Δcka qep tL true A] {true} := by
  dsimp only [localAuthBucketMain, localAuthBucketMainPar]
  simp only [simulateQ_bind]
  refine evalDist_bind_le_add _ _ _ _ fun ⟨vs, h⟩ => ?_
  cases vs with
  | none => simp [simulateQ_pure]
  | some vp =>
    rcases vp with ⟨vA, vB⟩
    simp only [simulateQ_bind]
    refine evalDist_bind_le_add _ _ _ _ fun ⟨_, es, winEp⟩ => ?_
    cases winEp with
    | none => simp [simulateQ_pure]
    | some tWin =>
      simp only [simulateQ_pure]
      cases (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g) <;>
        cases decide (Party.senderOf tWin == .A) <;> simp

/-- Bucket-wide post-PRNG sender-parity split (`par = false` + `par = true`) for
`localAuthBucketForgedHdr`. -/
theorem localAuthBucketForgedHdr_le_par_false_add_true
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthBucketForgedHdr cka prng fs lam Δcka qep tL A] {true} ≤
      𝒟[localAuthBucketForgedHdrPar cka prng fs lam Δcka qep tL false A] {true} +
      𝒟[localAuthBucketForgedHdrPar cka prng fs lam Δcka qep tL true A] {true} := by
  dsimp only [localAuthBucketForgedHdr, localAuthBucketForgedHdrPar]
  simp only [simulateQ_bind]
  refine evalDist_bind_le_add _ _ _ _ fun ⟨vs, h⟩ => ?_
  cases vs with
  | none => simp [simulateQ_pure]
  | some vp =>
    rcases vp with ⟨vA, vB⟩
    simp only [simulateQ_bind]
    refine evalDist_bind_le_add _ _ _ _ fun ⟨_, es, winEp⟩ => ?_
    cases winEp with
    | none => simp [simulateQ_pure]
    | some tWin =>
      simp only [simulateQ_pure]
      cases (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g) <;>
        cases decide (Party.senderOf tWin == .A) <;> simp

private theorem prng_mix_ico_telescope
    (μT μF : ℕ → MeasureTheory.Measure Bool)
    (a k : ℕ)
    (hStep : ∀ t, a ≤ t → t < a + k → μT t {true} ≤ μF (t + 1) {true}) :
    μF a {true} ≤
      (∑ t ∈ Finset.Ico a (a + k + 1), (μT t).boolDist (μF t)) +
      μT (a + k) {true} := by
  have hOne : ∀ t, μF t {true} ≤ (μT t).boolDist (μF t) + μT t {true} := fun t => by
    rw [MeasureTheory.Measure.boolDist_comm, add_comm (MeasureTheory.Measure.boolDist _ _)]
    exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _
  induction k with
  | zero =>
    rw [Nat.add_zero, Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.sum_empty,
      zero_add]
    exact hOne a
  | succ k ih =>
    have ih' := ih (fun t ht1 ht2 => hStep t ht1 (by omega))
    have hNext : μT (a + k) {true} ≤
        (μT (a + k + 1)).boolDist (μF (a + k + 1)) + μT (a + k + 1) {true} :=
      (hStep (a + k) (by omega) (by omega)).trans (hOne (a + k + 1))
    have hSum : ∑ t ∈ Finset.Ico a (a + (k + 1) + 1), (μT t).boolDist (μF t) =
        (∑ t ∈ Finset.Ico a (a + k + 1), (μT t).boolDist (μF t)) +
        (μT (a + k + 1)).boolDist (μF (a + k + 1)) := by
      have heq : a + (k + 1) + 1 = (a + k + 1) + 1 := by omega
      rw [heq, Finset.sum_Ico_succ_top (by omega)]
    rw [hSum, add_assoc]
    exact ih'.trans (add_le_add le_rfl hNext)

/-- Mixture (`oa : ProbComp α`) telescoped Hop 2 + `(gMain, par)` split: bounds the mixture
`CKA.branch true (redCKAAuthBucket)` win probability by the `Finset.Ico (healEpoch tL) (qep + 2)`
sum of `2 *` mixture `PRFPRNG` `boolDist`s on `redPRNGAuthBucketHybrid` plus the 4 mixture win
probabilities `localAuthBucket{Main,ForgedHdr}Par ... {false,true}`. -/
theorem cka_branch_true_redCKAAuthBucket_mix_le_sum_two_mul_prng_add_par
    {α : Type} [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K) (lam : I) (Δcka qep : ℕ)
    (hc : cka.Correct) (oa : ProbComp α)
    (fsFam : α → FSAEADScheme K SS RS (Header T) M E)
    (tL : Option ℕ) (htL : tL ∈ admissibleLastLeakGuesses (2 + Δcka) (qep + 1))
    (A : α → SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[oa >>= fun o => _root_.CryptoGames.CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthBucket cka prng (fsFam o) lam Δcka qep tL (A o))] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        2 * (𝒟[oa >>= fun o => PRFPRNG.branch prng true
              (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
          𝒟[oa >>= fun o => PRFPRNG.branch prng false
              (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))])) +
      𝒟[oa >>= fun o => localAuthBucketMainPar cka prng (fsFam o) lam Δcka qep tL false (A o)] {true} +
      𝒟[oa >>= fun o => localAuthBucketMainPar cka prng (fsFam o) lam Δcka qep tL true (A o)] {true} +
      𝒟[oa >>= fun o => localAuthBucketForgedHdrPar cka prng (fsFam o) lam Δcka qep tL false (A o)] {true} +
      𝒟[oa >>= fun o => localAuthBucketForgedHdrPar cka prng (fsFam o) lam Δcka qep tL true (A o)] {true} := by
  have htH : healEpoch tL ≤ qep + 1 := by
    rcases tL with _ | l
    · simp [healEpoch]
    · simp only [admissibleLastLeakGuesses, Finset.mem_insert, reduceCtorEq, Finset.mem_image,
        Finset.mem_range, Option.some.injEq, exists_eq_right, false_or] at htL
      simp only [healEpoch]; omega
  have hBase :
      𝒟[oa >>= fun o => _root_.CryptoGames.CKA.branch cka Δcka (healEpoch tL) true
          (redCKAAuthBucket cka prng (fsFam o) lam Δcka qep tL (A o))] {true} ≤
        2 * 𝒟[oa >>= fun o => PRFPRNG.branch prng false
          (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL (healEpoch tL) (A o))] {true} := by
    rw [evalDist_bind_two_mul_eq_add oa _ _ _ fun o =>
      two_mul_branch_redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep false tL (healEpoch tL) (A o)]
    exact evalDist_bind_le_add oa _ _ _ fun o =>
      cka_branch_true_redCKAAuthBucket_le_main_add_forgedHdr
        cka prng (fsFam o) lam Δcka qep hc tL (A o)
  set k := qep + 1 - healEpoch tL
  have hk1 : healEpoch tL + k = qep + 1 := by omega
  have hk2 : healEpoch tL + k + 1 = qep + 2 := by omega
  have hTel := prng_mix_ico_telescope
    (fun t => 𝒟[oa >>= fun o => PRFPRNG.branch prng true
      (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))])
    (fun t => 𝒟[oa >>= fun o => PRFPRNG.branch prng false
      (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))])
    (healEpoch tL) k
    (fun t ht1 ht2 => _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_mono oa _ _ fun o _ =>
      prng_branch_true_redPRNGAuthBucketHybrid_le_succ_false
        cka prng (fsFam o) lam Δcka qep tL t ht1 (by omega) (A o))
  rw [hk2, hk1] at hTel
  have hTel2 :
      2 * 𝒟[oa >>= fun o => PRFPRNG.branch prng false
          (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL (healEpoch tL) (A o))] {true} ≤
        (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
          2 * (𝒟[oa >>= fun o => PRFPRNG.branch prng true
                (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
            𝒟[oa >>= fun o => PRFPRNG.branch prng false
                (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))])) +
        2 * 𝒟[oa >>= fun o => PRFPRNG.branch prng true
          (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL (qep + 1) (A o))] {true} := by
    calc 2 * 𝒟[oa >>= fun o => PRFPRNG.branch prng false
            (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL (healEpoch tL) (A o))] {true}
        ≤ 2 * ((∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
              (𝒟[oa >>= fun o => PRFPRNG.branch prng true
                    (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
                𝒟[oa >>= fun o => PRFPRNG.branch prng false
                    (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))])) +
            𝒟[oa >>= fun o => PRFPRNG.branch prng true
              (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL (qep + 1) (A o))] {true}) :=
          mul_le_mul_of_nonneg_left hTel zero_le
      _ = (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
            2 * (𝒟[oa >>= fun o => PRFPRNG.branch prng true
                  (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
              𝒟[oa >>= fun o => PRFPRNG.branch prng false
                  (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL t (A o))])) +
          2 * 𝒟[oa >>= fun o => PRFPRNG.branch prng true
            (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL (qep + 1) (A o))] {true} := by
          rw [mul_add, Finset.mul_sum]
  have hTopSplit :
      2 * 𝒟[oa >>= fun o => PRFPRNG.branch prng true
          (redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep tL (qep + 1) (A o))] {true} ≤
        (𝒟[oa >>= fun o => localAuthBucketMainPar cka prng (fsFam o) lam Δcka qep tL false (A o)] {true} +
          𝒟[oa >>= fun o => localAuthBucketMainPar cka prng (fsFam o) lam Δcka qep tL true (A o)] {true}) +
        (𝒟[oa >>= fun o => localAuthBucketForgedHdrPar cka prng (fsFam o) lam Δcka qep tL false (A o)] {true} +
          𝒟[oa >>= fun o => localAuthBucketForgedHdrPar cka prng (fsFam o) lam Δcka qep tL true (A o)] {true}) := by
    rw [evalDist_bind_two_mul_eq_add oa _ _ _ fun o =>
      two_mul_branch_redPRNGAuthBucketHybrid cka prng (fsFam o) lam Δcka qep true tL (qep + 1) (A o)]
    exact add_le_add
      (evalDist_bind_le_add oa _ _ _ fun o =>
        (prng_branch_true_redPRNGAuthBucketHybridMain_top_le_local
          cka prng (fsFam o) lam Δcka qep tL htH (A o)).trans
          (localAuthBucketMain_le_par_false_add_true cka prng (fsFam o) lam Δcka qep tL (A o)))
      (evalDist_bind_le_add oa _ _ _ fun o =>
        (prng_branch_true_redPRNGAuthBucketHybridForgedHdr_top_le_local
          cka prng (fsFam o) lam Δcka qep tL htH (A o)).trans
          (localAuthBucketForgedHdr_le_par_false_add_true cka prng (fsFam o) lam Δcka qep tL (A o)))
  have hFinal := hBase.trans (hTel2.trans (add_le_add le_rfl hTopSplit))
  simpa only [add_assoc] using hFinal

end ShallowBucketAuth


/-! ## 3. Costed `ReductionDsl` Programs: `redPRNGAuthBucketHybridProg` & `redFSAuthMultiBucketProg` -/

section CostedBucketAuth

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E


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


/-! ## 4. Syntactic Query Equalities, `PotOK`, and Advantage Bridges -/

@[simp] theorem lookupPRNGBucketAuthFC_queries (L : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) :
    (lookupPRNGBucketAuthFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L hE tE ikE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [lookupPRNGBucketAuthFC, Comp.queries]

@[simp] theorem rootPRNGBucketAuthHybridC_queries (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σvE : Expr OO Γ' (.opt (.base .sig))) :
    (rootPRNGBucketAuthHybridC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L tL t hE tE plE ikE σvE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [rootPRNGBucketAuthHybridC, Comp.queries]

@[simp] theorem prngBucketAuthStartSendC_queries (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (prngBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L tL t hE ctxE pE tE γE σvE rE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [prngBucketAuthStartSendC, Comp.queries]

@[simp] theorem prngBucketAuthStartRecvC_queries (L Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) :
    (prngBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep tL t hE ctxE pE tE γE σvE tnE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [prngBucketAuthStartRecvC, Comp.queries]

@[simp] theorem prngBucketAuthRevealC_queries (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbaVpTy) :
    (prngBucketAuthRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [prngBucketAuthRevealC, Comp.queries]

@[simp] theorem prngBucketAuthMainStartRecvC_queries (Δcka qep : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t)) :
    (prngBucketAuthMainStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) Δcka qep tL hE ctxE pE tE γE σvE tnE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngBucketAuthMainStartRecvC, Comp.queries]

@[simp] theorem prngBucketAuthForgedHdrRevealC_queries (tL : Option ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' pbaVpTy) :
    (prngBucketAuthForgedHdrRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prngBucketAuthForgedHdrRevealC, Comp.queries]

@[simp] theorem initPRNGBucketAuthEStateC_queries (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (bE : Expr OO Γ' .bool) :
    (initPRNGBucketAuthEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L tL t bE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [initPRNGBucketAuthEStateC, Comp.queries]

/-- Syntactic target-query count `2 + q * 2` for `redPRNGAuthBucketHybridProg`. -/
@[simp] theorem redPRNGAuthBucketHybridProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t : ℕ) (q : ℕ) :
    (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  simp [CostedReduction.totalQueries, redPRNGAuthBucketHybridProg,
    deliverEC, injectEC, vSendC,
    _root_.CryptoGames.SM.Engine.vSendStep1C, _root_.CryptoGames.SM.Engine.vRecvC,
    _root_.CryptoGames.SM.Engine.vRecvStep1C, _root_.CryptoGames.SM.Engine.commitEC,
    hooksPRNGBucketAuthC, hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthForgedHdrC,
    prngBucketAuthFsSendC, prngBucketAuthFsRecvC, prngBucketAuthCommitC, Comp.queries]

section PbaPotOK

open _root_.ReductionDsl (isGameQuery)
open _root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
  (PotOKSPrng potSPrng_ret potSPrng_ite potSPrng_caseOpt potSPrng_caseSum potSPrng_comp_const
   prngVpReady prngReady prngReady_le_one ite_fst_eq_prng prngOtherPot prngOtherPot_add_pGet prngPot_pSet_eq
   party_sendsIn_succ_false pGet_eval_st_prng cEpMgmtE_some_st_prng
   cRecordE_st_prng cGsSetStP_st_prng cGsSetWin_st_prng cAcceptE_st_prng cAfterCorrE_st_prng
   costedReduction_makesAtMostQueries_prng)
open _root_.CryptoGames.SM
  (posTy partyDec partyDec_partyEnc sendsInE otherE letE_eval orE_eval sendsInE_eval)
open _root_.CryptoGames.SM.Engine
  (esSetH cGsMk cRecPos vpMk vpId vpSetVS vpSetVR
   vSendStep1C vRecvStep1C vRecvC commitEC eval_bind eval_bind_ret)
open _root_.CryptoGames.SM.Construction (Mode)

local notation "P_prng" => isGameQuery (G := _root_.CryptoGames.PRFPRNG.spec RSt I K)

private def hooksPRNGBucketAuthModeC (fm : Bool) (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) pbaHsTy :=
  if fm then
    hooksPRNGBucketAuthForgedHdrC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep tL t
  else
    hooksPRNGBucketAuthMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep tL t

private def pbaPot (mo : Mode) (es : (Ty.denote pbaEsTy)) : ℕ :=
  if es.2.2 then 0 else prngVpReady mo es.1.1.1 + prngVpReady mo es.1.1.2

private theorem pbaPot_mk_eq (mo : Mode)
    {g1 g2 : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E pbaVpTy).denote}
    {h1 h2 : (Ty.denote pbaHsTy)} {ab : Bool} (hst : g1.1 = g2.1) :
    pbaPot mo (g1, h1, ab) = pbaPot mo (g2, h2, ab) := by
  simp only [pbaPot, hst]

private theorem rootPRNGBucketAuthHybridC_potOKS (L : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)}
    (hE : Expr OO Γ' pbaHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((rootPRNGBucketAuthHybridC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE tE plE ikE σvE).eval ρ)
      ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r) := by
  unfold rootPRNGBucketAuthHybridC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => ?_) (fun hFalse => ?_)
  · exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hFalse
    have hleTrue : decide (tE.eval ρ ≤ t) = true :=
      decide_eq_true (Nat.le_of_not_lt (of_decide_eq_false hFalse))
    exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r)
      (by simp [Comp.queries, hleTrue])

private theorem prngBucketAuthStartSendC_potOKS (L : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (rE : Expr OO Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE ctxE pE tE γE σvE rE).eval ρ)
      ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r) := by
  unfold prngBucketAuthStartSendC; rw [eval_bind_ret, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r)
      ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r)
      (fun _ => Nat.le_refl _) (by simp [Comp.queries])) (fun coins => ?_)
  rw [eval_bind]
  have hRoot := rootPRNGBucketAuthHybridC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L tL t
    (.fst (Expr.v1 (O := OO))) (.fst (.snd (.snd .v1)))
    (postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
    (.fst (.snd (.snd (.snd (.snd .v1)))))
    (.cons coins (.cons (hE.eval ρ, ctxE.eval ρ, tE.eval ρ, γE.eval ρ, σvE.eval ρ, rE.eval ρ) ρ))
    r
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRoot
  exact PotOKSPrng.bindPot hRoot (fun _ =>
    potSPrng_caseOpt (fun _ => potSPrng_ret (Nat.le_refl r))
      (fun _ _ => potSPrng_ret (Nat.le_refl r)))

private theorem prngBucketAuthStartRecvC_potOKS (L Δcka qep : ℕ) (tL : Option ℕ)
    (t : ℕ) {Γ' : List (Ty S)}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δcka qep tL t hE ctxE pE tE γE σvE tnE).eval ρ)
      ((if decide (tE.eval ρ = t) then 1 else 0) + r) := by
  unfold prngBucketAuthStartRecvC; rw [eval_bind_ret]
  refine potSPrng_caseOpt (fun _ => ?_)
    (fun _ _ => potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries]))
  refine potSPrng_ite (fun _ => ?_)
    (fun _ => potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries]))
  refine potSPrng_ite
    (fun _ => potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries]))
    (fun _ => ?_)
  refine potSPrng_ite
    (fun _ => potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries]))
    (fun _ => ?_)
  refine potSPrng_ite (fun hEq => ?_)
    (fun _ => potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries]))
  have hEq' : decide (tE.eval ρ = t) = true := by
    simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hEq
  exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries, hEq'])

private theorem prngBucketAuthMainStartRecvC_potOKS (Δcka qep : ℕ) (tL : Option ℕ)
    {Γ' : List (Ty S)}
    (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig))) (tnE : Expr OO Γ' (.base .t))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngBucketAuthMainStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka qep tL hE ctxE pE tE γE σvE tnE).eval ρ)
      r :=
  potSPrng_comp_const _ _ r r (fun _ => Nat.le_refl r)
    (by simp [prngBucketAuthMainStartRecvC_queries])

private def pbaVpOptPost (mo : Mode) (m m_other : ℕ)
    (res : (Ty.prod (.opt pbaVpTy) pbaHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some vp' => m + m_other + prngVpReady mo vp'

private theorem pba_vSendStep1C_potOKS (fm : Bool) (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (sE : Expr OO Γ' pbaVpTy) (rE : Expr OO Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (pbaVpOptPost (Mode.mk true tL t) m m_other)
      ((vSendStep1C (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t)
        hE ctxE pE sE rE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potSPrng_ite (fun hs => ?_)
    (fun _ => potSPrng_ret (by simp [pbaVpOptPost, Expr.eval, Expr.v0]))
  rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hs
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hs
  have hSS_eq :
      ∀ {Γ''},
        (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t).startSend (Γ' := Γ'') =
        prngBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L tL t (Γ' := Γ'') := by
    intro Γ''; cases fm <;> rfl
  rw [hSS_eq, eval_bind]
  have hSS := prngBucketAuthStartSendC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L tL t (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (vpΓ (.fst (.snd (.snd (.snd .v0))))) (vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, rE.eval ρ) ρ) (m + m_other)
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hSS
  have hBud :
      (if decide ((sE.eval ρ).2.2.2.2.2.2 + 1 ≤ t) then 2 else 0) + (m + m_other) ≤
        1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ) := by
    simp only [prngVpReady, prngReady, hs, Bool.true_and]; split <;> omega
  refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hSS (fun _ => ?_)).run k hk' |>.mono hBud⟩
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbaVpOptPost, Expr.eval])) (fun _ _ => ?_)
  have hNextFalse := party_sendsIn_succ_false _ _ hs
  exact potSPrng_ret (by
    simp [pbaVpOptPost, prngVpReady, prngReady, vpMk, vpId, vpTcurNat,
      Expr.eval, Expr.v0, Expr.v2, hNextFalse])

private def pbaVSendPost (mo : Mode) (m m_other : ℕ)
    (res : (Ty.prod (.opt (.prod pbaVpTy hdrCtTy)) pbaHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some (vp', _) => m + m_other + prngVpReady mo vp'

private theorem pba_vSendC_potOKS (fm : Bool) (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (sE : Expr OO Γ' pbaVpTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (pbaVSendPost (Mode.mk true tL t) m m_other)
      ((vSendC (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t)
        hE ctxE pE sE mE pairE rE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := pba_vSendStep1C_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t
    (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)
    m m_other
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKSPrng.bindPot h1 (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun _ hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbaVSendPost, pbaVpOptPost, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt
      (fun _ => potSPrng_ret (by simp [pbaVSendPost, pbaVpOptPost, hSome, Expr.eval, Expr.v0]))
      (fun _ _ => ?_)
    have hFS_eq :
        ∀ {Γ''},
          (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
            (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t).fsSend (Γ' := Γ'') =
          prngBucketAuthFsSendC (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (Γ' := Γ'') := by
      intro Γ''; cases fm <;> rfl
    rw [hFS_eq]; dsimp only [prngBucketAuthFsSendC]; rw [eval_bind, eval_ret, pure_bind]
    exact potSPrng_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
      (fun _ _ => potSPrng_ret (by
        simp [pbaVSendPost, pbaVpOptPost, hSome, prngVpReady, vpSetVS, vpMk, vpId, vpTcurNat,
          letE_eval, Expr.eval, Expr.v0, Expr.v3]))

private def pbaVRecvStep1Post (mo : Mode) (m m_other : ℕ) (s0 : (Ty.denote pbaVpTy))
    (res : (Ty.prod (.opt (.opt pbaVpTy)) pbaHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some none => m + m_other + prngVpReady mo s0
  | some (some s1) => m + m_other + max (prngVpReady mo s0) (prngVpReady mo s1)

private theorem pba_vRecvStep1C_potOKS (fm : Bool) (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (sE : Expr OO Γ' pbaVpTy) (cE : Expr OO Γ' hdrCtTy)
    (ρ : Env Γ') (m m_other : ℕ)
    (hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false) :
    PotOKSPrng P_prng (pbaVRecvStep1Post (Mode.mk true tL t) m m_other (sE.eval ρ))
      ((vRecvStep1C (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t)
        hE ctxE pE sE cE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potSPrng_ite (fun ht => ?_)
    (fun _ => potSPrng_ret (by simp [pbaVRecvStep1Post, Expr.eval, Expr.v0]))
  have ht' : (cE.eval ρ).1.1 = (sE.eval ρ).2.2.2.2.2.2 + 1 := of_decide_eq_true ht
  have hReady0 : prngVpReady (Mode.mk true tL t) (sE.eval ρ) = 0 := by
    rw [ht'] at hNotSends; simp [prngVpReady, prngReady, hNotSends]
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbaVRecvStep1Post, Expr.eval]))
    (fun Tn _ => ?_)
  cases fm
  · dsimp only [hooksPRNGBucketAuthModeC, hooksPRNGBucketAuthMainC]; rw [eval_bind]
    have hSR := prngBucketAuthMainStartRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) Δcka qep tL
      (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
      (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
      (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
      (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ))
      (m + m_other + prngReady (Mode.mk true tL t) (partyDec (sE.eval ρ).1)
        ((sE.eval ρ).2.2.2.2.2.2 + 1))
    have hBud :
        m + m_other + prngReady (Mode.mk true tL t) (partyDec (sE.eval ρ).1)
            ((sE.eval ρ).2.2.2.2.2.2 + 1) ≤
          1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ) := by
      rw [hReady0]
      have hLe1 := prngReady_le_one (Mode.mk true tL t) (partyDec (sE.eval ρ).1)
        ((sE.eval ρ).2.2.2.2.2.2 + 1)
      omega
    refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hSR (fun _ => ?_)).run k hk' |>.mono hBud⟩
    refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbaVRecvStep1Post, Expr.eval]; omega))
      (fun _ _ => potSPrng_caseOpt
        (fun _ => potSPrng_ret (by simp [pbaVRecvStep1Post, hReady0, Expr.eval]))
        (fun _ _ => potSPrng_ret (by
          rw [pbaVRecvStep1Post, hReady0]
          simp [prngVpReady, vpMk, vpId, ht', Expr.eval, Expr.v0, Expr.v4])))
  · dsimp only [hooksPRNGBucketAuthModeC, hooksPRNGBucketAuthForgedHdrC, hooksPRNGBucketAuthC]
    rw [eval_bind]
    have hSR := prngBucketAuthStartRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L Δcka qep tL t
      (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
      (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
      (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
      (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ))
      (m + m_other + prngReady (Mode.mk true tL t) (partyDec (sE.eval ρ).1)
        ((sE.eval ρ).2.2.2.2.2.2 + 1))
    simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, ht'] at hSR
    have hBud :
        (if decide ((sE.eval ρ).2.2.2.2.2.2 + 1 = t) then 1 else 0) +
          (m + m_other + prngReady (Mode.mk true tL t) (partyDec (sE.eval ρ).1)
            ((sE.eval ρ).2.2.2.2.2.2 + 1)) ≤
          1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ) := by
      by_cases hEq : ((sE.eval ρ).2.2.2.2.2.2 : ℕ) + 1 = t
      · rw [hReady0, hEq]; simp [prngReady, Nat.add_assoc]
      · rw [hReady0]
        simp only [hEq, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        have hLe1 := prngReady_le_one (Mode.mk true tL t) (partyDec (sE.eval ρ).1)
          ((sE.eval ρ).2.2.2.2.2.2 + 1)
        omega
    refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hSR (fun _ => ?_)).run k hk' |>.mono hBud⟩
    refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbaVRecvStep1Post, Expr.eval]; omega))
      (fun _ _ => potSPrng_caseOpt
        (fun _ => potSPrng_ret (by simp [pbaVRecvStep1Post, hReady0, Expr.eval]))
        (fun _ _ => potSPrng_ret (by
          rw [pbaVRecvStep1Post, hReady0]
          simp [prngVpReady, vpMk, vpId, ht', Expr.eval, Expr.v0, Expr.v4])))

private def pbaVRecvPost (mo : Mode) (m m_other : ℕ) (s0 : (Ty.denote pbaVpTy))
    (res : (Ty.prod (.opt (.opt (.prod pbaVpTy (.prod .nat (.prod .nat (.base .msg))))))
      pbaHsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m
  | some none => m + m_other + prngVpReady mo s0
  | some (some (st', _, _, _)) => m + m_other + max (prngVpReady mo s0) (prngVpReady mo st')

private theorem pba_vRecvC_potOKS (fm : Bool) (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)} (hE : Expr OO Γ' pbaHsTy) (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool) (sE : Expr OO Γ' pbaVpTy) (cE : Expr OO Γ' hdrCtTy)
    (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (pbaVRecvPost (Mode.mk true tL t) m m_other (sE.eval ρ))
      ((vRecvC (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t)
        hE ctxE pE sE cE recE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [pbaVRecvPost, Expr.eval])) (fun hGuard => ?_)
  have hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false := by
    simp only [orE_eval, Bool.or_eq_false_iff] at hGuard
    have h1 := hGuard.1
    rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at h1
    simpa [Expr.eval, Expr.v0] using h1
  rw [eval_bind]
  have hStep1 := pba_vRecvStep1C_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t
    (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ)
    m m_other (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hNotSends)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKSPrng.bindPot hStep1 (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun _ hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbaVRecvPost, pbaVRecvStep1Post, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun _ hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      exact potSPrng_ret (by simp [pbaVRecvPost, pbaVRecvStep1Post, hSome, hInNone, Expr.eval])
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_caseOpt
        (fun _ => potSPrng_ret (by simp [pbaVRecvPost, pbaVRecvStep1Post, hSome, hInSome, Expr.eval]))
        (fun _ _ => ?_)
      have hFR_eq :
          ∀ {Γ''},
            (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t).fsRecv (Γ' := Γ'') =
            prngBucketAuthFsRecvC (sampKR := sampKR) (sampKC := sampKC)
              (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B (Γ' := Γ'') := by
        intro Γ''; cases fm <;> rfl
      rw [hFR_eq]; dsimp only [prngBucketAuthFsRecvC]; rw [eval_bind, eval_ret, pure_bind]
      exact potSPrng_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
        (fun _ _ => potSPrng_caseOpt
          (fun _ => potSPrng_ret (by
            simp [pbaVRecvPost, pbaVRecvStep1Post, hSome, hInSome, Expr.eval]))
          (fun _ _ => potSPrng_ret (by
            simp [pbaVRecvPost, pbaVRecvStep1Post, hSome, hInSome, prngVpReady,
              vpSetVR, vpMk, vpId, vpTcurNat, letE_eval, Expr.eval, Expr.v0, Expr.v4])))

private def pbaCommitECPost (mo : Mode) (m : ℕ)
    (res : (Ty.prod (.opt (cGsTy pbaVpTy)) pbaEsTy : Ty S).denote) : ℕ :=
  match res.1 with
  | none => m + pbaPot mo res.2
  | some s_acc => m + pbaPot mo (s_acc, res.2.2.1, res.2.2.2)

private theorem pba_commitEC_potOKS (fm : Bool) (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' pbaEsTy)
    (sE : Expr OO Γ' (cGsTy pbaVpTy)) (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' pbaVpTy) (posE : Expr OO Γ' posTy)
    (ρ : Env Γ') (m : ℕ) (hNoAbort : (esE.eval ρ).2.2 = false) :
    PotOKSPrng P_prng (pbaCommitECPost (Mode.mk true tL t) m)
      ((commitEC (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t)
        L esE sE pE oldE newE posE).eval ρ)
      (m + prngOtherPot (Mode.mk true tL t) (sE.eval ρ).1 (pE.eval ρ) +
        prngVpReady (Mode.mk true tL t) (newE.eval ρ)) := by
  unfold commitEC; rw [eval_bind_ret]
  have hCom_eq :
      ∀ {Γ''},
        (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t).commit (Γ' := Γ'') =
        prngBucketAuthCommitC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (Γ' := Γ'') := by
    intro Γ''; cases fm <;> rfl
  rw [hCom_eq]; dsimp only [prngBucketAuthCommitC]; rw [eval_bind, eval_ret, pure_bind]
  refine potSPrng_caseOpt (fun hCNone => by simp [Expr.eval, Expr.v0] at hCNone) (fun _ hCSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hCSome
  subst hCSome; refine potSPrng_ret ?_
  simp only [pbaCommitECPost, pbaPot, esMk, esAbort, cGsSetStP_st_prng, cAcceptE_st_prng,
    Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hNoAbort,
    Bool.false_eq_true, ↓reduceIte]
  cases (pE.eval ρ : Bool) <;> (simp only [prngOtherPot, ↓reduceIte, Bool.false_eq_true]; omega)

private theorem pba_deliverEC_potOKS (fm : Bool) (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ)
    (t : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' pbaEsTy) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + pbaPot (Mode.mk true tL t) x.2)
      ((deliverEC (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t)
        L maxSkip cfg esE argE).eval ρ)
      (1 + m + pbaPot (Mode.mk true tL t) (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotAbWin; exact hNotAbWin.1
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun r1 _ => ?_)
  rw [eval_bind]
  set m_other := prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := pba_vRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t
    (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hRecv
  change PotOKSPrng P_prng
    (pbaVRecvPost (Mode.mk true tL t) m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady (Mode.mk true tL t)
        (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      pbaPot (Mode.mk true tL t) (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [pbaPot, hab]
  rw [show 1 + m + pbaPot (Mode.mk true tL t) (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady (Mode.mk true tL t)
          (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbaVRecvPost, hNone, pbaPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [pbaVRecvPost, hSome, hInNone, esMk, esAbort, esG,
        Expr.eval, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
      refine Nat.le_trans
        (Nat.add_le_add_left (Nat.le_of_eq
          (pbaPot_mk_eq (Mode.mk true tL t) (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
      simp only [pbaPot, Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 +
          prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
          m_other + prngVpReady (Mode.mk true tL t)
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [pbaPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      rw [eval_bind]
      have hCom := pba_commitEC_potOKS (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t
        (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2))
        (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
        (.fst .v0) (cRecPos .v3)
        (.cons tup (.cons resInner (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
        (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
      simp only [esG, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom
      have hPre :
          m + prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1 +
            prngVpReady (Mode.mk true tL t) tup.1 ≤
            pbaVRecvPost (Mode.mk true tL t) m m_other
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
        simp [pbaVRecvPost, hSome, hInSome, m_other]
      refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
      refine potSPrng_caseOpt (fun hCNone => ?_) (fun s_acc hCSome => ?_)
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
        exact potSPrng_ret (by simp [pbaCommitECPost, hCNone, Expr.eval, Expr.v0])
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
        refine potSPrng_ret ?_
        simp only [pbaCommitECPost, hCSome, esSetG, letE_eval, esMk, esAbort,
          Expr.eval, Expr.v0, Expr.v1, Expr.v5, Expr.v6, Env.get_cons_zero, Env.get_cons_succ]
        exact Nat.add_le_add_left (Nat.le_of_eq
          (pbaPot_mk_eq (Mode.mk true tL t) (g2 := s_acc) (h2 := comOut.2.2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m

private theorem pba_injectEC_potOKS (fm : Bool) (L B Δcka qep : ℕ) (tL : Option ℕ)
    (t : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty S)} (esE : Expr OO Γ' pbaEsTy) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + pbaPot (Mode.mk true tL t) x.2)
      ((injectEC (hooksPRNGBucketAuthModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t)
        L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + pbaPot (Mode.mk true tL t) (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotRef; exact hNotRef.1
  rw [eval_bind]
  set m_other := prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := pba_vRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t
    (esH (.fst (Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  change PotOKSPrng P_prng
    (pbaVRecvPost (Mode.mk true tL t) m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady (Mode.mk true tL t)
        (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      pbaPot (Mode.mk true tL t) (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [pbaPot, hab]
  rw [show 1 + m + pbaPot (Mode.mk true tL t) (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady (Mode.mk true tL t)
          (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbaVRecvPost, hNone, pbaPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [pbaVRecvPost, hSome, hInNone, pbaPot, esSetH, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hab,
        Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 +
          prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
          m_other + prngVpReady (Mode.mk true tL t)
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [pbaPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
      · refine potSPrng_ret ?_
        simp only [pbaVRecvPost, hSome, hInSome, pbaPot, esSetH, letE_eval, esMk, esAbort, esG,
          Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
          Bool.false_eq_true, ↓reduceIte]
        have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 +
            prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
            m_other + prngVpReady (Mode.mk true tL t)
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
          simpa [pbaPot, hab] using hSum.symm
        omega
      · refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCom := pba_commitEC_potOKS (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) fm L B Δcka qep tL t
            (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2))
            (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
            (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v3, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1 +
                prngVpReady (Mode.mk true tL t) tup.1 ≤
                pbaVRecvPost (Mode.mk true tL t) m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
            simp [pbaVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
          refine potSPrng_caseOpt (fun hCNone => ?_) (fun _ hCSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
            exact potSPrng_ret (by simp [pbaCommitECPost, hCNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
            exact potSPrng_ret (by
              simp [pbaCommitECPost, hCSome, pbaPot, esSetG, letE_eval, esMk, esH, esAbort,
                Expr.eval, Expr.v0, Expr.v1])
        · refine potSPrng_ret ?_
          simp only [pbaVRecvPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort, esG,
            Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (pbaPot_mk_eq (Mode.mk true tL t) (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
          simp only [pbaPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 +
              prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
              m_other + prngVpReady (Mode.mk true tL t)
                (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
            simpa [pbaPot, hab] using hSum.symm
          omega

private theorem initPRNGBucketAuthEStateC_potOKS (L : ℕ) (tL : Option ℕ) (t : ℕ)
    {Γ' : List (Ty S)} (bE : Expr OO Γ' .bool) (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun es => m + pbaPot (Mode.mk true tL t) es)
      ((initPRNGBucketAuthEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t bE).eval ρ) (m + 3) := by
  unfold initPRNGBucketAuthEStateC; rw [eval_bind_ret, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + 3) (m + 3) (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
    (fun _ => ?_)
  rw [eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + 1) (m + 3) (fun _ => Nat.le_refl _)
      (by simp [rootPRNGBucketAuthHybridC_queries]; omega)) (fun _ => ?_)
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbaPot, esMk, Expr.eval])) (fun _ _ => ?_)
  refine potSPrng_ret ?_
  simp only [pbaPot, esMk, cGsInitE, cGsMk, mkPartiesE, vpMk, Expr.eval,
    Bool.false_eq_true, ↓reduceIte]
  have hB : prngReady (Mode.mk true tL t) Party.B 0 = 0 := by simp [prngReady, Party.sendsIn]
  simp only [prngVpReady, partyDec_partyEnc, hB, Nat.add_zero]
  exact Nat.add_le_add_left (prngReady_le_one (Mode.mk true tL t) _ _) m

private theorem pba_handle_potOKS (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ)
    (m : ℕ)
    (qv : (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).Q.denote)
    (sv : (Ty.denote pbaStage2RedEsTy)) :
    PotOKSPrng P_prng (fun x => m + pbaPot (Mode.mk true tL t) x.2.1.1)
      ((redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip tL t).handle.eval (.cons sv (.cons qv .nil)))
      (1 + m + pbaPot (Mode.mk true tL t) sv.1.1) := by
  dsimp only [redPRNGAuthBucketHybridProg]; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
  · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · refine potSPrng_caseSum (fun x _ => ?_) (fun _ _ => ?_)
          · rw [eval_bind_ret]
            refine potSPrng_ite
              (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v5]))
              (fun hNotAbWin => ?_)
            have hab : sv.1.1.2.2 = false := by
              simp [orE_eval, esAbort, Expr.eval, Expr.v0, Expr.v1, Expr.v5] at hNotAbWin
              exact hNotAbWin.1
            refine potSPrng_caseOpt
              (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v5]))
              (fun s1 hs1 => ?_)
            rw [eval_bind]
            have hs1_st : s1.1 = sv.1.1.1.1 := by
              have hs1' := cEpMgmtE_some_st_prng _ _ _ _ _ _ hs1
              simpa [esG, Expr.eval, Expr.v0, Expr.v1, Expr.v5,
                Env.get_cons_zero, Env.get_cons_succ] using hs1'
            set p0 := x.1
            set m_other := prngOtherPot (Mode.mk true tL t) s1.1 p0
            have hSum : m_other + prngVpReady (Mode.mk true tL t) (if p0 then s1.1.2 else s1.1.1) =
                pbaPot (Mode.mk true tL t) sv.1.1 := by
              rw [prngOtherPot_add_pGet, hs1_st]; simp [pbaPot, hab]
            refine ⟨fun {_} k hk' =>
              (PotOKSPrng.bindPot
                (pba_vSendC_potOKS (sampKR := sampKR) (sampKC := sampKC)
                  (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                  true L B Δcka qep tL t _ _ _ _ _ _ _ _ m m_other)
                (fun _ => ?_)).run k hk' |>.mono ?_⟩
            · refine potSPrng_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
              · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
                exact potSPrng_ret (by simp [pbaVSendPost, hNone, pbaPot, esMk, Expr.eval])
              · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
                refine potSPrng_ret ?_
                simp only [pbaVSendPost, hSome, pbaPot, esMk, esAbort, cRecordE_st_prng,
                  Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
                  Env.get_cons_zero, Env.get_cons_succ, hab, Bool.false_eq_true, ↓reduceIte]
                have hEq := prngPot_pSet_eq (Mode.mk true tL t) s1.1 p0 stCt.1; dsimp only at hEq
                change m + (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
                            prngVpReady (Mode.mk true tL t) st'.1 +
                              prngVpReady (Mode.mk true tL t) st'.2) ≤
                  m + m_other + prngVpReady (Mode.mk true tL t) stCt.1
                rw [hEq]; omega
            · simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1,
                Env.get_cons_zero, Env.get_cons_succ]
              change 1 + m + m_other + prngVpReady (Mode.mk true tL t) (if p0 then s1.1.2 else s1.1.1) ≤
                1 + m + pbaPot (Mode.mk true tL t) sv.1.1
              omega
          · exact potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v4])
        · rw [eval_bind]
          exact PotOKSPrng.bindPot
            (pba_deliverEC_potOKS true L B Δcka qep maxSkip tL t _ (.fst (Expr.v3 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1]))
      · rw [eval_bind]
        exact PotOKSPrng.bindPot
          (pba_injectEC_potOKS true L B Δcka qep tL t _ (.fst (Expr.v2 (O := OO))) .v0 _ m)
          (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1]))
    · refine potSPrng_ite
        (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1]))
        (fun _ => ?_)
      rw [eval_bind]
      refine PotOKSPrng.bindPot
        (potSPrng_comp_const _ _ (m + pbaPot (Mode.mk true tL t) sv.1.1)
          (1 + m + pbaPot (Mode.mk true tL t) sv.1.1)
          (fun _ => Nat.le_refl _) (by simp [prngBucketAuthForgedHdrRevealC_queries]))
        (fun _ => ?_)
      exact potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbaPot, esMk, Expr.eval]))
        (fun _ _ => potSPrng_ret (by
          simp [pbaPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v0, Expr.v1, Expr.v3]))
  · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · refine potSPrng_caseSum (fun x _ => ?_) (fun _ _ => ?_)
          · rw [eval_bind_ret]
            refine potSPrng_ite
              (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v5]))
              (fun hNotAbWin => ?_)
            have hab : sv.1.1.2.2 = false := by
              simp [orE_eval, esAbort, Expr.eval, Expr.v0, Expr.v1, Expr.v5] at hNotAbWin
              exact hNotAbWin.1
            refine potSPrng_caseOpt
              (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v5]))
              (fun s1 hs1 => ?_)
            rw [eval_bind]
            have hs1_st : s1.1 = sv.1.1.1.1 := by
              have hs1' := cEpMgmtE_some_st_prng _ _ _ _ _ _ hs1
              simpa [esG, Expr.eval, Expr.v0, Expr.v1, Expr.v5,
                Env.get_cons_zero, Env.get_cons_succ] using hs1'
            set p0 := x.1
            set m_other := prngOtherPot (Mode.mk true tL t) s1.1 p0
            have hSum : m_other + prngVpReady (Mode.mk true tL t) (if p0 then s1.1.2 else s1.1.1) =
                pbaPot (Mode.mk true tL t) sv.1.1 := by
              rw [prngOtherPot_add_pGet, hs1_st]; simp [pbaPot, hab]
            refine ⟨fun {_} k hk' =>
              (PotOKSPrng.bindPot
                (pba_vSendC_potOKS (sampKR := sampKR) (sampKC := sampKC)
                  (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                  false L B Δcka qep tL t _ _ _ _ _ _ _ _ m m_other)
                (fun _ => ?_)).run k hk' |>.mono ?_⟩
            · refine potSPrng_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
              · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
                exact potSPrng_ret (by simp [pbaVSendPost, hNone, pbaPot, esMk, Expr.eval])
              · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
                refine potSPrng_ret ?_
                simp only [pbaVSendPost, hSome, pbaPot, esMk, esAbort, cRecordE_st_prng,
                  Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
                  Env.get_cons_zero, Env.get_cons_succ, hab, Bool.false_eq_true, ↓reduceIte]
                have hEq := prngPot_pSet_eq (Mode.mk true tL t) s1.1 p0 stCt.1; dsimp only at hEq
                change m + (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
                            prngVpReady (Mode.mk true tL t) st'.1 +
                              prngVpReady (Mode.mk true tL t) st'.2) ≤
                  m + m_other + prngVpReady (Mode.mk true tL t) stCt.1
                rw [hEq]; omega
            · simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1,
                Env.get_cons_zero, Env.get_cons_succ]
              change 1 + m + m_other + prngVpReady (Mode.mk true tL t) (if p0 then s1.1.2 else s1.1.1) ≤
                1 + m + pbaPot (Mode.mk true tL t) sv.1.1
              omega
          · exact potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v4])
        · rw [eval_bind]
          exact PotOKSPrng.bindPot
            (pba_deliverEC_potOKS false L B Δcka qep maxSkip tL t _ (.fst (Expr.v3 (O := OO))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1]))
      · rw [eval_bind]
        exact PotOKSPrng.bindPot
          (pba_injectEC_potOKS false L B Δcka qep tL t _ (.fst (Expr.v2 (O := OO))) .v0 _ m)
          (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1]))
    · refine potSPrng_ite
        (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1]))
        (fun _ => ?_)
      rw [eval_bind]
      refine PotOKSPrng.bindPot
        (potSPrng_comp_const _ _ (m + pbaPot (Mode.mk true tL t) sv.1.1)
          (1 + m + pbaPot (Mode.mk true tL t) sv.1.1)
          (fun _ => Nat.le_refl _) (by simp [prngBucketAuthRevealC_queries]; omega)) (fun _ => ?_)
      exact potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbaPot, esMk, Expr.eval]))
        (fun _ _ => potSPrng_ret (by
          simp [pbaPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v0, Expr.v1, Expr.v3]))

end PbaPotOK

/-- **Potential-based `min (2 + 2 * q) (q + 3)` PRF-PRNG query bound (`PotOK`)** for
`redPRNGAuthBucketHybridProg`. -/
theorem redPRNGAuthBucketHybridProg_makesAtMostQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ)
    (A : _root_.CryptoGames.SM.Adversary (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
    (hq : MakesAtMostQueries A q) :
    (((redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL t).eval (fun _ => A) ()) :
      PRFPRNG.Adversary RSt I K).IsQueryBoundP (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine _root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.costedReduction_makesAtMostQueries_prng
    _ (fun st : (Ty.denote pbaStage2RedEsTy) =>
        pbaPot (_root_.CryptoGames.SM.Construction.Mode.mk true tL t) st.1.1) q A
    (hq.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGAuthBucketHybridProg_totalQueries L B Δcka qep maxSkip tL t q)
    ?_
    (fun m qv sv => pba_handle_potOKS L B Δcka qep maxSkip tL t m qv sv)
    (by simp [redPRNGAuthBucketHybridProg, Comp.queries])
  dsimp only [redPRNGAuthBucketHybridProg]
  rw [_root_.CryptoGames.SM.Engine.eval_bind]
  refine _root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.PotOKSPrng.bindPot
    (_root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.potSPrng_comp_const _ _ (q + 3) (q + 3)
      (fun _ => Nat.le_refl _) (by simp [Comp.queries])) (fun _ => ?_)
  rw [_root_.CryptoGames.SM.Engine.eval_bind]
  exact _root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.PotOKSPrng.bindPot
    (initPRNGBucketAuthEStateC_potOKS L tL t (.bool false) _ q)
    (fun _ => _root_.Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.potSPrng_ret
      (by simp [Expr.eval, Expr.v0]))

/-- Evaluation bridge (`HooksVRInv` / `fromAEADPRG`) for `redPRNGAuthBucketHybridProg`: under
`MakesAtMostQueries A qAdv` and `qAdv ≤ B_q`, the costed program's `PRFPRNG.branch b_prng`
computation equals shallow `redPRNGAuthBucketHybrid`. -/
theorem redPRNGAuthBucketHybridProg_branch_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
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
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (b_prng : Bool) :
    PRFPRNG.branch prng b_prng
      ((redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.branch prng b_prng (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A) := by
  exact Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthEval.redPRNGAuthBucketHybridProg_branch_eval_vr_impl
    cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE hDefaultE hSampKC hSampCCoins hSampI hSampK
    hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB b_prng

@[local simp] private theorem lookupMultiBucketFC_queries (L : ℕ) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) :
    (lookupMultiBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L hE tE ikE).queries w (fun _ => 0) = 0 := by
  simp [lookupMultiBucketFC, Comp.queries]

@[local simp] private theorem rootFSMultiBucketAuthC_queries (L Δcka qep : ℕ) (tL : Option ℕ)
    (par : Bool) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) :
    (rootFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep tL par hE tE plE ikE σE).queries w
      (fun _ => 0) = 0 := by
  simp [rootFSMultiBucketAuthC, Comp.queries]

@[local simp] private theorem fsMultiBucketAuthStartSendC_queries (L Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (fsMultiBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par hE ctxE pE tE γE σE rE).queries w
      (fun _ => 0) = 0 := by
  cases gMain <;> simp [fsMultiBucketAuthStartSendC, Comp.queries]

@[local simp] private theorem fsMultiBucketAuthStartRecvC_queries (L Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig)) (tnE : Expr OO Γ' (.base .t)) :
    (fsMultiBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par hE ctxE pE tE γE σE tnE).queries w
      (fun _ => 0) = 0 := by
  cases gMain <;> simp [fsMultiBucketAuthStartRecvC, Comp.queries]

@[local simp] private theorem initFSMultiBucketAuthEStateC_queries (L Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ) {Γ'} (bE : Expr OO Γ' .bool) :
    (initFSMultiBucketAuthEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par bE).queries w (fun _ => 0) = 0 := by
  cases gMain <;> simp [initFSMultiBucketAuthEStateC, Comp.queries]

/-- Syntactic total multi-session `FSAEAD` query bound `≤ 2 * q` for `redFSAuthMultiBucketProg`. -/
theorem redFSAuthMultiBucketProg_totalQueries (L B Δcka qep maxSkip : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (par : Bool) (q : ℕ) :
    (redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip gMain la tL par).totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  simp only [CostedReduction.totalQueries, redFSAuthMultiBucketProg,
    initFSMultiBucketAuthEStateC_queries, Comp.queries, zero_add, max_self, add_zero]
  rw [Nat.mul_comm 2 q]
  apply Nat.mul_le_mul_left q
  cases gMain <;> simp [deliverEC, injectEC, vSendC,
    _root_.CryptoGames.SM.Engine.vSendStep1C, _root_.CryptoGames.SM.Engine.vRecvC,
    _root_.CryptoGames.SM.Engine.vRecvStep1C, _root_.CryptoGames.SM.Engine.commitEC,
    hooksFSMultiBucketAuthC, fsMultiBucketAuthFsSendC, fsMultiBucketAuthFsRecvC,
    fsMultiBucketAuthCommitC, fsMultiBucketAuthRevealC, rangeListBucketC, Comp.queries]

end CostedBucketAuth

end -- public section

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth

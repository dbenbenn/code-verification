/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.SendShortC -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import

import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
import Computational.Proofs.E2E.SessionAuthBridge
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.ReductionDsl.FsAtomicMacros
import Computational.Proofs.SessionCostedFig8.BundlesMultiFs
import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
import Computational.Proofs.SessionCostedFs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketMode

public section

open scoped ENNReal
open OracleComp OracleSpec
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.FSAEAD (EncMsgsOk MakesAtMostQueries RatchetReceiverState
  RatchetSenderState challengeQuery corruptSenderQuery deliverQuery encBadMsg injectQuery
  transmitQuery)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32
  LibsignalMsgPublicPart dummyKey lAead lChainPRG lFS lPubOf)
open _root_.CryptoGames.SM (Config GameState specDF)
open _root_.CryptoGames.SM.Construction (PartyState FSMultiBook FSMultiDFBucketState FSMultiSpec FSMultiState
  Header Mode bucketAuthCfgGen fsClamp healEpoch
  hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode initFSMultiDFBucketPaper
  isHonestHdrFSMultiDFBucket liftFSMulti liftFSMultiDFBucket lookupMultiDFBucketF lookupMultiF
  mkParties redFSAuthDFPaperMultiBucketMode redFSAuthDFPaperMultiBucketModeGen
  redFSAuthDFPaperMultiBucketModeGen_fsClamp_fromAEADPRG redFSAuthDFPaperMultiBucketModeProg
  redFSAuthDFPaperMultiBucketModeProgGen_eval_clamp regSessMultiDFBucket regSessOptMultiDFBucket
  rootFSMultiDFBucketPaper)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF MakesAtMostQueriesDF challEBucket
  corrEPaperBucket deliverForgeE engRunDFPaperBucketMode implEDFPaperBucketMode
  implEDFPaperBucketRaw localAuthDFPaperBucketMode transmitEBucket withWinEpDF withWinEpDFMode)
open _root_.CryptoGames.SM.Engine (Policy VP Ctx EState Hooks HooksVRInv RSReach SMEngineInv SMVRInv TComp
  abortE challE coinsE commitE deliverE deliverE_inv deliverForgeE_inv deliverForgeE_vrInv
  epMgmt_st_eq implE_vrInv injectE injectE_inv run_liftH_bind transmitE vRecv vRecvStep1
  vRecv_eq_bind vSend vSendStep1 vSend_eq_bind vSend_vR_eq)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF badSendMsgDF)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (AllPartiesInv DdhRoleOk
  HooksLocalCKAAgree LocalPartyInv commitE_localCKA_eq ddhRoleOk_initA ddhRoleOk_initB
  dhSchemeFb_receive_of_roleOk dhSchemeFb_send_of_roleOk implE_localCKA_eq record_st_eq
  vRecv_localCKA_eq vSend_localCKA_eq)
open Computational.Proofs.ReductionDsl.Fig8Atomic (RSReachB atomicShortPubB
  atomicShortPubB_imp_shortB dhSchemeFb fsAtomic fsAtomicB fsAtomicB_receive_eq fsAtomicB_send_eq)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)

private theorem withWinEpDFMode_inl_run
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γ T Sig SS RS M CCoins E HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (isHonest : HS → Header T → Bool) (n : unifSpec.Domain)
    (es0 : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (winEp0 : Option ℕ) :
    ((implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain isHonest (.inl n)).run (es0, winEp0)) =
      (fun u => (u, (es0, winEp0))) <$> query (spec := unifSpec + tspec) (.inl n) := by
  cases gMain <;>
    simp [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, implEDFPaperBucketRaw,
      coinsE, StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc]

private theorem withWinEpDFMode_congr_of_raw_eq
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {St Msg Coins T' E' VPt HS : Type}
    (gMain : Bool) (isHonest : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl₁ impl₂ : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS) (TComp tspec)))
    (qy : (unifSpec + specDF St Msg Coins (Header T' × E')).Domain)
    (es0 : EState VPt Msg (Header T' × E') HS) (winEp0 : Option ℕ)
    (hEq : (impl₁ qy).run es0 = (impl₂ qy).run es0) :
    (withWinEpDFMode gMain isHonest epOf impl₁ qy).run (es0, winEp0) =
      (withWinEpDFMode gMain isHonest epOf impl₂ qy).run (es0, winEp0) := by
  cases gMain <;>
    simp only [withWinEpDFMode, withWinEpDF, ↓reduceIte, Bool.false_eq_true, StateT.run_mk, hEq]

private theorem mem_support_withWinEpDFMode_inr
    {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {St Msg Coins T' E' VPt HS : Type}
    (gMain : Bool) (isHonest : HS → Header T' → Bool) (epOf : VPt → ℕ)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins (Header T' × E'))
      (StateT (EState VPt Msg (Header T' × E') HS) (TComp tspec)))
    (t : (specDF St Msg Coins (Header T' × E')).Domain)
    (es0 es' : EState VPt Msg (Header T' × E') HS) (winEp0 winEp' : Option ℕ)
    (out : (unifSpec + specDF St Msg Coins (Header T' × E')).Range (.inr t))
    (hmem : (out, (es', winEp')) ∈
      support ((withWinEpDFMode gMain isHonest epOf impl (.inr t)).run (es0, winEp0))) :
    (out, es') ∈ support ((impl (.inr t)).run es0) ∧
    (es'.g.win = false → winEp' = winEp0) := by
  cases gMain
  · simp only [withWinEpDFMode, Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨r, es₁⟩, hr, rfl, rfl, hwin⟩ := hmem
    refine ⟨hr, fun hw => ?_⟩
    simp [hw] at hwin; exact hwin
  · simp only [withWinEpDFMode, ↓reduceIte, withWinEpDF, StateT.run_mk,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨r, es₁⟩, hr, rfl, rfl, hwin⟩ := hmem
    refine ⟨hr, fun hw => ?_⟩
    simp [hw] at hwin; exact hwin

private theorem hooksFSMultiDFBucketPaperMode_localCKAAgree
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [DecidableEq E]
    [SampleableType Pt] [SampleableType K]
    (L : ℕ) (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ)
      (hooksFSMultiDFBucketPaperMode L (dhSchemeFb Dh) prng fs Δcka Δbucket qep gMain tL par la)
      (hooksFSMultiDFBucketPaperMode L (dhScheme Dh) prng fs Δcka Δbucket qep gMain tL par la) where
  startSend_eq ctx P t γ σ r h ht hSend hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hSend' : P.sendsIn ((t - 1) + 1) = true := ht1.symm ▸ hSend
    dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]
    let pl := _root_.CryptoGames.SM.Construction.postLeakDFBucket tL ctx
    have hCoins : ∀ coins : BitVec 256,
        let body := fun c : _root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt × Pt × Pt => (do
          let (σ', kVal, sid) ← rootFSMultiDFBucketPaper (SS := SS) (RS := RS) (T := Pt) (M := M) (E := E)
            prng Δbucket qep tL par t pl c.2.2 σ
          let s1 ← get
          let (optIdx, s2) := regSessOptMultiDFBucket L tL t sid s1
          set { s2 with cache := Function.update s2.cache t (some (c.2.1, σ', kVal, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with | none => .inl (fs.initSender kVal) | some sIdx => .inr sIdx
          pure (some (c.1, c.2.1, σ', ssv)))
        (body ((dhSchemeFb Dh).send γ coins)).run h = (body ((dhScheme Dh).send γ coins)).run h ∧
        ∀ q ∈ support ((body ((dhScheme Dh).send γ coins)).run h),
          ∀ γ' T' σ' ss, q.1 = some (γ', T', σ', ss) → DdhRoleOk P t γ' := by
      intro coins; dsimp only
      have hsnd := dhSchemeFb_send_of_roleOk Dh hRole hSend' coins
      have hRole' : DdhRoleOk P t ((dhScheme Dh).send γ coins).1 := ht1 ▸ hsnd.2
      simp only [hsnd.1]
      refine ⟨trivial, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [StateT.run_bind, mem_support_bind_iff] at hq
      obtain ⟨⟨⟨σ₁, k₁, sid⟩, h₂⟩, _, hq⟩ := hq
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hq
      subst hq; cases hEq; exact hRole'
    rcases r with _ | c
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine ⟨bind_congr fun coins => (hCoins coins).1, fun q hq γ' T' σ' ss hEq => ?_⟩
      rw [mem_support_bind_iff] at hq
      obtain ⟨coins, _, hq⟩ := hq
      exact (hCoins coins).2 q hq γ' T' σ' ss hEq
    · simp only [pure_bind]; exact hCoins c
  startRecv_eq ctx P t γ σ Tn h ht hRecv hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hRole hRecv' Tn
    have hRole' : DdhRoleOk P t ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    cases gMain
    · simp only [hooksFSMultiDFBucketPaperMode, Bool.false_eq_true, ↓reduceIte,
        hooksFSMultiDFBucketPaper, hrcv.1]
      refine ⟨trivial, fun q hq γ' σ' rs hEq => ?_⟩
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hq
      cases hcache : h.cache t with
      | none =>
        simp only [hcache] at hq
        split_ifs at hq
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
          exact hRole'
        · rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨_, _, hq⟩ := hq
          simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq; exact hRole'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
      | some val =>
        rcases val with ⟨Tc, σc, kVal, optIdx⟩; simp only [hcache] at hq
        by_cases hT : Tc = Tn
        · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq; exact hRole'
        · simp only [hT, ↓reduceIte] at hq
          split_ifs at hq
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
            exact hRole'
          · rw [StateT.run_bind, mem_support_bind_iff] at hq; obtain ⟨_, _, hq⟩ := hq
            simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hq
            subst hq; cases hEq; exact hRole'
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq
    · simp only [hooksFSMultiDFBucketPaperMode, ↓reduceIte, hrcv.1]
      refine ⟨trivial, fun q hq γ' σ' rs hEq => ?_⟩
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hq
      cases hcache : h.cache t with
      | none =>
        simp only [hcache] at hq
        split_ifs at hq <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq)
      | some val =>
        rcases val with ⟨Tc, σc, kVal, optIdx⟩; simp only [hcache] at hq
        by_cases hT : Tc = Tn
        · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq; exact hRole'
        · simp only [hT, ↓reduceIte] at hq
          split_ifs at hq <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq; subst hq; cases hEq)
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := by cases gMain <;> rfl

private def FSVROkMultiReachB (maxSkip k : ℕ)
    (rsv : RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) : Prop :=
  match rsv with
  | .inl rs => RSReachB maxSkip k rs
  | .inr _ => True

private theorem rsReachB_skippedKeys_le {CK MK : Type} {maxSkip k B0 : ℕ}
    {rs : RatchetReceiverState CK MK}
    (h : RSReachB maxSkip k rs) (hkB : (k + 1) * (maxSkip + 1) ≤ B0) :
    rs.skippedKeys.length ≤ B0 := by
  have h1 : rs.skippedKeys.length ≤ rs.lastIndex := h.2
  have h2 : rs.lastIndex ≤ k * (maxSkip + 1) := h.1.1
  have h3 : k * (maxSkip + 1) ≤ (k + 1) * (maxSkip + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_succ k)
  omega

private theorem hooksFSMultiDFBucketPaperMode_vrInv_fsClamp_lFS
    {Pt KC Γ CCoins I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ B0 : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka Δbucket qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    HooksVRInv (FSVROkMultiReachB maxForwardJumps)
      (hooksFSMultiDFBucketPaperMode L cka prng
        (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        Δcka Δbucket qep gMain tL par la) where
  mono {_ _ rsv} hle hv := by cases rsv with | inl rs => exact hv.mono hle | inr _ => trivial
  startRecv_step _ _ t γ σ Tn h res hmem _ _ rsv := by
    cases gMain
    · simp only [hooksFSMultiDFBucketPaperMode, Bool.false_eq_true, ↓reduceIte,
        hooksFSMultiDFBucketPaper] at hmem
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      cases hcache : h.cache t with
      | none =>
        simp only [hcache] at hmem; split_ifs at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
          exact RSReachB.init
            ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
            (lChainPRG C.F) maxForwardJumps _
        · rw [StateT.run_bind, mem_support_bind_iff] at hmem; obtain ⟨_, _, hmem⟩ := hmem
          simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; intro hEq; cases hEq; trivial
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
      | some val =>
        rcases val with ⟨Tc, σc, k, optIdx⟩; simp only [hcache] at hmem
        by_cases hT : Tc = Tn
        · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; intro hEq; cases hEq
          rcases optIdx with _ | _
          · exact RSReachB.init
              ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
              (lChainPRG C.F) maxForwardJumps k
          · trivial
        · simp only [hT, ↓reduceIte] at hmem; split_ifs at hmem
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
            exact RSReachB.init
              ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
              (lChainPRG C.F) maxForwardJumps _
          · rw [StateT.run_bind, mem_support_bind_iff] at hmem; obtain ⟨_, _, hmem⟩ := hmem
            simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; intro hEq; cases hEq; trivial
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq
    · simp only [hooksFSMultiDFBucketPaperMode, ↓reduceIte] at hmem
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      cases hcache : h.cache t with
      | none =>
        simp only [hcache] at hmem
        split_ifs at hmem <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq)
      | some val =>
        rcases val with ⟨Tc, σc, k, optIdx⟩; simp only [hcache] at hmem
        by_cases hT : Tc = Tn
        · simp only [hT, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; intro hEq; cases hEq
          rcases optIdx with _ | _
          · exact RSReachB.init
              ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
              (lChainPRG C.F) maxForwardJumps k
          · trivial
        · simp only [hT, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro hEq; cases hEq)
  fsRecv_step ctx _ t0 rsv hdr e rec_ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩; dsimp only at hEq; subst hEq
    rcases rsv with rs | sIdx
    · dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper, fsClamp] at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some.injEq] at hmem
      obtain ⟨o, ho, hEqO⟩ := Option.map_eq_some_iff.mp hmem.1.symm
      obtain ⟨o₀, ho₀, rfl⟩ := Option.map_eq_some_iff.mp ho
      rcases o₀ with ⟨rs', i₀, m₀⟩
      cases hEqO
      exact (RSReachB.receive_fromAEADPRG
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps _ hVR (by simpa [lFS] using ho₀)).2
    · dsimp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper] at hmem
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      generalize List.find? _ ((h.book sIdx).getD {}).fsTrans = matched at hmem
      by_cases hCond : ((matched.isNone && !(_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t0)) &&
          !((h.book sIdx).getD {}).sCorr) = true
      · simp only [hCond, ↓reduceIte] at hmem
        rw [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨csAns, h₀⟩, _, hmem⟩ := hmem
        rcases csAns with _ | _
        · simp at hmem
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            (rw [StateT.run_bind, mem_support_bind_iff] at hmem;
             obtain ⟨⟨qres, h₁⟩, _, hmem⟩ := hmem;
             rcases qres with _ | (_ | ⟨i, mo'⟩) <;> [simp at hmem; simp at hmem; skip];
             simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem;
             split_ifs at hmem <;> [simp [StateT.run_modify] at hmem; skip];
             simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
             rcases mo' with _ | m <;> rcases rec_ with _ | r <;>
               simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                 Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at hmem <;>
               first | exact False.elim hmem | (rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial))
      · simp only [hCond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
        split_ifs at hmem <;>
          (rw [StateT.run_bind, mem_support_bind_iff] at hmem;
           obtain ⟨⟨qres, h₁⟩, _, hmem⟩ := hmem;
           rcases qres with _ | (_ | ⟨i, mo'⟩) <;> [simp at hmem; simp at hmem; skip];
           simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem;
           split_ifs at hmem <;> [simp [StateT.run_modify] at hmem; skip];
           simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
           rcases mo' with _ | m <;> rcases rec_ with _ | r <;>
             simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
               Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at hmem <;>
             first | exact False.elim hmem | (rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial))
  commit_vR _ _ _ _ _ _ hmem _ hEq := by
    simp only [hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases hEq; rfl

private theorem implEDFPaperBucketRaw_localCKA_step
    {Pt ι HS RSt SS RS M E σV ssV rsV : Type} {TSpec : OracleSpec.{0, 0} ι}
    [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E
      (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δ qep maxSkip : ℕ) (cfg : Config M)
    (es : EState (VP (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (t : (_root_.CryptoGames.SM.specDF (PartyState (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)).Domain)
    (hEs : AllPartiesInv es) :
    (implEDFPaperBucketRaw hk₁ Δ qep maxSkip cfg (.inr t)).run es =
      (implEDFPaperBucketRaw hk₂ Δ qep maxSkip cfg (.inr t)).run es ∧
    ∀ res ∈ support ((implEDFPaperBucketRaw hk₂ Δ qep maxSkip cfg (.inr t)).run es),
      AllPartiesInv res.2 := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (transmitEBucket hk₁ Δ qep (P, m, r)).run es =
        (transmitEBucket hk₂ Δ qep (P, m, r)).run es ∧
      ∀ res ∈ support ((transmitEBucket hk₂ Δ qep (P, m, r)).run es), AllPartiesInv res.2
    unfold transmitEBucket abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · have hs₁P : LocalPartyInv P (s₁.st P) := by rw [epMgmt_st_eq hep]; exact hEs P
        have hvs := vSend_localCKA_eq hAg s₁ P (s₁.st P) m none r es.h hs₁P
        simp only [run_liftH_bind, hvs.1]
        refine ⟨trivial, fun res hmem => ?_⟩
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvsMem, hmem⟩ := hmem
        rcases vsRes with _ | ⟨st', ct⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hEs
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; intro Q
          by_cases hQP : Q = P
          · subst hQP; simp [record_st_eq, hvs.2 _ hvsMem st' ct rfl]
          · simp [record_st_eq, Function.update_of_ne hQP, epMgmt_st_eq hep, hEs Q]
  · change (challEBucket (P, m₀, m₁, r)).run es = (challEBucket (P, m₀, m₁, r)).run es ∧
      ∀ res ∈ support ((challEBucket (P, m₀, m₁, r)).run es), AllPartiesInv res.2
    simp only [challEBucket, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
  · exact implE_localCKA_eq hAg Δ qep maxSkip cfg (⟨false, none, 0⟩ : Mode).policy
      es (.inl (.inl (.inr (P, c)))) hEs
  · exact implE_localCKA_eq hAg Δ qep maxSkip cfg (⟨false, none, 0⟩ : Mode).policy
      es (.inl (.inr (P, c))) hEs
  · change (corrEPaperBucket hk₁ P).run es = (corrEPaperBucket hk₂ P).run es ∧
      ∀ res ∈ support ((corrEPaperBucket hk₂ P).run es), AllPartiesInv res.2
    refine ⟨by unfold corrEPaperBucket; rw [hAg.reveal_eq], fun res hmem => ?_⟩
    unfold corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
    · rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, _⟩, _, hmem⟩ := hmem
      rcases revRes with _ | _ <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro Q;
          simpa [AllPartiesInv, GameState.afterCorr, GameState.leak] using hEs Q)
  · change (deliverForgeE hk₁ Δ qep cfg (P, c, c')).run es =
        (deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es ∧
      ∀ res ∈ support ((deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es), AllPartiesInv res.2
    unfold deliverForgeE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [hchk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
        · have hvr := vRecv_localCKA_eq hAg es.g P (es.g.st P) c' none es.h (hEs P)
          simp only [hchk, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvr.1]
          refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_,
            fun res hmem => ?_⟩
          · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
            · rfl
            · rfl
            · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
              · simp [hqep]
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
                by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
                · simp only [htriv, ↓reduceIte, StateT.run_bind]
                  rw [(commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                    { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
                · simp [htriv]
          · rw [mem_support_bind_iff] at hmem; obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
            rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hEs
            · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
              · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact hEs
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
                · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
                  obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
                  have hcm := (commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                    { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
                  rcases cmRes with _ | s₁
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; intro Q; dsimp [AllPartiesInv] at *; rw [hcm.1]; exact hEs Q
                  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                      support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; exact hcm.2 s₁ rfl
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                  split_ifs at hmem <;>
                    (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                       support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs)

private theorem redFSAuthDFPaperMultiBucketModeGen_dhSchemeFb_eq
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType Pt] [SampleableType KR] [SampleableType K]
    (L : ℕ) (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (lam : Pt) (Δcka Δbucket qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (PartyState (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)) :
    redFSAuthDFPaperMultiBucketModeGen L (dhSchemeFb Dh) prng fs lam Δcka Δbucket qep gMain la tL par A =
      redFSAuthDFPaperMultiBucketModeGen L (dhScheme Dh) prng fs lam Δcka Δbucket qep gMain la tL par A := by
  unfold redFSAuthDFPaperMultiBucketModeGen engRunDFPaperBucketMode
  have hInitEq : initFSMultiDFBucketPaper L (dhSchemeFb Dh) prng fs lam Δbucket qep tL par =
      initFSMultiDFBucketPaper L (dhScheme Dh) prng fs lam Δbucket qep tL par := rfl
  simp only [bind_assoc, hInitEq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h₀⟩ hmem₀ => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  simp only [bind_assoc, pure_bind]
  have hEs₀ : AllPartiesInv (M := M) (E := E)
      ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₀ }) := by
    unfold initFSMultiDFBucketPaper at hmem₀
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
      pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem₀
    obtain ⟨⟨kr, _⟩, _, ⟨kc, _⟩, _, ⟨⟨σ, kVal, sid⟩, h₁⟩, _, hEq⟩ := hmem₀
    cases hEq
    intro P; cases P
    · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
    · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
  have hAg := hooksFSMultiDFBucketPaperMode_localCKAAgree L Dh prng fs Δcka Δbucket qep gMain tL par la
  generalize hhk₁ : hooksFSMultiDFBucketPaperMode L (dhSchemeFb Dh) prng fs Δcka Δbucket qep gMain tL par la = hk₁
  generalize hhk₂ : hooksFSMultiDFBucketPaperMode L (dhScheme Dh) prng fs Δcka Δbucket qep gMain tL par la = hk₂
  generalize hcfg : bucketAuthCfgGen (Msg := M) Δbucket tL par = cfg
  rw [hhk₁, hhk₂] at hAg
  suffices hSim : ∀ st : EState _ M (Header Pt × E) _ × Option ℕ, AllPartiesInv st.1 →
      (simulateQ (implEDFPaperBucketMode hk₁ (2 + Δcka) qep fs.maxSkip cfg gMain isHonestHdrFSMultiDFBucket) A).run st =
      (simulateQ (implEDFPaperBucketMode hk₂ (2 + Δcka) qep fs.maxSkip cfg gMain isHonestHdrFSMultiDFBucket) A).run st by
    exact congrArg (· >>= _) (hSim (_, none) hEs₀)
  intro st hEs
  induction A using OracleComp.inductionOn generalizing st with
  | pure _ => simp
  | query_bind qy mx ih =>
    rcases st with ⟨es, winEp⟩
    rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind]
    rcases qy with n | t_df
    · have hCoinL := withWinEpDFMode_inl_run hk₁ (2 + Δcka) qep fs.maxSkip cfg gMain
        isHonestHdrFSMultiDFBucket n es winEp
      have hCoinR := withWinEpDFMode_inl_run hk₂ (2 + Δcka) qep fs.maxSkip cfg gMain
        isHonestHdrFSMultiDFBucket n es winEp
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u (es, winEp) hEs
    · obtain ⟨hEq, hInv⟩ := implEDFPaperBucketRaw_localCKA_step hAg (2 + Δcka) qep fs.maxSkip cfg es t_df hEs
      have hStep :
          ((implEDFPaperBucketMode hk₁ (2 + Δcka) qep fs.maxSkip cfg gMain
            isHonestHdrFSMultiDFBucket (.inr t_df)).run (es, winEp)) =
          ((implEDFPaperBucketMode hk₂ (2 + Δcka) qep fs.maxSkip cfg gMain
            isHonestHdrFSMultiDFBucket (.inr t_df)).run (es, winEp)) := by
        cases gMain <;>
          simp only [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, ↓reduceIte,
            Bool.false_eq_true, StateT.run_mk, hEq]
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, ⟨es', winEp'⟩⟩ hmem => ?_
      cases gMain <;>
        (simp only [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, ↓reduceIte,
          Bool.false_eq_true, StateT.run_mk, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         obtain ⟨⟨u₁, es₁⟩, hmem₁, huEq, hesEq, hwEq⟩ := hmem;
         subst huEq hesEq hwEq;
         exact ih u (es', _) (hInv _ hmem₁))

private theorem implEDFPaperBucketRaw_inv {Γ T RSt SS RS M E CCoins : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((transmitEBucket hk Δ qep (P, m, r)).run es) at hmem
    unfold transmitEBucket abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.2 ▸ hInvQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        exact hmem.2 ▸ hInvQ
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, _⟩, _, hmem⟩ := hmem; rcases vsRes with _ | ⟨st', _⟩ <;>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        · exact hmem.2 ▸ hInvQ
        · exact hmem.2 ▸ hInv.epMgmt_record hep st' _ false
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [challEBucket, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hmem.2 ▸ hInvQ
  · exact deliverE_inv hk cfg es (P, c) hInv
  · exact injectE_inv hk cfg es (P, c) hInv
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((corrEPaperBucket hk P).run es) at hmem
    unfold corrEPaperBucket abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.2 ▸ hInvQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, _⟩, _, hmem⟩ := hmem; rcases revRes with _ | _ <;>
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      · exact hmem.2 ▸ hInvQ
      · exact hmem.2 ▸ hInv.afterCorr P
  · exact deliverForgeE_inv hk cfg es arg hInv

private theorem implEDFPaperBucketRaw_vrInv {Γ T RSt SS RS M E CCoins : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((implEDFPaperBucketRaw hk Δ qep maxSkip cfg (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | arg
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((transmitEBucket hk Δ qep (P, m, r)).run es) at hmem
    unfold transmitEBucket abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.2 ▸ hVRQ
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        exact hmem.2 ▸ hVRQ
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem; rcases vsRes with _ | ⟨st', ct⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          exact hmem.2 ▸ hVRQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          have hst_eq := epMgmt_st_eq hep
          have hvR_eq := vSend_vR_eq hk s₁ P (s₁.st P) m none r es.h (some (st', ct), h') hvs st' ct rfl
          intro Q t₀ v₀ hv₀; simp only [GameState.record] at hv₀
          by_cases hQP : Q = P
          · subst hQP; simp only [Function.update_self, hvR_eq, hst_eq] at hv₀; exact hVRQ Q t₀ v₀ hv₀
          · simp only [Function.update_of_ne hQP, hst_eq] at hv₀; exact hVRQ Q t₀ v₀ hv₀
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [challEBucket, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hmem.2 ▸ hVRQ
  · exact implE_vrInv hk hVRHk (Δ := Δ) (qep := qep) (maxSkip := maxSkip) cfg
      (⟨false, none, 0⟩ : Mode).policy es (.inl (.inl (.inr (P, c)))) hInv hVR
  · exact implE_vrInv hk hVRHk (Δ := Δ) (qep := qep) (maxSkip := maxSkip) cfg
      (⟨false, none, 0⟩ : Mode).policy es (.inl (.inr (P, c))) hInv hVR
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((corrEPaperBucket hk P).run es) at hmem
    unfold corrEPaperBucket abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.2 ▸ hVRQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, _⟩, _, hmem⟩ := hmem; rcases revRes with _ | _ <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; exact hmem.2 ▸ hVRQ)
  · exact deliverForgeE_vrInv hk hVRHk cfg es arg hInv hVR

private theorem simulateQ_implEDFPaperBucketMode_fs_eq
    {Pt : Type} [DecidableEq Pt]
    {ℓ B0 L B_q q Δcka qep maxSkip : ℕ}
    (hk₁ hk₂ : Hooks
      (FSMultiSpec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        Pt (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiDFBucketState Pt (BitVec 256) (BitVec 256) Pt (ℕ × LibsignalCiphertextWithSalt32))
      (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (cfg : Config (LibsignalMsgPublicPart × Plain ℓ)) (gMain : Bool)
    (hVRHk : HooksVRInv (FSVROkMultiReachB maxSkip) hk₂)
    (hB0 : (B_q + 1) * (maxSkip + 1) ≤ B0)
    (hFsSendEq : ∀ ctx P t ssv hdr m pair, atomicShortPubB m.1 = true →
      hk₁.fsSend ctx P t ssv hdr m pair = hk₂.fsSend ctx P t ssv hdr m pair)
    (hFsRecvEq : ∀ ctx P t rsv hdr e rec_ k',
      (k' + 1) * (maxSkip + 1) ≤ B0 → FSVROkMultiReachB maxSkip k' rsv →
      hk₁.fsRecv ctx P t rsv hdr e rec_ = hk₂.fsRecv ctx P t rsv hdr e rec_)
    (hStartSend : hk₁.startSend = hk₂.startSend)
    (hStartRecv : hk₁.startRecv = hk₂.startRecv)
    (hCommit : hk₁.commit = hk₂.commit)
    (hReveal : hk₁.reveal = hk₂.reveal)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (st : EState _ _ _ _ × Option ℕ)
    (hoa : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := _root_.CryptoGames.SM.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hInv : SMEngineInv L B_q q st.1.g)
    (hVR : SMVRInv (FSVROkMultiReachB maxSkip) B_q q st.1.g) :
    (simulateQ (implEDFPaperBucketMode hk₁ (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket) A).run st =
      (simulateQ (implEDFPaperBucketMode hk₂ (2 + Δcka) qep maxSkip cfg gMain isHonestHdrFSMultiDFBucket) A).run st := by
  induction A using OracleComp.inductionOn generalizing q st with
  | pure _ => simp
  | query_bind qy mx ih =>
    rcases st with ⟨es, winEp⟩
    unfold SendMsgsOkDF at hSendOk
    rw [isQueryBoundP_query_bind_iff] at hoa hSendOk
    rcases hoa with ⟨hq0, hmx⟩
    rcases hSendOk with ⟨hBad0, hSendMx⟩
    rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hCoinL := withWinEpDFMode_inl_run hk₁ (2 + Δcka) qep maxSkip cfg gMain
        isHonestHdrFSMultiDFBucket n es winEp
      have hCoinR := withWinEpDFMode_inl_run hk₂ (2 + Δcka) qep maxSkip cfg gMain
        isHonestHdrFSMultiDFBucket n es winEp
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih (q := q) u (es, winEp) (hmx u) (by simpa [SendMsgsOkDF] using hSendMx u) hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hBadFalse : badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
          (fun m => atomicShortPubB m.1) (.inr t_sm) = false :=
        Bool.eq_false_iff.mpr (hBad0.resolve_right (by omega))
      have hkB : (B_q - (q' + 1) + 1) * (maxSkip + 1) ≤ B0 :=
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
      have hCommitE : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hCommit]
      have hvSendEq : ∀ s P m r, atomicShortPubB m.1 = true →
          (vSend hk₁ s P (s.st P) m none r).run es.h =
            (vSend hk₂ s P (s.st P) m none r).run es.h := by
        intro s P m r hm
        rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind]
        have hStep1 : vSendStep1 hk₁ s P (s.st P) r = vSendStep1 hk₂ s P (s.st P) r := by
          unfold vSendStep1; rw [hStartSend]
        rw [hStep1]
        refine bind_congr fun ⟨s₁?, h₁⟩ => ?_
        rcases s₁? with _ | s₁
        · rfl
        · rcases hvS : s₁.vS with _ | ssv
          · simp only [hvS]
          · simp only [hvS, StateT.run_bind, hFsSendEq s P s₁.tcur ssv (s₁.tcur, s₁.curCkaMsg) m none hm]
      have hvRecvEq : ∀ P c rec_,
          (vRecv hk₁ es.g P (es.g.st P) c rec_).run es.h =
            (vRecv hk₂ es.g P (es.g.st P) c rec_).run es.h := by
        intro P c rec_
        rw [vRecv_eq_bind, vRecv_eq_bind]
        by_cases href : ((es.g.st P).id.sendsIn c.1.1 || decide ((es.g.st P).tcur + 1 < c.1.1)) = true
        · simp [href]
        · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          have hStep1 : vRecvStep1 hk₁ es.g P (es.g.st P) c = vRecvStep1 hk₂ es.g P (es.g.st P) c := by
            unfold vRecvStep1; rw [hStartRecv]
          rw [hStep1]
          refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
          rcases s₁? with _ | (_ | s₁)
          · rfl
          · rfl
          · have hs₁VR : ∀ t v, s₁.vR t = some v → FSVROkMultiReachB maxSkip (B_q - (q' + 1)) v := by
              unfold vRecvStep1 at hmem
              by_cases ht : c.1.1 = (es.g.st P).tcur + 1
              · simp only [ht, ↓reduceIte] at hmem
                rcases hTn : c.1.2 with _ | Tn
                · simp [hTn] at hmem
                · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem
                  obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
                  rcases srRes with _ | _ | ⟨γ', σ', rsv⟩
                  · simp at hmem
                  · simp at hmem
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                      Prod.mk.injEq, Option.some.injEq] at hmem
                    rcases hmem with ⟨rfl, rfl⟩
                    intro t₀ v₀ hv₀
                    by_cases ht₀ : t₀ = (es.g.st P).tcur + 1
                    · subst ht₀
                      simp only [Function.update_self, Option.some.injEq] at hv₀; subst hv₀
                      exact hVRHk.mono (Nat.zero_le _)
                        (hVRHk.startRecv_step es.g P ((es.g.st P).tcur + 1)
                          (es.g.st P).γ (es.g.st P).root Tn es.h
                          (some (some (γ', σ', rsv)), h₁) hsr γ' σ' rsv rfl)
                    · simp only [Function.update_of_ne ht₀] at hv₀
                      exact hVR P t₀ v₀ hv₀
              · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq, Option.some.injEq] at hmem
                rcases hmem with ⟨rfl, _⟩; exact hVR P
            rcases hvRc : s₁.vR c.1.1 with _ | rsv
            · simp [hvRc]
            · simp only [hvRc, StateT.run_bind,
                hFsRecvEq es.g P c.1.1 rsv c.1 c.2 rec_ _ hkB (hs₁VR c.1.1 rsv hvRc)]
      have hStepRaw :
          (implEDFPaperBucketRaw hk₁ (2 + Δcka) qep maxSkip cfg (.inr t_sm)).run es =
          (implEDFPaperBucketRaw hk₂ (2 + Δcka) qep maxSkip cfg (.inr t_sm)).run es := by
        rcases t_sm with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
        · change (transmitEBucket hk₁ (2 + Δcka) qep (P, m, r)).run es =
            (transmitEBucket hk₂ (2 + Δcka) qep (P, m, r)).run es
          have hm : atomicShortPubB m.1 = true := by simpa [badSendMsgDF] using hBadFalse
          unfold transmitEBucket
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hab : (es.abort || es.g.win) = true
          · simp [hab]
          · simp only [hab, Bool.false_eq_true, ↓reduceIte]
            rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
            · rfl
            · simp only [run_liftH_bind, hvSendEq s₁ P m r hm]
        · change (challEBucket (P, m₀, m₁, r)).run es = (challEBucket (P, m₀, m₁, r)).run es
          rfl
        · change (deliverE hk₁ maxSkip cfg (P, c)).run es = (deliverE hk₂ maxSkip cfg (P, c)).run es
          unfold deliverE
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hab : (es.abort || es.g.win) = true
          · simp [hab]
          · simp only [hab, Bool.false_eq_true, ↓reduceIte]
            rcases es.g.inTransit P.other c with _ | rec_
            · rfl
            · simp only [run_liftH_bind, hvRecvEq P c (some rec_), hCommitE]
        · change (_root_.CryptoGames.SM.Engine.injectE hk₁ (2 + Δcka) qep cfg (P, c)).run es =
            (_root_.CryptoGames.SM.Engine.injectE hk₂ (2 + Δcka) qep cfg (P, c)).run es
          unfold _root_.CryptoGames.SM.Engine.injectE
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
          · simp [href]
          · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvRecvEq P c none, hCommitE]
        · change (corrEPaperBucket hk₁ P).run es = (corrEPaperBucket hk₂ P).run es
          unfold corrEPaperBucket; rw [hReveal]
        · change (deliverForgeE hk₁ (2 + Δcka) qep cfg (P, c, c')).run es =
            (deliverForgeE hk₂ (2 + Δcka) qep cfg (P, c, c')).run es
          unfold deliverForgeE
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hab : (es.abort || es.g.win) = true
          · simp [hab]
          · simp only [hab, Bool.false_eq_true, ↓reduceIte]
            rcases es.g.inTransit P.other c with _ | r
            · rfl
            · dsimp only
              by_cases hbad : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
              · simp only [hbad, ↓reduceIte]
              · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvRecvEq P c' none, hCommitE]
      have hStep :
          ((implEDFPaperBucketMode hk₁ (2 + Δcka) qep maxSkip cfg gMain
            isHonestHdrFSMultiDFBucket (.inr t_sm)).run (es, winEp)) =
          ((implEDFPaperBucketMode hk₂ (2 + Δcka) qep maxSkip cfg gMain
            isHonestHdrFSMultiDFBucket (.inr t_sm)).run (es, winEp)) := by
        cases gMain <;>
          simp only [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, ↓reduceIte,
            Bool.false_eq_true, StateT.run_mk, hStepRaw]
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, ⟨es', winEp'⟩⟩ hmem => ?_
      cases gMain <;>
        (simp only [implEDFPaperBucketMode, withWinEpDFMode, withWinEpDF, ↓reduceIte,
          Bool.false_eq_true, StateT.run_mk, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         obtain ⟨⟨u₁, es₁⟩, hmem₁, huEq, hesEq, hwEq⟩ := hmem;
         subst huEq hesEq hwEq;
         exact ih (q := q') u (es', _) (by simpa using hmx u) (by simpa [SendMsgsOkDF] using hSendMx u)
           (implEDFPaperBucketRaw_inv hk₂ cfg es t_sm hInv (u, es') hmem₁)
           (implEDFPaperBucketRaw_vrInv hk₂ hVRHk cfg es t_sm hInv hVR (u, es') hmem₁))

private theorem redFSAuthDFPaperMultiBucketModeGen_fsClamp_fsAtomicB_eq_lFS
    {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (cka : CKAScheme (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (C : Crypto) (ℓ B0 L B_q q Δcka Δbucket qep : ℕ)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqB : q ≤ B_q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    redFSAuthDFPaperMultiBucketModeGen L cka (rootPRNG C.F encPt)
        (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam Δcka Δbucket qep gMain la tL par A =
      redFSAuthDFPaperMultiBucketModeGen L cka (rootPRNG C.F encPt)
        (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        lam Δcka Δbucket qep gMain la tL par A := by
  let prng := rootPRNG C.F encPt
  let fs₁ := fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
  let fs₂ := fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
  let hk₁ := hooksFSMultiDFBucketPaperMode L cka prng fs₁ Δcka Δbucket qep gMain tL par la
  let hk₂ := hooksFSMultiDFBucketPaperMode L cka prng fs₂ Δcka Δbucket qep gMain tL par la
  let cfg := bucketAuthCfgGen (Msg := LibsignalMsgPublicPart × Plain ℓ) Δbucket tL par
  have hVRHk := hooksFSMultiDFBucketPaperMode_vrInv_fsClamp_lFS L cka prng C ℓ B0 encT idOf
    Δcka Δbucket qep gMain tL par la
  have hInitEq : initFSMultiDFBucketPaper L cka (rootPRNG C.F encPt)
        (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam Δbucket qep tL par =
      initFSMultiDFBucketPaper L cka (rootPRNG C.F encPt)
        (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) lam Δbucket qep tL par := by
    dsimp only [initFSMultiDFBucketPaper, rootFSMultiDFBucketPaper, fsClamp, fsAtomicB, fsAtomic,
      lFS, _root_.CryptoGames.FSAEAD.fromAEADPRG]
  have hms1 : (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)).maxSkip = maxForwardJumps := by
    dsimp only [fsClamp, fsAtomicB, fsAtomic, _root_.CryptoGames.FSAEAD.fromAEADPRG]
  have hms2 : (fsClamp B0 (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)).maxSkip = maxForwardJumps := by
    dsimp only [fsClamp, lFS, _root_.CryptoGames.FSAEAD.fromAEADPRG]
  unfold redFSAuthDFPaperMultiBucketModeGen engRunDFPaperBucketMode
  rw [hInitEq, hms1, hms2, bind_assoc, bind_assoc]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h₀⟩ hmem₀ => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  dsimp only [bind_assoc, pure_bind]
  let g₀ : Ctx (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256) ⊕ ℕ) (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
    { st := fun P => match P with | .A => vA | .B => vB, b := false }
  have ⟨hInv₀, hVR₀⟩ : SMEngineInv L B_q q g₀ ∧
      SMVRInv (FSVROkMultiReachB maxForwardJumps) B_q q g₀ := by
    unfold initFSMultiDFBucketPaper at hmem₀
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
      pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem₀
    obtain ⟨⟨kr, _⟩, _, ⟨kc, _⟩, _, ⟨⟨σ, kVal, sid⟩, h₁⟩, _, hEq⟩ := hmem₀
    cases hEq
    refine ⟨(SMEngineInv.init _ false hB1 hBB).mono hqB, fun P t₀ v hv => ?_⟩
    cases P <;> simp only [g₀] at hv
    · by_cases ht0 : t₀ = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv; subst hv
        rcases (regSessOptMultiDFBucket L tL 0 sid h₁).1 with _ | _
        · exact (RSReachB.init
            ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
            (lChainPRG C.F) maxForwardJumps kVal).mono (Nat.zero_le _)
        · trivial
      · simp [ht0] at hv
    · cases hv
  have hFsSendEq : ∀ ctx P t ssv hdr m pair, atomicShortPubB m.1 = true →
      hk₁.fsSend ctx P t ssv hdr m pair = hk₂.fsSend ctx P t ssv hdr m pair := by
    intro ctx P t ssv hdr m pair hm
    rcases ssv with ss | sIdx
    · dsimp only [hk₁, hk₂, hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper, fs₁, fs₂, fsClamp]
      rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
    · rfl
  have hFsRecvEq : ∀ ctx P t rsv hdr e rec_ k',
      (k' + 1) * (maxForwardJumps + 1) ≤ B0 → FSVROkMultiReachB maxForwardJumps k' rsv →
      hk₁.fsRecv ctx P t rsv hdr e rec_ = hk₂.fsRecv ctx P t rsv hdr e rec_ := by
    intro ctx P t rsv hdr e rec_ k' hkB hvr
    rcases rsv with rs | sIdx
    · dsimp only [hk₁, hk₂, hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper, fs₁, fs₂, fsClamp]
      rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e (rsReachB_skippedKeys_le hvr hkB)]
    · rfl
  have hStartSend : hk₁.startSend = hk₂.startSend := by
    dsimp only [hk₁, hk₂, hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper,
      rootFSMultiDFBucketPaper, fs₁, fs₂, fsClamp, fsAtomicB, fsAtomic, lFS,
      _root_.CryptoGames.FSAEAD.fromAEADPRG]
  have hStartRecv : hk₁.startRecv = hk₂.startRecv := by
    cases gMain <;>
      dsimp only [hk₁, hk₂, hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper,
        fs₁, fs₂, fsClamp, fsAtomicB, fsAtomic, lFS, _root_.CryptoGames.FSAEAD.fromAEADPRG]
  have hCommit : hk₁.commit = hk₂.commit := by
    dsimp only [hk₁, hk₂, hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]
  have hReveal : hk₁.reveal = hk₂.reveal := by
    cases gMain <;> dsimp only [hk₁, hk₂, hooksFSMultiDFBucketPaperMode, hooksFSMultiDFBucketPaper]
  have hA_game : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := _root_.CryptoGames.SM.specDF
      (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) q :=
    hq.of_imp fun x hx => by cases x <;> [cases hx; rfl]
  simp only [bind_assoc, pure_bind]
  exact congrArg (· >>= _)
    (simulateQ_implEDFPaperBucketMode_fs_eq hk₁ hk₂ cfg gMain hVRHk hB0
      hFsSendEq hFsRecvEq hStartSend hStartRecv hCommit hReveal A
      ({ g := g₀, h := h₀ }, none) hA_game hsh hInv₀ hVR₀)

theorem redFSAuthDFPaperMultiBucketModeProg_eval_lFS
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (Z : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    (redFSAuthDFPaperMultiBucketModeProg
        (ckaInitA := (dhSchemeFb Dh).initA) (ckaInitB := (dhSchemeFb Dh).initB)
        (ckaSend := (dhSchemeFb Dh).send) (ckaReceive := (dhSchemeFb Dh).receive)
        (prngInit := (rootPRNG Z.F encPt).init) (prngUp := (rootPRNG Z.F encPt).up)
        (fsInitSender := (fsAtomicB Z ℓ encT idOf B0).initSender)
        (fsInitReceiver := (fsAtomicB Z ℓ encT idOf B0).initReceiver)
        (fsSend := (fsAtomicB Z ℓ encT idOf B0).send)
        (fsReceive := (fsAtomicB Z ℓ encT idOf B0).receive)
        (eqT := (· == ·)) (eqI := (· == ·)) (eqM := (· == ·)) (eqE := (· == ·))
        (lam := lam) (defaultE := default)
        (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
        (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
        (q + 1) B0 1 4 qep maxForwardJumps gMain la tL par).eval (fun _ => A) () =
      redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 4 qep gMain la tL par A := by
  have heqM' : (fun x1 x2 : LibsignalMsgPublicPart × Plain ℓ => x1 == x2) =
      fun x1 x2 => @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq x1 x2 := by
    funext x1 x2
    exact Bool.eq_iff_iff.mpr (beq_iff_eq.trans decide_eq_true_iff.symm)
  have heqE' : (fun x1 x2 : ℕ × LibsignalCiphertextWithSalt32 => x1 == x2) =
      fun x1 x2 => @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq x1 x2 := by
    funext x1 x2
    exact Bool.eq_iff_iff.mpr (beq_iff_eq.trans decide_eq_true_iff.symm)
  have hB1 : q + 1 ≤ q + 1 := le_rfl
  have hBB : q * q ≤ (q + 1) * (q + 1) := Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have hEval := redFSAuthDFPaperMultiBucketModeProgGen_eval_clamp (lam := lam)
    (eqT := (· == ·)) (eqI := (· == ·)) (eqM := (· == ·)) (eqE := (· == ·))
    (dhSchemeFb Dh) (rootPRNG Z.F encPt) (fsAtomicB Z ℓ encT idOf B0)
    (q + 1) B0 q 1 4 qep gMain la tL par
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl heqM' heqE' rfl rfl rfl rfl rfl rfl
    hB1 hBB A q hq le_rfl
  have hms : (fsAtomicB Z ℓ encT idOf B0).maxSkip = maxForwardJumps := rfl
  rw [hms] at hEval
  have hStep1 := redFSAuthDFPaperMultiBucketModeGen_dhSchemeFb_eq (q + 1) Dh (rootPRNG Z.F encPt)
    (fsClamp B0 (fsAtomicB Z ℓ encT idOf B0)) lam 1 4 qep gMain la tL par A
  have hStep2 := redFSAuthDFPaperMultiBucketModeGen_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) Z ℓ B0
    (q + 1) q q 1 4 qep encPt encT idOf lam gMain la tL par (le_of_eq hB0.symm) hB1 hBB A hq le_rfl hsh
  have hStep3 := redFSAuthDFPaperMultiBucketModeGen_fsClamp_fromAEADPRG (dhScheme Dh) (rootPRNG Z.F encPt)
    ((lAead Z protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
    (lChainPRG Z.F) maxForwardJumps (q + 1) B0 q 1 4 qep lam gMain la tL par
    (le_of_eq hB0.symm) hB1 hBB A q hq le_rfl
  have hlFS : ∀ ms, _root_.CryptoGames.FSAEAD.fromAEADPRG
      ((lAead Z protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG Z.F) ms =
    lFS Z protoSignalCodec ℓ encT idOf ms := fun _ => rfl
  rw [hlFS] at hStep3
  exact hEval.trans (hStep1.trans (hStep2.trans hStep3))


end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketMode

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow
import Computational.Proofs.ReductionDsl.SM.RedFS
import Computational.Proofs.Fig8SchemeBridge

/-!
# Atomic Scheme Swap for `BucketFSAuthBridgeHop` (`N09b`)

Proves `redFSAuthMultiBucket_main_atomic_eq`, rewriting `(redFSAuthMultiBucketShallow ... true la tL par).eval`
(`dhSchemeFb Dh` + `fsClamp B0 (fsAtomicB ... B0)`) to `redFSAuthMultiBucket ... (dhScheme Dh) ... (lFS ...)`
under `MakesAtMostQueries A q` and `SendMsgsOk (fun m => atomicShortPubB m.1) A`.-/

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopAtomic

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState fromAEADPRG)
open _root_.CryptoGames.SM (GameState Record)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header
  FSMultiSpec fsClamp mkParties)
open _root_.CryptoGames.SM.Engine (VP Ctx EState Hooks HooksVRInv SMEngineInv SMVRInv Policy
  vSend vSendStep1 vSend_eq_bind vRecv vRecvStep1 vRecv_eq_bind commitE
  transmitE challE deliverE injectE corrE coinsE implE abortE run_liftH_bind
  implE_inv implE_vrInv)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (badSendMsg_chall_false
  badSendMsg_query_bind_step badSendMsg_transmit_false)
open _root_.ReductionDsl (isGameQuery)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lChainPRG lAead lPubOf lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  rootFSMultiBucketAuth regSessOptMultiBucket isHonestHdrMultiBucket
  hooksFSMultiBucketAuth initFSMultiBucketAuth implFSMultiBucketAuth redFSAuthMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeShallow (
  redFSAuthMultiBucketShallow_eval_eq)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase (redFSAuthMultiBucketShallow)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak bucketAuthCfg)

private def noDoomPolicy : Policy := ⟨false, none, 0⟩

@[simp] private theorem noDoomPolicy_leakDoom {St Msg C : Type}
    (g g' : GameState St Msg C) :
    noDoomPolicy.leakDoom g g' = false := by
  simp [noDoomPolicy, Policy.leakDoom]

@[simp] private theorem noDoomPolicy_corrDoom {St Msg C : Type}
    (g : GameState St Msg C) (P : Party) :
    noDoomPolicy.corrDoom g P = false := by
  simp [noDoomPolicy, Policy.corrDoom]

private def fsMultiUpdateWinEp {Γ T RSt SS RS M E K I CCoins : Type} [DecidableEq T]
    (gMain : Bool)
    (es0 es' : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiBucketAuthState T RSt K I E))
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (winEp0 : Option ℕ) : Option ℕ :=
  match qy with
  | .inr (.inl (.inr x)) =>
    let isNewForged :=
      decide (x.2.1.1 = (es0.g.st x.1).tcur + 1) && !isHonestHdrMultiBucket es0.h x.2.1
    if !es0.g.win && es'.g.win && (gMain || isNewForged) then some x.2.1.1 else winEp0
  | _ => winEp0

private theorem implFSMultiBucketAuth_run_eq_implE
    {Γ T RSt SS RS M E K I CCoins : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E]
    (hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (Δcka qep maxSkip : ℕ) (gMain : Bool) (tL : Option ℕ)
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiBucketAuthState T RSt K I E))
    (winEp0 : Option ℕ) :
    (implFSMultiBucketAuth hk Δcka qep maxSkip gMain tL qy).run (es0, winEp0) =
      ((implE hk (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy qy).run es0 >>=
        fun res => pure (res.1,
          (res.2, fsMultiUpdateWinEp gMain es0 res.2 qy winEp0))) := by
  rcases qy with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [implFSMultiBucketAuth, implE, QueryImpl.add_apply, coinsE, fsMultiUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implFSMultiBucketAuth, implE, QueryImpl.add_apply, transmitE, fsMultiUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp
      | some s₁ =>
        simp only [noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte]
        rw [StateT.run_bind, StateT.run_lift, _root_.CryptoGames.SM.Engine.run_liftH_bind]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun ⟨res, h'⟩ => ?_
        rcases res with _ | ⟨st', ct⟩ <;> simp [abortE]
  · dsimp only [implFSMultiBucketAuth, implE, QueryImpl.add_apply, challE,
      bucketAuthCfg, fsMultiUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome <;> simp
  · dsimp only [implFSMultiBucketAuth, implE, QueryImpl.add_apply, fsMultiUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implFSMultiBucketAuth, implE, QueryImpl.add_apply, fsMultiUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind]
    exact bind_congr fun _ => rfl
  · dsimp only [implFSMultiBucketAuth, implE, QueryImpl.add_apply, corrE, fsMultiUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win || !es0.g.corrAllowed P) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte,
        noDoomPolicy_leakDoom, noDoomPolicy_corrDoom, Bool.or_self]
      rw [StateT.run_bind, StateT.run_lift, _root_.CryptoGames.SM.Engine.run_liftH_bind]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun ⟨res, h'⟩ => ?_
      cases res <;> simp [abortE]

private theorem hooksFSMultiBucketAuth_main_localCKAAgree
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [DecidableEq E]
    [SampleableType Pt] [SampleableType K]
    (L : ℕ) (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par la : Bool) :
    _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree
      (fun P γ t => _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P t γ)
      (hooksFSMultiBucketAuth L (dhSchemeFb Dh) prng fs Δcka qep true tL par la)
      (hooksFSMultiBucketAuth L (dhScheme Dh) prng fs Δcka qep true tL par la) where
  startSend_eq ctx P t γ σv r h ht hSend hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hSend' : P.sendsIn ((t - 1) + 1) = true := ht1.symm ▸ hSend
    dsimp only [hooksFSMultiBucketAuth]
    have hCoins : ∀ coins : BitVec 256,
        (do
          let (σ', kVal, sid) ← rootFSMultiBucketAuth (SS := SS) (RS := RS) (M := M)
            prng Δcka qep tL par t (postLeak tL ctx) ((dhSchemeFb Dh).send γ coins).2.2 σv
          let s1 : FSMultiBucketAuthState Pt RSt K Pt E ← get
          let (optIdx, s2) := regSessOptMultiBucket L true tL t sid s1
          set { s2 with cache := Function.update s2.cache t (some (((dhSchemeFb Dh).send γ coins).2.1, σ', kVal, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with | none => .inl (fs.initSender kVal) | some sIdx => .inr sIdx
          return some (((dhSchemeFb Dh).send γ coins).1, ((dhSchemeFb Dh).send γ coins).2.1, σ', ssv)).run h =
        (do
          let (σ', kVal, sid) ← rootFSMultiBucketAuth (SS := SS) (RS := RS) (M := M)
            prng Δcka qep tL par t (postLeak tL ctx) ((dhScheme Dh).send γ coins).2.2 σv
          let s1 : FSMultiBucketAuthState Pt RSt K Pt E ← get
          let (optIdx, s2) := regSessOptMultiBucket L true tL t sid s1
          set { s2 with cache := Function.update s2.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', kVal, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with | none => .inl (fs.initSender kVal) | some sIdx => .inr sIdx
          return some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', ssv)).run h ∧
        ∀ q ∈ support ((do
          let (σ', kVal, sid) ← rootFSMultiBucketAuth (SS := SS) (RS := RS) (M := M)
            prng Δcka qep tL par t (postLeak tL ctx) ((dhScheme Dh).send γ coins).2.2 σv
          let s1 : FSMultiBucketAuthState Pt RSt K Pt E ← get
          let (optIdx, s2) := regSessOptMultiBucket L true tL t sid s1
          set { s2 with cache := Function.update s2.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', kVal, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with | none => .inl (fs.initSender kVal) | some sIdx => .inr sIdx
          return some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', ssv)).run h),
          ∀ γ' T' σ' ssv, q.1 = some (γ', T', σ', ssv) →
            _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P t γ' := by
      intro coins
      have hsnd := _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.dhSchemeFb_send_of_roleOk
        Dh hRole hSend' coins
      have hRole' : _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P t
          ((dhScheme Dh).send γ coins).1 := ht1 ▸ hsnd.2
      simp only [hsnd.1]
      refine ⟨trivial, fun q hq γ' T' σ' ssv hEq => ?_⟩
      rw [StateT.run_bind, mem_support_bind_iff] at hq
      obtain ⟨⟨⟨σ₁, k₁, sid₁⟩, h₁⟩, _, hq⟩ := hq
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hq
      subst hq; cases hEq; exact hRole'
    rcases r with _ | c
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine ⟨bind_congr fun coins => (hCoins coins).1, fun q hq γ' T' σ' ssv hEq => ?_⟩
      rw [mem_support_bind_iff] at hq
      obtain ⟨coins, _, hq⟩ := hq
      exact (hCoins coins).2 q hq γ' T' σ' ssv hEq
    · simp only [pure_bind]; exact hCoins c
  startRecv_eq ctx P t γ σv Tn h ht hRecv hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.dhSchemeFb_receive_of_roleOk
      Dh hRole hRecv' Tn
    have hRole' : _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P t
        ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    dsimp only [hooksFSMultiBucketAuth]
    simp only [hrcv.1, ↓reduceIte]
    refine ⟨trivial, fun q hq γ' σ' rsv hEq => ?_⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
    split at hq
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
      subst hq; cases hEq; exact hRole'
    · split_ifs at hq <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
         subst hq; cases hEq)
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

private theorem redFSAuthMultiBucket_main_dhSchemeFb_eq
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType Pt] [SampleableType K]
    (L : ℕ) (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep : ℕ)
    (la : Bool) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    redFSAuthMultiBucket L (dhSchemeFb Dh) prng fs lam Δcka qep true la tL par A =
      redFSAuthMultiBucket L (dhScheme Dh) prng fs lam Δcka qep true la tL par A := by
  unfold redFSAuthMultiBucket
  have hInit : initFSMultiBucketAuth L (dhSchemeFb Dh) prng fs lam Δcka qep true tL par =
      initFSMultiBucketAuth L (dhScheme Dh) prng fs lam Δcka qep true tL par := rfl
  rw [hInit]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨vA, vB⟩, h0⟩ hmem => ?_
  have hAll : _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv
      (M := M) (E := E) (HS := FSMultiBucketAuthState Pt RSt K Pt E)
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h0 } := by
    unfold initFSMultiBucketAuth at hmem
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨kr, _, kc, _, ⟨⟨σ, kVal, sid⟩, h1⟩, _, hmem⟩ := hmem
    rcases Prod.mk.inj hmem.symm with ⟨hvp, rfl⟩
    rcases Prod.mk.inj hvp with ⟨rfl, rfl⟩
    intro P; cases P
    · exact ⟨rfl, _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.ddhRoleOk_initA Dh kc⟩
    · exact ⟨rfl, _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.ddhRoleOk_initB Dh kc⟩
  have hAg := hooksFSMultiBucketAuth_main_localCKAAgree L Dh prng fs Δcka qep tL par la
  suffices hSim : ∀ (oa : SchemeAdversary (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        Pt RSt SS RS M (BitVec 256) E) (es : _) (we : Option ℕ),
      _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv es →
      (simulateQ (implFSMultiBucketAuth (hooksFSMultiBucketAuth L (dhSchemeFb Dh) prng fs Δcka qep true tL par la)
          Δcka qep fs.maxSkip true tL) oa).run (es, we) =
        (simulateQ (implFSMultiBucketAuth (hooksFSMultiBucketAuth L (dhScheme Dh) prng fs Δcka qep true tL par la)
          Δcka qep fs.maxSkip true tL) oa).run (es, we) by
    exact congrArg (· >>= _) (hSim A _ none hAll)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => intro es we _; simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    intro es we hEs
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rw [implFSMultiBucketAuth_run_eq_implE, implFSMultiBucketAuth_run_eq_implE]
    simp only [bind_assoc, pure_bind]
    rcases qy with n | t_sm
    · have hInl1 : (implE (hooksFSMultiBucketAuth L (dhSchemeFb Dh) prng fs Δcka qep true tL par la)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl2 : (implE (hooksFSMultiBucketAuth L (dhScheme Dh) prng fs Δcka qep true tL par la)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem' => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem'
      obtain ⟨_, _, _, rfl⟩ := hmem'
      exact ih u _ _ hEs
    · have hStep := _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge.implE_localCKA_eq
        hAg (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy es t_sm hEs
      rw [hStep.1]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem' =>
        ih u es' _ (hStep.2 (u, es') hmem')

private def MultiBucketVROk (k : ℕ) :
    (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ) → Prop
  | .inl rs => RSReachB maxForwardJumps k rs
  | .inr _ => True

private theorem rsReachB_len_le_local {CK MK : Type} {maxSkip k B0 : ℕ}
    (hB0 : (k + 1) * (maxSkip + 1) ≤ B0) {v : RatchetReceiverState CK MK}
    (hv : RSReachB maxSkip k v) : v.skippedKeys.length ≤ B0 := by
  have h1 := hv.1.1
  have h2 := hv.2
  have h3 : k * (maxSkip + 1) ≤ (k + 1) * (maxSkip + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_succ k)
  omega

private theorem fsClamp_fsAtomicB_receive_eq_lFS {Pt : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 k : ℕ) (hB0 : (k + 1) * (maxForwardJumps + 1) ≤ B0)
    {rs : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hrs : RSReachB maxForwardJumps k rs)
    (hdr : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) :
    (fsClamp B0 (fsAtomicB C ℓ encT idOf B0)).receive rs hdr e =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs hdr e := by
  have hlen : rs.skippedKeys.length ≤ B0 := rsReachB_len_le_local hB0 hrs
  change ((fsAtomicB C ℓ encT idOf B0).receive rs hdr e).map
      (fun (rs', i, m) => (rs', min i B0, m)) = _
  rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  exact _root_.CryptoGames.SM.Construction.fsClamp_receive_fromAEADPRG
    ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
    (lChainPRG C.F) maxForwardJumps B0 k hB0 hrs.1 hdr e

private theorem hooksFSMultiBucketAuth_main_vrInv_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep : ℕ) (tL : Option ℕ) (par la : Bool) :
    HooksVRInv MultiBucketVROk
      (hooksFSMultiBucketAuth L cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep true tL par la) where
  mono {_ _ v} hle hv := by
    cases v with
    | inl rs => exact hv.mono hle
    | inr _ => trivial
  startRecv_step ctx P t γ σ Tn h res hmem γ' σ' rsv hEq := by
    dsimp only [hooksFSMultiBucketAuth] at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      cases hEq
      split
      · exact Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
          ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
          (lChainPRG C.F) maxForwardJumps _
      · trivial
    · simp only [↓reduceIte] at hmem
      split_ifs at hmem <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
         subst hmem; cases hEq)
  fsRecv_step {k} _ _ _ rsv hdr e rec h res hVR hmem v' i' m' hEq := by
    cases rsv with
    | inl rs =>
      dsimp only [hooksFSMultiBucketAuth] at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      dsimp only at hEq
      cases hrec : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rs hdr e with
      | none => rw [hrec] at hEq; cases hEq
      | some o =>
        rw [hrec] at hEq
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hEq
        rcases hEq with ⟨rfl, rfl, rfl⟩
        exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
          ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
          (lChainPRG C.F) maxForwardJumps k hVR hrec).2
    | inr sIdx =>
      dsimp only [hooksFSMultiBucketAuth] at hmem
      simp only [StateT.run_bind, StateT.run_get, pure_bind, mem_support_bind_iff] at hmem
      rcases hmem with ⟨⟨ok, h1⟩, _, hmem⟩
      by_cases hok : (!ok) = true
      · simp [hok] at hmem; subst hmem; cases hEq
      · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
        rcases hmem with ⟨⟨rOut, h2⟩, _, hmem⟩
        rcases rOut with _ | (_ | ⟨idx', mo'⟩)
        · simp at hmem; subst hmem; cases hEq
        · simp at hmem; subst hmem; cases hEq
        · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
          split_ifs at hmem
          · simp [StateT.run_modify] at hmem; subst hmem; cases hEq
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
            rcases mo' with _ | m0
            · rcases rec with _ | r0
              · simp at hmem; subst hmem; cases hEq
              · simp at hmem; subst hmem; cases hEq; trivial
            · simp at hmem; subst hmem; cases hEq; trivial
  commit_vR _ _ _ new h res hmem new' hEq := by
    dsimp only [hooksFSMultiBucketAuth] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases hEq; rfl

private theorem vSend_multiBucket_fs_eq
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (s : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (m : LibsignalMsgPublicPart × Plain ℓ)
    (pair : Option ((LibsignalMsgPublicPart × Plain ℓ) × (LibsignalMsgPublicPart × Plain ℓ)))
    (r : Option CCoins) (hm : atomicShortPubB m.1 = true)
    (h : FSMultiBucketAuthState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32)) :
    (vSend (hooksFSMultiBucketAuth L cka prng (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        Δcka qep true tL par la) ctx P s m pair r).run h =
      (vSend (hooksFSMultiBucketAuth L cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        Δcka qep true tL par la) ctx P s m pair r).run h := by
  rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind]
  have hStep1 :
      vSendStep1 (hooksFSMultiBucketAuth L cka prng (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
          Δcka qep true tL par la) ctx P s r =
        vSendStep1 (hooksFSMultiBucketAuth L cka prng
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          Δcka qep true tL par la) ctx P s r := by
    unfold vSendStep1 hooksFSMultiBucketAuth fsClamp fsAtomicB lFS fromAEADPRG; rfl
  rw [hStep1]
  refine bind_congr fun ⟨s₁?, h₁⟩ => ?_
  rcases s₁? with _ | s₁
  · rfl
  · rcases hvS : s₁.vS with _ | (ss | sIdx)
    · simp only [hvS]
    · simp only [hvS, StateT.run_bind]
      dsimp only [hooksFSMultiBucketAuth, fsClamp]
      rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss (s₁.tcur, s₁.curCkaMsg) m hm]
    · simp only [hvS, StateT.run_bind]; rfl

private theorem vRecv_multiBucket_fs_eq
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 k Δcka qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (hB0 : (k + 1) * (maxForwardJumps + 1) ≤ B0)
    (ctx : Ctx Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (s : VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec_ : Option (Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h : FSMultiBucketAuthState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32))
    (hVR : ∀ t v, s.vR t = some v → MultiBucketVROk k v) :
    (vRecv (hooksFSMultiBucketAuth L cka prng (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        Δcka qep true tL par la) ctx P s c rec_).run h =
      (vRecv (hooksFSMultiBucketAuth L cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        Δcka qep true tL par la) ctx P s c rec_).run h := by
  have hVRHk := hooksFSMultiBucketAuth_main_vrInv_lFS L cka prng C ℓ encT idOf Δcka qep tL par la
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hStep1 :
        vRecvStep1 (hooksFSMultiBucketAuth L cka prng (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
            Δcka qep true tL par la) ctx P s c =
          vRecvStep1 (hooksFSMultiBucketAuth L cka prng
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
            Δcka qep true tL par la) ctx P s c := by
      unfold vRecvStep1 hooksFSMultiBucketAuth fsClamp fsAtomicB lFS fromAEADPRG; rfl
    rw [hStep1]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
    rcases s₁? with _ | (_ | s₁)
    · rfl
    · rfl
    · have hs₁VR : ∀ t v, s₁.vR t = some v → MultiBucketVROk k v := by
        unfold vRecvStep1 at hmem
        by_cases ht : c.1.1 = s.tcur + 1
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
              by_cases ht₀ : t₀ = s.tcur + 1
              · subst ht₀
                simp only [Function.update_self, Option.some.injEq] at hv₀; subst hv₀
                exact hVRHk.mono (Nat.zero_le k)
                  (hVRHk.startRecv_step ctx P (s.tcur + 1) s.γ s.root Tn h
                    (some (some (γ', σ', rsv)), h₁) hsr γ' σ' rsv rfl)
              · simp only [Function.update_of_ne ht₀] at hv₀
                exact hVR t₀ v₀ hv₀
        · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, _⟩; exact hVR
      rcases hvRc : s₁.vR c.1.1 with _ | (rs | sIdx)
      · simp [hvRc]
      · simp only [hvRc, StateT.run_bind]
        dsimp only [hooksFSMultiBucketAuth]
        rw [fsClamp_fsAtomicB_receive_eq_lFS C ℓ encT idOf B0 k hB0 (hs₁VR c.1.1 (.inl rs) hvRc)]
      · simp only [hvRc, StateT.run_bind]; rfl

private theorem implE_multiBucket_fs_eq
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 B_q q' Δcka qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP Γ Pt RSt (RatchetSenderState (BitVec 256) ⊕ ℕ)
      (RatchetReceiverState (BitVec 256) (BitVec 256) ⊕ ℕ))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSMultiBucketAuthState Pt RSt (BitVec 256) I (ℕ × LibsignalCiphertextWithSalt32)))
    (t : (CryptoGames.SM.spec (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
      (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) (.inr t) = false)
    (hVR : SMVRInv MultiBucketVROk B_q (q' + 1) es.g) :
    (implE (hooksFSMultiBucketAuth L cka prng (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        Δcka qep true tL par la) (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL) noDoomPolicy (.inr t)).run es =
      (implE (hooksFSMultiBucketAuth L cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        Δcka qep true tL par la) (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL) noDoomPolicy (.inr t)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE _ (2 + Δcka) qep noDoomPolicy (P, m, r)).run es =
      (transmitE _ (2 + Δcka) qep noDoomPolicy (P, m, r)).run es
    unfold transmitE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · have hm : atomicShortPubB m.1 = true :=
          badSendMsg_transmit_false (ok := fun x : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB x.1) hBad
        simp only [noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
        exact congrArg (· >>= _)
          (vSend_multiBucket_fs_eq L cka prng C ℓ encT idOf B0 Δcka qep tL par la s₁ P (s₁.st P) m none r hm es.h)
  · change (challE _ (2 + Δcka) qep (bucketAuthCfg Δcka tL) noDoomPolicy (P, m₀, m₁, r)).run es =
      (challE _ (2 + Δcka) qep (bucketAuthCfg Δcka tL) noDoomPolicy (P, m₀, m₁, r)).run es
    obtain ⟨hm₀, hm₁⟩ := badSendMsg_chall_false hBad
    have hm : atomicShortPubB (if es.g.b then m₁ else m₀).1 = true := by
      cases es.g.b <;> simp [hm₀, hm₁]
    unfold challE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · simp [bucketAuthCfg]
  · change (deliverE _ maxForwardJumps (bucketAuthCfg Δcka tL) (P, c)).run es =
      (deliverE _ maxForwardJumps (bucketAuthCfg Δcka tL) (P, c)).run es
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind,
          vRecv_multiBucket_fs_eq L cka prng C ℓ encT idOf B0 (B_q - (q' + 1)) Δcka qep tL par la
            hkB es.g P (es.g.st P) c (some r) es.h (hVR P)]
        refine bind_congr fun ⟨rv, h'⟩ => ?_
        rcases rv with _ | (_ | ⟨st', t', i', m'⟩)
        · rfl
        · rfl
        · dsimp only [commitE, _root_.CryptoGames.SM.Engine.liftH, hooksFSMultiBucketAuth]
  · change (injectE _ (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run es =
      (injectE _ (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run es
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        vRecv_multiBucket_fs_eq L cka prng C ℓ encT idOf B0 (B_q - (q' + 1)) Δcka qep tL par la
          hkB es.g P (es.g.st P) c none es.h (hVR P)]
      refine bind_congr fun ⟨rv, h'⟩ => ?_
      rcases rv with _ | (_ | ⟨st', t', i', m'⟩)
      · rfl
      · rfl
      · by_cases hq : qep + 1 < t'
        · simp [hq]
        · simp only [hq, ↓reduceIte]
          by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte]
            dsimp only [commitE, _root_.CryptoGames.SM.Engine.liftH, hooksFSMultiBucketAuth]
          · simp [htriv]
  · change (corrE _ noDoomPolicy P).run es = (corrE _ noDoomPolicy P).run es
    unfold corrE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · rfl
    · simp only [noDoomPolicy_leakDoom, noDoomPolicy_corrDoom, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte]
      dsimp only [_root_.CryptoGames.SM.Engine.liftH, hooksFSMultiBucketAuth]

theorem redFSAuthMultiBucket_main_atomic_eq
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
        true la tL par).eval (fun _ => A) ()) =
      redFSAuthMultiBucket (q + 1) (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep true la tL par A := by
  let _ : Inhabited Pt := ⟨0⟩
  rw [redFSAuthMultiBucketShallow_eval_eq ℓ Pt C Dh encPt encT idOf lam q B0 qep true la tL par A hq,
    redFSAuthMultiBucket_main_dhSchemeFb_eq]
  have hB0Le : (q + 1) * (maxForwardJumps + 1) ≤ B0 := by omega
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) q := by
    refine hq.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hSendOk : A.IsQueryBoundP
      (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true) 0 := by
    refine hsh.of_imp fun t ht => ?_
    rcases t with _ | ((((_ | _) | _) | _) | _) <;> exact ht
  let cka := dhScheme Dh
  let prng := rootPRNG C.F encPt
  let fs₁ := fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
  let fs₂ := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  unfold redFSAuthMultiBucket
  have hInitEq : initFSMultiBucketAuth (q + 1) cka prng fs₁ lam 1 qep true tL par =
      initFSMultiBucketAuth (q + 1) cka prng fs₂ lam 1 qep true tL par := by
    unfold initFSMultiBucketAuth fs₁ fs₂ fsClamp fsAtomicB lFS fromAEADPRG; rfl
  rw [hInitEq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨vA, vB⟩, h0⟩ hmem => ?_
  let es₀ : EState _ (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) _ :=
    { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h0 }
  have hInv₀ : SMEngineInv (q + 1) q q es₀.g ∧ SMVRInv MultiBucketVROk q q es₀.g := by
    unfold initFSMultiBucketAuth at hmem
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨kr, _, kc, _, ⟨⟨σ, kVal, sid⟩, h1⟩, _, hmem⟩ := hmem
    rcases Prod.mk.inj hmem.symm with ⟨hvp, rfl⟩
    rcases Prod.mk.inj hvp with ⟨rfl, rfl⟩
    refine ⟨SMEngineInv.init _ false le_rfl
      (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q)), fun P t v hv => ?_⟩
    cases P
    · change (if t = 0 then _ else none) = some v at hv
      by_cases ht0 : t = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv; subst hv
        simp only [Nat.sub_self]
        split
        · exact Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
            ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
            (lChainPRG C.F) maxForwardJumps kVal
        · trivial
      · simp only [ht0, ↓reduceIte] at hv; cases hv
    · cases hv
  have hVRHk := hooksFSMultiBucketAuth_main_vrInv_lFS (q + 1) cka prng C ℓ encT idOf 1 qep tL par la
  have hms1 : fs₁.maxSkip = maxForwardJumps := rfl
  have hms2 : fs₂.maxSkip = maxForwardJumps := rfl
  dsimp only
  rw [hms1, hms2]
  suffices hSim : ∀ (oa : SchemeAdversary (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        Pt (BitVec 256) (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (ℕ × LibsignalCiphertextWithSalt32))
      (rem : ℕ) (es : EState _ _ _ _) (we : Option ℕ),
      oa.IsQueryBoundP
        (isGameQuery (G := CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) rem →
      oa.IsQueryBoundP
        (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
          (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
          (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true) 0 →
      SMEngineInv (q + 1) q rem es.g →
      SMVRInv MultiBucketVROk q rem es.g →
      (simulateQ (implFSMultiBucketAuth (hooksFSMultiBucketAuth (q + 1) cka prng fs₁ 1 qep true tL par la)
          1 qep maxForwardJumps true tL) oa).run (es, we) =
        (simulateQ (implFSMultiBucketAuth (hooksFSMultiBucketAuth (q + 1) cka prng fs₂ 1 qep true tL par la)
          1 qep maxForwardJumps true tL) oa).run (es, we) by
    exact congrArg (· >>= _) (hSim A q _ none hA' hSendOk hInv₀.1 hInv₀.2)
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => intro rem es we _ _ _ _; simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    intro rem es we hoa hSend esInv esVR
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ :=
      badSendMsg_query_bind_step (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) qy mx hSend
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rw [implFSMultiBucketAuth_run_eq_implE, implFSMultiBucketAuth_run_eq_implE]
    simp only [bind_assoc, pure_bind]
    rcases qy with n | t_sm
    · simp only [isGameQuery, ↓reduceIte] at hmx
      have hInl1 : (implE (hooksFSMultiBucketAuth (q + 1) cka prng fs₁ 1 qep true tL par la)
          (2 + 1) qep maxForwardJumps (bucketAuthCfg 1 tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl2 : (implE (hooksFSMultiBucketAuth (q + 1) cka prng fs₂ 1 qep true tL par la)
          (2 + 1) qep maxForwardJumps (bucketAuthCfg 1 tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem' => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem'
      obtain ⟨_, _, _, rfl⟩ := hmem'
      exact ih u rem _ _ (hmx u) (hSendMx u) esInv esVR
    · simp only [isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < rem := hq0.resolve_left (by decide)
      obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
      rw [implE_multiBucket_fs_eq (q + 1) cka prng C ℓ encT idOf B0 q rem' 1 qep tL par la
        hB0Le es t_sm hBad esVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem' => ?_
      have hInv' := implE_inv
        (hooksFSMultiBucketAuth (q + 1) cka prng fs₂ 1 qep true tL par la)
        (bucketAuthCfg 1 tL) noDoomPolicy es t_sm esInv (u, es') hmem'
      have hVR' := implE_vrInv
        (hooksFSMultiBucketAuth (q + 1) cka prng fs₂ 1 qep true tL par la)
        hVRHk (bucketAuthCfg 1 tL) noDoomPolicy es t_sm esInv esVR (u, es') hmem'
      exact ih u rem' es' _ (by simpa using hmx u) (hSendMx u) hInv' hVR'

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopAtomic

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesCompilers -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
import Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed -- proof-setup: allow-public-import

/-!
# Decryption, Corrupt-Receiver, & `TwoModeMultiSessBounds` Assembly for `(tL, par)`-Bucket FS-AEAD

Proves `redFSAuthMultiBucketShallow_noCr`, `redFSAuthMultiBucketShallow_decQueries`, and
`redFSAuthMultiBucketProg_twoModeMultiSessBounds_of_parts` (parameterized over `hoff`, `hgs`, and
`hone` so sibling leaves compile in parallel).-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthTwoMode

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl (CostedReduction Comp Expr Env handlerImpl)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.FSAEAD (pubRedImpl RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.PRFPRNG (FSHdrTag prngSMCodec)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM.Construction (Header healEpoch fsaeadMultiHeaderAdIface)
open _root_.CryptoGames.SM.Engine (cGsTy vSendC vSendStep1C vRecvC vRecvStep1C commitEC
  deliverEC injectEC eval_bind eval_bind_ret)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks (PotOKInvFS potInvFS_ret
  potInvFS_ite potInvFS_caseOpt potInvFS_caseSum)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lPubOf)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (multiSessSpec sessOffRange onAnySess onSess)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec)
open _root_.CryptoVerification.E2E.Signed.SessionQueries (fsInjQ)
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries (fsEncBadAD fsOutsideClass shortOk
  multiInjectLong GuardedMultiInjectShort)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  atomicShortPubB_imp_shortB fsAtomicB)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.E2E.SessionAuthBridge (MultiSessPubFsAdv multiSessPubToAD
  TwoModeMultiSessBounds)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (redFSAuthMultiBucketProg
  hooksFSMultiBucketAuthC initFSMultiBucketAuthEStateC rootFSMultiBucketAuthC lookupMultiBucketFC
  fsMultiBucketAuthStartSendC fsMultiBucketAuthStartRecvC fsMultiBucketAuthFsSendC
  fsMultiBucketAuthFsRecvC fsMultiBucketAuthCommitC fsMultiBucketAuthRevealC rangeListBucketC)

/-- Shallow-ops instantiation of `BucketPRNGAuth.redFSAuthMultiBucketProg` over
`BundlesCompilers.fig8CkaOpsShallow` and `fsaeadMultiHeaderAdIface`. -/
@[expose] def redFSAuthMultiBucketShallow'
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool :=
  let _ : Inhabited Pt := ⟨0⟩
  redFSAuthMultiBucketProg L B0 1 qep maxForwardJumps gMain la tL par

section MultiBucketQueriesAndGen

open _root_.CryptoGames.PRFPRNG (prngSig prngOps)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (fsaeadMultiBucketIface)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (fsMultiBucketHsTy fsMultiBucketVpTy)

@[local simp] private theorem lookupMultiBucketFC_queries'
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
    {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}
    (L : ℕ) (w : FSHdrTag → ℕ) {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (hE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (@fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (tE : Expr _ Γ' .nat) (ikE : Expr _ Γ' (.base .i)) :
    (lookupMultiBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L hE tE ikE).queries w (fun _ => 0) = 0 := by
  simp [lookupMultiBucketFC, Comp.queries]

@[local simp] private theorem rootFSMultiBucketAuthC_queries'
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (L Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ)
    {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (hE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (@fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (tE : Expr _ Γ' .nat) (plE : Expr _ Γ' .bool)
    (ikE : Expr _ Γ' (.base .i)) (σE : Expr _ Γ' (.base .sig)) :
    (rootFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep tL par hE tE plE ikE σE).queries w
      (fun _ => 0) = 0 := by
  simp [rootFSMultiBucketAuthC, Comp.queries]

@[local simp] private theorem fsMultiBucketAuthStartSendC_queries'
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ)
    {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (hE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (@fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (ctxE : Expr _ Γ' (cGsTy (@fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (pE : Expr _ Γ' .bool) (tE : Expr _ Γ' .nat)
    (γE : Expr _ Γ' (.base .γ)) (σE : Expr _ Γ' (.base .sig))
    (rE : Expr _ Γ' (.opt (.base .ccoins))) :
    (fsMultiBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par hE ctxE pE tE γE σE rE).queries w
      (fun _ => 0) = 0 := by
  cases gMain <;> simp [fsMultiBucketAuthStartSendC, Comp.queries]

@[local simp] private theorem fsMultiBucketAuthStartRecvC_queries'
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ)
    {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (hE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (@fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (ctxE : Expr _ Γ' (cGsTy (@fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (pE : Expr _ Γ' .bool) (tE : Expr _ Γ' .nat)
    (γE : Expr _ Γ' (.base .γ)) (σE : Expr _ Γ' (.base .sig)) (tnE : Expr _ Γ' (.base .t)) :
    (fsMultiBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par hE ctxE pE tE γE σE tnE).queries w
      (fun _ => 0) = 0 := by
  cases gMain <;> simp [fsMultiBucketAuthStartRecvC, Comp.queries]

@[local simp] private theorem initFSMultiBucketAuthEStateC_queries'
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (L Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) (w : FSHdrTag → ℕ)
    {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (bE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' .bool) :
    (initFSMultiBucketAuthEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δcka qep gMain tL par bE).queries w (fun _ => 0) = 0 := by
  cases gMain <;> simp [initFSMultiBucketAuthEStateC, Comp.queries]

private abbrev wCr : FSHdrTag → ℕ
  | .cr => 1
  | _ => 0

private theorem redFSAuthMultiBucketProg_totalCrQueries_gen
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (q : ℕ) :
    (redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip gMain la tL par).totalQueries wCr (fun _ => 0) q = 0 := by
  simp only [CostedReduction.totalQueries, redFSAuthMultiBucketProg,
    initFSMultiBucketAuthEStateC_queries', Comp.queries, zero_add, add_zero]
  cases gMain <;> simp [hooksFSMultiBucketAuthC,
    vSendC, vSendStep1C, deliverEC, injectEC, vRecvC, vRecvStep1C, commitEC,
    fsMultiBucketAuthFsSendC, fsMultiBucketAuthFsRecvC,
    fsMultiBucketAuthCommitC, fsMultiBucketAuthRevealC, rangeListBucketC, Comp.queries, wCr]

attribute [local irreducible] redFSAuthMultiBucketProg in
private theorem redFSAuthMultiBucketShallow_totalCrQueries
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (q : ℕ) :
    (redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par).totalQueries
      wCr (fun _ => 0) q = 0 := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow', fig8CkaOpsShallow, CryptoGames.CKA.ckaSchemeOps]
  exact redFSAuthMultiBucketProg_totalCrQueries_gen L B0 1 qep maxForwardJumps gMain la tL par q

attribute [local irreducible] redFSAuthMultiBucketShallow' in
theorem redFSAuthMultiBucketShallow_noCr
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (q : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inr ⟨_, .inl (.inl (.inr _))⟩ => true
        | _ => false) = true) 0 := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) q := by
    refine hq.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have h := ReductionDsl.CostedReduction.queryBound_eval
    (redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par)
    (fun t => (match t with
      | .inr ⟨_, .inl (.inl (.inr _))⟩ => true
      | _ => false) = true)
    wCr (fun _ => 0)
    (fun g x hg => by cases g <;> simp_all [wCr])
    (fun n => by
      change OracleComp.IsQueryBoundP
        (liftM (OracleSpec.query
          (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ =>
            CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)))
          (.inl n))) _ 0
      rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun _ => by simp⟩)
    (fun _ => A) q (fun _ => hA') ()
  rwa [redFSAuthMultiBucketShallow_totalCrQueries] at h

private abbrev wDlIj : FSHdrTag → ℕ
  | .dl => 1
  | .ij => 1
  | _ => 0

private theorem redFSAuthMultiBucketProg_totalDecQueries_gen
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (q : ℕ) :
    (redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip gMain la tL par).totalQueries wDlIj (fun _ => 0) q ≤ q := by
  simp only [CostedReduction.totalQueries, redFSAuthMultiBucketProg,
    initFSMultiBucketAuthEStateC_queries', Comp.queries, zero_add, add_zero]
  conv_rhs => rw [← Nat.mul_one q]
  apply Nat.mul_le_mul_left q
  cases gMain <;> simp [hooksFSMultiBucketAuthC,
    vSendC, vSendStep1C, deliverEC, injectEC, vRecvC, vRecvStep1C, commitEC,
    fsMultiBucketAuthFsSendC, fsMultiBucketAuthFsRecvC,
    fsMultiBucketAuthCommitC, fsMultiBucketAuthRevealC, rangeListBucketC,
    Comp.queries, wDlIj]

attribute [local irreducible] redFSAuthMultiBucketProg in
private theorem redFSAuthMultiBucketShallow_totalDecQueries
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (q : ℕ) :
    (redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par).totalQueries
      wDlIj (fun _ => 0) q ≤ q := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow', fig8CkaOpsShallow, CryptoGames.CKA.ckaSchemeOps]
  exact redFSAuthMultiBucketProg_totalDecQueries_gen L B0 1 qep maxForwardJumps gMain la tL par q

attribute [local irreducible] redFSAuthMultiBucketShallow' in
theorem redFSAuthMultiBucketShallow_decQueries
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (idx q : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, qv⟩ => decide (s = idx) &&
            CryptoGames.FSAEAD.isDecQuery
              (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (.inr qv)) = true)
      q := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))) q := by
    refine hq.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have h := ReductionDsl.CostedReduction.queryBound_eval
    (redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par)
    (fun t => (match t with
      | .inl _ => false
      | .inr ⟨s, qv⟩ => decide (s = idx) &&
          CryptoGames.FSAEAD.isDecQuery
            (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (.inr qv)) = true)
    wDlIj (fun _ => 0)
    (fun g x hg => by cases g <;> simp_all [CryptoGames.FSAEAD.isDecQuery, wDlIj])
    (fun n => by
      change OracleComp.IsQueryBoundP
        (liftM (OracleSpec.query
          (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ =>
            CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)))
          (.inl n))) _ 0
      rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun _ => by simp⟩)
    (fun _ => A) q (fun _ => hA') ()
  exact h.mono (redFSAuthMultiBucketShallow_totalDecQueries ℓ Pt C Dh encPt encT idOf lam L B0 qep
    gMain la tL par q)

private theorem isQueryBoundP_sessOffRange_of_ge_zero {κ β : Type} {spec : OracleSpec.{0, 0} κ}
    (M : ℕ)
    (c : OracleComp (unifSpec + multiSessSpec spec) β)
    (h : ∀ idx ≥ M, c.IsQueryBoundP
      (fun t => (match t with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0) :
    c.IsQueryBoundP
      (fun t => sessOffRange M t = true) 0 := by
  induction c using OracleComp.inductionOn with
  | pure _ => simp
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff]
    simp only [Nat.zero_sub, ite_self]
    cases q with
    | inl _ =>
      refine ⟨Or.inl (by simp [sessOffRange]),
        fun u => ih u fun idx hidx => ?_⟩
      have hq := h idx hidx
      rw [isQueryBoundP_query_bind_iff] at hq
      simpa using hq.2 u
    | inr sq =>
      rcases sq with ⟨s, _⟩
      by_cases hs : M ≤ s
      · exfalso
        have hq := h s hs
        rw [isQueryBoundP_query_bind_iff] at hq
        simp at hq
      · refine ⟨Or.inl (by simp [sessOffRange, hs]),
          fun u => ih u fun idx hidx => ?_⟩
        have hq := h idx hidx
        rw [isQueryBoundP_query_bind_iff] at hq
        simpa using hq.2 u

private theorem isQueryBoundP_query_bind_pure_le_one {κ β : Type} {spec : OracleSpec.{0, 0} κ}
    {Q : spec.Domain → Prop} [DecidablePred Q] (q : spec.Domain) {f : spec.Range q → β} :
    OracleComp.IsQueryBoundP
      ((liftM (OracleSpec.query q) : OracleComp spec (spec.Range q)) >>= fun x => pure (f x)) Q 1 := by
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩

private theorem isQueryBoundP_query_bind_pure_zero_of_not {κ β : Type} {spec : OracleSpec.{0, 0} κ}
    {Q : spec.Domain → Prop} [DecidablePred Q] {q : spec.Domain} (hq : ¬ Q q)
    {f : spec.Range q → β} :
    OracleComp.IsQueryBoundP
      ((liftM (OracleSpec.query q) : OracleComp spec (spec.Range q)) >>= fun x => pure (f x)) Q 0 := by
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl hq, fun _ => by simp⟩

private theorem multiSessPubToAD_isQueryBoundP {Pt : Type} {ℓ : ℕ}
    (codec : SignalMessageProtoCodec)
    (P : (unifSpec + multiSessSpec
      (fsSpec (BitVec 256) (BitVec 256) (Header Pt)
        (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32)).Domain → Prop)
    [DecidablePred P]
    (Q : (unifSpec + multiSessSpec
      (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)).Domain → Prop)
    [DecidablePred Q]
    (hInl : ∀ u, ¬ P (.inl u) ∧ ¬ Q (.inl u))
    (hTr : ∀ s a pm,
      ¬ P (.inr ⟨s, .inl (.inl (.inl (.inl (.inl (a, pm)))))⟩) →
      ¬ Q (.inr ⟨s, .inl (.inl (.inl (.inl (.inl ((a, pm.1), pm.2)))))⟩))
    (hCh : ∀ s a pm₀ pm₁,
      ¬ P (.inr ⟨s, .inl (.inl (.inl (.inl (.inr (a, pm₀, pm₁)))))⟩) →
      ¬ Q (.inr ⟨s, .inl (.inl (.inl (.inl (.inr ((a, pm₀.1), pm₀.2, pm₁.2)))))⟩))
    (hCs : ∀ s u,
      ¬ P (.inr ⟨s, .inl (.inl (.inl (.inr u)))⟩) →
      ¬ Q (.inr ⟨s, .inl (.inl (.inl (.inr u)))⟩))
    (hCr : ∀ s u,
      ¬ P (.inr ⟨s, .inl (.inl (.inr u))⟩) →
      ¬ Q (.inr ⟨s, .inl (.inl (.inr u))⟩))
    (hDl : ∀ s a c p,
      ¬ P (.inr ⟨s, .inl (.inr (a, c))⟩) →
      ¬ Q (.inr ⟨s, .inl (.inr ((a, p), c))⟩))
    (hIj : ∀ s a c p,
      ¬ P (.inr ⟨s, .inr (a, c)⟩) →
      ¬ Q (.inr ⟨s, .inr ((a, p), c)⟩))
    {n : ℕ} (AdvPub : MultiSessPubFsAdv Pt ℓ) (hAdv : AdvPub.IsQueryBoundP P n) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP Q n := by
  unfold multiSessPubToAD
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  refine IsQueryBoundP.simulateQ_run_of_step hAdv ?_ ?_ (fun _ => false)
  · rintro (u | ⟨s, o⟩) hp st
    · exact absurd hp (hInl u).1
    · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.transmitQuery, StateT.run_lift,
          simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
        exact isQueryBoundP_query_bind_pure_le_one _
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.challengeQuery, StateT.run_lift,
          simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
        exact isQueryBoundP_query_bind_pure_le_one _
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.corruptSenderQuery, StateT.run_lift,
          simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
        exact isQueryBoundP_query_bind_pure_le_one _
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.corruptReceiverQuery,
          StateT.run_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
        apply (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        refine ⟨Or.inr Nat.zero_lt_one, fun r => ?_⟩
        cases r <;> simp [StateT.run_pure, StateT.run_set]
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.deliverQuery]
        cases lPubOf codec c.2 with
        | none => simp [StateT.run_pure]
        | some p =>
          simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
          exact isQueryBoundP_query_bind_pure_le_one _
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.injectQuery]
        cases lPubOf codec c.2 with
        | none => simp [StateT.run_get]
        | some p =>
          simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
          exact isQueryBoundP_query_bind_pure_le_one _
  · rintro (u | ⟨s, o⟩) hnp st
    · simp only [StateT.run_lift]
      exact isQueryBoundP_query_bind_pure_zero_of_not (hInl u).2
    · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.transmitQuery, StateT.run_lift,
          simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
        exact isQueryBoundP_query_bind_pure_zero_of_not (hTr s a pm hnp)
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.challengeQuery, StateT.run_lift,
          simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
        exact isQueryBoundP_query_bind_pure_zero_of_not (hCh s a pm₀ pm₁ hnp)
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.corruptSenderQuery, StateT.run_lift,
          simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
        exact isQueryBoundP_query_bind_pure_zero_of_not (hCs s u hnp)
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.corruptReceiverQuery,
          StateT.run_bind, StateT.run_lift, simulateQ_bind, bind_assoc]
        apply (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        refine ⟨Or.inl (hCr s u hnp), fun r => ?_⟩
        cases r <;> simp [StateT.run_pure, StateT.run_set]
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.deliverQuery]
        cases lPubOf codec c.2 with
        | none => simp [StateT.run_pure]
        | some p =>
          simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
          exact isQueryBoundP_query_bind_pure_zero_of_not (hDl s a c p hnp)
      · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.injectQuery]
        cases lPubOf codec c.2 with
        | none => simp [StateT.run_get]
        | some p =>
          simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
          exact isQueryBoundP_query_bind_pure_zero_of_not (hIj s a c p hnp)

private def fsEncBadGen {SS RS AD M C : Type} (ok : M → Bool) :
    (CryptoGames.FSAEAD.spec SS RS AD M C).Domain → Bool
  | .inl (.inl (.inl (.inl (.inl ⟨_, m⟩)))) => !ok m
  | .inl (.inl (.inl (.inl (.inr ⟨_, m₀, m₁⟩)))) => !ok m₀ || !ok m₁
  | _ => false

private abbrev fsEncBadPub (Pt : Type) {ℓ : ℕ}
    (ok : LibsignalMsgPublicPart × Plain ℓ → Bool) :
    (CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Domain → Bool :=
  fsEncBadGen ok

private def fsInjGen {SS RS AD M C : Type} :
    (CryptoGames.FSAEAD.spec SS RS AD M C).Domain → Bool
  | .inr _ => true
  | _ => false

section MultiBucketGen

open _root_.CryptoGames.PRFPRNG (prngSig prngOps)
open _root_.CryptoGames.SM.Construction (PartyState)

variable
  {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

private abbrev fsInjPred {SS RS T M E : Type} :
    (unifSpec + OracleSpec.sigma
      (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Domain → Prop :=
  fun t => (match t with | .inl _ => false | .inr ⟨_, o⟩ => fsInjGen o) = true

private theorem redFSAuthMultiBucketProg_decBound_gen
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (q : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      fsInjPred q := by
  let R := redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka qep maxSkip gMain la tL par
  let qW : FSHdrTag → ℕ := fun | .ij => 1 | _ => 0
  have hraw := CostedReduction.queryBound_eval R
    fsInjPred
    qW (fun _ => 0)
    (fun g _ hP => by cases g <;> simp [qW, fsInjPred, fsInjGen] at hP ⊢)
    (fun n => by
      change OracleComp.IsQueryBoundP
        ((liftM (OracleSpec.query (spec := unifSpec + OracleSpec.sigma
          (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)) (.inl n)) : OracleComp _ _) >>=
          fun x => pure x) _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun _ => by simp⟩)
    (fun _ => A) q
    (fun _ => hq.of_imp (fun x hx => by cases x <;> [cases hx; rfl])) ()
  refine hraw.mono ?_
  have hInit : R.init.queries qW (fun _ => 0) = 0 := by
    simp [R, redFSAuthMultiBucketProg, Comp.queries]
  have hFin : R.finish.queries qW (fun _ => 0) = 0 := by
    simp [R, redFSAuthMultiBucketProg, Comp.queries]
  have hHdl : R.handle.queries qW (fun _ => 0) ≤ 1 := by
    cases gMain <;> simp [R, redFSAuthMultiBucketProg, hooksFSMultiBucketAuthC,
      vSendC, vSendStep1C, deliverEC, injectEC, vRecvC, vRecvStep1C, commitEC,
      fsMultiBucketAuthFsSendC, fsMultiBucketAuthFsRecvC,
      fsMultiBucketAuthCommitC, fsMultiBucketAuthRevealC, rangeListBucketC, Comp.queries, qW]
  have hmul : q * R.handle.queries qW (fun _ => 0) ≤ q * 1 := Nat.mul_le_mul_left q hHdl
  unfold CostedReduction.totalQueries
  omega

private abbrev encBadPred {SS RS T M E : Type} (ok : M → Bool) :
    (unifSpec + OracleSpec.sigma
      (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Domain → Prop :=
  fun t => (match t with | .inl _ => false | .inr ⟨_, o⟩ => fsEncBadGen ok o) = true

private abbrev qWEncBad : FSHdrTag → ℕ
  | .tr => 1
  | .ch => 1
  | _ => 0

private theorem multiIface_fwdU_encBad_zero (ok : M → Bool) (n : ℕ) :
    ((@fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK).fwdU n).IsQueryBoundP
      (encBadPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) ok) 0 := by
  change OracleComp.IsQueryBoundP
    ((liftM (OracleSpec.query (spec := unifSpec + OracleSpec.sigma
      (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)) (.inl n)) : OracleComp _ _) >>=
      fun x => pure x) (encBadPred ok) 0
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [encBadPred]), fun _ => by simp⟩

private theorem multiIface_encBad_le_qW (ok : M → Bool) (g : FSHdrTag)
    (a : ((@fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).dom g).denote)
    (hP : encBadPred ok ((@fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).enc g a)) :
    1 ≤ qWEncBad g := by
  cases g <;> simp [encBadPred, qWEncBad, fsEncBadGen] at hP ⊢

private theorem comp_encBad_zero (ok : M → Bool)
    {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    {τ : _root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E)}
    (c : Comp
      (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (@fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK) Γ' τ)
    (ρ : Env Γ') (hz : c.queries qWEncBad (fun _ => 0) = 0) :
    (c.eval ρ).IsQueryBoundP (encBadPred ok) 0 :=
  (Comp.queryBound_eval (encBadPred ok) qWEncBad (fun _ => 0)
    (multiIface_encBad_le_qW ok) (multiIface_fwdU_encBad_zero ok) c ρ).mono (by omega)

private theorem potInvFS_encBad_zero (ok : M → Bool)
    {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    {τ : _root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E)}
    (c : Comp
      (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (@fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK) Γ' τ)
    (ρ : Env Γ') (hz : c.queries qWEncBad (fun _ => 0) = 0) :
    Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS
      (encBadPred ok) (fun _ => True) (fun _ => 0) (c.eval ρ) 0 :=
  ⟨fun _ hk => (isQueryBoundP_bind (comp_encBad_zero (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) ok c ρ hz)
    fun a _ => hk a trivial).mono (Nat.le_refl 0)⟩

private theorem eval_query_isQueryBoundP_zero' {S : _root_.ReductionDsl.Sig} {O : _root_.ReductionDsl.Ops S}
    {ι : Type} {T' : OracleSpec.{0, 0} ι} {I : _root_.ReductionDsl.Iface S T'}
    {Γ' : List (_root_.ReductionDsl.Ty S)} (g : I.Tag) (e : Expr O Γ' (I.dom g))
    (ρ : Env Γ') (P : ι → Prop) [DecidablePred P]
    (h : ¬ P (I.enc g (e.eval ρ))) :
    ((Comp.query (I := I) g e).eval ρ).IsQueryBoundP P 0 := by
  dsimp only [Comp.eval]
  rw [map_eq_bind_pure_comp, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl h, fun _ => by simp⟩

private theorem potInvFS_tr_shortAD (ok : M → Bool)
    {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (argE : Expr
      (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      ((fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK).dom .tr))
    (ρ : Env Γ')
    (hok' : ok (argE.eval ρ).2.2 = true) :
    PotOKInvFS
      (encBadPred ok) (fun _ => True) (fun _ => 0)
      ((Comp.query (I := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK) FSHdrTag.tr argE).eval ρ) 0 := by
  refine ⟨fun k hk => ?_⟩
  have hQ0 := eval_query_isQueryBoundP_zero'
    (I := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK)
    FSHdrTag.tr argE ρ (encBadPred ok)
    (by simp [fsaeadMultiHeaderAdIface, encBadPred, fsEncBadGen, hok'])
  exact (isQueryBoundP_bind hQ0 (fun a _ => hk a trivial)).mono (Nat.le_refl 0)

private theorem vSendC_shortAD_gen
    (L B Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    {ok : M → Bool} {Γ' : List (_root_.ReductionDsl.Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E))}
    (eH : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eG : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (_root_.CryptoGames.SM.Engine.cGsTy
        (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (eP : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' .bool)
    (eVp : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eM : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' (.base .msg))
    (eCh : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (eR : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ')
    (hOk : ok (eM.eval ρ) = true)
    (hCh : eCh.eval ρ = none) :
    Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS
      (encBadPred ok) (fun _ => True) (fun _ => 0)
      ((_root_.CryptoGames.SM.Engine.vSendC
        (hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
          L B Δcka qep gMain tL par la)
        eH eG eP eVp eM eCh eR).eval ρ) 0 := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  refine PotOKInvFS.bindPot
    (potInvFS_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) ok _ _
      (by simp [vSendStep1C, hooksFSMultiBucketAuthC, Comp.queries]))
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (Nat.le_refl 0))
      (fun _ _ => potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial (Nat.le_refl 0))
        (fun _ _ => ?_)))
  dsimp only [hooksFSMultiBucketAuthC]; rw [eval_bind]
  refine PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => 0) ?_
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (Nat.le_refl 0))
      (fun _ _ => potInvFS_ret trivial (Nat.le_refl 0)))
  unfold fsMultiBucketAuthFsSendC; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => potInvFS_ret trivial (Nat.le_refl 0)) (fun _ _ => ?_)
  rw [eval_bind]
  refine PotOKInvFS.bindPot
    (potInvFS_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) ok _ _ (by simp [Comp.queries, qWEncBad]))
    (fun _ _ => ?_)
  refine potInvFS_ite (fun _ => potInvFS_ret trivial (Nat.le_refl 0)) (fun _ => ?_)
  rw [eval_bind]
  refine PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => 0) ?_
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (Nat.le_refl 0))
      (fun _ _ => potInvFS_ret trivial (Nat.le_refl 0)))
  refine potInvFS_caseOpt
    (fun _ => potInvFS_tr_shortAD (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) ok _ _ (by
        simp [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
          Env.get_cons_zero, Env.get_cons_succ, hOk]))
    (fun _ hsome => by
      simp [Expr.eval, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hCh] at hsome)

private theorem redFSAuthMultiBucketProg_shortAD_gen
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    {okB ok : M → Bool} (hok : ∀ m, okB m = true → ok m = true)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk okB A) :
    ((redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (encBadPred ok) 0 := by
  let R := redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka qep maxSkip gMain la tL par
  change (R.init.eval (.cons () .nil) >>= fun (a, s0) =>
      (simulateQ (handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E) R.handle) A).run s0 >>=
        fun (bOut, sOut) => R.finish.eval (.cons sOut (.cons bOut .nil))).IsQueryBoundP (encBadPred ok) 0
  refine (isQueryBoundP_bind
    (comp_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) ok R.init (.cons () .nil) (by
      simp [R, redFSAuthMultiBucketProg, Comp.queries]))
    fun ⟨_, s0⟩ _ => ?_).mono (Nat.zero_add 0).le
  refine (isQueryBoundP_bind ?_ fun ⟨bOut, sOut⟩ _ =>
    comp_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) ok R.finish (.cons sOut (.cons bOut .nil))
      (by simp [R, redFSAuthMultiBucketProg, Comp.queries])).mono (Nat.add_zero 0).le
  refine IsQueryBoundP.simulateQ_run_of_step hsh ?_ ?_ s0
  · rintro (u | gq) hp st
    · simp [CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.badSendMsg] at hp
    · let qv := (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc gq
      change (do
        let p ← R.handle.eval (.cons st (.cons qv .nil))
        pure ((prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec gq p.1, p.2)).IsQueryBoundP (encBadPred ok) 1
      refine (isQueryBoundP_bind (m := 0)
        (Comp.queryBound_eval (encBadPred ok) qWEncBad (fun _ => 0)
          (multiIface_encBad_le_qW ok) (multiIface_fwdU_encBad_zero ok)
          R.handle (.cons st (.cons qv .nil)))
        fun _ _ => by simp).mono ?_
      cases gMain <;> simp [R, redFSAuthMultiBucketProg, hooksFSMultiBucketAuthC,
        vSendC, vSendStep1C, deliverEC, injectEC, vRecvC, vRecvStep1C, commitEC,
        fsMultiBucketAuthFsSendC, fsMultiBucketAuthFsRecvC,
        fsMultiBucketAuthCommitC, fsMultiBucketAuthRevealC, rangeListBucketC, Comp.queries, qWEncBad]
  · rintro (u | gq) hnp st
    · exact (isQueryBoundP_bind (n := 0) (m := 0)
        (multiIface_fwdU_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) ok u)
        fun _ _ => by simp).mono (Nat.zero_add 0).le
    · let qv := (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc gq
      change (do
        let p ← R.handle.eval (.cons st (.cons qv .nil))
        pure ((prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec gq p.1, p.2)).IsQueryBoundP (encBadPred ok) 0
      refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => by simp).mono (Nat.add_zero 0).le
      suffices hPot : PotOKInvFS (encBadPred ok) (fun _ => True) (fun _ => 0)
          (R.handle.eval (.cons st (.cons qv .nil))) 0 by
        simpa [bind_pure] using hPot.run (fun x => pure x) (fun _ _ => by simp)
      dsimp only [R, redFSAuthMultiBucketProg]
      rw [eval_bind_ret]
      refine potInvFS_caseSum (fun _ h1 => ?_) (fun _ _ => ?_)
      · refine potInvFS_caseSum (fun _ h2 => ?_) (fun _ _ => ?_)
        · refine potInvFS_caseSum (fun _ h3 => ?_) (fun _ _ => ?_)
          · refine potInvFS_caseSum (fun x h4 => ?_) (fun _ _ => potInvFS_ret trivial (Nat.le_refl 0))
            have hxOk : ok x.2.1 = true := by
              simp only [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero] at h1 h2 h3 h4
              dsimp only [qv, prngSMCodec] at h1
              rcases gq with (((⟨p0, m0, r0⟩ | ⟨p0, m0, m1, r0⟩) | ⟨p0, hc⟩) | ⟨p0, hc⟩) | p0
              · injection h1 with h1'; subst h1'
                injection h2 with h2'; subst h2'
                injection h3 with h3'; subst h3'
                injection h4 with h4'; subst h4'
                exact hok m0 (by simpa [CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.badSendMsg] using hnp)
              · injection h1 with h1'; subst h1'
                injection h2 with h2'; subst h2'
                injection h3 with h3'; subst h3'
                cases h4
              · injection h1 with h1'; subst h1'
                injection h2 with h2'; subst h2'
                cases h3
              · injection h1 with h1'; subst h1'
                cases h2
              · cases h1
            rw [eval_bind_ret]
            refine potInvFS_ite (fun _ => potInvFS_ret trivial (Nat.le_refl 0))
              (fun _ => potInvFS_caseOpt (fun _ => potInvFS_ret trivial (Nat.le_refl 0)) (fun _ _ => ?_))
            rw [eval_bind]
            refine PotOKInvFS.bindPot
              (vSendC_shortAD_gen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
                (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                L B Δcka qep gMain la tL par _ _ _ _ _ _ _ _
                (by simpa [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] using hxOk)
                (by simp [Expr.eval]))
              (fun _ _ => potInvFS_caseOpt
                (fun _ => potInvFS_ret trivial (Nat.le_refl 0))
                (fun _ _ => potInvFS_ret trivial (Nat.le_refl 0)))
          · exact potInvFS_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) ok _ _
              (by simp [deliverEC, vRecvC, vRecvStep1C, commitEC, hooksFSMultiBucketAuthC,
                fsMultiBucketAuthFsRecvC, fsMultiBucketAuthCommitC, Comp.queries, qWEncBad])
        · exact potInvFS_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) ok _ _
            (by simp [injectEC, vRecvC, vRecvStep1C, commitEC, hooksFSMultiBucketAuthC,
              fsMultiBucketAuthFsRecvC, fsMultiBucketAuthCommitC, Comp.queries, qWEncBad])
      · exact potInvFS_encBad_zero (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) ok _ _
          (by simp [fsMultiBucketAuthRevealC, rangeListBucketC, Comp.queries, qWEncBad])

end MultiBucketGen

end MultiBucketQueriesAndGen

attribute [local irreducible] redFSAuthMultiBucketProg in
private theorem redFSAuthMultiBucketShallow_decBound_pub
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
        gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP fsInjPred q := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow', fig8CkaOpsShallow, CryptoGames.CKA.ckaSchemeOps]
  exact redFSAuthMultiBucketProg_decBound_gen (q + 1) B0 1 qep maxForwardJumps gMain la tL par q A hq

attribute [local irreducible] redFSAuthMultiBucketProg in
private theorem redFSAuthMultiBucketShallow_shortAD_pub
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
        gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (encBadPred (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)) 0 := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow', fig8CkaOpsShallow, CryptoGames.CKA.ckaSchemeOps]
  exact redFSAuthMultiBucketProg_shortAD_gen
    (q + 1) B0 1 qep maxForwardJumps gMain la tL par
    (fun _ hm => atomicShortPubB_imp_shortB hm) A hsh

private theorem multiSessPubToAD_offRange {Pt : Type} {ℓ : ℕ}
    (codec : SignalMessageProtoCodec) {M : ℕ} (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (h : ∀ idx ≥ M, AdvPub.IsQueryBoundP
      (fun t => (match t with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP (fun t => sessOffRange M t = true) 0 :=
  multiSessPubToAD_isQueryBoundP codec
    (fun t => sessOffRange M t = true) (fun t => sessOffRange M t = true)
    (fun _ => ⟨by simp [sessOffRange], by simp [sessOffRange]⟩)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hp => hp) (fun _ _ hp => hp) (fun _ _ hp => hp)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ hp => hp) AdvPub
    (isQueryBoundP_sessOffRange_of_ge_zero M AdvPub
      (fun idx hidx => (h idx hidx).of_imp fun x hx => by
        rcases x with _ | ⟨_, _⟩ <;> exact hx))

private theorem multiSessPubToAD_decBound {Pt : Type} {ℓ : ℕ}
    (codec : SignalMessageProtoCodec) {qd : ℕ} (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (h : AdvPub.IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd :=
  multiSessPubToAD_isQueryBoundP codec
    (fun t => onAnySess fsInjQ t = true) (fun t => onAnySess fsInjQ t = true)
    (fun _ => ⟨by simp [onAnySess], by simp [onAnySess]⟩)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hp => hp) (fun _ _ hp => hp) (fun _ _ hp => hp)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ hp => hp) AdvPub h

private theorem multiSessPubToAD_shortAD {Pt : Type} {ℓ : ℕ}
    (codec : SignalMessageProtoCodec) (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (h : AdvPub.IsQueryBoundP
      (fun t => onAnySess (fsEncBadPub Pt (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)) t = true) 0) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP (fun t => onAnySess (fsEncBadAD shortOk) t = true) 0 :=
  multiSessPubToAD_isQueryBoundP codec
    (fun t => onAnySess (fsEncBadPub Pt (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)) t = true)
    (fun t => onAnySess (fsEncBadAD shortOk) t = true)
    (fun _ => ⟨by simp [onAnySess], by simp [onAnySess]⟩)
    (fun _ _ _ hp => hp)
    (fun _ _ pm₀ pm₁ hp hq => hp (by
      simp only [onAnySess, fsEncBadAD, shortOk, CryptoGames.FSAEAD.encBadAD] at hq
      simp [onAnySess, fsEncBadPub, fsEncBadGen, hq]))
    (fun _ _ _ hq => by simp [onAnySess, fsEncBadAD, CryptoGames.FSAEAD.encBadAD] at hq)
    (fun _ _ _ hq => by simp [onAnySess, fsEncBadAD, CryptoGames.FSAEAD.encBadAD] at hq)
    (fun _ _ _ _ _ hq => by simp [onAnySess, fsEncBadAD, CryptoGames.FSAEAD.encBadAD] at hq)
    (fun _ _ _ _ _ hq => by simp [onAnySess, fsEncBadAD, CryptoGames.FSAEAD.encBadAD] at hq)
    AdvPub h

private theorem multiSessPubToAD_oneADClass {Pt : Type} {ℓ : ℕ}
    (codec : SignalMessageProtoCodec) {j k₀ : ℕ} (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (h : AdvPub.IsQueryBoundP
      (fun t => onSess (fsOutsideClass (fun h : Header Pt => h.1) k₀) j t = true) 0) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP
      (fun t => onSess (fsOutsideClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0 :=
  multiSessPubToAD_isQueryBoundP codec
    (fun t => onSess (fsOutsideClass (fun h : Header Pt => h.1) k₀) j t = true)
    (fun t => onSess (fsOutsideClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true)
    (fun _ => ⟨by simp [onSess], by simp [onSess]⟩)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hp => hp) (fun _ _ hp => hp) (fun _ _ hp => hp)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ hp => hp) AdvPub h

set_option linter.unusedSimpArgs false in
private theorem multiSessPubToAD_guardedShort {Pt : Type} {ℓ : ℕ}
    (codec : SignalMessageProtoCodec) (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (hAdv : GuardedMultiInjectShort AdvPub) :
    GuardedMultiInjectShort (multiSessPubToAD codec AdvPub) := by
  unfold multiSessPubToAD GuardedMultiInjectShort
  rw [StateT.run'_eq]
  refine CryptoGames.GuardedSafe.GuardedSafePost.map (P := fun _ => True) Prod.fst ?_ (fun _ _ => trivial)
  refine CryptoGames.GuardedSafe.GuardedSafePost.simulateQ_run (I := fun _ : ℕ → Bool => True) hAdv ?_ trivial
  rintro (u | ⟨s, o⟩) ht st _
  · simp only [StateT.run_lift]
    exact (CryptoGames.GuardedSafe.GuardedSafePost.query (by simp [multiInjectLong])).bind fun a ha =>
      CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨ha, trivial⟩
  · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, i, e⟩
    · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.transmitQuery, StateT.run_lift,
        simulateQ_bind, simulateQ_query, simulateQ_pure, bind_assoc, pure_bind]
      exact (CryptoGames.GuardedSafe.GuardedSafePost.query
        (by simp [multiInjectLong, CryptoGames.Ratchet.LibsignalInst.fsInjectLong])).bind fun r hr =>
        CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨hr, trivial⟩
    · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.challengeQuery, StateT.run_lift,
        simulateQ_bind, simulateQ_query, simulateQ_pure, bind_assoc, pure_bind]
      exact (CryptoGames.GuardedSafe.GuardedSafePost.query
        (by simp [multiInjectLong, CryptoGames.Ratchet.LibsignalInst.fsInjectLong])).bind fun r hr =>
        CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨hr, trivial⟩
    · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.corruptSenderQuery, StateT.run_lift,
        simulateQ_bind, simulateQ_query, simulateQ_pure, bind_assoc, pure_bind]
      exact (CryptoGames.GuardedSafe.GuardedSafePost.query
        (by simp [multiInjectLong, CryptoGames.Ratchet.LibsignalInst.fsInjectLong])).bind fun r hr =>
        CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨hr, trivial⟩
    · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.corruptReceiverQuery,
        StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_query, bind_assoc]
      refine (CryptoGames.GuardedSafe.GuardedSafePost.query
        (by simp [multiInjectLong, CryptoGames.Ratchet.LibsignalInst.fsInjectLong])).bind fun r _ => ?_
      cases r <;> simp only [Option.isSome, Bool.true_eq_false, ↓reduceIte, StateT.run_pure,
        StateT.run_set, simulateQ_pure, pure_bind] <;>
        exact CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩
    · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.deliverQuery]
      cases lPubOf codec c.2 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure, pure_bind]
        exact CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩
      | some p =>
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, simulateQ_bind,
          simulateQ_query, simulateQ_pure, bind_assoc, pure_bind]
        exact (CryptoGames.GuardedSafe.GuardedSafePost.query
          (by simp [multiInjectLong, CryptoGames.Ratchet.LibsignalInst.fsInjectLong])).bind fun _ _ =>
          CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩
    · simp only [pubRedImpl, StateT.run_mk, CryptoGames.FSAEAD.injectQuery]
      cases lPubOf codec e with
      | none =>
        simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure, pure_bind]
        exact CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩
      | some p =>
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, simulateQ_bind,
          simulateQ_query, simulateQ_pure, bind_assoc, pure_bind]
        exact (CryptoGames.GuardedSafe.GuardedSafePost.query
          (by simpa [multiInjectLong, CryptoGames.Ratchet.LibsignalInst.fsInjectLong] using ht)).bind
          fun _ _ => CryptoGames.GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩

private abbrev RawMultiPubFsAdv (Pt : Type) (ℓ : ℕ) : Type :=
  OracleComp (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
    CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))) Bool

private def multiRespShortRaw {SS RS AD Msg : Type} :
    (t : (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
      CryptoGames.FSAEAD.spec SS RS AD Msg (ℕ × LibsignalCiphertextWithSalt32))).Domain) →
    (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
      CryptoGames.FSAEAD.spec SS RS AD Msg (ℕ × LibsignalCiphertextWithSalt32))).Range t → Prop
  | .inr ⟨_, o⟩, r =>
      CryptoGames.Ratchet.LibsignalInst.fsRespShort (SS := SS) (RS := RS) (AD := AD) (Msg := Msg) (.inr o) r
  | .inl _, _ => True

private def multiInjectLongRaw {SS RS AD Msg : Type} :
    (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
      CryptoGames.FSAEAD.spec SS RS AD Msg (ℕ × LibsignalCiphertextWithSalt32))).Domain → Prop
  | .inr ⟨_, o⟩ =>
      CryptoGames.Ratchet.LibsignalInst.fsInjectLong (SS := SS) (RS := RS) (AD := AD) (Msg := Msg) (.inr o)
  | .inl _ => False

private theorem guardedMultiInjectShort_of_raw {Pt : Type} {ℓ : ℕ}
    (c : RawMultiPubFsAdv Pt ℓ)
    (h : CryptoGames.GuardedSafe.GuardedSafePost multiRespShortRaw multiInjectLongRaw (fun _ => True) c) :
    GuardedMultiInjectShort c := by
  induction h with
  | pure _ => exact CryptoGames.GuardedSafe.GuardedSafePost.pure trivial
  | @query_bind q _ hnb _ ih =>
    rcases q with u | ⟨s, ((((_ | _) | _) | _) | _) | ⟨_, _, _⟩⟩ <;>
      exact CryptoGames.GuardedSafe.GuardedSafePost.query_bind hnb fun r hr => ih r hr

attribute [local irreducible] redFSAuthMultiBucketShallow' in
/-- `TwoModeMultiSessBounds` assembly for `multiSessPubToAD` over `redFSAuthMultiBucketShallow'`
parameterized over `hoff`, `hgs`, and `hone`. -/
theorem redFSAuthMultiBucketProg_twoModeMultiSessBounds_of_parts
    {α : Type}
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (lam : α → Pt)
    (q B0 qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : α → OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hsh : ∀ o,
      CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o))
    (hoff : ∀ la o idx, idx ≥ ((qep + 2) - healEpoch tL) * (q + 1) →
      ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
          gMain la tL par).eval (fun _ => A o) ()).IsQueryBoundP
        (fun t => (match t with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0)
    (hgs : ∀ la o, GuardedMultiInjectShort
      ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
          gMain la tL par).eval (fun _ => A o) ()))
    (hone : ∀ la j o, ∃ k₀ : ℕ,
      ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
          gMain la tL par).eval (fun _ => A o) ()).IsQueryBoundP
        (fun t => (match t with
          | .inl _ => false
          | .inr ⟨s', o'⟩ =>
            decide (s' = j) &&
              CryptoGames.FSAEAD.queryADOutsideClass (SS := RatchetSenderState (BitVec 256))
                (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                (fun h : Header Pt => h.1) k₀ (.inr o')) = true) 0) :
    TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2))
      (((qep + 2) - healEpoch tL) * (q + 1)) q
      (fun la o =>
        multiSessPubToAD protoSignalCodec
          ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
              gMain la tL par).eval (fun _ => A o) ())) where
  offRange la o := multiSessPubToAD_offRange protoSignalCodec
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
      gMain la tL par).eval (fun _ => A o) ())
    (fun idx hidx => (hoff la o idx hidx).of_imp fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx)
  decBound la o := multiSessPubToAD_decBound protoSignalCodec
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
      gMain la tL par).eval (fun _ => A o) ())
    ((redFSAuthMultiBucketShallow_decBound_pub ℓ Pt C Dh encPt encT (idOf o) (lam o) q B0 qep
      gMain la tL par (A o) (hq o)).of_imp fun x hx => by
      rcases x with _ | ⟨_, ((((_ | _) | _) | _) | _) | _⟩ <;> exact hx)
  shortAD la o := multiSessPubToAD_shortAD protoSignalCodec
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
      gMain la tL par).eval (fun _ => A o) ())
    ((redFSAuthMultiBucketShallow_shortAD_pub ℓ Pt C Dh encPt encT (idOf o) (lam o) q B0 qep
      gMain la tL par (A o) (hsh o)).of_imp fun x hx => by
      rcases x with _ | ⟨_, ((((_ | _) | _) | _) | _) | _⟩ <;> exact hx)
  guardedShort la o := multiSessPubToAD_guardedShort protoSignalCodec
    ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
      gMain la tL par).eval (fun _ => A o) ())
    (hgs la o)
  oneADClass la j o :=
    let ⟨k₀, hk₀⟩ := hone la j o
    ⟨k₀, multiSessPubToAD_oneADClass protoSignalCodec
      ((redFSAuthMultiBucketShallow' ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
        gMain la tL par).eval (fun _ => A o) ())
      (hk₀.of_imp fun x hx => by
        rcases x with _ | ⟨s', ((((_ | _) | _) | _) | _) | _⟩
        · cases hx
        all_goals simp only [onSess, fsOutsideClass, CryptoGames.FSAEAD.queryADOutsideClass] at hx; exact hx)⟩

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthTwoMode

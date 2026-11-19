/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.RedCKA -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Notation
public import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesEval -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.QuerySubsumes
public import Computational.Proofs.CryptoGames.SM.Theorem12 -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SignedCoin -- proof-setup: allow-public-import

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open scoped Computational.Proofs.ReductionDsl.Notation
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesEval (fsAtomicB_receive_rsReach)
open CryptoVerification.E2E.Signed (advAvg ckaBranch_avg)

open scoped ENNReal
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree simulateQ_implE_localFs_eq)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun ckaIface ckaOps ckaPsEnc ckaSamplers ckaSig)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.SM (isSomeE ite_eval leN leN_eval letE_eval pair_eval partyEnc some_eval)
open CryptoGames.SM.Construction (CKAState CKAUState Header Mode PartyState SchemeAdversary cacheCU ckaHsEnc ckaHsTy ckaStartRecvUAnsE ckaStartSendUC ckaUHsTy ckaVpEnc ckaVpTy hooksCKAU hooksCKAUC initCKA initCKAEStateC_eval initCKARaw initCKARaw_inv initCKARaw_vrInv initCKAU query_chall_eval query_corr_eval query_receive_eval query_sendBad_eval query_send_eval redCKAPrivU redCKAPrivUProg runCKAU sampleT)
open CryptoGames.SM.Engine (Ctx EState HM HooksCAgrees HooksVRInv RSReach TComp VP cGsB cGsTy engRun esAbort esEnc esG esH eval_bind eval_bind_ret eval_caseOpt eval_ite eval_ret implE liftP_eq_liftM modeCfgEC modeCfgEC_agrees privOutC_eval realPartyE_eval simulateQ_implEC_vr_eq tset_eval_eq_update vpEnc vpRoot vpSetΓ_eval vpTblEnc vpTcurNat vpVR vpVS vpΓ)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open ReductionDsl (CostedReduction Env Expr Ops Sig Ty isGameQuery)

namespace Computational.Proofs.SessionCostedFig8.RedCKAPrivUBridge

section DslEval

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E

@[expose] def ckaUHsEnc (s : CKAUState T I K) :
    (@ckaUHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (ckaHsEnc s.1, s.2)

@[simp] private theorem run_liftU_bind {α β : Type}
    (x : CryptoGames.CKA.AdversaryComp Γ CCoins T I α)
    (k : α → HM (CryptoGames.CKA.spec Γ CCoins T I) (CKAUState T I K) β)
    (h : CKAUState T I K) :
    (StateT.lift x >>= k).run h = x >>= fun a => (k a).run h := by
  simp [StateT.run_bind, StateT.run_lift, bind_map_left]

private theorem caseOpt_eval {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.opt a)) (n : Expr O' Γ' b) (s : Expr O' (a :: Γ') b) (ρ : Env Γ') :
    (ReductionDsl.Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => s.eval (.cons x ρ) := rfl

@[simp] private theorem v0_eval_cons {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a : Ty S'}
    (x : a.denote) (ρ : Env Γ') :
    (ReductionDsl.Expr.v0 (O := O')).eval (ReductionDsl.Env.cons x ρ) = x := rfl

private theorem ckaVpEnc_eq_vpTblEnc :
    @ckaVpEnc KC Γ CCoins T I KR RSt K SS RS M E =
      vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
        (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        (γvT := .opt (.base .γ)) (svT := .base .sig) (ssvT := .base .ss) (rsvT := .base .rs) := rfl

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
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

@[simp] private theorem eval_v0_cons {Γ' : List (Ty S)} {t : Ty S} (x : t.denote) (ρ : Env Γ') :
    (ReductionDsl.Expr.v0 (O := OO)).eval (ReductionDsl.Env.cons x ρ) = x := rfl

theorem ckaStartSendUC_eval [DecidableEq T] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaUHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : CKAUState T I K) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaUHsEnc h) (hp : pE.eval ρ = partyEnc P) :
    (ckaStartSendUC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka mo hE ctxE pE tE γvE σE rE).eval ρ =
      Prod.map id ckaUHsEnc <$>
        ((hooksCKAU cka prng fs Δcka mo).startSend ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h := by
  have hSampKEq : ∀ {Γ''} (ρ' : Env Γ''),
      (ReductionDsl.Comp.sample (O := OO) (I := II) CryptoGames.CKA.CKASamp.k .unit).eval ρ' = sampleT K := by
    intro Γ'' ρ'
    simp only [ReductionDsl.Comp.eval, ckaIface, ckaSamplers, hSampK, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ K)
  dsimp only [ckaStartSendUC, hooksCKAU]
  rw [eval_bind_ret]
  set t := tE.eval ρ
  set γv := γvE.eval ρ
  set σ := σE.eval ρ
  set r := rE.eval ρ
  have h0 : (ReductionDsl.Expr.pair hE (.pair pE (.pair tE (.pair γvE (.pair σE rE))))).eval ρ =
      (ckaUHsEnc h, partyEnc P, t, γv, σ, r) := by
    simp [ReductionDsl.Expr.eval, hh, hp, t, γv, σ, r]
  rw [h0]; clear h0
  set ρ₁ := ReductionDsl.Env.cons
    (t := .prod ckaUHsTy (.prod .bool (.prod .nat
      (.prod (.opt (.base CryptoGames.CKA.CKASort.γ)) (.prod (.base CryptoGames.CKA.CKASort.sig) (.opt (.base CryptoGames.CKA.CKASort.ccoins)))))))
    (ckaUHsEnc h, partyEnc P, t, γv, σ, r) ρ
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  rw [eval_caseOpt]
  have hγv : (ReductionDsl.Expr.fst (.snd (.snd (.snd (ReductionDsl.Expr.v0 (O := OO)))))).eval ρ₁ = γv := rfl
  rw [hγv]
  rcases γv with _ | γ
  · dsimp only
    let Γ₁ : List (Ty S) :=
      .prod ckaUHsTy (.prod .bool (.prod .nat
        (.prod (.opt (.base CryptoGames.CKA.CKASort.γ))
          (.prod (.base CryptoGames.CKA.CKASort.sig) (.opt (.base CryptoGames.CKA.CKASort.ccoins)))))) :: Γ'
    let Γ₂ : List (Ty S) :=
      .prod (.base CryptoGames.CKA.CKASort.t) (.base CryptoGames.CKA.CKASort.i) ::
        .opt (.prod (.base CryptoGames.CKA.CKASort.t) (.base CryptoGames.CKA.CKASort.i)) :: Γ₁
    let Γ₃ : List (Ty S) := .prod (.base CryptoGames.CKA.CKASort.k) (.opt (.base CryptoGames.CKA.CKASort.k)) :: Γ₂
    let Γ₅ : List (Ty S) := (.base CryptoGames.CKA.CKASort.γ) :: (.opt (.base CryptoGames.CKA.CKASort.γ)) :: Γ₃
    have hCont (ans : Option (T × I)) :
        (ReductionDsl.Comp.caseOpt (O := OO) (I := II)
          (Γ := .opt (.prod (.base CryptoGames.CKA.CKASort.t) (.base CryptoGames.CKA.CKASort.i)) :: Γ₁)
          .v0
          (.ret (.pair .none (.pair (.fst (.fst .v1)) (.snd (.fst .v1)))))
          (let tMsg : Expr OO Γ₂ (.base .t) := .fst .v0
           let ik : Expr OO Γ₂ (.base .i) := .snd .v0
           let h0_2 : Expr OO Γ₂ ckaHsTy := .fst (.fst .v2)
           let kOpt0_2 : Expr OO Γ₂ (.opt (.base .k)) := .snd (.fst .v2)
           let p0_2 : Expr OO Γ₂ .bool := .fst (.snd .v2)
           let t0_2 : Expr OO Γ₂ .nat := .fst (.snd (.snd .v2))
           let σ0_2 : Expr OO Γ₂ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v2))))
           let pOut_2 : Expr OO Γ₂ (.prod (.base .sig) (.base .k)) :=
             ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp (.pair σ0_2 ik)
           .bind
             (.ite (.eqN t0_2 (.nat mo.tStar))
               (.bind (ReductionDsl.Comp.sample (O := OO) (I := II) CryptoGames.CKA.CKASamp.k .unit)
                 (.ret (.pair .v0 (.some .v0))))
               (.ret (.pair (.snd pOut_2) kOpt0_2)))
             (let kEpoch : Expr OO Γ₃ (.base .k) := .fst .v0
              let kOpt1 : Expr OO Γ₃ (.opt (.base .k)) := .snd .v0
              let tMsg_3 : Expr OO Γ₃ (.base .t) := .fst .v1
              let ik_3 : Expr OO Γ₃ (.base .i) := .snd .v1
              let h0_3 : Expr OO Γ₃ ckaHsTy := .fst (.fst .v3)
              let p0_3 : Expr OO Γ₃ .bool := .fst (.snd .v3)
              let t0_3 : Expr OO Γ₃ .nat := .fst (.snd (.snd .v3))
              let σ0_3 : Expr OO Γ₃ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v3))))
              let h1_3 : Expr OO Γ₃ ckaHsTy := .tset h0_3 t0_3 (.some (.pair tMsg_3 ik_3))
              let pOut_3 : Expr OO Γ₃ (.prod (.base .sig) (.base .k)) :=
                ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp (.pair σ0_3 ik_3)
              let ss_3 : Expr OO Γ₃ (.base .ss) :=
                ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.fsInitSender kEpoch
              .ite (leN (.nat (mo.tH + Δcka)) t0_3)
                (.bind (ReductionDsl.Comp.query (O := OO) (I := II) CryptoGames.CKA.CKATag.corr p0_3)
                  (.caseOpt .v0
                    (.ret (.pair .none
                      (.pair (.tset (.fst (.fst .v4)) (.fst (.snd (.snd .v4)))
                        (.some (.pair (.fst .v2) (.snd .v2)))) (.snd .v1))))
                    (let γ' : Expr OO Γ₅ (.base .γ) := .v0
                     let kEpoch_5 : Expr OO Γ₅ (.base .k) := .fst .v2
                     let kOpt1_5 : Expr OO Γ₅ (.opt (.base .k)) := .snd .v2
                     let tMsg_5 : Expr OO Γ₅ (.base .t) := .fst .v3
                     let ik_5 : Expr OO Γ₅ (.base .i) := .snd .v3
                     let h0_5 : Expr OO Γ₅ ckaHsTy := .fst (.fst .v5)
                     let t0_5 : Expr OO Γ₅ .nat := .fst (.snd (.snd .v5))
                     let σ0_5 : Expr OO Γ₅ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v5))))
                     let h1_5 : Expr OO Γ₅ ckaHsTy := .tset h0_5 t0_5 (.some (.pair tMsg_5 ik_5))
                     let pOut_5 : Expr OO Γ₅ (.prod (.base .sig) (.base .k)) :=
                       ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp (.pair σ0_5 ik_5)
                     let ss_5 : Expr OO Γ₅ (.base .ss) :=
                       ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.fsInitSender kEpoch_5
                     .ret (.pair
                       (.some (.pair (.some γ') (.pair tMsg_5 (.pair (.fst pOut_5) ss_5))))
                       (.pair h1_5 kOpt1_5)))))
                (.ret (.pair
                  (.some (.pair .none (.pair tMsg_3 (.pair (.fst pOut_3) ss_3))))
                  (.pair h1_3 kOpt1)))))).eval
          (ReductionDsl.Env.cons (t := .opt (.prod (.base CryptoGames.CKA.CKASort.t) (.base CryptoGames.CKA.CKASort.i))) ans ρ₁) =
        Prod.map id ckaUHsEnc <$>
          (match ans with
          | none => pure none
          | some (T', Ik) => do
            cacheCU t (T', Ik)
            let p := prng.up σ Ik
            let (kEpoch, kOpt1) ←
              if t = mo.tStar then do
                let kU ← StateT.lift (sampleT K)
                pure (kU, some kU)
              else pure (p.2, h.2)
            modify fun s => (s.1, kOpt1)
            if mo.tH + Δcka ≤ t then do
              match ← StateT.lift (CryptoGames.CKA.corrQuery P : CryptoGames.CKA.AdversaryComp Γ CCoins T I (Option Γ)) with
              | none => pure none
              | some γ => pure (some (some γ, T', p.1, fs.initSender kEpoch))
            else pure (some (none, T', p.1, fs.initSender kEpoch))).run h := by
      dsimp only
      rcases ans with _ | ⟨T', Ik⟩
      · simp [ρ₁, ReductionDsl.Comp.eval, StateT.run_pure, Prod.map, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
      · simp only [eval_caseOpt, cacheCU, StateT.run_bind, StateT.run_modify, pure_bind]
        set ρ₂ := ReductionDsl.Env.cons (t := .prod (.base CryptoGames.CKA.CKASort.t) (.base CryptoGames.CKA.CKASort.i)) (T', Ik)
          (ReductionDsl.Env.cons (t := .opt (.prod (.base CryptoGames.CKA.CKASort.t) (.base CryptoGames.CKA.CKASort.i))) (some (T', Ik)) ρ₁)
        change (ReductionDsl.Comp.bind _ _).eval ρ₂ = _
        rw [eval_bind, eval_ite]
        have htStar : (ReductionDsl.Expr.eqN (.fst (.snd (.snd (ReductionDsl.Expr.v2 (O := OO))))) (.nat mo.tStar)).eval ρ₂ =
            decide (t = mo.tStar) := rfl
        rw [htStar]
        have hPostK (kk : K × Option K) :
            (ReductionDsl.Comp.ite (O := OO) (I := II) (Γ := Γ₃)
              (leN (.nat (mo.tH + Δcka)) (.fst (.snd (.snd .v3))))
              (.bind (ReductionDsl.Comp.query (O := OO) (I := II) CryptoGames.CKA.CKATag.corr (.fst (.snd .v3)))
                (.caseOpt .v0
                  (.ret (.pair .none
                    (.pair (.tset (.fst (.fst .v4)) (.fst (.snd (.snd .v4)))
                      (.some (.pair (.fst .v2) (.snd .v2)))) (.snd .v1))))
                  (let γ' : Expr OO Γ₅ (.base .γ) := .v0
                   let kEpoch_5 : Expr OO Γ₅ (.base .k) := .fst .v2
                   let kOpt1_5 : Expr OO Γ₅ (.opt (.base .k)) := .snd .v2
                   let tMsg_5 : Expr OO Γ₅ (.base .t) := .fst .v3
                   let ik_5 : Expr OO Γ₅ (.base .i) := .snd .v3
                   let h0_5 : Expr OO Γ₅ ckaHsTy := .fst (.fst .v5)
                   let t0_5 : Expr OO Γ₅ .nat := .fst (.snd (.snd .v5))
                   let σ0_5 : Expr OO Γ₅ (.base .sig) := .fst (.snd (.snd (.snd (.snd .v5))))
                   let h1_5 : Expr OO Γ₅ ckaHsTy := .tset h0_5 t0_5 (.some (.pair tMsg_5 ik_5))
                   let pOut_5 : Expr OO Γ₅ (.prod (.base .sig) (.base .k)) :=
                     ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp (.pair σ0_5 ik_5)
                   let ss_5 : Expr OO Γ₅ (.base .ss) :=
                     ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.fsInitSender kEpoch_5
                   .ret (.pair
                     (.some (.pair (.some γ') (.pair tMsg_5 (.pair (.fst pOut_5) ss_5))))
                     (.pair h1_5 kOpt1_5)))))
              (.ret (.pair
                (.some (.pair .none (.pair (.fst .v1)
                  (.pair (.fst (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp
                    (.pair (.fst (.snd (.snd (.snd (.snd .v3))))) (.snd .v1))))
                    (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.fsInitSender (.fst .v0))))))
                (.pair (.tset (.fst (.fst .v3)) (.fst (.snd (.snd .v3)))
                  (.some (.pair (.fst .v1) (.snd .v1)))) (.snd .v0))))).eval
              (ReductionDsl.Env.cons (t := .prod (.base CryptoGames.CKA.CKASort.k) (.opt (.base CryptoGames.CKA.CKASort.k))) kk ρ₂) =
            Prod.map id ckaUHsEnc <$>
              (if mo.tH + Δcka ≤ t then do
                match ← StateT.lift (CryptoGames.CKA.corrQuery P : CryptoGames.CKA.AdversaryComp Γ CCoins T I (Option Γ)) with
                | none => pure none
                | some γ => pure (some (some γ, T', (prng.up σ Ik).1, fs.initSender kk.1))
               else pure (some (none, T', (prng.up σ Ik).1, fs.initSender kk.1))).run
                (⟨Function.update h.1.cache t (some (T', Ik))⟩, kk.2) := by
          set ρK := ReductionDsl.Env.cons (t := .prod (.base CryptoGames.CKA.CKASort.k) (.opt (.base CryptoGames.CKA.CKASort.k))) kk ρ₂
          rw [eval_ite]
          have hle : (leN (.nat (mo.tH + Δcka)) (.fst (.snd (.snd (ReductionDsl.Expr.v3 (O := OO)))))).eval ρK =
              decide (mo.tH + Δcka ≤ t) := by
            rw [leN_eval]; rfl
          rw [hle]
          by_cases hfin : mo.tH + Δcka ≤ t
          · simp only [hfin, decide_true, ↓reduceIte, eval_bind, run_liftU_bind, map_bind]
            have hp3 : (ReductionDsl.Expr.fst (.snd (ReductionDsl.Expr.v3 (O := OO)))).eval ρK = partyEnc P := rfl
            rw [query_corr_eval _ ρK P hp3]
            refine bind_congr fun γ? => ?_
            rcases γ? with _ | γ'
            · simp only [eval_caseOpt, v0_eval_cons, eval_ret, pair_eval,
                StateT.run_pure, map_pure, Prod.map, id_eq, ckaUHsEnc]
              congr 3
              exact tset_eval_eq_update (.fst (.fst .v4)) (.fst (.snd (.snd .v4)))
                (.some (.pair (.fst .v2) (.snd .v2)))
                (ReductionDsl.Env.cons (t := .opt (.base CryptoGames.CKA.CKASort.γ)) none ρK)
            · simp only [eval_caseOpt, v0_eval_cons, eval_ret,
                StateT.run_pure, map_pure, Prod.map, id_eq, ckaUHsEnc]
              set ρ₃ := ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.γ) γ'
                (ReductionDsl.Env.cons (t := .opt (.base CryptoGames.CKA.CKASort.γ)) (some γ') ρK)
              have hTset := tset_eval_eq_update (O' := OO) (.fst (.fst .v5)) (.fst (.snd (.snd .v5)))
                (.some (.pair (.fst .v3) (.snd .v3))) ρ₃
              simp only [pair_eval, some_eval, hTset]
              simp [ρ₃, ρK, ρ₂, ρ₁, ckaOps, hPrngUp, hFsInitS, ckaUHsEnc, ckaHsEnc,
                ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Expr.v5]
          · simp only [hfin, decide_false, Bool.false_eq_true, ↓reduceIte,
              eval_ret, StateT.run_pure, map_pure, Prod.map, id_eq, ckaUHsEnc]
            have hTset := tset_eval_eq_update (O' := OO) (.fst (.fst .v3)) (.fst (.snd (.snd .v3)))
              (.some (.pair (.fst .v1) (.snd .v1))) ρK
            simp only [pair_eval, some_eval, hTset]
            simp [ρK, ρ₂, ρ₁, ckaOps, hPrngUp, hFsInitS, ckaUHsEnc, ckaHsEnc,
              ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v3]
        by_cases htEq : t = mo.tStar
        · rw [ite_eq_left (decide_eq_true htEq), ite_eq_left htEq]
          rw [eval_bind, hSampKEq, bind_assoc]
          simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify,
            bind_assoc, pure_bind, map_bind]
          refine bind_congr fun kU => ?_
          rw [eval_ret, pair_eval, some_eval, eval_v0_cons, pure_bind]
          dsimp only at hPostK ⊢
          exact hPostK (kU, some kU)
        · simp only [htEq, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ret, pure_bind]
          have hPairEval :
              (ReductionDsl.Expr.pair
                (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp
                  (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (.snd .v0))))
                (.snd (.fst .v2))).eval ρ₂ = ((prng.up σ Ik).2, h.2) := by
            simp [ρ₂, ρ₁, ckaOps, hPrngUp, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2]
          rw [hPairEval]
          exact hPostK ((prng.up σ Ik).2, h.2)
    have hp1 : (ReductionDsl.Expr.fst (.snd (ReductionDsl.Expr.v0 (O := OO)))).eval ρ₁ = partyEnc P := rfl
    have hr : (ReductionDsl.Expr.snd (.snd (.snd (.snd (.snd (ReductionDsl.Expr.v0 (O := OO))))))).eval ρ₁ = r := rfl
    rw [eval_bind, eval_caseOpt, hr]
    rcases r with _ | c
    · rw [eval_ite]
      have htH : (ReductionDsl.Expr.eqN (.fst (.snd (.snd (ReductionDsl.Expr.v0 (O := OO))))) (.nat mo.tH)).eval ρ₁ =
          decide (t = mo.tH) := rfl
      rw [htH]
      by_cases hteq : t = mo.tH
      · rw [ite_eq_left (decide_eq_true hteq), ite_eq_left hteq]
        simp only [query_chall_eval _ ρ₁ P hp1, run_liftU_bind, map_bind]
        exact bind_congr hCont
      · rw [ite_eq_right (by simp [hteq]), ite_eq_right hteq]
        simp only [query_send_eval _ ρ₁ P hp1, run_liftU_bind, map_bind]
        exact bind_congr hCont
    · have hbad : (ReductionDsl.Expr.pair (.fst (.snd (ReductionDsl.Expr.v1 (O := OO)))) .v0).eval
          (ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.ccoins) c ρ₁) = (partyEnc P, c) := rfl
      simp only [query_sendBad_eval _ _ P c hbad, run_liftU_bind, map_bind]
      exact bind_congr hCont
  · dsimp only
    set ρ₂ := ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.γ) γ ρ₁
    have hCoinsCont (coins : CCoins) :
        (ReductionDsl.Comp.bind (O := OO) (I := II)
          (.ite (.eqN (.fst (.snd (.snd .v2))) (.nat mo.tStar))
            (.bind (ReductionDsl.Comp.sample (O := OO) (I := II) CryptoGames.CKA.CKASamp.k .unit)
              (.ret (.pair .v0 (.some .v0))))
            (.ret (.pair
              (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp
                (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                  (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v1 .v0)))))))
              (.snd (.fst .v2)))))
          (.ret (.pair
            (.some (.pair (.some (.fst (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1))))
              (.pair (.fst (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1))))
                (.pair
                  (.fst (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp
                    (.pair (.fst (.snd (.snd (.snd (.snd .v3)))))
                      (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1)))))))
                  (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.fsInitSender (.fst .v0))))))
            (.pair
              (.tset (.fst (.fst .v3)) (.fst (.snd (.snd .v3)))
                (.some (.pair
                  (.fst (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1))))
                  (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1)))))))
              (.snd .v0))))).eval
          (ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.ccoins) coins ρ₂) =
        Prod.map id ckaUHsEnc <$>
          (do
            let c := cka.send γ coins
            cacheCU t (c.2.1, c.2.2)
            let p := prng.up σ c.2.2
            let (kEpoch, kOpt1) ←
              if t = mo.tStar then do
                let kU ← StateT.lift (sampleT K)
                pure (kU, some kU)
              else pure (p.2, h.2)
            modify fun s => (s.1, kOpt1)
            pure (some (some c.1, c.2.1, p.1, fs.initSender kEpoch))).run h := by
      dsimp only
      set ρ₃ := ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.ccoins) coins ρ₂
      simp only [cacheCU, StateT.run_bind, StateT.run_modify, pure_bind]
      change (ReductionDsl.Comp.bind _ _).eval ρ₃ = _
      rw [eval_bind, eval_ite]
      have htStar : (ReductionDsl.Expr.eqN (.fst (.snd (.snd (ReductionDsl.Expr.v2 (O := OO))))) (.nat mo.tStar)).eval ρ₃ =
          decide (t = mo.tStar) := rfl
      rw [htStar]
      have hPostK (kk : K × Option K) :
          (ReductionDsl.Comp.ret (O := OO) (I := II) (.pair
            (.some (.pair (.some (.fst (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1))))
              (.pair (.fst (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1))))
                (.pair
                  (.fst (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp
                    (.pair (.fst (.snd (.snd (.snd (.snd .v3)))))
                      (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1)))))))
                  (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.fsInitSender (.fst .v0))))))
            (.pair
              (.tset (.fst (.fst .v3)) (.fst (.snd (.snd .v3)))
                (.some (.pair
                  (.fst (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1))))
                  (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1)))))))
              (.snd .v0)))).eval
            (ReductionDsl.Env.cons (t := .prod (.base CryptoGames.CKA.CKASort.k) (.opt (.base CryptoGames.CKA.CKASort.k))) kk ρ₃) =
          pure (Prod.map id ckaUHsEnc
            (some (some (cka.send γ coins).1, (cka.send γ coins).2.1,
              (prng.up σ (cka.send γ coins).2.2).1, fs.initSender kk.1),
             (⟨Function.update h.1.cache t
                (some ((cka.send γ coins).2.1, (cka.send γ coins).2.2))⟩, kk.2))) := by
        set ρ₄ := ReductionDsl.Env.cons (t := .prod (.base CryptoGames.CKA.CKASort.k) (.opt (.base CryptoGames.CKA.CKASort.k))) kk ρ₃
        have hTset := tset_eval_eq_update (O' := OO) (.fst (.fst .v3)) (.fst (.snd (.snd .v3)))
          (.some (.pair (.fst (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1))))
            (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v2 .v1)))))) ρ₄
        simp only [eval_ret, pair_eval, some_eval, hTset]
        simp [ρ₄, ρ₃, ρ₂, ρ₁, ckaOps, hSend, hPrngUp, hFsInitS, ckaUHsEnc, ckaHsEnc,
          Prod.map, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3]
      by_cases htEq : t = mo.tStar
      · rw [ite_eq_left (decide_eq_true htEq), ite_eq_left htEq]
        rw [eval_bind, hSampKEq, bind_assoc]
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, StateT.run_modify,
          bind_assoc, pure_bind, map_bind, map_pure]
        refine bind_congr fun kU => ?_
        rw [eval_ret, pair_eval, some_eval, eval_v0_cons, pure_bind]
        dsimp only at hPostK ⊢
        exact hPostK (kU, some kU)
      · simp only [htEq, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ret,
          StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, map_pure]
        have hPairEval :
            (ReductionDsl.Expr.pair
              (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.prngUp
                (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                  (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair .v1 .v0)))))))
              (.snd (.fst .v2))).eval ρ₃ =
              ((prng.up σ (cka.send γ coins).2.2).2, h.2) := by
          simp [ρ₃, ρ₂, ρ₁, ckaOps, hSend, hPrngUp, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2]
        rw [hPairEval]
        exact hPostK ((prng.up σ (cka.send γ coins).2.2).2, h.2)
    have hr2 : (ReductionDsl.Expr.snd (.snd (.snd (.snd (.snd (ReductionDsl.Expr.v1 (O := OO))))))).eval ρ₂ = r := rfl
    rw [eval_bind, eval_caseOpt, hr2]
    rcases r with _ | c
    · have hSamp : (ReductionDsl.Comp.sample (O := OO) (I := II) CryptoGames.CKA.CKASamp.ccoins .unit).eval ρ₂ =
          sampleT CCoins := by
        simp only [ReductionDsl.Comp.eval, ckaIface, ckaSamplers, hSampCCoins, sampleT]
        exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ CCoins)
      simp only [hSamp, run_liftU_bind, map_bind]
      exact bind_congr hCoinsCont
    · simp only [eval_ret, v0_eval_cons, pure_bind]
      exact hCoinsCont c

theorem ckaStartRecvUC_eval [DecidableEq T] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (B Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaUHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γvE : Expr OO Γ' (.opt (.base .γ))) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : CKAUState T I K) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaUHsEnc h) :
    ((hooksCKAUC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo).startRecv hE ctxE pE tE γvE σE tnE).eval ρ =
      Prod.map id ckaUHsEnc <$>
        ((hooksCKAU cka prng fs Δcka mo).startRecv ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  dsimp only [hooksCKAUC, ckaStartRecvUAnsE, hooksCKAU]
  simp only [eval_ret, pair_eval, letE_eval, hh, StateT.run_bind, StateT.run_get, pure_bind]
  set t : ℕ := tE.eval ρ
  set γv : Option Γ := γvE.eval ρ
  set σ : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  set ρ₁ := ReductionDsl.Env.cons
    (t := .prod ckaUHsTy (.prod .nat (.prod (.opt (.base CryptoGames.CKA.CKASort.γ))
      (.prod (.base CryptoGames.CKA.CKASort.sig) (.base CryptoGames.CKA.CKASort.t)))))
    (ckaUHsEnc h, t, γv, σ, Tn) ρ
  change (pure ((ReductionDsl.Expr.caseOpt _ _ _).eval ρ₁, ckaUHsEnc h) :
      TComp (CryptoGames.CKA.spec Γ CCoins T I) _) = _
  have hHonest :
      (ReductionDsl.Expr.caseOpt (.tget (.fst (.fst (ReductionDsl.Expr.v0 (O := OO)))) (.fst (.snd .v0))) .none
        (.ite (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.1.cache t with
        | some (Tc, Ik) => if Tc = Tn then some Ik else none
        | none => none) := by
    have hGet : (ReductionDsl.Expr.tget (.fst (.fst (ReductionDsl.Expr.v0 (O := OO)))) (.fst (.snd .v0))).eval ρ₁ =
        h.1.cache t := rfl
    rw [caseOpt_eval, hGet]
    rcases h.1.cache t with _ | ⟨Tc, Ik⟩
    · rfl
    · simp only [ρ₁, ckaOps, heqT, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, BEq.beq]
      by_cases hEq : Tc = Tn <;> simp [hEq]
  rw [caseOpt_eval, hHonest]
  rcases h.1.cache t with _ | ⟨Tc, Ik⟩
  · dsimp only
    rw [ite_eval]
    have hCond :
        (ReductionDsl.Expr.and (.bool mo.auth)
          (.eqN (.fst (.snd (ReductionDsl.Expr.v0 (O := OO)))) (.nat mo.tStar))).eval ρ₁ =
        (mo.auth && decide (t = mo.tStar)) := rfl
    rw [hCond]
    by_cases hAuthB : (mo.auth && decide (t = mo.tStar)) = true
    · simp only [hAuthB, ↓reduceIte]
      rcases γv with _ | γ
      · simp only [StateT.run_pure, map_pure]; rfl
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
    · simp only [hAuthB]; rfl
  · dsimp only
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte]
      rcases h with ⟨h1, _ | kU⟩ <;> by_cases htStar : t = mo.tStar <;> rcases γv with _ | γ <;>
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, htStar, ckaOps, hRecv, hPrngUp, hFsInitR, ckaUHsEnc,
          ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2]
    · simp only [hEq, ↓reduceIte]
      rw [ite_eval]
      have hCond :
          (ReductionDsl.Expr.and (.bool mo.auth)
            (.eqN (.fst (.snd (ReductionDsl.Expr.v0 (O := OO)))) (.nat mo.tStar))).eval ρ₁ =
          (mo.auth && decide (t = mo.tStar)) := rfl
      rw [hCond]
      by_cases hAuthB : (mo.auth && decide (t = mo.tStar)) = true
      · simp only [hAuthB, ↓reduceIte]
        rcases γv with _ | γ
        · simp only [StateT.run_pure, map_pure]; rfl
        · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
          congr 1; congr 1
          simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
      · simp only [hAuthB]; rfl

theorem ckaCommitUC_eval [DecidableEq T] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaUHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' ckaVpTy) (ρ : Env Γ')
    (h : CKAUState T I K) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : VP (Option Γ) T RSt SS RS)
    (hh : hE.eval ρ = ckaUHsEnc h) (hp : pE.eval ρ = partyEnc P)
    (hold : oldE.eval ρ = ckaVpEnc old) (hnew : newE.eval ρ = ckaVpEnc new) :
    ((hooksCKAUC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo).commit hE ctxE pE oldE newE).eval ρ =
      Prod.map (Option.map ckaVpEnc) ckaUHsEnc <$>
        ((hooksCKAU cka prng fs Δcka mo).commit ctx P old new).run h := by
  dsimp only [hooksCKAUC, hooksCKAU]
  rw [eval_bind_ret]
  have h0 : (ReductionDsl.Expr.pair hE (.pair pE (.pair oldE newE))).eval ρ =
      (ckaUHsEnc h, partyEnc P, ckaVpEnc old, ckaVpEnc new) := by
    simp [ReductionDsl.Expr.eval, hh, hp, hold, hnew]
  rw [h0]; clear h0
  set ρ₁ := ReductionDsl.Env.cons (t := .prod ckaUHsTy (.prod .bool (.prod ckaVpTy ckaVpTy)))
    (ckaUHsEnc h, partyEnc P, ckaVpEnc old, ckaVpEnc new) ρ
  rw [eval_ite]
  have hCond :
      (ReductionDsl.Expr.and (.lt (vpTcurNat (.fst (.snd (.snd (ReductionDsl.Expr.v0 (O := OO))))))
          (vpTcurNat (.snd (.snd (.snd .v0)))))
        (.not (isSomeE (vpΓ (.fst (.snd (.snd .v0))))))).eval ρ₁ =
      (decide (old.tcur < new.tcur) && old.γ.isNone) := by
    rcases new with ⟨id_n, root_n, vS_n, vR_n, γ_n, Tcur_n, tcur_n⟩
    rcases old with ⟨id_o, root_o, vS_o, vR_o, _ | γ_o, Tcur_o, tcur_o⟩
    · simp [ρ₁, isSomeE, vpTcurNat, vpΓ, ckaVpEnc, vpTblEnc, vpEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]; rfl
    · simp [ρ₁, isSomeE, vpTcurNat, vpΓ, ckaVpEnc, vpTblEnc, vpEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]
  rw [hCond]
  by_cases hc : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [hc, ↓reduceIte, eval_bind, run_liftU_bind, map_bind]
    rw [query_receive_eval _ ρ₁ P rfl]
    refine bind_congr fun rcvRes => ?_
    rcases rcvRes with _ | ⟨⟩
    · simp [ρ₁, ReductionDsl.Comp.eval, StateT.run_pure, Prod.map, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
    · simp only [eval_caseOpt]
      set ρ₂ := ReductionDsl.Env.cons (t := .unit) ()
        (ReductionDsl.Env.cons (t := .opt .unit) (some ()) ρ₁)
      change (ReductionDsl.Comp.ite _ _ _).eval ρ₂ = _
      rw [eval_ite]
      have hle : (leN (.nat (mo.tH + Δcka))
          (vpTcurNat (.snd (.snd (.snd (ReductionDsl.Expr.v2 (O := OO))))))).eval ρ₂ =
          decide (mo.tH + Δcka ≤ new.tcur) := by
        rw [leN_eval]; rfl
      rw [hle]
      by_cases hfin : mo.tH + Δcka ≤ new.tcur
      · simp only [hfin, decide_true, ↓reduceIte, eval_bind, run_liftU_bind, map_bind]
        rw [query_corr_eval _ ρ₂ P rfl]
        refine bind_congr fun γ? => ?_
        rcases γ? with _ | γ'
        · simp [ρ₂, ρ₁, ReductionDsl.Comp.eval, StateT.run_pure, Prod.map, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v3]
        · simp only [eval_caseOpt, v0_eval_cons, eval_ret,
            StateT.run_pure, map_pure, Prod.map, Option.map_some, ckaUHsEnc]
          set ρ₃ := ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.γ) γ'
            (ReductionDsl.Env.cons (t := .opt (.base CryptoGames.CKA.CKASort.γ)) (some γ') ρ₂)
          have hSetΓ := vpSetΓ_eval (O' := OO)
            (.snd (.snd (.snd (ReductionDsl.Expr.v4 (O := OO))))) (.some .v0) ρ₃ new rfl
          simp only [pair_eval, some_eval, hSetΓ]
          rfl
      · simp [ρ₂, ρ₁, hfin, eval_ret, StateT.run_pure, Prod.map, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2]
  · simp [ρ₁, hc, eval_ret, StateT.run_pure, Prod.map, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]

theorem ckaRevealUC_eval [DecidableEq T] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (mo : Mode)
    {Γ'} (hE : Expr OO Γ' ckaUHsTy) (ctxE : Expr OO Γ' (cGsTy ckaVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' ckaVpTy) (ρ : Env Γ')
    (h : CKAUState T I K) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (vp : VP (Option Γ) T RSt SS RS)
    (hh : hE.eval ρ = ckaUHsEnc h) (hp : pE.eval ρ = partyEnc P)
    (hvp : vpE.eval ρ = ckaVpEnc vp) :
    ((hooksCKAUC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo).reveal hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) ckaUHsEnc <$>
        ((hooksCKAU cka prng fs Δcka mo).reveal ctx P vp).run h := by
  dsimp only [hooksCKAUC, hooksCKAU]
  rw [eval_bind_ret]
  have h0 : (ReductionDsl.Expr.pair hE (.pair pE vpE)).eval ρ =
      (ckaUHsEnc h, partyEnc P, ckaVpEnc vp) := by
    simp [ReductionDsl.Expr.eval, hh, hp, hvp]
  rw [h0]; clear h0
  set ρ₁ := ReductionDsl.Env.cons (t := .prod ckaUHsTy (.prod .bool ckaVpTy))
    (ckaUHsEnc h, partyEnc P, ckaVpEnc vp) ρ
  rw [eval_caseOpt]
  have hγ : (vpΓ (.snd (.snd (ReductionDsl.Expr.v0 (O := OO))))).eval ρ₁ = vp.γ := rfl
  rw [hγ]
  rcases vp.γ with _ | γ
  · simp only [eval_bind, run_liftU_bind, map_bind]
    rw [query_corr_eval _ ρ₁ P rfl]
    refine bind_congr fun γ? => ?_
    rcases γ? with _ | γ'
    · simp [ρ₁, ReductionDsl.Comp.eval, StateT.run_pure, Prod.map, ckaUHsEnc, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
    · simp only [eval_caseOpt, v0_eval_cons, eval_ret,
        StateT.run_pure, map_pure, Prod.map, Option.map_some, ckaUHsEnc]
      set ρ₂ := ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.γ) γ'
        (ReductionDsl.Env.cons (t := .opt (.base CryptoGames.CKA.CKASort.γ)) (some γ') ρ₁)
      have hReal := realPartyE_eval (O' := OO)
        (.snd (.snd .v2)) .v0 (vpRoot (.snd (.snd .v2)))
        (vpVS (.snd (.snd .v2))) (vpVR (.snd (.snd .v2))) ρ₂ vp rfl
      simp only [pair_eval, some_eval, hReal]
      rfl
  · simp only [pure_bind, StateT.run_pure, map_pure, Prod.map, Option.map_some, ckaUHsEnc]
    set ρ₂ := ReductionDsl.Env.cons (t := .base CryptoGames.CKA.CKASort.γ) γ ρ₁
    change (ReductionDsl.Comp.ret _).eval ρ₂ = _
    have hReal := realPartyE_eval (O' := OO)
      (.snd (.snd .v1)) .v0 (vpRoot (.snd (.snd .v1)))
      (vpVS (.snd (.snd .v1))) (vpVR (.snd (.snd .v1))) ρ₂ vp rfl
    simp only [eval_ret, pair_eval, some_eval, hReal]
    rfl

theorem hooksCKAU_startRecv_rs [DecidableEq T] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party) (t : ℕ)
    (γv : Option Γ) (σ : RSt) (Tn : T) (h : CKAUState T I K) :
    ∀ res ∈ support (((hooksCKAU cka prng fs Δcka mo).startRecv ctx P t γv σ Tn).run h),
      ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs := by
  intro ⟨ans, h'⟩ hmem γ' σ' rs hEq
  subst hEq
  unfold hooksCKAU at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  revert hmem
  rcases h.1.cache t with _ | ⟨Tc, Ik⟩
  · intro hmem
    dsimp only at hmem
    split_ifs at hmem
    · rcases γv with _ | γ
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨h0, _⟩; cases h0
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨h0, _⟩; cases h0
  · intro hmem
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
    · simp only [hEq, ↓reduceIte] at hmem
      split_ifs at hmem
      · rcases γv with _ | γ
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h0, _⟩; cases h0
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; exact hInitR _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨h0, _⟩; cases h0

theorem hooksCKAU_commit_vR [DecidableEq T] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode)
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : VP (Option Γ) T RSt SS RS) (h : CKAUState T I K) :
    ∀ res ∈ support (((hooksCKAU cka prng fs Δcka mo).commit ctx P old new).run h),
      ∀ new', res.1 = some new' → new'.vR = new.vR := by
  intro ⟨ans, h'⟩ hmem new' hEq
  subst hEq
  dsimp only [hooksCKAU] at hmem
  by_cases h1 : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [h1, ↓reduceIte, StateT.run_bind, StateT.run_lift, mem_support_bind_iff] at hmem
    obtain ⟨rcvRes, _, hmem⟩ := hmem
    rcases rcvRes with _ | ⟨⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h0, _⟩; cases h0
    · dsimp only at hmem
      by_cases h2 : mo.tH + Δcka ≤ new.tcur
      · simp only [h2, ↓reduceIte, StateT.run_bind, StateT.run_lift, mem_support_bind_iff] at hmem
        obtain ⟨γ?, _, hmem⟩ := hmem
        rcases γ? with _ | γ'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h0, _⟩; cases h0
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; rfl

theorem hooksCKAUC_agrees_vr [DecidableEq T] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (mo : Mode)
    {VROk : RS → Prop}
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROk rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      ckaUHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROk)
      (hooksCKAUC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo)
      (hooksCKAU cka prng fs Δcka mo) where
  hBounded_post _ _ := trivial
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P _ hh _ hp :=
    ckaStartSendUC_eval cka prng fs hSend hPrngUp hFsInitS hSampCCoins hSampK Δcka mo
      hE ctxE pE tE γE σE rE ρ h ctx P hh hp
  startSend_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P _ hh _ _ :=
    ckaStartRecvUC_eval cka prng fs hRecv hPrngUp hFsInitR heqT B Δcka mo
      hE ctxE pE tE γE σE tnE ρ h ctx P hh
  startRecv_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_vrOk ctx P t γ σ Tn h _ :=
    hooksCKAU_startRecv_rs cka prng fs Δcka mo hInitR ctx P t γ σ Tn h
  fsSend_eval hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ := by
    simp [hooksCKAUC, hooksCKAU, ckaOps, hFsSend, hh,
      StateT.run_pure, Prod.map, ReductionDsl.Expr.eval]
  fsRecv_eval hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ := by
    simp only [hooksCKAUC, hooksCKAU, eval_ret,
      ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, ReductionDsl.Expr.eval]
    congr 2
    rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
    · rfl
    · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
  fsRecv_bounded _ _ _ _ _ _ _ _ _ _ _ := trivial
  commit_eval hE ctxE pE oldE newE ρ h ctx P old new _ hh _ hp hold hnew :=
    ckaCommitUC_eval cka prng fs B Δcka mo hE ctxE pE oldE newE ρ h ctx P old new hh hp hold hnew
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ hp hvp :=
    ckaRevealUC_eval cka prng fs B Δcka mo hE ctxE pE vpE ρ h ctx P vp hh hp hvp

@[expose] def initCKAURaw [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool) :
    CryptoGames.CKA.AdversaryComp Γ CCoins T I
      (EState (VP (Option Γ) T RSt SS RS) M (Header T × E) (CKAUState T I K)) :=
  (fun es => { g := es.g, h := (es.h, none), abort := es.abort }) <$>
    initCKARaw cka prng fs lam mo b

theorem runCKAU_eq_bind_initCKAURaw
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (mo : Mode) (b : Bool)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    runCKAU cka prng fs lam Δcka qep mo b A =
      (do
        let es₀ ← initCKAURaw cka prng fs lam mo b
        let res ←
          (simulateQ
            (implE (hooksCKAU cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
            A).run es₀
        return some res) := by
  unfold runCKAU engRun initCKAURaw initCKARaw
  have hInitRun : (initCKAU cka prng fs lam mo).run ({}, none) =
      ((initCKA cka prng fs lam mo).run {} >>= fun x => pure (x.1, (x.2, none))) := rfl
  rw [hInitRun]
  unfold initCKA
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, bind_map_left]
  refine bind_congr fun kr => ?_
  rcases mo.tL with _ | l
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      bind_map_left]; rfl
  · simp only [StateT.run_pure, pure_bind]; rfl

theorem redCKAPrivUProg_eval_vr
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
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (hooksCKAU cka prng fs Δcka ⟨false, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redCKAPrivUProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      redCKAPrivU cka prng fs lam Δcka qep tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksCKAUC_agrees_vr (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B Δcka ⟨false, tL, t⟩ hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins hSampK (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (ReductionDsl.Comp.sample (O := OO) (I := II) CryptoGames.CKA.CKASamp.bit .unit).eval ρ' = sampleT Bool := by
    intro Γ' ρ'
    simp only [ReductionDsl.Comp.eval, ckaIface, ckaSamplers, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  unfold redCKAPrivUProg ReductionDsl.CostedReduction.eval ReductionDsl.CostedReduction.impl redCKAPrivU
  dsimp only
  rw [eval_bind, hBit, bind_assoc]
  refine bind_congr fun b => ?_
  have hInit := initCKAEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR hSampKR hSampKC
    ⟨false, tL, t⟩ (ReductionDsl.Expr.v0 (O := OO)) (ReductionDsl.Env.cons (t := .bool) b (ReductionDsl.Env.cons (t := .unit) () .nil))
  have hEvalRetInitU : ∀ {Γ' : List (Ty S)}
      (es₀ : EState (VP (Option Γ) T RSt SS RS) M (Header T × E) (CKAState T I))
      (ρ' : Env Γ'),
      (ReductionDsl.Comp.ret (O := OO) (I := II)
        (.pair .unit (.pair (esG .v0) (.pair (.pair (esH .v0) .none) (esAbort .v0))))).eval
          (ReductionDsl.Env.cons (esEnc ckaVpEnc ckaHsEnc es₀) ρ') =
        pure ((), esEnc ckaVpEnc ckaUHsEnc { g := es₀.g, h := (es₀.h, none), abort := es₀.abort }) :=
    fun _ _ => rfl
  rw [eval_bind, hInit, runCKAU_eq_bind_initCKAURaw]
  unfold initCKAURaw
  simp only [bind_map_left, eval_v0_cons, hEvalRetInitU, ckaVpEnc_eq_vpTblEnc, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initCKARaw cka prng fs lam ⟨false, tL, t⟩ b) fun es₀ hes₀ => ?_
  have ⟨hInv₀, hb₀⟩ := initCKARaw_inv cka prng fs lam ⟨false, tL, t⟩ b hqB hB1 hBB es₀ hes₀
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨false, tL, t⟩ b
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  let esU₀ : EState (VP (Option Γ) T RSt SS RS) M (Header T × E) (CKAUState T I K) :=
    { g := es₀.g, h := (es₀.h, none), abort := es₀.abort }
  have ⟨hSim, hSimInv⟩ := simulateQ_implEC_vr_eq hDefaultE (fun _ => rfl) ckaUHsEnc (fun _ => True)
    (hooksCKAUC B Δcka ⟨false, tL, t⟩) (hooksCKAU cka prng fs Δcka ⟨false, tL, t⟩)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (modeCfgEC OO ⟨false, tL, t⟩) (⟨false, tL, t⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨false, tL, t⟩) heqT heqM heqE (⟨false, tL, t⟩ : Mode).policy
    (fun _ _ _ _ _ _ => trivial) hA' esU₀ trivial hInv₀ hVR₀
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', hb'⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hbEq : (cGsB (esG (ReductionDsl.Expr.v0 (O := OO)))).eval
      (ReductionDsl.Env.cons (esEnc vpTblEnc ckaUHsEnc es') (ReductionDsl.Env.cons (t := .bool) b' .nil)) = b := by
    change es'.g.b = b
    exact hb'.trans hb₀
  exact privOutC_eval ckaUHsEnc L (2 + Δcka) (⟨false, tL, t⟩ : Mode).policy
    (ReductionDsl.Comp.sample (I := II) CryptoGames.CKA.CKASamp.bit .unit) hBit
    (cGsB (esG .v0)) .v1 .v0
    (ReductionDsl.Env.cons (esEnc vpTblEnc ckaUHsEnc es') (ReductionDsl.Env.cons (t := .bool) b' .nil))
    b b' es' hBnd'.leaks_le hbEq rfl rfl

end DslEval

section AtomicSwap

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

omit [Zero Pt] [SampleableType Pt] in
lemma hooksCKAU_vrInv_fsAtomicB (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka : ℕ) (mo : Mode) :
    HooksVRInv (RSReach maxForwardJumps)
      (hooksCKAU (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) Δcka mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKAU_startRecv_rs (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) Δcka mo
      (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
        (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksCKAU] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (fsAtomicB_receive_rsReach C ℓ encT idOf B0 _ hVR hmem.1.symm).2
  commit_vR := hooksCKAU_commit_vR (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) Δcka mo

omit [Zero Pt] in
theorem redCKAPrivUProg_eval_atomic (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : CryptoGames.SM.MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((redCKAPrivUProg (q + 1) B0 1 qep maxForwardJumps tL i :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
      redCKAPrivU (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
        lam 1 qep tL i A := by
  intro B0
  exact redCKAPrivUProg_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksCKAU_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 1 ⟨false, tL, i⟩)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
      (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] [SampleableType Pt] in
lemma hooksCKAU_vrInv_lFS {KC Γ CCoins I KR RSt : Type}
    [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka : ℕ) (mo : Mode) :
    HooksVRInv (RSReachB maxForwardJumps)
      (hooksCKAU cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKAU_startRecv_rs cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksCKAU] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR hmem.1.symm).2
  commit_vR := hooksCKAU_commit_vR cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo

omit [Zero Pt] [SampleableType Pt] in
lemma hooksCKAU_localFsAgree {KC Γ CCoins I KR RSt : Type}
    [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka : ℕ) (mo : Mode) :
    HooksLocalFsAgree ℓ B0
      (hooksCKAU cka prng (fsAtomicB C ℓ encT idOf B0) Δcka mo)
      (hooksCKAU cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo) where
  startSend_eq := by unfold hooksCKAU fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  startRecv_eq := by unfold hooksCKAU fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [hooksCKAU]; rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [hooksCKAU]; rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold hooksCKAU; rfl
  reveal_eq := by unfold hooksCKAU; rfl

omit [Zero Pt] [SampleableType Pt] in
theorem runCKAU_fsAtomicB_eq_lFS
    {KC Γ CCoins I KR RSt : Type} [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (mo : Mode) (b : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    runCKAU cka prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep mo b A =
      runCKAU cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep mo b A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  rw [runCKAU_eq_bind_initCKAURaw, runCKAU_eq_bind_initCKAURaw]
  unfold initCKAURaw
  have hInitEq :
      initCKARaw cka prng (fsAtomicB C ℓ encT idOf B0) lam mo b =
        initCKARaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b := by
    unfold initCKARaw fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  rw [hInitEq, bind_map_left, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
  have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
    Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b hqB hB1 hBB es₀ hes₀
  have hVRHk := hooksCKAU_vrInv_lFS cka prng C ℓ encT idOf Δcka mo
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b
    (fun k => hVRHk.mono (Nat.zero_le _)
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps k)) es₀ hes₀
  let esU₀ : EState
      (VP (Option Γ) Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (CKAUState Pt I (BitVec 256)) :=
    { g := es₀.g, h := (es₀.h, none), abort := es₀.abort }
  change (simulateQ (implE _ (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) A).run esU₀ >>= _ =
    (simulateQ (implE _ (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) A).run esU₀ >>= _
  rw [simulateQ_implE_localFs_eq
    (hooksCKAU_localFsAgree cka prng C ℓ encT idOf B0 Δcka mo)
    hVRHk hB0 hA' hSendOk esU₀ hInv₀ hVR₀]

end AtomicSwap

end Computational.Proofs.SessionCostedFig8.RedCKAPrivUBridge

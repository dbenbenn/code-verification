/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.KemFailFind
public import LibsignalBinary.Proofs.SpqrV1Sync.CoinBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Defs
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeCKA -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeFS

/-!
# Bound on `hiddenSaltTerm`

**Checked by Lean.** Bounds `hiddenSaltTerm` via explicit reductions to `DeliverForge` (`CKA`, `PRFPRNG`, and `FS-AEAD`), MAC forgery and ratchet-key collision terms, and an online `MlKem.KemFailBad` transfer over logged send tapes.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoGames.SM.Thm1L17
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-! ## `DeliverForge` hook adapter -/

abbrev DeliverForgeM (Pt : Type) (ℓ : ℕ) :=
  StateT (List (Fig8C Pt))
    (DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))

/-- Header, message-index, and wire-payload agreement between two Fig. 8 ciphertexts. -/
@[expose] def sameWireFig8 (c c' : Fig8C Pt) : Bool :=
  decide (c.1 = c'.1 ∧ c.2.1 = c'.2.1 ∧ c.2.2.1 = c'.2.2.1)

/-- Translates Fig. 8 queries into `DeliverForge` queries while logging sent ciphertexts. -/
@[expose] def fig8ToDFImpl (Pt : Type) (ℓ : ℕ) :
    QueryImpl (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (DeliverForgeM Pt ℓ) :=
  fun q => match q with
  | .inl n =>
    StateT.lift (query (spec := unifSpec +
      DeliverForge.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr (.inl (.inl (.inl (.inl (Q, m, r))))) => do
    let res ← StateT.lift (DeliverForge.transmitQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q m r)
    match res with
    | some c => modify (c :: ·)
    | none => pure ()
    return res
  | .inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) => do
    let res ← StateT.lift (DeliverForge.challQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q m₀ m₁ r)
    match res with
    | some c => modify (c :: ·)
    | none => pure ()
    return res
  | .inr (.inl (.inl (.inr (Q, c)))) =>
    StateT.lift (DeliverForge.deliverQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c)
  | .inr (.inl (.inr (Q, c))) =>
    StateT.lift (DeliverForge.injectQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c)
  | .inr (.inr Q) =>
    StateT.lift (DeliverForge.corrQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)

/-- `Hook` adapter lifting Fig. 8 computations via `fig8ToDFImpl` and forwarding `probe` to `deliverForgeQuery`. -/
@[expose] def deliverForgeHook (Pt : Type) [DecidableEq Pt] (ℓ : ℕ) :
    Hook Pt ℓ (DeliverForgeM Pt ℓ) where
  lift x := simulateQ (fig8ToDFImpl Pt ℓ) x
  probe Q c' := do
    let sent ← get
    match sent.find? (fun c => sameWireFig8 c c') with
    | some c =>
      let _ ← StateT.lift (DeliverForge.deliverForgeQuery
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c c')
      pure ()
    | none => pure ()

/-- Fig. 8 `DeliverForge` adversary induced by running `simRunCWith` under `deliverForgeHook`. -/
@[expose] def simDeliverForge (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) :=
  (simRunCWith (P := P) (encT := encT) (decT := decT) (qep := qep)
    (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (fs := lFS P.C P.codec ℓ encT idOf 25000)
    (H := deliverForgeHook Pt ℓ) Dh A).run' []

/-! ## Explicit reductions -/

/-- CKA reduction for `hiddenSaltTerm` at healing guess `tL` and target epoch `t`. -/
def redCKAHiddenSalt (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : LibAdv PQ PQC ℓ) : CKA.Adversary (DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt :=
  DeliverForge.redCKAAuthDF (dhScheme Dh) (rootPRNG P.C.F encPt)
    (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) tL t
    (DeliverForge.challSimDF (2 + 1) (qep + 1)
      (simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A))

/-! ### `KemFailFind` reduction -/

@[expose] def kemBraidParty : Party → Braid.Party
  | .A => .a
  | .B => .b

/-- Braid-tracker state monitoring cross-party `(seed, encRandOf r)` pairs along honest SPQR V1 sends and deliveries. -/
structure KemFailTrackState (F : ShaCompress) where
  e : Epoch
  auth : Authenticator
  c : Coins
  st : Party → St F
  sentB : List (Msg × BitVec 32)
  sendCtr : Party → ℕ → ℕ
  cand : Option (List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32)

@[expose] def initKemFailTrack (F : ShaCompress) (k : BitVec 256) : KemFailTrackState F :=
  let auth₀ := Authenticator.new F (CryptoGames.HMAC.keyToBytes32 k) 1#64
  let stA₀ : St F := .keysUnsampled { uc := { epoch := 1#64, auth := auth₀ } }
  let stB₀ : St F := .noHeaderReceived
    { uc := { epoch := 1#64, auth := auth₀ }, receiving_hdr := freshDec 96 }
  { e := 1#64
    auth := auth₀
    c := .init
    st := fun Q => match Q with | .A => stA₀ | .B => stB₀
    sentB := []
    sendCtr := fun _ _ => 0
    cand := none }

/-- Advances `KemFailTrackState` on a send by `Q` with coins `r`, latching the first pair that triggers `K.honestExchangeFails`. -/
@[expose] def stepKemFailSend (F : ShaCompress) (K : MlKem) (tr : KemFailTrackState F) (Q : Party)
    (r : BitVec 512) : KemFailTrackState F :=
  let cand' :=
    match tr.cand with
    | some p => some p
    | none =>
      if ekSide tr.e != kemBraidParty Q then
        match tr.c, tr.st Q with
        | .seed s, .headerReceived _ =>
          if K.honestExchangeFails s (encRandOf r) then some (s, encRandOf r) else none
        | _, _ => none
      else none
  match (tr.st Q).send K (coinBytes r) with
  | .ok (out, _) =>
    let E := out.msg.epoch.toNat - 1
    let n := tr.sendCtr Q E
    { tr with
      c := nextCoins F tr.c (tr.st Q) (coinBytes r)
      st := Function.update tr.st Q out.state
      sentB := tr.sentB ++ [(out.msg, BitVec.ofNat 32 (n + 1))]
      sendCtr := Function.update tr.sendCtr Q (Function.update (tr.sendCtr Q) E (n + 1))
      cand := cand' }
  | .error _ => { tr with cand := cand' }

/-- Advances `KemFailTrackState` on an accepted delivery of send `j` to `Q`. -/
@[expose] def stepKemFailDeliver (F : ShaCompress) (K : MlKem) (tr : KemFailTrackState F) (Q : Party)
    (j : ℕ) : KemFailTrackState F :=
  match tr.sentB[j]? with
  | none => tr
  | some (m, _) =>
    match (tr.st Q).recv K m with
    | .ok out =>
      let tr1 := { tr with st := Function.update tr.st Q out.state }
      if m = noneMsg (tr.e + 1#64) then
        match tr.c with
        | .both s r =>
          { tr1 with e := tr.e + 1#64, auth := authNext F K tr.e tr.auth s r, c := .init }
        | _ => tr1
      else tr1
    | .error _ => tr

abbrev KemFailSimM (PQ Pt : Type) (F : ShaCompress) (ℓ : ℕ) :=
  StateT (LibsignalToModularSchemeSimState PQ Pt ℓ ×
    (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
    KemFailTrackState F) ProbComp

@[expose] def runProbeStep (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (_decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (_qep : ℕ)
    {α : Type} (step : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) :
    KemFailSimM PQ Pt P.C.F ℓ α := fun ⟨sC, gh, tr⟩ => do
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let ((a, sC'), gh') ← (step.run sC).run gh
  let _ := fig
  return (a, (sC', gh', tr))

@[expose] def kemFailSendStep (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (_decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    KemFailSimM PQ Pt P.C.F ℓ (Option (List (BitVec 8))) := do
  let ⟨sC, gh, tr⟩ ← get
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then
    return none
  match sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let rq ← match r with
      | some rq => pure rq
      | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512))
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    let _ := fs
    let pn :=
      if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    let rc : Option (BitVec 256) ← match r with
      | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      | none => pure none
    let tr' := stepKemFailSend P.C.F K tr Q rq
    match mkPub (P := P) sC.base Q rq pn with
    | none =>
      set (sC, gh, { tr with cand := tr'.cand })
      return none
    | some (pq', pub) =>
      let qFig : Fig8Comp Pt ℓ (Option (Fig8C Pt)) := match chal with
        | none => SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
        | some m₁ => SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc
      let (res, gh') ← ((probeHook fig (qep + 1)).lift qFig).run gh
      match res with
      | none =>
        set (sC, gh', { tr with cand := tr'.cand })
        return none
      | some c =>
        let w := toWire c
        let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
          ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
        let mir' := s₁.record 3 Q () rec' chal.isSome
        let base' : SimState PQ Pt ℓ :=
          { sC.base with
            mir := mir'
            pq := Function.update sC.base.pq Q pq'
            pn := Function.update sC.base.pn Q pn
            honest := (w, c) :: sC.base.honest }
        let sent' := match (sC.kept Q).full, base'.honest.head? with
          | some st, some (_, c₀) =>
            if st.id.sendsIn (st.tcur + 1) then sC.sent
            else match st.vS with
              | some v => (c₀, v) :: sC.sent
              | none => sC.sent
          | _, _ => sC.sent
        let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          { sC with
            base := base'
            kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q))
            sent := sent' }
        set (sC', gh', tr')
        return some w

@[expose] def kemFailSimImpl (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      (KemFailSimM PQ Pt P.C.F ℓ) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let H := probeHook fig (qep + 1)
  let c : QueryImpl unifSpec (KemFailSimM PQ Pt P.C.F ℓ) := fun n =>
    StateT.lift (query (spec := unifSpec) n)
  let i₁ : QueryImpl ((Party × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8)))
      (KemFailSimM PQ Pt P.C.F ℓ) :=
    fun ⟨Q, m₀, r⟩ =>
      kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
  let i₂ : QueryImpl
      ((Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8)))
      (KemFailSimM PQ Pt P.C.F ℓ) :=
    fun ⟨Q, m₀, m₁, r⟩ =>
      kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ)))
      (KemFailSimM PQ Pt P.C.F ℓ) :=
    fun ⟨Q, w⟩ => do
      let ⟨sC, _, _⟩ ← get
      let revHonest := sC.base.honest.reverse
      let j? := revHonest.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      let res ← runProbeStep P ℓ Dh encPt encT decT idOf lam qep
        (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
          (fig := fig) (fs := fs) (H := H) Q w true))
      match res, j? with
      | some (.accepted _ _ _), some j =>
        modify fun ⟨sC', gh', tr⟩ => (sC', gh', stepKemFailDeliver P.C.F K tr Q j)
      | _, _ => pure ()
      return res
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ)))
      (KemFailSimM PQ Pt P.C.F ℓ) :=
    fun ⟨Q, w⟩ =>
      runProbeStep P ℓ Dh encPt encT decT idOf lam qep
        (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
          (fig := fig) (fs := fs) (H := H) Q w false))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) (KemFailSimM PQ Pt P.C.F ℓ) :=
    fun Q =>
      runProbeStep P ℓ Dh encPt encT decT idOf lam qep
        (guardC (simCorrC (P := P) (encT := encT) (H := H) Dh Q))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

/-- `KemFailFind` reduction simulating `A` in `hiddenSaltGame` and returning the first cross-party pair triggering `K.honestExchangeFails`. -/
@[expose] def redKemFailHiddenSalt (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) : MlKem.KemFailFindAdversary := do
  let b ← $ᵗ Bool
  let k ← $ᵗ (BitVec 256 × BitVec 256)
  let pqrKey ← $ᵗ BitVec 256
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
    initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  let gh₀ := (initState fig k b, false)
  let tr₀ := initKemFailTrack P.C.F pqrKey
  let (_, (_, _, tr)) ←
    (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
  return tr.cand.getD (List.Vector.replicate 64 0, List.Vector.replicate 32 0)

/-! ### Online `KemFailBad` transfer over logged send tapes -/

theorem tapePairFails_coinBytes (K : MlKem) (r₁ r₂ : BitVec 512) :
    K.tapePairFails (coinBytes r₁) (coinBytes r₂) =
      K.honestExchangeFails (coinEquiv r₁) (encRandOf r₂) := by
  have h₁ := coinBytes_length r₁; have h₂ := coinBytes_length r₂
  simp only [MlKem.tapePairFails, h₁, h₂, ↓reduceDIte]
  rw [show (⟨coinBytes r₁, h₁⟩ : Seed) = coinEquiv r₁ from List.Vector.eq _ _ (coinEquiv_apply r₁).symm,
    show (⟨(coinBytes r₂).take 32, by simp [h₂]⟩ : EncRand) = encRandOf r₂ from List.Vector.eq _ _ rfl]

theorem kemFailBad_of_honestExchangeFails_coinEquiv (K : MlKem) (log : List (BitVec 512))
    {r₁ r₂ : BitVec 512} (hr₁ : r₁ ∈ log) (hr₂ : r₂ ∈ log)
    (hfail : K.honestExchangeFails (coinEquiv r₁) (encRandOf r₂) = true) :
    K.KemFailBad (log.map coinBytes) = true := by
  simp only [MlKem.KemFailBad, List.any_eq_true, List.mem_map]
  exact ⟨_, ⟨r₁, hr₁, rfl⟩, _, ⟨r₂, hr₂, rfl⟩, (tapePairFails_coinBytes K r₁ r₂).trans hfail⟩

theorem kemFailBad_mono_subset {K : MlKem} {l₁ l₂ : List (List (BitVec 8))}
    (hsub : ∀ t ∈ l₁, t ∈ l₂) (hbad : K.KemFailBad l₁ = true) : K.KemFailBad l₂ = true := by
  simp only [MlKem.KemFailBad, List.any_eq_true] at hbad ⊢
  rcases hbad with ⟨t₁, ht₁, t₂, ht₂, hf⟩; exact ⟨t₁, hsub t₁ ht₁, t₂, hsub t₂ ht₂, hf⟩

theorem kemFailBad_mono (K : MlKem) {l₁ l₂ : List (List (BitVec 8))}
    (hbad : K.KemFailBad l₁ = true) : K.KemFailBad (l₁ ++ l₂) = true :=
  kemFailBad_mono_subset (fun _ ht => List.mem_append_left l₂ ht) hbad

/-- Invariant tying `KemFailTrackState` (`tr.c` and `tr.cand`) to a send-coin log `log`. -/
structure KemTrackLoggedInv {F : ShaCompress} (K : MlKem)
    (tr : KemFailTrackState F) (log : List (BitVec 512)) : Prop where
  seed_mem : ∀ s, tr.c = .seed s → ∃ r₁ ∈ log, s = coinEquiv r₁
  cand_mem : ∀ p, tr.cand = some p →
    ∃ r₁ ∈ log, ∃ r₂ ∈ log, p = (coinEquiv r₁, encRandOf r₂) ∧ K.honestExchangeFails p.1 p.2 = true

theorem kemTrackLoggedInv_init (F : ShaCompress) (K : MlKem) (pqrKey : BitVec 256) :
    KemTrackLoggedInv K (initKemFailTrack F pqrKey) [] where
  seed_mem _ hs := by simp [initKemFailTrack] at hs
  cand_mem _ hc := by simp [initKemFailTrack] at hc

theorem kemTrackLoggedInv_mono {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log log' : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (hsub : ∀ r ∈ log, r ∈ log') :
    KemTrackLoggedInv K tr log' where
  seed_mem s hs := let ⟨r₁, hr₁, hEq⟩ := hinv.seed_mem s hs; ⟨r₁, hsub r₁ hr₁, hEq⟩
  cand_mem p hp := let ⟨r₁, hr₁, r₂, hr₂, hEq, hf⟩ := hinv.cand_mem p hp
    ⟨r₁, hsub r₁ hr₁, r₂, hsub r₂ hr₂, hEq, hf⟩

theorem nextCoins_seed_mem {F : ShaCompress} {c : Coins} {st : St F} {log : List (BitVec 512)}
    (r : BitVec 512) (hseed : ∀ s, c = .seed s → ∃ r₁ ∈ log, s = coinEquiv r₁)
    {s' : Seed} (hs' : nextCoins F c st (coinBytes r) = .seed s') :
    ∃ r₁ ∈ log ++ [r], s' = coinEquiv r₁ := by
  cases c with
  | init => cases st with
    | keysUnsampled ku =>
      rw [nextCoins_init_coin F r (.keysUnsampled ku) ⟨ku, rfl⟩] at hs'; cases hs'
      exact ⟨r, List.mem_append_right _ (List.mem_singleton_self r), rfl⟩
    | _ => simp [nextCoins] at hs'
  | seed s => cases st with
    | headerReceived hr =>
      rw [nextCoins_seed_coin F s r (.headerReceived hr) ⟨hr, rfl⟩] at hs'; cases hs'
    | _ => simp [nextCoins] at hs'; subst hs'
           obtain ⟨r₁, hr₁, hEq⟩ := hseed s rfl; exact ⟨r₁, List.mem_append_left _ hr₁, hEq⟩
  | both _ _ => simp [nextCoins] at hs'

theorem stepKemFailSend_cand_mem {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (r : BitVec 512)
    {p : Seed × EncRand} (hp : (stepKemFailSend F K tr Q r).cand = some p) :
    ∃ r₁ ∈ log ++ [r], ∃ r₂ ∈ log ++ [r],
      p = (coinEquiv r₁, encRandOf r₂) ∧ K.honestExchangeFails p.1 p.2 = true := by
  have hcand_eq : (stepKemFailSend F K tr Q r).cand = match tr.cand with
      | some p => some p
      | none => if ekSide tr.e != kemBraidParty Q then match tr.c, tr.st Q with
        | .seed s, .headerReceived _ =>
          if K.honestExchangeFails s (encRandOf r) then some (s, encRandOf r) else none
        | _, _ => none else none := by
    unfold stepKemFailSend; cases (tr.st Q).send K (coinBytes r) <;> rfl
  rw [hcand_eq] at hp
  cases htc : tr.cand with
  | some p₀ =>
    rw [htc] at hp; obtain ⟨r₁, hr₁, r₂, hr₂, hEq, hf⟩ := hinv.cand_mem p₀ htc; cases hp
    exact ⟨r₁, List.mem_append_left _ hr₁, r₂, List.mem_append_left _ hr₂, hEq, hf⟩
  | none =>
    rw [htc] at hp
    by_cases hek : (ekSide tr.e != kemBraidParty Q) = true
    · simp only [hek] at hp; cases hc : tr.c <;> rw [hc] at hp
      · simp at hp
      · rename_i s; cases hst : tr.st Q <;> rw [hst] at hp <;> try simp at hp
        by_cases hf : K.honestExchangeFails s (encRandOf r) = true
        · have hp' : (s, encRandOf r) = p := by simpa [hf] using hp
          subst hp'; obtain ⟨r₁, hr₁, rfl⟩ := hinv.seed_mem s hc
          exact ⟨r₁, List.mem_append_left _ hr₁,
            r, List.mem_append_right _ (List.mem_singleton_self r), rfl, hf⟩
        · simp [hf] at hp
      · simp at hp
    · simp [hek] at hp

theorem kemTrackLoggedInv_stepKemFailSend {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (r : BitVec 512) :
    KemTrackLoggedInv K (stepKemFailSend F K tr Q r) (log ++ [r]) where
  seed_mem s' hs' := by
    unfold stepKemFailSend at hs'
    cases hsend : (tr.st Q).send K (coinBytes r) with
    | ok p => obtain ⟨_, _⟩ := p; rw [hsend] at hs'; exact nextCoins_seed_mem r hinv.seed_mem hs'
    | error _ =>
      rw [hsend] at hs'; obtain ⟨r₁, hr₁, hEq⟩ := hinv.seed_mem s' hs'
      exact ⟨r₁, List.mem_append_left _ hr₁, hEq⟩
  cand_mem _ hp := stepKemFailSend_cand_mem hinv Q r hp

theorem kemTrackLoggedInv_stepKemFailSend_candOnly {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (r : BitVec 512) :
    KemTrackLoggedInv K { tr with cand := (stepKemFailSend F K tr Q r).cand } (log ++ [r]) where
  seed_mem s' hs' := let ⟨r₁, hr₁, hEq⟩ := hinv.seed_mem s' hs'; ⟨r₁, List.mem_append_left _ hr₁, hEq⟩
  cand_mem _ hp := stepKemFailSend_cand_mem hinv Q r hp

theorem stepKemFailDeliver_cand {F : ShaCompress} (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    (stepKemFailDeliver F K tr Q j).cand = tr.cand := by
  unfold stepKemFailDeliver
  split <;> [rfl; (split <;> [(dsimp only; split <;> [(split <;> rfl); rfl]); rfl])]

theorem stepKemFailDeliver_c_eq_seed {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {Q : Party} {j : ℕ} {s' : Seed}
    (hs' : (stepKemFailDeliver F K tr Q j).c = .seed s') : tr.c = .seed s' := by
  unfold stepKemFailDeliver at hs'
  split at hs' <;> [exact hs'; (split at hs' <;>
    [(dsimp only at hs'; split at hs' <;> [(split at hs' <;> [cases hs'; exact hs']); exact hs']); exact hs'])]

theorem kemTrackLoggedInv_stepKemFailDeliver {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (j : ℕ) :
    KemTrackLoggedInv K (stepKemFailDeliver F K tr Q j) log where
  seed_mem s' hs' := hinv.seed_mem s' (stepKemFailDeliver_c_eq_seed hs')
  cand_mem p hp := hinv.cand_mem p (stepKemFailDeliver_cand K tr Q j ▸ hp)

/-- `KemTrackLoggedInv` and `tr.cand.isSome` imply `KemFailBad` on the logged send tapes. -/
theorem kemFailBad_of_kemTrackLoggedInv {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (hcand : tr.cand.isSome = true) :
    K.KemFailBad (log.map coinBytes) = true := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hcand
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl, hfail⟩ := hinv.cand_mem p hp
  exact kemFailBad_of_honestExchangeFails_coinEquiv K log hr₁ hr₂ hfail

theorem cand_eq_none_of_kemTrackLoggedInv {F : ShaCompress} (K : MlKem)
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (hgood : K.KemFailBad (log.map coinBytes) = false) :
    tr.cand = none := by
  cases hc : tr.cand with
  | none => rfl
  | some _ =>
    have hbad := kemFailBad_of_kemTrackLoggedInv hinv (by simp [hc])
    rw [hgood] at hbad; cases hbad

abbrev KemFailLogSimM (PQ Pt : Type) (F : ShaCompress) (ℓ : ℕ) :=
  StateT (List (BitVec 512)) (KemFailSimM PQ Pt F ℓ)

@[expose] def kemFailSendStepPostCoin (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (rq : BitVec 512) : KemFailSimM PQ Pt P.C.F ℓ (Option (List (BitVec 8))) := do
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000; let _ := fs
  let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
  let rc : Option (BitVec 256) ← match r with
    | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) | none => pure none
  let tr' := stepKemFailSend P.C.F K tr Q rq
  match mkPub (P := P) sC.base Q rq pn with
  | none => set (sC, gh, { tr with cand := tr'.cand }); return none
  | some (pq', pub) =>
    let qFig : Fig8Comp Pt ℓ (Option (Fig8C Pt)) := match chal with
      | none => SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
      | some m₁ => SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc
    let (res, gh') ← ((probeHook fig (qep + 1)).lift qFig).run gh
    match res with
    | none => set (sC, gh', { tr with cand := tr'.cand }); return none
    | some c =>
      let w := toWire c
      let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
      let base' : SimState PQ Pt ℓ := { sC.base with
        mir := s₁.record 3 Q () rec' chal.isSome, pq := Function.update sC.base.pq Q pq',
        pn := Function.update sC.base.pn Q pn, honest := (w, c) :: sC.base.honest }
      let sent' := match (sC.kept Q).full, base'.honest.head? with
        | some st, some (_, c₀) => if st.id.sendsIn (st.tcur + 1) then sC.sent
          else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
        | _, _ => sC.sent
      set ({ sC with base := base',
                     kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)),
                     sent := sent' }, gh', tr')
      return some w

def kemFailLogSendStep (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (_decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    KemFailLogSimM PQ Pt P.C.F ℓ (Option (List (BitVec 8))) := do
  let ⟨sC, gh, tr⟩ ← StateT.lift get
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then return none
  match sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let rq ← StateT.lift (match r with
      | some rq => pure rq | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512)))
    let log ← get; set (log ++ [rq])
    StateT.lift (kemFailSendStepPostCoin P K ℓ Dh encPt encT idOf lam qep sC gh tr s₁ Q m₀ chal r rq)

private theorem evalDist_pure_bool_mono' {b₁ b₂ : Bool} (h : b₁ = true → b₂ = true) :
    𝒟[(pure b₁ : ProbComp Bool)] {true} ≤ 𝒟[(pure b₂ : ProbComp Bool)] {true} := by
  cases hb₁ : b₁ <;> [simp; rw [h hb₁]]

private theorem evalDist_bind_mono_bool_of_support' {α : Type} (p : ProbComp α)
    (f g : α → ProbComp Bool) (h : ∀ a ∈ support p, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[p >>= f] {true} ≤ 𝒟[p >>= g] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [pure_bind]; exact h a (by simp)
  | query_bind _ _ ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha => h a ?_
    rw [MonadAttach.mem_support_bind]; exact ⟨u, by simp, ha⟩

/-! ### Tracker-halted simulators -/

theorem stepKemFailSend_cand_sticky {F : ShaCompress} (K : MlKem) (tr : KemFailTrackState F)
    (Q : Party) (rq : BitVec 512) {p : Seed × EncRand} (hc : tr.cand = some p) :
    (stepKemFailSend F K tr Q rq).cand = some p := by
  unfold stepKemFailSend; cases (tr.st Q).send K (coinBytes rq) <;> simp [hc]

@[expose] def kemFailSendStepHalted (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (_decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    KemFailSimM PQ Pt P.C.F ℓ (Option (List (BitVec 8))) := do
  let ⟨sC, gh, tr⟩ ← get
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then return none
  match sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let rq ← match r with | some rq => pure rq | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512))
    let tr' := stepKemFailSend P.C.F K tr Q rq
    if tr'.cand.isSome then set (sC, gh, { tr with cand := tr'.cand }); return none
    else kemFailSendStepPostCoin P K ℓ Dh encPt encT idOf lam qep sC gh tr s₁ Q m₀ chal r rq

@[expose] def kemFailSimImplHalted (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      (KemFailSimM PQ Pt P.C.F ℓ) :=
  let base := kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep; let SimM := KemFailSimM PQ Pt P.C.F ℓ
  let c : QueryImpl unifSpec SimM := fun n => base (.inl n)
  let i₁ : QueryImpl ((Party × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8))) SimM :=
    fun ⟨Q, m₀, r⟩ => kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8))) SimM :=
    fun ⟨Q, m₀, m₁, r⟩ => kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) SimM :=
    fun q => base (.inr (.inl (.inl (.inr q))))
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) SimM :=
    fun q => base (.inr (.inl (.inr q)))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) SimM := fun q => base (.inr (.inr q))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

@[expose] def simSendCTrackHalted {M : Type → Type} [Monad M] (P : Params PQ (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (qep : ℕ) (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) (H : Hook Pt ℓ M) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) M (Option (List (BitVec 8))) := do
  let (sC, tr) ← get
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then return none
  match sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let rq ← StateT.lift (H.lift (match r with
      | some rq => pure rq | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512))))
    let tr' := stepKemFailSend P.C.F K tr Q rq
    if tr'.cand.isSome then set (sC, { tr with cand := tr'.cand }); return none
    else
      let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
      let rc : Option (BitVec 256) ← StateT.lift (H.lift (match r with
        | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) | none => pure none))
      match mkPub (P := P) sC.base Q rq pn with
      | none => set (sC, { tr with cand := tr'.cand }); return none
      | some (pq', pub) =>
        let res ← StateT.lift (H.lift (match chal with
          | none => SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
          | some m₁ => SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc))
        match res with
        | none => set (sC, { tr with cand := tr'.cand }); return none
        | some c =>
          let w := toWire c
          let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
          let base' : SimState PQ Pt ℓ := { sC.base with
            mir := s₁.record 3 Q () rec' chal.isSome, pq := Function.update sC.base.pq Q pq',
            pn := Function.update sC.base.pn Q pn, honest := (w, c) :: sC.base.honest }
          let sent' := match (sC.kept Q).full, base'.honest.head? with
            | some st, some (_, c₀) => if st.id.sendsIn (st.tcur + 1) then sC.sent
              else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
            | _, _ => sC.sent
          set ({ sC with base := base', kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)),
                         sent := sent' }, tr')
          return some w

@[expose] def simImplCTrackHalted {M : Type → Type} [Monad M] (P : Params PQ (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) M) :=
  let TrM := StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) M
  let liftS {α : Type} (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M α) : TrM α := do
    let (sC, tr) ← get; let (a, sC') ← StateT.lift (m.run sC); set (sC', tr); return a
  let c : QueryImpl unifSpec TrM := fun n =>
    StateT.lift (H.lift (liftM (query (spec := unifSpec) n : ProbComp _) : Fig8Comp Pt ℓ _))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8))) TrM :=
    fun ⟨Q, m, r⟩ => simSendCTrackHalted P K qep fig H Q m none r
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8))) TrM :=
    fun ⟨Q, m₀, m₁, r⟩ => simSendCTrackHalted P K qep fig H Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) TrM := fun ⟨Q, w⟩ => do
    let (sC, _) ← get
    let j? := sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let res ← liftS (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := H) Q w true))
    match res, j? with
    | some (.accepted _ _ _), some j => modify fun (sC', tr) => (sC', stepKemFailDeliver P.C.F K tr Q j)
    | _, _ => pure ()
    return res
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) TrM := fun ⟨Q, w⟩ =>
    liftS (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs) (H := H) Q w false))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) TrM := fun Q =>
    liftS (guardC (simCorrC (P := P) (encT := encT) (H := H) Dh Q))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

@[expose] def simRunCTrackHaltedWith {M : Type → Type} [Monad M] (P : Params PQ (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) : M Bool := do
  let pqrKey ← H.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  (simulateQ (simImplCTrackHalted P K encT decT qep fig fs H Dh) A).run'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), initKemFailTrack P.C.F pqrKey)

@[expose] def runLibsignalToModularSchemeSimTrackHalted (P : Params PQ (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) : Fig8Comp Pt ℓ Bool :=
  simRunCTrackHaltedWith P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh A

@[expose] def hiddenSaltGameTrackHalted (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) : ProbComp Bool := do
  let b ← $ᵗ Bool; let k ← $ᵗ (BitVec 256 × BitVec 256); let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, gh) ← (simRunCTrackHaltedWith P K encT decT qep fig (lFS P.C P.codec ℓ encT idOf 25000)
    (probeHook fig (qep + 1)) Dh A).run (initState fig k b, false)
  return gh.2

@[expose] noncomputable def hiddenSaltTermTrackHalted (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) : ℝ≥0∞ :=
  𝒟[hiddenSaltGameTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] {true}

@[expose] def simDeliverForgeTrackHalted (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ (BitVec 512) ℓ) :
    DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) :=
  (simRunCTrackHaltedWith P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Dh A).run' []

/-! ### Coin-log send-halted simulator -/

def simSendCHalted {M : Type → Type} [Monad M] (P : Params PQ PQC) {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (H : Hook Pt ℓ M) (badLog : List PQC → Bool)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    StateT (List PQC) (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M)
      (Option (List (BitVec 8))) := do
  let sC ← StateT.lift get
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then return none
  match sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let rq ← StateT.lift (StateT.lift (H.lift (match r with
      | some rq => pure rq | none => liftM ($ᵗ PQC : ProbComp PQC))))
    let log ← get; let log' := log ++ [rq]; set log'
    if badLog log' then pure none
    else StateT.lift do
      let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
      let rc : Option (BitVec 256) ← StateT.lift (H.lift (match r with
        | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) | none => pure none))
      match mkPub (P := P) sC.base Q rq pn with
      | none => return none
      | some (pq', pub) =>
        let res ← StateT.lift (H.lift (match chal with
          | none => SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
          | some m₁ => SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc))
        match res with
        | none => return none
        | some c =>
          let w := toWire c
          let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
          let base' : SimState PQ Pt ℓ := { sC.base with
            mir := s₁.record 3 Q () rec' chal.isSome, pq := Function.update sC.base.pq Q pq',
            pn := Function.update sC.base.pn Q pn, honest := (w, c) :: sC.base.honest }
          let sent' := match (sC.kept Q).full, base'.honest.head? with
            | some st, some (_, c₀) => if st.id.sendsIn (st.tcur + 1) then sC.sent
              else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
            | _, _ => sC.sent
          set { sC with base := base',
                        kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)),
                        sent := sent' }
          return some w

def simImplCHalted {M : Type → Type} [Monad M] (P : Params PQ PQC) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (badLog : List PQC → Bool) (Dh : DHFun (BitVec 256) Pt) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (List PQC) (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M)) :=
  let base := simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs) (H := H) Dh
  let LogM := StateT (List PQC) (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M)
  let c : QueryImpl unifSpec LogM := fun n => StateT.lift (base (.inl n))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8))) LogM :=
    fun ⟨Q, m, r⟩ => simSendCHalted P qep fig H badLog Q m none r
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8))) LogM :=
    fun ⟨Q, m₀, m₁, r⟩ => simSendCHalted P qep fig H badLog Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) LogM :=
    fun q => StateT.lift (base (.inr (.inl (.inl (.inr q)))))
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) LogM :=
    fun q => StateT.lift (base (.inr (.inl (.inr q))))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) LogM := fun q => StateT.lift (base (.inr (.inr q)))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

def simRunCHaltedWith {M : Type → Type} [Monad M] (P : Params PQ PQC) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (badLog : List PQC → Bool) (Dh : DHFun (BitVec 256) Pt)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : M Bool := do
  let pqrKey ← H.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  ((simulateQ (simImplCHalted P encT decT qep fig fs H badLog Dh) A).run' []).run'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))

def hiddenSaltGameHalted (badLog : List PQC → Bool) (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : ProbComp Bool := do
  let b ← $ᵗ Bool; let k ← $ᵗ (BitVec 256 × BitVec 256); let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, gh) ← (simRunCHaltedWith P encT decT qep fig (lFS P.C P.codec ℓ encT idOf 25000)
    (probeHook fig (qep + 1)) badLog Dh A).run (initState fig k b, false)
  return gh.2

noncomputable def hiddenSaltTermHalted (badLog : List PQC → Bool) (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : ℝ≥0∞ :=
  𝒟[hiddenSaltGameHalted badLog P ℓ Dh encPt encT decT idOf lam qep A] {true}

def simDeliverForgeHalted (badLog : List PQC → Bool) (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) :=
  (simRunCHaltedWith P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) badLog Dh A).run' []

/-! ## Bound terms for `hiddenSaltTerm` -/

/-- Computational per-session FS-AEAD deliver-forgery bound across the `fsSlotCount qR` active slots. -/
@[expose] noncomputable def deliverForgeFSCompBound (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ) (R : FsAdv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ k ∈ Finset.range (fsSlotCount qR),
    (chainPRGTerm C codec ℓ encT idOf R (FSAEAD.Thm5.slotToHybridHopIndex qR k) +
      2 * saltPRFTerm C codec ℓ encT idOf qR R (FSAEAD.Thm5.slotToHybridHopIndex qR k) +
      wireOtccaTerm C codec ℓ encT idOf qR qR R (FSAEAD.Thm5.slotToHybridHopIndex qR k))

/-- Per-session FS-AEAD deliver-forgery bound including `4 * macForgeryTerm C qd`. -/
noncomputable def deliverForgeFSBound (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qd : ℕ) (R : FsAdv Pt ℓ) : ℝ≥0∞ :=
  deliverForgeFSCompBound C codec ℓ encT idOf qR R + 4 * macForgeryTerm C qd

end CryptoGames.LibsignalSM.Proofs.Refinement

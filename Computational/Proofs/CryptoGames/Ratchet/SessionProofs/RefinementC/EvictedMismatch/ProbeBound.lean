/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import ProofLib.SepLogic.WP.StateNorm
import LibsignalBinary.Proofs.SpqrV1Sync.NoWrongSalt -- shake: keep
import Computational.Proofs.CryptoGames.AEAD.HKDFProofDefs

/-!
# Evicted salt-mismatch probe: bound and reduction

**Checked by Lean.** Connects the evicted salt-mismatch probe branch (`DeliverProbe`) to the SPQR salt-provenance invariants, the `DeliverForge` reduction, and the `spuriousStepTerm` coin-draw bound when `Q.other` is corrupted after the draw.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

/-! ## No-wrong-salt invariants -/

/-! ## Reduction to `DeliverForge` -/

/-- Steered Fig. 8 record evaluated by `fwdEvictCPure` at `sC.base.mir.epoch Q + 1`. -/
@[expose] def evictedProbeRecord {Pt PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (Dh : DHFun (BitVec 256) Pt)
    (epExp : ℕ → BitVec 256) (c : Fig8C Pt) (w : List (BitVec 8))
    (h : SignalHeader) (salt : Salt) : Fig8C Pt :=
  ((sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)),
    (h.counter.toNat + 1,
      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))

@[expose] def evictedEpochSeed {Pt PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) : Ratchet.RootKey × Pt :=
  ((s_fig8.st Q).root,
    Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))

@[expose] def evictedEpochStep {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) : Ratchet.RootKey × BitVec 256 :=
  let seed := evictedEpochSeed sC s_fig8 Q Dh epExp c
  (rootPRNG P.C.F encPt).up seed.1 seed.2

@[expose] def evictedMessageKey {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (h : SignalHeader) : BitVec 256 :=
  let p₁ := evictedEpochStep P encPt sC s_fig8 Q Dh epExp c
  let step := FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat p₁.2 0 []
  ((lChainPRG P.C.F h.counter.toNat).gen step.1).2

/-- Acceptance of `(ser, tag)` with steered salt `effectiveHkdfSalt32 salt` under `evictedMessageKey` at `sC.base.mir.epoch Q + 1`. -/
@[expose] def EvictedDeliverForgeEvent {Pt PQ PQC : Type} [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt) : Bool :=
  let t := sC.base.mir.epoch Q + 1
  let i := h.counter.toNat + 1
  let T := Dh.dh (epExp c.1.1) Dh.base
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let key := evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h
  (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
    key (i, (t, some T)) ((ser, tag), effectiveHkdfSalt32 salt)).isSome

/-- Outside `inReceiveOnlyEpoch` with counter within `maxForwardJumps`, Fig. 8 `receive` on `evictedProbeRecord` decrypts under `evictedMessageKey`. -/
theorem lFig8_receive_evictedProbeRecord_eq
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)) :
    let t := sC.base.mir.epoch Q + 1
    let i := h.counter.toNat + 1
    let T := Dh.dh (epExp c.1.1) Dh.base
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let p₁ := evictedEpochStep P encPt sC s_fig8 Q Dh epExp c
    let step := FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat p₁.2 0 []
    let gen := (lChainPRG P.C.F h.counter.toNat).gen step.1
    let v' : RatchetReceiverState (BitVec 256) (BitVec 256) := ⟨gen.1, i, step.2⟩
    (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (evictedProbeRecord sC Q Dh epExp c w h salt) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h)
        (i, (t, some T)) ((ser, tag), effectiveHkdfSalt32 salt)).map
        (fun pm =>
          ({ (s_fig8.st Q) with
              root := p₁.1,
              vR := Function.update (s_fig8.st Q).vR t (some v'),
              γ := .pub T,
              tcur := t },
            t, i, pm)) := by
  dsimp only
  have hsim := hinv.hsim
  have hst_id : (s_fig8.st Q).id = Q := hsim.hst_id Q
  have htcur : (s_fig8.st Q).tcur = sC.base.mir.epoch Q := hsim.htcur Q
  have hQ_recv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
    sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  rcases hsim.hspur Q with ⟨_, _, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw with ⟨hγ_Q, _, _, _, _⟩
  unfold lFig8 SM.Construction.scheme SM.Construction.receive lFS dhScheme
    evictedProbeRecord evictedMessageKey evictedEpochStep evictedEpochSeed
  dsimp only
  rw [htcur]
  have hcond1 :
      ((s_fig8.st Q).id.sendsIn (sC.base.mir.epoch Q + 1) ||
        decide (sC.base.mir.epoch Q + 1 < sC.base.mir.epoch Q + 1)) = false := by
    rw [hst_id, hQ_recv]
    simp
  simp only [hcond1, Bool.false_eq_true, ↓reduceIte, hγ_Q, Function.update_self]
  unfold FSAEAD.fromAEADPRG
  dsimp only
  have hlk : ([] : List (ℕ × BitVec 256)).lookup (h.counter.toNat + 1) = none := rfl
  have hcond_false :
      ¬ (h.counter.toNat + 1 ≤ 0 ∨ 25000 < h.counter.toNat + 1 - 0 - 1) := by
    intro hbad
    rcases hbad with hle | hgt
    · omega
    · exact hbound (Or.inl (by omega))
  have hsub1 : h.counter.toNat + 1 - 0 - 1 = h.counter.toNat := by omega
  have hsub2 : h.counter.toNat + 1 - 1 = h.counter.toNat := by omega
  rw [hlk, ite_eq_right hcond_false, hsub1, hsub2]
  cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
      ((lChainPRG P.C.F h.counter.toNat).gen
        (FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat
          ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root
            (Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))).2 0 []).1).2
      (h.counter.toNat + 1, (sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)))
      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) with
  | none => rfl
  | some pm =>
    simp [Function.update_idem]

/-- Fig. 8 `receive` accepts `evictedProbeRecord` iff `EvictedDeliverForgeEvent` holds. -/
theorem lFig8_receive_evictedProbeRecord_isSome_eq_deliverForgeEvent
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)) :
    ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (evictedProbeRecord sC Q Dh epExp c w h salt)).isSome =
      EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h salt := by
  rw [lFig8_receive_evictedProbeRecord_eq P Inv Dh encPt encT idOf lam qep q r x₀
    s_R sC s_fig8 ec winBefore epExp hinv Q c w h salt hinw hbound]
  unfold EvictedDeliverForgeEvent
  exact Option.isSome_map

/-! ## Spurious-step coin bound -/

theorem skipKeys_lChainPRG_fst (F : ShaCompress) (k : ℕ) (w : BitVec 256) (p : ℕ)
    (dict : List (ℕ × BitVec 256)) :
    (FSAEAD.skipKeys (lChainPRG F) k w p dict).1 =
      (List.range k).foldl (fun key _ => (hmacPRF F).tag key Ratchet.chainKeySeed) w := by
  induction k generalizing w p dict with
  | zero => rfl
  | succ k ih =>
    dsimp only [FSAEAD.skipKeys, lChainPRG]
    rw [ih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

theorem evictedEpochStep_eq_spurPRG {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hrk : (s_fig8.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1) :
    evictedEpochStep P encPt sC s_fig8 Q Dh epExp c =
      (evictedKeySpuriousStepPrg P.C.F encPt Dh rk_base T_base (epExp c.1.1)).gen
        (epExp (sC.base.mir.epoch Q)) := by
  unfold evictedEpochStep evictedEpochSeed evictedKeySpuriousStepPrg Ratchet.rootPRNG
  dsimp only
  rw [hrk]

theorem evictedMessageKey_keyToBytes32_eq {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (h : SignalHeader) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hrk : (s_fig8.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1) :
    let p₁ := (evictedKeySpuriousStepPrg P.C.F encPt Dh rk_base T_base (epExp c.1.1)).gen
      (epExp (sC.base.mir.epoch Q))
    let ck := (List.range h.counter.toNat).foldl
      (fun k _ => (hmacPRF P.C.F).tag k Ratchet.chainKeySeed) p₁.2
    keyToBytes32 (evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h) =
      Ratchet.chainHmac P.C.F ck Ratchet.messageKeySeed := by
  unfold evictedMessageKey
  dsimp only [lChainPRG]
  rw [evictedEpochStep_eq_spurPRG P encPt sC s_fig8 Q Dh epExp c rk_base T_base hrk,
    skipKeys_lChainPRG_fst]
  exact keyToBytes32_hmacPRF_tag P.C.F _ Ratchet.messageKeySeed

/-- Outside `inReceiveOnlyEpoch` with `(s_fig8.st Q).root` from `Q`'s eager step, `EvictedDeliverForgeEvent` implies `spurBadSingle`. -/
theorem evictedDeliverForgeEvent_implies_spurBadSingle
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [DecidableEq PQ]
    [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
    (salt : Salt) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hrk : (s_fig8.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hw32 : w.length < 2 ^ 32)
    (hevent : EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h salt = true) :
    spurBadSingle P encPt Dh Q rk_base T_base w salt (epExp c.1.1)
      (epExp (sC.base.mir.epoch Q)) = true := by
  have hrecv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
    sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  have hlids : lIds idOf (sC.base.mir.epoch Q + 1) = macIds (idOfP P Q.other) (idOfP P Q) :=
    lIds_eq_macIds_of_not_sendsIn P idOf hid Q (sC.base.mir.epoch Q + 1) hrecv
  have hkey := evictedMessageKey_keyToBytes32_eq P encPt sC s_fig8 Q Dh epExp c h
    rk_base T_base hrk
  dsimp only at hkey
  unfold EvictedDeliverForgeEvent AEADScheme.movePubPartToAD lPubOf lAead lAeadK lWire
    libsignalWireAead libsignalReceiveWire at hevent
  simp only [hparse, Option.map_some, ne_eq, not_true_eq_false, ↓reduceIte] at hevent
  unfold spurBadSingle
  simp only [hparse, hw32, ↓reduceIte]
  rw [← hlids, ← hkey, msgKeys_effSalt]
  by_cases hmac :
      ((hmacScheme P.C.F).tag
        (deriveMessageKeys P.C.F (some (effectiveHkdfSalt32 salt))
          (keyToBytes32 (evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h))).2
        ((lIds idOf (sC.base.mir.epoch Q + 1)).toList ++ w.take (w.length - 8)) ==
          bytesToWord64LE (w.drop (w.length - 8))) = true
  · exact hmac
  · simp [hmac] at hevent

/-- Bounds the probability of `spurBadList` over at most `q * qep` pre-fixed triples by `spuriousStepTerm`. -/
theorem spurBadList_prob_le_spuriousStepTerm
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
    [SampleableType PQC]
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (Q : Party) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (q qep : ℕ) (L : List (List (BitVec 8) × Salt × BitVec 256))
    (hL : L.length ≤ q * qep) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {x | spurBadList P encPt Dh Q rk_base T_base L x = true} ≤
      spuriousStepTerm P.C.F encPt Dh q qep := by
  rw [spurBound_eq_mul_spurUnit]
  refine (spurBadList_prob_le P encPt Dh Q rk_base T_base L).trans ?_
  gcongr

end CryptoGames.LibsignalSM.Proofs.Refinement


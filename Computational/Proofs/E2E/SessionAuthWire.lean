/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthWireEnd

/-!
# Wire-side FS-AEAD session hybrid and libsignal real-to-ideal session bound-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal CryptoGames.Lazy
open CryptoGames CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5 CryptoGames.FSAEAD.Thm5.Ends

namespace CryptoVerification.E2E.Signed.SessionWire

open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
open CryptoVerification.E2E.Signed CryptoVerification.E2E.Signed.SessionRouter
open CryptoVerification.E2E.Signed.SessionFS CryptoVerification.E2E.Signed.SessionFSMix
open CryptoVerification.E2E.Signed.SessionMac

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 2. Reversed chain-PRG hops on mixtures (`hp N t₀ la → hp 0 t₀ la`) -/

section ReversedChainOut

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-- `cumulativeChainPrgReductionOut` at an arbitrary AEAD ideal cutoff `t₀` (`t₀ = 0` on the salt
side, `t₀ = N` when reversing the chain-PRG hops on the ideal wire side). -/
@[expose] def cumulativeChainPrgReductionAtOut (ideal : ℕ × AD → ProbComp C)
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (t₀ j : ℕ) (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) : PRGScheme.PRGAdversary (CK × MK) := fun mt =>
  hRunOut ideal ae G maxSkip (hp (j / 2) t₀ (isLookaheadHop j)) (DG G)
    (none : Option (SpecialOps AD M C ProbComp)) F A (.mat (j / 2) mt)

@[simp] theorem cumulativeChainPrgReductionAtOut_zero (ideal : ℕ × AD → ProbComp C)
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip j : ℕ)
    (F : Bool → HState CK MK AD M C → Bool) (A : RatchetAdversary CK MK AD M C) :
    cumulativeChainPrgReductionAtOut ideal ae G maxSkip 0 j F A =
      cumulativeChainPrgReductionOut ideal ae G maxSkip j F A := rfl

private theorem hRunOut_eq (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) (P : Params)
    (D : ℕ → ProbComp (CK × MK)) (sl : Slot CK MK) :
    hRunOut ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) F A sl =
      ($ᵗ Bool : ProbComp Bool) >>= fun b =>
        (fun z => F z.1 z.2.1) <$>
          (simulateQ (implWith ideal ae G maxSkip P D none) A).run (hInit b sl) := by
  simp only [hRunOut, map_eq_bind_pure_comp]
  rfl

private theorem out_fill (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) (P : Params)
    (D : ℕ → ProbComp (CK × MK))
    {fill : HState CK MK AD M C → Slot CK MK → ProbComp (Slot CK MK)} (hI : Idem fill)
    (hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length → fill h = fill h')
    (hGen : Comm fill (genStep G P D : StateT (HSt CK MK AD M C) ProbComp Unit))
    (hRev : Comm fill (reveal : StateT (HSt CK MK AD M C) ProbComp CK))
    (s : HSt CK MK AD M C) :
    DEq ((fun z => F z.1 z.2.1) <$> (fillSt fill s >>=
        (simulateQ (implWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)))
          A).run))
      ((fun z => F z.1 z.2.1) <$> (simulateQ (implWith ideal ae G maxSkip P D none) A).run s) := by
  have hc := Comm.simulateQ hI (comm_impl ideal ae G maxSkip P D hI hK hGen hRev) A s
  exact (map_fillOut (fill := fill) F _).symm.trans
    ((DEq.map hc _).trans (map_fillOut (fill := fill) F _))

private theorem out_L2_gen (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) (k t₀ : ℕ) (la : Bool) (b : Bool) :
    DEq ((fun z => F z.1 z.2.1) <$> (simulateQ (implWith ideal ae G maxSkip (hp k t₀ la) DU
        (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown))
      ((fun z => F z.1 z.2.1) <$> (simulateQ (implWith ideal ae G maxSkip (hp (k + 1) t₀ la)
        (DG G) (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown)) := by
  have hI := seedFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1)
  have hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length →
      seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1) h =
        seedFill (k + 1) h' := by
    intro h h' hl; funext sl; cases sl <;> simp [seedFill, hl]
  have hr := Rel.simulateQ hI (fun t => (rc_impl_L2_gen ideal ae G maxSkip k t₀ la hI hK t).1)
    (fun t => (rc_impl_L2_gen ideal ae G maxSkip k t₀ la hI hK t).2) A (hInit b .unknown)
  have h0 : fillSt (seedFill (k + 1)) (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
      b .unknown) = pure (hInit b .unknown) := by
    simp [fillSt, seedFill, hInit]
  rw [h0, pure_bind, pure_bind] at hr
  exact (DEq.map hr _).trans (map_fillOut (fill := seedFill (k + 1)) F _)

private theorem hRunOut_mat_eq (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (F : Bool → HState CK MK AD M C → Bool)
    (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK))
    (A : RatchetAdversary CK MK AD M C) (pos : ℕ) (mt : CK × MK) :
    hRunOut ideal ae G maxSkip P D₁ (none : Option (SpecialOps AD M C ProbComp)) F A (.mat pos mt) =
      hRunOut ideal ae G maxSkip P D₂ (none : Option (SpecialOps AD M C ProbComp)) F A
        (.mat pos mt) := by
  unfold hRunOut
  refine bind_congr fun b => ?_
  exact eqKnown_simulateQ ideal ae G maxSkip P D₁ D₂ A (hInit b (.mat pos mt)) _ _
    (by simp [hInit]) (fun _ _ => rfl)

end ReversedChainOut

/-! ## 3. Symmetric wire-side router hybrid on mixtures (`fsWireHyb`) -/

section WireRouter

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  {α : Type} (oa : ProbComp α) (ae : α → AEADScheme MK (ℕ × AD) M C)
  (N : ℕ) (la : Bool) {S : Type}
  (O : α → QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
  (initS : α → ProbComp (ℕ → S))
  (Adv : α → OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool)

/-- Wire-side session adversary for session `k` (target parameter `P`, e.g. `hp N N la` or
`hp 0 N la`): forwards session `k`, simulates sessions `< k` on `fsImpl … P` and sessions `> k` on
the slot side `fsSlotImpl … (O o)`, each started lazily. -/
@[expose] def fsWireSessAdv (ae₀ : AEADScheme MK (ℕ × AD) M C) (P : Params)
    (O₀ : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) (initS₀ : ProbComp (ℕ → S))
    (A : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool) (k : ℕ) :
    RatchetAdversary CK MK AD M C :=
  sessAdv
    (lazyInit (fsSlotInit initS₀) (fsSlotImpl ideal ae₀ G maxSkip N la O₀))
    (lazyInit fsInit (fsImpl ideal ae₀ G maxSkip P))
    A (fun _ => none) (fun _ => none) k

/-- Wire-side router hybrid `j` on mixtures (target parameter `P`): sample `o ← oa`, then run
`Adv o` with sessions `< j` on `fsImpl … P` and sessions `≥ j` on the slot side
`fsSlotImpl … (O o)`, every session started lazily. -/
@[expose] def fsWireHyb (P : Params) (j : ℕ) : ProbComp Bool := do
  let o ← oa
  Prod.fst <$> (simulateQ (hybSess
    (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o)))
    (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip P)) j)
    (Adv o)).run ((fun _ => none), (fun _ => none))

/-- Wire hybrid `0` (`hAR`): every session runs the slot side `fsSlotImpl … (O o)`. -/
theorem fsWireHyb_zero (P : Params) :
    𝒟[fsWireHyb ideal G maxSkip oa ae N la O initS Adv P 0] =
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o))))
          (Adv o)).run (fun _ => none)] := by
  unfold fsWireHyb
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [hybSess_zero, Functor.map_map]

/-- Wire hybrid `j` is session `j`'s wire session adversary against a fresh slot-side session. -/
theorem fsWireHyb_left (P : Params) (j : ℕ) :
    𝒟[fsWireHyb ideal G maxSkip oa ae N la O initS Adv P j] =
      𝒟[oa >>= fun o => fsSlotInit (initS o) >>= fun s => Prod.fst <$>
        (simulateQ (fwd (fsSlotImpl ideal (ae o) G maxSkip N la (O o)))
          (fsWireSessAdv ideal G maxSkip N la (ae o) P (O o) (initS o) (Adv o) j)).run s] := by
  unfold fsWireHyb fsWireSessAdv
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [← (lazyInit_run_none (fsSlotInit (initS o))
    (fsSlotImpl ideal (ae o) G maxSkip N la (O o)) _).evalDist_eq]
  exact congrArg evalDist (sessAdv_left_eq
    (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o)))
    (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip P))
    (Adv o) (fun _ => none) (fun _ => none) j).symm

/-- Wire-side left endpoint (`hEL`). Wire hybrid `j` is `E j = multiSlotOtccaReductionOut …
(fsWireSessAdv … j)` run against the slot world `slotLift (O o)`. -/
theorem fsWireHyb_slot_eq (P : Params) (j : ℕ) :
    𝒟[fsWireHyb ideal G maxSkip oa ae N la O initS Adv P j] =
      𝒟[oa >>= fun o => initS o >>= fun σ => Prod.fst <$> (simulateQ (slotLift (O o))
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit
          (fsWireSessAdv ideal G maxSkip N la (ae o) P (O o) (initS o) (Adv o) j))).run σ] := by
  rw [fsWireHyb_left, fsSlot_mix_eq]

/-- Wire hybrid `j + 1` is session `j`'s wire session adversary against a fresh `fsImpl … P`
session. -/
theorem fsWireHyb_right (P : Params) (j : ℕ) :
    𝒟[fsWireHyb ideal G maxSkip oa ae N la O initS Adv P (j + 1)] =
      𝒟[oa >>= fun o => fsInit >>= fun s => Prod.fst <$>
        (simulateQ (fwd (fsImpl ideal (ae o) G maxSkip P))
          (fsWireSessAdv ideal G maxSkip N la (ae o) P (O o) (initS o) (Adv o) j)).run s] := by
  unfold fsWireHyb fsWireSessAdv
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [← (lazyInit_run_none fsInit (fsImpl ideal (ae o) G maxSkip P) _).evalDist_eq]
  exact congrArg evalDist (sessAdv_right_eq
    (lazyInit (fsSlotInit (initS o)) (fsSlotImpl ideal (ae o) G maxSkip N la (O o)))
    (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip P))
    (Adv o) (fun _ => none) (fun _ => none) j).symm

/-- Bridge B on `fsWireHyb` at `P = hp N N la`: hybrid `j + 1` equals `multiOtBranch true N`
against `multiSlotOtccaReductionOut … (fsWireSessAdv … (hp N N la) … j)` with zero slack. -/
theorem fsWireHyb_succ_eq_multiOtBranch (j : ℕ) :
    𝒟[fsWireHyb ideal G maxSkip oa ae N la O initS Adv (hp N N la) (j + 1)] =
      𝒟[oa >>= fun o => multiOtBranch ideal (ae o) true N
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit
          (fsWireSessAdv ideal G maxSkip N la (ae o) (hp N N la) (O o) (initS o) (Adv o) j))] := by
  rw [fsWireHyb_right, ← fsIdeal_mix_eq]

/-- Wire-side right endpoint (`hER`) at `P = hp N N la` (`post j = 0`). -/
theorem fsWireHyb_step_le_zero (j : ℕ) :
    𝒟[oa >>= fun o => multiOtBranch ideal (ae o) true N
        (multiSlotOtccaReductionOut ideal (ae o) G maxSkip N la advBit
          (fsWireSessAdv ideal G maxSkip N la (ae o) (hp N N la) (O o) (initS o) (Adv o) j))].boolDist
      𝒟[fsWireHyb ideal G maxSkip oa ae N la O initS Adv (hp N N la) (j + 1)] ≤ 0 := by
  rw [fsWireHyb_succ_eq_multiOtBranch, Measure.boolDist_self]

/-- Wire hybrid `q`: every session runs `fsImpl … P`, when every `Adv o` stays in sessions
`< q`. -/
theorem fsWireHyb_of_offRange (P : Params) (q : ℕ)
    (hoff : ∀ o, (Adv o).IsQueryBoundP (fun t => sessOffRange q t = true) 0) :
    𝒟[fsWireHyb ideal G maxSkip oa ae N la O initS Adv P q] =
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl ideal (ae o) G maxSkip P))) (Adv o)).run (fun _ => none)] := by
  unfold fsWireHyb
  refine evalDist_bind_congr oa _ _ fun o => ?_
  rw [hybSess_eq_sessLift_of_offRange _ _ q (Adv o) (hoff o), Functor.map_map]

end WireRouter

/-! ## 4. The libsignal instance: real-to-ideal FS-AEAD session hybrid -/

section Libsignal

open CryptoGames.LibsignalSM.Proofs CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoGames.LibsignalSession CryptoGames.LibsignalSM.Proofs.SaltHopKeyed
open CryptoGames.LibsignalSM.Proofs.WireHop CryptoVerification.E2E.Signed.FSMix
open CryptoVerification.E2E.Signed.SessionHybrid CryptoVerification.E2E.Signed.SessionFSMix
open CryptoVerification.E2E.Signed.SessionMac
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto)
  (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α)
  (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
  (Adv : α → OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) Bool)

/-- Session `j`'s wire-side session adversary in the libsignal chain (sessions `< j` at target `P`,
sessions `> j` on the `slotSaltImplNF` slot side). -/
abbrev lWireSessAdv (P : Params) (o : α) (j : ℕ) :
    RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32 :=
  fsWireSessAdv (lIdeal C codec ℓ encT) (lChainPRG C.F) maxSkip N la
    (lAeadR C codec ℓ encT (idOf o)) P
    (slotSaltImplNF C codec ℓ encT (idOf o) false)
    (pure fun _ => ({} : SaltSlotSt Pt)) (Adv o) j

/-- Session `j`'s wire-side reduction `E j` (target `P`): the multi-slot OT-CCA reduction (output
"the adversary's bit") of `lWireSessAdv … P o j`. -/
abbrev lWireE (P : Params) (j : ℕ) (o : α) :
    OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32 :=
  multiSlotOtccaReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
    (lChainPRG C.F) maxSkip N la advBit
    (lWireSessAdv C codec ℓ encT idOf maxSkip N la Adv P o j)

/-- Combined libsignal FS-AEAD session hybrid (`hp 0 0 la` → `hp N N la`, `post = 0`).

Bounds the Boolean distance between the all-real FS-AEAD session mixture (`hp 0 0 la`) and the
all-ideal FS-AEAD session mixture (`hp N N la`, which equals `hpIdeal N la` under per-session query
bounds via `allSessions_hp_eq_hpIdeal_main` / `allSessions_hp_eq_hpIdeal_la`) by:
* `q` per-session salt-side terms (`lSaltPre j` + salt-PRF terms of `lSaltD j`),
* **one** global MAC-forgery term `qd · macForgeryProb C.F` across all sessions (`lMacAdv`), and
* `q` per-session wire OT-CCA terms (`lWireE … (hp N N la) j`), with zero wire-side slack. -/
theorem sessionHybrid_fs_real_to_ideal_mix_le (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hN : N ≤ 2 ^ 32) (q : ℕ)
    (hoffAdv : ∀ o, (Adv o).IsQueryBoundP (fun t => sessOffRange q t = true) 0)
    {qd : ℕ}
    (hqdA : ∀ o, MakesAtMostDecQueries (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o) qd)
    (hshortA : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB)
      (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o))
    (hdecA : ∀ o, GuardedOTDecShort (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o))
    (hclsE : ∀ j o, AEADScheme.OTAllQueriesInOneADClass lCls
      (lWireE C codec ℓ encT idOf maxSkip N la Adv (hp N N la) j o))
    (hshortE : ∀ j o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB)
      (lWireE C codec ℓ encT idOf maxSkip N la Adv (hp N N la) j o)) :
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip (hp 0 0 la)))) (Adv o)).run (fun _ => none)].boolDist
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip (hp N N la)))) (Adv o)).run (fun _ => none)] ≤
      (∑ j ∈ Finset.range q,
        (lSaltPre C codec ℓ encT oa idOf maxSkip N la Adv j +
          ∑ k ∈ Finset.range N, 2 * (lSaltPRF32 C.F).prfAdvantage
            (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
              (slotSaltRed C codec ℓ encT (idOf o) N k
                (lSaltD C codec ℓ encT idOf maxSkip N la Adv j o))))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F +
      ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range N, (lWire C codec ℓ).wireOtccaAdvantage
          (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
            (slotWireRed C codec ℓ encT (idOf o) k
              (lWireE C codec ℓ encT idOf maxSkip N la Adv (hp N N la) j o))) := by
  let Hw := fsWireHyb (lIdeal C codec ℓ encT) (lChainPRG C.F) maxSkip oa
    (fun o => lAeadR C codec ℓ encT (idOf o)) N la
    (fun o => slotSaltImplNF C codec ℓ encT (idOf o) false)
    (fun _ => pure fun _ => ({} : SaltSlotSt Pt)) Adv (hp N N la)
  rw [← fsWireHyb_of_offRange (lIdeal C codec ℓ encT) (lChainPRG C.F) maxSkip oa
    (fun o => lAeadR C codec ℓ encT (idOf o)) N la
    (fun o => slotSaltImplNF C codec ℓ encT (idOf o) false)
    (fun _ => pure fun _ => ({} : SaltSlotSt Pt)) Adv (hp N N la) q hoffAdv]
  have h := sessionHybrid_fs_mac_mix_le C codec ℓ encT oa idOf maxSkip N la Adv
    hrt hfit hℓ hinj hdum q Hw hoffAdv hqdA hshortA hdecA
    (fsWireHyb_zero _ _ _ oa _ N la _ _ Adv (hp N N la))
    (fun _ => N) (fun _ => hN)
    (lWireE C codec ℓ encT idOf maxSkip N la Adv (hp N N la))
    (fun j o => multiSlotOtccaReductionOut_offRange _ _ _ _ N la advBit _)
    hclsE hshortE (fun _ => 0)
    (fun j _ => (fsWireHyb_slot_eq _ _ _ oa _ N la _ _ Adv (hp N N la) j).trans
      (by simp only [pure_bind]))
    (fun j _ => fsWireHyb_step_le_zero _ _ _ oa _ N la _ _ Adv j)
  simpa only [add_zero] using h

end Libsignal

end CryptoVerification.E2E.Signed.SessionWire


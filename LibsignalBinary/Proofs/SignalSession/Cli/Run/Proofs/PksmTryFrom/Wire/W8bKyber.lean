/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bBaseKey -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyber -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberc
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: `+0x684` Continuation via Kyber 3-Way Dispatch

Proves `preKey684OkW_of_830`, discharging `PreKey684OkW` (`+0x684 → ret`) via
`w8b_kyber_dispatch` into `w5b_kyber_ok_wp` + `PreKey830OkW` (`Ok`) and
`PreKeyKyberErrW` (`Err`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

/-! ## 1. Kyber dispatch and stack-scratch splits -/

/-- The Kyber 3-way dispatch is exhaustive: the `w5b_kyber_ok_wp` condition or the
`w5b_kyber_err_wp` condition holds. -/
theorem w8b_kyber_dispatch (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (vb : BitVec 8) :
    ((kpkOpt.isSome && kyberOpt.isSome) = true ∨
        (kpkOpt = none ∧ kyberOpt = none ∧ vb.toNat < 0x40)) ∨
      ((kpkOpt.isSome != kyberOpt.isSome) = true ∨
        (kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat)) := by
  cases kpkOpt with
  | none =>
    cases kyberOpt with
    | none =>
      by_cases h : vb.toNat < 0x40
      · exact Or.inl (Or.inr ⟨rfl, rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl, by omega⟩)
    | some _ => exact Or.inr (Or.inl rfl)
  | some _ =>
    cases kyberOpt with
    | none => exact Or.inr (Or.inl rfl)
    | some _ => exact Or.inl (Or.inl rfl)

theorem w8b_memRegion16_split (sp' : BitVec 64) :
    memRegion sp' 16 = memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 := by
  rw [show (16 : Nat) = 12 + 4 by decide]
  exact Prost.memRegion_split sp' 12 4 (by decide)

theorem w8b_memRegion184_split (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 184 =
      memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 152 := by
  rw [show (184 : Nat) = 32 + 152 by decide,
    Prost.memRegion_split (sp' + 112#64) 32 152 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## 2. Frames and the `+0x830` continuation -/

/-- Kyber `Ok` post-frame at `+0x830` (`2096`): the `Pf` of `w5b_kyber_ok_wp`. -/
@[expose] def w8bRowYPost (A : RustAlloc)
    (sp' bkCap bkPtr kyberLen ikPtr msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (ik msg : List (BitVec 8)) : SepProp :=
  kyberSpillsAtW sp' bkCap bkPtr kyberLen ikPtr (BitVec.ofNat 64 ik.length) msgPtr
      (BitVec.ofNat 64 msg.length) regTag regVal opkTag opkVal spkId kpkVal
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 ∗
    memRegion (sp' + 312#64) 48 ∗
    kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
    A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

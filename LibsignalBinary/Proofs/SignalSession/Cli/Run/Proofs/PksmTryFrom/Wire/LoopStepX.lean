/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArms -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKey
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Int32Arms
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArm

/-!
# `PreKeySignalMessage::try_from`: Protobuf Field-Merge Dispatch and Decode Loop

Combines the 8-way tag dispatch, `int32::merge`, `bytes::merge`, and `skip_field` arms into
`mergePreKeyField_cps`, single-iteration `preKeyStep_wp`, and fuel-inducted `preKeyDecodeLoop_ok` /
`preKeyDecodeLoopF4_ok`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

theorem L1_IS5Wire_LoopStep : True := trivial

/-! ## 1. Pure model lemmas -/

/-- `Pksm.mergeProtoField` returns a suffix of its input (analog of `Wire.mergeField_suffix`). -/
theorem mergePreKeyField_suffix {m m' : ProtoPreKeySignalMessage} {tag : Nat} {wt : WireType}
    {bs rest : List (BitVec 8)} (h : Pksm.mergeProtoField m tag wt bs = some (m', rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold Pksm.mergeProtoField at h
  split at h
  case h_1 | h_5 | h_6 | h_7 =>
    obtain ⟨⟨v, r⟩, hm, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact mergeUint32_suffix hm
  case h_2 | h_3 | h_4 | h_8 =>
    obtain ⟨⟨v, r⟩, hm, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    obtain ⟨k, hk, hr, -⟩ := mergeBytes_suffix hm
    exact ⟨k, hk, hr⟩
  case h_9 =>
    obtain ⟨r, hs, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact skipField_suffix hs

/-- Fuel monotonicity: any two fuels `≥ bs.length` give the same `Pksm.decodeProtoLoop` result. -/
theorem decodePreKeyLoop_fuel_mono :
    ∀ (fuel fuel' : Nat) (m : ProtoPreKeySignalMessage) (bs : List (BitVec 8)),
      bs.length ≤ fuel → bs.length ≤ fuel' →
      Pksm.decodeProtoLoop fuel m bs = Pksm.decodeProtoLoop fuel' m bs
  | _, _, _, [], _, _ => by simp [Pksm.decodeProtoLoop]
  | 0, _, _, _ :: _, h, _ => by simp at h
  | _ + 1, 0, _, _ :: _, _, h => by simp at h
  | fuel + 1, fuel' + 1, m, b0 :: bs1, h, h' => by
    simp only [Pksm.decodeProtoLoop]
    cases hdk : decodeKey (b0 :: bs1) with
    | none => rfl
    | some p =>
      obtain ⟨⟨tag, wt⟩, rest⟩ := p
      obtain ⟨k, hk1, hkl, hr, -, -⟩ := Wire.decodeKey_suffix hdk
      dsimp only
      cases hmf : Pksm.mergeProtoField m tag wt rest with
      | none => rfl
      | some q =>
        obtain ⟨m', rest'⟩ := q
        obtain ⟨k2, hk2, hr2⟩ := mergePreKeyField_suffix hmf
        dsimp only
        have hlen : rest'.length ≤ bs1.length := by
          rw [hr2, hr, List.length_drop, List.length_drop]
          simp only [List.length_cons]
          omega
        simp only [List.length_cons] at h h'
        exact decodePreKeyLoop_fuel_mono fuel fuel' m' rest' (by omega) (by omega)

/-! ## 2. `mergePreKeyField_cps`: dispatch `+0x170` → arms → `+0x0e4` / `+0x460` -/

private theorem sepWPp_to_proofLib {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    ProofLib.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq, _⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

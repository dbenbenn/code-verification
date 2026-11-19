/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Dispatch
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff /-! ## Prologue + `bl spqr::decode_state` (`0x3085c -> 0x5349c`) -/
theorem memRegion_190_1f20_split_states_from_pb (fsp : BitVec 64) :
    memRegion (fsp + 0x190#64) (0x1f20 - 0x190) =
      memRegion (fsp + 0x190#64) (0x1260 - 0x190) ∗
      memRegion (fsp + 0x1260#64) 928 ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) := by
  rw [ProofLib.memRegion_split' (b := fsp + 0x190#64) (n := 0x1260 - 0x190) (k := 0x1f20 - 0x1260)
        (b' := fsp + 0x1260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 928) (k := 0x1f20 - 0x1600)
        (b' := fsp + 0x1600#64) rfl (by bv_omega) (by decide)]

theorem memRegion_b0_rejoin_190 (fsp : BitVec 64) :
    memRegion (fsp + 0xb0#64) Drop.optProtoInnerStateSize ∗
      memRegion (fsp + 0x190#64) (0x1260 - 0x190) =
      memRegion (fsp + 0xb0#64) (0x1260 - 0xb0) := by
  unfold Drop.optProtoInnerStateSize
  rw [← ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 224) (k := 0x1260 - 0x190)
        (b' := fsp + 0x190#64) rfl (by bv_omega) (by decide)]

theorem memRegion_b0_1260_split_930_950 (fsp : BitVec 64) :
    memRegion (fsp + 0xb0#64) (0x1260 - 0xb0) =
      memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      memRegion (fsp + 0x930#64) 24 ∗
      memRegion (fsp + 0x948#64) 8 ∗
      memRegion (fsp + 0x950#64) 928 ∗
      memRegion (fsp + 0xcf0#64) (0x1260 - 0xcf0) := by
  rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 0x930 - 0xb0) (k := 0x1260 - 0x930)
        (b' := fsp + 0x930#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x930#64) (n := 24) (k := 0x1260 - 0x948)
        (b' := fsp + 0x948#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x948#64) (n := 8) (k := 0x1260 - 0x950)
        (b' := fsp + 0x950#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x950#64) (n := 928) (k := 0x1260 - 0xcf0)
        (b' := fsp + 0xcf0#64) rfl (by bv_omega) (by decide)]

theorem memRegion_b0_950_and_cf0_1f20_rejoin (fsp : BitVec 64) :
    (memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      memRegion (fsp + 0x930#64) 24 ∗
      memRegion (fsp + 0x948#64) 8) ∗
    (memRegion (fsp + 0xcf0#64) (0x1260 - 0xcf0) ∗
      memRegion (fsp + 0x1260#64) 928 ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600)) =
    memRegion (fsp + 0xb0#64) (0x950 - 0xb0) ∗
    memRegion (fsp + 0xcf0#64) (0x1f20 - 0xcf0) := by
  have h1 :
      memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
        memRegion (fsp + 0x930#64) 24 ∗
        memRegion (fsp + 0x948#64) 8 =
      memRegion (fsp + 0xb0#64) (0x950 - 0xb0) := by
    rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 0x930 - 0xb0) (k := 32)
          (b' := fsp + 0x930#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x930#64) (n := 24) (k := 8)
          (b' := fsp + 0x948#64) rfl (by bv_omega) (by decide)]
  have h2 :
      memRegion (fsp + 0xcf0#64) (0x1260 - 0xcf0) ∗
        memRegion (fsp + 0x1260#64) 928 ∗
        memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) =
      memRegion (fsp + 0xcf0#64) (0x1f20 - 0xcf0) := by
    rw [ProofLib.memRegion_split' (b := fsp + 0xcf0#64) (n := 0x1260 - 0xcf0) (k := 0x1f20 - 0x1260)
          (b' := fsp + 0x1260#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 928) (k := 0x1f20 - 0x1600)
          (b' := fsp + 0x1600#64) rfl (by bv_omega) (by decide)]
  rw [h1, h2]

/-! ## Early-Return Bridge to `SepWPp` -/

/-- Lift a non-panicking early-return `SepWP` reaching `s0.readReg64 .x30` into a `SepWPp`
    satisfying a target postcondition `post` implied by the restored frame. -/
theorem sepWPp_of_early_return {prog : Program} {s0 s : State} {P P_out : SepProp}
    {post onPanic : State → SepProp → Prop}
    (h : SepWP prog (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢ P_out) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace))
    (hpost : ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      (Pf ⊢ P_out) → sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
      post sf Pf) :
    SepWPp prog (s0.readReg64 .x30) s P post onPanic := by
  refine SepWPp.of_sepWP (SepWP.mono h ?_)
  intro sf Pf hpc hrun ⟨hPf, hsp, hcc, htr⟩
  exact SepWPp.done hpc hrun (hpost sf Pf hpc hrun hPf hsp hcc htr)

end CryptoVerification.SpqrV1.Top.Send

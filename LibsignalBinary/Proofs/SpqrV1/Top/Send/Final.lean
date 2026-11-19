/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1 -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Dispatch
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk

/-!
# Phase 1 Entry Wrapper and Contract Assembly for `spqr::send::<HookRng>` (`0x3085c`)

**Checked by Lean.**

Provides `spqrSendFullRoAt` extraction/restoration, `SpqrSendContracts` assembly from
`TripleRatchetHooks` and `SpqrHooks`, Phase 1 early-return model equations, and the
panic-polymorphic Phase 1 step `spqr_send_phase1_step_panic` (`0x3085c..0x309cc`).
-/

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
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## `.rodata` and Global Invariant (`TokenInit`, `logOff`) Extraction -/

/-- When `0` tape bytes are drawn, `tapeAt ctl cur rest` decomposes into
    `⌜rest.length < 2 ^ 63⌝ ∗ tapeAfter ctl cur rest 0`. -/
theorem tapeAt_eq_pure_sep_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest = ⌜rest.length < 2 ^ 63⌝ ∗ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  simp only [Nat.zero_min, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero, List.take_zero,
    List.drop_zero, pointsToBytes_nil, emp_sepConj, sepConj_assoc]

theorem tapeAt_entails_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  rw [tapeAt_eq_pure_sep_tapeAfter_zero]
  exact Entails.pure_left fun _ => Entails.refl _

/-- On `spqrDecodeState stateBytes = .error e`, `(spqrV1 F K).send stateBytes rest = none`,
    `(spqrV1 F K).draws stateBytes rest = 0`, and the model does not panic. -/
theorem send_and_draws_of_spqrDecodeState_error {F : ShaCompress} {K : MlKem}
    {stateBytes rest : Bytes} {e : LibsignalSpqrV1.Error}
    (hdec : Proto.spqrDecodeState stateBytes = .error e) :
    (spqrV1 F K).send stateBytes rest = none ∧
    (spqrV1 F K).draws stateBytes rest = 0 ∧
    ¬ (spqrV1 F K).sendPanics stateBytes rest := by
  have ⟨hd, _⟩ := decodeState_spqrDeps_of_spqrDecodeState_error F K hdec
  have hsend := send_of_decodeState_error (spqrDeps F K) (spqrHkdfWith F) (tape := rest) hd
  refine ⟨spqrV1_send_of_err (by rw [hsend]),
          spqrV1_draws_zero_of_remaining_eq (by rw [hsend]),
          spqrV1_not_sendPanics_of_err (by rw [hsend])⟩

/-- On `spqrDecodeState stateBytes = .ok pq` with `pq.inner = none`,
    `(spqrV1 F K).send stateBytes rest = some ([], none, [])`,
    `(spqrV1 F K).draws stateBytes rest = 0`, and the model does not panic. -/
theorem send_and_draws_of_spqrDecodeState_inner_none {F : ShaCompress} {K : MlKem}
    {stateBytes rest : Bytes} {pq : PqRatchetState}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = none) :
    (spqrV1 F K).send stateBytes rest = some ([], none, []) ∧
    (spqrV1 F K).draws stateBytes rest = 0 ∧
    ¬ (spqrV1 F K).sendPanics stateBytes rest := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hinner_pb : (pqRatchetStateToPb pq).inner = none := by
    unfold pqRatchetStateToPb
    simp [hinner]
  have hsend := send_of_inner_none (spqrDeps F K) (spqrHkdfWith F) (tape := rest) hd hinner_pb
  refine ⟨spqrV1_send_of_ok (by rw [hsend]) rfl,
          spqrV1_draws_zero_of_remaining_eq (by rw [hsend]),
          spqrV1_not_sendPanics_of_ok (by rw [hsend])⟩

/-- On `spqrDecodeState stateBytes = .ok pq`, `pq.inner = some (.v1 v1)`, and
    `States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err)`,
    `(spqrV1 F K).send stateBytes rest = none`,
    `(spqrV1 F K).draws stateBytes rest = 0`, and the model does not panic. -/
theorem send_and_draws_of_statesFromPb_error {F : ShaCompress} {K : MlKem}
    {stateBytes rest : Bytes} {pq : PqRatchetState} {v1 : V1State} {err : LibsignalSpqrV1.Error}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err)) :
    (spqrV1 F K).send stateBytes rest = none ∧
    (spqrV1 F K).draws stateBytes rest = 0 ∧
    ¬ (spqrV1 F K).sendPanics stateBytes rest := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
    unfold pqRatchetStateToPb
    simp [hinner]
  have hfrom_deps := spqrDeps_statesFromPb_of_err F K hfrom
  have hsend := send_of_statesFromPb_error (spqrDeps F K) (spqrHkdfWith F) (tape := rest)
    hd hinner_pb hfrom_deps
  refine ⟨spqrV1_send_of_err (by rw [hsend]),
          spqrV1_draws_zero_of_remaining_eq (by rw [hsend]),
          spqrV1_not_sendPanics_of_err (by rw [hsend])⟩

/-! ## Phase 1 to Phase 2 Stack Splitting -/

/-- Split `memRegion (sp + 0xb0) (0x950 - 0xb0)` into `[+0xb0..+0x550)` and `[+0x550..+0x950)`. -/
theorem memRegion_950_split_phase2 (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x950 - 0xb0) =
      memRegion (sp + 0xb0#64) (0x550 - 0xb0) ∗
      memRegion (sp + 0x550#64) (0x950 - 0x550) := by
  have h := ProofLib.memRegion_split (sp + 0xb0#64) (0x550 - 0xb0) (0x950 - 0x550) (by decide)
  have hlen : (0x550 - 0xb0) + (0x950 - 0x550) = 0x950 - 0xb0 := by decide
  have haddr : (sp + 0xb0#64) + BitVec.ofNat 64 (0x550 - 0xb0) = sp + 0x550#64 := by
    change (sp + 0xb0#64) + 0x4a0#64 = sp + 0x550#64
    bv_omega
  rw [hlen, haddr] at h
  exact h

/-- Split `memRegion (sp + 0xcf0) (0x1f20 - 0xcf0)` into the Phase 2 scratch sub-regions:
    `[+0xcf0..+0x1260)`, `[+0x1260..+0x1600)`, `[+0x1600..+0x1bc0)`, `[+0x1bc0..+0x1bd0)`,
    and `[+0x1bd0..+0x1f20)`. -/
theorem memRegion_cf0_split_phase2 (sp : BitVec 64) :
    memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
      memRegion (sp + 0xcf0#64) (0x1260 - 0xcf0) ∗
      memRegion (sp + 0x1260#64) (0x1600 - 0x1260) ∗
      memRegion (sp + 0x1600#64) (0x1bc0 - 0x1600) ∗
      memRegion (sp + 0x1bc0#64) 16 ∗
      memRegion (sp + 0x1bd0#64) (0x1f20 - 0x1bd0) := by
  have h1 := ProofLib.memRegion_split (sp + 0xcf0#64) (0x1260 - 0xcf0) (0x1f20 - 0x1260) (by decide)
  have h1_len : (0x1260 - 0xcf0) + (0x1f20 - 0x1260) = 0x1f20 - 0xcf0 := by decide
  have h1_addr : (sp + 0xcf0#64) + BitVec.ofNat 64 (0x1260 - 0xcf0) = sp + 0x1260#64 := by
    change (sp + 0xcf0#64) + 0x570#64 = sp + 0x1260#64
    bv_omega
  rw [h1_len, h1_addr] at h1
  have h2 := ProofLib.memRegion_split (sp + 0x1260#64) (0x1600 - 0x1260) (0x1f20 - 0x1600) (by decide)
  have h2_len : (0x1600 - 0x1260) + (0x1f20 - 0x1600) = 0x1f20 - 0x1260 := by decide
  have h2_addr : (sp + 0x1260#64) + BitVec.ofNat 64 (0x1600 - 0x1260) = sp + 0x1600#64 := by
    change (sp + 0x1260#64) + 0x3a0#64 = sp + 0x1600#64
    bv_omega
  rw [h2_len, h2_addr] at h2
  have h3 := ProofLib.memRegion_split (sp + 0x1600#64) (0x1bc0 - 0x1600) (0x1f20 - 0x1bc0) (by decide)
  have h3_len : (0x1bc0 - 0x1600) + (0x1f20 - 0x1bc0) = 0x1f20 - 0x1600 := by decide
  have h3_addr : (sp + 0x1600#64) + BitVec.ofNat 64 (0x1bc0 - 0x1600) = sp + 0x1bc0#64 := by
    change (sp + 0x1600#64) + 0x5c0#64 = sp + 0x1bc0#64
    bv_omega
  rw [h3_len, h3_addr] at h3
  have h4 := ProofLib.memRegion_split (sp + 0x1bc0#64) 16 (0x1f20 - 0x1bd0) (by decide)
  have h4_len : 16 + (0x1f20 - 0x1bd0) = 0x1f20 - 0x1bc0 := by decide
  have h4_addr : (sp + 0x1bc0#64) + BitVec.ofNat 64 16 = sp + 0x1bd0#64 := by bv_omega
  rw [h4_len, h4_addr] at h4
  rw [h1, h2, h3, h4]

/-! ## Panic-Polymorphic Phase 1 Step (`spqr_send_phase1_step_panic`) -/

end CryptoVerification.SpqrV1.Top.Send

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Chain.Defs -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.Repr -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Extract Invariants

Shared `S2FrameRO`-backed frame invariants (`HFrameExt`, `HCommonExt`, `HPreExt`) and extract-phase
cut predicates at stack budget `hkdfToSliceStackExt` (`17616` B).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame frame_of_agreesOutside)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs hiding hkdfToSliceName
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

/-! ## `HkdfStubsExt`, `CallingConventionPreserved` / `CalleeSaved` Helpers, & `RunsToE.trans_inv` -/

theorem cc_sp  {s s' : State} (h : CallingConventionPreserved s s') : s'.sp = s.sp := h.1
theorem cc_x19 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x19 = s.readReg64 .x19 := h.2.1
theorem cc_x20 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x20 = s.readReg64 .x20 := h.2.2.1
theorem cc_x21 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x21 = s.readReg64 .x21 := h.2.2.2.1
theorem cc_x22 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x22 = s.readReg64 .x22 := h.2.2.2.2.1
theorem cc_x23 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x23 = s.readReg64 .x23 := h.2.2.2.2.2.1
theorem cc_x24 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x24 = s.readReg64 .x24 := h.2.2.2.2.2.2.1
theorem cc_x25 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x25 = s.readReg64 .x25 := h.2.2.2.2.2.2.2.1
theorem cc_x26 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x26 = s.readReg64 .x26 := h.2.2.2.2.2.2.2.2.1
theorem cc_x27 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x27 = s.readReg64 .x27 := h.2.2.2.2.2.2.2.2.2.1
theorem cc_x28 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x28 = s.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.2.1
theorem cc_x29 {s s' : State} (h : CallingConventionPreserved s s') : s'.readReg64 .x29 = s.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.2.1

theorem cs_x29 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x29 = s.readReg64 .x29 :=
  h.2 .x29 (by simp)

/-- Contract-backed frame condition for `spqr::kdf::hkdf_to_slice`: only `[okmA .. okmA + okmLen)`
and `[hsp s₀ - 16928#64 .. hsp s₀ + 688#64)` (`hkdfToSliceStackExt = 17616` B) are modified,
allowing read-only `memcpy` touches on `roRegs`. -/
abbrev HFrameExt (roRegs : List (BitVec 64 × ℕ)) (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2FrameRO roRegs s₀.mem m [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 16928#64, 17616)]

/-- Common state invariant across `spqr::kdf::hkdf_to_slice` under `S2FrameRO roRegs`. -/
structure HCommonExt (roRegs : List (BitVec 64 × ℕ)) (okmLen : ℕ) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x29_eq : s.readReg64 .x29 = hsp s₀ + 592#64
  saved  : HSaved s₀ s.mem
  frame  : HFrameExt roRegs okmLen s₀ s.mem

theorem HFrameExt.of_agreesOutside_hsp {roRegs : List (BitVec 64 × ℕ)} {okmLen : ℕ} {s₀ : State}
    {m m' : Memory} {off : BitVec 64} {sz : ℕ} (hf : HFrameExt roRegs okmLen s₀ m)
    (hA : AgreesOutside m m' (hsp s₀ + off) sz) (hoff : off.toNat + sz ≤ 688) :
    HFrameExt roRegs okmLen s₀ m' :=
  hf.trans_agreesOutside_sub (rbase := hsp s₀ - 16928#64) (rlen := 17616) (by simp) (by clear * - hoff; bv_omega) hA

section HFrameExtProps

variable {b : BitVec 64} {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
  {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
  {okmLen : ℕ} {s₀ : State} {m : Memory}

end HFrameExtProps

theorem HSaved.of_s2FrameRO {roRegs : List (BitVec 64 × ℕ)} {s₀ : State} {m m' : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hs : HSaved s₀ m) (hrw_hsp : m.RW (hsp s₀) 688) (hfr : S2FrameRO roRegs m m' regs)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96) : HSaved s₀ m' := by
  have h_saved_eq (off : BitVec 64) (hoff : decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true) :
      m'.read64 (hsp s₀ + off) = m.read64 (hsp s₀ + off) := by
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    have hrd : m.Readable (hsp s₀ + off) 8 := (hrw_hsp.sub (by bv_omega)).readable
    refine hfr.read64_eq_of_readable hrd fun r hr => ?_
    exact (hd r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  exact ⟨(h_saved_eq 592#64 (by decide)).trans hs.m592, (h_saved_eq 600#64 (by decide)).trans hs.m600,
    (h_saved_eq 608#64 (by decide)).trans hs.m608, (h_saved_eq 616#64 (by decide)).trans hs.m616,
    (h_saved_eq 624#64 (by decide)).trans hs.m624, (h_saved_eq 632#64 (by decide)).trans hs.m632,
    (h_saved_eq 640#64 (by decide)).trans hs.m640, (h_saved_eq 648#64 (by decide)).trans hs.m648,
    (h_saved_eq 656#64 (by decide)).trans hs.m656, (h_saved_eq 664#64 (by decide)).trans hs.m664,
    (h_saved_eq 672#64 (by decide)).trans hs.m672, (h_saved_eq 680#64 (by decide)).trans hs.m680⟩

theorem HSaved.of_s2Frame {s₀ : State} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hs : HSaved s₀ m) (hrw_hsp : m.RW (hsp s₀) 688) (hfr : S2Frame m m' regs)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96) : HSaved s₀ m' :=
  HSaved.of_s2FrameRO hs hrw_hsp (S2FrameRO.of_s2frame (roRegs := []) hfr) hd

theorem HCommonExt.of_agreesOutside_hsp {roRegs : List (BitVec 64 × ℕ)} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HCommonExt roRegs okmLen s₀ s)
    (hstat : s'.status = .Running) (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (0 < sz ∧ off.toNat + sz ≤ 592) = true) :
    HCommonExt roRegs okmLen s₀ s' := by
  have ⟨h1, h2⟩ : 0 < sz ∧ off.toNat + sz ≤ 592 := of_decide_eq_true hoff
  exact ⟨hstat, hsp_eq, hx29, HSaved.of_agreesOutside_low hc.saved hA ⟨h1, h2⟩,
    HFrameExt.of_agreesOutside_hsp hc.frame hA (by omega)⟩

section HCommonExtProps

variable {b : BitVec 64} {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
  {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
  {okmLen : ℕ} {s₀ s s' : State}

end HCommonExtProps

/-! ## Extract-Phase Cut Predicates (`hex:63284 → hex:633cc`) -/

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

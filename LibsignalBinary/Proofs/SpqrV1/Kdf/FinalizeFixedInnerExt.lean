/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.CodeLayout

/-!
# Inner-Hash Segments of Contract-Backed `finalize_fixed` (`0x6ce50`)

Proves the inner-hash segments of `finalize_fixed3_gen_runsToE_ext` from `SpqrKdfHooksExt img C.F ext`
at `finalizeFixed3StackExt` (`16528` B), covering both `< 56` one-block and `[56, 64)` two-block
inner padding over `HmacStN`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.CodeLayout
open ProofLib.ProgramReflection
open SpqrKdfExt

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

namespace FinalizeFixed3ExtProof

@[local simp, local arm64_norm]
theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

abbrev FinRegsExt (s0 : State) : List (BitVec 64 × ℕ) :=
  [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)]

structure FinCommonExt (s0 s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = s0.sp - 144#64
  x29_eq : s.readReg64 .x29 = s0.sp - 144#64 + 64#64
  x26_eq : s.readReg64 .x26 = s0.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s0.readReg64 .x27
  x28_eq : s.readReg64 .x28 = s0.readReg64 .x28
  saved  : FinSaved s0 (s0.sp - 144#64) s.mem
  frame  : S2Frame s0.mem s.mem (FinRegsExt s0)

theorem rw_fsp144_of {s0 : State} {m : Memory}
    (hrw0 : RW s0.mem (s0.sp - 16528#64) 16528) (hf : S2Frame s0.mem m (FinRegsExt s0)) :
    RW m (s0.sp - 144#64) 144 := by
  have hrw : RW m (s0.sp - 16528#64) 16528 := hf.rw_of_rw _ _ hrw0
  exact hrw.sub (by bv_omega)

theorem rw_hm_of {s0 : State} {m : Memory}
    (hrw0 : RW s0.mem (s0.readReg64 .x1) 0x90) (hf : S2Frame s0.mem m (FinRegsExt s0)) :
    RW m (s0.readReg64 .x1) 0x90 :=
  hf.rw_of_rw _ _ hrw0

theorem rw_out_of {s0 : State} {m : Memory}
    (hrw0 : RW s0.mem (s0.readReg64 .x0) 32) (hf : S2Frame s0.mem m (FinRegsExt s0)) :
    RW m (s0.readReg64 .x0) 32 :=
  hf.rw_of_rw _ _ hrw0

theorem s2frame_seg2a {s0 : State} {m1 m2 m3 m4 : Memory}
    (hf : S2Frame s0.mem m1 (FinRegsExt s0))
    (hag1 : AgreesOutside m1 m2 (s0.sp - 144#64) 64)
    (hag2 : AgreesOutside m2 m3 (s0.readReg64 .x1) 64)
    (hag3 : AgreesOutside m3 m4 (s0.sp - 144#64) 64) :
    S2Frame s0.mem m4 (FinRegsExt s0) := by
  have hf1 := S2Frame.trans_agreesOutside_sub hf (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag1
  have hf2 := S2Frame.trans_agreesOutside_sub hf1 (rbase := s0.readReg64 .x1) (rlen := 0x90)
    (by simp [FinRegsExt]) (by bv_omega) hag2
  exact S2Frame.trans_agreesOutside_sub hf2 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag3

theorem s2frame_seg3a {s0 : State} {m1 m2 m3 m4 m5 : Memory}
    (hf : S2Frame s0.mem m1 (FinRegsExt s0))
    (hag1 : AgreesOutside m1 m2 (s0.readReg64 .x1) 64)
    (hag2 : AgreesOutside m2 m3 (s0.sp - 144#64) 64)
    (hag3 : AgreesOutside m3 m4 (s0.readReg64 .x1) 64)
    (hag4 : AgreesOutside m4 m5 (s0.sp - 144#64) 64) :
    S2Frame s0.mem m5 (FinRegsExt s0) := by
  have hf1 := S2Frame.trans_agreesOutside_sub hf (rbase := s0.readReg64 .x1) (rlen := 0x90)
    (by simp [FinRegsExt]) (by bv_omega) hag1
  have hf2 := S2Frame.trans_agreesOutside_sub hf1 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag2
  have hf3 := S2Frame.trans_agreesOutside_sub hf2 (rbase := s0.readReg64 .x1) (rlen := 0x90)
    (by simp [FinRegsExt]) (by bv_omega) hag3
  exact S2Frame.trans_agreesOutside_sub hf3 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag4

theorem s2frame_seg4a {s0 : State} {m1 m2 m3 m4 m5 : Memory}
    (hf : S2Frame s0.mem m1 (FinRegsExt s0))
    (hag1 : AgreesOutside m1 m2 (s0.readReg64 .x1) 0x90)
    (hag2 : AgreesOutside m2 m3 (s0.sp - 144#64) 64)
    (hag3 : AgreesOutside m3 m4 (s0.readReg64 .x1) 0x90)
    (hag4 : AgreesOutside m4 m5 (s0.readReg64 .x0) 32) :
    S2Frame s0.mem m5 (FinRegsExt s0) := by
  have hf1 := S2Frame.trans_agreesOutside hf (by simp [FinRegsExt]) hag1
  have hf2 := S2Frame.trans_agreesOutside_sub hf1 (rbase := s0.sp - 16528#64) (rlen := 16528)
    (by simp [FinRegsExt]) (by bv_omega) hag2
  have hf3 := S2Frame.trans_agreesOutside hf2 (by simp [FinRegsExt]) hag3
  exact S2Frame.trans_agreesOutside hf3 (by simp [FinRegsExt]) hag4

theorem s2frame_hook_hm_sub {s0 : State} {m1 m2 : Memory} {off : BitVec 64} {sz : ℕ}
    (hf1 : S2Frame s0.mem m1 (FinRegsExt s0))
    (hf2 : S2Frame m1 m2 [(s0.readReg64 .x1 + off, sz), ((s0.sp - 144#64) - 16384#64, 16384)])
    (hoff : off.toNat + sz ≤ 0x90) :
    S2Frame s0.mem m2 (FinRegsExt s0) := by
  refine hf1.trans (hf2.mono fun a ha r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have h_hm := ha (s0.readReg64 .x1, 0x90) (by simp [FinRegsExt])
    simp only [OutsideRegion] at h_hm ⊢; bv_omega
  · have h_stk := ha (s0.sp - 16528#64, 16528) (by simp [FinRegsExt])
    simp only [OutsideRegion] at h_stk ⊢; bv_omega

end FinalizeFixed3ExtProof

end CryptoVerification.SpqrV1.Kdf

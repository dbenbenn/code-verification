/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Frame -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public import ProofLib.GenDecodes
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome

/-!
# Wrapper Prologue Symbolic Execution for `decrypt_prekey`

Steps the `signal_session_handshake::decrypt_prekey` wrapper prologue from function entry up to the
call to the `message_decrypt_prekey` poll closure.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (v : BitVec 5) :
    (s.setPC pc).readVReg128 v = s.readVReg128 v := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (v : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 v = s.readVReg128 v := by cases s; rfl

theorem sep_rearrange {P P' : SepProp} (hf : P = P' ∗ emp) : P = P' := by
  rw [hf, sepConj_emp]

@[scoped arm64_norm] theorem bv128_lo_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
@[scoped arm64_norm] theorem bv128_hi_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
@[scoped arm64_norm] theorem bv_add_16_8 (x : BitVec 64) : x + 16#64 + 8#64 = x + 24#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_add_32_8 (x : BitVec 64) : x + 32#64 + 8#64 = x + 40#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_01 (x : BitVec 64) : x - 48#64 + 8#64 = x - 40#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_02 (x : BitVec 64) : x - 48#64 + 16#64 = x - 32#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_03 (x : BitVec 64) : x - 32#64 + 8#64 = x - 24#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_04 (x : BitVec 64) : x - 48#64 + 32#64 = x - 16#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_05 (x : BitVec 64) : x - 16#64 + 8#64 = x - 8#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_06 (x : BitVec 64) : x - 48#64 + 48#64 = x := by bv_kernel
@[scoped arm64_norm] theorem bv_off_07 (x : BitVec 64) : x - 48#64 + 80#64 = x + 32#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_08 (x : BitVec 64) : x - 48#64 - 1#64 = x - 49#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_09 (x : BitVec 64) : x - 48#64 - 2096#64 = x - 2144#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_10 (x : BitVec 64) : x - 48#64 - 56#64 = x - 104#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_11 (x : BitVec 64) : x - 48#64 - 88#64 = x - 136#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_12 (x : BitVec 64) : x - 48#64 - 72#64 = x - 120#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_13 (x : BitVec 64) : x - 136#64 + 8#64 = x - 128#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_14 (x : BitVec 64) : x - 104#64 + 8#64 = x - 96#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_15 (x : BitVec 64) : x - 104#64 + 16#64 = x - 88#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_15b (x : BitVec 64) : x - 104#64 + 24#64 = x - 80#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_16 (x : BitVec 64) : x - 88#64 + 8#64 = x - 80#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_17 (x : BitVec 64) : x - 104#64 + 32#64 = x - 72#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_17b (x : BitVec 64) : x - 104#64 + 40#64 = x - 64#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_18 (x : BitVec 64) : x - 72#64 + 8#64 = x - 64#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_19 (x : BitVec 64) : x - 2144#64 + 8#64 = x - 2136#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_20 (x : BitVec 64) : x - 2144#64 + 16#64 = x - 2128#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_21 (x : BitVec 64) : x - 2128#64 + 8#64 = x - 2120#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_22 (x : BitVec 64) : x - 2144#64 + 32#64 = x - 2112#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_23 (x : BitVec 64) : x - 2112#64 + 8#64 = x - 2104#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_24 (x : BitVec 64) : x - 2144#64 + 48#64 = x - 2096#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_25 (x : BitVec 64) : x - 2096#64 + 8#64 = x - 2088#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_26 (x : BitVec 64) : x - 2144#64 + 64#64 = x - 2080#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_27 (x : BitVec 64) : x - 2080#64 + 8#64 = x - 2072#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_28 (x : BitVec 64) : x - 2080#64 + 16#64 = x - 2064#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_29 (x : BitVec 64) : x - 2064#64 + 8#64 = x - 2056#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_30 (x : BitVec 64) : x - 2144#64 + 96#64 = x - 2048#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_31 (x : BitVec 64) : x - 2048#64 + 8#64 = x - 2040#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_32 (x : BitVec 64) : x - 2144#64 + 704#64 = x - 1440#64 := by bv_kernel
@[scoped arm64_norm] theorem bv_off_33 (x : BitVec 64) : x - 2144#64 + 2096#64 = x - 48#64 := by bv_kernel

private theorem dp_sp_sub_2144_aligned (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    (sp - 2144#64 &&& 15#64 == 0#64) = true := by bv_kernel

abbrev dpPrologueMid2Prop (stk : Nat) (s0 : State) (ret : BitVec 64) {K : DpPollK} (g : K.Ghost)
    (a12 f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64) (fstate : BitVec 8) (cx0 cx1 cx2 : BitVec 64) : SepProp :=
  stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗
    ((s0.sp - 2144#64) ↦₆₄ s0.readReg64 (Reg.gpr 0#5)) ∗ ((s0.sp - 2136#64) ↦₆₄ s0.readReg64 (Reg.gpr 1#5)) ∗
    ((s0.sp - 2128#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗ ((s0.sp - 2120#64) ↦₆₄ s0.readReg64 (Reg.gpr 3#5)) ∗
    ((s0.sp - 2112#64) ↦₆₄ f4) ∗ ((s0.sp - 2104#64) ↦₆₄ f5) ∗ ((s0.sp - 2096#64) ↦₆₄ f6) ∗ ((s0.sp - 2088#64) ↦₆₄ f7) ∗
    ((s0.sp - 2080#64) ↦₆₄ f8) ∗ ((s0.sp - 2072#64) ↦₆₄ f9) ∗ ((s0.sp - 2064#64) ↦₆₄ f10) ∗ ((s0.sp - 2056#64) ↦₆₄ f11) ∗
    ((s0.sp - 2048#64) ↦₆₄ a12) ∗ ((s0.sp - 2040#64) ↦₆₄ (s0.sp - 49#64)) ∗
    memRegion (s0.sp - 2032#64) 592 ∗ ((s0.sp - 1440#64) ↦₈ fstate) ∗ memRegion (s0.sp - 1439#64) 1303 ∗
    ((s0.sp - 136#64) ↦₆₄ cx0) ∗ ((s0.sp - 128#64) ↦₆₄ cx1) ∗ ((s0.sp - 120#64) ↦₆₄ cx2) ∗
    memRegion (s0.sp - 112#64) 8 ∗ memRegion (s0.sp - 104#64) 48 ∗
    K.inv g ∗ dpCallerFrame s0 ret ((K.args g).drop 8)

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

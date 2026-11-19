/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 2 Early `Err` Unwind (`0x0584 → 0x157c → 0x0350 → ret`)

Verifies `segB_err_ok` and `segB_err_ext_ok` when `get_identity_key_pair` returns `.error ()`,
skipping teardown of the empty `SessionRecord` and returning the `SpeOwned` error payload via `0x0350`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16

theorem sepWPp_of_sepWP_exit {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, hok | hoom⟩
  · exact ⟨sm, hsteps, Or.inl hok⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem memRegion_48_eq_words6 (r : BitVec 64) :
    memRegion r 48 =
      ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (r ↦₆₄ u0) ∗ ((r + 8#64) ↦₆₄ u1) ∗ ((r + 16#64) ↦₆₄ u2) ∗
        ((r + 24#64) ↦₆₄ u3) ∗ ((r + 32#64) ↦₆₄ u4) ∗ ((r + 40#64) ↦₆₄ u5) := by
  apply Entails.antisymm
  · rw [mr_split r (r + 8#64) 8 40 48 rfl rfl,
        mr_split (r + 8#64) (r + 16#64) 8 32 40 rfl (by bv_omega),
        mr_split (r + 16#64) (r + 24#64) 8 24 32 rfl (by bv_omega),
        mr_split (r + 24#64) (r + 32#64) 8 16 24 rfl (by bv_omega),
        mr_split (r + 32#64) (r + 40#64) 8 8 16 rfl (by bv_omega),
        memRegion_8_eq_exists r, memRegion_8_eq_exists (r + 8#64),
        memRegion_8_eq_exists (r + 16#64), memRegion_8_eq_exists (r + 24#64),
        memRegion_8_eq_exists (r + 32#64), memRegion_8_eq_exists (r + 40#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact Entails.refl _
  · refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u0 => ?_
    refine mr_fold r (r + 8#64) 8 40 48 (mr_of_u64 _ _) ?_ rfl rfl
    refine mr_fold (r + 8#64) (r + 16#64) 8 32 40 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
    refine mr_fold (r + 16#64) (r + 24#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
    refine mr_fold (r + 24#64) (r + 32#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
    exact mr_fold (r + 32#64) (r + 40#64) 8 8 16 (mr_of_u64 _ _) (mr_of_u64 _ _) rfl (by bv_omega)

theorem initSaved_eq_fsp {s0 s : State} (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) :
    initSaved s0 =
      ((s.sp + 7312#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s.sp + 7320#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s.sp + 7328#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s.sp + 7336#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s.sp + 7344#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s.sp + 7352#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s.sp + 7360#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s.sp + 7368#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s.sp + 7376#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s.sp + 7384#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s.sp + 7392#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s.sp + 7400#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  have hb : s0.sp - 0x60#64 = s.sp + 7312#64 := by
    rw [cliInitiateFrame_eq] at hsp
    bv_omega
  unfold initSaved
  dsimp only
  simp only [hb, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]

/-- Witness `ApiError AddrVal Unit` value representing an identity-key-pair error return. -/
@[expose] def initErrVal : Except (ApiError AddrVal Unit) Unit :=
  .error (.protocol .invalidProtobufEncoding)

theorem initErrVal_ne_panic : initErrVal ≠ .error .panic := by nofun

theorem initErrVal_ne_store : initErrVal ≠ .error (.store ()) := by nofun

theorem slotTrace_of_eq {s0 sf : State}
    (htr : sf.trace = s0.trace) (hfiles : sf.fs.files = s0.fs.files) :
    slotTrace s0 sf :=
  ⟨htr ▸ List.prefix_refl _, hfiles, congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

theorem initResAt_err_of_speOwned (A : RustAlloc) (ret : BitVec 64) (k : RunDrop.SpeOwned) :
    RunDrop.speOwnedAt A ret k ⊢ initResAt A ret initErrVal :=
  Entails.sepExists_intro k

theorem calleeSavedPreserved_of_regs {s0 sf : State}
    (hx19 : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (hx20 : sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (hx21 : sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (hx22 : sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5))
    (hx23 : sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5))
    (hx24 : sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5))
    (hx25 : sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5))
    (hx26 : sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hx27 : sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hx28 : sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5))
    (hfp : sf.readReg64 .fp = s0.readReg64 .fp)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf :=
  ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

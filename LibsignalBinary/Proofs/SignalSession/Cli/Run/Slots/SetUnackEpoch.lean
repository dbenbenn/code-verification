/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Bin.SendSegsCommon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.Run
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit Initiator.bv_sub_add_lit' BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_send sp_setMem_setPC_pre_send
  readReg64_setPC_pre_send readReg64_setMem_setPC_pre_send
  readReg32_setPC_pre_send readReg32_setMem_setPC_pre_send
  readReg_setPC_pre_send readReg_setMem_setPC_pre_send
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_hi_addsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64
attribute [local arm64_norm, local wp_norm]
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_32 bv_add_neg_36
  CryptoVerification.E2E.Pqxdh.TopLevel.bv_add_neg_0x60
  bv_add_neg_728 bv_add_neg_828 bv_add_neg_864 bv_add_neg_904 bv_add_neg_944
  bv_add_neg_1000 bv_add_neg_1032 bv_add_neg_1048 bv_add_neg_1056 bv_add_neg_1068 bv_add_neg_1072
    bv_add_neg_1116 bv_add_neg_1144
  bv_add_neg_1444 bv_add_neg_2088 bv_add_neg_2108 bv_add_neg_2132 bv_add_neg_2400
  bv_add_neg_2536 bv_add_neg_2684 bv_add_neg_0xb20 bv_add_neg_3032
  bv_add_bl_0x123d0 bv_add_bl_0x17490 bv_add_bl_0x49e80
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg
attribute [-arm64_norm]
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  SpqrV1.Kdf.HkdfToSliceProof.read8_write64_264_271
  SpqrV1.Kdf.HkdfToSliceProof.read8_write64_408_415
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint

/-!
# `SessionState::set_unacknowledged_pre_key_message` at `UNIX_EPOCH`

Verifies `SessionState::set_unacknowledged_pre_key_message` when `now = UNIX_EPOCH` (`x5 = 0`,
`w6 = 0`) against `setUnackPreKeyMsgExactStackEpochSpec` on `trTrapProgAt` and `cliExterns W`, and
against the 16-KiB `setUnackPreKeyMsgExtStackEpochSpec` under `CliExternsOk P A ext`.

## 1. `UNIX_EPOCH` stack specification (`setUnackPreKeyMsgExactStackEpochSpec`)
-/

private theorem sessionShim_hookOk_std3 : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

private theorem hookSat_trTrap_std3 {α : Type} (C : Crypto)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : trTrapExterns C abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  unfold HookSat at *; rwa [heq]

private theorem memRegion_33_cells_epoch (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ u0 : BitVec 64, (a + 1#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (a + 9#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (a + 17#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (a + 25#64) ↦₆₄ u3) := by
  rw [ProofLib.memRegion_split a 1 32 (by decide),
    ProofLib.memRegion_split (a + 1#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem bytesToBv8_encodeEC_epoch (bs : Initiator.Bytes) :
    Initiator.bytesToBv8 (Initiator.encodeEC bs) = 5#8 :: Initiator.bytesToBv8 bs := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true_epoch :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ite_zero64_epoch (b : Bool) : (if b = true then 0#64 else 0#64) = 0#64 := by
  cases b <;> rfl

private theorem memRegion_16_split_64_epoch (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a,
    ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_24_split_64_epoch (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

private theorem pointsTo64_triple_entails_memRegion24_epoch (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_split_64_epoch a]
  exact Entails.sepExists_right w2 (Entails.sepExists_right w1
    (Entails.sepExists_right w0 (Entails.refl _)))

private theorem memRegion_40_unack_split_epoch (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (statePtr + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗
      (∃∗ w114 : BitVec 32, (statePtr + 0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (statePtr + 0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [ProofLib.memRegion_split (statePtr + 0x100#64) 8 32 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4
      (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_four, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_setUnack_call_epoch (sp : BitVec 64) :
    stackAt (sp - 144#64) (RustHeap.allocHookStack + 32) =
      stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := ProofLib.stackAt_split_cells (sp - 144#64) RustHeap.allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1

private theorem stackAt_setUnack_hooks_epoch (sp : BitVec 64) :
    stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack := by
  rw [← stackAt_setUnack_call_epoch sp]
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 32 RustHeap.allocHookStack (by decide)
  have h2 : (32 + RustHeap.allocHookStack : Nat) = RustHeap.allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + RustHeap.allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem pointsToBytes_entails_memRegion_33_epoch (p : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 33) : (p ↦ₛ bs) ⊢ memRegion p 33 := by
  rw [← h]; exact ProofLib.pointsToBytes_entails_memRegion p bs

private theorem cells_pre_unfold_18_epoch (sp : BitVec 64) :
    cells (sp - 144#64) 18 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
       ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
       ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64,
       ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64,
       ∃∗ c15 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c0) ∗ ((sp - 136#64) ↦₆₄ c1) ∗ ((sp - 128#64) ↦₆₄ c2) ∗
        ((sp - 120#64) ↦₆₄ c3) ∗ ((sp - 112#64) ↦₆₄ c4) ∗ ((sp - 104#64) ↦₆₄ c5) ∗
        ((sp - 96#64) ↦₆₄ c6) ∗ ((sp - 88#64) ↦₆₄ c7) ∗ ((sp - 80#64) ↦₆₄ c8) ∗
        ((sp - 72#64) ↦₆₄ c9) ∗ ((sp - 64#64) ↦₆₄ c10) ∗ ((sp - 56#64) ↦₆₄ c11) ∗
        ((sp - 48#64) ↦₆₄ c12) ∗ ((sp - 40#64) ↦₆₄ c13) ∗ ((sp - 32#64) ↦₆₄ c14) ∗
        ((sp - 24#64) ↦₆₄ c15) ∗ ((sp - 16#64) ↦₆₄ c16) ∗ ((sp - 8#64) ↦₆₄ c17)) := by
  cells_unfold

private theorem hookOk_cliMemcpy_of_region_std3 {h : State → State}
    (hh : HookOk h sessionMemcpyRegionSpec) : HookOk h CliExt.memcpySpec := by
  intro x R s0 hrun hpre hsp
  rcases x with ⟨dst, src, bs⟩
  dsimp only [CliExt.memcpySpec, libcMemcpySpec] at hpre
  simp only [sepConj_assoc] at hpre
  obtain ⟨hkf, hsym, hout⟩ :=
    hh (dst, src, bs) (stackAt s0.sp CliExt.memHookStack ∗ R) s0 hrun
      (by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
          simpa only [sepConj_assoc] using hpre)
      hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionSpec] at hpost
    dsimp only [CliExt.memcpySpec]
    simpa only [sepConj_assoc] using hpost
  · refine False.elim ?_
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hpan
    exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using hpan.2)).1
  · refine False.elim ?_
    rcases hex with ⟨_, _, hex2⟩
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hex2
    exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using hex2)).1
  · refine False.elim ?_
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hoom
    exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using hoom.2)).1

private theorem sessionShimSpec_eq_cliExt : sessionShimSpec = CliExt.shimSpec := by
  unfold sessionShimSpec CliExt.shimSpec
  rfl

private theorem cliHookNames_nodup_std3 : cliHookNames.Nodup := by
  unfold cliHookNames
  decide

private theorem cliHookNames_notPanic_epoch_std3 :
    cliHookNames.all (fun n => !E2E.isImagePanicSymbol n) = true := by
  rw [List.all_eq_true]
  intro n hn
  simp only [cliHookNames,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.compress512Name,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.toEdwardsName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.compressName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.edNegName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.torsionFreeName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.dsmbName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.scalarModName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.scalarWideName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.kemEncapsName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.kemDecapsName,
    LibsignalSpqrV1.mlkemFromSeedName, LibsignalSpqrV1.mlkemPk1Name,
    LibsignalSpqrV1.mlkemPk2Name, LibsignalSpqrV1.mlkemEncaps1Name,
    LibsignalSpqrV1.mlkemEncaps2Name, LibsignalSpqrV1.mlkemDecapsName,
    LibsignalSpqrV1.mlkemValidatePkName, LibsignalSpqrV1.libcruxHmacName,
    SignalSession.readFileName, SignalSession.writeFileName,
    SignalSession.readStdinName, SignalSession.writeStdoutName,
    List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames]

private theorem cliExterns_row_std3 (W : CliHooks) {n : String} {h : State → State}
    (hm : (n, h) ∈ cliHookTable W) : cliExterns W n = some h := by
  have hn : n ∈ cliHookNames := by
    rw [← cliHookNames_eq W]
    exact List.mem_map.mpr ⟨(n, h), hm, rfl⟩
  have hp : E2E.isImagePanicSymbol n = false := by
    have := List.all_eq_true.mp cliHookNames_notPanic_epoch_std3 n hn
    simpa using this
  unfold cliExterns
  rw [withCliPanics_of_isImagePanicSymbol_false _ hp]
  exact lookup_of_mem_nodup _ n h (by rw [cliHookNames_eq W]; exact cliHookNames_nodup_std3) hm

private theorem cliExterns_none_std3 (W : CliHooks) {n : String} (hn : n ∉ cliHookNames)
    (hp : E2E.isImagePanicSymbol n = false) : cliExterns W n = none := by
  unfold cliExterns
  rw [withCliPanics_of_isImagePanicSymbol_false _ hp]
  exact lookup_of_not_mem _ n (by rw [cliHookNames_eq W]; exact hn)

private theorem cliExterns_durationSinceEpochAlloc_std3 (W : CliHooks) :
    HookSat (cliExterns W) E2E.durationSinceName durationSinceEpochAllocSpec :=
  ⟨durationSinceExactHook, cliExterns_row_std3 W (durationSince_row W),
    durationSinceExactHook_epoch_alloc_ok⟩

private theorem cliExterns_agree_std3 (W : CliHooks) (ctl : BitVec 64) {n : String}
    (hn : n ≠ rngFillName) :
    Rust.withPanics (tripleRatchetExterns W.C ctl (cliExterns W)) n =
      Rust.withPanics (cliExterns W) n := by
  rw [withPanics_cliExterns]
  by_cases hp : Rust.isPanicSymbol n = true
  · have hpC : isCliPanicSymbol n = true := isCliPanicSymbol_of_isPanicSymbol hp
    unfold cliExterns withCliPanics
    simp [Rust.withPanics, hp, hpC]
  · simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte]
    by_cases hk : n ∈ kitOwnNames
    · simp only [kitOwnNames, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      simp [tripleRatchetExterns, CryptoVerification.LibsignalSession.sessionExterns,
        dhName, pubFromSecretName, staticDropName, sharedDropName, rngFillName, noHookNames] <;>
      first
        | (unfold cliExterns withCliPanics
           simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
             deadCliHashbrownPanicNames]; done)
        | (refine (cliExterns_row_std3 W ?_).symm
           simp [cliHookTable])
        | (refine (cliExterns_none_std3 W ?_ ?_).symm
           · unfold cliHookNames; decide
           · simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames])
    · exact tripleRatchetExterns_of_not_mem W.C ctl (cliExterns W) hk hn

private theorem stackAt_ext_split_exact_epoch (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 12288 ∗
        stackAt (sp - 144#64) (RustHeap.allocHookStack + 32) := by
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 12288 (RustHeap.allocHookStack + 32)
    (by decide)
  have h2 : (12288 + (RustHeap.allocHookStack + 32) : Nat) = extHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (12288 + (RustHeap.allocHookStack + 32)) = 16416#64 := rfl
  have h4 : sp - 144#64 - 16416#64 = sp - 16560#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem stackAt_setUnack_ext_call (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 12288 ∗
        stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 := by
  rw [stackAt_ext_split_exact_epoch sp, stackAt_setUnack_call_epoch sp]

private theorem stackAt_setUnack_ext_4k (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 12320 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack := by
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 12320 RustHeap.allocHookStack (by decide)
  have h2 : (12320 + RustHeap.allocHookStack : Nat) = extHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (12320 + RustHeap.allocHookStack) = 16416#64 := rfl
  have h4 : sp - 144#64 - 16416#64 = sp - 16560#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem stackAt_setUnack_ext_16k (sp : BitVec 64) :
    stackAt (sp - 144#64) (extHookStack + 32) =
      memRegion (sp - 16560#64) 32 ∗ stackAt (sp - 144#64) extHookStack := by
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 32 extHookStack (by decide)
  have h2 : (32 + extHookStack : Nat) = extHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + extHookStack) = 16416#64 := rfl
  have h4 : sp - 144#64 - 16416#64 = sp - 16560#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem stackAt_setUnack_ext_after_ser (sp : BitVec 64) :
    memRegion (sp - 16560#64) 12288 ∗
        stackAt (sp - 176#64) RustHeap.allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 16560#64) 12320 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack :=
  (stackAt_setUnack_ext_call sp).symm.trans (stackAt_setUnack_ext_4k sp)

private theorem stackAt_setUnack_ext_4k_to_16k (sp : BitVec 64) :
    memRegion (sp - 16560#64) 12320 ∗ stackAt (sp - 144#64) RustHeap.allocHookStack =
      memRegion (sp - 16560#64) 32 ∗ stackAt (sp - 144#64) extHookStack :=
  (stackAt_setUnack_ext_4k sp).symm.trans (stackAt_setUnack_ext_16k sp)

private theorem durationSinceEpochAtSpec_ext_eq :
    durationSinceEpochAtSpec extHookStack = CliExt.durationSinceEpochSpec := by
  unfold durationSinceEpochAtSpec CliExt.durationSinceEpochSpec
  rfl

end CryptoVerification.SignalSession.Cli.Slots

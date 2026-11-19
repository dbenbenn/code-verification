/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ConsumerGlue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CryptoHooksDehook -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg
import LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk
import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
import ProofLib.Placed.CheckText
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Stock-ELF `dalekCliMultiLib` Placement and 9-Row Crypto/Dalek Ghost Discharges

Supplies the zero-hook stock-ELF placement witness `c2DalekMpl` for the 28 active blocks and 9
`.rodata.lib2` tables of `dalekCliMultiLib`, together with `GhostRowSpecOk`, `GhostRowReplayOn`,
`GhostRowOk`, and `HookNoAllocFailed` discharges for 9 directly linked `cliExtraGhostSyms` rows
(`lsToEdwardsSym`, `lsCompressSym`, `lsEdNegSym`, `lsTorsionFreeSym`, `lsDsmbSym`,
`lsScalarModSym`, `lsScalarWideSym`, `lsMlkemPk1Sym`, `lsMlkemPk2Sym`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekHooksDehook

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
  ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsCompressSym lsDsmbSym lsEdNegSym lsMlkemPk1Sym lsMlkemPk2Sym
   lsScalarModSym lsScalarWideSym lsSharedSecretDropSym lsToEdwardsSym lsTorsionFreeSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks IsFsC mlkemPk1Hook_fsT mlkemPk2Hook_fsT)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg (dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg
  (edwardsPointNegInstrs edwardsPointNegWords pureWordsProg_hasInstrs_edNeg)
open LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk
  (hasInstrs_of_hasWords mlkemPk1Words mlkemPk2Words)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
  (zeroize32Instrs zeroize32Words)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase
  (basepointOrderBytes basepoint_order fe51EdwardsD2Bytes fe51EdwardsDBytes fe51MinusOneBytes
   fe51OneBytes fe51SqrtM1Bytes fe51_edwards_d fe51_edwards_d2 fe51_minus_one fe51_one
   fe51_sqrt_m1 oddMultiplesBasepointBytes odd_multiples_basepoint sc52LBytes sc52RRBytes
   sc52_l sc52_rr)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality
  (DalekActiveCodeLoaded DalekActivePlaceable DalekActiveRoOk dalekActiveBlocks
   dalekActiveInvMem dalekActiveInvMem_of_keepsFrozen dalekActiveKeep dalekActivePlaceable_of_check)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ConsumerGlue
  (dalekCompressGhostLs_rowSpec dalekDsmbGhostLs_rowSpec dalekMontToEdGhostLs_rowSpec
   dalekScalarModGhostLs_rowSpec dalekScalarWideGhostLs_rowSpec dalekTorsionFreeGhostLs_rowSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks
  (dalekCompressGhostLs dalekCompressGhostLs_fsT dalekCompressGhostLs_rowReplayOn
   dalekCompressGhostLs_vmPreserved_and_nonSyscall dalekDsmbGhostLs dalekDsmbGhostLs_fsT
   dalekDsmbGhostLs_rowReplayOn dalekDsmbGhostLs_vmPreserved_and_nonSyscall dalekMontToEdGhostLs
   dalekMontToEdGhostLs_fsT dalekMontToEdGhostLs_rowReplayOn
   dalekMontToEdGhostLs_vmPreserved_and_nonSyscall dalekScalarModGhostLs dalekScalarModGhostLs_fsT
   dalekScalarModGhostLs_rowReplayOn dalekScalarModGhostLs_vmPreserved_and_nonSyscall
   dalekScalarWideGhostLs dalekScalarWideGhostLs_fsT dalekScalarWideGhostLs_rowReplayOn
   dalekScalarWideGhostLs_vmPreserved_and_nonSyscall dalekTorsionFreeGhostLs
   dalekTorsionFreeGhostLs_fsT dalekTorsionFreeGhostLs_rowReplayOn
   dalekTorsionFreeGhostLs_vmPreserved_and_nonSyscall)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealPre ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (HookNoAllocFailed hookNoAllocFailed_of_trace_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (c2GuardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice rxSubslice_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_ghostAt_of_extraLookup c2_keepLib2Text_of_sub_lt c2_keepTextBPre_of_sub_lt
   c2_noPanic_of_band_sub_lt f3CodeInv_and_fs_keepsFrozen isLinkedPanicAddr_false_of_keepTextBPre
   resolve_c2RxSym_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_lsmpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CryptoHooksDehook
  (edNegByteLen edNegByteLen_eq f3EmptyEdNegGhostHook f3EmptyEdNegGhostHook_eq keepEdNeg
   keepEdNeg_iff narrowEdNegGhostHook narrowEdNegGhostHook_fs narrowEdNegGhostHook_fsT
   narrowEdNegGhostHook_master_ok narrowEdNegGhostHook_preserves_execFrozen
   narrowEdNegGhostHook_visitedIn narrowEdNegGhostHook_vmPreserved
   steps_mlkemPk1_of_hasWords steps_mlkemPk2_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode
  (EdNegStatePreserved masterEdNegSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
  (linkedCallHook_activeRealPre_of_noException)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
  (mlkemPk1Hook mlkemPk2Hook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode
  (ZeroizeStatePreserved hookOk_zeroizeSecret_of_master masterZeroizeSpec processZeroizeSpec
   pureWordsProg_zeroize32_hasWords subroutine_ok_processZeroize_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost
  (f3EmptyZeroizeGhostHook f3EmptyZeroizeGhostHook_eq f3EmptyZeroizeGhostHook_fs
   f3EmptyZeroizeGhostHook_fsT f3EmptyZeroizeGhostHook_master_ok_of_process
   f3EmptyZeroizeGhostHook_preserves_execFrozen f3EmptyZeroizeGhostHook_trace_of_process
   f3EmptyZeroizeGhostHook_visitedIn f3EmptyZeroizeGhostHook_vmPreserved_of_process)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
  (keepStaticSecretDrop keepStaticSecretDrop_iff staticSecretDropByteLen
   staticSecretDrop_codeLoaded_stripExecOutside)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable ExtraRowSpec GhostRowSpecOk cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (DalekCompressRowSpec DalekDsmbRowSpec DalekMontToEdRowSpec DalekScalarModRowSpec
   DalekScalarWideRowSpec DalekTorsionFreeRowSpec EdNegRowSpec MlkemPk1RowSpec MlkemPk2RowSpec
   mlkemPk1Hook_rowSpec mlkemPk2Hook_rowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec
  (SharedSecretDropRowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3CodeInv_roDataAt_of_checkSegSlice f3LsRetAddr624_rxRegion_guard
   isLinkedPanicAddr isLinkedPanicAddr_false_of_mid keepLib2Text keepLib2Text_sub_rxProg
   keepTextBPre keepTextBPre_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BlackBoxAddr c2Compress256Addr c2DurationSinceCst16Addr c2FirstExternStubAddr c2Lib2TextHi
   c2Lib2TextLo c2MemmoveAddr c2RxDehookedSyms c2SharedSecretDropAddr c2TextBPreHi c2TextBPreLo
   c2Zeroize32Addr)

/-! ## 1. Stock-ELF `c2DalekMpl` Placement & Computable `DalekActivePlaceable` -/

/-- Stock-ELF entry address of `<EdwardsPoint as Neg>::neg` (`lsEdNegSym`) in `.text.lib2`. -/
@[expose] def c2EdNegAddr : BitVec 64 := c2Zeroize32Addr + 8820#64

/-- Stock-ELF entry address of `KeyPairCompressedBytes::pk1` (`lsMlkemPk1Sym`) in `.text.lib2`. -/
@[expose] def c2MlkemPk1Addr : BitVec 64 := c2Compress256Addr - 17184#64

/-- Stock-ELF entry address of `KeyPairCompressedBytes::pk2` (`lsMlkemPk2Sym`) in `.text.lib2`. -/
@[expose] def c2MlkemPk2Addr : BitVec 64 := c2Compress256Addr - 17176#64

/-- Computable `MultiPlacement` for the 28 active blocks (`B00..B33` in `.text.lib2`, `B36 = memcpy`
    in `.text.b_pre`) and 12 active external / `.rodata.lib2` symbols of `dalekCliMultiLib` on the
    0-hook stock ELF, anchored purely to `Wp4LayoutGen` offsets. -/
@[expose] def c2DalekMpl : Obj.MultiPlacement where
  base i :=
    match i with
    | 0  => c2BlackBoxAddr
    | 1  => c2BlackBoxAddr + 20#64
    | 2  => c2BlackBoxAddr + 32#64
    | 3  => c2BlackBoxAddr + 1140#64
    | 4  => c2BlackBoxAddr + 3752#64
    | 5  => c2BlackBoxAddr + 4156#64
    | 6  => c2BlackBoxAddr + 4860#64
    | 8  => c2BlackBoxAddr + 6176#64
    | 10 => c2BlackBoxAddr + 8076#64
    | 11 => c2BlackBoxAddr + 8992#64
    | 12 => c2BlackBoxAddr + 9392#64
    | 13 => c2BlackBoxAddr + 10288#64
    | 14 => c2BlackBoxAddr + 11548#64
    | 15 => c2BlackBoxAddr + 12364#64
    | 16 => c2BlackBoxAddr + 13056#64
    | 17 => c2BlackBoxAddr + 14808#64
    | 19 => c2BlackBoxAddr + 16388#64
    | 20 => c2BlackBoxAddr + 17468#64
    | 22 => c2Zeroize32Addr + 252#64
    | 24 => c2Zeroize32Addr + 916#64
    | 25 => c2Zeroize32Addr + 1756#64
    | 28 => c2Zeroize32Addr + 4724#64
    | 29 => c2Zeroize32Addr + 5348#64
    | 30 => c2Zeroize32Addr + 5972#64
    | 31 => c2Zeroize32Addr + 7604#64
    | 32 => c2Zeroize32Addr + 8212#64
    | 33 => c2Zeroize32Addr + 9048#64
    | 36 => c2MemmoveAddr - 660#64
    | _  => 0#64
  ρ sym :=
    if sym == "curve25519_dalek:.rodata..Lanon.0" then c2DurationSinceCst16Addr + 3152#64
    else if sym == "curve25519_dalek:.rodata..Lanon.6" then c2DurationSinceCst16Addr + 3216#64
    else if sym == "curve25519_dalek:.rodata..Lanon.7" then c2DurationSinceCst16Addr + 3256#64
    else if sym == "curve25519_dalek:.rodata..Lanon.8" then c2DurationSinceCst16Addr + 3296#64
    else if sym == "curve25519_dalek:.rodata..Lanon.16" then c2DurationSinceCst16Addr + 3336#64
    else if sym == "curve25519_dalek:.rodata..Lanon.17" then c2DurationSinceCst16Addr + 3376#64
    else if sym == "curve25519_dalek:.rodata..Lanon.22" then c2DurationSinceCst16Addr + 3416#64
    else if sym == "curve25519_dalek:.rodata.cst32+0x0" then c2DurationSinceCst16Addr + 3456#64
    else if sym == "curve25519_dalek:.rodata..Lanon.36" then c2DurationSinceCst16Addr + 3528#64
    else if sym == "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.37" then
      c2DurationSinceCst16Addr + 11208#64
    else if sym == "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.38" then
      c2DurationSinceCst16Addr + 11232#64
    else if sym == "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" then
      0x47a2a4#64
    else 0#64

set_option maxRecDepth 2000000 in
/-- Kernel-checked `DalekActivePlaceable` witness for `c2DalekMpl` across all 8 phantom windows. -/
theorem c2DalekMpl_activePlaceable : DalekActivePlaceable c2DalekMpl :=
  dalekActivePlaceable_of_check (by rfl_kernel)

/-! ## 2. Symbol Resolution, `F3CodeInv` Discharges & Hull Inclusions -/

theorem resolve_scalarMod_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsScalarModSym = c2DalekMpl.base 1 :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_scalarWide_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsScalarWideSym = c2DalekMpl.base 2 :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_toEdwards_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsToEdwardsSym = c2DalekMpl.base 8 :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_compress_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsCompressSym = c2DalekMpl.base 14 :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_dsmb_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsDsmbSym = c2DalekMpl.base 17 :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_torsionFree_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsTorsionFreeSym = c2DalekMpl.base 19 :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_edNeg_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsEdNegSym = c2EdNegAddr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_mlkemPk1_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsMlkemPk1Sym = c2MlkemPk1Addr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

theorem resolve_mlkemPk2_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsMlkemPk2Sym = c2MlkemPk2Addr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

private def c2SharedDropWord : BitVec 32 :=
  Obj.branchWord 0x14000000#32 c2SharedSecretDropAddr c2Zeroize32Addr

private noncomputable def checkPureSubsliceR (rxBytes : List (BitVec 8)) (rxLen : Nat)
    (subProg : Program) : Bool :=
  let off := (subProg.base - f3RxSegBase).toNat
  let subLen := ProofLib.Placed.Split.rLen subProg.code
  Nat.beq (subProg.base.toNat % 4) 0 &&
  Nat.ble (subProg.base.toNat + subLen) (2 ^ 64) &&
  decide (f3RxSegBase + BitVec.ofNat 64 off = subProg.base) &&
  Nat.ble (off + subLen) rxLen &&
  (subProg.code == ProofLib.Placed.Split.rTake subLen (ProofLib.Placed.Split.rDrop off rxBytes))

private theorem codeLoaded_of_pureSubsliceR {subProg : Program} {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m)
    (h : checkPureSubsliceR f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes) subProg = true) :
    subProg.CodeLoaded m := by
  apply codeLoaded_of_checkProgCodeSubslice hRx
  unfold checkPureSubsliceR at h
  simp only [ProofLib.Placed.Split.rLen_eq, ProofLib.Placed.Split.rTake_eq,
    ProofLib.Placed.Split.rDrop_eq] at h
  unfold checkProgCodeSubslice
  rwa [f3TrialRxProg_base, f3TrialRxWordTree_eq]

private def relocsSorted (len : Nat) : Nat → List RelocEntry → Bool
  | _, [] => true
  | lb, r :: rs =>
    Nat.ble lb r.off && Nat.beq (r.off % 4) 0 && Nat.blt r.off len &&
      relocsSorted len (r.off + 1) rs

private theorem find?_reloc_append_of_lt {o : Nat} :
    ∀ {pre rs : List RelocEntry}, (∀ x ∈ pre, x.off < o) →
      (pre ++ rs).find? (·.off == o) = rs.find? (·.off == o)
  | [], _, _ => rfl
  | x :: xs, rs, hpre => by
    have hx : (x.off == o) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (hpre x (List.mem_cons_self ..)))
    simp only [List.cons_append, List.find?_cons, hx]
    exact find?_reloc_append_of_lt fun y hy => hpre y (List.mem_cons_of_mem _ hy)

private theorem find?_reloc_eq_none_of_gt {o len : Nat} :
    ∀ {lb : Nat} {rs : List RelocEntry}, o < lb → relocsSorted len lb rs = true →
      rs.find? (·.off == o) = none
  | _, [], _, _ => rfl
  | lb, r :: rs, hlt, hwf => by
    simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq] at hwf
    have hne : (r.off == o) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [List.find?_cons, hne]
    exact find?_reloc_eq_none_of_gt (by omega) hwf.2

private theorem patchedWord_unrelaxed (blk : CodeBlock) (pl : Placement)
    (hRel : pl.relax = fun _ => false) (hB2b : pl.b2b = fun _ => false)
    (hWeak : pl.undefWeak = fun _ => false) (o : Nat) :
    blk.patchedWord pl o =
      match blk.relocAt? o with
      | none => blk.wordAt o
      | some r =>
        patchRelocWord r.kind (blk.wordAt o) (pl.base + BitVec.ofNat 64 o) (blk.target pl r) := by
  unfold CodeBlock.patchedWord CodeBlock.relaxedAt CodeBlock.undefWeakBranch CodeBlock.relocTarget
  rw [hRel, hB2b, hWeak]
  cases blk.relocAt? o with
  | none => rfl
  | some r => simp

private def walkUnrelaxed (blk : CodeBlock) (pl : Placement) :
    Nat → List RelocEntry → List (BitVec 8) → List (BitVec 8) → Bool
  | _, _, [], _ => true
  | o, rs, b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss =>
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then
        let w := b3 ++ b2 ++ b1 ++ b0
        let place := pl.base + BitVec.ofNat 64 o
        bytesOfWordLE (patchRelocWord r.kind w place (blk.target pl r)) == [s0, s1, s2, s3] &&
          walkUnrelaxed blk pl (o + 4) rs' cs ss
      else
        b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 &&
          walkUnrelaxed blk pl (o + 4) rs cs ss
    | [] =>
      b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 &&
        walkUnrelaxed blk pl (o + 4) [] cs ss
  | _, _, _ :: _, _ => false

private theorem walkUnrelaxed_isPrefix {blk : CodeBlock} {pl : Placement}
    (hRel : pl.relax = fun _ => false) (hB2b : pl.b2b = fun _ => false)
    (hWeak : pl.undefWeak = fun _ => false) :
    ∀ (cs seg : List (BitVec 8)) (o : Nat) (pre rs : List RelocEntry),
      blk.code.drop o = cs → o % 4 = 0 → blk.code.length % 4 = 0 →
      blk.relocs = pre ++ rs → (∀ x ∈ pre, x.off < o) →
      relocsSorted blk.code.length o rs = true →
      walkUnrelaxed blk pl o rs cs seg = true →
      ((blk.patched pl).drop o).IsPrefix seg
  | [], seg, o, _, _, hcs, _, _, _, _, _, _ => by
    have hlen : blk.code.length ≤ o := by
      have := congrArg List.length hcs; simp at this; omega
    rw [List.drop_eq_nil_of_le (by rw [CodeBlock.length_patched]; omega)]
    exact List.nil_prefix
  | b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss, o, pre, rs,
      hcs, ho, hal, hrel, hpre, hwf, hw => by
    have hlen : o + 4 ≤ blk.code.length := by
      have := congrArg List.length hcs; simp at this; omega
    have hcs' : blk.code.drop (o + 4) = cs := by
      rw [← List.drop_drop, hcs]; rfl
    have htake := CodeBlock.take4_drop_patched (blk := blk) (pl := pl) ho hlen
    have hdrop : ((blk.patched pl).drop o).drop 4 = (blk.patched pl).drop (o + 4) := by
      rw [List.drop_drop, Nat.add_comm]
    have hw1 : blk.wordAt o = b3 ++ b2 ++ b1 ++ b0 := by
      unfold CodeBlock.wordAt
      rw [← Nat.add_zero o, getD_eq_drop_getD_word, hcs, wordOfBytesLE_cons4_zero]
    have hpw := patchedWord_unrelaxed blk pl hRel hB2b hWeak o
    match rs, hwf, hw with
    | [], _, hw =>
      simp only [walkUnrelaxed, Bool.and_eq_true, beq_iff_eq] at hw
      rcases hw with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hw'⟩
      have hnone : blk.relocAt? o = none := by
        unfold CodeBlock.relocAt?; rw [hrel, find?_reloc_append_of_lt hpre]; rfl
      have ih := walkUnrelaxed_isPrefix hRel hB2b hWeak cs ss (o + 4) pre []
        hcs' (by omega) hal hrel (fun x hx => by have := hpre x hx; omega) rfl hw'
      refine Obj.Interned.prefix_of_take_drop (k := 4) (t := [b0, b1, b2, b3])
        (htake.trans ?_) (by rw [hdrop]; exact ih) rfl
      rw [hpw, hnone, hw1, Obj.Interned.bytesOfWordLE_append4]
    | r :: rs', hwf, hw =>
      simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.blt_eq] at hwf
      rcases hwf with ⟨⟨⟨hlb, hmod⟩, hlt_len⟩, hwf'⟩
      simp only [walkUnrelaxed] at hw
      by_cases hro : r.off = o
      · have hbeq : Nat.beq r.off o = true := Nat.beq_eq.mpr hro
        simp only [hbeq, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hw
        obtain ⟨hbytes, hw'⟩ := hw
        have hsome : blk.relocAt? o = some r := by
          unfold CodeBlock.relocAt?
          rw [hrel, find?_reloc_append_of_lt hpre]
          simp [beq_iff_eq.mpr hro]
        have hwf4 : relocsSorted blk.code.length (o + 4) rs' = true := by
          cases rs' with
          | nil => rfl
          | cons r2 rs2 =>
            simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hwf' ⊢
            exact ⟨⟨⟨by omega, hwf'.1.1.2⟩, hwf'.1.2⟩, hwf'.2⟩
        have hrel' : blk.relocs = (pre ++ [r]) ++ rs' := by rw [List.append_assoc]; exact hrel
        have hpre' : ∀ x ∈ pre ++ [r], x.off < o + 4 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · have := hpre x hx; omega
          · rw [List.mem_singleton.mp hx]; omega
        have ih := walkUnrelaxed_isPrefix hRel hB2b hWeak cs ss (o + 4) (pre ++ [r]) rs'
          hcs' (by omega) hal hrel' hpre' hwf4 hw'
        refine Obj.Interned.prefix_of_take_drop (k := 4) (t := [s0, s1, s2, s3])
          (htake.trans ?_) (by rw [hdrop]; exact ih) rfl
        rw [hpw, hsome, hw1, hbytes]
      · have hbeq : Nat.beq r.off o = false :=
          Bool.eq_false_iff.mpr fun hc => hro (Nat.beq_eq.mp hc)
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hw
        rcases hw with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hw'⟩
        have hwf4 : relocsSorted blk.code.length (o + 4) (r :: rs') = true := by
          simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.blt_eq]
          exact ⟨⟨⟨by omega, hmod⟩, hlt_len⟩, hwf'⟩
        have hnone : blk.relocAt? o = none := by
          unfold CodeBlock.relocAt?
          rw [hrel, find?_reloc_append_of_lt hpre]
          exact find?_reloc_eq_none_of_gt (by omega) hwf4
        have ih := walkUnrelaxed_isPrefix hRel hB2b hWeak cs ss (o + 4) pre (r :: rs')
          hcs' (by omega) hal hrel (fun x hx => by have := hpre x hx; omega) hwf4 hw'
        refine Obj.Interned.prefix_of_take_drop (k := 4) (t := [b0, b1, b2, b3])
          (htake.trans ?_) (by rw [hdrop]; exact ih) rfl
        rw [hpw, hnone, hw1, Obj.Interned.bytesOfWordLE_append4]
  | [_], _, o, _, _, hcs, ho, hal, _, _, _, _ => by
    have := congrArg List.length hcs; simp at this; omega
  | [_, _], _, o, _, _, hcs, ho, hal, _, _, _, _ => by
    have := congrArg List.length hcs; simp at this; omega
  | [_, _, _], _, o, _, _, hcs, ho, hal, _, _, _, _ => by
    have := congrArg List.length hcs; simp at this; omega
  | _ :: _ :: _ :: _ :: _, [], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw
  | _ :: _ :: _ :: _ :: _, [_], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw
  | _ :: _ :: _ :: _ :: _, [_, _, _], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw

private noncomputable def checkBlockWalk (rxBytes : List (BitVec 8)) (rxLen : Nat)
    (lib : MultiPlacedLib) (mpl : MultiPlacement) (j : Nat) : Bool :=
  let blk := (lib.blockLib j).text
  let pl := lib.blockPlacement mpl j
  let len := ProofLib.Placed.Split.rLen blk.code
  let off := (pl.base - f3RxSegBase).toNat
  Nat.beq (len % 4) 0 &&
  Nat.beq (pl.base.toNat % 4) 0 &&
  Nat.ble (pl.base.toNat + len) (2 ^ 64) &&
  decide (f3RxSegBase + BitVec.ofNat 64 off = pl.base) &&
  Nat.ble (off + len) rxLen &&
  relocsSorted len 0 blk.relocs &&
  walkUnrelaxed blk pl 0 blk.relocs blk.code (ProofLib.Placed.Split.rDrop off rxBytes)

private theorem codeLoaded_of_blockWalk {j : Nat} {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m)
    (h : checkBlockWalk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes) dalekCliMultiLib c2DalekMpl j = true) :
    (dalekCliMultiLib.blockProgram c2DalekMpl j).CodeLoaded m := by
  apply codeLoaded_of_checkProgCodeSubslice hRx
  unfold checkBlockWalk at h
  dsimp only at h
  simp only [ProofLib.Placed.Split.rLen_eq, ProofLib.Placed.Split.rDrop_eq,
    Bool.and_eq_true, Nat.beq_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hal, hbase4⟩, hnowrap⟩, hbaseEq⟩, hbound⟩, hwf⟩, hwalk⟩
  let blk := (dalekCliMultiLib.blockLib j).text
  let pl := dalekCliMultiLib.blockPlacement c2DalekMpl j
  have hpre : (blk.patched pl).IsPrefix
      (f3TrialRxWordTree.toBytes.drop (pl.base - f3RxSegBase).toNat) :=
    walkUnrelaxed_isPrefix rfl rfl rfl blk.code _ 0 [] blk.relocs
      rfl rfl hal rfl (fun _ hx => nomatch hx) hwf hwalk
  obtain ⟨tail, htail⟩ := hpre
  have hplen : (blk.patched pl).length = blk.code.length :=
    CodeBlock.length_patched_of_aligned pl hal
  unfold checkProgCodeSubslice MultiPlacedLib.blockProgram PlacedLib.program
  rw [f3TrialRxProg_base, f3TrialRxWordTree_eq]
  dsimp only
  change (Nat.beq (pl.base.toNat % 4) 0 &&
    Nat.ble (pl.base.toNat + (blk.patched pl).length) (2 ^ 64) &&
    decide (f3RxSegBase + BitVec.ofNat 64 (pl.base - f3RxSegBase).toNat = pl.base) &&
    Nat.ble ((pl.base - f3RxSegBase).toNat + (blk.patched pl).length)
      f3TrialRxWordTree.toBytes.length &&
    ((blk.patched pl) ==
      (f3TrialRxWordTree.toBytes.drop (pl.base - f3RxSegBase).toNat).take
        (blk.patched pl).length)) = true
  rw [← htail, List.take_left, hplen]
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_self_eq_true]
  exact ⟨⟨⟨⟨hbase4, hnowrap⟩, hbaseEq⟩, hbound⟩, trivial⟩

set_option maxRecDepth 2000000 in
private theorem c2AllRxSlices_ok :
    (let rxBytes := f3TrialRxWordTree.toBytes
     let rxLen := ProofLib.Placed.Split.rLen rxBytes
     (dalekActiveBlocks.all fun j =>
        checkBlockWalk rxBytes rxLen dalekCliMultiLib c2DalekMpl j) &&
     checkPureSubsliceR rxBytes rxLen (pureWordsProg c2MlkemPk1Addr mlkemPk1Words) &&
     checkPureSubsliceR rxBytes rxLen (pureWordsProg c2MlkemPk2Addr mlkemPk2Words) &&
     checkPureSubsliceR rxBytes rxLen (pureWordsProg c2EdNegAddr edwardsPointNegWords) &&
     checkPureSubsliceR rxBytes rxLen (pureWordsProg c2SharedSecretDropAddr [c2SharedDropWord]) &&
     checkPureSubsliceR rxBytes rxLen (pureWordsProg c2Zeroize32Addr zeroize32Words)) = true := by
  rfl_kernel

private theorem c2DalekActiveCodeSlices_ok :
    (dalekActiveBlocks.all fun j =>
      checkBlockWalk f3TrialRxWordTree.toBytes
        (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
        dalekCliMultiLib c2DalekMpl j) = true := by
  have h := c2AllRxSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1

private theorem c2MlkemPk1Slice_ok :
    checkPureSubsliceR f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2MlkemPk1Addr mlkemPk1Words) = true := by
  have h := c2AllRxSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.2

private theorem c2MlkemPk2Slice_ok :
    checkPureSubsliceR f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2MlkemPk2Addr mlkemPk2Words) = true := by
  have h := c2AllRxSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1.1.1.2

private theorem c2EdNegSlice_ok :
    checkPureSubsliceR f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2EdNegAddr edwardsPointNegWords) = true := by
  have h := c2AllRxSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1.1.2

private theorem c2SharedDropSlice_ok :
    checkPureSubsliceR f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2SharedSecretDropAddr [c2SharedDropWord]) = true := by
  have h := c2AllRxSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.1.2

private theorem c2Zeroize32Slice_ok :
    checkPureSubsliceR f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes)
      (pureWordsProg c2Zeroize32Addr zeroize32Words) = true := by
  have h := c2AllRxSlices_ok; dsimp only at h
  simp only [Bool.and_eq_true] at h; exact h.2

theorem c2DalekMpl_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    DalekActiveCodeLoaded c2DalekMpl m :=
  fun j hj => codeLoaded_of_blockWalk hInv.rxCode
    (List.all_eq_true.mp c2DalekActiveCodeSlices_ok j hj)

private noncomputable def checkDalekRoAll (elf : Process.ElfImage) : Bool :=
  match ProofLib.Placed.Split.rGetD (elf.segments.map some) f3StdLayout.roSegIdx none with
  | none => false
  | some seg =>
    let roLen := ProofLib.Placed.Split.rLen seg.bytes
    decide (seg.perm.rwx = Perm.ro) &&
    checkSegSlice seg roLen (fe51_one c2DalekMpl) fe51OneBytes &&
    checkSegSlice seg roLen (fe51_edwards_d c2DalekMpl) fe51EdwardsDBytes &&
    checkSegSlice seg roLen (fe51_minus_one c2DalekMpl) fe51MinusOneBytes &&
    checkSegSlice seg roLen (fe51_sqrt_m1 c2DalekMpl) fe51SqrtM1Bytes &&
    checkSegSlice seg roLen (sc52_l c2DalekMpl) sc52LBytes &&
    checkSegSlice seg roLen (sc52_rr c2DalekMpl) sc52RRBytes &&
    checkSegSlice seg roLen (fe51_edwards_d2 c2DalekMpl) fe51EdwardsD2Bytes &&
    checkSegSlice seg roLen (basepoint_order c2DalekMpl) basepointOrderBytes &&
    checkSegSlice seg roLen (odd_multiples_basepoint c2DalekMpl) oddMultiplesBasepointBytes

set_option maxRecDepth 4000000 in
private theorem c2DalekRoSlices_ok : checkDalekRoAll f3PatchedElf = true := by
  rfl_kernel

private theorem rGetD_map_some_eq_getElem? {α : Type} (l : List α) (n : Nat) :
    ProofLib.Placed.Split.rGetD (l.map some) n none = l[n]? := by
  rw [ProofLib.Placed.Split.rGetD_eq]
  induction l generalizing n with
  | nil => simp
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

theorem c2DalekMpl_roOk_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    DalekActiveRoOk c2DalekMpl m := by
  have h := c2DalekRoSlices_ok
  unfold checkDalekRoAll at h
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : f3PatchedElf.segments[f3StdLayout.roSegIdx]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [ProofLib.Placed.Split.rLen_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hperm, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
    exact
      { ro_fe51_one := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h1⟩
        ro_fe51_edwards_d := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h2⟩
        ro_fe51_minus_one := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h3⟩
        ro_fe51_sqrt_m1 := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h4⟩
        ro_sc52_l := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h5⟩
        ro_sc52_rr := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h6⟩
        ro_fe51_edwards_d2 := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h7⟩
        ro_basepoint_order := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h8⟩
        ro_odd_multiples_basepoint := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _
          ⟨seg, hseg, hperm, h9⟩ }

theorem c2DalekMpl_activeCodeAndRo_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    DalekActiveCodeLoaded c2DalekMpl m ∧ DalekActiveRoOk c2DalekMpl m :=
  ⟨c2DalekMpl_codeLoaded_of_f3CodeInv hInv, c2DalekMpl_roOk_of_f3CodeInv hLs hInv⟩

theorem c2DalekMpl_invMem_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    dalekActiveInvMem c2DalekMpl m :=
  ⟨c2DalekMpl_activePlaceable, c2DalekMpl_codeLoaded_of_f3CodeInv hInv,
   c2DalekMpl_roOk_of_f3CodeInv hLs hInv⟩

private theorem progKeep_sub_interval {P : Program} {lo hi pc : BitVec 64}
    (hlo : lo.toNat ≤ P.base.toNat)
    (hhi : P.base.toNat + P.code.length ≤ hi.toNat)
    (hk : progKeep P pc = true) :
    decide (lo.toNat ≤ pc.toNat ∧ pc.toNat < hi.toNat) = true := by
  unfold progKeep at hk
  rw [decide_eq_true_eq] at hk ⊢
  have hhi_lt : hi.toNat < 2 ^ 64 := BitVec.isLt hi
  have hsub : P.base.toNat ≤ pc.toNat ∧ pc.toNat < P.base.toNat + P.code.length := by bv_omega
  omega

set_option maxRecDepth 2000000 in
private theorem c2DalekLib2Bounds_ok :
    ((dalekActiveBlocks.erase 36).all fun j =>
      let Pj := dalekCliMultiLib.blockProgram c2DalekMpl j
      Nat.ble 0x47ac2c Pj.base.toNat &&
        Nat.ble (Pj.base.toNat + Pj.code.length) 0x4cb070) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
private theorem c2DalekBlk36Bounds_ok :
    (let P36 := dalekCliMultiLib.blockProgram c2DalekMpl 36
     Nat.ble c2TextBPreLo.toNat P36.base.toNat &&
       Nat.ble (P36.base.toNat + P36.code.length) c2TextBPreHi.toNat) = true := by
  rfl_kernel

/-- Every `.text.lib2` active Dalek block (`B00..B33`) sits inside `keepLib2Text`. -/
theorem c2DalekMpl_lib2Block_sub_keepLib2Text {j : Nat}
    (hj : j ∈ dalekActiveBlocks.erase 36) {pc : BitVec 64}
    (hk : progKeep (dalekCliMultiLib.blockProgram c2DalekMpl j) pc = true) :
    keepLib2Text pc = true := by
  have hb := List.all_eq_true.mp c2DalekLib2Bounds_ok j hj
  dsimp only at hb
  simp only [Bool.and_eq_true, Nat.ble_eq] at hb
  exact progKeep_sub_interval
    (Nat.le_trans (by decide : c2Lib2TextLo.toNat ≤ 0x47ac2c) hb.1)
    (Nat.le_trans hb.2 (by decide : 0x4cb070 ≤ c2Lib2TextHi.toNat)) hk

theorem c2DalekMpl_lib2Block_noPanic {j : Nat}
    (hj : j ∈ dalekActiveBlocks.erase 36) {pc : BitVec 64}
    (hk : progKeep (dalekCliMultiLib.blockProgram c2DalekMpl j) pc = true) :
    isLinkedPanicAddr pc = false := by
  have hb := List.all_eq_true.mp c2DalekLib2Bounds_ok j hj
  dsimp only at hb
  simp only [Bool.and_eq_true, Nat.ble_eq] at hb
  have hint := progKeep_sub_interval (lo := 0x47ac2c#64) (hi := 0x4cb070#64) hb.1 hb.2 hk
  obtain ⟨hlo, hhi⟩ := of_decide_eq_true hint
  exact isLinkedPanicAddr_false_of_mid hlo hhi

/-- Every active Dalek block sits inside `keepTextBPre ∪ keepLib2Text` (`B00..B33` in
    `keepLib2Text`, `B36 = memcpy` in `keepTextBPre`). -/
theorem c2DalekMpl_keep_sub_rxRegion (pc : BitVec 64)
    (hk : dalekActiveKeep c2DalekMpl pc = true) :
    keepTextBPre pc = true ∨ keepLib2Text pc = true := by
  unfold dalekActiveKeep at hk
  rw [List.any_eq_true] at hk
  rcases hk with ⟨j, hj, hkj⟩
  by_cases hj36 : j = 36
  · subst hj36
    have hb := c2DalekBlk36Bounds_ok
    dsimp only at hb
    simp only [Bool.and_eq_true, Nat.ble_eq] at hb
    exact Or.inl (progKeep_sub_interval hb.1 hb.2 hkj)
  · exact Or.inr (c2DalekMpl_lib2Block_sub_keepLib2Text
      (List.mem_erase_of_ne hj36 |>.mpr hj) hkj)

theorem c2DalekMpl_keep_sub_rxProg {pc : BitVec 64}
    (hk : dalekActiveKeep c2DalekMpl pc = true) :
    progKeep f3TrialRxProg pc = true := by
  rcases c2DalekMpl_keep_sub_rxRegion pc hk with hb | hl
  · exact keepTextBPre_sub_rxProg hb
  · exact keepLib2Text_sub_rxProg hl

theorem c2DalekMpl_keep_lr_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (lr : BitVec 64) (hRet : LsRetAddr624 lr) :
    dalekActiveKeep c2DalekMpl lr = false := by
  have hsym : keepLib2Text (libsignalSessionLib.resolve lsmpl lsToEdwardsSym) = true := by
    rw [resolve_toEdwards_eq hLs]
    decide
  exact (f3LsRetAddr624_rxRegion_guard hLs hRet (Or.inr hsym) c2DalekMpl_keep_sub_rxRegion).1

theorem c2DalekMpl_keep_noPanic {pc : BitVec 64}
    (hk : dalekActiveKeep c2DalekMpl pc = true) :
    isLinkedPanicAddr pc = false := by
  unfold dalekActiveKeep at hk
  rw [List.any_eq_true] at hk
  rcases hk with ⟨j, hj, hkj⟩
  by_cases hj36 : j = 36
  · subst hj36
    have hb := c2DalekBlk36Bounds_ok
    dsimp only at hb
    simp only [Bool.and_eq_true, Nat.ble_eq] at hb
    exact isLinkedPanicAddr_false_of_keepTextBPre (progKeep_sub_interval hb.1 hb.2 hkj)
  · exact c2DalekMpl_lib2Block_noPanic (List.mem_erase_of_ne hj36 |>.mpr hj) hkj

theorem c2DalekMpl_realNoExt {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl) (W : CliHooks) {pc : BitVec 64}
    (hk : dalekActiveKeep c2DalekMpl pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  hExt.realRxNoExtern mmpl W (c2DalekMpl_keep_sub_rxProg hk) (c2DalekMpl_keep_noPanic hk)

/-! ## 3. `GhostRowOk` and `HookNoAllocFailed` for the 6 `dalekCliMultiLib` and 2 ML-KEM Rows -/

private theorem extraRowSpec_toEdwards [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsToEdwardsSym f = DalekMontToEdRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_compress [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsCompressSym f = DalekCompressRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_edNeg [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsEdNegSym f = EdNegRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_torsionFree [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsTorsionFreeSym f = DalekTorsionFreeRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_dsmb [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsDsmbSym f = DalekDsmbRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_scalarMod [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsScalarModSym f = DalekScalarModRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_scalarWide [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsScalarWideSym f = DalekScalarWideRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_mlkemPk1 [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsMlkemPk1Sym f = MlkemPk1RowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem extraRowSpec_mlkemPk2 [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsMlkemPk2Sym f = MlkemPk2RowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

private theorem ghostRowReplayOn_of_guard_imp
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {g1 g2 : State → Prop} {f : State → State}
    (h : GhostRowReplayOn mpl mmpl InvS EG sym g1 f)
    (himp : ∀ s0, g2 s0 → g1 s0) :
    GhostRowReplayOn mpl mmpl InvS EG sym g2 f :=
  ⟨h.preserves_execFrozen, fun W s0 sf hg2 => h.replay_at_stub W s0 sf (himp s0 hg2)⟩

theorem c2_toEdwardsGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsToEdwardsSym (dalekMontToEdGhostLs c2DalekMpl) where
  fs_eq s := (dalekMontToEdGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.1
  fsT := dalekMontToEdGhostLs_fsT c2DalekMpl
  rowSpec := (extraRowSpec_toEdwards _).symm ▸
    dalekMontToEdGhostLs_rowSpec c2DalekMpl

theorem c2_compressGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsCompressSym (dalekCompressGhostLs c2DalekMpl) where
  fs_eq s := (dalekCompressGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.1
  fsT := dalekCompressGhostLs_fsT c2DalekMpl
  rowSpec := (extraRowSpec_compress _).symm ▸
    dalekCompressGhostLs_rowSpec c2DalekMpl

theorem c2_torsionFreeGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsTorsionFreeSym (dalekTorsionFreeGhostLs c2DalekMpl) where
  fs_eq s := (dalekTorsionFreeGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.1
  fsT := dalekTorsionFreeGhostLs_fsT c2DalekMpl
  rowSpec := (extraRowSpec_torsionFree _).symm ▸
    dalekTorsionFreeGhostLs_rowSpec c2DalekMpl

theorem c2_dsmbGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsDsmbSym (dalekDsmbGhostLs c2DalekMpl) where
  fs_eq s := (dalekDsmbGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.1
  fsT := dalekDsmbGhostLs_fsT c2DalekMpl
  rowSpec := (extraRowSpec_dsmb _).symm ▸
    dalekDsmbGhostLs_rowSpec c2DalekMpl

theorem c2_scalarModGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsScalarModSym (dalekScalarModGhostLs c2DalekMpl) where
  fs_eq s := (dalekScalarModGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.1
  fsT := dalekScalarModGhostLs_fsT c2DalekMpl
  rowSpec := (extraRowSpec_scalarMod _).symm ▸
    dalekScalarModGhostLs_rowSpec c2DalekMpl

theorem c2_scalarWideGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsScalarWideSym (dalekScalarWideGhostLs c2DalekMpl) where
  fs_eq s := (dalekScalarWideGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.1
  fsT := dalekScalarWideGhostLs_fsT c2DalekMpl
  rowSpec := (extraRowSpec_scalarWide _).symm ▸
    dalekScalarWideGhostLs_rowSpec c2DalekMpl

theorem c2_toEdwardsGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsToEdwardsSym (c2GuardOf lsmpl lsToEdwardsSym)
      (dalekMontToEdGhostLs c2DalekMpl) :=
  ⟨c2_toEdwardsGhost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (dalekMontToEdGhostLs_rowReplayOn lsmpl mmpl c2DalekMpl _ _
       c2DalekMpl_activePlaceable (resolve_toEdwards_eq hLs)
       (fun _ hu => c2DalekMpl_invMem_of_f3CodeInv hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2DalekMpl_keep_lr_false hLs) (c2DalekMpl_realNoExt (c2ExternTableFacts_lsmpl hLs)))
     (fun _ _ => trivial)⟩

theorem c2_compressGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsCompressSym (c2GuardOf lsmpl lsCompressSym)
      (dalekCompressGhostLs c2DalekMpl) :=
  ⟨c2_compressGhost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (dalekCompressGhostLs_rowReplayOn lsmpl mmpl c2DalekMpl _ _
       c2DalekMpl_activePlaceable (resolve_compress_eq hLs)
       (fun _ hu => c2DalekMpl_invMem_of_f3CodeInv hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2DalekMpl_keep_lr_false hLs) (c2DalekMpl_realNoExt (c2ExternTableFacts_lsmpl hLs)))
     (fun _ _ => trivial)⟩

theorem c2_torsionFreeGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTorsionFreeSym (c2GuardOf lsmpl lsTorsionFreeSym)
      (dalekTorsionFreeGhostLs c2DalekMpl) :=
  ⟨c2_torsionFreeGhost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (dalekTorsionFreeGhostLs_rowReplayOn lsmpl mmpl c2DalekMpl _ _
       c2DalekMpl_activePlaceable (resolve_torsionFree_eq hLs)
       (fun _ hu => c2DalekMpl_invMem_of_f3CodeInv hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2DalekMpl_keep_lr_false hLs) (c2DalekMpl_realNoExt (c2ExternTableFacts_lsmpl hLs)))
     (fun _ _ => trivial)⟩

theorem c2_dsmbGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsDsmbSym (c2GuardOf lsmpl lsDsmbSym)
      (dalekDsmbGhostLs c2DalekMpl) :=
  ⟨c2_dsmbGhost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (dalekDsmbGhostLs_rowReplayOn lsmpl mmpl c2DalekMpl _ _
       c2DalekMpl_activePlaceable (resolve_dsmb_eq hLs)
       (fun _ hu => c2DalekMpl_invMem_of_f3CodeInv hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2DalekMpl_keep_lr_false hLs) (c2DalekMpl_realNoExt (c2ExternTableFacts_lsmpl hLs)))
     (fun _ _ => trivial)⟩

theorem c2_scalarModGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsScalarModSym (c2GuardOf lsmpl lsScalarModSym)
      (dalekScalarModGhostLs c2DalekMpl) :=
  ⟨c2_scalarModGhost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (dalekScalarModGhostLs_rowReplayOn lsmpl mmpl c2DalekMpl _ _
       c2DalekMpl_activePlaceable (resolve_scalarMod_eq hLs)
       (fun _ hu => c2DalekMpl_invMem_of_f3CodeInv hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2DalekMpl_keep_lr_false hLs) (c2DalekMpl_realNoExt (c2ExternTableFacts_lsmpl hLs)))
     (fun _ _ => trivial)⟩

theorem c2_scalarWideGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsScalarWideSym (c2GuardOf lsmpl lsScalarWideSym)
      (dalekScalarWideGhostLs c2DalekMpl) :=
  ⟨c2_scalarWideGhost_rowSpecOk,
   ghostRowReplayOn_of_guard_imp
     (dalekScalarWideGhostLs_rowReplayOn lsmpl mmpl c2DalekMpl _ _
       c2DalekMpl_activePlaceable (resolve_scalarWide_eq hLs)
       (fun _ hu => c2DalekMpl_invMem_of_f3CodeInv hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2DalekMpl_keep_lr_false hLs) (c2DalekMpl_realNoExt (c2ExternTableFacts_lsmpl hLs)))
     (fun _ _ => trivial)⟩

theorem c2_toEdwardsGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (dalekMontToEdGhostLs c2DalekMpl) :=
  hookNoAllocFailed_of_trace_eq _ fun s =>
    (dalekMontToEdGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.2.1

theorem c2_compressGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (dalekCompressGhostLs c2DalekMpl) :=
  hookNoAllocFailed_of_trace_eq _ fun s =>
    (dalekCompressGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.2.1

theorem c2_torsionFreeGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (dalekTorsionFreeGhostLs c2DalekMpl) :=
  hookNoAllocFailed_of_trace_eq _ fun s =>
    (dalekTorsionFreeGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.2.1

theorem c2_dsmbGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (dalekDsmbGhostLs c2DalekMpl) :=
  hookNoAllocFailed_of_trace_eq _ fun s =>
    (dalekDsmbGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.2.1

theorem c2_scalarModGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (dalekScalarModGhostLs c2DalekMpl) :=
  hookNoAllocFailed_of_trace_eq _ fun s =>
    (dalekScalarModGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.2.1

theorem c2_scalarWideGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (dalekScalarWideGhostLs c2DalekMpl) :=
  hookNoAllocFailed_of_trace_eq _ fun s =>
    (dalekScalarWideGhostLs_vmPreserved_and_nonSyscall c2DalekMpl s).2.2.1

theorem c2_mlkemPk1Hook_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemPk1Sym mlkemPk1Hook where
  fs_eq := fun _ => rfl
  fsT := mlkemPk1Hook_fsT
  rowSpec := (extraRowSpec_mlkemPk1 _).symm ▸ mlkemPk1Hook_rowSpec

theorem c2_mlkemPk2Hook_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemPk2Sym mlkemPk2Hook where
  fs_eq := fun _ => rfl
  fsT := mlkemPk2Hook_fsT
  rowSpec := (extraRowSpec_mlkemPk2 _).symm ▸ mlkemPk2Hook_rowSpec

private theorem setPC_eq_self {u : State} {pc : BitVec 64} (h : u.pc = pc) :
    u.setPC pc = u := by
  cases u; dsimp only [State.setPC] at h ⊢; subst h; rfl

theorem c2_mlkemPk1Hook_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMlkemPk1Sym (c2GuardOf lsmpl lsMlkemPk1Sym) mlkemPk1Hook := by
  refine ⟨c2_mlkemPk1Hook_rowSpecOk, ?_⟩
  refine { preserves_execFrozen := fun u _ _ hfr => ⟨hfr, rfl⟩, replay_at_stub := ?_ }
  dsimp only
  intro W s0 sf _ _ _ _
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_mlkemPk1_eq hLs
  have hk0 : keepLib2Text c2MlkemPk1Addr = true := by decide
  have hk4 : keepLib2Text (c2MlkemPk1Addr + 4#64) = true := by decide
  have hnp0 : isLinkedPanicAddr c2MlkemPk1Addr = false := by decide
  have hnp4 : isLinkedPanicAddr (c2MlkemPk1Addr + 4#64) = false := by decide
  refine Or.inr ⟨hRes ▸ hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk0) hnp0, ?_⟩
  intro u _ _ hpc hrun _ hkf hfr hinv
  have hpc' : u.pc = c2MlkemPk1Addr := hpc.trans hRes
  have hst := steps_mlkemPk1_of_hasWords
    (P_rx := pureWordsProg c2MlkemPk1Addr mlkemPk1Words)
    (codeLoaded_of_pureSubsliceR hinv.1.rxCode c2MlkemPk1Slice_ok)
    (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel))
    (pureWordsProg_externAt_none _ _ _)
    (pureWordsProg_externAt_none _ _ _)
    (hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk0) hnp0)
    (hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk4) hnp4)
    hrun
  rw [setPC_eq_self hpc'] at hst
  exact ⟨hst, hfr, f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs u (mlkemPk1Hook u) hinv hkf rfl⟩

theorem c2_mlkemPk2Hook_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMlkemPk2Sym (c2GuardOf lsmpl lsMlkemPk2Sym) mlkemPk2Hook := by
  refine ⟨c2_mlkemPk2Hook_rowSpecOk, ?_⟩
  refine { preserves_execFrozen := fun u _ _ hfr => ⟨hfr, rfl⟩, replay_at_stub := ?_ }
  dsimp only
  intro W s0 sf _ _ _ _
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_mlkemPk2_eq hLs
  have hk0 : keepLib2Text c2MlkemPk2Addr = true := by decide
  have hk4 : keepLib2Text (c2MlkemPk2Addr + 4#64) = true := by decide
  have hnp0 : isLinkedPanicAddr c2MlkemPk2Addr = false := by decide
  have hnp4 : isLinkedPanicAddr (c2MlkemPk2Addr + 4#64) = false := by decide
  refine Or.inr ⟨hRes ▸ hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk0) hnp0, ?_⟩
  intro u _ _ hpc hrun _ hkf hfr hinv
  have hpc' : u.pc = c2MlkemPk2Addr := hpc.trans hRes
  have hst := steps_mlkemPk2_of_hasWords
    (P_rx := pureWordsProg c2MlkemPk2Addr mlkemPk2Words)
    (codeLoaded_of_pureSubsliceR hinv.1.rxCode c2MlkemPk2Slice_ok)
    (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel))
    (pureWordsProg_externAt_none _ _ _)
    (pureWordsProg_externAt_none _ _ _)
    (hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk0) hnp0)
    (hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk4) hnp4)
    hrun
  rw [setPC_eq_self hpc'] at hst
  exact ⟨hst, hfr, f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs u (mlkemPk2Hook u) hinv hkf rfl⟩

theorem c2_mlkemPk1Hook_noAllocFailed : HookNoAllocFailed mlkemPk1Hook :=
  hookNoAllocFailed_of_trace_eq _ fun _ => rfl

theorem c2_mlkemPk2Hook_noAllocFailed : HookNoAllocFailed mlkemPk2Hook :=
  hookNoAllocFailed_of_trace_eq _ fun _ => rfl

/-! ## 4. Sentinel-`lr` Straight-Line `edNegSentinelGhost` (`lsEdNegSym`, `entryGuard := True`) -/

/-- Straight-line 57-instruction `<EdwardsPoint as Neg>::neg` ghost hook substituting sentinel
    return address `entry + 0xe4#64` during `narrowEdNegGhostHook` execution and restoring the
    caller's `.lr` and `pc` upon return, eliminating any caller-`lr` region hypothesis. -/
@[expose] noncomputable def edNegSentinelGhost (entry : BitVec 64) (u : State) : State :=
  let lr0 := u.readReg64 .lr
  let u_sent := u.writeReg64 .lr (entry + 0xe4#64)
  let sf_sent := narrowEdNegGhostHook entry u_sent
  if sf_sent.status == .Running then
    (sf_sent.writeReg64 .lr lr0).setPC lr0
  else
    sf_sent

theorem edNegSentinelGhost_fs (entry : BitVec 64) (u : State) :
    (edNegSentinelGhost entry u).fs = u.fs := by
  dsimp only [edNegSentinelGhost]
  have hfs := narrowEdNegGhostHook_fs entry (u.writeReg64 .lr (entry + 0xe4#64))
  have hfs_w : (u.writeReg64 .lr (entry + 0xe4#64)).fs = u.fs := by cases u; rfl
  split
  · generalize narrowEdNegGhostHook entry (u.writeReg64 .lr (entry + 0xe4#64)) = sf at hfs ⊢
    cases sf; exact hfs.trans hfs_w
  · exact hfs.trans hfs_w

theorem edNegSentinelGhost_trace (entry : BitVec 64) (u : State) :
    (edNegSentinelGhost entry u).trace =
      (narrowEdNegGhostHook entry (u.writeReg64 .lr (entry + 0xe4#64))).trace := by
  dsimp only [edNegSentinelGhost]
  split
  · generalize narrowEdNegGhostHook entry (u.writeReg64 .lr (entry + 0xe4#64)) = sf
    cases sf; rfl
  · rfl

theorem edNegSentinelGhost_fsT (entry : BitVec 64) :
    HookFsTraced IsFsC (edNegSentinelGhost entry) := by
  intro u
  rcases narrowEdNegGhostHook_fsT entry (u.writeReg64 .lr (entry + 0xe4#64)) with ⟨d, hd, _⟩
  have htr_u : (u.writeReg64 .lr (entry + 0xe4#64)).trace = u.trace := by cases u; rfl
  exact FsTraced.of_files d
    ((edNegSentinelGhost_trace entry u).trans (hd.trans (congrArg (· ++ d) htr_u)))
    (congrArg (·.files) (edNegSentinelGhost_fs entry u))

theorem edNegSentinelGhost_vmPreserved (entry : BitVec 64) (u : State) :
    VmPreserved u (edNegSentinelGhost entry u) := by
  have hvm := narrowEdNegGhostHook_vmPreserved entry (u.writeReg64 .lr (entry + 0xe4#64))
  dsimp only [edNegSentinelGhost]
  split
  · generalize narrowEdNegGhostHook entry (u.writeReg64 .lr (entry + 0xe4#64)) = sf at hvm ⊢
    rcases u with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    rcases sf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    exact hvm
  · generalize narrowEdNegGhostHook entry (u.writeReg64 .lr (entry + 0xe4#64)) = sf at hvm ⊢
    rcases u with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    exact hvm

theorem edNegSentinelGhost_preserves_execFrozen {entry : BitVec 64} {u : State}
    (_hrun : u.status = .Running)
    (_hnoex : ∀ msg, (edNegSentinelGhost entry u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem) :
    ExecFrozen (edNegSentinelGhost entry u).mem := by
  have hmem_u : (u.writeReg64 .lr (entry + 0xe4#64)).mem = u.mem := by cases u; rfl
  have hfr_sf : ExecFrozen (narrowEdNegGhostHook entry (u.writeReg64 .lr (entry + 0xe4#64))).mem :=
    narrowEdNegGhostHook_preserves_execFrozen entry (hmem_u ▸ hfr)
  dsimp only [edNegSentinelGhost]
  split
  · generalize narrowEdNegGhostHook entry (u.writeReg64 .lr (entry + 0xe4#64)) = sf at hfr_sf ⊢
    have hm : ((sf.writeReg64 .lr (u.readReg64 .lr)).setPC (u.readReg64 .lr)).mem = sf.mem := by
      cases sf; rfl
    rwa [hm]
  · exact hfr_sf

private theorem sentinel_returned {u sf_s : State} {sent : BitVec 64}
    (hret : Returned (u.writeReg64 .lr sent) sf_s) :
    Returned u ((sf_s.writeReg64 .lr (u.readReg64 .lr)).setPC (u.readReg64 .lr)) := by
  let lr0 := u.readReg64 .lr
  let sf := (sf_s.writeReg64 .lr lr0).setPC lr0
  have hsp1 : sf.sp = sf_s.sp := by cases sf_s; rfl
  have hsp2 : (u.writeReg64 .lr sent).sp = u.sp := by cases u; rfl
  exact ⟨by cases sf_s; rfl, hsp1.trans (hret.2.1.trans hsp2), by cases sf_s; exact hret.2.2⟩

private theorem sentinel_ccPreserved {u sf_s : State} {sent : BitVec 64}
    (hcc : CallingConventionPreserved (u.writeReg64 .lr sent) sf_s) :
    CallingConventionPreserved u
      ((sf_s.writeReg64 .lr (u.readReg64 .lr)).setPC (u.readReg64 .lr)) := by
  let lr0 := u.readReg64 .lr
  let sf := (sf_s.writeReg64 .lr lr0).setPC lr0
  have hreg : ∀ r : Reg, r ≠ .lr →
      sf_s.readReg64 r = (u.writeReg64 .lr sent).readReg64 r →
      sf.readReg64 r = u.readReg64 r := fun r hne h => by
    have h1 : sf.readReg64 r = (sf_s.writeReg64 .lr lr0).readReg64 r := by cases sf_s; rfl
    exact h1.trans ((State.readReg64_writeReg64_ne sf_s .lr r lr0 hne).trans
      (h.trans (State.readReg64_writeReg64_ne u .lr r sent hne)))
  rcases hcc with ⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
  have hsp1 : sf.sp = sf_s.sp := by cases sf_s; rfl
  have hsp2 : (u.writeReg64 .lr sent).sp = u.sp := by cases u; rfl
  have hv1 : Arm64.calleeSavedVRegs sf = Arm64.calleeSavedVRegs sf_s := by cases sf_s; rfl
  have hv2 : Arm64.calleeSavedVRegs (u.writeReg64 .lr sent) = Arm64.calleeSavedVRegs u := by
    cases u; rfl
  exact ⟨hsp1.trans (hsp.trans hsp2),
    hreg _ (by decide) h19, hreg _ (by decide) h20, hreg _ (by decide) h21,
    hreg _ (by decide) h22, hreg _ (by decide) h23, hreg _ (by decide) h24,
    hreg _ (by decide) h25, hreg _ (by decide) h26, hreg _ (by decide) h27,
    hreg _ (by decide) h28, hreg _ (by decide) hfp,
    hv1.trans (hv.trans hv2)⟩

private theorem sentinel_statePreserved {u sf_s : State} {sent : BitVec 64}
    (h : EdNegStatePreserved (u.writeReg64 .lr sent) sf_s) :
    EdNegStatePreserved u
      ((sf_s.writeReg64 .lr (u.readReg64 .lr)).setPC (u.readReg64 .lr)) := by
  let lr0 := u.readReg64 .lr
  let sf := (sf_s.writeReg64 .lr lr0).setPC lr0
  let u_s := u.writeReg64 .lr sent
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨(show sf.fs = sf_s.fs by cases sf_s; rfl).trans
      (h1.trans (show u_s.fs = u.fs by cases u; rfl)),
    (show sf.trace = sf_s.trace by cases sf_s; rfl).trans
      (h2.trans (show u_s.trace = u.trace by cases u; rfl)),
    (show sf.tpidrEl0 = sf_s.tpidrEl0 by cases sf_s; rfl).trans
      (h3.trans (show u_s.tpidrEl0 = u.tpidrEl0 by cases u; rfl)),
    (show sf.sigActions = sf_s.sigActions by cases sf_s; rfl).trans
      (h4.trans (show u_s.sigActions = u.sigActions by cases u; rfl)),
    (show sf.brk = sf_s.brk by cases sf_s; rfl).trans
      (h5.trans (show u_s.brk = u.brk by cases u; rfl)),
    (show sf.brkStart = sf_s.brkStart by cases sf_s; rfl).trans
      (h6.trans (show u_s.brkStart = u.brkStart by cases u; rfl)),
    (show sf.physMemAvail = sf_s.physMemAvail by cases sf_s; rfl).trans
      (h7.trans (show u_s.physMemAvail = u.physMemAvail by cases u; rfl))⟩

theorem edNegSentinelGhost_master_ok (entry : BitVec 64) :
    HookOk (edNegSentinelGhost entry) masterEdNegSpec := by
  intro ⟨inA, v, ret⟩ R u hrun hpre hsp_u
  let lr0 := u.readReg64 .lr
  let u_sent := u.writeReg64 .lr (entry + 0xe4#64)
  have hrun_sent : u_sent.status = .Running := by cases u; exact hrun
  have hsp_sent : u_sent.spAligned = true := by cases u; exact hsp_u
  have hpre_eq : masterEdNegSpec.pre (inA, v, ret) u_sent = masterEdNegSpec.pre (inA, v, ret) u := by
    dsimp only [u_sent, masterEdNegSpec]
    rw [State.readReg64_writeReg64_ne u .lr .x0 _ (by decide),
        State.readReg64_writeReg64_ne u .lr .x8 _ (by decide)]
  have hmem_sent : u_sent.mem = u.mem := by cases u; rfl
  obtain ⟨hkf_s, hsym_s, hout⟩ := narrowEdNegGhostHook_master_ok entry (inA, v, ret) R u_sent hrun_sent
    (hmem_sent ▸ hpre_eq ▸ hpre) hsp_sent
  rcases hout with ⟨hret_s, hcc_s, hpost_s⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · have hrun_sf : (narrowEdNegGhostHook entry u_sent).status = .Running := hret_s.2.2
    have hbe : (ExecStatus.Running == .Running) = true := rfl
    have hghost_eq : edNegSentinelGhost entry u =
        ((narrowEdNegGhostHook entry u_sent).writeReg64 .lr lr0).setPC lr0 := by
      dsimp only [edNegSentinelGhost, lr0, u_sent]
      rw [hrun_sf, hbe]; rfl
    rw [hghost_eq]
    generalize narrowEdNegGhostHook entry u_sent = sf_s at hkf_s hsym_s hret_s hcc_s hpost_s
    let sf := (sf_s.writeReg64 .lr lr0).setPC lr0
    have hkf_out : u.mem.KeepsFrozen sf.mem := by
      have hm1 : sf.mem = sf_s.mem := by cases sf_s; rfl
      rw [hm1, ← hmem_sent]; exact hkf_s
    have hsym_out : sf.symtab = u.symtab := by
      have hs1 : sf.symtab = sf_s.symtab := by cases sf_s; rfl
      have hs2 : u_sent.symtab = u.symtab := by cases u; rfl
      exact hs1.trans (hsym_s.trans hs2)
    refine ⟨hkf_out, hsym_out, Or.inl ⟨sentinel_returned hret_s, sentinel_ccPreserved hcc_s, ?_⟩⟩
    dsimp only [masterEdNegSpec] at hpost_s ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_s ⊢
    have hmem_sf : sf.mem = sf_s.mem := by cases sf_s; rfl
    rw [hmem_sf]
    exact ⟨sentinel_statePreserved hpost_s.1, hpost_s.2⟩
  · dsimp only [masterEdNegSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [masterEdNegSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [masterEdNegSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem c2_edNegGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsEdNegSym (edNegSentinelGhost c2EdNegAddr) where
  fs_eq := edNegSentinelGhost_fs c2EdNegAddr
  fsT := edNegSentinelGhost_fsT c2EdNegAddr
  rowSpec := (extraRowSpec_edNeg _).symm ▸
    ⟨edNegSentinelGhost_master_ok c2EdNegAddr, edNegSentinelGhost_vmPreserved c2EdNegAddr⟩

theorem c2_edNegGhost_noAllocFailed : HookNoAllocFailed (edNegSentinelGhost c2EdNegAddr) := by
  classical
  intro s0
  let u_sent := s0.writeReg64 .lr (c2EdNegAddr + 0xe4#64)
  have htr_eq : (edNegSentinelGhost c2EdNegAddr s0).trace = (narrowEdNegGhostHook c2EdNegAddr u_sent).trace :=
    edNegSentinelGhost_trace c2EdNegAddr s0
  have htr_u : u_sent.trace = s0.trace := by cases s0; rfl
  have hna : LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.TraceDeltaNoAllocFailed
      u_sent (narrowEdNegGhostHook c2EdNegAddr u_sent) := by
    dsimp only [narrowEdNegGhostHook]
    rw [f3EmptyEdNegGhostHook_eq]
    unfold CryptoHooksDehook.edNegGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.linkedCallHook
    split
    · split
      · rename_i hReal
        exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_trans
          (s1 := u_sent.setPC c2EdNegAddr)
          (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl)
          (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.steps_traceDeltaNoAllocFailed
            LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.execSyscall_noAllocFailed
            (fun pc _ he => nomatch (rfl : emptyStdProg.externAt? pc = none).symm.trans he)
            (Classical.choose_spec hReal.2.2.2).1.toSteps)
      · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
    · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  rcases hna with ⟨δ, hδ_eq, hδ_ok⟩
  exact ⟨δ, htr_eq.trans (hδ_eq.trans (congrArg (· ++ δ) htr_u)), hδ_ok⟩

private def NonBranchNoLr (inst : Instr) : Bool :=
  match inst with
  | .ldp _ _ rt1 rt2 (.Offset rn _) => (rt1 != .lr) && (rt2 != .lr) && (rn != .lr)
  | .stp _ rt1 rt2 (.Offset rn _) => (rt1 != .lr) && (rt2 != .lr) && (rn != .lr)
  | .ldr _ _ _ rt (.Offset rn _) => (rt != .lr) && (rn != .lr)
  | .str _ rt (.Offset rn _) => (rt != .lr) && (rn != .lr)
  | .str _ rt (.PreIndex rn _) => (rt != .lr) && (rn != .lr)
  | .ldrSimd _ _ (.UnscaledOffset rn _) => (rn != .lr)
  | .strSimd _ _ (.UnscaledOffset rn _) => (rn != .lr)
  | .ldpSimd _ _ _ (.Offset rn _) => (rn != .lr)
  | .stpSimd _ _ _ (.Offset rn _) => (rn != .lr)
  | .moveWide _ _ rd _ _ => (rd != .lr)
  | .logicalImm _ _ rd rn _ => (rd != .lr) && (rn != .lr)
  | .logicalShift _ _ rd rn rm _ _ => (rd != .lr) && (rn != .lr) && (rm != .lr)
  | .addSubShift _ _ rd rn rm _ _ => (rd != .lr) && (rn != .lr) && (rm != .lr)
  | .bitfield _ _ rd rn _ _ => (rd != .lr) && (rn != .lr)
  | .dataProc3 _ _ rd rn rm ra => (rd != .lr) && (rn != .lr) && (rm != .lr) && (ra != .lr)
  | _ => false

private theorem reg_bne_iff_ne {r1 r2 : Reg} : (r1 != r2) = true ↔ r1 ≠ r2 := by
  cases r1 <;> cases r2 <;> simp [bne, BEq.beq, instBEqReg.beq]

private theorem edNegBody56_noLr :
    ((edwardsPointNegInstrs.take 56).all NonBranchNoLr) = true := by decide

private theorem writeReg_comm_lr (a : State) (w : Width) {rd : Reg} (hrd : rd ≠ .lr)
    (v L : BitVec 64) :
    (a.writeReg64 .lr L).writeReg w rd v = (a.writeReg w rd v).writeReg64 .lr L := by
  cases w <;>
    simp only [State.writeReg_w32, State.writeReg_w64,
      State.writeReg64_comm_or_same a .lr rd, Ne.symm hrd, ↓reduceIte]

private theorem readReg64_lr_writeReg (a : State) (w : Width) {rd : Reg} (hrd : rd ≠ .lr)
    (v : BitVec 64) :
    (a.writeReg w rd v).readReg64 .lr = a.readReg64 .lr := by
  cases w <;>
    simp only [State.writeReg_w32, State.writeReg_w64] <;>
    exact State.readReg64_writeReg64_ne a rd .lr _ (Ne.symm hrd)

private theorem readReg32_writeReg64_lr (a : State) {r : Reg} (hr : r ≠ .lr) (L : BitVec 64) :
    (a.writeReg64 .lr L).readReg32 r = a.readReg32 r := by
  unfold State.readReg32
  rw [State.readReg64_writeReg64_ne a .lr r L hr]

private theorem readReg_writeReg64_lr (a : State) (w : Width) {r : Reg} (hr : r ≠ .lr) (L : BitVec 64) :
    (a.writeReg64 .lr L).readReg w r = a.readReg w r := by
  cases w
  · exact congrArg (BitVec.zeroExtend 64) (readReg32_writeReg64_lr a hr L)
  · exact State.readReg64_writeReg64_ne a .lr r L hr

private theorem fault_branch_lr (a : State) (L : BitVec 64) (msg : String) :
    (a.writeReg64 .lr L).setStatus (.Exception msg) =
      (a.setStatus (.Exception msg)).writeReg64 .lr L ∧
    (a.setStatus (.Exception msg)).readReg64 .lr = a.readReg64 .lr ∧
    ((a.setStatus (.Exception msg)).status = .Running →
      (a.setStatus (.Exception msg)).pc = a.pc + 4#64) :=
  ⟨by cases a; rfl, by cases a; rfl, fun h => by cases a; cases h⟩

private theorem ite_fault_lr (c : Bool) (a : State) (L : BitVec 64) (msg : String)
    {s1 s2 : State}
    (hs : s1 = s2.writeReg64 .lr L ∧ s2.readReg64 .lr = a.readReg64 .lr ∧
      (s2.status = .Running → s2.pc = a.pc + 4#64)) :
    (if c then (a.writeReg64 .lr L).setStatus (.Exception msg) else s1) =
      (if c then a.setStatus (.Exception msg) else s2).writeReg64 .lr L ∧
    (if c then a.setStatus (.Exception msg) else s2).readReg64 .lr = a.readReg64 .lr ∧
    ((if c then a.setStatus (.Exception msg) else s2).status = .Running →
      (if c then a.setStatus (.Exception msg) else s2).pc = a.pc + 4#64) := by
  cases c
  · simpa using hs
  · simpa using fault_branch_lr a L msg

private theorem checkAddrSPAligned_lr (a : State) (addr : AddrMode) (L : BitVec 64) :
    checkAddrSPAligned (a.writeReg64 .lr L) addr = checkAddrSPAligned a addr := by
  cases addr <;> cases a <;> rfl

private theorem advancePC_writeReg64_lr (s : State) (L : BitVec 64) :
    (s.writeReg64 .lr L).advancePC = s.advancePC.writeReg64 .lr L := by
  cases s; rfl

private theorem setMem_writeReg64_lr (s : State) (m : Memory) (L : BitVec 64) :
    (s.writeReg64 .lr L).setMem m = (s.setMem m).writeReg64 .lr L := by
  cases s; rfl

private theorem setPState_writeReg64_lr (s : State) (ps : PState) (L : BitVec 64) :
    (s.writeReg64 .lr L).setPState ps = (s.setPState ps).writeReg64 .lr L := by
  cases s; rfl

private theorem writeVReg128_writeReg64_lr (s : State) (vt : BitVec 5) (v : BitVec 128) (L : BitVec 64) :
    (s.writeReg64 .lr L).writeVReg128 vt v = (s.writeVReg128 vt v).writeReg64 .lr L := by
  cases s; rfl

private theorem advancePC_pc_writeReg (a : State) (w : Width) (rd : Reg) (v : BitVec 64) :
    ((a.writeReg w rd v).advancePC).pc = a.pc + 4#64 := by
  cases a; cases w <;> cases rd <;> simp [State.writeReg, State.writeReg64, State.advancePC]

private theorem advancePC_pc_writeReg_setPState (a : State) (w : Width) (rd : Reg) (v : BitVec 64) (ps : PState) :
    (((a.writeReg w rd v).setPState ps).advancePC).pc = a.pc + 4#64 := by
  cases a; cases w <;> cases rd <;>
    simp [State.writeReg, State.writeReg64, State.setPState, State.advancePC]

private theorem advancePC_pc_writeReg2 (a : State) (w : Width) (r1 r2 : Reg) (v1 v2 : BitVec 64) :
    (((a.writeReg w r1 v1).writeReg w r2 v2).advancePC).pc = a.pc + 4#64 := by
  have h1 : (a.writeReg w r1 v1).pc = a.pc := by
    cases a; cases w <;> cases r1 <;> simp [State.writeReg, State.writeReg64]
  exact (advancePC_pc_writeReg (a.writeReg w r1 v1) w r2 v2).trans (congrArg (· + 4#64) h1)

private theorem evalInst_nonBranchNoLr_writeReg64_lr (P : Program) {inst : Instr}
    (hnb : NonBranchNoLr inst = true) (a : State) (L : BitVec 64) :
    P.evalInst inst (a.writeReg64 .lr L) = (P.evalInst inst a).writeReg64 .lr L ∧
      (P.evalInst inst a).readReg64 .lr = a.readReg64 .lr ∧
      ((P.evalInst inst a).status = .Running → (P.evalInst inst a).pc = a.pc + 4#64) := by
  have hmem : (a.writeReg64 .lr L).mem = a.mem := by cases a; rfl
  have hps : (a.writeReg64 .lr L).pstate = a.pstate := by cases a; rfl
  have hvr : ∀ vt, (a.writeReg64 .lr L).readVReg128 vt = a.readVReg128 vt := fun _ => by cases a; rfl
  have hadv_lr : ∀ s : State, s.advancePC.readReg64 .lr = s.readReg64 .lr := fun s => by cases s; rfl
  have hsm_lr : ∀ (s : State) m, (s.setMem m).readReg64 .lr = s.readReg64 .lr := fun s _ => by cases s; rfl
  have hsp_lr : ∀ (s : State) ps, (s.setPState ps).readReg64 .lr = s.readReg64 .lr := fun s _ => by cases s; rfl
  have hvw_lr : ∀ (s : State) vt v, (s.writeVReg128 vt v).readReg64 .lr = s.readReg64 .lr := fun s _ _ => by cases s; rfl
  cases inst with
  | ldp w sg rt1 rt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨⟨hrt1, hrt2⟩, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execLdp, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hrn]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeReg_comm_lr _ _ hrt1, writeReg_comm_lr _ _ hrt2, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((readReg64_lr_writeReg _ _ hrt2 _).trans (readReg64_lr_writeReg _ _ hrt1 _)),
        fun _ => advancePC_pc_writeReg2 a _ rt1 rt2 _ _⟩
    | _ => simp [NonBranchNoLr] at hnb
  | stp w rt1 rt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨⟨hrt1, hrt2⟩, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execStp, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem,
          State.readReg64_writeReg64_ne a .lr rn L hrn,
          State.readReg64_writeReg64_ne a .lr rt1 L hrt1,
          State.readReg64_writeReg64_ne a .lr rt2 L hrt2]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | ldr w sz sg rt addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨hrt, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execLdr, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hrn]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeReg_comm_lr _ _ hrt, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrt _),
        fun _ => advancePC_pc_writeReg a w rt _⟩
    | _ => simp [NonBranchNoLr] at hnb
  | str sz rt addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨hrt, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execStr, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem,
          State.readReg64_writeReg64_ne a .lr rn L hrn,
          State.readReg64_writeReg64_ne a .lr rt L hrt]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | PreIndex rn off =>
      simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
      rcases hnb with ⟨hrt, hrn⟩
      dsimp only [Program.evalInst, execInstWithSvc, execStr, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem,
          State.readReg64_writeReg64_ne a .lr rn L hrn,
          State.readReg64_writeReg64_ne a .lr rt L hrt]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      have hcomm_rn :
          ((a.setMem (a.mem.writeSized sz (a.readReg64 rn + off) (a.readReg64 rt))).writeReg64 .lr L).writeReg64
              rn (a.readReg64 rn + off) =
            ((a.setMem (a.mem.writeSized sz (a.readReg64 rn + off) (a.readReg64 rt))).writeReg64
              rn (a.readReg64 rn + off)).writeReg64 .lr L := by
        simp only [State.writeReg64_comm_or_same _ .lr rn, Ne.symm hrn, ↓reduceIte]
      rw [setMem_writeReg64_lr, hcomm_rn, advancePC_writeReg64_lr]
      exact ⟨rfl,
        (hadv_lr _).trans ((State.readReg64_writeReg64_ne _ rn .lr _ (Ne.symm hrn)).trans (hsm_lr _ _)),
        fun _ => by
          have hsm_pc : (a.setMem (a.mem.writeSized sz (a.readReg64 rn + off) (a.readReg64 rt))).pc = a.pc := by
            cases a; rfl
          exact (advancePC_pc_writeReg _ .W64 rn _).trans (congrArg (· + 4#64) hsm_pc)⟩
    | _ => simp [NonBranchNoLr] at hnb
  | ldrSimd sz vt addr =>
    cases addr with
    | UnscaledOffset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeVReg128_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hvw_lr _ _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | strSimd sz vt addr =>
    cases addr with
    | UnscaledOffset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb, hvr vt]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | ldpSimd sz vt1 vt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [writeVReg128_writeReg64_lr, writeVReg128_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hvw_lr _ _ _).trans (hvw_lr _ _ _)), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | stpSimd sz vt1 vt2 addr =>
    cases addr with
    | Offset rn off =>
      simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
      dsimp only [Program.evalInst, execInstWithSvc, evalAddrMode]
      rw [checkAddrSPAligned_lr, hmem, State.readReg64_writeReg64_ne a .lr rn L hnb, hvr vt1, hvr vt2]
      refine ite_fault_lr _ a L _ (ite_fault_lr _ a L _ ?_)
      rw [setMem_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (hsm_lr _ _), fun _ => by cases a; rfl⟩
    | _ => simp [NonBranchNoLr] at hnb
  | moveWide w op rd imm hw =>
    simp only [NonBranchNoLr, reg_bne_iff_ne] at hnb
    dsimp only [Program.evalInst, execInstWithSvc, execMoveWide]
    cases op
    · dsimp only
      rw [writeReg_comm_lr _ _ hnb, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hnb _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    · dsimp only
      rw [writeReg_comm_lr _ _ hnb, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hnb _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    · dsimp only
      rw [readReg_writeReg64_lr a w hnb L, writeReg_comm_lr _ _ hnb, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hnb _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
  | logicalImm w op rd rn imm =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨hrd, hrn⟩
    dsimp only [Program.evalInst, execInstWithSvc, execLogicalImm]
    rw [readReg_writeReg64_lr a w hrn L, hps]
    cases (evalLogical w op (a.readReg w rn) imm a.pstate).2 with
    | none =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    | some ps =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, setPState_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hsp_lr _ _).trans (readReg64_lr_writeReg _ _ hrd _)),
        fun _ => advancePC_pc_writeReg_setPState a w rd _ ps⟩
  | addSubShift w op rd rn rm sh amt =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨⟨hrd, hrn⟩, hrm⟩
    dsimp only [Program.evalInst, execInstWithSvc, execAddSubShift]
    rw [readReg_writeReg64_lr a w hrn L, readReg_writeReg64_lr a w hrm L]
    cases (evalAddSub w op (a.readReg w rn) (shiftVal w (a.readReg w rm) sh amt) none).2 with
    | none =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    | some ps =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, setPState_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hsp_lr _ _).trans (readReg64_lr_writeReg _ _ hrd _)),
        fun _ => advancePC_pc_writeReg_setPState a w rd _ ps⟩
  | bitfield w op rd rn immr imms =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨hrd, hrn⟩
    dsimp only [Program.evalInst, execInstWithSvc, execBitfield]
    rw [readReg_writeReg64_lr a w hrd L, readReg_writeReg64_lr a w hrn L,
        writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
    exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
      fun _ => advancePC_pc_writeReg a w rd _⟩
  | logicalShift w op rd rn rm sh amt =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨⟨hrd, hrn⟩, hrm⟩
    dsimp only [Program.evalInst, execInstWithSvc, execLogicalShift]
    rw [readReg_writeReg64_lr a w hrn L, readReg_writeReg64_lr a w hrm L, hps]
    cases (evalLogical w op (a.readReg w rn) (shiftVal w (a.readReg w rm) sh amt) a.pstate).2 with
    | none =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a w rd _⟩
    | some ps =>
      dsimp only
      rw [writeReg_comm_lr _ _ hrd, setPState_writeReg64_lr, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans ((hsp_lr _ _).trans (readReg64_lr_writeReg _ _ hrd _)),
        fun _ => advancePC_pc_writeReg_setPState a w rd _ ps⟩
  | dataProc3 w op rd rn rm ra =>
    simp only [NonBranchNoLr, Bool.and_eq_true, reg_bne_iff_ne] at hnb
    rcases hnb with ⟨⟨⟨hrd, hrn⟩, hrm⟩, hra⟩
    dsimp only [Program.evalInst, execInstWithSvc, execDataProc3]
    cases op <;> cases w <;> dsimp only <;>
      repeat first
        | rw [State.readReg64_writeReg64_ne a .lr rn L hrn]
        | rw [State.readReg64_writeReg64_ne a .lr rm L hrm]
        | rw [State.readReg64_writeReg64_ne a .lr ra L hra]
        | rw [readReg32_writeReg64_lr a hrn L]
        | rw [readReg32_writeReg64_lr a hrm L]
        | rw [readReg32_writeReg64_lr a hra L]
    all_goals
      rw [writeReg_comm_lr _ _ hrd, advancePC_writeReg64_lr]
      exact ⟨rfl, (hadv_lr _).trans (readReg64_lr_writeReg _ _ hrd _),
        fun _ => advancePC_pc_writeReg a _ rd _⟩
  | _ => simp [NonBranchNoLr] at hnb

private theorem steps_not_running_eq {P : Program} {s sf : State}
    (hs : s.status ≠ .Running) (h : Steps P s sf) : sf = s := by
  cases h with
  | refl _ => rfl
  | step h1 _ => exact absurd h1.status_running hs

private theorem steps_edNegSentinel_of_visitedIn
    {P_real : Program} {entry lr0 : BitVec 64}
    (hsvc : P_real.svc = emptyStdProg.svc)
    (hreal_no : ∀ pc, keepEdNeg entry pc = true → P_real.externAt? pc = none)
    {s_sent sf_sent : State}
    (hvis : h2fsgen_StepsVisitedIn (keepEdNeg entry) emptyStdProg s_sent sf_sent)
    (hrun_sf : sf_sent.status = .Running)
    (hk_sf : keepEdNeg entry sf_sent.pc = false) :
    ∀ a : State,
      s_sent = a.writeReg64 .lr (entry + 0xe4#64) →
      a.readReg64 .lr = lr0 →
      keepEdNeg entry a.pc = true →
      (pureWordsProg entry edwardsPointNegWords).CodeLoaded a.mem →
      Steps P_real a ((sf_sent.writeReg64 .lr lr0).setPC lr0) := by
  induction hvis with
  | refl s =>
    intro a hs _ hka _
    have hpc : s.pc = a.pc := by subst hs; cases a; rfl
    rw [hpc, hka] at hk_sf
    cases hk_sf
  | @step s1 s2 sf hd h1 h2 ih =>
    intro a hs1 hlr_a hka hCode
    let L := entry + 0xe4#64
    let P_ed := pureWordsProg entry edwardsPointNegWords
    have hpc1 : s1.pc = a.pc := by subst hs1; cases a; rfl
    have hmem1 : s1.mem = a.mem := by subst hs1; cases a; rfl
    have hrun_a : a.status = .Running := by
      have hr := h1.status_running; subst hs1; cases a; exact hr
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := steps_not_running_eq (fun h => ExecStatus.noConfusion h) h2.toSteps
      rw [heq] at hrun_sf; cases hrun_sf
    | extern _ hext _ _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | extern_fault _ hext _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | @exec inst hrun1 hfm1 =>
      rw [hpc1, hmem1] at hfm1
      have hmod4 : a.pc.toNat % 4 = 0 := by
        unfold Program.fetchMem at hfm1
        have hne : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [hne] at hfm1
        by_contra hnz
        simp [hnz] at hfm1
      have halign_e : entry.toNat % 4 = 0 := hCode.aligned
      have hlt228 : (a.pc - entry).toNat < 228 := by
        rw [keepEdNeg_iff, edNegByteLen_eq] at hka; exact hka
      have hnwrap : entry.toNat + 228 ≤ 2 ^ 64 := hCode.no_wrap
      have hd_mod4 : (a.pc - entry).toNat % 4 = 0 := by
        have hsub_nat : (a.pc - entry).toNat = a.pc.toNat - entry.toNat := by bv_omega
        have hle_e : entry.toNat ≤ a.pc.toNat := by bv_omega
        rw [hsub_nat]; omega
      let k := (a.pc - entry).toNat / 4
      have hk57 : k < 57 := by change (a.pc - entry).toNat / 4 < 57; omega
      have hk4 : 4 * k = (a.pc - entry).toNat := by change 4 * ((a.pc - entry).toNat / 4) = _; omega
      have hpc_off : a.pc = entry + BitVec.ofNat 64 (4 * k) := by
        rw [hk4]; bv_omega
      have hins : hasInstrs P_ed entry edwardsPointNegInstrs := pureWordsProg_hasInstrs_edNeg entry
      have hlen_ins : edwardsPointNegInstrs.length = 57 := rfl
      have hf_ed : P_ed.fetch (entry + BitVec.ofNat 64 (4 * k)) = some (edwardsPointNegInstrs[k]'(hlen_ins ▸ hk57)) :=
        hins.fetch_off k (BitVec.ofNat 64 (4 * k)) (hlen_ins ▸ hk57) rfl
      have hfm_ed : P_ed.fetchMem a.mem a.pc = some (edwardsPointNegInstrs[k]'(hlen_ins ▸ hk57)) := by
        rw [hpc_off]; exact Program.fetchMem_of_fetch hCode hf_ed
      have hfm_eq_empty : P_ed.fetchMem a.mem a.pc = emptyStdProg.fetchMem a.mem a.pc := by
        unfold Program.fetchMem
        have h1 : (P_ed.externAt? a.pc).isSome = false := by
          rw [pureWordsProg_externAt_none]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1, h2']
      have hinst_eq : inst = edwardsPointNegInstrs[k]'(hlen_ins ▸ hk57) :=
        Option.some.inj ((hfm1.symm.trans hfm_eq_empty.symm).trans hfm_ed)
      have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
        unfold Program.fetchMem
        have h1 : (P_real.externAt? a.pc).isSome = false := by
          rw [hreal_no a.pc hka]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1]
        simpa [Program.fetchMem, h2'] using hfm1
      have heval_svc : emptyStdProg.evalInst inst = P_real.evalInst inst := by
        funext st; unfold Program.evalInst; rw [hsvc]
      by_cases hk56 : k < 56
      · have hmem_take : inst ∈ edwardsPointNegInstrs.take 56 := by
          rw [hinst_eq, List.mem_iff_getElem]
          refine ⟨k, by simp [hlen_ins]; exact hk56, List.getElem_take⟩
        have hnb : NonBranchNoLr inst = true := List.all_eq_true.mp edNegBody56_noLr inst hmem_take
        obtain ⟨hcomm, hlr_next, hpc_next⟩ := evalInst_nonBranchNoLr_writeReg64_lr P_real hnb a L
        let a' := P_real.evalInst inst a
        have hs2_eq : emptyStdProg.evalInst inst s1 = a'.writeReg64 .lr L := by
          rw [heval_svc, hs1]; exact hcomm
        have hrun_s2 : (emptyStdProg.evalInst inst s1).status = .Running := by
          by_contra hnr
          have heq := steps_not_running_eq hnr h2.toSteps
          exact hnr (heq ▸ hrun_sf)
        have hrun_a' : a'.status = .Running := by
          rw [hs2_eq] at hrun_s2
          have hw_st : (a'.writeReg64 .lr L).status = a'.status := by
            generalize a' = st; cases st; rfl
          exact hw_st ▸ hrun_s2
        have hka' : keepEdNeg entry a'.pc = true := by
          rw [hpc_next hrun_a', hpc_off, keepEdNeg_iff, edNegByteLen_eq]
          have hsub : (entry + BitVec.ofNat 64 (4 * k) + 4#64) - entry =
              BitVec.ofNat 64 (4 * k + 4) := by bv_omega
          rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hstep_real : Step P_real a a' := Step.exec hrun_a hfm_real
        have hCode' : P_ed.CodeLoaded a'.mem := hCode.of_keepsFrozen hstep_real.keepsFrozen
        exact Steps.step hstep_real
          (ih hrun_sf hk_sf a' hs2_eq (hlr_next.trans hlr_a) hka' hCode')
      · have hk_eq56 : k = 56 := by omega
        have hinst_ret : inst = .ret .lr := by
          have h56 : edwardsPointNegInstrs[56]'(by decide) = .ret .lr := by decide
          exact Eq.trans (by simpa only [hk_eq56] using hinst_eq) h56
        subst hinst_ret
        have hs2_pc : (emptyStdProg.evalInst (.ret .lr) s1).pc = L := by
          subst hs1
          dsimp only [Program.evalInst, execInstWithSvc]
          have hlr_L : (a.writeReg64 .lr L).readReg64 .lr = L := by cases a; rfl
          rw [hlr_L]; cases a; rfl
        have hk_L : keepEdNeg entry L = false := by
          rw [Bool.eq_false_iff, Ne, keepEdNeg_iff, edNegByteLen_eq]
          have hsub : L - entry = 0xe4#64 := by dsimp [L]; bv_omega
          rw [hsub]; decide
        cases h2 with
        | step hd2 _ _ =>
          rw [hs2_pc, hk_L] at hd2; cases hd2
        | refl _ =>
          have hstep_ret : Step P_real a (P_real.evalInst (.ret .lr) a) := Step.exec hrun_a hfm_real
          have htarget_eq :
              (((emptyStdProg.evalInst (.ret .lr) s1).writeReg64 .lr lr0).setPC lr0) =
                P_real.evalInst (.ret .lr) a := by
            subst hs1
            dsimp only [Program.evalInst, execInstWithSvc]
            rw [hlr_a]
            rcases a with ⟨⟨rf⟩, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
            dsimp [State.readReg64, RegFile.read, State.writeReg64, State.setPC, RegFile.write] at hlr_a ⊢
            congr 2; funext i; by_cases hi : i = 30#5 <;> simp [hi, hlr_a]
          rw [htarget_eq]
          exact Steps.step hstep_ret (Steps.refl _)

private theorem keepEdNeg_c2_sub_keepLib2Text {pc : BitVec 64}
    (hk : keepEdNeg c2EdNegAddr pc = true) :
    keepLib2Text pc = true :=
  c2_keepLib2Text_of_sub_lt (by rwa [keepEdNeg_iff] at hk) (by decide) (by decide)

theorem keepEdNeg_c2_noPanic {pc : BitVec 64}
    (hk : keepEdNeg c2EdNegAddr pc = true) :
    isLinkedPanicAddr pc = false :=
  c2_noPanic_of_band_sub_lt (by rwa [keepEdNeg_iff] at hk) (by decide) (by decide)

theorem c2_edNegGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsEdNegSym (c2GuardOf lsmpl lsEdNegSym)
      (edNegSentinelGhost c2EdNegAddr) := by
  refine ⟨c2_edNegGhost_rowSpecOk, ?_⟩
  refine
    { preserves_execFrozen := fun u hrun hnoex hfr =>
        ⟨edNegSentinelGhost_preserves_execFrozen hrun hnoex hfr,
         edNegSentinelGhost_fs c2EdNegAddr u⟩
      replay_at_stub := ?_ }
  dsimp only
  intro W s0 sf _ _ _ _
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_edNeg_eq hLs
  have hk0 : keepEdNeg c2EdNegAddr c2EdNegAddr = true := by
    rw [keepEdNeg_iff, BitVec.sub_self]; decide
  refine Or.inr ⟨hRes ▸ hExt.realRxNoExtern mmpl W
    (keepLib2Text_sub_rxProg (keepEdNeg_c2_sub_keepLib2Text hk0))
    (keepEdNeg_c2_noPanic hk0), ?_⟩
  intro u _ _ hpc hrun hnoex hkf hfr hinv
  have hpc' : u.pc = c2EdNegAddr := hpc.trans hRes
  let lr0 := u.readReg64 .lr
  let L := c2EdNegAddr + 0xe4#64
  let u_sent := u.writeReg64 .lr L
  have hnoex_sent : ∀ msg, (narrowEdNegGhostHook c2EdNegAddr u_sent).status ≠ .Exception msg := by
    intro msg hex
    apply hnoex msg
    dsimp only [edNegSentinelGhost, L, u_sent]
    have hbe : (ExecStatus.Exception msg == .Running) = false := rfl
    rw [hex, hbe]; exact hex
  have hrun_sent : u_sent.status = .Running := by cases u; exact hrun
  have hmem_sent : u_sent.mem = u.mem := by cases u; rfl
  have hCode : (pureWordsProg c2EdNegAddr edwardsPointNegWords).CodeLoaded u.mem :=
    codeLoaded_of_pureSubsliceR hinv.1.rxCode c2EdNegSlice_ok
  have hk_L : keepEdNeg c2EdNegAddr (u_sent.readReg64 .lr) = false := by
    have hlr_L : u_sent.readReg64 .lr = L := by cases u; rfl
    rw [hlr_L]; decide
  obtain ⟨hvis, _, _⟩ := narrowEdNegGhostHook_visitedIn
    (hmem_sent ▸ hCode)
    (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel))
    hrun_sent hnoex_sent (hmem_sent ▸ hfr) hk_L
  have hnoex_eq : ∀ msg, (f3EmptyEdNegGhostHook (keepEdNeg c2EdNegAddr)
      (pureWordsProg c2EdNegAddr edwardsPointNegWords) c2EdNegAddr u_sent).status ≠ .Exception msg :=
    hnoex_sent
  rw [f3EmptyEdNegGhostHook_eq] at hnoex_eq
  obtain ⟨_, hsp_sent, x, R, hpre⟩ := linkedCallHook_activeRealPre_of_noException hnoex_eq
  obtain ⟨_, _, hout⟩ := narrowEdNegGhostHook_master_ok c2EdNegAddr x R u_sent hrun_sent hpre hsp_sent
  have hret_sf : (narrowEdNegGhostHook c2EdNegAddr u_sent).status = .Running ∧
      (narrowEdNegGhostHook c2EdNegAddr u_sent).pc = L := by
    rcases hout with ⟨hr, _, _⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · exact ⟨hr.2.2, hr.1.trans (by cases u; rfl)⟩
    · dsimp only [masterEdNegSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
    · dsimp only [masterEdNegSpec] at he; rw [satisfies_pure_sepConj] at he; exact False.elim he.1
    · dsimp only [masterEdNegSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1
  have hbe : (ExecStatus.Running == .Running) = true := rfl
  have hghost_eq : edNegSentinelGhost c2EdNegAddr u =
      ((narrowEdNegGhostHook c2EdNegAddr u_sent).writeReg64 .lr lr0).setPC lr0 := by
    dsimp only [edNegSentinelGhost, lr0, L, u_sent]
    rw [hret_sf.1, hbe]; rfl
  have hu_sent_pc : u_sent.setPC c2EdNegAddr = u.writeReg64 .lr L := by
    dsimp [u_sent]; cases u; dsimp only [State.writeReg64, State.setPC] at hpc' ⊢; subst hpc'; rfl
  have hk_sf : keepEdNeg c2EdNegAddr (narrowEdNegGhostHook c2EdNegAddr u_sent).pc = false := by
    rw [hret_sf.2]; decide
  have hst := steps_edNegSentinel_of_visitedIn
    (P_real := cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
    rfl
    (fun pc hkp => hExt.realRxNoExtern mmpl W
      (keepLib2Text_sub_rxProg (keepEdNeg_c2_sub_keepLib2Text hkp))
      (keepEdNeg_c2_noPanic hkp))
    hvis hret_sf.1 hk_sf u hu_sent_pc rfl (hpc' ▸ hk0) hCode
  rw [← hghost_eq] at hst
  exact ⟨hst, edNegSentinelGhost_preserves_execFrozen hrun hnoex hfr,
    f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs u (edNegSentinelGhost c2EdNegAddr u)
      hinv hkf (edNegSentinelGhost_fs c2EdNegAddr u)⟩

/-! ## 5. Sentinel-`lr` `SharedSecret::drop` (`lsSharedSecretDropSym`) Two-Block Ghost & Replay -/

private theorem resolve_sharedSecretDrop_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

@[expose] noncomputable def c2ZeroizeSentinelGhost (entry : BitVec 64) (u : State) : State :=
  let lr0 := u.readReg64 .lr
  let u_sent := u.writeReg64 .lr (entry + 0xfc#64)
  let sf_sent := f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
    (pureWordsProg entry zeroize32Words) entry u_sent
  if sf_sent.status == .Running then
    (sf_sent.writeReg64 .lr lr0).setPC lr0
  else
    sf_sent

noncomputable abbrev c2SharedSecretDropSentinelGhost : State → State :=
  c2ZeroizeSentinelGhost c2Zeroize32Addr

private theorem zeroize32_sub_proc (entry : BitVec 64) :
    subroutine_ok (pureWordsProg entry zeroize32Words) entry processZeroizeSpec :=
  subroutine_ok_processZeroize_of_hasWords
    (pureWordsProg_externAt_none entry zeroize32Words)
    (pureWordsProg_zeroize32_hasWords entry)

theorem c2ZeroizeSentinelGhost_fs (entry : BitVec 64) (u : State) :
    (c2ZeroizeSentinelGhost entry u).fs = u.fs := by
  dsimp only [c2ZeroizeSentinelGhost]
  have hfs := f3EmptyZeroizeGhostHook_fs (keepStaticSecretDrop entry)
    (pureWordsProg entry zeroize32Words) entry (u.writeReg64 .lr (entry + 0xfc#64))
  have hfs_w : (u.writeReg64 .lr (entry + 0xfc#64)).fs = u.fs := by cases u; rfl
  split
  · generalize f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
      (pureWordsProg entry zeroize32Words) entry (u.writeReg64 .lr (entry + 0xfc#64)) = sf at hfs ⊢
    cases sf; exact hfs.trans hfs_w
  · exact hfs.trans hfs_w

theorem c2ZeroizeSentinelGhost_trace (entry : BitVec 64) (u : State) :
    (c2ZeroizeSentinelGhost entry u).trace = u.trace := by
  dsimp only [c2ZeroizeSentinelGhost]
  have htr := f3EmptyZeroizeGhostHook_trace_of_process rfl
    (pureWordsProg_externAt_none entry zeroize32Words) (zeroize32_sub_proc entry)
    (keep := keepStaticSecretDrop entry) (u.writeReg64 .lr (entry + 0xfc#64))
  have htr_w : (u.writeReg64 .lr (entry + 0xfc#64)).trace = u.trace := by cases u; rfl
  split
  · generalize f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
      (pureWordsProg entry zeroize32Words) entry (u.writeReg64 .lr (entry + 0xfc#64)) = sf at htr ⊢
    cases sf; exact htr.trans htr_w
  · exact htr.trans htr_w

theorem c2ZeroizeSentinelGhost_fsT (entry : BitVec 64) :
    HookFsTraced IsFsC (c2ZeroizeSentinelGhost entry) :=
  fun u => FsTraced.of_eq (c2ZeroizeSentinelGhost_trace entry u)
    (congrArg (·.files) (c2ZeroizeSentinelGhost_fs entry u))

theorem c2ZeroizeSentinelGhost_vmPreserved (entry : BitVec 64) (u : State) :
    VmPreserved u (c2ZeroizeSentinelGhost entry u) := by
  have hvm := f3EmptyZeroizeGhostHook_vmPreserved_of_process rfl
    (pureWordsProg_externAt_none entry zeroize32Words) (zeroize32_sub_proc entry)
    (keep := keepStaticSecretDrop entry) (u.writeReg64 .lr (entry + 0xfc#64))
  dsimp only [c2ZeroizeSentinelGhost]
  split
  · generalize f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
      (pureWordsProg entry zeroize32Words) entry (u.writeReg64 .lr (entry + 0xfc#64)) = sf at hvm ⊢
    rcases u with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    rcases sf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    exact hvm
  · generalize f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
      (pureWordsProg entry zeroize32Words) entry (u.writeReg64 .lr (entry + 0xfc#64)) = sf at hvm ⊢
    rcases u with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    exact hvm

theorem c2ZeroizeSentinelGhost_preserves_execFrozen {entry : BitVec 64} {u : State}
    (_hrun : u.status = .Running)
    (_hnoex : ∀ msg, (c2ZeroizeSentinelGhost entry u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem) :
    ExecFrozen (c2ZeroizeSentinelGhost entry u).mem := by
  have hfr_sent : ExecFrozen (u.writeReg64 .lr (entry + 0xfc#64)).mem := by
    have hm : (u.writeReg64 .lr (entry + 0xfc#64)).mem = u.mem := by cases u; rfl
    rwa [hm]
  have hef := f3EmptyZeroizeGhostHook_preserves_execFrozen (keepStaticSecretDrop entry)
    (pureWordsProg entry zeroize32Words) entry
    (s0 := u.writeReg64 .lr (entry + 0xfc#64)) hfr_sent
  dsimp only [c2ZeroizeSentinelGhost]
  split
  · generalize f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
      (pureWordsProg entry zeroize32Words) entry (u.writeReg64 .lr (entry + 0xfc#64)) = sf at hef ⊢
    have hm : ((sf.writeReg64 .lr (u.readReg64 .lr)).setPC (u.readReg64 .lr)).mem = sf.mem := by
      cases sf; rfl
    rwa [hm]
  · exact hef

theorem c2ZeroizeSentinelGhost_master_ok (entry : BitVec 64) :
    HookOk (c2ZeroizeSentinelGhost entry) masterZeroizeSpec := by
  intro a R u hrun hpre hsp_u
  let lr0 := u.readReg64 .lr
  let u_sent := u.writeReg64 .lr (entry + 0xfc#64)
  have hrun_sent : u_sent.status = .Running := by cases u; exact hrun
  have hsp_sent : u_sent.spAligned = true := by cases u; exact hsp_u
  have hmem_sent : u_sent.mem = u.mem := by cases u; rfl
  have hpre_sent : u_sent.mem ⊨ masterZeroizeSpec.pre a u_sent ∗ R := by
    rw [hmem_sent]
    have hx0 : u_sent.readReg64 .x0 = u.readReg64 .x0 :=
      State.readReg64_writeReg64_ne u .lr .x0 _ (by decide)
    dsimp only [masterZeroizeSpec] at hpre ⊢
    rwa [hx0]
  obtain ⟨hkf_s, hsym_s, hout⟩ := f3EmptyZeroizeGhostHook_master_ok_of_process rfl
    (pureWordsProg_externAt_none entry zeroize32Words) (zeroize32_sub_proc entry)
    (keep := keepStaticSecretDrop entry) a R u_sent hrun_sent hpre_sent hsp_sent
  rcases hout with ⟨hret_s, hcc_s, hpost_s⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hrun_sf : (f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
        (pureWordsProg entry zeroize32Words) entry u_sent).status = .Running := hret_s.2.2
    have hbe : (ExecStatus.Running == .Running) = true := rfl
    have hghost_eq : c2ZeroizeSentinelGhost entry u =
        ((f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
          (pureWordsProg entry zeroize32Words) entry u_sent).writeReg64 .lr lr0).setPC lr0 := by
      dsimp only [c2ZeroizeSentinelGhost, lr0, u_sent]
      rw [hrun_sf, hbe]; rfl
    rw [hghost_eq]
    generalize f3EmptyZeroizeGhostHook (keepStaticSecretDrop entry)
      (pureWordsProg entry zeroize32Words) entry u_sent = sf_s at hkf_s hsym_s hret_s hcc_s hpost_s
    let sf := (sf_s.writeReg64 .lr lr0).setPC lr0
    have hkf_out : u.mem.KeepsFrozen sf.mem := by
      have hm1 : sf.mem = sf_s.mem := by cases sf_s; rfl
      rw [hm1, ← hmem_sent]; exact hkf_s
    have hsym_out : sf.symtab = u.symtab := by
      have hs1 : sf.symtab = sf_s.symtab := by cases sf_s; rfl
      have hs2 : u_sent.symtab = u.symtab := by cases u; rfl
      exact hs1.trans (hsym_s.trans hs2)
    refine ⟨hkf_out, hsym_out, Or.inl ⟨sentinel_returned hret_s, sentinel_ccPreserved hcc_s, ?_⟩⟩
    have hmem_sf : sf.mem = sf_s.mem := by cases sf_s; rfl
    rw [hmem_sf]
    dsimp only [masterZeroizeSpec] at hpost_s ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_s ⊢
    exact ⟨sentinel_statePreserved hpost_s.1, hpost_s.2⟩
  · dsimp only [masterZeroizeSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [masterZeroizeSpec] at he; rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [masterZeroizeSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem extraRowSpec_sharedSecretDrop [LibsignalPlacement] (f : State → State) :
    ExtraRowSpec lsSharedSecretDropSym f = SharedSecretDropRowSpec f := by
  unfold ExtraRowSpec; simp (config := { decide := true })

theorem c2_sharedSecretDropGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsSharedSecretDropSym c2SharedSecretDropSentinelGhost where
  fs_eq := c2ZeroizeSentinelGhost_fs c2Zeroize32Addr
  fsT := c2ZeroizeSentinelGhost_fsT c2Zeroize32Addr
  rowSpec := (extraRowSpec_sharedSecretDrop _).symm ▸
    SharedSecretDropRowSpec.of_vm
      (hookOk_zeroizeSecret_of_master (c2ZeroizeSentinelGhost_master_ok c2Zeroize32Addr))
      (c2ZeroizeSentinelGhost_vmPreserved c2Zeroize32Addr)

theorem c2_sharedSecretDropGhost_noAllocFailed :
    HookNoAllocFailed c2SharedSecretDropSentinelGhost :=
  hookNoAllocFailed_of_trace_eq _ (c2ZeroizeSentinelGhost_trace c2Zeroize32Addr)

private theorem zeroizeBody62_noLr :
    ((zeroize32Instrs.take 62).all NonBranchNoLr) = true := by decide

private theorem steps_zeroizeSentinel_of_visitedIn
    {P_real : Program} {entry lr0 : BitVec 64}
    (hsvc : P_real.svc = emptyStdProg.svc)
    (hreal_no : ∀ pc, keepStaticSecretDrop entry pc = true → P_real.externAt? pc = none)
    {s_sent sf_sent : State}
    (hvis : h2fsgen_StepsVisitedIn (keepStaticSecretDrop entry) emptyStdProg s_sent sf_sent)
    (hrun_sf : sf_sent.status = .Running)
    (hk_sf : keepStaticSecretDrop entry sf_sent.pc = false) :
    ∀ a : State,
      s_sent = a.writeReg64 .lr (entry + 0xfc#64) →
      a.readReg64 .lr = lr0 →
      keepStaticSecretDrop entry a.pc = true →
      (pureWordsProg entry zeroize32Words).CodeLoaded a.mem →
      Steps P_real a ((sf_sent.writeReg64 .lr lr0).setPC lr0) := by
  induction hvis with
  | refl s =>
    intro a hs _ hka _
    have hpc : s.pc = a.pc := by subst hs; cases a; rfl
    rw [hpc, hka] at hk_sf
    cases hk_sf
  | @step s1 s2 sf hd h1 h2 ih =>
    intro a hs1 hlr_a hka hCode
    let L := entry + 0xfc#64
    let P_z := pureWordsProg entry zeroize32Words
    have hpc1 : s1.pc = a.pc := by subst hs1; cases a; rfl
    have hmem1 : s1.mem = a.mem := by subst hs1; cases a; rfl
    have hrun_a : a.status = .Running := by
      have hr := h1.status_running; subst hs1; cases a; exact hr
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := steps_not_running_eq (fun h => ExecStatus.noConfusion h) h2.toSteps
      rw [heq] at hrun_sf; cases hrun_sf
    | extern _ hext _ _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | extern_fault _ hext _ => cases (rfl : emptyStdProg.externAt? s1.pc = none).symm.trans hext
    | @exec inst hrun1 hfm1 =>
      rw [hpc1, hmem1] at hfm1
      have hmod4 : a.pc.toNat % 4 = 0 := by
        unfold Program.fetchMem at hfm1
        have hne : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [hne] at hfm1
        by_contra hnz
        simp [hnz] at hfm1
      have halign_e : entry.toNat % 4 = 0 := hCode.aligned
      have hlt252 : (a.pc - entry).toNat < 252 := by
        rw [keepStaticSecretDrop_iff] at hka
        exact hka
      have hnwrap : entry.toNat + 252 ≤ 2 ^ 64 := by
        have hnw := hCode.no_wrap
        have hbase : P_z.base = entry := rfl
        have hcode : P_z.code = (pureWordsProg 0#64 zeroize32Words).code := rfl
        have hlen0 : (pureWordsProg 0#64 zeroize32Words).code.length = 252 := by decide +kernel
        rwa [hbase, hcode, hlen0] at hnw
      have hd_mod4 : (a.pc - entry).toNat % 4 = 0 := by
        have hsub_nat : (a.pc - entry).toNat = a.pc.toNat - entry.toNat := by bv_omega
        have hle_e : entry.toNat ≤ a.pc.toNat := by bv_omega
        rw [hsub_nat]; omega
      let k := (a.pc - entry).toNat / 4
      have hk63 : k < 63 := by change (a.pc - entry).toNat / 4 < 63; omega
      have hk4 : 4 * k = (a.pc - entry).toNat := by change 4 * ((a.pc - entry).toNat / 4) = _; omega
      have hpc_off : a.pc = entry + BitVec.ofNat 64 (4 * k) := by
        rw [hk4]; bv_omega
      have hins : hasInstrs P_z entry zeroize32Instrs :=
        LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop.hasInstrs_of_hasWords
          (pureWordsProg_zeroize32_hasWords entry)
      have hlen_ins : zeroize32Instrs.length = 63 := rfl
      have hf_z : P_z.fetch (entry + BitVec.ofNat 64 (4 * k)) = some (zeroize32Instrs[k]'(hlen_ins ▸ hk63)) :=
        hins.fetch_off k (BitVec.ofNat 64 (4 * k)) (hlen_ins ▸ hk63) rfl
      have hfm_z : P_z.fetchMem a.mem a.pc = some (zeroize32Instrs[k]'(hlen_ins ▸ hk63)) := by
        rw [hpc_off]; exact Program.fetchMem_of_fetch hCode hf_z
      have hfm_eq_empty : P_z.fetchMem a.mem a.pc = emptyStdProg.fetchMem a.mem a.pc := by
        unfold Program.fetchMem
        have h1 : (P_z.externAt? a.pc).isSome = false := by
          rw [pureWordsProg_externAt_none]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1, h2']
      have hinst_eq : inst = zeroize32Instrs[k]'(hlen_ins ▸ hk63) :=
        Option.some.inj ((hfm1.symm.trans hfm_eq_empty.symm).trans hfm_z)
      have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
        unfold Program.fetchMem
        have h1 : (P_real.externAt? a.pc).isSome = false := by
          rw [hreal_no a.pc hka]; rfl
        have h2' : (emptyStdProg.externAt? a.pc).isSome = false := rfl
        rw [h1]
        simpa [Program.fetchMem, h2'] using hfm1
      have heval_svc : emptyStdProg.evalInst inst = P_real.evalInst inst := by
        funext st; unfold Program.evalInst; rw [hsvc]
      by_cases hk62 : k < 62
      · have hmem_take : inst ∈ zeroize32Instrs.take 62 := by
          rw [hinst_eq, List.mem_iff_getElem]
          refine ⟨k, by simp [hlen_ins]; exact hk62, List.getElem_take⟩
        have hnb : NonBranchNoLr inst = true := List.all_eq_true.mp zeroizeBody62_noLr inst hmem_take
        obtain ⟨hcomm, hlr_next, hpc_next⟩ := evalInst_nonBranchNoLr_writeReg64_lr P_real hnb a L
        let a' := P_real.evalInst inst a
        have hs2_eq : emptyStdProg.evalInst inst s1 = a'.writeReg64 .lr L := by
          rw [heval_svc, hs1]; exact hcomm
        have hrun_s2 : (emptyStdProg.evalInst inst s1).status = .Running := by
          by_contra hnr
          have heq := steps_not_running_eq hnr h2.toSteps
          exact hnr (heq ▸ hrun_sf)
        have hrun_a' : a'.status = .Running := by
          rw [hs2_eq] at hrun_s2
          have hw_st : (a'.writeReg64 .lr L).status = a'.status := by
            generalize a' = st; cases st; rfl
          exact hw_st ▸ hrun_s2
        have hka' : keepStaticSecretDrop entry a'.pc = true := by
          rw [hpc_next hrun_a', hpc_off, keepStaticSecretDrop_iff]
          have hsub : (entry + BitVec.ofNat 64 (4 * k) + 4#64) - entry =
              BitVec.ofNat 64 (4 * k + 4) := by bv_omega
          rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          show 4 * k + 4 < 252
          omega
        have hstep_real : Step P_real a a' := Step.exec hrun_a hfm_real
        have hCode' : P_z.CodeLoaded a'.mem := hCode.of_keepsFrozen hstep_real.keepsFrozen
        exact Steps.step hstep_real
          (ih hrun_sf hk_sf a' hs2_eq (hlr_next.trans hlr_a) hka' hCode')
      · have hk_eq62 : k = 62 := by omega
        have hinst_ret : inst = .ret .lr := by
          have h62 : zeroize32Instrs[62]'(by decide) = .ret .lr := by decide
          exact Eq.trans (by simpa only [hk_eq62] using hinst_eq) h62
        subst hinst_ret
        have hs2_pc : (emptyStdProg.evalInst (.ret .lr) s1).pc = L := by
          subst hs1
          dsimp only [Program.evalInst, execInstWithSvc]
          have hlr_L : (a.writeReg64 .lr L).readReg64 .lr = L := by cases a; rfl
          rw [hlr_L]; cases a; rfl
        have hk_L : keepStaticSecretDrop entry L = false := by
          rw [Bool.eq_false_iff, Ne, keepStaticSecretDrop_iff]
          have hsub : L - entry = 0xfc#64 := by dsimp [L]; bv_omega
          rw [hsub]; show ¬ (0xfc#64 : BitVec 64).toNat < 252; decide
        cases h2 with
        | step hd2 _ _ =>
          rw [hs2_pc, hk_L] at hd2; cases hd2
        | refl _ =>
          have hstep_ret : Step P_real a (P_real.evalInst (.ret .lr) a) := Step.exec hrun_a hfm_real
          have htarget_eq :
              (((emptyStdProg.evalInst (.ret .lr) s1).writeReg64 .lr lr0).setPC lr0) =
                P_real.evalInst (.ret .lr) a := by
            subst hs1
            dsimp only [Program.evalInst, execInstWithSvc]
            rw [hlr_a]
            rcases a with ⟨⟨rf⟩, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
            dsimp [State.readReg64, RegFile.read, State.writeReg64, State.setPC, RegFile.write] at hlr_a ⊢
            congr 2; funext i; by_cases hi : i = 30#5 <;> simp [hi, hlr_a]
          rw [htarget_eq]
          exact Steps.step hstep_ret (Steps.refl _)

private theorem keepZeroize32_c2_sub_keepLib2Text {pc : BitVec 64}
    (hk : keepStaticSecretDrop c2Zeroize32Addr pc = true) :
    keepLib2Text pc = true :=
  c2_keepLib2Text_of_sub_lt (by rwa [keepStaticSecretDrop_iff] at hk) (by decide) (by decide)

theorem keepZeroize32_c2_noPanic {pc : BitVec 64}
    (hk : keepStaticSecretDrop c2Zeroize32Addr pc = true) :
    isLinkedPanicAddr pc = false :=
  c2_noPanic_of_band_sub_lt (by rwa [keepStaticSecretDrop_iff] at hk) (by decide) (by decide)

theorem c2_sharedSecretDropGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsSharedSecretDropSym (c2GuardOf lsmpl lsSharedSecretDropSym)
      c2SharedSecretDropSentinelGhost := by
  refine ⟨c2_sharedSecretDropGhost_rowSpecOk, ?_⟩
  refine
    { preserves_execFrozen := fun u hrun hnoex hfr =>
        ⟨c2ZeroizeSentinelGhost_preserves_execFrozen hrun hnoex hfr,
         c2ZeroizeSentinelGhost_fs c2Zeroize32Addr u⟩
      replay_at_stub := ?_ }
  dsimp only
  intro W s0 sf _ _ _ _
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := resolve_sharedSecretDrop_eq hLs
  have hk_drop : keepLib2Text c2SharedSecretDropAddr = true := by decide
  have hnp_drop : isLinkedPanicAddr c2SharedSecretDropAddr = false := by decide
  have hk0 : keepStaticSecretDrop c2Zeroize32Addr c2Zeroize32Addr = true := by
    rw [keepStaticSecretDrop_iff, BitVec.sub_self]; decide
  refine Or.inr ⟨hRes ▸ hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk_drop) hnp_drop, ?_⟩
  intro u _ _ hpc hrun hnoex hkf hfr hinv
  have hpc' : u.pc = c2SharedSecretDropAddr := hpc.trans hRes
  let P_real := cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W
  let P_drop := pureWordsProg c2SharedSecretDropAddr [c2SharedDropWord]
  have hCode_drop : P_drop.CodeLoaded u.mem :=
    codeLoaded_of_pureSubsliceR hinv.1.rxCode c2SharedDropSlice_ok
  have hCode_z : (pureWordsProg c2Zeroize32Addr zeroize32Words).CodeLoaded u.mem :=
    codeLoaded_of_pureSubsliceR hinv.1.rxCode c2Zeroize32Slice_ok
  have hf_drop : P_drop.fetch (c2SharedSecretDropAddr + 0#64) =
      some (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) :=
    Program.fetch_of_hasWords_decodeAt 0
      (pureWordsProg_hasWords (by decide +kernel) (by decide +kernel)) rfl (by decide)
  have hfm_drop : P_drop.fetchMem u.mem u.pc =
      some (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) := by
    rw [hpc']
    simpa [BitVec.add_zero] using Program.fetchMem_of_fetch hCode_drop hf_drop
  have hfm_real0 : P_real.fetchMem u.mem u.pc =
      some (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) := by
    unfold Program.fetchMem at hfm_drop ⊢
    have h1 : (P_real.externAt? u.pc).isSome = false := by
      rw [hpc', hExt.realRxNoExtern mmpl W (keepLib2Text_sub_rxProg hk_drop) hnp_drop]; rfl
    have h2 : (P_drop.externAt? u.pc).isSome = false := by
      rw [pureWordsProg_externAt_none]; rfl
    rw [h1]; simpa [h2] using hfm_drop
  have heval_b : P_real.evalInst (.b (c2Zeroize32Addr - c2SharedSecretDropAddr)) u =
      u.setPC c2Zeroize32Addr := by
    dsimp only [Program.evalInst, execInstWithSvc]
    rw [hpc']
    have hadd : c2SharedSecretDropAddr + (c2Zeroize32Addr - c2SharedSecretDropAddr) =
        c2Zeroize32Addr := by decide
    rw [hadd]
  have hstep_b : Step P_real u (u.setPC c2Zeroize32Addr) :=
    heval_b ▸ Step.exec hrun hfm_real0
  let lr0 := u.readReg64 .lr
  let L := c2Zeroize32Addr + 0xfc#64
  let u_sent := u.writeReg64 .lr L
  have hnoex_sent : ∀ msg, (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
      (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).status ≠ .Exception msg := by
    intro msg hex
    apply hnoex msg
    dsimp only [c2SharedSecretDropSentinelGhost, c2ZeroizeSentinelGhost, L, u_sent]
    have hbe : (ExecStatus.Exception msg == .Running) = false := rfl
    rw [hex, hbe]; exact hex
  have hrun_sent : u_sent.status = .Running := by cases u; exact hrun
  have hmem_sent : u_sent.mem = u.mem := by cases u; rfl
  have hk_L : keepStaticSecretDrop c2Zeroize32Addr (u_sent.readReg64 .lr) = false := by
    have hlr_L : u_sent.readReg64 .lr = L := by cases u; rfl
    rw [hlr_L]; decide
  have hCodeSub : (pureWordsProg c2Zeroize32Addr zeroize32Words).CodeLoaded
      (ProofLib.stripExecOutside (keepStaticSecretDrop c2Zeroize32Addr) u_sent.mem) := by
    rw [hmem_sent]
    refine staticSecretDrop_codeLoaded_stripExecOutside (fun off hoff => ?_) hCode_z
    rw [keepStaticSecretDrop_iff]
    have hbase : (pureWordsProg c2Zeroize32Addr zeroize32Words).base = c2Zeroize32Addr := rfl
    have hcode : (pureWordsProg c2Zeroize32Addr zeroize32Words).code =
        (pureWordsProg 0#64 zeroize32Words).code := rfl
    have hlen0 : (pureWordsProg 0#64 zeroize32Words).code.length = 252 := by decide +kernel
    rw [hbase]
    rw [hcode, hlen0] at hoff
    have hsub : (c2Zeroize32Addr + BitVec.ofNat 64 off) - c2Zeroize32Addr =
        BitVec.ofNat 64 off := by bv_omega
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hoff
  obtain ⟨hvis, _, _⟩ := f3EmptyZeroizeGhostHook_visitedIn rfl
    (pureWordsProg_externAt_none c2Zeroize32Addr zeroize32Words)
    (pureWordsProg_zeroize32_hasWords c2Zeroize32Addr)
    hrun_sent hnoex_sent (hmem_sent ▸ hfr) hk_L hCodeSub
  have hnoex_eq := hnoex_sent
  rw [f3EmptyZeroizeGhostHook_eq] at hnoex_eq
  obtain ⟨_, hsp_sent, x, R, hpre⟩ := linkedCallHook_activeRealPre_of_noException hnoex_eq
  obtain ⟨_, _, hout⟩ := f3EmptyZeroizeGhostHook_master_ok_of_process rfl
    (pureWordsProg_externAt_none c2Zeroize32Addr zeroize32Words)
    (zeroize32_sub_proc c2Zeroize32Addr)
    (keep := keepStaticSecretDrop c2Zeroize32Addr) x R u_sent hrun_sent hpre hsp_sent
  have hret_sf : (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).status = .Running ∧
      (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).pc = L := by
    rcases hout with ⟨hr, _, _⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · exact ⟨hr.2.2, hr.1.trans (by cases u; rfl)⟩
    · dsimp only [masterZeroizeSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
    · dsimp only [masterZeroizeSpec] at he; rw [satisfies_pure_sepConj] at he; exact False.elim he.1
    · dsimp only [masterZeroizeSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1
  have hbe : (ExecStatus.Running == .Running) = true := rfl
  have hghost_eq : c2SharedSecretDropSentinelGhost u =
      ((f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).writeReg64 .lr lr0).setPC lr0 := by
    dsimp only [c2SharedSecretDropSentinelGhost, c2ZeroizeSentinelGhost, lr0, L, u_sent]
    rw [hret_sf.1, hbe]; rfl
  have hu_sent_pc : u_sent.setPC c2Zeroize32Addr = (u.setPC c2Zeroize32Addr).writeReg64 .lr L := by
    dsimp [u_sent]; cases u; rfl
  have hlr_z : (u.setPC c2Zeroize32Addr).readReg64 .lr = lr0 := by
    dsimp [lr0]; cases u; rfl
  have hk_sf : keepStaticSecretDrop c2Zeroize32Addr
      (f3EmptyZeroizeGhostHook (keepStaticSecretDrop c2Zeroize32Addr)
        (pureWordsProg c2Zeroize32Addr zeroize32Words) c2Zeroize32Addr u_sent).pc = false := by
    rw [hret_sf.2]; decide
  have hst_z := steps_zeroizeSentinel_of_visitedIn
    (P_real := P_real) (lr0 := lr0) rfl
    (fun pc hkp => hExt.realRxNoExtern mmpl W
      (keepLib2Text_sub_rxProg (keepZeroize32_c2_sub_keepLib2Text hkp))
      (keepZeroize32_c2_noPanic hkp))
    hvis hret_sf.1 hk_sf (u.setPC c2Zeroize32Addr) hu_sent_pc hlr_z hk0
    (by cases u; exact hCode_z)
  have hst := Steps.step hstep_b hst_z
  rw [← hghost_eq] at hst
  exact ⟨hst, c2ZeroizeSentinelGhost_preserves_execFrozen hrun hnoex hfr,
    f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs u (c2SharedSecretDropSentinelGhost u)
      hinv hkf (c2ZeroizeSentinelGhost_fs c2Zeroize32Addr u)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekHooksDehook

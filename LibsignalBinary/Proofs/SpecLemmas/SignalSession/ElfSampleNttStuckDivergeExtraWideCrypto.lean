/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmacRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
import LibsignalBinary.Heap.AesDecErrRoBudget
import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEncrypt
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWide
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Wide-Keep Crypto Extra Ghost `StepsStrictAvoid` of `mlkemSampleNttSyms` (`ElfSampleNttStuckDivergeExtraWideCrypto`)

Proves `StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))`
on `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` for the wide-keep crypto
`ExtraGhostTable` rows (`lsLibcruxHmacSym`, `lsAesEncSym`, and `lsAesDecSym` for both
`aesDecErrRoGhost` and `aesDecGhost`), lifting the single-program `libcrux_hmac::hmac` and
`aes_256_cbc_{encrypt,decrypt}` subroutine proofs onto `addS5Trap libcruxHmacSubProg` and
`addS5Trap aesCbcSubProg` via `ElfSampleNttStuckDivergeExtraWide`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideCrypto

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open VerifiedLibraries.RustStd (checkShimInstrsAt)
open CryptoGames.AES256 (aes256Dec aes256Enc)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsAesDecSym lsAesEncSym lsLibcruxHmacSym)
open LibsignalBinary.Heap (AllocEvent BudgetLimits zeroBudgetLimits)
open LibsignalBinary.Heap.AesDecErrRoBudget
  (aesDecBudgetSpecErrRo cliAesDecBudgetSpecErrRo cliAesDecErrStr1Addr cliAesDecErrStr1Addr_ne_zero
   cliAesDecErrStr2Addr cliAesDecErrStr2Addr_ne_zero)
open LibsignalBinary.Heap.Fine
  (f3NoShimV2Addr f3RxWordCount f3StdLayout f3StubAddrs f3StubAzAddr fineCostModel
   fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (hasShimInstrs_of_wordTree rustHandleErrorPanic_of_extern)
open LibsignalBinary.Heap.SpecBudget
  (aesCallPreBudget aesDecBudgetSpec aesEncBudgetSpec libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode (AesInitInnerCode)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt
  (Aes256CbcDecryptCallees aes256CbcDecrypt_errRo_keepsFs_of_wordTree_ok
   aes256CbcDecrypt_keepsFs_of_wordTree_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEncrypt
  (Aes256CbcEncryptCallees aes256CbcEncrypt_keepsFs_of_wordTree_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
  (bitslice4_ok bitslice_rep_ok invBitslice_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
  (Aes256DecryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
  (Aes256KeyScheduleCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers
  (memshift32_ok xorColumns_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
  (invMixColumns1_ok invMixColumns2_ok invMixColumns3_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
  (invSubBytes_ok subBytes_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256 (haclSubroutinesTrace_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib memcpySym rustAllocShimSym rustAllocSym rustAllocZeroedSym rustDeallocSym
   rustHandleErrorSym rustUnwrapFailedSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts (HaclInProg)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256 (haclMemcpy_of_allocMemcpyVm)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac
  (HaclSubroutinesTrace HmacBudgetAllocSubroutines libcruxHmac_budget_fs_subroutineOk
   withFsTraceBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep (HmacAuxSubroutines)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
  (sha256CompressState_eq_spqrSha256Compress)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
  (aesDecGhost aesDecGhost_eq_f3LinkedCallHook_of_aesStubRcon aesDecSpecOf aesEncGhost
   aesEncGhost_eq_f3LinkedCallHook_of_aesStubRcon aesEncSpecOf aesStubRconGuard c2AesRconAddr
   specPreservesFsTrace_withFsTraceExact specStripSInvariant_aesDecSpecOf
   specStripSInvariant_aesEncSpecOf withAesStubRconRO withFsTraceExact withStubPermRO)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoGhost
  (aesDecErrRoGhost aesDecErrRoGhost_eq_f3LinkedCallHook_of_aesStubRcon aesDecErrRoSpecOf
   specStripSInvariant_aesDecErrRoSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcPanicExterns aesCbcSubProg aesCbcSubProg_base aesCbcSubProg_codeLoaded_iff
   aesCbcSubProg_externAt_cases aesCbcSubProg_externAt_handleError
   aesCbcSubProg_externAt_none_of_not_panic aesCbcSubProg_svc c2Aes256DecryptAddr c2Aes256EncryptAddr
   c2Aes256KeyScheduleAddr c2AesDecAddr c2AesDecHwAddrs c2AesEncAddr c2AesEncHwAddrs
   c2AesGetauxvalHwcapAddr c2AesInitInnerAddr c2AesStorageAddr c2BitsliceAddr c2InvBitsliceAddr
   c2InvMixColumns1Addr c2InvMixColumns2Addr c2InvMixColumns3Addr c2InvSubBytesAddr
   c2LinkedPanicStubSym c2Memshift32Addr c2SubBytesAddr c2XorColumnsAddr
   c2_aes256CbcDecrypt_chk c2_aes256CbcEncrypt_chk
   c2_aes256Decrypt_chk c2_aes256Encrypt_chk c2_aesCbc_hKeep c2_aesCbc_hlr_ne_stub c2_bitslice_chk
   c2_dropDecryptor_chk c2_errnoLocation_chk c2_expandKey15_chk c2_getauxvalHwcap_chk
   c2_getauxval_chk c2_hwDecrypt15_chk c2_hwDecryptPar17_chk c2_hwEncrypt15_chk c2_initInner_chk
   c2_invBitslice_chk c2_invExpandedKeys15_chk c2_invMixColumns1_chk c2_invMixColumns2_chk
   c2_invMixColumns3_chk c2_invSubBytes_chk c2_keepRxSeg_mallocng c2_keySchedule_chk
   c2_memshift32_chk c2_mixColumns1_chk c2_mixColumns3_chk c2_mng_libc_eq c2_subBytes_chk
   c2_xorColumns_chk keepRxSeg keepRxSeg_eq_lt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow
  (c2_aesCbc_hCL_strip c2_aesCbc_hPanReal c2_aesCbc_hRconRo c2_aesCbc_hRealHullNoExt
   c2_aesCbc_hStubFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac
  (c2HaclMpl_base6 c2_haclInProg_libcruxHmacSubProg c2_libcruxHmacLib_codeLoaded_of_rxProg
   c2_libcruxHmacLib_placeable c2_libcruxHmac_hKeep c2_libcruxHmac_hlr_ne_stub
   libcruxHmacPanicExterns libcruxHmacSubProg libcruxHmacSubProg_codeLoaded_iff
   libcruxHmacSubProg_externAt_cases libcruxHmacSubProg_externAt_handleError
   libcruxHmacSubProg_externAt_none_of_not_panic libcruxHmacSubProg_externAt_unwrapFailed
   libcruxHmacSubProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmacRow
  (c2_libcruxHmac_hCL_strip c2_libcruxHmac_hPanReal c2_libcruxHmac_hRealHullNoExt
   c2_libcruxHmac_hStubFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2Kyber1024EncapsAddr c2Mlkem768FromSeedAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_of_linkedAt c2ResolveFacts_of_linkedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays
  (libcruxHmacGhost libcruxHmacGhost_eq_f3LinkedCallHook_of_stubFrozen libcruxHmacSpecOf
   specStripSInvariant_libcruxHmacSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (stripCommExtern_rustPanicked)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (isLinkedPanicAddr_false_of_ge isLinkedPanicAddr_false_of_lt isLinkedPanicAddr_false_of_mid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWide
  (addS5Trap addS5Trap_codeLoaded_iff addS5Trap_externAt_of_not_s5 addS5Trap_svc
   c2_allocZeroed_noAes_withExecFrozen_ok c2_allocZeroed_withExecFrozen_ok
   c2_alloc_withExecFrozen_ok c2_dealloc_noAes_withExecFrozen_ok c2_dealloc_withExecFrozen_ok
   c2_memcpy_f3Lo_ok c2_memset_f3Lo_ok c2_shim_f3Lo_ok f3LinkedCallHook_aesStubRcon_avoidS5
   f3LinkedCallHook_avoidS5 f3LoRxProg f3LoRxProg_codeLoaded_of_f3Trial f3LoWordCount
   fineHookPool_nonZeroEquivLim fitsEnv_nonZeroEquivLim instPoolAesInitSplitWithExecFrozenBudget
   keepLo keepLo_s5_false nonZeroEquivLim nonZeroEquivLim_ne_zero s5Addrs
   s5Addrs_contains_false_of_gt s5Addrs_contains_false_of_lt s5TrapSym withExecFrozenBudget
   withExecFrozenBudget_pool_entails withExecFrozenSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2HaclMpl c2LibcruxHmacAddr wp4HandleErrorAddr)

/-! ## 1. Shared `addS5Trap` & `keepLo` Helpers on `libcruxHmacSubProg` and `aesCbcSubProg` -/

private noncomputable abbrev P_hmac : Program := addS5Trap libcruxHmacSubProg
private noncomputable abbrev P_aes : Program := addS5Trap aesCbcSubProg

private theorem aes_trapNone : aesCbcSubProg.externs s5TrapSym = none := by
  have h : s5TrapSym ≠ c2LinkedPanicStubSym := by decide
  simp [aesCbcSubProg, aesCbcPanicExterns, h]

private theorem hmac_trapNone : libcruxHmacSubProg.externs s5TrapSym = none :=
  aes_trapNone

private theorem hmacTrap_svc : P_hmac.svc = Syscall.standard :=
  (addS5Trap_svc libcruxHmacSubProg).trans libcruxHmacSubProg_svc

private theorem aesTrap_svc : P_aes.svc = Syscall.standard :=
  (addS5Trap_svc aesCbcSubProg).trans aesCbcSubProg_svc

private theorem hmacTrap_cl_f3Lo (m : Memory) (h : P_hmac.CodeLoaded m) :
    f3LoRxProg.CodeLoaded m :=
  f3LoRxProg_codeLoaded_of_f3Trial
    ((libcruxHmacSubProg_codeLoaded_iff m).mp
      ((addS5Trap_codeLoaded_iff libcruxHmacSubProg m).mp h))

private theorem aesTrap_cl_f3Lo (m : Memory) (h : P_aes.CodeLoaded m) :
    f3LoRxProg.CodeLoaded m :=
  f3LoRxProg_codeLoaded_of_f3Trial
    ((aesCbcSubProg_codeLoaded_iff m).mp
      ((addS5Trap_codeLoaded_iff aesCbcSubProg m).mp h))

private theorem keepLo_sub_keepRxSeg {pc : BitVec 64} (hk : keepLo pc = true) :
    keepRxSeg pc = true := by
  unfold keepLo at hk
  rw [keepRxSeg_eq_lt]
  have hlt := of_decide_eq_true hk
  have hle : 4 * f3LoWordCount ≤ 4 * f3RxWordCount := by decide
  exact decide_eq_true (Nat.lt_of_lt_of_le hlt hle)

private theorem keepLo_lt_panic {pc : BitVec 64} (hk : keepLo pc = true) :
    pc.toNat < 0x479798 := by
  unfold keepLo at hk
  have hlt := of_decide_eq_true hk
  have hbase : f3RxSegBase.toNat = 0x474000 := rfl
  have hwc : 4 * f3LoWordCount = 0x5798 := rfl
  have hpc64 : pc.toNat < 2 ^ 64 := BitVec.isLt pc
  by_cases hle : f3RxSegBase.toNat ≤ pc.toNat
  · rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)] at hlt
    omega
  · have hwrap : (pc - f3RxSegBase).toNat = 2 ^ 64 - f3RxSegBase.toNat + pc.toNat := by
      rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem hmacTrap_ext_none_of_keepLo {pc : BitVec 64} (hk : keepLo pc = true) :
    P_hmac.externAt? pc = none := by
  rw [addS5Trap_externAt_of_not_s5 libcruxHmacSubProg hmac_trapNone (keepLo_s5_false hk)]
  exact libcruxHmacSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_lt (keepLo_lt_panic hk))

private theorem aesTrap_ext_none_of_keepLo {pc : BitVec 64} (hk : keepLo pc = true) :
    P_aes.externAt? pc = none := by
  rw [addS5Trap_externAt_of_not_s5 aesCbcSubProg aes_trapNone (keepLo_s5_false hk)]
  exact aesCbcSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_lt (keepLo_lt_panic hk))

/-! ## 2. Row 1: Trapped `subroutine_ok` for `libcrux_hmac::hmac` (`P_hmac`) -/

private theorem c2HaclMpl_base_gt_s5 {i : Nat} (hi : i < libcruxHmacLib.blocks.length) :
    c2Kyber1024EncapsAddr.toNat < (c2HaclMpl.base i).toNat := by
  have hlen : libcruxHmacLib.blocks.length = 7 := rfl
  rw [hlen] at hi
  match i, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide

private theorem c2_haclInProg_hmacTrap : HaclInProg P_hmac c2HaclMpl where
  placeable := c2_libcruxHmacLib_placeable
  svc_eq := hmacTrap_svc
  noHooks := by
    intro i hi off hoff
    have hgt_base := c2HaclMpl_base_gt_s5 hi
    have hnw := (c2_libcruxHmacLib_placeable.blocks_ok i hi).no_wrap
    have hoff64 : off < 2 ^ 64 := Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le hoff (Nat.le_add_left _ _)) hnw
    have hsum64 : (c2HaclMpl.base i).toNat + off < 2 ^ 64 := Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hoff _) hnw
    have hpc_nat : (c2HaclMpl.base i + BitVec.ofNat 64 off).toNat =
        (c2HaclMpl.base i).toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hsum64]
    have hns5 : s5Addrs.contains
        (c2HaclMpl.base i + BitVec.ofNat 64 off) = false :=
      s5Addrs_contains_false_of_gt (by omega)
    rw [addS5Trap_externAt_of_not_s5 libcruxHmacSubProg hmac_trapNone hns5]
    exact c2_haclInProg_libcruxHmacSubProg.noHooks i hi off hoff

private theorem hmacTrap_externAt_handleError :
    P_hmac.externAt? (c2HaclMpl.ρ rustHandleErrorSym) = some Rust.panicked := by
  rw [addS5Trap_externAt_of_not_s5 libcruxHmacSubProg hmac_trapNone
    (s5Addrs_contains_false_of_gt (by decide))]
  exact libcruxHmacSubProg_externAt_handleError

private theorem hmacTrap_externAt_unwrapFailed :
    P_hmac.externAt? (c2HaclMpl.ρ rustUnwrapFailedSym) = some Rust.panicked := by
  rw [addS5Trap_externAt_of_not_s5 libcruxHmacSubProg hmac_trapNone
    (s5Addrs_contains_false_of_lt (by decide))]
  exact libcruxHmacSubProg_externAt_unwrapFailed

private theorem c2HaclMpl_rho_memcpy : c2HaclMpl.ρ memcpySym = f3StdLayout.memcpyAddr := by
  decide

private theorem c2HaclMpl_rho_shim : c2HaclMpl.ρ rustAllocShimSym = f3NoShimV2Addr := by
  decide

private theorem c2HaclMpl_rho_alloc : c2HaclMpl.ρ rustAllocSym = f3StubAddrs.alloc := by
  decide

private theorem c2HaclMpl_rho_dealloc : c2HaclMpl.ρ rustDeallocSym = f3StubAddrs.dealloc := by
  decide

private theorem c2HaclMpl_rho_allocZeroed : c2HaclMpl.ρ rustAllocZeroedSym = f3StubAzAddr := by
  decide

private theorem c2_haclSubroutinesTrace_hmacTrap :
    HaclSubroutinesTrace P_hmac c2HaclMpl := by
  refine haclSubroutinesTrace_ok c2_haclInProg_hmacTrap ?_
  rw [c2HaclMpl_rho_memcpy]
  exact haclMemcpy_of_allocMemcpyVm
    (c2_memcpy_f3Lo_ok hmacTrap_svc hmacTrap_cl_f3Lo (fun _ hk => hmacTrap_ext_none_of_keepLo hk))

private theorem c2_hmacAux_hmacTrap :
    HmacAuxSubroutines P_hmac c2HaclMpl :=
  HmacAuxSubroutines.of_rustStdAllocAux
    ⟨c2HaclMpl_rho_shim ▸ c2_shim_f3Lo_ok hmacTrap_svc hmacTrap_cl_f3Lo
       (fun _ hk => hmacTrap_ext_none_of_keepLo hk),
     c2HaclMpl_rho_memcpy ▸ c2_memcpy_f3Lo_ok hmacTrap_svc hmacTrap_cl_f3Lo
       (fun _ hk => hmacTrap_ext_none_of_keepLo hk),
     rustHandleErrorPanic_of_extern hmacTrap_externAt_handleError⟩
    hmacTrap_externAt_unwrapFailed

private theorem c2_hmacBudgetAlloc_hmacTrap (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits) :
    HmacBudgetAllocSubroutines fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim
      P_hmac c2HaclMpl where
  allocZeroed_ok := by
    rw [c2HaclMpl_rho_allocZeroed]
    exact c2_allocZeroed_withExecFrozen_ok hMm γ tp brkStart hlim
      hmacTrap_svc hmacTrap_cl_f3Lo (fun _ hk => hmacTrap_ext_none_of_keepLo hk)
  alloc_ok := by
    rw [c2HaclMpl_rho_alloc]
    exact c2_alloc_withExecFrozen_ok hMm γ tp brkStart hlim
      hmacTrap_svc hmacTrap_cl_f3Lo (fun _ hk => hmacTrap_ext_none_of_keepLo hk)
  dealloc_ok := by
    rw [c2HaclMpl_rho_dealloc]
    exact c2_dealloc_withExecFrozen_ok hMm γ tp brkStart hlim
      hmacTrap_svc hmacTrap_cl_f3Lo (fun _ hk => hmacTrap_ext_none_of_keepLo hk)

private theorem c2_libcruxHmac_trap_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok P_hmac c2LibcruxHmacAddr
      (withStubPermRO libcruxHmacSubProg
        (withExecFrozenSpec
          (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp)))) := by
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp brkStart
  let A' := withExecFrozenBudget A0
  have hRaw := libcruxHmac_budget_fs_subroutineOk
    c2_haclInProg_hmacTrap
    (fun m hCL => c2_libcruxHmacLib_codeLoaded_of_rxProg
      ((libcruxHmacSubProg_codeLoaded_iff m).mp
        ((addS5Trap_codeLoaded_iff libcruxHmacSubProg m).mp hCL)))
    c2_haclSubroutinesTrace_hmacTrap
    c2_hmacAux_hmacTrap
    hmacTrap_externAt_unwrapFailed
    (c2_hmacBudgetAlloc_hmacTrap mmpl hMm γ tp brkStart hlim')
  rw [c2HaclMpl_base6, sha256CompressState_eq_spqrSha256Compress] at hRaw
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withStubPermRO, withExecFrozenSpec, withFsTraceExact, libcruxHmacSpecOf,
    withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hro, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfr, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hret, hpre⟩
  have hpre' : s0.mem ⊨
      (withFsTraceBudget (libcruxHmacBudgetSpec sha256Compress fineCostModel A' lim')).pre
        (x, st0) s0 ∗ R := by
    dsimp only [withFsTraceBudget, libcruxHmacBudgetSpec, A', A0, withExecFrozenBudget,
      lim'] at hpre ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFsTraceBudget, libcruxHmacBudgetSpec, A', A0, lim'] at hpost
    dsimp only [withStubPermRO, withExecFrozenSpec, withFsTraceExact, libcruxHmacSpecOf,
      withLsRet, libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hfs_tr, hpost⟩
    refine ⟨hfs_tr, ?_⟩
    rw [sepExists_sepConj_left] at hpost ⊢
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hev_pure, hpost⟩
    refine ⟨hev_pure, ?_⟩
    refine Satisfies.mono ?_ hpost
    exact sepConj_mono_left
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono_left (withExecFrozenBudget_pool_entails γ mmpl tp brkStart lim _ sf)))))
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    simpa only [withStubPermRO, withExecFrozenSpec, withFsTraceExact, libcruxHmacSpecOf,
      withLsRet, withFsTraceBudget, libcruxHmacBudgetSpec] using hpan
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-! ## 3. Rows 2 & 3: Trapped `subroutine_ok` for `aes_256_cbc_{encrypt,decrypt}` (`P_aes`) -/

private theorem aesTrap_code : P_aes.code = f3TrialRxWordTree.toBytes :=
  f3TrialRxWordTree_eq

private theorem aesTrap_base : P_aes.base = f3RxSegBase :=
  aesCbcSubProg_base

private theorem aesTrap_hookAtOff_none_of_gt {off : Nat}
    (hband : (c2Kyber1024EncapsAddr.toNat < f3RxSegBase.toNat + off ∧
        f3RxSegBase.toNat + off < 0x4cb070) ∨
      (0x4cb0e4 ≤ f3RxSegBase.toNat + off ∧
        f3RxSegBase.toNat + off < f3RxSegBase.toNat + 4 * f3RxWordCount)) :
    P_aes.hookAtOff? off = none := by
  have htop : f3RxSegBase.toNat + 4 * f3RxWordCount < 2 ^ 64 := by decide
  have hoff64 : off < 2 ^ 64 := by omega
  let pc : BitVec 64 := f3RxSegBase + BitVec.ofNat 64 off
  have hpc_nat : pc.toNat = f3RxSegBase.toNat + off := by
    dsimp only [pc]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt (by omega)]
  have hsub_nat : (pc - f3RxSegBase).toNat = off := by
    have hbv : pc - f3RxSegBase = BitVec.ofNat 64 off := by dsimp only [pc]; bv_omega
    rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64]
  have hext_eq : P_aes.externAt? pc = P_aes.hookAtOff? off := by
    unfold Program.externAt?
    rw [aesTrap_base, hsub_nat]
  have hlo_mid : 0x47ac2c ≤ c2Kyber1024EncapsAddr.toNat := by decide
  have hhi_s5 : c2Kyber1024EncapsAddr.toNat < 0x4cb0e4 := by decide
  rw [← hext_eq, addS5Trap_externAt_of_not_s5 aesCbcSubProg aes_trapNone
    (s5Addrs_contains_false_of_gt (by omega))]
  rcases hband with ⟨_, _⟩ | ⟨_, _⟩
  · exact aesCbcSubProg_externAt_none_of_not_panic
      (isLinkedPanicAddr_false_of_mid (by omega) (by omega))
  · exact aesCbcSubProg_externAt_none_of_not_panic
      (isLinkedPanicAddr_false_of_ge (by omega))

private theorem aesTrap_hookAtOff_none_of_lt {off : Nat}
    (hlt_p : f3RxSegBase.toNat + off < 0x479798) :
    P_aes.hookAtOff? off = none := by
  have hoff64 : off < 2 ^ 64 := by omega
  let pc : BitVec 64 := f3RxSegBase + BitVec.ofNat 64 off
  have hpc_nat : pc.toNat = f3RxSegBase.toNat + off := by
    dsimp only [pc]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt (by omega)]
  have hsub_nat : (pc - f3RxSegBase).toNat = off := by
    have hbv : pc - f3RxSegBase = BitVec.ofNat 64 off := by dsimp only [pc]; bv_omega
    rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64]
  have hext_eq : P_aes.externAt? pc = P_aes.hookAtOff? off := by
    unfold Program.externAt?
    rw [aesTrap_base, hsub_nat]
  have hs5 : 0x479798 ≤ c2Mlkem768FromSeedAddr.toNat := by decide
  rw [← hext_eq, addS5Trap_externAt_of_not_s5 aesCbcSubProg aes_trapNone
    (s5Addrs_contains_false_of_lt (by omega))]
  exact aesCbcSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_lt (by omega))

private theorem hasInstrs_aesTrap_of_check {addr : BitVec 64} {instrs : List Instr}
    (hband : (c2Kyber1024EncapsAddr.toNat < addr.toNat ∧
        addr.toNat + 4 * instrs.length ≤ 0x4cb070) ∨
      (0x4cb0e4 ≤ addr.toNat ∧
        addr.toNat + 4 * instrs.length ≤ f3RxSegBase.toNat + 4 * f3RxWordCount))
    (hchk : checkShimInstrsAt f3RxSegBase f3TrialRxWordTree addr instrs = true) :
    hasInstrs P_aes addr instrs := by
  have hchk' : checkShimInstrsAt P_aes.base f3TrialRxWordTree addr instrs = true := by
    rwa [aesTrap_base]
  simp only [checkShimInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
  have hbase_add : f3RxSegBase + BitVec.ofNat 64 (addr - f3RxSegBase).toNat = addr := hchk.1.1
  refine hasShimInstrs_of_wordTree f3RxWordCount aesTrap_code f3TrialRxWordTree_size
    (fun i hi => ?_) hchk'
  have hoff0_64 : (addr - f3RxSegBase).toNat < 2 ^ 64 := BitVec.isLt _
  have hrx_lt : f3RxSegBase.toNat < c2Kyber1024EncapsAddr.toNat := by decide
  have hrx_lt2 : f3RxSegBase.toNat < 0x4cb0e4 := by decide
  have haddr_le : f3RxSegBase.toNat ≤ addr.toNat := by omega
  have haddr_nat : addr.toNat = f3RxSegBase.toNat + (addr - f3RxSegBase).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr haddr_le)]
    omega
  rw [aesTrap_base]
  exact aesTrap_hookAtOff_none_of_gt (by omega)

private theorem hasInstrs_aesTrap_of_check_lt {addr : BitVec 64} {instrs : List Instr}
    (hlt_end : addr.toNat + 4 * instrs.length ≤ 0x479798)
    (hchk : checkShimInstrsAt f3RxSegBase f3TrialRxWordTree addr instrs = true)
    (hge : f3RxSegBase.toNat ≤ addr.toNat := by decide) :
    hasInstrs P_aes addr instrs := by
  have hchk' : checkShimInstrsAt P_aes.base f3TrialRxWordTree addr instrs = true := by
    rwa [aesTrap_base]
  refine hasShimInstrs_of_wordTree f3RxWordCount aesTrap_code f3TrialRxWordTree_size
    (fun i hi => ?_) hchk'
  have haddr_nat : addr.toNat = f3RxSegBase.toNat + (addr - f3RxSegBase).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hge)]
    omega
  rw [aesTrap_base]
  exact aesTrap_hookAtOff_none_of_lt (by omega)

private theorem aesTrap_externAt_handleError :
    P_aes.externAt? wp4HandleErrorAddr = some Rust.panicked := by
  rw [addS5Trap_externAt_of_not_s5 aesCbcSubProg aes_trapNone
    (s5Addrs_contains_false_of_gt (by decide))]
  exact aesCbcSubProg_externAt_handleError

private theorem c2_aesInitInnerCode_aesTrap (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    AesInitInnerCode P_aes c2AesInitInnerAddr c2AesGetauxvalHwcapAddr
      f3StdLayout.getauxvalAddr f3StdLayout.errnoLocationAddr
      (mallocngAddrsOfPlacement mmpl).libc c2AesStorageAddr where
  initInner_code := hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_initInner_chk
  getauxvalHwcap_code := hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_getauxvalHwcap_chk
  getauxval_code := by
    rw [c2_mng_libc_eq mmpl hMm]
    exact hasInstrs_aesTrap_of_check_lt (by decide) c2_getauxval_chk
  errnoLocation_code := hasInstrs_aesTrap_of_check_lt (by decide) c2_errnoLocation_chk

private theorem c2_ksCallees_aesTrap :
    Aes256KeyScheduleCallees P_aes f3StdLayout.memsetAddr c2BitsliceAddr
      c2Memshift32Addr c2SubBytesAddr c2XorColumnsAddr f3StdLayout.memcpyAddr where
  memset_ok := c2_memset_f3Lo_ok aesTrap_svc aesTrap_cl_f3Lo
    (fun _ hk => aesTrap_ext_none_of_keepLo hk)
  bitslice_ok := bitslice_rep_ok (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_bitslice_chk)
  memshift32_ok := memshift32_ok P_aes c2Memshift32Addr
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_memshift32_chk)
  subBytes_ok := subBytes_ok (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_subBytes_chk)
  xorColumns_ok := xorColumns_ok P_aes c2XorColumnsAddr
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_xorColumns_chk)
  memcpy_ok := c2_memcpy_f3Lo_ok aesTrap_svc aesTrap_cl_f3Lo
    (fun _ hk => aesTrap_ext_none_of_keepLo hk)

private theorem c2_decBlockCallees_aesTrap :
    Aes256DecryptCallees P_aes c2BitsliceAddr c2InvSubBytesAddr
      c2InvMixColumns1Addr c2InvMixColumns2Addr c2InvMixColumns3Addr c2InvBitsliceAddr where
  bitslice_ok := bitslice4_ok (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_bitslice_chk)
  invSubBytes_ok := invSubBytes_ok (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invSubBytes_chk)
  invMixColumns1_ok := invMixColumns1_ok
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invMixColumns1_chk)
  invMixColumns2_ok := invMixColumns2_ok
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invMixColumns2_chk)
  invMixColumns3_ok := invMixColumns3_ok
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invMixColumns3_chk)
  invBitslice_ok := invBitslice_ok (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invBitslice_chk)

private theorem c2_aesEnc_trap_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (hbrk : brkStart = f3StdLayout.brkStart)
    (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok P_aes c2AesEncAddr
      (withAesStubRconRO aesCbcSubProg
        (withExecFrozenSpec
          (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp)))) := by
  subst hbrk
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart
  let A' := withExecFrozenBudget A0
  have hCal : Aes256CbcEncryptCallees fineCostModel A' lim' P_aes c2AesEncHwAddrs
      c2Aes256KeyScheduleAddr c2Aes256EncryptAddr f3NoShimV2Addr f3StubAzAddr
      f3StdLayout.memcpyAddr f3StdLayout.memsetAddr wp4HandleErrorAddr :=
    Aes256CbcEncryptCallees.of_hasInstrs lim'
      (c2_aesInitInnerCode_aesTrap mmpl hMm)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_expandKey15_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invExpandedKeys15_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_hwEncrypt15_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_dropDecryptor_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_keySchedule_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_aes256Encrypt_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_bitslice_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_memshift32_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_subBytes_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_xorColumns_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_mixColumns1_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_mixColumns3_chk)
      (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invBitslice_chk)
      (c2_allocZeroed_noAes_withExecFrozen_ok hMm γ tp f3StdLayout.brkStart hlim'
        aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk))
      ⟨c2_shim_f3Lo_ok aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk),
       c2_memcpy_f3Lo_ok aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk),
       rustHandleErrorPanic_of_extern aesTrap_externAt_handleError⟩
      (c2_memset_f3Lo_ok aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk))
  have hRaw := aes256CbcEncrypt_keepsFs_of_wordTree_ok (fnAddr := c2AesEncAddr)
    A' lim' f3RxWordCount aesTrap_code f3TrialRxWordTree_size
    (fun i hi => by
      rw [aesTrap_base]
      have hfit : f3RxSegBase.toNat + (c2AesEncAddr - f3RxSegBase).toNat + 4 * 595 ≤ 0x4cb070 := by
        decide
      have hgt : c2Kyber1024EncapsAddr.toNat <
          f3RxSegBase.toNat + (c2AesEncAddr - f3RxSegBase).toNat := by decide
      exact aesTrap_hookAtOff_none_of_gt (Or.inl ⟨by omega, by omega⟩))
    c2_aes256CbcEncrypt_chk
    hCal
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withExecFrozenSpec,
    withFsTraceExact, aesEncSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hro, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hrcon, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfr, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hret, hpre⟩
  have hpre' : s0.mem ⊨
      (withRoData c2AesRconAddr aesRconBytes
        (keepsFs (aesEncBudgetSpec aes256Enc fineCostModel A' lim'))).pre (x, st0) s0 ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hrcon, ?_⟩
    dsimp only [keepsFs, aesEncBudgetSpec, aesCallPreBudget, A', A0, withExecFrozenBudget,
      lim'] at hpre ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, keepsFs, aesEncBudgetSpec, A', A0, lim'] at hpost
    dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withExecFrozenSpec,
      withFsTraceExact, aesEncSpecOf, withLsRet, aesEncBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hfs, hpost⟩
    rw [sepExists_sepConj_left] at hpost
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, hev⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfs, htr⟩, ?_⟩
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hev⟩, ?_⟩
    refine Satisfies.mono ?_ hpost
    exact sepConj_mono_left
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono_left
            (withExecFrozenBudget_pool_entails γ mmpl tp f3StdLayout.brkStart lim _ sf))))
  · dsimp only [withRoData, keepsFs, aesEncBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

private theorem c2_aesDecCallees_aesTrap (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits) :
    Aes256CbcDecryptCallees fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart)) lim P_aes
      c2AesDecHwAddrs c2Aes256KeyScheduleAddr c2Aes256DecryptAddr f3NoShimV2Addr f3StubAzAddr
      f3StubAddrs.dealloc f3StdLayout.memcpyAddr wp4HandleErrorAddr :=
  Aes256CbcDecryptCallees.of_hasInstrs
    (c2_aesInitInnerCode_aesTrap mmpl hMm)
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_expandKey15_chk)
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_invExpandedKeys15_chk)
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_hwDecryptPar17_chk)
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_hwDecrypt15_chk)
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_dropDecryptor_chk)
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_keySchedule_chk)
    c2_ksCallees_aesTrap
    (hasInstrs_aesTrap_of_check (of_decide_eq_true (by rfl_kernel)) c2_aes256Decrypt_chk)
    c2_decBlockCallees_aesTrap
    (c2_shim_f3Lo_ok aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk))
    (c2_allocZeroed_noAes_withExecFrozen_ok hMm γ tp f3StdLayout.brkStart hlim
      aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk))
    (c2_dealloc_noAes_withExecFrozen_ok hMm γ tp f3StdLayout.brkStart hlim
      aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk))
    (c2_memcpy_f3Lo_ok aesTrap_svc aesTrap_cl_f3Lo (fun _ hk => aesTrap_ext_none_of_keepLo hk))
    (rustHandleErrorPanic_of_extern aesTrap_externAt_handleError)

private theorem c2_aesDec_trap_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (hbrk : brkStart = f3StdLayout.brkStart)
    (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok P_aes c2AesDecAddr
      (withAesStubRconRO aesCbcSubProg
        (withExecFrozenSpec
          (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)))) := by
  subst hbrk
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart
  let A' := withExecFrozenBudget A0
  have hRaw := aes256CbcDecrypt_keepsFs_of_wordTree_ok (fnAddr := c2AesDecAddr)
    A' lim' f3RxWordCount aesTrap_code f3TrialRxWordTree_size
    (fun i hi => by
      rw [aesTrap_base]
      have hfit : f3RxSegBase.toNat + (c2AesDecAddr - f3RxSegBase).toNat + 4 * 900 ≤ 0x4cb070 := by
        decide
      have hgt : c2Kyber1024EncapsAddr.toNat <
          f3RxSegBase.toNat + (c2AesDecAddr - f3RxSegBase).toNat := by decide
      exact aesTrap_hookAtOff_none_of_gt (Or.inl ⟨by omega, by omega⟩))
    c2_aes256CbcDecrypt_chk
    (c2_aesDecCallees_aesTrap mmpl hMm γ tp hlim')
    cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr_ne_zero
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withExecFrozenSpec,
    withFsTraceExact, aesDecSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hro, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hrcon, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfr, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hret, hpre⟩
  have hpre' : s0.mem ⊨
      (withRoData c2AesRconAddr aesRconBytes
        (keepsFs (aesDecBudgetSpec aes256Dec fineCostModel A' lim'))).pre (x, st0) s0 ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hrcon, ?_⟩
    dsimp only [keepsFs, aesDecBudgetSpec, aesCallPreBudget, A', A0, withExecFrozenBudget,
      lim'] at hpre ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, keepsFs, aesDecBudgetSpec, A', A0, lim'] at hpost
    dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withExecFrozenSpec,
      withFsTraceExact, aesDecSpecOf, withLsRet, aesDecBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hfs, hpost⟩
    rw [sepExists_sepConj_left] at hpost
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, hev⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfs, htr⟩, ?_⟩
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hev⟩, ?_⟩
    refine Satisfies.mono ?_ hpost
    exact sepConj_mono_left
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono_left
            (withExecFrozenBudget_pool_entails γ mmpl tp f3StdLayout.brkStart lim _ sf))))
  · dsimp only [withRoData, keepsFs, aesDecBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

private theorem c2_aesDec_errRo_trap_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (hbrk : brkStart = f3StdLayout.brkStart)
    (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok P_aes c2AesDecAddr
      (withAesStubRconRO aesCbcSubProg
        (withExecFrozenSpec
          (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)))) := by
  subst hbrk
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart
  let A' := withExecFrozenBudget A0
  have hRaw := aes256CbcDecrypt_errRo_keepsFs_of_wordTree_ok (fnAddr := c2AesDecAddr)
    A' lim' f3RxWordCount aesTrap_code f3TrialRxWordTree_size
    (fun i hi => by
      rw [aesTrap_base]
      have hfit : f3RxSegBase.toNat + (c2AesDecAddr - f3RxSegBase).toNat + 4 * 900 ≤ 0x4cb070 := by
        decide
      have hgt : c2Kyber1024EncapsAddr.toNat <
          f3RxSegBase.toNat + (c2AesDecAddr - f3RxSegBase).toNat := by decide
      exact aesTrap_hookAtOff_none_of_gt (Or.inl ⟨by omega, by omega⟩))
    c2_aes256CbcDecrypt_chk
    (c2_aesDecCallees_aesTrap mmpl hMm γ tp hlim')
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withExecFrozenSpec,
    withFsTraceExact, aesDecErrRoSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hro, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hrcon, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfr, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hret, hpre⟩
  have hpre' : s0.mem ⊨
      (withRoData c2AesRconAddr aesRconBytes
        (keepsFs
          (aesDecBudgetSpecErrRo aes256Dec cliAesDecErrStr1Addr cliAesDecErrStr2Addr
            fineCostModel A' lim'))).pre (x, st0) s0 ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hrcon, ?_⟩
    dsimp only [keepsFs, cliAesDecBudgetSpecErrRo, aesDecBudgetSpecErrRo, aesCallPreBudget,
      A', A0, withExecFrozenBudget, lim'] at hpre ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, keepsFs, aesDecBudgetSpecErrRo, A', A0, lim'] at hpost
    dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withExecFrozenSpec,
      withFsTraceExact, aesDecErrRoSpecOf, withLsRet, cliAesDecBudgetSpecErrRo,
      aesDecBudgetSpecErrRo]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hfs, hpost⟩
    rw [sepExists_sepConj_left] at hpost
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, hev⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfs, htr⟩, ?_⟩
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hev⟩, ?_⟩
    refine Satisfies.mono ?_ hpost
    exact sepConj_mono_left
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono_left
            (withExecFrozenBudget_pool_entails γ mmpl tp f3StdLayout.brkStart lim _ sf))))
  · dsimp only [withRoData, keepsFs, aesDecBudgetSpecErrRo] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-! ## 4. Exported `StepsStrictAvoid` Theorems for Wide-Keep Crypto Rows 1–3 -/

private theorem setPC_eq_self {u : State} {target : BitVec 64} (h : u.pc = target) :
    u.setPC target = u := by
  cases u
  dsimp only [State.setPC] at h ⊢
  subst h
  rfl

theorem c2_libcruxHmacGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsLibcruxHmacSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (libcruxHmacGhost
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac.keepRxSeg
        libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (libcruxHmacGhost
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac.keepRxSeg
        libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim u) := by
  have hSF := c2_libcruxHmac_hStubFrozen hLs (fun (_ : State) (h : F3CodeInv mpl mmpl _) => h) u hinv
  have heq := libcruxHmacGhost_eq_f3LinkedCallHook_of_stubFrozen
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac.keepRxSeg
    libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim hSF
  rw [heq] at hnoex ⊢
  exact f3LinkedCallHook_avoidS5
    (InvS := fun z => F3CodeInv mpl mmpl z.mem)
    (sym := lsLibcruxHmacSym)
    (specOf := fun γ tp => withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))
    hLs hmac_trapNone libcruxHmacSubProg_svc
    (fun _ _ he => (libcruxHmacSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked _)
    (fun γ tp => c2_libcruxHmac_trap_subroutineOk mmpl hMm brkStart lim γ tp)
    (fun γ tp =>
      specStripSInvariant_libcruxHmacSpecOf γ mmpl tp brkStart (c2_keepRxSeg_mallocng mmpl hMm) lim)
    (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
    (fun _ _ ⟨_, _⟩ s _ => by cases s; rfl)
    (fun _ _ _ _ s0 _ _ => by cases s0; exact id)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, libcruxHmacSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_libcruxHmac_hKeep hLsLsmpl hpre.1)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, libcruxHmacSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_libcruxHmac_hlr_ne_stub hLsLsmpl _ hpre.1)
    (fun _ => rfl)
    (fun W' _ hk hnone => c2_libcruxHmac_hRealHullNoExt (c2ExternTableFacts_of_linkedAt hLs) W' hk hnone)
    (fun W' pc f he => by
      obtain ⟨rfl, h2⟩ := c2_libcruxHmac_hPanReal mmpl hLs W' pc f he
      exact h2)
    (fun _ s hs _ _ _ => by
      rw [setPC_eq_self (hs.trans (c2ResolveFacts_of_linkedAt hLs).libcruxHmac_eq)]
      exact StepsStrictAvoid.refl s)
    (c2_libcruxHmac_hStubFrozen hLs (fun _ h => h))
    (c2_libcruxHmac_hCL_strip (fun _ h => h))
    hpc hrun hnoex hfr hinv

theorem c2_aesEncGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsAesEncSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr
        mmpl brkStart lim u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr
        mmpl brkStart lim u) := by
  have hSF := c2_aesCbc_hStubFrozen hLs (fun (_ : State) (h : F3CodeInv mpl mmpl _) => h) u hinv
  have hRcon := c2_aesCbc_hRconRo hLs (fun (_ : State) (h : F3CodeInv mpl mmpl _) => h) u hinv
  have hG : aesStubRconGuard aesCbcSubProg brkStart u := ⟨hSF, hRcon, hbrk⟩
  have heq := aesEncGhost_eq_f3LinkedCallHook_of_aesStubRcon
    keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim hG
  rw [heq] at hnoex ⊢
  exact f3LinkedCallHook_aesStubRcon_avoidS5
    (InvS := fun z => F3CodeInv mpl mmpl z.mem)
    (sym := lsAesEncSym)
    (specOf := fun γ tp => withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))
    hLs aes_trapNone aesCbcSubProg_svc
    (fun _ _ he => (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked _)
    (fun γ tp => c2_aesEnc_trap_subroutineOk mmpl hMm brkStart hbrk lim γ tp)
    (fun γ tp =>
      specStripSInvariant_aesEncSpecOf γ mmpl tp brkStart (c2_keepRxSeg_mallocng mmpl hMm) lim)
    (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
    (fun _ _ ⟨_, _⟩ s _ => by cases s; rfl)
    (fun _ _ _ _ s0 _ _ => by cases s0; exact id)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, aesEncSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_aesCbc_hKeep hLsLsmpl hpre.1)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, aesEncSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_aesCbc_hlr_ne_stub hLsLsmpl _ hpre.1)
    (fun _ => rfl)
    (fun W' _ hk hnone => c2_aesCbc_hRealHullNoExt (c2ExternTableFacts_of_linkedAt hLs) W' hk hnone)
    (fun W' pc f he => by
      obtain ⟨rfl, h2⟩ := c2_aesCbc_hPanReal mmpl hLs W' pc f he
      exact h2)
    (fun _ s hs _ _ _ => by
      rw [setPC_eq_self (hs.trans (c2ResolveFacts_of_linkedAt hLs).aesEnc_eq)]
      exact StepsStrictAvoid.refl s)
    (c2_aesCbc_hStubFrozen hLs (fun _ h => h))
    (c2_aesCbc_hRconRo hLs (fun _ h => h))
    (c2_aesCbc_hCL_strip (fun _ h => h))
    hpc hrun hnoex hfr hinv

theorem c2_aesDecErrRoGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsAesDecSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr
        mmpl brkStart lim u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr
        mmpl brkStart lim u) := by
  have hSF := c2_aesCbc_hStubFrozen hLs (fun (_ : State) (h : F3CodeInv mpl mmpl _) => h) u hinv
  have hRcon := c2_aesCbc_hRconRo hLs (fun (_ : State) (h : F3CodeInv mpl mmpl _) => h) u hinv
  have hG : aesStubRconGuard aesCbcSubProg brkStart u := ⟨hSF, hRcon, hbrk⟩
  have heq := aesDecErrRoGhost_eq_f3LinkedCallHook_of_aesStubRcon
    keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim hG
  rw [heq] at hnoex ⊢
  exact f3LinkedCallHook_aesStubRcon_avoidS5
    (InvS := fun z => F3CodeInv mpl mmpl z.mem)
    (sym := lsAesDecSym)
    (specOf := fun γ tp => withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))
    hLs aes_trapNone aesCbcSubProg_svc
    (fun _ _ he => (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked _)
    (fun γ tp => c2_aesDec_errRo_trap_subroutineOk mmpl hMm brkStart hbrk lim γ tp)
    (fun γ tp =>
      specStripSInvariant_aesDecErrRoSpecOf γ mmpl tp brkStart (c2_keepRxSeg_mallocng mmpl hMm) lim)
    (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
    (fun _ _ ⟨_, _⟩ s _ => by cases s; rfl)
    (fun _ _ _ _ s0 _ _ => by cases s0; exact id)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, aesDecErrRoSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_aesCbc_hKeep hLsLsmpl hpre.1)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, aesDecErrRoSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_aesCbc_hlr_ne_stub hLsLsmpl _ hpre.1)
    (fun _ => rfl)
    (fun W' _ hk hnone => c2_aesCbc_hRealHullNoExt (c2ExternTableFacts_of_linkedAt hLs) W' hk hnone)
    (fun W' pc f he => by
      obtain ⟨rfl, h2⟩ := c2_aesCbc_hPanReal mmpl hLs W' pc f he
      exact h2)
    (fun _ s hs _ _ _ => by
      rw [setPC_eq_self (hs.trans (c2ResolveFacts_of_linkedAt hLs).aesDec_eq)]
      exact StepsStrictAvoid.refl s)
    (c2_aesCbc_hStubFrozen hLs (fun _ h => h))
    (c2_aesCbc_hRconRo hLs (fun _ h => h))
    (c2_aesCbc_hCL_strip (fun _ h => h))
    hpc hrun hnoex hfr hinv

theorem c2_aesDecGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsAesDecSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr
        mmpl brkStart lim u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr
        mmpl brkStart lim u) := by
  have hSF := c2_aesCbc_hStubFrozen hLs (fun (_ : State) (h : F3CodeInv mpl mmpl _) => h) u hinv
  have hRcon := c2_aesCbc_hRconRo hLs (fun (_ : State) (h : F3CodeInv mpl mmpl _) => h) u hinv
  have hG : aesStubRconGuard aesCbcSubProg brkStart u := ⟨hSF, hRcon, hbrk⟩
  have heq := aesDecGhost_eq_f3LinkedCallHook_of_aesStubRcon
    keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim hG
  rw [heq] at hnoex ⊢
  exact f3LinkedCallHook_aesStubRcon_avoidS5
    (InvS := fun z => F3CodeInv mpl mmpl z.mem)
    (sym := lsAesDecSym)
    (specOf := fun γ tp => withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))
    hLs aes_trapNone aesCbcSubProg_svc
    (fun _ _ he => (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked _)
    (fun γ tp => c2_aesDec_trap_subroutineOk mmpl hMm brkStart hbrk lim γ tp)
    (fun γ tp =>
      specStripSInvariant_aesDecSpecOf γ mmpl tp brkStart (c2_keepRxSeg_mallocng mmpl hMm) lim)
    (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
    (fun _ _ ⟨_, _⟩ s _ => by cases s; rfl)
    (fun _ _ _ _ s0 _ _ => by cases s0; exact id)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, aesDecSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_aesCbc_hKeep hLsLsmpl hpre.1)
    (fun _ _ _ _ s hpre => by
      dsimp only [withFsTraceExact, aesDecSpecOf, withLsRet] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact c2_aesCbc_hlr_ne_stub hLsLsmpl _ hpre.1)
    (fun _ => rfl)
    (fun W' _ hk hnone => c2_aesCbc_hRealHullNoExt (c2ExternTableFacts_of_linkedAt hLs) W' hk hnone)
    (fun W' pc f he => by
      obtain ⟨rfl, h2⟩ := c2_aesCbc_hPanReal mmpl hLs W' pc f he
      exact h2)
    (fun _ s hs _ _ _ => by
      rw [setPC_eq_self (hs.trans (c2ResolveFacts_of_linkedAt hLs).aesDec_eq)]
      exact StepsStrictAvoid.refl s)
    (c2_aesCbc_hStubFrozen hLs (fun _ h => h))
    (c2_aesCbc_hRconRo hLs (fun _ h => h))
    (c2_aesCbc_hCL_strip (fun _ h => h))
    hpc hrun hnoex hfr hinv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideCrypto

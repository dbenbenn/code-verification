/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Budget-Threaded `cliExternsPlaced` and `cliGhostExterns` Contracts (Placed)

`VmPreserved`-strengthened `HookSat` contracts for non-allocating ghost-hook rows, together with
budget-threaded ghost-hook bundles (`CliGhostAllocHooks`, `CliGhostSpqrAllocHooks`, and
`CliAllocHooks`) over `cliGhostExterns g (cliExternsPlaced mmpl W)` under `[LibsignalPlacement]`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalHooks LibsignalPlacement libsignalHookedExterns
  libsignalSessionExterns lsHandleErrorSym ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (derivePublicKeyBytesSpec derivePublicKeyBytesStackSpec diffieHellmanSpec extHookStack framelessMemcpySpec framelessMemcpy_hookOk hookMemcpy_region_trace_ok hookMemcpy_trace_ok hookMemmove_trace_ok hookMemset_region_trace_ok hookMemset_trace_ok memcpyName memmoveName memsetName noAllocShimSpec noAllocShim_hookOk pubFromSecretSpec sessionMemcpyRegionSpec sessionMemcpySpec sessionMemsetRegionSpec sessionMemsetSpec sessionShim_hookOk withStack zeroizeSecretSpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsBlackBoxSym lsDiffieHellmanSym lsDurationSinceSym lsFmtWriteSym lsFormatInnerSym lsFromUtf8Sym lsMemcpySym lsMemrchrSym lsMemsetSym lsPubFromSecretSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsSpqrOnceCallSym lsStringCloneSym lsTimeAddSym lsWriteFileSym lsWriteStdoutSym writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops (allocHook0_fs cliIo deallocHook_fs extHookStack_le fromUtf8AsciiSpec hookMemcpy_fs hookMemmove_fs hookMemset_fs hookNoop_fs hookOk_withStack memrchrSpec pos_of_extHookStack_le reallocHook0_fs strlenSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC allocHook0_fsT cliExternsPlaced_row cliExtraGhostSyms cliGhostExterns cliGhostExterns_alloc cliGhostExterns_allocZeroed cliGhostExterns_dealloc cliGhostExterns_memcpy_some cliGhostExterns_memset_some cliGhostExterns_other cliGhostExterns_realloc cliGhostExterns_shim deallocHook_fsT hookMemcpy_fsT hookMemset_fsT hookSat_of_eq reallocHook0_fsT)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_panic_handle_alloc_error cliGhostExterns_panic_handle_error cliGhostExterns_panic_option_expect_failed cliGhostExterns_sat_of_cliExternsPlaced cliWriteFileHook_ok_placed cliWriteStdoutHook_ok_placed compress256SingleSpec durationSinceBoundedSpec durationSinceEpochAllocSpec lsCompress512SymCli lsCompressSymCli lsDsmbSymCli lsEdNegSymCli lsKemDecapsSymCli lsKemEncapsSymCli lsMlkemDecapsSymCli lsMlkemEncaps1SymCli lsMlkemEncaps2SymCli lsMlkemFromSeedSymCli lsMlkemPk1SymCli lsMlkemPk2SymCli lsMlkemValidatePkSymCli lsScalarModSymCli lsScalarWideSymCli lsToEdwardsSymCli lsTorsionFreeSymCli)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.E2E (PEParams PqxdhPrims UnreachedPqxdhPrimitives modelPrims u8Vec vecU8)
open CryptoVerification.E2E.Pqxdh.Shared
  (compressInPlaceStubSpecPlaced cryptoLeafStubSpec sha512CompressOutBytes)
open CryptoVerification.LibsignalSpqrV1
  (MlKem mlkemEncaps2Spec mlkemPk1Spec mlkemPk2Spec mlkemValidatePkSpec)
open CryptoVerification.SignalSession.CliExt (dhSpec pureByteFunctionSpec)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (durationSinceEpochBudgetSpec hookSat_withVmPreserved timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
  (kemDecapsAtSpec kemEncapsAtSpec kemEncapsPreservedAtSpec mlkemDecapsAtSpec
   mlkemEncaps1AtSpec mlkemEncaps2AtSpec mlkemFromSeedAtSpec mlkemValidatePkAtSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
  (kyber1024DecapsVec kyber1024EncapsVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768Incremental)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512 (compress512StackedMasterSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
  (x25519PubFromSecretRef x25519Ref)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (dalekHookStack)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202
  (dalekMontToEdExtSpec dalekTorsionFreeExtSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204
  (dalekCompressExtSpec dalekDsmbExtSpec dalekEdNegExtSpec dalekScalarModExtSpec
   dalekScalarWideExtSpec edwardsPointNegUnstackedSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget (Stage2ContractsMinPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode (masterEdNegSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy hookMemcpy_exact)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
  (hookOk_withVmPreserved hookOk_rustAllocWithStack hookOk_rustDeallocExternWithStack
   hookOk_rustReallocExternWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraListSpecOk ExtraSpecOk GhostRowSpecOk hookSat_cliGhostExterns_of_extraOk
   hookSat_cliGhostExterns_of_extra_lookup)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack mlkemEncaps1TightStack
   mlkemEncaps2TightStack mlkemFromSeedTightStack mlkemHookStack mlkemValidatePkTightStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts
  (pureExtraGhosts pureExtraGhosts_lookup_writeFile pureExtraGhosts_lookup_writeStdout
   pureExtraGhosts_specOk)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (OnceCallHookOk spqrOnceCallGhostSpec spqrOnceCallSym)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesStackBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec
   sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack rustReallocExternSpecWithStack)

private theorem retHook_vm {f : State → State} {s : State} (h : VmPreserved s (f s)) :
    VmPreserved s (retHook f s) := h

private theorem setMem_vm (s : State) {m : Memory} (hp : ∀ a : BitVec 64, m.perm a = s.mem.perm a) :
    VmPreserved s (s.setMem m) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => by cases s; rfl⟩

private theorem writeBytes_perm_eq (m : Memory) (p : BitVec 64) (bs : List (BitVec 8))
    (a : BitVec 64) : (m.writeBytes p bs).perm a = m.perm a :=
  congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm m p bs) a

private theorem hookNoop_vm (s : State) : VmPreserved s (hookNoop s) :=
  LibsignalBinary.Heap.VmPreserved.refl s

private theorem hookMemset_vm (s : State) : VmPreserved s (hookMemset s) :=
  retHook_vm (setMem_vm s (writeBytes_perm_eq _ _ _))

private theorem hookMemcpy_vm (s : State) : VmPreserved s (hookMemcpy s) :=
  retHook_vm (setMem_vm s (writeBytes_perm_eq _ _ _))

private theorem writeStdoutHook_vm (s : State) : VmPreserved s (writeStdoutHook s) := by
  unfold writeStdoutHook; try dsimp only
  split <;> exact LibsignalBinary.Heap.VmPreserved.refl s

private theorem writeFileHook_vm (s : State) : VmPreserved s (writeFileHook s) :=
  LibsignalBinary.Heap.SpecBudget.vmPreserved_writeFileHook s

private theorem compress256Hook_vm (W : CliHooks) (s : State) :
    VmPreserved s (CryptoVerification.LibsignalHmac.compress256Hook W.C.F s) := by
  unfold CryptoVerification.LibsignalHmac.compress256Hook CryptoVerification.LibsignalAesCbc.returnToLinkRegister
  exact setMem_vm s (writeBytes_perm_eq _ _ _)

/-! ## 2. Budget and `VmPreserved` `HookSat` for non-allocating symbols -/

theorem cliExternsPlaced_shim_budget_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
      sessionShimBudgetSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim),
    hookOk_withVmPreserved sessionShim_hookOk hookNoop_vm⟩

theorem cliExternsPlaced_noAllocShim_budget_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
      (withVmPreserved noAllocShimSpec) :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim),
    hookOk_withVmPreserved noAllocShim_hookOk hookNoop_vm⟩

theorem cliGhostExterns_sessionMemmove_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "memmove"
      (LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.sessionMemmoveBoundedBudgetSpec stk) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.sessionMemmove_budget_ok stk

theorem cliGhostExterns_bcmp_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp" (withVmPreserved cliBcmpSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.bcmp_budget_ok

theorem cliGhostExterns_bcmp_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp" (withVmPreserved cliBcmpSpec).keepsFs :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    (hRow.bcmp_budget_ok).keepsFs hRow.fs_eq

theorem cliGhostExterns_bcmpVregs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp"
      (withVmPreserved CryptoVerification.E2E.HooksE.bcmpVregsSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.bcmpVregs_budget_ok

theorem cliGhostExterns_e2eBcmp_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp"
      (withVmPreserved CryptoVerification.E2E.HooksE.e2eBcmpSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow x R s0 hrun hpre hsp => by
    obtain ⟨hkf, hst, hout⟩ := hRow.bcmpVregs_budget_ok x R s0 hrun hpre hsp
    refine ⟨hkf, hst, ?_⟩
    rcases hout with ⟨hret, habi, hpost⟩ | hrest
    · refine Or.inl ⟨hret, habi, ?_⟩
      dsimp only [withVmPreserved, CryptoVerification.E2E.HooksE.bcmpVregsSpec,
        CryptoVerification.E2E.HooksE.e2eBcmpSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, ⟨hpost.2.1.1, hpost.2.1.2.2⟩, hpost.2.2⟩
    · exact Or.inr hrest

theorem cliGhostExterns_strlen_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "strlen"
      (withVmPreserved
        (LibsignalBinary.Proofs.HookDischarge.Libc.Strlen.withStrlenPadRO
          (strlenSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.strlen_budget_ok stk

theorem cliGhostExterns_strlenRO_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "strlen"
      (withVmPreserved
        (LibsignalBinary.Proofs.HookDischarge.Libc.Strlen.withStrlenPadRO
          (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.strlenSpecRO stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.strlenRO_budget_ok stk

theorem cliGhostExterns_memrchr_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsMemrchrSym
      (withLsRet (withVmPreserved (memrchrSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.memrchr_budget_ok hstk hstk_ub

theorem cliGhostExterns_memrchrRO_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsMemrchrSym
      (withLsRet (withVmPreserved
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.memrchrSpecRO stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.memrchrRO_budget_ok hstk hstk_ub

theorem cliGhostExterns_fromUtf8_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) lsFromUtf8Sym
      (withVmPreserved (fromUtf8AsciiSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.fromUtf8_budget_ok stk

theorem cliGhostExterns_fromUtf8RO_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) lsFromUtf8Sym
      (withVmPreserved
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.fromUtf8AsciiSpecRO stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.fromUtf8RO_budget_ok stk

theorem cliWriteFileHook_vm_ok_placed (stk : Nat) :
    HookOk writeFileHook
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk)) :=
  hookOk_withVmPreserved (cliWriteFileHook_ok_placed stk) writeFileHook_vm

theorem cliWriteStdoutHook_vm_ok_placed (stk : Nat) :
    HookOk writeStdoutHook
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk)) :=
  hookOk_withVmPreserved (cliWriteStdoutHook_ok_placed stk) writeStdoutHook_vm

theorem cliGhostExterns_writeFile_vm_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} (stk : Nat)
    (hf : g.extra.lookup lsWriteFileSym = some f)
    (hok : HookOk f
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk))) :
    HookSat (cliGhostExterns g baseExt) lsWriteFileSym
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk)) :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_writeFile_hook_vm_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (stk : Nat) (hf : g.extra.lookup lsWriteFileSym = some writeFileHook) :
    HookSat (cliGhostExterns g baseExt) lsWriteFileSym
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk)) :=
  cliGhostExterns_writeFile_vm_sat g baseExt stk hf (cliWriteFileHook_vm_ok_placed stk)

theorem cliGhostExterns_writeStdout_vm_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} (stk : Nat)
    (hf : g.extra.lookup lsWriteStdoutSym = some f)
    (hok : HookOk f
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk))) :
    HookSat (cliGhostExterns g baseExt) lsWriteStdoutSym
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk)) :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_writeStdout_hook_vm_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (stk : Nat) (hf : g.extra.lookup lsWriteStdoutSym = some writeStdoutHook) :
    HookSat (cliGhostExterns g baseExt) lsWriteStdoutSym
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk)) :=
  cliGhostExterns_writeStdout_vm_sat g baseExt stk hf (cliWriteStdoutHook_vm_ok_placed stk)

theorem cliWriteFileHook_budget_ok_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeFileHook
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced
        cliIo A lim stk) := by
  have hok := cliWriteFileHook_ok_placed stk
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  have hvm : VmPreserved s0 (writeFileHook s0) := writeFileHook_vm s0
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hok x (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (writeFileHook s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (writeFileHook s0) hvm
    have hrest' : (writeFileHook s0).mem ⊨
        ((x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono (sepConj_mono_left
      (Entails.sepExists_right ([] : List LibsignalBinary.Heap.AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨LibsignalBinary.Heap.SpecBudget.writeFileEnv_nil x.path.length, hres⟩
      (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem cliWriteStdoutHook_budget_ok_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeStdoutHook
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced
        A lim stk) := by
  have hok := cliWriteStdoutHook_ok_placed stk
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  have hvm : VmPreserved s0 (writeStdoutHook s0) := writeStdoutHook_vm s0
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hok x (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (writeStdoutHook s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (writeStdoutHook s0) hvm
    have hrest' : (writeStdoutHook s0).mem ⊨
        ((x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono (sepConj_mono_left
      (Entails.sepExists_right ([] : List LibsignalBinary.Heap.AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨LibsignalBinary.Heap.SpecBudget.writeStdoutEnv_nil, hres⟩
      (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem cliGhostExterns_writeFile_budget_sat {α : Type} (g : CliGhostHooks)
    (baseExt : LibsignalHooks) {f : State → State} {spec : Spec α}
    (hf : g.extra.lookup lsWriteFileSym = some f)
    (hok : HookOk f spec) :
    HookSat (cliGhostExterns g baseExt) lsWriteFileSym spec :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_writeFile_hook_budget_sat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks) (stk : Nat)
    (hf : g.extra.lookup lsWriteFileSym = some writeFileHook) :
    HookSat (cliGhostExterns g baseExt) lsWriteFileSym
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced
        cliIo A lim stk) :=
  cliGhostExterns_writeFile_budget_sat g baseExt hf (cliWriteFileHook_budget_ok_placed A lim stk)

theorem cliGhostExterns_writeStdout_budget_sat {α : Type} (g : CliGhostHooks)
    (baseExt : LibsignalHooks) {f : State → State} {spec : Spec α}
    (hf : g.extra.lookup lsWriteStdoutSym = some f)
    (hok : HookOk f spec) :
    HookSat (cliGhostExterns g baseExt) lsWriteStdoutSym spec :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_writeStdout_hook_budget_sat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks) (stk : Nat)
    (hf : g.extra.lookup lsWriteStdoutSym = some writeStdoutHook) :
    HookSat (cliGhostExterns g baseExt) lsWriteStdoutSym
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced
        A lim stk) :=
  cliGhostExterns_writeStdout_budget_sat g baseExt hf
    (cliWriteStdoutHook_budget_ok_placed A lim stk)

theorem cliGhostExterns_fmtWrite_budget_sat {α : Type} (g : CliGhostHooks)
    (baseExt : LibsignalHooks) {f : State → State} {spec : Spec α}
    (hf : g.extra.lookup lsFmtWriteSym = some f)
    (hok : HookOk f spec) :
    HookSat (cliGhostExterns g baseExt) lsFmtWriteSym spec :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_formatInner_budget_sat {α : Type} (g : CliGhostHooks)
    (baseExt : LibsignalHooks) {f : State → State} {spec : Spec α}
    (hf : g.extra.lookup lsFormatInnerSym = some f)
    (hok : HookOk f spec) :
    HookSat (cliGhostExterns g baseExt) lsFormatInnerSym spec :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_durationSinceEpoch_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet durationSinceEpochBudgetSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.durationSinceEpoch_budget_ok

theorem cliGhostExterns_durationSinceEpochAlloc_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet (withVmPreserved durationSinceEpochAllocSpec)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.durationSinceEpochAlloc_budget_ok

theorem cliGhostExterns_durationSinceBounded_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet (withVmPreserved durationSinceBoundedSpec)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.durationSinceBounded_budget_ok

theorem cliGhostExterns_timeAdd_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsTimeAddSym
      (withLsRet timeAddBudgetSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.timeAdd_budget_ok

theorem cliGhostExterns_blackBox_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsBlackBoxSym
      (withVmPreserved
        (CryptoVerification.LibsignalTripleRatchet.withStack
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.findReceiverBlackBox_budget_ok hstk hstk_ub

theorem cliGhostExterns_blackBoxSat_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsBlackBoxSym
      LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat.blackBoxSpecSat :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.blackBox_budget_ok (by decide : 16 ≤ 16) (by decide)

theorem cliGhostExterns_compress256_roBudget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {stk : Nat} (hstk : 176 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) CryptoVerification.SignalSession.lsCompress256Sym
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
        (LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionCompress256ROBudgetSpec
          CryptoVerification.LibsignalSpqrV1.sha256Compress stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress256_roBudget_ok hstk

theorem cliGhostExterns_compress256Multi_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {stk : Nat} (hstk : 176 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) CryptoVerification.SignalSession.lsCompress256Sym
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
        (withVmPreserved
          (CryptoVerification.LibsignalTripleRatchet.withStack
            (CryptoVerification.LibsignalTripleRatchet.compress256Spec
              CryptoVerification.LibsignalSpqrV1.sha256Compress) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress256_multi_budget_ok hstk

theorem cliGhostExterns_compress256_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {stk : Nat} (hstk : 176 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) CryptoVerification.SignalSession.lsCompress256Sym
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
        (withVmPreserved
          (CryptoVerification.LibsignalTripleRatchet.withStack
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress256RowSpec.compress256RowSingleSpec
              CryptoVerification.LibsignalSpqrV1.sha256Compress) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress256_single_budget_ok hstk

theorem cliGhostExterns_pubFromSecretWithStack_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.withStack
        (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretWithStack_budget_ok stk hlo hhi

theorem cliGhostExterns_pubFromSecretWithStack_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved (keepsFs
        (CryptoVerification.SignalSession.CliExt.withStack
          (pubFromSecretSpec x25519PubFromSecretRef) stk)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretWithStack_keepsFs_budget_ok stk hlo hhi

theorem cliGhostExterns_pubFromSecretWithStack_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.withStack
        (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretWithStack_ls_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_pubFromSecretWithStack_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
        (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretWithStack_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_pubFromSecret_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecret_budget_ok hC

theorem cliGhostExterns_pubFromSecret_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved
        (keepsFs (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecret_keepsFs_budget_ok hC

theorem cliGhostExterns_pubFromSecret_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecret_ls_withAlloc_ok A lim hC

theorem cliGhostExterns_pubFromSecret_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecret_withAlloc_ok A lim hC

theorem cliGhostExterns_pubFromSecretPureByte_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (byVal : Bool := false) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretPureByte_budget_ok byVal

theorem cliGhostExterns_pubFromSecretPureByte_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (byVal : Bool := false) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved (keepsFs (pureByteFunctionSpec x25519PubFromSecretRef byVal)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretPureByte_keepsFs_budget_ok byVal

theorem cliGhostExterns_pubFromSecretPureByte_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (byVal : Bool := false) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withAlloc A lim (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretPureByte_ls_withAlloc_ok A lim byVal

theorem cliGhostExterns_pubFromSecretPureByte_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (byVal : Bool := false) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withAlloc A lim (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretPureByte_withAlloc_ok A lim byVal

theorem cliGhostExterns_derivePublicKeyBytesStack_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStack_budget_ok stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStack_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved
        (keepsFs (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStack_keepsFs_budget_ok stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStack_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withAlloc A lim (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStack_ls_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStack_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withAlloc A lim (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStack_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStackBudget_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStackBudget_budget_ok stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStackBudget_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withVmPreserved
        (keepsFs (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStackBudget_keepsFs_budget_ok stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStackBudget_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (withAlloc A lim (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStackBudget_ls_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStackBudget_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withAlloc A lim (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStackBudget_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_diffieHellmanWithStack_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.withStack
        (diffieHellmanSpec x25519Ref) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellmanWithStack_budget_ok stk hlo hhi

theorem cliGhostExterns_diffieHellmanWithStack_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withLsRet (withVmPreserved (keepsFs
        (CryptoVerification.SignalSession.CliExt.withStack (diffieHellmanSpec x25519Ref) stk)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellmanWithStack_keepsFs_budget_ok stk hlo hhi

theorem cliGhostExterns_diffieHellmanWithStack_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.withStack
        (diffieHellmanSpec x25519Ref) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellmanWithStack_ls_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_diffieHellmanWithStack_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
        (diffieHellmanSpec x25519Ref) stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellmanWithStack_withAlloc_ok A lim stk hlo hhi

theorem cliGhostExterns_diffieHellman_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withLsRet (withVmPreserved (dhSpec C))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellman_budget_ok hC

theorem cliGhostExterns_diffieHellman_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withLsRet (withVmPreserved (keepsFs (dhSpec C)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellman_keepsFs_budget_ok hC

theorem cliGhostExterns_diffieHellman_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withLsRet (withAlloc A lim (dhSpec C))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellman_ls_withAlloc_ok A lim hC

theorem cliGhostExterns_diffieHellman_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withAlloc A lim (withLsRet (dhSpec C))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellman_withAlloc_ok A lim hC

theorem cliGhostExterns_staticSecretDrop_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) CryptoVerification.SignalSession.lsStaticSecretDropSym
      (withVmPreserved zeroizeSecretSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.staticSecretDrop_budget_ok

theorem cliGhostExterns_sharedSecretDrop_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) CryptoVerification.SignalSession.lsSharedSecretDropSym
      (withVmPreserved zeroizeSecretSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.sharedSecretDrop_budget_ok

theorem cliGhostExterns_toEdwards_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsToEdwardsSymCli
      (withLsRet (withVmPreserved (dalekMontToEdExtSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.toEdwards_budget_ok stk hlo hhi

theorem cliGhostExterns_compress_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompressSymCli
      (withLsRet (withVmPreserved (dalekCompressExtSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress_budget_ok stk hlo hhi

theorem cliGhostExterns_edNegMaster_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli
      (withVmPreserved masterEdNegSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_master_budget_ok

theorem cliGhostExterns_edNegUnstacked_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (byVal : Bool := false) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli
      (withVmPreserved (edwardsPointNegUnstackedSpec byVal)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_unstacked_budget_ok byVal

theorem cliGhostExterns_edNeg_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli
      (withVmPreserved
        (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_cryptoLeafStub_budget_ok

theorem cliGhostExterns_edNegExt_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli
      (withLsRet (withVmPreserved (dalekEdNegExtSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_ext_budget_ok stk

theorem cliGhostExterns_torsionFree_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsTorsionFreeSymCli
      (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.torsionFree_budget_ok stk hlo hhi

theorem cliGhostExterns_dsmb_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDsmbSymCli
      (withLsRet (withVmPreserved (dalekDsmbExtSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.dsmb_budget_ok stk hlo hhi

theorem cliGhostExterns_scalarMod_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsScalarModSymCli
      (withLsRet (withVmPreserved (dalekScalarModExtSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.scalarMod_budget_ok stk hlo hhi

theorem cliGhostExterns_scalarWide_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsScalarWideSymCli
      (withLsRet (withVmPreserved (dalekScalarWideExtSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.scalarWide_budget_ok stk hlo hhi

theorem cliGhostExterns_mlkemPk1_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk1SymCli
      (withVmPreserved mlkemPk1Spec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk1_budget_ok

theorem cliGhostExterns_mlkemPk1Ls_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk1SymCli
      (withLsRet (withVmPreserved mlkemPk1Spec)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk1_ls_budget_ok

theorem cliGhostExterns_mlkemPk2_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk2SymCli
      (withVmPreserved mlkemPk2Spec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk2_budget_ok

theorem cliGhostExterns_mlkemPk2Ls_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk2SymCli
      (withLsRet (withVmPreserved mlkemPk2Spec)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk2_ls_budget_ok

theorem cliGhostExterns_compress512_stackedMaster_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {stk : Nat} (hstk : 256 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (withVmPreserved (compress512StackedMasterSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_stackedMaster_budget_ok hstk

theorem cliGhostExterns_compress512_stackedMaster_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {stk : Nat} (hstk : 256 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (withAlloc A lim (compress512StackedMasterSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_stackedMaster_ls_withAlloc_ok A lim hstk

theorem cliGhostExterns_compress512_stackedMaster_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {stk : Nat} (hstk : 256 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withAlloc A lim (withLsRet (compress512StackedMasterSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_stackedMaster_withAlloc_ok A lim hstk

theorem cliGhostExterns_compress512_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_budget_ok hF

theorem cliGhostExterns_compress512_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_ls_withAlloc_ok A lim hF

theorem cliGhostExterns_compress512_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_withAlloc_ok A lim hF

theorem cliGhostExterns_compress512_pqxdhStubPlaced_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (withVmPreserved (compressInPlaceStubSpecPlaced
        (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_pqxdhStubPlaced_budget_ok X hF

theorem cliGhostExterns_compress512_pqxdhStubPlaced_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (withAlloc A lim (compressInPlaceStubSpecPlaced
        (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_pqxdhStubPlaced_ls_withAlloc_ok A lim X hF

theorem cliGhostExterns_compress512_pqxdhStubPlaced_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withAlloc A lim (withLsRet (compressInPlaceStubSpecPlaced
        (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_pqxdhStubPlaced_withAlloc_ok A lim X hF

theorem cliGhostExterns_kemEncapsPreserved_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (withVmPreserved (kemEncapsPreservedAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncapsPreserved_budget_ok stk hlo hhi hQ

theorem cliGhostExterns_kemEncapsPreserved_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (withVmPreserved (keepsFs (kemEncapsPreservedAtSpec stk Q)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncapsPreserved_keepsFs_budget_ok stk hlo hhi hQ

theorem cliGhostExterns_kemEncapsPreserved_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withAlloc A lim (withLsRet (kemEncapsPreservedAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncapsPreserved_withAlloc_ok A lim stk hlo hhi hQ

theorem cliGhostExterns_kemEncapsPreserved_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (withAlloc A lim (kemEncapsPreservedAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncapsPreserved_ls_withAlloc_ok A lim stk hlo hhi hQ

theorem cliGhostExterns_kemEncaps_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (withVmPreserved (kemEncapsAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncaps_budget_ok stk hlo hhi hQ

theorem cliGhostExterns_kemEncaps_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (withVmPreserved (keepsFs (kemEncapsAtSpec stk Q)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncaps_keepsFs_budget_ok stk hlo hhi hQ

theorem cliGhostExterns_kemEncaps_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withAlloc A lim (withLsRet (kemEncapsAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncaps_withAlloc_ok A lim stk hlo hhi hQ

theorem cliGhostExterns_kemEncaps_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (withAlloc A lim (kemEncapsAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncaps_ls_withAlloc_ok A lim stk hlo hhi hQ

theorem cliGhostExterns_kemDecaps_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemDecapsSymCli
      (withLsRet (withVmPreserved (kemDecapsAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemDecaps_budget_ok stk hlo hhi hQ

theorem cliGhostExterns_kemDecaps_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemDecapsSymCli
      (withLsRet (withVmPreserved (keepsFs (kemDecapsAtSpec stk Q)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemDecaps_keepsFs_budget_ok stk hlo hhi hQ

theorem cliGhostExterns_kemDecaps_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemDecapsSymCli
      (withAlloc A lim (withLsRet (kemDecapsAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemDecaps_withAlloc_ok A lim stk hlo hhi hQ

theorem cliGhostExterns_kemDecaps_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemDecapsSymCli
      (withLsRet (withAlloc A lim (kemDecapsAtSpec stk Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemDecaps_ls_withAlloc_ok A lim stk hlo hhi hQ

theorem cliGhostExterns_mlkemFromSeed_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemFromSeedSymCli
      (withLsRet (withVmPreserved (mlkemFromSeedAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemFromSeed_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemFromSeed_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemFromSeedSymCli
      (withLsRet (withVmPreserved (keepsFs (mlkemFromSeedAtSpec stk K)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemFromSeed_keepsFs_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemFromSeed_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemFromSeedSymCli
      (withAlloc A lim (withLsRet (mlkemFromSeedAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemFromSeed_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemFromSeed_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemFromSeedSymCli
      (withLsRet (withAlloc A lim (mlkemFromSeedAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemFromSeed_ls_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps1_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps1SymCli
      (withLsRet (withVmPreserved (mlkemEncaps1AtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps1_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps1_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps1SymCli
      (withLsRet (withVmPreserved (keepsFs (mlkemEncaps1AtSpec stk K)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps1_keepsFs_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps1_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps1SymCli
      (withAlloc A lim (withLsRet (mlkemEncaps1AtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps1_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps1_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps1SymCli
      (withLsRet (withAlloc A lim (mlkemEncaps1AtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps1_ls_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps2_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (withVmPreserved (mlkemEncaps2Spec K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2_budget_ok hK

theorem cliGhostExterns_mlkemEncaps2_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (withVmPreserved (keepsFs (mlkemEncaps2Spec K)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2_keepsFs_budget_ok hK

theorem cliGhostExterns_mlkemEncaps2_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withAlloc A lim (withLsRet (mlkemEncaps2Spec K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2_withAlloc_ok A lim hK

theorem cliGhostExterns_mlkemEncaps2_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (withAlloc A lim (mlkemEncaps2Spec K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2_ls_withAlloc_ok A lim hK

theorem cliGhostExterns_mlkemEncaps2At_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (withVmPreserved (mlkemEncaps2AtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2At_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps2At_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (withVmPreserved (keepsFs (mlkemEncaps2AtSpec stk K)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2At_keepsFs_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps2At_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withAlloc A lim (withLsRet (mlkemEncaps2AtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2At_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps2At_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (withAlloc A lim (mlkemEncaps2AtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2At_ls_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemDecapsAt_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemDecapsSymCli
      (withLsRet (withVmPreserved (mlkemDecapsAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemDecapsAt_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemDecapsAt_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemDecapsSymCli
      (withLsRet (withVmPreserved (keepsFs (mlkemDecapsAtSpec stk K)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemDecapsAt_keepsFs_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemDecapsAt_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemDecapsSymCli
      (withAlloc A lim (withLsRet (mlkemDecapsAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemDecapsAt_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemDecapsAt_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemDecapsSymCli
      (withLsRet (withAlloc A lim (mlkemDecapsAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemDecapsAt_ls_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemValidatePk_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (withVmPreserved (mlkemValidatePkSpec K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePk_budget_ok hK

theorem cliGhostExterns_mlkemValidatePk_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (withVmPreserved (keepsFs (mlkemValidatePkSpec K)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePk_keepsFs_budget_ok hK

theorem cliGhostExterns_mlkemValidatePk_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withAlloc A lim (withLsRet (mlkemValidatePkSpec K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePk_withAlloc_ok A lim hK

theorem cliGhostExterns_mlkemValidatePk_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (withAlloc A lim (mlkemValidatePkSpec K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePk_ls_withAlloc_ok A lim hK

theorem cliGhostExterns_mlkemValidatePkAt_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (withVmPreserved (mlkemValidatePkAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePkAt_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemValidatePkAt_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (withVmPreserved (keepsFs (mlkemValidatePkAtSpec stk K)))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePkAt_keepsFs_budget_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemValidatePkAt_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withAlloc A lim (withLsRet (mlkemValidatePkAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePkAt_withAlloc_ok A lim stk hlo hhi hK

theorem cliGhostExterns_mlkemValidatePkAt_ls_withAlloc_sat [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (withAlloc A lim (mlkemValidatePkAtSpec stk K))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePkAt_ls_withAlloc_ok A lim stk hlo hhi hK

/-! ## 3. `HookOk` helpers and `CliGhostAllocHooks` -/

private theorem allocHookStack_le_extHookStack : allocHookStack ≤ extHookStack := by decide

private theorem hook_placed_rocl_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalHookedExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain (ls_hook_ok_ultra_of_mem hsat hmem)

private theorem hookSat_withStack_of_hookSat {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hsat : HookSat H sym spec) (stk : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookSat H sym (withStack spec stk) := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_withStack hok stk hpan hex hoom⟩

private theorem hookSat_keepsFs_of_hookSat {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hsat : HookSat H sym spec)
    (hfs : ∀ f, H sym = some f → ∀ s : State, (f s).fs = s.fs) :
    HookSat H sym spec.keepsFs := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hok.keepsFs (hfs f hf)⟩

/-- Witnesses that `E2E.allocHook0`, `E2E.deallocHook`, and `E2E.reallocHook0` satisfy
`rustCli{Alloc,Dealloc,Realloc}BudgetSpec M A lim`. -/
structure CliAllocHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Prop where
  alloc : HookOk CryptoVerification.E2E.allocHook0 (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookOk CryptoVerification.E2E.deallocHook (rustCliDeallocBudgetSpec M A lim)
  realloc : HookOk CryptoVerification.E2E.reallocHook0 (rustCliReallocBudgetSpec M A lim)

/-- Witnesses that `g.alloc`, `g.dealloc`, and `g.realloc` satisfy
`rustCli{Alloc,Dealloc,Realloc}BudgetSpec`, preserve `State.fs`, and satisfy `HookFsTraced IsFsC`,
and that `g.memset`, `g.memcpy`, and `g.extra` satisfy the budget-threaded consumer specs
(`VmPreserved`, `State.fs` preservation, and `HookFsTraced IsFsC`). -/
structure CliGhostAllocHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) : Prop where
  alloc : HookOk g.alloc (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookOk g.dealloc (rustCliDeallocBudgetSpec M A lim)
  realloc : HookOk g.realloc (rustCliReallocBudgetSpec M A lim)
  alloc_fs : ∀ s : State, (g.alloc s).fs = s.fs
  dealloc_fs : ∀ s : State, (g.dealloc s).fs = s.fs
  realloc_fs : ∀ s : State, (g.realloc s).fs = s.fs
  alloc_fsT : HookFsTraced IsFsC g.alloc
  dealloc_fsT : HookFsTraced IsFsC g.dealloc
  realloc_fsT : HookFsTraced IsFsC g.realloc
  shim_eq : g.shim = hookNoop := by rfl
  memset : ∃ f, g.memset = some f ∧
    (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
    HookOk f memsetRegionSpec ∧
    HookOk f sessionMemsetRegionSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy : ∃ f, g.memcpy = some f ∧
    (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
    HookOk f memcpyRegionSpec ∧
    HookOk f sessionMemcpyRegionSpec ∧
    HookOk f framelessMemcpySpec ∧
    HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy_exact : ∀ f, g.memcpy = some f → HookExactMemcpy f
  memset_acp : ∀ f, g.memset = some f →
    ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle
  extraOk : ExtraSpecOk g

/-- Extends `CliGhostAllocHooks` with `g.allocZeroed` (`rustCliAllocBudgetSpec M A lim true`),
`HookFsTraced IsFsC g.allocZeroed`, and the `spqrOnceCallSym` extra-ghost row + address uniqueness. -/
structure CliGhostSpqrAllocHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) : Prop extends CliGhostAllocHooks M A lim g where
  allocZeroed : HookOk g.allocZeroed (rustCliAllocBudgetSpec M A lim true)
  allocZeroed_fs : ∀ s : State, (g.allocZeroed s).fs = s.fs
  allocZeroed_fsT : HookFsTraced IsFsC g.allocZeroed
  onceCall : ∃ f, g.extra.lookup lsSpqrOnceCallSym = some f ∧ HookOk f spqrOnceCallGhostSpec
  onceCall_unique :
    ∀ e ∈ libsignalSessionExterns, lsρ e = lsρ spqrOnceCallSym → e = spqrOnceCallSym

theorem CliGhostSpqrAllocHooks.onceCall_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostSpqrAllocHooks M A lim g) (baseExt : LibsignalHooks) :
    HookSat (cliGhostExterns g baseExt) spqrOnceCallSym spqrOnceCallGhostSpec := by
  obtain ⟨f, hlook, hok⟩ := hG.onceCall
  exact ⟨f, CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_extra_some g baseExt hlook,
    hok⟩

theorem CliGhostSpqrAllocHooks.onceCallHookOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostSpqrAllocHooks M A lim g) (baseExt : LibsignalHooks) :
    OnceCallHookOk (cliGhostExterns g baseExt) :=
  ⟨hG.onceCall_sat baseExt, hG.onceCall_unique⟩

theorem CliGhostSpqrAllocHooks.onceCallHookOk_withPanics [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    OnceCallHookOk (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
  rw [CryptoVerification.SignalSession.Cli.RunGlue.withPanics_cliGhostExterns mmpl g W]
  exact hG.onceCallHookOk (cliExternsPlaced mmpl W)

theorem CliGhostSpqrAllocHooks.onceCallHookOk_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns g (cliExternsPlaced mmpl W) sym) :
    OnceCallHookOk (Rust.withPanics ext) := by
  refine ⟨?_, hG.onceCall_unique⟩
  have heq : Rust.withPanics ext spqrOnceCallSym =
      cliGhostExterns g (cliExternsPlaced mmpl W) spqrOnceCallSym := by
    have hnp : Rust.isPanicSymbol spqrOnceCallSym = false := by
      simp [Rust.isPanicSymbol, spqrOnceCallSym]
    simp only [Rust.withPanics, hnp, Bool.false_eq_true, ↓reduceIte]
    exact hExt spqrOnceCallSym (by decide)
  exact hookSat_of_eq heq (hG.onceCall_sat (cliExternsPlaced mmpl W))

/-- Bump-allocator instantiation of `CliGhostHooks` (`allocHook0`, `deallocHook`, `reallocHook0`, `allocZeroedHook0`; no replay obligation). -/
@[expose] noncomputable def bumpGhost : CliGhostHooks where
  alloc := CryptoVerification.E2E.allocHook0
  dealloc := CryptoVerification.E2E.deallocHook
  realloc := CryptoVerification.E2E.reallocHook0
  allocZeroed := CryptoVerification.E2E.allocZeroedHook0
  shim := hookNoop
  stringClone := none
  memset := some hookMemset
  memcpy := some hookMemcpy
  extra := pureExtraGhosts

theorem cliGhostAllocHooks_bumpGhost [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hA : CliAllocHooks M A lim) :
    CliGhostAllocHooks M A lim bumpGhost where
  alloc := hA.alloc
  dealloc := hA.dealloc
  realloc := hA.realloc
  alloc_fs := allocHook0_fs
  dealloc_fs := deallocHook_fs
  realloc_fs := reallocHook0_fs
  alloc_fsT := allocHook0_fsT
  dealloc_fsT := deallocHook_fsT
  realloc_fsT := reallocHook0_fsT
  shim_eq := rfl
  memset := ⟨hookMemset, rfl, fun stk hpos => hookMemset_ok stk hpos,
    fun stk hpos => hookMemset_trace_ok stk hpos, hookMemset_region_ok,
    hookMemset_region_trace_ok, hookMemset_vm, hookMemset_fs, hookMemset_fsT⟩
  memcpy := ⟨hookMemcpy, rfl, fun stk => hookMemcpy_ok stk, fun stk => hookMemcpy_trace_ok stk,
    hookMemcpy_region_ok, hookMemcpy_region_trace_ok, framelessMemcpy_hookOk,
    CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok,
    hookMemcpy_vm, hookMemcpy_fs, hookMemcpy_fsT⟩
  memcpy_exact := fun f hf => by cases hf; exact hookMemcpy_exact
  memset_acp := fun f hf s => by cases hf; exact ⟨rfl, rfl⟩
  extraOk := pureExtraGhosts_specOk

theorem bumpGhost_writeFile_budget_sat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (baseExt : LibsignalHooks) (stk : Nat) :
    HookSat (cliGhostExterns bumpGhost baseExt) lsWriteFileSym
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced
        cliIo A lim stk) :=
  cliGhostExterns_writeFile_hook_budget_sat A lim bumpGhost baseExt stk pureExtraGhosts_lookup_writeFile

theorem bumpGhost_writeStdout_budget_sat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (baseExt : LibsignalHooks) (stk : Nat) :
    HookSat (cliGhostExterns bumpGhost baseExt) lsWriteStdoutSym
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced
        A lim stk) :=
  cliGhostExterns_writeStdout_hook_budget_sat A lim bumpGhost baseExt stk
    pureExtraGhosts_lookup_writeStdout

theorem cliGhostExterns_memset_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g baseExt) "memset" (withVmPreserved (libcMemsetSpec stk)) := by
  obtain ⟨f, hf, hok, _, _, _, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved (hok stk hpos) hvm⟩

theorem cliGhostExterns_sessionMemset_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g baseExt) "memset" (sessionMemsetBudgetSpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved (hok stk hpos) hvm⟩

theorem cliGhostExterns_memsetRegion_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memset" (withVmPreserved memsetRegionSpec) := by
  obtain ⟨f, hf, _, _, hok, _, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_sessionMemsetRegion_budget_sat [LibsignalPlacement]
    (baseExt : LibsignalHooks) {g : CliGhostHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memset" sessionMemsetRegionBudgetSpec := by
  obtain ⟨f, hf, _, _, _, hok, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_memcpy_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (withVmPreserved (libcMemcpySpec stk)) := by
  obtain ⟨f, hf, hok, _, _, _, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved (hok stk) hvm⟩

theorem cliGhostExterns_sessionMemcpy_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (sessionMemcpyBudgetSpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved (hok stk) hvm⟩

theorem cliGhostExterns_memcpyRegion_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (withVmPreserved memcpyRegionSpec) := by
  obtain ⟨f, hf, _, _, hok, _, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_sessionMemcpyRegion_budget_sat [LibsignalPlacement]
    (baseExt : LibsignalHooks) {g : CliGhostHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy" sessionMemcpyRegionBudgetSpec := by
  obtain ⟨f, hf, _, _, _, hok, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_framelessMemcpy_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (withVmPreserved framelessMemcpySpec) := by
  obtain ⟨f, hf, _, _, _, _, hok, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_memcpyRegionRO_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy"
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) := by
  obtain ⟨f, hf, _, _, _, _, _, hok, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliExternsPlaced_memset_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset"
      (withVmPreserved (libcMemsetSpec stk)) :=
  cliGhostExterns_memset_budget_sat (cliExternsPlaced mmpl W) hG stk hpos

theorem cliExternsPlaced_sessionMemset_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" (sessionMemsetBudgetSpec stk) :=
  cliGhostExterns_sessionMemset_budget_sat (cliExternsPlaced mmpl W) hG stk hpos

theorem cliExternsPlaced_memsetRegion_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset"
      (withVmPreserved memsetRegionSpec) :=
  cliGhostExterns_memsetRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_sessionMemsetRegion_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" sessionMemsetRegionBudgetSpec :=
  cliGhostExterns_sessionMemsetRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_memcpy_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved (libcMemcpySpec stk)) :=
  cliGhostExterns_memcpy_budget_sat (cliExternsPlaced mmpl W) hG stk

theorem cliExternsPlaced_sessionMemcpy_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" (sessionMemcpyBudgetSpec stk) :=
  cliGhostExterns_sessionMemcpy_budget_sat (cliExternsPlaced mmpl W) hG stk

theorem cliExternsPlaced_memcpyRegion_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved memcpyRegionSpec) :=
  cliGhostExterns_memcpyRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_sessionMemcpyRegion_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" sessionMemcpyRegionBudgetSpec :=
  cliGhostExterns_sessionMemcpyRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_framelessMemcpy_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved framelessMemcpySpec) :=
  cliGhostExterns_framelessMemcpy_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_memcpyRegionRO_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) :=
  cliGhostExterns_memcpyRegionRO_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliGhostExterns_exactMemcpy_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSatExactMemcpy (cliGhostExterns g baseExt) "memcpy" := by
  obtain ⟨f, hf, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hG.memcpy_exact f hf⟩

theorem cliExternsPlaced_exactMemcpy_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSatExactMemcpy (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" :=
  cliGhostExterns_exactMemcpy_sat (cliExternsPlaced mmpl W) hG

/-- `CliGhostAllocHooks` discharges `HkdfPlacedHooksExactSat sha256Compress` on
    `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks_sha256
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HkdfPlacedHooksExactSat CryptoVerification.LibsignalSpqrV1.sha256Compress
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { memset := by
      obtain ⟨f, hf, _, _, _, hok, _⟩ := hG.memset
      exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩
    memcpy := cliExternsPlaced_exactMemcpy_sat mmpl g W hG
    compress256 :=
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs.hookSatCompress256_cliGhostExterns_of_extraOk
        g (cliExternsPlaced mmpl W) hG.extraOk }

/-- `CliGhostAllocHooks` with `W.C.F = sha256Compress` discharges
    `HkdfPlacedHooksExactSat W.C.F` on `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  hF ▸ HkdfPlacedHooksExactSat.of_allocHooks_sha256 hG

/-- `Rust.withPanics` specialization of `HkdfPlacedHooksExactSat.of_allocHooks`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks_withPanics
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) :
    HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
  rw [CryptoVerification.SignalSession.Cli.RunGlue.withPanics_cliGhostExterns mmpl g W]
  exact HkdfPlacedHooksExactSat.of_allocHooks hG hF

/-- Variant-extern lift of `HkdfPlacedHooksExactSat.of_allocHooks` (covers any `H` agreeing with
    `cliGhostExterns g (cliExternsPlaced mmpl W)` outside RNG). -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks_ext
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) {H : LibsignalHooks}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns g (cliExternsPlaced mmpl W) sym) :
    HkdfPlacedHooksExactSat W.C.F H := by
  have hBase : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG hF
  refine { memset := ?_, memcpy := ?_, compress256 := ?_ }
  · obtain ⟨f, hf, hok⟩ := hBase.memset
    exact ⟨f, (hExt lsMemsetSym (by decide)).trans hf, hok⟩
  · obtain ⟨f, hf, hex⟩ := hBase.memcpy
    exact ⟨f, (hExt lsMemcpySym (by decide)).trans hf, hex⟩
  · exact LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.hookSatCompress256_of_sym_eq
      (hExt CryptoVerification.LibsignalTripleRatchet.lsCompress256Sym (by decide))
      hBase.compress256

/-- `HookExactMemcpy` implies `HookOk f ConcatBudgetAux.framelessMemcpyAcpSpec`
    (`AllocCallPreserved ∧ VmPreserved`, 0-stack). -/
theorem hookExactMemcpy_framelessMemcpyAcp_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f framelessMemcpyAcpSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [framelessMemcpyAcpSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : bs.length ≤ 2 ^ 64 := hx2 ▸ Nat.le_of_lt (s0.readReg64 .x2).isLt
  have hrw : s0.mem.RW dst bs.length := (IsBlock.memRegion dst bs.length).rw hmem
  have hsrc_front : s0.mem ⊨ (src ↦ₛ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hb := IsBlock.pointsToBytes src bs
  have hread : s0.mem.readBytes src bs.length = bs := (hb.read hsrc_front).2
  have hreadable : s0.mem.Readable src bs.length :=
    fun a ha => ⟨by rw [hb.perm_rw hsrc_front ha]; rfl, hb.isLazyFree_false hsrc_front ha⟩
  have hdisj : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length := by
    by_cases h0 : bs.length = 0
    · exact Or.inl h0
    · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
      exact Or.inr ((IsBlock.memRegion dst bs.length).disjoint hb hpos hpos hmem)
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hread hrw hreadable hdisj
  have hvm : VmPreserved s0 (f s0) := by
    rw [heq]
    exact LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.vmPreserved_applyMemcpyClobber_writeBytes
      s0 dst bs (s0.readReg64 .lr) c
  have hacp : LibsignalBinary.Heap.AllocCallPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkf : s0.mem.KeepsFrozen (f s0).mem := by
    rw [heq]; exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  have hsym : (f s0).symtab = s0.symtab := by rw [heq]; rfl
  have hret : Returned s0 (f s0) := by rw [heq]; exact ⟨rfl, rfl, hrun⟩
  have hcc : CallingConventionPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
  dsimp only [framelessMemcpyAcpSpec]
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  have hx0_ret : (f s0).readReg64 .x0 = dst := by rw [heq]; exact hx0
  refine ⟨⟨hx0_ret, hacp, hvm⟩, ?_⟩
  rw [heq]
  exact satisfies_writeBytes bs hlen hmem

theorem hookSat_framelessMemcpyAcp_of_exact {H : String → Option (State → State)} {name : String}
    (h : HookSatExactMemcpy H name) :
    HookSat H name framelessMemcpyAcpSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_framelessMemcpyAcp_ok hex⟩

theorem cliExternsPlaced_framelessMemcpyAcp_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" framelessMemcpyAcpSpec :=
  hookSat_framelessMemcpyAcp_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

/-- `HookExactMemcpy` implies `HookOk f ConcatBudgetAux.sessionMemcpyRegionROSpec`
    (read-only source `src ↦ᵣ bs`, `AllocCallPreserved ∧ VmPreserved`, 0-stack). -/
theorem hookExactMemcpy_sessionMemcpyRegionROAcp_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hrw : s0.mem.RW dst bs.length := (IsBlock.memRegion dst bs.length).rw hmem
  have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hb := IsBlockRO.pointsToBytesRO src bs hlen
  have hread : s0.mem.readBytes src bs.length = bs := hb.read hsrc_front
  have hreadable : s0.mem.Readable src bs.length :=
    fun a ha => ⟨hb.perm_r hsrc_front ha, hb.isLazyFree_false hsrc_front ha⟩
  have hdisj : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length := by
    by_cases h0 : bs.length = 0
    · exact Or.inl h0
    · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
      have hnd : ¬ InRegion dst bs.length src := fun h =>
        not_satisfies_ownsRO_ownsRW
          (ownsRO_pointsToBytesRO_at hlen (by simp [InRegion, hpos]))
          (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length src h))
          hsrc_front
      have hns : ¬ InRegion src bs.length dst := fun h =>
        not_satisfies_ownsRO_ownsRW
          (ownsRO_pointsToBytesRO_at hlen h)
          (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length dst (by simp [InRegion, hpos])))
          hsrc_front
      dsimp only [InRegion] at hnd hns
      exact Or.inr ⟨Nat.le_of_not_lt hnd, Nat.le_of_not_lt hns⟩
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hread hrw hreadable hdisj
  have hvm : VmPreserved s0 (f s0) := by
    rw [heq]
    exact LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.vmPreserved_applyMemcpyClobber_writeBytes
      s0 dst bs (s0.readReg64 .lr) c
  have hacp : LibsignalBinary.Heap.AllocCallPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkf : s0.mem.KeepsFrozen (f s0).mem := by
    rw [heq]; exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  have hsym : (f s0).symtab = s0.symtab := by rw [heq]; rfl
  have hret : Returned s0 (f s0) := by rw [heq]; exact ⟨rfl, rfl, hrun⟩
  have hcc : CallingConventionPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec]
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  have hx0_ret : (f s0).readReg64 .x0 = dst := by rw [heq]; exact hx0
  refine ⟨⟨hx0_ret, hacp, hvm⟩, ?_⟩
  rw [heq]
  exact satisfies_writeBytes bs hlen hmem

theorem hookSat_sessionMemcpyRegionROAcp_of_exact {H : String → Option (State → State)}
    {name : String} (h : HookSatExactMemcpy H name) :
    HookSat H name LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_sessionMemcpyRegionROAcp_ok hex⟩

theorem cliExternsPlaced_sessionMemcpyRegionROAcp_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec :=
  hookSat_sessionMemcpyRegionROAcp_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

/-- `HookExactMemcpy` implies `HookOk f RustStdAllocBudgetBridge.allocMemcpyVmSpec`
    (`AllocCallPreserved ∧ VmPreserved`). -/
theorem hookExactMemcpy_allocMemcpyVm_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨ framelessMemcpyAcpSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hookExactMemcpy_framelessMemcpyAcp_ok hf (dst, src, bs) R s0 hrun hpre' hsp with
    ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec,
      framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

theorem hookSat_allocMemcpyVm_of_exact {H : String → Option (State → State)} {name : String}
    (h : HookSatExactMemcpy H name) :
    HookSat H name LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_allocMemcpyVm_ok hex⟩

theorem cliExternsPlaced_allocMemcpyVm_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec :=
  hookSat_allocMemcpyVm_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

/-- `HookExactMemcpy` implies `HookOk f LibsignalBinary.Heap.allocMemcpyVmSpec`
    (`MallocngBridgeBudget.allocMemcpyVmSpec`, `AllocCallPreserved ∧ VmPreserved`). -/
theorem hookExactMemcpy_heapAllocMemcpyVm_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f LibsignalBinary.Heap.allocMemcpyVmSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨ framelessMemcpyAcpSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hookExactMemcpy_framelessMemcpyAcp_ok hf (dst, src, bs) R s0 hrun hpre' hsp with
    ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec, framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

theorem hookSat_heapAllocMemcpyVm_of_exact {H : String → Option (State → State)} {name : String}
    (h : HookSatExactMemcpy H name) :
    HookSat H name LibsignalBinary.Heap.allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_heapAllocMemcpyVm_ok hex⟩

theorem cliExternsPlaced_heapAllocMemcpyVm_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      LibsignalBinary.Heap.allocMemcpyVmSpec :=
  hookSat_heapAllocMemcpyVm_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

theorem cliExternsPlaced_alloc_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSymCli
      (rustCliAllocBudgetSpec M A lim false) :=
  ⟨g.alloc, cliGhostExterns_alloc g _, hG.alloc⟩

theorem cliExternsPlaced_dealloc_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSymCli
      (rustCliDeallocBudgetSpec M A lim) :=
  ⟨g.dealloc, cliGhostExterns_dealloc g _, hG.dealloc⟩

theorem cliExternsPlaced_realloc_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustReallocSymCli
      (rustCliReallocBudgetSpec M A lim) :=
  ⟨g.realloc, cliGhostExterns_realloc g _, hG.realloc⟩

/-! ## 4. `AllocContractsXCliPlaced` and `AllocContractsFsPlaced` -/

theorem allocContractsXCliPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsXCliPlaced A lim
      (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  alloc := hook_placed_rocl_ok
    ⟨g.alloc, cliGhostExterns_alloc g _,
      hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le⟩
  dealloc := hook_placed_rocl_ok
    ⟨g.dealloc, cliGhostExterns_dealloc g _,
      hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack extHookStack_le⟩
  realloc := hook_placed_rocl_ok
    ⟨g.realloc, cliGhostExterns_realloc g _,
      hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack extHookStack_le⟩
  shim stk _ _ := hook_placed_rocl_ok
    ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
      hookOk_withStack (hookOk_withVmPreserved sessionShim_hookOk hookNoop_vm) stk⟩
  memcpy stk _ _ := hook_placed_rocl_ok (cliExternsPlaced_memcpy_budget_sat mmpl g W hG stk)
  session_memcpy stk _ _ := hook_placed_rocl_ok
    (cliExternsPlaced_sessionMemcpy_budget_sat mmpl g W hG stk)
  memcpy_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_memcpyRegion_budget_sat mmpl g W hG) stk)
  session_memcpy_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG) stk)
  memset stk hle _ := hook_placed_rocl_ok
    (cliExternsPlaced_memset_budget_sat mmpl g W hG stk (pos_of_extHookStack_le hle))
  session_memset stk hle _ := hook_placed_rocl_ok
    (cliExternsPlaced_sessionMemset_budget_sat mmpl g W hG stk (pos_of_extHookStack_le hle))
  memset_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_memsetRegion_budget_sat mmpl g W hG) stk)
  session_memset_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG) stk)

theorem allocContractsFsPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsFsPlaced A lim
      (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  obtain ⟨fMs, hfMs, hMsLibc, hMsSess, hMsReg, hMsSessReg, hMsVm, hMsFs, _⟩ := hG.memset
  obtain ⟨fMc, hfMc, hMcLibc, hMcSess, hMcReg, hMcSessReg, _, hMcRO, hMcVm, hMcFs, _⟩ := hG.memcpy
  have hMsEq := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hfMs
  have hMcEq := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hfMc
  exact
    { alloc := hook_placed_rocl_ok
        ⟨g.alloc, cliGhostExterns_alloc g _,
          (hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le).keepsFs
            hG.alloc_fs⟩
      dealloc := hook_placed_rocl_ok
        ⟨g.dealloc, cliGhostExterns_dealloc g _,
          (hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.dealloc_fs⟩
      realloc := hook_placed_rocl_ok
        ⟨g.realloc, cliGhostExterns_realloc g _,
          (hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.realloc_fs⟩
      shim stk _ _ := hook_placed_rocl_ok
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
          (hookOk_withStack (hookOk_withVmPreserved sessionShim_hookOk hookNoop_vm) stk).keepsFs
            hookNoop_fs⟩
      memcpy stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withVmPreserved (hMcLibc stk) hMcVm).keepsFs hMcFs⟩
      session_memcpy stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withVmPreserved (hMcSess stk) hMcVm).keepsFs hMcFs⟩
      memcpy_region stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcReg hMcVm) stk).keepsFs hMcFs⟩
      session_memcpy_region stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcSessReg hMcVm) stk).keepsFs hMcFs⟩
      memset stk hle _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withVmPreserved (hMsLibc stk (pos_of_extHookStack_le hle)) hMsVm).keepsFs hMsFs⟩
      session_memset stk hle _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withVmPreserved (hMsSess stk (pos_of_extHookStack_le hle)) hMsVm).keepsFs hMsFs⟩
      memset_region stk _ _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq, (hookOk_withStack (hookOk_withVmPreserved hMsReg hMsVm) stk).keepsFs hMsFs⟩
      session_memset_region stk _ _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withStack (hookOk_withVmPreserved hMsSessReg hMsVm) stk).keepsFs hMsFs⟩
      session_memcpy_region_ro stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcRO hMcVm) stk).keepsFs hMcFs⟩ }

/-- Constructs `AllocContractsXCliPlaced A lim H` from `HookSat H` witnesses for allocator, shim, and
`libc` memory hooks. -/
theorem allocContractsXCliPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (hmemcpy : ∀ stk : Nat, HookSat H memcpyName (withVmPreserved (libcMemcpySpec stk)))
    (hsessMemcpy : ∀ stk : Nat, HookSat H memcpyName (sessionMemcpyBudgetSpec stk))
    (hmemcpyReg : HookSat H memcpyName (withVmPreserved memcpyRegionSpec))
    (hsessMemcpyReg : HookSat H memcpyName sessionMemcpyRegionBudgetSpec)
    (hmemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (withVmPreserved (libcMemsetSpec stk)))
    (hsessMemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (sessionMemsetBudgetSpec stk))
    (hmemsetReg : HookSat H memsetName (withVmPreserved memsetRegionSpec))
    (hsessMemsetReg : HookSat H memsetName sessionMemsetRegionBudgetSpec) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsXCliPlaced A lim H where
  alloc := by
    rcases halloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok
      ⟨f, hf, hookOk_rustAllocWithStack hok allocHookStack_le_extHookStack extHookStack_le⟩
  dealloc := by
    rcases hdealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok
      ⟨f, hf, hookOk_rustDeallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le⟩
  realloc := by
    rcases hrealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok
      ⟨f, hf, hookOk_rustReallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le⟩
  shim stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hshim stk)
  memcpy stk _ _ := hook_placed_rocl_ok (hmemcpy stk)
  session_memcpy stk _ _ := hook_placed_rocl_ok (hsessMemcpy stk)
  memcpy_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hmemcpyReg stk)
  session_memcpy_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hsessMemcpyReg stk)
  memset stk hle _ := hook_placed_rocl_ok (hmemset stk (pos_of_extHookStack_le hle))
  session_memset stk hle _ := hook_placed_rocl_ok (hsessMemset stk (pos_of_extHookStack_le hle))
  memset_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hmemsetReg stk)
  session_memset_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hsessMemsetReg stk)

/-- Constructs `AllocContractsFsPlaced A lim H` when the allocator and `libc` hooks preserve
`State.fs`. -/
theorem allocContractsFsPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (hmemcpy : ∀ stk : Nat, HookSat H memcpyName (withVmPreserved (libcMemcpySpec stk)))
    (hsessMemcpy : ∀ stk : Nat, HookSat H memcpyName (sessionMemcpyBudgetSpec stk))
    (hmemcpyReg : HookSat H memcpyName (withVmPreserved memcpyRegionSpec))
    (hsessMemcpyReg : HookSat H memcpyName sessionMemcpyRegionBudgetSpec)
    (hsessMemcpyRO : HookSat H memcpyName
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec))
    (hmemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (withVmPreserved (libcMemsetSpec stk)))
    (hsessMemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (sessionMemsetBudgetSpec stk))
    (hmemsetReg : HookSat H memsetName (withVmPreserved memsetRegionSpec))
    (hsessMemsetReg : HookSat H memsetName sessionMemsetRegionBudgetSpec)
    (hfs : ∀ sym ∈ [lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli,
        lsRustNoAllocShimSymCli, memcpyName, memsetName],
      ∀ f, H sym = some f → ∀ s : State, (f s).fs = s.fs) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsFsPlaced A lim H where
  alloc := by
    rcases halloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok ⟨f, hf,
      (hookOk_rustAllocWithStack hok allocHookStack_le_extHookStack extHookStack_le).keepsFs
        (hfs lsRustAllocSymCli (by decide) f hf)⟩
  dealloc := by
    rcases hdealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok ⟨f, hf,
      (hookOk_rustDeallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le).keepsFs
        (hfs lsRustDeallocSymCli (by decide) f hf)⟩
  realloc := by
    rcases hrealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok ⟨f, hf,
      (hookOk_rustReallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le).keepsFs
        (hfs lsRustReallocSymCli (by decide) f hf)⟩
  shim stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hshim stk)
      (hfs lsRustNoAllocShimSymCli (by decide))
  memcpy stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hmemcpy stk) (hfs memcpyName (by decide))
  session_memcpy stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hsessMemcpy stk) (hfs memcpyName (by decide))
  memcpy_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hmemcpyReg stk)
      (hfs memcpyName (by decide))
  session_memcpy_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hsessMemcpyReg stk)
      (hfs memcpyName (by decide))
  memset stk hle _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hmemset stk (pos_of_extHookStack_le hle))
      (hfs memsetName (by decide))
  session_memset stk hle _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hsessMemset stk (pos_of_extHookStack_le hle))
      (hfs memsetName (by decide))
  memset_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hmemsetReg stk)
      (hfs memsetName (by decide))
  session_memset_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hsessMemsetReg stk)
      (hfs memsetName (by decide))
  session_memcpy_region_ro stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hsessMemcpyRO stk)
      (hfs memcpyName (by decide))

/-! ## 5. Placed budget hook bundles at `cliGhostExterns` -/

theorem stage2ContractsMinPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    Stage2ContractsMinPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget.Stage2ContractsMinPlaced.of_hooks
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_sessionMemcpy_budget_sat mmpl g W hG extHookStack)

theorem codecHooksPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    CodecHooksPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  realloc := cliExternsPlaced_realloc_budget_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  memcpy := cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG
  panic_alloc := cliGhostExterns_panic_handle_alloc_error mmpl g W
  panic_raw := cliGhostExterns_panic_handle_error mmpl g W

theorem publicApiDecHooksPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim)) :
    PublicApiDecHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  memcpy := cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG
  stringClone := hStrClone
  handleError := cliGhostExterns_panic_handle_error mmpl g W
  expectFailed := cliGhostExterns_panic_option_expect_failed mmpl g W

theorem stage2ContractsMinPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (hmemcpy : HookSat H memcpyName (sessionMemcpyBudgetSpec extHookStack)) :
    Stage2ContractsMinPlaced M A lim H :=
  LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget.Stage2ContractsMinPlaced.of_hooks halloc hdealloc hrealloc hshim hmemcpy

theorem codecHooksPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSymCli (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H memcpyName (withVmPreserved framelessMemcpySpec))
    (hPanicAlloc : H CryptoVerification.LibsignalTripleRatchet.Prost.lsHandleAllocErrorSym =
      some Rust.panicked)
    (hPanicRaw : H lsHandleErrorSym = some Rust.panicked) :
    CodecHooksPlaced M A lim H where
  shim := hshim
  alloc := halloc
  realloc := hrealloc
  dealloc := hdealloc
  memcpy := hmemcpy
  panic_alloc := hPanicAlloc
  panic_raw := hPanicRaw

theorem publicApiDecHooksPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H memcpyName sessionMemcpyRegionBudgetSpec)
    (hStrClone : HookSat H CryptoVerification.LibsignalPublicApi.MessageDecrypt.lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hHandleError : H lsHandleErrorSym = some Rust.panicked)
    (hExpectFailed :
      H CryptoVerification.LibsignalPublicApi.MessageDecrypt.lsExpectFailedSym =
        some Rust.panicked) :
    PublicApiDecHooksPlaced A lim H where
  shim := hshim
  alloc := halloc
  dealloc := hdealloc
  memcpy := hmemcpy
  stringClone := hStrClone
  handleError := hHandleError
  expectFailed := hExpectFailed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SessionRecordAt.ExternStack -- shake: keep

public section

set_option autoImplicit false

/-!
# External Hook Contract Adapters on `SP2Ext`

Adapts `LibsignalExterns` hook contracts (`TRStubsOKX` / `ExtStubsOKX` / `HooksOKX`) at
`externStack = 2 ^ 14` onto `SP2Ext img.base ext` (`contractProg img.base ext`), providing
`Stage2ContractsA0`, arbitrary-allocator `Stage2ContractsA`, and relocatable
`[LibsignalPlacement]` `Stage2ContractsA0Placed` bundles for allocator, memory/shim, zeroize, RNG,
and formatting hooks.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustSpec CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.HooksE

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

/-! ## 1. Stack & `HooksE.A0` Representation Helpers -/

/-- Split `stackAt sp externStack` (`16384`) into `stackAt sp allocHookStack` (`4096`) and the lower `12288` bytes. -/
theorem stackAt_externStack_split_allocHookStack' (sp : BitVec 64) :
    stackAt sp CryptoVerification.LibsignalTripleRatchet.extHookStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 16384#64) 12288 := by
  have h := ProofLib.stackAt_split_bottom sp 4096 12288 (by decide)
  rw [sepConj_comm] at h
  exact h

/-! ## 2. Allocator Adapters (`HooksE.A0`) -/

/-- `rustDeallocSpec A` with the `LayoutOk size align` precondition required by `Externs.deallocSpec`. -/
@[expose] def rustDeallocLayoutSpec' (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜LayoutOk size align⌝ ∗ (rustDeallocSpec A).pre (p, size, align) s
  post := (rustDeallocSpec A).post

/-! ## 3. `Stage2ContractsA0` Bundle & Caller-Relative `.ok_at` Methods -/

section Placed

set_option maxRecDepth 2000000

theorem subroutine_ok_rustDeallocLayoutSpec'_of_rustDeallocSpec {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustDeallocSpec A)) :
    subroutine_ok prog entry (rustDeallocLayoutSpec' A) := by
  refine subroutine_ok_map h (fun ⟨p, sz, al⟩ R s0 hpre => ?_)
  dsimp only [rustDeallocLayoutSpec'] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨(p, sz, al), R, hpre.2, fun _ hp => hp⟩

/-- Relocatable `[LibsignalPlacement]` counterpart of `Stage2ContractsA0` at `HooksE.A0`
(`externStack = 16384`). -/
structure Stage2ContractsA0Placed [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  alloc_A0 : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ CryptoVerification.lsRustAllocSym)
      (withLsCl lsmpl ((rustAllocSpec HooksE.A0).withExternStackFromAlloc'))
  allocNW_A0 : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ CryptoVerification.lsRustAllocSym)
      (withLsCl lsmpl ((rustAllocNWSpec HooksE.A0).withExternStackFromAlloc'))
  deallocLayout_A0 : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl ((rustDeallocLayoutSpec' HooksE.A0).withExternStackFromAlloc'))
  realloc_A0 : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ CryptoVerification.lsRustReallocSym)
      (withLsCl lsmpl ((rustReallocSpec HooksE.A0).withExternStackFromAlloc'))
  shim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ CryptoVerification.lsRustNoAllocShimSym)
      (withLsCl lsmpl (sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack))
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))
  memcpyROX : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl sessionMemcpyROXSpec)
  memset : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memset")
      (withLsCl lsmpl (sessionMemsetSpec CryptoVerification.LibsignalTripleRatchet.extHookStack))
  bcmp : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "bcmp")
      (withLsCl lsmpl CryptoVerification.E2E.HooksE.e2eBcmpSpec)
  panic_handle_error : H CryptoVerification.lsHandleErrorSym = some Rust.panicked
  panic_handle_alloc_error :
    H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked

theorem Stage2ContractsA0Placed.of_block0 [LibsignalPlacement] {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ CryptoVerification.lsRustAllocSym)
      (withLsCodeLoaded lsmpl ((rustAllocSpec HooksE.A0).withExternStackFromAlloc')))
    (hallocNW : subroutine_ok blk0Prog (lsρ CryptoVerification.lsRustAllocSym)
      (withLsCodeLoaded lsmpl ((rustAllocNWSpec HooksE.A0).withExternStackFromAlloc')))
    (hdealloc : subroutine_ok blk0Prog (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCodeLoaded lsmpl ((rustDeallocLayoutSpec' HooksE.A0).withExternStackFromAlloc')))
    (hrealloc : subroutine_ok blk0Prog (lsρ CryptoVerification.lsRustReallocSym)
      (withLsCodeLoaded lsmpl ((rustReallocSpec HooksE.A0).withExternStackFromAlloc')))
    (hshim : subroutine_ok blk0Prog (lsρ CryptoVerification.lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl
        (sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hmemcpy : subroutine_ok blk0Prog (lsρ "memcpy")
      (withLsCodeLoaded lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hmemcpyROX : subroutine_ok blk0Prog (lsρ "memcpy")
      (withLsCodeLoaded lsmpl sessionMemcpyROXSpec))
    (hmemset : subroutine_ok blk0Prog (lsρ "memset")
      (withLsCodeLoaded lsmpl (sessionMemsetSpec CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hbcmp : subroutine_ok blk0Prog (lsρ "bcmp")
      (withLsCodeLoaded lsmpl CryptoVerification.E2E.HooksE.e2eBcmpSpec))
    (hpan_err : H CryptoVerification.lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2ContractsA0Placed H where
  alloc_A0 := ls_subroutine_ok_cl_of_callee (j := 0) halloc
  allocNW_A0 := ls_subroutine_ok_cl_of_callee (j := 0) hallocNW
  deallocLayout_A0 := ls_subroutine_ok_cl_of_callee (j := 0) hdealloc
  realloc_A0 := ls_subroutine_ok_cl_of_callee (j := 0) hrealloc
  shim := ls_subroutine_ok_cl_of_callee (j := 0) hshim
  memcpy := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpy
  memcpyROX := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpyROX
  memset := ls_subroutine_ok_cl_of_callee (j := 0) hmemset
  bcmp := ls_subroutine_ok_cl_of_callee (j := 0) hbcmp
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

theorem Stage2ContractsA0Placed.of_hooks [LibsignalPlacement] {H : LibsignalHooks}
    (halloc : HookSat H CryptoVerification.lsRustAllocSym (rustAllocSpec HooksE.A0))
    (hallocNW : HookSat H CryptoVerification.lsRustAllocSym (rustAllocNWSpec HooksE.A0))
    (hdealloc : HookSat H CryptoVerification.lsRustDeallocSym (rustDeallocSpec HooksE.A0))
    (hrealloc : HookSat H CryptoVerification.lsRustReallocSym (rustReallocSpec HooksE.A0))
    (hshim : HookSat H CryptoVerification.lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy"
      (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))
    (hmemcpyROX : HookSat H "memcpy" sessionMemcpyROXSpec)
    (hmemset : HookSat H "memset"
      (sessionMemsetSpec CryptoVerification.LibsignalTripleRatchet.extHookStack))
    (hbcmp : HookSat H "bcmp" CryptoVerification.E2E.HooksE.e2eBcmpSpec)
    (hpan_err : H CryptoVerification.lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2ContractsA0Placed H where
  alloc_A0 := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller halloc))
  allocNW_A0 := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller hallocNW))
  deallocLayout_A0 := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc'
      (subroutine_ok_rustDeallocLayoutSpec'_of_rustDeallocSpec (ls_hook_ok_of_caller hdealloc)))
  realloc_A0 := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller hrealloc))
  shim := fun {callerProg callerBlk _} => by
    have h0 : subroutine_ok callerProg (lsρ CryptoVerification.lsRustNoAllocShimSym)
        (withLsCl lsmpl (sessionShimSpec.withHookStack 0)) := by
      refine subroutine_ok_withLsCl_map' (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hshim))
        fun x R s0 hpre => ⟨x, stackAt s0.sp 0 ∗ R, ?_, fun sf hpost => ?_⟩
      · dsimp only [Spec.withHookStack] at hpre; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
      · dsimp only [Spec.withHookStack]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    exact subroutine_ok_withLsCl_withHookStack_mono (by decide) (by decide) h0
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)
  memcpyROX := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpyROX)
  memset := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemset)
  bcmp := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hbcmp)
  panic_handle_error := hpan_err
  panic_handle_alloc_error := hpan_alloc

end Placed

end Proofs.libsignal.Hooks2

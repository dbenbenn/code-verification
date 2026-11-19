/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AesDecErrRoWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoSubroutine
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time

/-!
# Concrete `.rodata` Error-String `aes_256_cbc_decrypt` Ghost Hook

Strengthens the `lsAesDecSym` linked ghost-call hook from `aesDecSpecOf` to
`aesDecErrRoSpecOf` (`withLsRet (cliAesDecBudgetSpecErrRo ...)`), exposing the concrete `.rodata`
error-string `(ptr, len) ∈ {(0x414401#64, 0x33#64), (0x4143f0#64, 0x11#64)}` on `.none` for
`DecryptTailTrap{507,}PlacedBudget`, while also proving `HookOk` against `aesDecSpecOf` and
`aesDecWeakSpecOf` plus `GhostRowOk` as a replacement for `aesDecGhost`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoGhost

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open CryptoGames.AES256 (aes256Dec)
open CryptoGames.CBC
  (AesKey Block blockToBytesLE bytesToBlock cbcDecRaw cbcDecryptBlocks chunks16 pkcs7Unpad)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E
  (aesDecFrameBytes aesDecHookMallocng aesDecOut stepRustAlloc1 stepRustDealloc1 writeVecHeader)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsAesDecSym lsAesEncSym unmodelled)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks ExtraGhostTable IsFsC cliGhostExternsWithExtra)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits MallocngCostModelIface MallocngCostModelSound
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.AesDecErrRoBudget
  (aesDecBudgetSpecErrRo cliAesDecBudgetSpecErrRo cliAesDecErrStr1Addr cliAesDecErrStr2Addr
   errResultErrRo_pack)
open LibsignalBinary.Heap.Fine (f3StdLayout fineCostModel fineCostModelIface fineCostModelSound)
open LibsignalBinary.Heap.SpecBudget
  (AesDecEnv aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (allocCallPreserved_refl cc_retHook_setMem_sameRegs fineHookRustCliAllocBudget
   mallocngHookBudgetPool mallocngHookBudgetPool_transport mallocngHookRustCliAllocBudget
   vmPreserved_retHook_setMem)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
  (aes_post_calloc_inputs fitsEvent_of_fitsAlloc1 pointsTo_replicate_to_memRegion
   rustAllocEvents_one stepRustAlloc1_budget_cps stepRustDealloc1_budget_cps write_vecU8_from_alloc)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen SpecStripSInvariant keepFsTrace keepFsTrace_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
  (aesDecHookMallocng_fs_eq_of_pre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (StubReachesTargetOn execFrozen_aesDecHookMallocng)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AesDecErrRoWithFds
  (hookOk_withLsRet_aesDecBudgetSpec_of_cliErrRo)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
  (aesDecEntryGuard aesDecSpecOf aesDecWeakSpecOf aesStubRconGuard c2AesRconAddr
   f3LinkedCallHook_externOnly_visitedIn_with_aesStubRcon f3LinkedCallHook_ok_at_aesStubRcon
   hookOk_of_withFsTraceExact specPreservesFsTrace_withFsTraceExact stubFrozenGuard
   withAesStubRconRO withFsTraceExact)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoSubroutine
  (c2_aesDec_errRo_subroutineOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcSubProg aesCbcSubProg_externAt_aesDec aesCbcSubProg_externAt_cases
   aesCbcSubProg_svc c2AesDecAddr c2_aesCbc_hKeep c2_aesCbc_hlr_ne_stub c2_keepRxSeg_mallocng
   c2_mng_placeable keepRxSeg keepRxSeg_aesDec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow
  (c2_aesCbc_hCL_strip c2_aesCbc_hPanReal c2_aesCbc_hRconRo c2_aesCbc_hRealHullNoExt
   c2_aesCbc_hStubFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
  (c2_f3CodeInv_and_fs_hInvKeep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (StripCommExtern externOnlyStdProg externOnlyStdProg_externAt
   steps_externOnly_to_real_of_visitedIn_inKeep stripCommExtern_rustPanicked)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookOk_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (GhostRowSpecOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open VerifiedLibraries (mallocngLib)

/-! ## 1. Fallback `aesDecErrRoHookMallocng` & `HookOk` -/

/-- `signal_crypto::aes_cbc::aes_256_cbc_decrypt` fallback ghost replay over shared `mallocng`
    writing the exact `.rodata` error-string `(ptr, len)` pair at `x8 + 8` and `x8 + 16`:
    - `(cliAesDecErrStr1Addr, 0x33#64)` when `ctLen == 0 || ctLen % 16 != 0`;
    - `(cliAesDecErrStr2Addr, 0x11#64)` when PKCS#7 unpadding returns `none`. -/
@[expose] noncomputable def aesDecErrRoHookMallocng (mpl : Obj.MultiPlacement)
    (D : AesKey → Block → Block) (s0 : State) : State :=
  if s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64 then
    unmodelled "aes_256_cbc_decrypt: key.len != 32 or iv.len != 16" s0
  else
    let ctLen := (s0.readReg64 .x1).toNat
    if ctLen == 0 || ctLen % 16 != 0 then
      retHook (fun s =>
        let r := s.readReg64 .x8
        s.setMem
          (((s.mem.write64 r errTag).write64 (r + 8#64) cliAesDecErrStr1Addr).write64
            (r + 16#64) 0x33#64)) s0
    else
      stepRustAlloc1 mpl true aesDecFrameBytes ctLen (fun s1 p =>
        match aesDecOut D s1 with
        | some pt =>
          retHook (fun s =>
            let r := s.readReg64 .x8
            s.setMem (writeVecHeader (s.mem.writeBytes p pt) r
              (BitVec.ofNat 64 ctLen) p (BitVec.ofNat 64 pt.length))) s1
        | none =>
          stepRustDealloc1 mpl aesDecFrameBytes p (fun s2 =>
            retHook (fun s =>
              let r := s.readReg64 .x8
              s.setMem
                (((s.mem.write64 r errTag).write64 (r + 8#64) cliAesDecErrStr2Addr).write64
                  (r + 16#64) 0x11#64)) s2) s1) s0

private theorem stepRustAlloc1_fs_perm_congr
    (mpl : Obj.MultiPlacement) (zeroed : Bool) (frameBytes size : Nat)
    {k1 k2 : State → BitVec 64 → State}
    (hk : ∀ s1 p, (k1 s1 p).fs = (k2 s1 p).fs ∧ (k1 s1 p).mem.perm = (k2 s1 p).mem.perm)
    (s : State) :
    (stepRustAlloc1 mpl zeroed frameBytes size k1 s).fs =
        (stepRustAlloc1 mpl zeroed frameBytes size k2 s).fs ∧
      (stepRustAlloc1 mpl zeroed frameBytes size k1 s).mem.perm =
        (stepRustAlloc1 mpl zeroed frameBytes size k2 s).mem.perm := by
  cases zeroed <;> simp only [stepRustAlloc1, Bool.false_eq_true, ↓reduceIte] <;> (
    split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · exact hk _ _)

private theorem stepRustDealloc1_fs_perm_congr
    (mpl : Obj.MultiPlacement) (frameBytes : Nat) (ptr : BitVec 64)
    {k1 k2 : State → State}
    (hk : ∀ s1, (k1 s1).fs = (k2 s1).fs ∧ (k1 s1).mem.perm = (k2 s1).mem.perm)
    (s : State) :
    (stepRustDealloc1 mpl frameBytes ptr k1 s).fs =
        (stepRustDealloc1 mpl frameBytes ptr k2 s).fs ∧
      (stepRustDealloc1 mpl frameBytes ptr k1 s).mem.perm =
        (stepRustDealloc1 mpl frameBytes ptr k2 s).mem.perm := by
  unfold stepRustDealloc1
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · exact hk _

private theorem aesDecErrRoHookMallocng_fs_perm_eq
    (mpl : Obj.MultiPlacement) (D : AesKey → Block → Block) (s0 : State) :
    (aesDecErrRoHookMallocng mpl D s0).fs = (aesDecHookMallocng mpl D s0).fs ∧
      (aesDecErrRoHookMallocng mpl D s0).mem.perm = (aesDecHookMallocng mpl D s0).mem.perm := by
  unfold aesDecErrRoHookMallocng aesDecHookMallocng
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split
    · refine ⟨rfl, ?_⟩
      change (((s0.mem.write64 _ _).write64 _ _).write64 _ _).perm =
        ((s0.mem.write64 _ _).write64 _ _).perm
      simp [Memory.perm_write64]
    · refine stepRustAlloc1_fs_perm_congr mpl true aesDecFrameBytes _ (fun s1 p => ?_) s0
      cases aesDecOut D s1 with
      | some pt => exact ⟨rfl, rfl⟩
      | none =>
        refine stepRustDealloc1_fs_perm_congr mpl aesDecFrameBytes p (fun s2 => ?_) s1
        refine ⟨rfl, ?_⟩
        change (((s2.mem.write64 _ _).write64 _ _).write64 _ _).perm =
          ((s2.mem.write64 _ _).write64 _ _).perm
        simp [Memory.perm_write64]

theorem execFrozen_aesDecErrRoHookMallocng
    (mpl : Obj.MultiPlacement) (D : AesKey → Block → Block)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (aesDecErrRoHookMallocng mpl D s0).mem :=
  ExecFrozen.of_perm_eq (execFrozen_aesDecHookMallocng mpl D s0 hfr0)
    (fun a => congrFun (aesDecErrRoHookMallocng_fs_perm_eq mpl D s0).2 a)

theorem aesDecErrRoHookMallocng_fs_eq_of_pre {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block)
    {x : AesCall} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (cliAesDecBudgetSpecErrRo D M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim).pre
        (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    (aesDecErrRoHookMallocng mpl D s0).fs = s0.fs :=
  (aesDecErrRoHookMallocng_fs_perm_eq mpl D s0).1.trans
    (aesDecHookMallocng_fs_eq_of_pre hS γ tp brkStart lim hPl D hpre hsp)

private theorem keepsFrozen_write64_of_pointsTo64 {m : Memory} {a old : BitVec 64} {F : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ old) ∗ F) :
    m.KeepsFrozen (m.write64 a v) := by
  have hm : m ⊨ memRegion a 8 ∗ F :=
    Satisfies.mono (sepConj_mono_left (pointsTo64_entails_memRegion a old)) h
  exact Memory.keepsFrozen_write64 ((IsBlock.memRegion a 8).canWrite (by decide) hm) v

private theorem satisfies_write64_of_pointsTo64 {m : Memory} {a old : BitVec 64} {F : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ old) ∗ F) :
    m.write64 a v ⊨ (a ↦₆₄ v) ∗ F := by
  have hm : m ⊨ memRegion a 8 ∗ F :=
    Satisfies.mono (sepConj_mono_left (pointsTo64_entails_memRegion a old)) h
  exact (IsBlock.memRegion a 8).write64 hm v

private theorem cbcDecryptBlocks_length (g : Block → Block) :
    ∀ (prev : Block) (cs : List Block), (cbcDecryptBlocks g prev cs).length = cs.length
  | _, [] => rfl
  | prev, c :: cs => by simp [cbcDecryptBlocks, cbcDecryptBlocks_length g c cs]

private theorem flatMap_blockToBytesLE_length :
    ∀ (bs : List Block), (bs.flatMap blockToBytesLE).length = 16 * bs.length
  | [] => rfl
  | b :: bs => by
    have hb : (blockToBytesLE b).length = 16 := by simp [blockToBytesLE]
    simp only [List.flatMap_cons, List.length_append, hb, flatMap_blockToBytesLE_length bs,
      List.length_cons]
    omega

private theorem pkcs7Unpad_length_le {bs pt : List (BitVec 8)}
    (h : pkcs7Unpad bs = some pt) : pt.length ≤ bs.length := by
  unfold pkcs7Unpad at h
  cases hlast : bs.getLast? with
  | none => simp [hlast] at h
  | some last =>
    simp only [hlast] at h
    split at h
    · cases h
    · split at h
      · injection h with hpt; subst hpt; simp
      · cases h

private theorem write_aesErrRo_at_ret {m : Memory} {ret errStr1Addr errStr2Addr p len : BitVec 64}
    {Frame : SepProp}
    (hdisj : (p = errStr1Addr ∧ len = 0x33#64) ∨ (p = errStr2Addr ∧ len = 0x11#64))
    (hmem : m ⊨ memRegion ret 24 ∗ Frame) :
    let mf := ((m.write64 ret errTag).write64 (ret + 8#64) p).write64 (ret + 16#64) len
    m.KeepsFrozen mf ∧ (mf.perm = m.perm) ∧
      (mf ⊨ ((ret ↦₆₄ errTag) ∗
        (∃∗ q : BitVec 64, ∃∗ l : BitVec 64,
          ⌜(q = errStr1Addr ∧ l = 0x33#64) ∨ (q = errStr2Addr ∧ l = 0x11#64)⌝ ∗
          ((ret + 8#64) ↦₆₄ q) ∗ ((ret + 16#64) ↦₆₄ l))) ∗ Frame) := by
  have hsplit : memRegion ret 24 = (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗
      ((∃∗ w1 : BitVec 64, (ret + 8#64) ↦₆₄ w1) ∗
        (∃∗ w2 : BitVec 64, (ret + 16#64) ↦₆₄ w2)) := by
    rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide), memRegion_eight ret,
      memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64)
        rfl (by bv_omega) (by decide),
      memRegion_eight (ret + 8#64), memRegion_eight (ret + 16#64)]
  rw [hsplit] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hmem
  rcases hmem with ⟨w2, w1, w0, hmem0⟩
  have hmem1 : m.write64 ret errTag ⊨
      ((ret + 8#64) ↦₆₄ w1) ∗ (((ret + 16#64) ↦₆₄ w2) ∗ ((ret ↦₆₄ errTag) ∗ Frame)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) (satisfies_write64_of_pointsTo64 errTag hmem0)
  have hmem2 : (m.write64 ret errTag).write64 (ret + 8#64) p ⊨
      ((ret + 16#64) ↦₆₄ w2) ∗ (((ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ p)) ∗ Frame) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) (satisfies_write64_of_pointsTo64 p hmem1)
  have hperm : (((m.write64 ret errTag).write64 (ret + 8#64) p).write64 (ret + 16#64) len).perm =
      m.perm := by
    simp [Memory.perm_write64]
  refine ⟨((keepsFrozen_write64_of_pointsTo64 errTag hmem0).trans
      (keepsFrozen_write64_of_pointsTo64 p hmem1)).trans
      (keepsFrozen_write64_of_pointsTo64 len hmem2), hperm, ?_⟩
  have hmem3 : ((m.write64 ret errTag).write64 (ret + 8#64) p).write64 (ret + 16#64) len ⊨
      ((ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ p) ∗ ((ret + 16#64) ↦₆₄ len)) ∗ Frame :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) (satisfies_write64_of_pointsTo64 len hmem2)
  exact Satisfies.mono (sepConj_mono_left
    (errResultErrRo_pack ret errStr1Addr errStr2Addr p len hdisj)) hmem3

/-- `aesDecErrRoHookMallocng mpl D` satisfies `cliAesDecBudgetSpecErrRo` over any `(M, I)` with
    `MallocngCostModelSound M I`. -/
theorem aesDecErrRoHookMallocng_budget_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecErrRoHookMallocng mpl D)
      (cliAesDecBudgetSpecErrRo D M (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) lim) := by
  rintro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre' := hpre
  dsimp only [cliAesDecBudgetSpecErrRo, aesDecBudgetSpecErrRo, aesCallPreBudget,
    mallocngHookRustCliAllocBudget] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hkey_len, hiv_len, hin_lt, hFitEnv⟩, hmem⟩
  unfold aesDecErrRoHookMallocng
  have hguard : (s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64) = false := by
    rw [hx3, hx5]; rfl
  simp only [hguard, Bool.false_eq_true, ↓reduceIte, hx1]
  by_cases hbad : (x.input.length == 0 || x.input.length % 16 != 0) = true
  · simp only [hbad, ↓reduceIte]
    have hbad_prop : x.input.length = 0 ∨ x.input.length % 16 ≠ 0 := by
      rcases Bool.or_eq_true_iff.mp hbad with h0 | hm
      · exact Or.inl (beq_iff_eq.mp h0)
      · exact Or.inr (bne_iff_ne.mp hm)
    have hdec_none : aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input = none := by
      unfold aesCbcDecrypt cbcDecRaw
      have hcond : x.input = [] ∨ x.input.length % 16 ≠ 0 :=
        hbad_prop.elim (fun h0 => Or.inl (List.eq_nil_of_length_eq_zero h0)) Or.inr
      simp [hcond]
    have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
        (x.frame ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
          stackAt s0.sp extHookStack ∗ R) := by
      unfold AesCall.frame; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    obtain ⟨hkf_e, hperm_e, herr⟩ := write_aesErrRo_at_ret
      (errStr1Addr := cliAesDecErrStr1Addr) (errStr2Addr := cliAesDecErrStr2Addr)
      (Or.inl ⟨rfl, rfl⟩) hmem_ret
    let mf := ((s0.mem.write64 x.ret errTag).write64 (x.ret + 8#64) cliAesDecErrStr1Addr).write64
      (x.ret + 16#64) 0x33#64
    rw [show retHook (fun s => let r := s.readReg64 .x8; s.setMem
        (((s.mem.write64 r errTag).write64 (r + 8#64) cliAesDecErrStr1Addr).write64
          (r + 16#64) 0x33#64)) s0 =
        retHook (fun s => s.setMem mf) s0 by simp [retHook, hx8, mf]]
    obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf rfl rfl rfl hrun
    refine ⟨hkf_e, rfl, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
    dsimp only [cliAesDecBudgetSpecErrRo, aesDecBudgetSpecErrRo]
    rw [hdec_none]; dsimp only
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨[], ?_⟩
    have hEnvNil : AesDecEnv x [] := by
      unfold AesDecEnv; split
      · rfl
      · next h => exact False.elim (h hbad_prop)
    have hpool_f :
        (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
          (M.stepEvents [] st) (retHook (fun s => s.setMem mf) s0) =
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 :=
      mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st
        (vmPreserved_retHook_setMem hperm_e)
    rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, hEnvNil⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) herr⟩
  · simp only [Bool.eq_false_iff.mpr hbad, Bool.false_eq_true, ↓reduceIte]
    have hnot_bad : ¬(x.input.length = 0 ∨ x.input.length % 16 ≠ 0) := by
      rintro (h0 | hm)
      · exact hbad (Bool.or_eq_true_iff.mpr (Or.inl (beq_iff_eq.mpr h0)))
      · exact hbad (Bool.or_eq_true_iff.mpr (Or.inr (bne_iff_ne.mpr hm)))
    have hpos : 1 ≤ x.input.length := by omega
    have hEnvOk : AesDecEnv x (rustAllocEvents x.input.length 1) := by
      unfold AesDecEnv; split
      · next h => exact False.elim (hnot_bad h)
      · exact Or.inl rfl
    have hFit : LibsignalBinary.Heap.FitsEvent M lim st (.alloc x.input.length) :=
      fitsEvent_of_fitsAlloc1 hpos (hFitEnv _ hEnvOk)
    have hmem0 : s0.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗ stackAt s0.sp extHookStack ∗
          (x.frame ∗ memRegion x.ret 24)) ∗ R := by
      unfold AesCall.frame; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    refine stepRustAlloc1_budget_cps hS hPl true aesDecFrameBytes x.input.length
      (by decide) (by decide) hFit hrun rfl rfl rfl hsp
      (Memory.KeepsFrozen.refl _) rfl (allocCallPreserved_refl s0) hmem0 _ ?_
    intro s1 p hp_ne hp_al16 hp_fit64 hs1_run hs1_sp hs1_regs hs1_vregs hkf1 hsym1 hpres1 hmem1
    simp only [↓reduceIte] at hmem1
    obtain ⟨hs1_x8, h_in, h_k, h_iv⟩ := aes_post_calloc_inputs hx0 hx1 hx2 hx4 hx8 hkey_len hiv_len
      hs1_regs (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1)
    have hout_eq : aesDecOut D s1 = aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input := by
      unfold aesDecOut; rw [h_in, h_k, h_iv]
    rw [hout_eq]
    rcases hdec : aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with _ | pt
    · dsimp only
      have hm_free : s1.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.alloc x.input.length) st) s1 ∗
            stackAt s0.sp extHookStack ∗
            I.BlockM γ p x.input.length 16 ∗ memRegion p x.input.length ∗
            (x.frame ∗ memRegion x.ret 24)) ∗ R :=
        Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion p x.input.length))))))
          (Entails.of_eq (by sep_ac_rfl))) hmem1
      refine stepRustDealloc1_budget_cps hS hPl aesDecFrameBytes x.input.length p
        hp_ne hp_al16 hp_fit64 (by decide) (by decide)
        hs1_run hs1_sp hs1_regs hs1_vregs hsp hkf1 hsym1 hpres1 hm_free _ ?_
      intro s2 hs2_run hs2_sp hs2_regs hs2_vregs hkf2 hsym2 hpres2 hmem2
      have hs2_x8 : s2.readReg64 .x8 = x.ret := by simp [State.readReg64, hs2_regs] at hx8 ⊢; exact hx8
      obtain ⟨hkf_e, hperm_e, herr⟩ := write_aesErrRo_at_ret
        (errStr1Addr := cliAesDecErrStr1Addr) (errStr2Addr := cliAesDecErrStr2Addr)
        (Or.inr ⟨rfl, rfl⟩)
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem2 : s2.mem ⊨ memRegion x.ret 24 ∗
          (x.frame ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim
            (M.step (.free 1 x.input.length) (M.step (.alloc x.input.length) st)) s2 ∗
            stackAt s0.sp extHookStack ∗ R))
      let mf := ((s2.mem.write64 x.ret errTag).write64 (x.ret + 8#64) cliAesDecErrStr2Addr).write64
        (x.ret + 16#64) 0x11#64
      rw [show retHook (fun s => let r := s.readReg64 .x8; s.setMem
          (((s.mem.write64 r errTag).write64 (r + 8#64) cliAesDecErrStr2Addr).write64
            (r + 16#64) 0x11#64)) s2 =
          retHook (fun s => s.setMem mf) s2 by simp [retHook, hs2_x8, mf]]
      obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs2_regs hs2_vregs hs2_sp hs2_run
      refine ⟨hkf2.trans hkf_e, hsym2, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
      dsimp only [cliAesDecBudgetSpecErrRo, aesDecBudgetSpecErrRo]
      rw [hdec]; dsimp only
      rw [sepExists_sepConj_left, satisfies_sepExists]
      let evsErr := rustAllocEvents x.input.length 1 ++ rustDeallocEvents x.input.length 1
      refine ⟨evsErr, ?_⟩
      have hEnvErr : AesDecEnv x evsErr := by
        unfold AesDecEnv; split
        · next h => exact False.elim (hnot_bad h)
        · exact Or.inr rfl
      have hev_step : M.stepEvents evsErr st =
          M.step (.free 1 x.input.length) (M.step (.alloc x.input.length) st) := by
        dsimp [evsErr]; rw [rustAllocEvents_one hpos]; rfl
      have hpool_f :
          (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
            (M.stepEvents evsErr st) (retHook (fun s => s.setMem mf) s2) =
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.free 1 x.input.length) (M.step (.alloc x.input.length) st)) s2 := by
        rw [hev_step]
        exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim _
          (vmPreserved_retHook_setMem hperm_e)
      rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres2.2.1, hEnvErr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) herr⟩
    · dsimp only
      have hpt_le : pt.length ≤ x.input.length := by
        have hdec' := hdec; unfold aesCbcDecrypt cbcDecRaw at hdec'
        split at hdec'
        · simp at hdec'
        · have hle := pkcs7Unpad_length_le hdec'
          rw [flatMap_blockToBytesLE_length, cbcDecryptBlocks_length, chunks16, List.length_ofFn] at hle
          omega
      have hm_prep : s1.mem ⊨
          I.BlockM γ p x.input.length 16 ∗ memRegion p x.input.length ∗ memRegion x.ret 24 ∗
            (x.frame ∗ mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.alloc x.input.length) st) s1 ∗ stackAt s0.sp extHookStack ∗ R) :=
        Satisfies.mono (Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (pointsTo_replicate_to_memRegion p x.input.length))))))
          (Entails.of_eq (by sep_ac_rfl))) hmem1
      obtain ⟨hkf_w, hperm_w, hvec⟩ := write_vecU8_from_alloc hS (mpl := mpl) (tp := tp) (brkStart := brkStart)
        (bs := pt) hp_ne hp_al16 hp_fit64 hpos (by omega) hpt_le hm_prep
      let mf := writeVecHeader (s1.mem.writeBytes p pt) x.ret
        (BitVec.ofNat 64 x.input.length) p (BitVec.ofNat 64 pt.length)
      rw [show retHook (fun s => let r := s.readReg64 .x8; s.setMem (writeVecHeader (s.mem.writeBytes p pt) r
          (BitVec.ofNat 64 x.input.length) p (BitVec.ofNat 64 pt.length))) s1 =
          retHook (fun s => s.setMem mf) s1 by simp [retHook, hs1_x8, mf]]
      obtain ⟨hret_f, hcc_f⟩ := cc_retHook_setMem_sameRegs mf hs1_regs hs1_vregs hs1_sp hs1_run
      refine ⟨hkf1.trans hkf_w, hsym1, Or.inl ⟨hret_f, hcc_f, ?_⟩⟩
      dsimp only [cliAesDecBudgetSpecErrRo, aesDecBudgetSpecErrRo]
      rw [hdec]; dsimp only
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨rustAllocEvents x.input.length 1, ?_⟩
      have hev_step : M.stepEvents (rustAllocEvents x.input.length 1) st =
          M.step (.alloc x.input.length) st := by
        rw [rustAllocEvents_one hpos]; rfl
      have hpool_f :
          (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim
            (M.stepEvents (rustAllocEvents x.input.length 1) st)
            (retHook (fun s => s.setMem mf) s1) =
            mallocngHookBudgetPool M I γ mpl tp brkStart lim
              (M.step (.alloc x.input.length) st) s1 := by
        rw [hev_step]
        exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim _
          (vmPreserved_retHook_setMem hperm_w)
      rw [hpool_f, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres1.2.1, hEnvOk⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hvec⟩

theorem fineAesDecErrRo_budget_hookOk (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecErrRoHookMallocng mpl D)
      (cliAesDecBudgetSpecErrRo D fineCostModel
        (fineHookRustCliAllocBudget γ mpl tp brkStart) lim) :=
  aesDecErrRoHookMallocng_budget_ok fineCostModelSound γ tp brkStart lim hPl D

/-! ## 2. `aesDecErrRoSpecOf`, `aesDecErrRoGhost`, State Preservation, & `GhostRowSpecOk` -/

/-- `(γ, tp)`-indexed `withLsRet`-narrowed `cliAesDecBudgetSpecErrRo` for `f3LinkedCallHook`. -/
@[expose] def aesDecErrRoSpecOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) : Spec (AesCall × fineCostModel.σ) :=
  withLsRet (cliAesDecBudgetSpecErrRo aes256Dec fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)

/-- `(γ, tp)`- and `W`-independent linked ghost-call hook for `lsAesDecSym` exposing the `.rodata`
    error-string `(ptr, len)` pair on `.none`. -/
@[expose] noncomputable def aesDecErrRoGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) : State :=
  letI := Classical.propDecidable
  if aesStubRconGuard P_sub brkStart s0 then
    f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesDecErrRoSpecOf mmpl brkStart lim)
      (aesDecErrRoHookMallocng mmpl aes256Dec) s0
  else if ActiveF3CallPre (aesDecErrRoSpecOf mmpl brkStart lim) s0 then
    keepFsTrace (aesDecErrRoHookMallocng mmpl aes256Dec) s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

theorem aesDecErrRoGhost_eq_f3LinkedCallHook_of_aesStubRcon [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hG : aesStubRconGuard P_sub brkStart s0) :
    aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim s0 =
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
        (aesDecErrRoSpecOf mmpl brkStart lim)
        (aesDecErrRoHookMallocng mmpl aes256Dec) s0 := by
  classical
  unfold aesDecErrRoGhost
  simp only [hG, ↓reduceIte]

theorem aesDecErrRoGhost_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs := by
  classical
  unfold aesDecErrRoGhost
  split
  · exact f3LinkedCallHook_fs keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesDecErrRoSpecOf mmpl brkStart lim) (aesDecErrRoHookMallocng mmpl aes256Dec) s0
  · split <;> rfl

theorem aesDecErrRoGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim) := by
  classical
  intro s0
  unfold aesDecErrRoGhost
  split
  · exact f3LinkedCallHook_fsT keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesDecErrRoSpecOf mmpl brkStart lim) (aesDecErrRoHookMallocng mmpl aes256Dec) s0
  · split <;> exact FsTraced.of_eq rfl rfl

theorem aesDecErrRoGhost_preserves_execFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim u).mem := by
  classical
  unfold aesDecErrRoGhost
  split
  · unfold f3LinkedCallHook
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
      · exact execFrozen_aesDecErrRoHookMallocng mmpl aes256Dec u hfr
    · exact hfr
  · split
    · exact execFrozen_aesDecErrRoHookMallocng mmpl aes256Dec u hfr
    · exact hfr

theorem aesDecErrRoGhost_rowSpecOk [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsAesDecSym
      (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim) :=
  ⟨aesDecErrRoGhost_fs keep P_sub entryTarget mmpl brkStart lim,
   aesDecErrRoGhost_fsT keep P_sub entryTarget mmpl brkStart lim, by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs.ExtraRowSpec
    have hd1 : (lsAesDecSym == "bcmp") = false := by decide
    have hd2 : (lsAesDecSym == "strlen") = false := by decide
    have hd3 : (lsAesDecSym == "memmove") = false := by decide
    have hd4 : (lsAesDecSym == CryptoVerification.SignalSession.lsFromUtf8Sym) = false := by decide
    have hd5 : (lsAesDecSym == CryptoVerification.SignalSession.lsMemrchrSym) = false := by decide
    have hd6 : (lsAesDecSym == CryptoVerification.SignalSession.lsDurationSinceSym) = false := by decide
    have hd7 : (lsAesDecSym == CryptoVerification.SignalSession.lsTimeAddSym) = false := by decide
    have hd8 : (lsAesDecSym == CryptoVerification.SignalSession.lsBlackBoxSym) = false := by decide
    have hd9 : (lsAesDecSym == CryptoVerification.SignalSession.lsStaticSecretDropSym) = false := by decide
    have hd10 : (lsAesDecSym == CryptoVerification.SignalSession.lsSharedSecretDropSym) = false := by decide
    have hd11 : (lsAesDecSym == lsAesEncSym) = false := by decide
    have hd12 : (lsAesDecSym == lsAesDecSym) = true := by decide
    simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, Bool.false_eq_true,
      ↓reduceIte]
    trivial⟩

/-! ## 3. Invariants, Pointwise `HookOk`, & `GhostRowOk` -/

theorem specStripSInvariant_aesDecErrRoSpecOf [LibsignalPlacement]
    {keep : BitVec 64 → Bool} (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)) where
  pre_eq := by
    intro ⟨x, st⟩ s
    dsimp only [withFsTraceExact, aesDecErrRoSpecOf, withLsRet, cliAesDecBudgetSpecErrRo,
      aesDecBudgetSpecErrRo, aesCallPreBudget]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    intro ⟨x, st⟩ s0 sf
    dsimp only [withFsTraceExact, aesDecErrRoSpecOf, withLsRet, cliAesDecBudgetSpecErrRo,
      aesDecBudgetSpecErrRo]
    congr 1
    exact congrArg sepExists (funext fun evs => by
      rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
      rfl)
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem prePC_aesDecErrRoSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (s : State) (pc : BitVec 64),
      (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)).pre x (s.setPC pc) =
        (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)).pre x s := by
  intro ⟨_, _⟩ s _
  cases s
  rfl

private theorem outPC_aesDecErrRoSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))
        x R (s0.setPC pc) sf →
      SubroutineOutcome (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))
        x R s0 sf := by
  intro _ _ s0 _ _
  cases s0
  exact id

private theorem aesDecErrRoFallback_withFsTraceExact_ok [LibsignalPlacement]
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookOk (keepFsTrace (aesDecErrRoHookMallocng mmpl aes256Dec))
      (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)) := by
  have hBase : HookOk (aesDecErrRoHookMallocng mmpl aes256Dec)
      (aesDecErrRoSpecOf mmpl brkStart lim γ tp) :=
    hookOk_withLsRet (fineAesDecErrRo_budget_hookOk γ tp brkStart lim hPl aes256Dec)
  have hExact : HookOk (aesDecErrRoHookMallocng mmpl aes256Dec)
      (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)) := by
    intro ⟨x, st⟩ R s0 hrun hpre hsp
    have hpre_ls : s0.mem ⊨ (aesDecErrRoSpecOf mmpl brkStart lim γ tp).pre (x, st) s0 ∗ R := hpre
    dsimp only [aesDecErrRoSpecOf, withLsRet] at hpre_ls
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ls
    have hpre_bud : s0.mem ⊨
        (cliAesDecBudgetSpecErrRo aes256Dec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre (x, st) s0 ∗ R := hpre_ls.2
    have hfs : (aesDecErrRoHookMallocng mmpl aes256Dec s0).fs = s0.fs :=
      aesDecErrRoHookMallocng_fs_eq_of_pre fineCostModelSound γ tp brkStart lim hPl aes256Dec
        hpre_bud hsp
    obtain ⟨hkf, hsym, hout⟩ := hBase (x, st) R s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      have htr : (aesDecErrRoHookMallocng mmpl aes256Dec s0).trace = s0.trace := by
        dsimp only [aesDecErrRoSpecOf, withLsRet, cliAesDecBudgetSpecErrRo,
          aesDecBudgetSpecErrRo] at hpost
        rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
        rcases hpost with ⟨_, hevs⟩
        simp only [sepConj_assoc] at hevs
        rw [satisfies_pure_sepConj] at hevs
        exact hevs.1.1
      dsimp only [withFsTraceExact]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfs, htr⟩, hpost⟩
    · dsimp only [aesDecErrRoSpecOf, withLsRet, cliAesDecBudgetSpecErrRo,
        aesDecBudgetSpecErrRo] at hpan
      rw [satisfies_pure_sepConj] at hpan
      exact False.elim hpan.1
    · dsimp only [aesDecErrRoSpecOf, withLsRet, cliAesDecBudgetSpecErrRo,
        aesDecBudgetSpecErrRo] at hex
      rw [satisfies_pure_sepConj] at hex
      exact False.elim hex.1
    · dsimp only [aesDecErrRoSpecOf, withLsRet, cliAesDecBudgetSpecErrRo,
        aesDecBudgetSpecErrRo] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1
  refine keepFsTrace_ok hExact (fun _ _ s0 hout => ?_)
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- Pointwise `HookOk` for `aesDecErrRoGhost` at `aesDecErrRoSpecOf mmpl brkStart lim γ tp`. -/
theorem aesDecErrRoGhost_errRo_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : brkStart = f3StdLayout.brkStart → subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)))) :
    HookOk (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim)
      (aesDecErrRoSpecOf mmpl brkStart lim γ tp) := by
  classical
  apply hookOk_of_withFsTraceExact
  intro x R s0 hrun hpre hsp
  by_cases hG : aesStubRconGuard P_sub brkStart s0
  · rw [aesDecErrRoGhost_eq_f3LinkedCallHook_of_aesStubRcon keep P_sub entryTarget mmpl brkStart
      lim hG]
    exact f3LinkedCallHook_ok_at_aesStubRcon
      (P_real := externOnlyStdProg P_sub)
      (specOf := fun γ' tp' => withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ' tp'))
      (fallback := aesDecErrRoHookMallocng mmpl aes256Dec)
      rfl hsvc_sub (fun pc _ h => (externOnlyStdProg_externAt P_sub pc).trans h)
      (fun pc f he => ⟨(externOnlyStdProg_externAt P_sub pc).trans he, hcomm pc f he⟩) γ tp
      (fun _ _ s0' hpre' => by
        dsimp only [withFsTraceExact, aesDecErrRoSpecOf, withLsRet] at hpre'
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
        exact hlr_ne_stub (s0'.readReg64 .lr) hpre'.1)
      (hOk hG.2.2)
      (specStripSInvariant_aesDecErrRoSpecOf γ mmpl tp brkStart hKeepMallocng lim)
      (specPreservesFsTrace_withFsTraceExact _)
      (prePC_aesDecErrRoSpecOf γ mmpl tp brkStart lim)
      (outPC_aesDecErrRoSpecOf γ mmpl tp brkStart lim)
      (aesDecErrRoFallback_withFsTraceExact_ok γ tp brkStart lim hPl)
      hG.1 hG.2.1 hrun hpre hsp
  · have hActPre : ActiveF3CallPre (aesDecErrRoSpecOf mmpl brkStart lim) s0 :=
      ⟨hrun, hsp, γ, tp, x, R, hpre⟩
    have heq : aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim s0 =
        keepFsTrace (aesDecErrRoHookMallocng mmpl aes256Dec) s0 := by
      unfold aesDecErrRoGhost
      simp only [hG, hActPre, ↓reduceIte]
    rw [heq]
    exact aesDecErrRoFallback_withFsTraceExact_ok γ tp brkStart lim hPl x R s0 hrun hpre hsp

/-- Pointwise `HookOk` for `aesDecErrRoGhost` weakened to `aesDecSpecOf mmpl brkStart lim γ tp`. -/
theorem aesDecErrRoGhost_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : brkStart = f3StdLayout.brkStart → subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)))) :
    HookOk (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim)
      (aesDecSpecOf mmpl brkStart lim γ tp) :=
  hookOk_withLsRet_aesDecBudgetSpec_of_cliErrRo
    (aesDecErrRoGhost_errRo_ok hsvc_sub hcomm hlr_ne_stub hPl hKeepMallocng γ tp hOk)

private theorem aesErr_entails_weak (ret : BitVec 64) :
    (ret ↦₆₄ errTag) ∗
      (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ∗ memRegion (ret + 16#64) 8 ⊢
      (ret ↦₆₄ errTag) ∗ memRegion (ret + 8#64) 16 := by
  have hp8 : (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ⊢ memRegion (ret + 8#64) 8 := by
    rw [memRegion_eight (ret + 8#64)]
    refine Entails.sepExists_elim fun p => Entails.pure_left fun _ => ?_
    exact @Entails.sepExists_intro (BitVec 64) (fun q => (ret + 8#64) ↦₆₄ q) p
  have h16 : memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 = memRegion (ret + 8#64) 16 :=
    (memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64)
      rfl (by bv_omega) (by decide)).symm
  rw [← h16]
  exact sepConj_mono_right (sepConj_mono_left hp8)

/-- Pointwise `aesDecWeakSpecOf` companion `HookOk` for `aesDecErrRoGhost`. -/
theorem aesDecErrRoGhost_weak_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : brkStart = f3StdLayout.brkStart → subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp)))) :
    HookOk (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim)
      (aesDecWeakSpecOf mmpl brkStart lim γ tp) := by
  refine HookOk.mono
    (aesDecErrRoGhost_ok hsvc_sub hcomm hlr_ne_stub hPl hKeepMallocng γ tp hOk)
    (fun _ _ _ h => h) ?_ (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
  rintro ⟨x, st⟩ R s0 sf _ hpost
  dsimp only [aesDecSpecOf, aesDecWeakSpecOf, withLsRet, aesDecBudgetSpec,
    aesDecWeakBudgetSpec, aesDecFnBudgetSpec] at hpost ⊢
  refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_elim fun evs => ?_)) hpost
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List AllocEvent) _ evs)
  cases aesCbcDecrypt aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
  | none =>
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (aesErr_entails_weak x.ret)))
  | some _ =>
    exact Entails.refl _

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem lsRetAddr624_of_aesDecErrRoGhost_noException [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits} {u : State}
    (hnoex : ∀ msg,
      (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) := by
  classical
  have hAct : ActiveF3CallPre (aesDecErrRoSpecOf mmpl brkStart lim) u := by
    by_cases hG : aesStubRconGuard P_sub brkStart u
    · rw [aesDecErrRoGhost_eq_f3LinkedCallHook_of_aesStubRcon keep P_sub entryTarget mmpl brkStart
        lim hG] at hnoex
      by_contra hnot
      have hex :
          (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (aesDecErrRoSpecOf mmpl brkStart lim)
            (aesDecErrRoHookMallocng mmpl aes256Dec) u).status =
            .Exception "ghost-hook precondition violated" := by
        unfold f3LinkedCallHook
        simp only [hnot, ↓reduceDIte]
      exact hnoex _ hex
    · by_contra hnot
      have hex : (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim u).status =
          .Exception "ghost-hook precondition violated" := by
        unfold aesDecErrRoGhost
        simp only [hG, hnot, ↓reduceIte]
      exact hnoex _ hex
  rcases hAct with ⟨_, _, γ, tp, x, R, hpre⟩
  dsimp only [aesDecErrRoSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

theorem aesDecErrRoGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsAesDecSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => P_sub.CodeLoaded (stripExecOutside keep m))
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsAesDecSym)
        entryTarget) :
    GhostRowReplayOn mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨aesDecErrRoGhost_preserves_execFrozen keep P_sub entryTarget mmpl brkStart lim hfr,
     aesDecErrRoGhost_fs keep P_sub entryTarget mmpl brkStart lim u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealStubNone W, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hSF : stubFrozenGuard P_sub u := hStubFrozen u hInvU
    have hRcon : RoDataAt u.mem c2AesRconAddr aesRconBytes := hRconRo u hInvU
    have hG : aesStubRconGuard P_sub brkStart u := ⟨hSF, hRcon, hbrk⟩
    have hlr624 : LsRetAddr624 (u.readReg64 .lr) :=
      lsRetAddr624_of_aesDecErrRoGhost_noException hnoex
    have hlr_out : keep (u.readReg64 .lr) = false := hKeep _ hlr624
    have hlr_ne := hlr_ne_stub _ hlr624
    have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hCL_strip u hfr hInvU
    have heq_f3 := aesDecErrRoGhost_eq_f3LinkedCallHook_of_aesStubRcon
      keep P_sub entryTarget mmpl brkStart lim hG
    have hnoex_f3 : ∀ msg,
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
          (aesDecErrRoSpecOf mmpl brkStart lim)
          (aesDecErrRoHookMallocng mmpl aes256Dec) u).status ≠ .Exception msg := by
      rwa [← heq_f3]
    obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
      f3LinkedCallHook_externOnly_visitedIn_with_aesStubRcon
        (specOf := fun γ tp => withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))
        (fallback := aesDecErrRoHookMallocng mmpl aes256Dec)
        hsvc_sub
        (fun pc f he => by
          obtain ⟨rfl, _⟩ := hPanReal W pc f he
          exact stripCommExtern_rustPanicked keep)
        hOk
        (fun γ tp => specStripSInvariant_aesDecErrRoSpecOf γ mmpl tp brkStart hKeepMallocng lim)
        (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
        (fun γ tp => prePC_aesDecErrRoSpecOf γ mmpl tp brkStart lim)
        (fun γ tp => outPC_aesDecErrRoSpecOf γ mmpl tp brkStart lim)
        hnoex_f3 hfr hSF hRcon hlr_out hlr_ne hCodeSub
    have hhook_exact_eq :
        f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (fun γ tp => withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))
            (aesDecErrRoHookMallocng mmpl aes256Dec) u =
          f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (aesDecErrRoSpecOf mmpl brkStart lim)
            (aesDecErrRoHookMallocng mmpl aes256Dec) u := rfl
    rw [hhook_exact_eq] at hvis hfr_sf hfs_sf
    have hStubSteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        u (u.setPC entryTarget) :=
      hStub W u hpc hrun hfr hCodeSub
    have hBodySteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC entryTarget)
        (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim u) := by
      rw [heq_f3]
      exact steps_externOnly_to_real_of_visitedIn_inKeep rfl
        (fun _ hk hsub => hRealHullNoExt W hk hsub)
        (fun pc f he => by
          obtain ⟨rfl, hreal⟩ := hPanReal W pc f he
          exact hreal)
        hvis
    rw [← heq_f3] at hfr_sf hfs_sf
    exact ⟨hStubSteps.trans hBodySteps, hfr_sf,
      hInvKeep u (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim u) hInvU hkf hfs_sf⟩

theorem aesDecErrRoGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hTargetEq : libsignalSessionLib.resolve mpl lsAesDecSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowReplayOn mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim) :=
  aesDecErrRoGhost_rowReplayOn_of_stub mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
    hsvc_sub hKeepMallocng hOk hStubFrozen hRconRo hbrk hCL_strip hInvKeep hKeep
    hlr_ne_stub hRealHullNoExt hPanReal
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W hkeep_entry hsub_entry_none)
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

theorem aesDecErrRoGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecErrRoSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hTargetEq : libsignalSessionLib.resolve mpl lsAesDecSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowOk mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecErrRoGhost keep P_sub entryTarget mmpl brkStart lim) :=
  ⟨aesDecErrRoGhost_rowSpecOk keep P_sub entryTarget mmpl brkStart lim,
   aesDecErrRoGhost_rowReplayOn mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
     hsvc_sub hsub_entry_none hkeep_entry hKeepMallocng hOk hStubFrozen hRconRo hbrk hTargetEq
     hCL_strip hInvKeep hKeep hlr_ne_stub hRealHullNoExt hPanReal⟩

/-! ## 4. Concrete (`keepRxSeg`, `aesCbcSubProg`, `c2AesDecAddr`) Specializations -/

/-- Pointwise `HookOk` for `aesDecErrRoGhost` at `aesDecErrRoSpecOf`. -/
theorem c2_aesDecErrRoGhost_errRo_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim)
      (aesDecErrRoSpecOf mmpl brkStart lim γ tp) :=
  aesDecErrRoGhost_errRo_ok
    aesCbcSubProg_svc
    (fun _ _ he =>
      (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked keepRxSeg)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_mng_placeable mmpl hMm)
    (c2_keepRxSeg_mallocng mmpl hMm)
    γ tp
    (fun hbrk => c2_aesDec_errRo_subroutineOk mmpl hMm brkStart hbrk lim γ tp)

/-- Pointwise `HookOk` for `aesDecErrRoGhost` at `aesDecSpecOf` (replaces
    `C2RowLayoutFacts.c2_aesDecGhost_ok`). -/
theorem c2_aesDecErrRoGhost_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim)
      (aesDecSpecOf mmpl brkStart lim γ tp) :=
  aesDecErrRoGhost_ok
    aesCbcSubProg_svc
    (fun _ _ he =>
      (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked keepRxSeg)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_mng_placeable mmpl hMm)
    (c2_keepRxSeg_mallocng mmpl hMm)
    γ tp
    (fun hbrk => c2_aesDec_errRo_subroutineOk mmpl hMm brkStart hbrk lim γ tp)

/-- Pointwise `HookOk` companion for `aesDecErrRoGhost` at `aesDecWeakSpecOf` (replaces
    `C2RowLayoutFacts.c2_aesDecGhost_weak_ok`). -/
theorem c2_aesDecErrRoGhost_weak_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim)
      (aesDecWeakSpecOf mmpl brkStart lim γ tp) :=
  aesDecErrRoGhost_weak_ok
    aesCbcSubProg_svc
    (fun _ _ he =>
      (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked keepRxSeg)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_mng_placeable mmpl hMm)
    (c2_keepRxSeg_mallocng mmpl hMm)
    γ tp
    (fun hbrk => c2_aesDec_errRo_subroutineOk mmpl hMm brkStart hbrk lim γ tp)

/-- Generic `InvS` `GhostRowOk` for `aesDecErrRoGhost`. -/
theorem c2_aesDecErrRoGhost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hResDec : libsignalSessionLib.resolve mpl lsAesDecSym = c2AesDecAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  aesDecErrRoGhost_rowOk mpl mmpl keepRxSeg aesCbcSubProg c2AesDecAddr brkStart lim
    InvS EG
    aesCbcSubProg_svc
    aesCbcSubProg_externAt_aesDec
    keepRxSeg_aesDec
    (c2_keepRxSeg_mallocng mmpl hMm)
    (fun γ tp => c2_aesDec_errRo_subroutineOk mmpl hMm brkStart hbrk lim γ tp)
    (c2_aesCbc_hStubFrozen hLs hInv)
    (c2_aesCbc_hRconRo hLs hInv)
    hbrk
    hResDec
    (c2_aesCbc_hCL_strip hInv)
    hInvKeep
    (fun _ hlr => c2_aesCbc_hKeep hLsLsmpl hlr)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_aesCbc_hRealHullNoExt hExt)
    (c2_aesCbc_hPanReal mmpl hLs)

/-- `mpl := lsmpl` `GhostRowOk` for `aesDecErrRoGhost` over `EG`. -/
theorem c2_aesDecErrRoGhost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hResDec : libsignalSessionLib.resolve lsmpl lsAesDecSym = c2AesDecAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsAesDecSym
      (fun _ => True)
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  c2_aesDecErrRoGhost_rowOk_of_inv lsmpl mmpl brkStart lim
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    hExt hResDec hLs hLs hMm
    (fun _ h => h.1)
    (c2_f3CodeInv_and_fs_hInvKeep lsmpl mmpl PredFs)
    hbrk

/-- Replacement for `C2RowLayoutFacts.c2_aesDecGhost_rowOk` (taking `hRes.aesDec_eq`). -/
theorem c2_aesDecErrRoGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hResDec : libsignalSessionLib.resolve lsmpl lsAesDecSym = c2AesDecAddr)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesDecSym
      (aesDecEntryGuard lsmpl)
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  c2_aesDecErrRoGhost_rowOk_lsmpl_and_fs mmpl brkStart lim PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hExt hResDec hLs hMm hbrk

/-- Replacement for `C2RowLayoutFacts.c2_aesDecGhost_rowOk_guardOf` (taking `hRes.aesDec_eq`). -/
theorem c2_aesDecErrRoGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hResDec : libsignalSessionLib.resolve lsmpl lsAesDecSym = c2AesDecAddr)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesDecSym
      (guardOf lsAesDecSym)
      (aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_aesDecErrRoGhost_rowOk mmpl brkStart lim PredFs g extra hResDec hExt hLs hMm hbrk
  exact ⟨hSpec, ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoGhost

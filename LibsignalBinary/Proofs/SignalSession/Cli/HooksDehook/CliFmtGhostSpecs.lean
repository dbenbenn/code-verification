/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.AsciiNum
public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `[LibsignalPlacement]`-Native Formatting Call Descriptors and Contracts

Bottom-of-DAG call-descriptor contracts for linked `core::fmt::write` (`lsFmtWriteSym`) and
`alloc::fmt::format::format_inner` (`lsFormatInnerSym`), placed below `TripleRatchet`, `SpqrV1`,
`PeakBudget`, and `SignalSession/Cli`:

- Call descriptors (`CliFmtWriteProtoAddrCall`, `CliFormatInnerLsCall`): pure `Type 0` structures
  carrying no `Prop`, `Env`, or `MultiPlacement` fields. Read-only `.rodata` vtables and
  `DEC_DIGITS_LUT` are discharged in the ghost-hook replay layer from `F3CodeInv`, so caller
  preconditions mention only register values, `fmtArgumentsAt`, and live formattee memory
  (`c.clientSep`).
- `<ProtocolAddress as Display>::fmt` `core::fmt::write` contract (`cliFmtWriteProtoAddrSpec`,
  `fmtWriteProtoAddrLsEnvSpec`, `fmtWriteProtoAddrCliLsSpec`): matches Block `215`'s 2-argument
  `"{}.{}"` call (`args = [(namePtr, lsmpl.base shimBlock), (devPtr, lsmpl.base 214)]`, where Block
  `214` is `<DeviceId as Display>::fmt` on `dev : BitVec 8` and `x1` is one of the 3 crate
  `<String as fmt::Write>` `.rodata` vtables).
- 13-shape `alloc::fmt::format::format_inner` contract (`cliFormatInnerLsCallSpec`,
  `formatInnerCallLsEnvSpec`, `formatInnerCallCliLsSpec`): covers `empty`, `fromStr`, `lit0`,
  `u8Display`, `u32Display`, `u8DisplayPrefixed`, `strRefDisplayShim` (via crate-local
  `cliStrRefDisplayShimBlocks`, avoiding GC'd `coreFmtMultiLib` block `7`),
  `strRefDisplayPrefixedShim`, `cliAesErrDisplayPrefixedShim`, `spqrErrorDisplayPrefixed`,
  `protoAddrDisplay`, `dottedStringDevIdShim`, and `dottedStringU32Shim`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E (fmtWriteHook0 formatInnerHook0 writeVecHeader)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv
   RustCliAllocBudget VmPreserved rustAllocEvents)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecErrStr1Addr cliAesDecErrStr2Addr)
open LibsignalBinary.Heap.SpecBudget
  (fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (fmtWriteKnownEvents formatInnerKnownEvents)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof
  (FmtWriteAddrEnv formatDecimalNat_u32_length formatDecimalNat_u8_length)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof
  (FormatInnerAddrEnv FormatInnerFromStrEnv FormatInnerShortLitEnv FormatInnerSingleEnv
   FormatInnerU32Env FormatInnerU8Env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers (write_empty_vecU8)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (CliFmtWriteEnv CliFormatInnerEnv ExactOrNilEnv FormatInnerPrefixedEnv
   cliFmtWriteEnv_of_addr0 cliFormatInnerEnv_nil cliFormatInnerEnv_of_addr
   cliFormatInnerEnv_of_fromStr cliFormatInnerEnv_of_prefixed cliFormatInnerEnv_of_shortLit
   cliFormatInnerEnv_of_single cliFormatInnerEnv_of_u32 cliFormatInnerEnv_of_u8
   exactOrNilEnv_exact exactOrNilEnv_imp fitsEnv_exactOrNil)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplay
  (spqrErrorPrefixedExactEvs spqrErrorPrefixedExactEvs_mem_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux (spqrErrorCellsAt)
open LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag (SpqrErrorValidTag)
open VerifiedLibraries.RustStd
  (fmtArgumentsAt fmtRef32 fmtRef8 fmtRefStr fmtRefString fmtSrcBytes)

/-! ## 1. Pure Guard, Narrowed `withLsRet` Wrappers, Exact `fs`/`trace` Wrapper, and Stub Helpers -/

/-- `seg[1]` internal leaf blocks inside `P_sub` of `lsFmtWriteSym`:
    - the 5 `<String as Display>::fmt` shims `[121, 191, 216, 498, 537]`,
    - Block `214` (`<DeviceId as Display>::fmt`) and Block `217` (`<NonZero<u8> as Display>::fmt`),
    - the 3 crate-local copies of `allocMultiLib` `stringWriterKeep` (`B01, B02, B06, B07`:
      `do_reserve_and_handle`, `finish_grow`, `String::write_char`, `String::write_str`):
      `.libsignalSession` `[157, 160, 181, 182]`, `.cliRatchet` `[460, 465, 488, 489]`,
      `.cliHandshake` `[517, 522, 533, 534]`.
    Note: Block `215` (`<ProtocolAddress as Display>::fmt`, the caller of `lsFmtWriteSym`) and all
    other `seg[1]` caller blocks are strictly excluded (`isFmtWriteInternalBlock 215 = false`). -/
@[expose] def cliFmtWriteInternalBlocks : List Nat :=
  [121, 157, 160, 181, 182, 191, 214, 216, 217, 460, 465, 488, 489, 498, 517, 522, 533, 534, 537]

@[expose] def isFmtWriteInternalBlock (j : Nat) : Bool :=
  j == 121 || j == 157 || j == 160 || j == 181 || j == 182 ||
    j == 191 || j == 214 || j == 216 || j == 217 ||
    j == 460 || j == 465 || j == 488 || j == 489 || j == 498 ||
    j == 517 || j == 522 || j == 533 || j == 534 || j == 537

/-- `seg[1]` internal leaf blocks inside `P_sub` of `lsFormatInnerSym`:
    `cliFmtWriteInternalBlocks` plus the 5 `<&str as Display>::fmt` shims `[78, 170, 395, 477, 529]`,
    Block `215` (`<ProtocolAddress as Display>::fmt`), `<spqr::Error as Display>::fmt` Block `412`
    with its transitive sub-formatter blocks `[392, 393, 394, 396, 397]`, and `allocMultiLib` `B04`
    (`<String as Clone>::clone`, Block `623`).
    None of these 32 leaf blocks ever invoke `lsFormatInnerSym`. -/
@[expose] def cliFormatInnerInternalBlocks : List Nat :=
  [78, 121, 157, 160, 170, 181, 182, 191, 214, 215, 216, 217,
   392, 393, 394, 395, 396, 397, 412, 460, 465, 477, 488, 489, 498,
   517, 522, 529, 533, 534, 537, 623]

@[expose] def isFormatInnerInternalBlock (j : Nat) : Bool :=
  isFmtWriteInternalBlock j ||
    j == 78 || j == 170 || j == 215 || j == 392 || j == 393 || j == 394 ||
    j == 395 || j == 396 || j == 397 || j == 412 || j == 477 || j == 529 || j == 623

/-- Caller return address for `lsFmtWriteSym`: inside `libsignalSessionLib` blocks `0 .. 623`
    outside the 19 internal leaf blocks `cliFmtWriteInternalBlocks`. -/
@[expose] def LsRetAddrFmtWrite [LibsignalPlacement] (lr : BitVec 64) : Prop :=
  ∃ j < 624, isFmtWriteInternalBlock j = false ∧ ∃ o < lsLen j, lr = lsmpl.base j + BitVec.ofNat 64 o

/-- Caller return address for `lsFormatInnerSym`: inside `libsignalSessionLib` blocks `0 .. 623`
    outside the 32 internal leaf blocks `cliFormatInnerInternalBlocks`. -/
@[expose] def LsRetAddrFormatInner [LibsignalPlacement] (lr : BitVec 64) : Prop :=
  ∃ j < 624, isFormatInnerInternalBlock j = false ∧ ∃ o < lsLen j, lr = lsmpl.base j + BitVec.ofNat 64 o

theorem LsRetAddrFmtWrite.toLsRetAddr624 [LibsignalPlacement] {lr : BitVec 64}
    (h : LsRetAddrFmtWrite lr) : LsRetAddr624 lr := by
  rcases h with ⟨j, hj, _, o, ho, hlr⟩
  exact ⟨j, hj, o, ho, hlr⟩

theorem LsRetAddrFormatInner.toLsRetAddr624 [LibsignalPlacement] {lr : BitVec 64}
    (h : LsRetAddrFormatInner lr) : LsRetAddr624 lr := by
  rcases h with ⟨j, hj, _, o, ho, hlr⟩
  exact ⟨j, hj, o, ho, hlr⟩

@[wp_norm]
theorem lsRetAddrFmtWrite_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (hnot : isFmtWriteInternalBlock j = false) (ho : off.toNat < lsLen j) :
    LsRetAddrFmtWrite (lsmpl.base j + off) :=
  ⟨j, hj, hnot, off.toNat, ho, by simp [BitVec.ofNat_toNat]⟩

@[wp_norm]
theorem lsRetAddrFmtWrite_blockPlacement_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (hnot : isFmtWriteInternalBlock j = false) (ho : off.toNat < lsLen j) :
    LsRetAddrFmtWrite
      ((CryptoVerification.SignalSession.libsignalSessionLib.blockPlacement lsmpl j).base + off) :=
  lsRetAddrFmtWrite_base_add j off hj hnot ho

@[wp_norm]
theorem lsRetAddrFmtWrite_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (hnot : isFmtWriteInternalBlock j = false) (ho : 0 < lsLen j) :
    LsRetAddrFmtWrite (lsmpl.base j) :=
  ⟨j, hj, hnot, 0, ho, by simp⟩

@[wp_norm]
theorem lsRetAddrFmtWrite_blockPlacement_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (hnot : isFmtWriteInternalBlock j = false) (ho : 0 < lsLen j) :
    LsRetAddrFmtWrite
      ((CryptoVerification.SignalSession.libsignalSessionLib.blockPlacement lsmpl j).base) :=
  lsRetAddrFmtWrite_base_zero j hj hnot ho

@[wp_norm]
theorem lsRetAddrFormatInner_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (hnot : isFormatInnerInternalBlock j = false) (ho : off.toNat < lsLen j) :
    LsRetAddrFormatInner (lsmpl.base j + off) :=
  ⟨j, hj, hnot, off.toNat, ho, by simp [BitVec.ofNat_toNat]⟩

@[wp_norm]
theorem lsRetAddrFormatInner_blockPlacement_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (hnot : isFormatInnerInternalBlock j = false) (ho : off.toNat < lsLen j) :
    LsRetAddrFormatInner
      ((CryptoVerification.SignalSession.libsignalSessionLib.blockPlacement lsmpl j).base + off) :=
  lsRetAddrFormatInner_base_add j off hj hnot ho

@[wp_norm]
theorem lsRetAddrFormatInner_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (hnot : isFormatInnerInternalBlock j = false) (ho : 0 < lsLen j) :
    LsRetAddrFormatInner (lsmpl.base j) :=
  ⟨j, hj, hnot, 0, ho, by simp⟩

@[wp_norm]
theorem lsRetAddrFormatInner_blockPlacement_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (hnot : isFormatInnerInternalBlock j = false) (ho : 0 < lsLen j) :
    LsRetAddrFormatInner
      ((CryptoVerification.SignalSession.libsignalSessionLib.blockPlacement lsmpl j).base) :=
  lsRetAddrFormatInner_base_zero j hj hnot ho

/-- Narrow `spec.pre` with `⌜LsRetAddrFmtWrite (s.readReg64 .lr)⌝`. -/
@[expose] def withLsRetFmtWrite [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜LsRetAddrFmtWrite (s.readReg64 .lr)⌝ ∗ spec.pre x s }

/-- Narrow `spec.pre` with `⌜LsRetAddrFormatInner (s.readReg64 .lr)⌝`. -/
@[expose] def withLsRetFormatInner [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜LsRetAddrFormatInner (s.readReg64 .lr)⌝ ∗ spec.pre x s }

theorem extract_withLsRetFmtWrite [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsRetFmtWrite spec).pre x s0 ∗ R) :
    LsRetAddrFmtWrite (s0.readReg64 .lr) ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsRetFmtWrite] at hpre
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre

theorem intro_withLsRetFmtWrite [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hlr : LsRetAddrFmtWrite (s0.readReg64 .lr))
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsRetFmtWrite spec).pre x s0 ∗ R := by
  dsimp only [withLsRetFmtWrite]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hlr, hpre⟩

theorem hookOk_withLsRetFmtWrite [LibsignalPlacement] {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) :
    HookOk f (withLsRetFmtWrite spec) := by
  intro x R s0 hrun hpre hsp
  exact h x R s0 hrun (extract_withLsRetFmtWrite hpre).2 hsp

theorem hookSat_withLsRetFmtWrite [LibsignalPlacement] {α : Type}
    {H : String → Option (State → State)} {n : String} {spec : Spec α}
    (h : HookSat H n spec) :
    HookSat H n (withLsRetFmtWrite spec) := by
  rcases h with ⟨f, hfn, hok⟩
  exact ⟨f, hfn, hookOk_withLsRetFmtWrite hok⟩

theorem extract_withLsRetFormatInner [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsRetFormatInner spec).pre x s0 ∗ R) :
    LsRetAddrFormatInner (s0.readReg64 .lr) ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsRetFormatInner] at hpre
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre

theorem intro_withLsRetFormatInner [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hlr : LsRetAddrFormatInner (s0.readReg64 .lr))
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsRetFormatInner spec).pre x s0 ∗ R := by
  dsimp only [withLsRetFormatInner]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hlr, hpre⟩

theorem hookOk_withLsRetFormatInner [LibsignalPlacement] {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) :
    HookOk f (withLsRetFormatInner spec) := by
  intro x R s0 hrun hpre hsp
  exact h x R s0 hrun (extract_withLsRetFormatInner hpre).2 hsp

theorem hookSat_withLsRetFormatInner [LibsignalPlacement] {α : Type}
    {H : String → Option (State → State)} {n : String} {spec : Spec α}
    (h : HookSat H n spec) :
    HookSat H n (withLsRetFormatInner spec) := by
  rcases h with ⟨f, hfn, hok⟩
  exact ⟨f, hfn, hookOk_withLsRetFormatInner hok⟩

/-- Strengthen `spec.pre x s` with pure call/state guard `⌜G x s⌝`, keeping `post`, `onPanic`,
    `onExit`, and `onOom` definitionally unchanged. -/
@[expose] def withCallGuard {α : Type} (G : α → State → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜G x s⌝ ∗ spec.pre x s }

/-- Strengthen `spec.post` and `spec.onPanic` with `⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝`
    (with `onExit = False` and `onOom = False`), keeping `spec.pre` definitionally (`rfl`) unchanged. -/
@[expose] def withFsTraceExact {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.post x s0 sf
    onPanic := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.onPanic x s0 sf
    onExit := fun _ _ _ _ => ⌜False⌝
    onOom := fun _ _ _ => ⌜False⌝ }

/-- Clamp `fallback s0`'s `fs` and `trace` to `s0` (definitionally `rfl`-equal to
    `AllocGhostLinkTransfer.keepFsTrace`). -/
@[expose] def keepFsTraceFmt (fallback : State → State) (s0 : State) : State :=
  let sf := fallback s0
  { sf with fs := s0.fs, trace := s0.trace }

private theorem keepFsTraceFmt_fmtWriteHook0 (s0 : State) :
    keepFsTraceFmt fmtWriteHook0 s0 = fmtWriteHook0 s0 := by
  cases s0; rfl

private theorem keepFsTraceFmt_formatInnerHook0 (s0 : State) :
    keepFsTraceFmt formatInnerHook0 s0 = formatInnerHook0 s0 := by
  cases s0; rfl

private theorem vmPreserved_fmtWriteHook0 (s0 : State) :
    VmPreserved s0 (fmtWriteHook0 s0) := by
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, FdsHiFrame.of_fs_eq rfl⟩

private theorem vmPreserved_formatInnerHook0 (s0 : State) :
    VmPreserved s0 (formatInnerHook0 s0) := by
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, ?_, FdsHiFrame.of_fs_eq rfl⟩
  intro a
  exact congrFun
    (LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.perm_writeVecHeader
      s0.mem (s0.readReg64 .x8) 0#64 1#64 0#64) a

/-! ## 2. `[LibsignalPlacement]`-Native Symbol, Block, and Template Constants -/

/-- Mangled `libsignal_session` extern symbols for `u8` and `u32` `Display::fmt`. -/
abbrev lsU8DisplayFmtSym : String :=
  "_RNvXNtNtNtCskxtBwYRO61I_4core3fmt3num3imphNtB6_7Display3fmt"
abbrev lsU32DisplayFmtSym : String :=
  "_RNvXs8_NtNtNtCskxtBwYRO61I_4core3fmt3num3impmNtB9_7Display3fmt"

/-- Crate-local `<String as core::fmt::Write>` `.rodata` vtable symbols in `libsignalSessionLib`. -/
abbrev lsLibsignalSessionStringVtableSym : String := "libsignal_session:.rodata..Lanon.161"
abbrev lsCliRatchetStringVtableSym : String := "libsignal_cli_ratchet:.rodata..Lanon.161"
abbrev lsCliHandshakeStringVtableSym : String := "libsignal_cli_handshake:.rodata..Lanon.115"

/-- Internal `libsignalSessionLib` block indices for `DeviceId`, `ProtocolAddress`, `NonZero<u8>`,
    and `spqr::Error` `Display::fmt`. -/
@[expose] def lsDeviceIdDisplayBlock : Nat := 214
@[expose] def lsProtocolAddressDisplayBlock : Nat := 215
@[expose] def lsNonZeroU8DisplayBlock : Nat := 217
@[expose] def lsSpqrErrorDisplayBlock : Nat := 412

/-- All 5 crate-local `<String as Display>::fmt` 20-byte shim blocks in `libsignalSessionLib`. -/
@[expose] def cliStringDisplayShimBlocks : List Nat := [121, 191, 216, 498, 537]

/-- All 5 crate-local 20-byte `&str`-forwarding `Display::fmt` shim blocks in `libsignalSessionLib`
    (block `78` `<InvalidSessionError as Display>::fmt` and `<&str as Display>::fmt` shims
    `170, 395, 477, 529`). -/
@[expose] def cliStrRefDisplayShimBlocks : List Nat := [78, 170, 395, 477, 529]

/-- Template bytes `[0xc0, 0x01, '.', 0xc0, 0x00]` of `"{}.{}"`. -/
@[expose] def dotTplBytes : List (BitVec 8) :=
  [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]

/-- Template bytes `[0xc0, 0x00]` of `"{}"`. -/
@[expose] def oneArgTplBytes : List (BitVec 8) :=
  [0xc0#8, 0x00#8]

/-- Template bytes `[len] ++ pfxBs ++ [0xc0, 0x00]` of `"<pfxBs>{}"` (`1 ≤ pfxBs.length ≤ 127`). -/
@[expose] def prefixedOneArgTplBytes (pfxBs : List (BitVec 8)) : List (BitVec 8) :=
  [BitVec.ofNat 8 pfxBs.length] ++ pfxBs ++ [0xc0#8, 0x00#8]

/-! ## 3. `core::fmt::write` (`<ProtocolAddress as Display>::fmt`) Call Descriptor & Contracts -/

/-- Crate-local `<String as core::fmt::Write>` `.rodata` vtable selector in `libsignalSessionLib`. -/
inductive CliFmtWriteVtableKind where
  | libsignalSession
  | cliRatchet
  | cliHandshake
  deriving DecidableEq, Repr

/-- `.rodata` symbol name for `k`. -/
@[expose] def CliFmtWriteVtableKind.vtableSym : CliFmtWriteVtableKind → String
  | .libsignalSession => lsLibsignalSessionStringVtableSym
  | .cliRatchet => lsCliRatchetStringVtableSym
  | .cliHandshake => lsCliHandshakeStringVtableSym

/-- Resolved `[LibsignalPlacement]` `.rodata` address `lsρ k.vtableSym` passed in `x1`. -/
@[expose] def CliFmtWriteVtableKind.vtableAddr [LibsignalPlacement]
    (k : CliFmtWriteVtableKind) : BitVec 64 :=
  lsρ k.vtableSym

/-- Pure `Type 0` call descriptor for `core::fmt::write` on `"{}.{}"` (`<ProtocolAddress as Display>::fmt`,
    Block `215`), with `dev : BitVec 8` (`AddrGhost.device`) formatted via Block `214`
    (`<DeviceId as Display>::fmt` → Block `217` `<NonZero<u8> as Display>::fmt` → `u8::fmt`). -/
structure CliFmtWriteProtoAddrCall where
  v : BitVec 64
  cap0 : BitVec 64
  ptr0 : BitVec 64
  x2 : BitVec 64
  x3 : BitVec 64
  namePtr : BitVec 64
  nameCap : BitVec 64
  nameDataPtr : BitVec 64
  shimBlock : Nat
  devPtr : BitVec 64
  bs : List (BitVec 8)
  nameBs : List (BitVec 8)
  argsRo : Bool
  strRefRo : Bool
  strSrcRo : Bool
  devRo : Bool
  dev : BitVec 8
  vtKind : CliFmtWriteVtableKind

/-- Exact `AllocEvent` list emitted by `core::fmt::write` on `c`. -/
@[expose] def CliFmtWriteProtoAddrCall.exactEvs (c : CliFmtWriteProtoAddrCall) :
    List AllocEvent :=
  fmtWriteKnownEvents c.bs.length c.cap0
    [c.nameBs.length, 1, (formatDecimalNat c.dev.toNat).length]

/-- Argument `(ptr, fmtFn)` pairs passed by `<ProtocolAddress as Display>::fmt` (Block `215`). -/
@[expose] def CliFmtWriteProtoAddrCall.args [LibsignalPlacement]
    (c : CliFmtWriteProtoAddrCall) : List (BitVec 64 × BitVec 64) :=
  [(c.namePtr, lsmpl.base c.shimBlock), (c.devPtr, lsmpl.base lsDeviceIdDisplayBlock)]

/-- Formattee memory footprint of `c` (zero `.rodata` assertions). -/
@[expose] def CliFmtWriteProtoAddrCall.clientSep (c : CliFmtWriteProtoAddrCall) : SepProp :=
  (fmtRefString c.strRefRo c.namePtr c.nameCap c.nameDataPtr (BitVec.ofNat 64 c.nameBs.length) ∗
    fmtSrcBytes c.strSrcRo c.nameDataPtr c.nameBs) ∗
  fmtRef8 c.devRo c.devPtr c.dev

/-- `[LibsignalPlacement]`-native `extHookStack` contract for `core::fmt::write` on `"{}.{}"`
    (`<ProtocolAddress as Display>::fmt`), parameterized by `EnvOf` with existential output bytes
    `∃∗ bs', vecU8 A.repAlloc c.v bs'` in `.post` and zero `.rodata` obligations in `.pre`. -/
@[expose] def cliFmtWriteProtoAddrSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EnvOf : CliFmtWriteProtoAddrCall → List AllocEvent → Prop) :
    Spec (CliFmtWriteProtoAddrCall × M.σ) where
  pre := fun (c, st0) s =>
    ⌜s.readReg64 .x0 = c.v ∧ s.readReg64 .x1 = c.vtKind.vtableAddr ∧
      s.readReg64 .x2 = c.x2 ∧ s.readReg64 .x3 = c.x3 ∧
      c.shimBlock ∈ cliStringDisplayShimBlocks ∧
      c.x3.getLsbD 0 = false ∧ c.nameBs.length < 2 ^ 60 ∧
      FitsEnv M lim st0 (EnvOf c) ∧ EnvOf c c.exactEvs⌝ ∗
    vecU8At A.repAlloc c.v c.cap0 c.ptr0 c.bs ∗
    fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
    c.clientSep ∗
    A.pool lim st0 s ∗ stackAt s.sp extHookStack
  post := fun (c, st0) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bs' : List (BitVec 8),
      ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
        sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ EnvOf c evs⌝ ∗
      vecU8 A.repAlloc c.v bs' ∗
      fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
      c.clientSep ∗
      A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack

/-- Placed `withLsRetFmtWrite`-guarded `core::fmt::write` `<ProtocolAddress as Display>::fmt`
    contract at arbitrary caller `Env`. -/
@[expose] def fmtWriteProtoAddrLsEnvSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop) :
    Spec (CliFmtWriteProtoAddrCall × M.σ) :=
  withLsRetFmtWrite (cliFmtWriteProtoAddrSpec M A lim (fun _ => Env))

/-- Canonical CLI placed `core::fmt::write` `<ProtocolAddress as Display>::fmt` contract
    (`Env := CliFmtWriteEnv`). -/
@[expose] def fmtWriteProtoAddrCliLsSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (CliFmtWriteProtoAddrCall × M.σ) :=
  fmtWriteProtoAddrLsEnvSpec M A lim CliFmtWriteEnv

/-- On an empty initial buffer (`c.cap0 = 0#64`, `c.bs = []`) with `c.nameBs.length ≤ 40`,
    `c.exactEvs` lies in `CliFmtWriteEnv`. -/
theorem cliFmtWriteProtoAddr_exactEvs_mem_cliFmtWriteEnv (c : CliFmtWriteProtoAddrCall)
    (hcap : c.cap0 = 0#64) (hbs : c.bs = []) (hlen : c.nameBs.length ≤ 40) :
    CliFmtWriteEnv c.exactEvs := by
  have ⟨hd1, hd3⟩ := formatDecimalNat_u8_length c.dev
  refine cliFmtWriteEnv_of_addr0 hlen hd1 (by omega) ?_
  unfold FmtWriteAddrEnv CliFmtWriteProtoAddrCall.exactEvs
  rw [hcap, hbs]
  rfl

/-- Stub fallback `keepFsTraceFmt fmtWriteHook0` satisfies
    `withFsTraceExact (cliFmtWriteProtoAddrSpec ...)` whenever `EnvOf c []` holds. -/
theorem fmtWriteHook0_cliProtoAddr_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {EnvOf : CliFmtWriteProtoAddrCall → List AllocEvent → Prop}
    (hNil : ∀ c, EnvOf c []) :
    HookOk (keepFsTraceFmt fmtWriteHook0)
      (withFsTraceExact (cliFmtWriteProtoAddrSpec M A lim EnvOf)) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre _hsp
  rw [keepFsTraceFmt_fmtWriteHook0]
  dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hm0⟩
  have hret : Returned s0 (fmtWriteHook0 s0) := ⟨rfl, rfl, hrun⟩
  have hacp : AllocCallPreserved s0 (fmtWriteHook0 s0) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpool :
      A.pool lim (M.stepEvents [] st0) (fmtWriteHook0 s0) = A.pool lim st0 s0 := by
    rw [AllocCostModel.stepEvents_nil]
    exact A.pool_transport lim st0 s0 (fmtWriteHook0 s0) (vmPreserved_fmtWriteHook0 s0)
  have hw0 : ((fmtWriteHook0 s0).readReg64 .x0).setWidth 32 = 0#32 := by
    simp [fmtWriteHook0, retHook]
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl,
    Or.inl ⟨hret, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  change s0.mem ⊨ _
  refine Satisfies.mono (sepConj_mono_left ?_) hm0
  dsimp only
  rw [pure_sepConj_of_true ⟨rfl, rfl⟩]
  refine Entails.sepExists_right ([] : List AllocEvent) ?_
  refine Entails.sepExists_right c.bs ?_
  rw [hpool, pure_sepConj_of_true ⟨hw0, hacp, rfl, rfl, hNil c⟩]
  have hvec : vecU8At A.repAlloc c.v c.cap0 c.ptr0 c.bs ⊢ vecU8 A.repAlloc c.v c.bs :=
    Entails.sepExists_right c.cap0 (Entails.sepExists_right c.ptr0 (Entails.refl _))
  refine Entails.trans (sepConj_mono_left hvec) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Plain `fmtWriteHook0` satisfies `cliFmtWriteProtoAddrSpec` whenever `EnvOf c []` holds. -/
theorem fmtWriteHook0_cliProtoAddr_plain_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {EnvOf : CliFmtWriteProtoAddrCall → List AllocEvent → Prop}
    (hNil : ∀ c, EnvOf c []) :
    HookOk fmtWriteHook0 (cliFmtWriteProtoAddrSpec M A lim EnvOf) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre hsp
  have h0 := fmtWriteHook0_cliProtoAddr_ok M A lim hNil (c, st0) R₀ s0 hrun hpre hsp
  rw [keepFsTraceFmt_fmtWriteHook0] at h0
  rcases h0 with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withFsTraceExact] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom; rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem fmtWriteHook0_protoAddrLsEnv_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {Env : List AllocEvent → Prop}
    (hNil : Env []) :
    HookOk fmtWriteHook0 (fmtWriteProtoAddrLsEnvSpec M A lim Env) :=
  hookOk_withLsRetFmtWrite (fmtWriteHook0_cliProtoAddr_plain_ok M A lim (fun _ => hNil))

theorem fmtWriteHook0_protoAddrCliLs_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk fmtWriteHook0 (fmtWriteProtoAddrCliLsSpec M A lim) :=
  fmtWriteHook0_protoAddrLsEnv_ok M A lim CliFmtLsPlacedSpecs.cliFmtWriteEnv_nil

/-- Lift `HookOk f` from `ExactOrNilEnv c.exactEvs` to any caller `Env` containing `[]`. -/
theorem hookOk_cliFmtWriteProtoAddr_of_exactOrNil [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f
      (withFsTraceExact (cliFmtWriteProtoAddrSpec M A lim (fun c => ExactOrNilEnv c.exactEvs))))
    {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk f (withFsTraceExact (cliFmtWriteProtoAddrSpec M A lim (fun _ => Env))) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre hsp
  dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen, hFit, hEx⟩, hm0⟩
  have hpre0 : s0.mem ⊨
      (withFsTraceExact
        (cliFmtWriteProtoAddrSpec M A lim (fun c => ExactOrNilEnv c.exactEvs))).pre (c, st0) s0 ∗
        R₀ := by
    dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen,
      fitsEnv_exactOrNil hFit hEx, exactOrNilEnv_exact c.exactEvs⟩, hm0⟩
  obtain ⟨hkf, hsym, hout⟩ := hok (c, st0) R₀ s0 hrun hpre0 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hp := hpost.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1,
      exactOrNilEnv_imp hNil hEx evs hp.1.2.2.2.2⟩, hp.2⟩
  · dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withFsTraceExact] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom; rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- Monotonicity of `fmtWriteProtoAddrLsEnvSpec` from `CliFmtWriteEnv` to any wider `Env`
    when `c.exactEvs ∈ CliFmtWriteEnv` or via `Env₁ ⊆ Env₂` on a fixed sub-envelope. -/
theorem hookOk_fmtWriteProtoAddrLsEnv_of_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (fmtWriteProtoAddrCliLsSpec M A lim))
    {Env : List AllocEvent → Prop}
    (hSub : ∀ evs, CliFmtWriteEnv evs → Env evs) :
    HookOk f
      (withCallGuard (fun (c, _) _ => CliFmtWriteEnv c.exactEvs)
        (fmtWriteProtoAddrLsEnvSpec M A lim Env)) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre hsp
  dsimp only [withCallGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hCliEx, hpre⟩
  obtain ⟨hlr, hpreInner⟩ := extract_withLsRetFmtWrite hpre
  dsimp only [cliFmtWriteProtoAddrSpec] at hpreInner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreInner
  rcases hpreInner with ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen, hFit, _⟩, hm0⟩
  have hFitCli : FitsEnv M lim st0 CliFmtWriteEnv := fun evs hE => hFit evs (hSub evs hE)
  have hpreCli : s0.mem ⊨ (fmtWriteProtoAddrCliLsSpec M A lim).pre (c, st0) s0 ∗ R₀ := by
    refine intro_withLsRetFmtWrite hlr ?_
    dsimp only [cliFmtWriteProtoAddrSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen, hFitCli, hCliEx⟩, hm0⟩
  obtain ⟨hkf, hsym, hout⟩ := hok (c, st0) R₀ s0 hrun hpreCli hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨ec, he, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withCallGuard, fmtWriteProtoAddrLsEnvSpec, fmtWriteProtoAddrCliLsSpec,
      withLsRetFmtWrite, cliFmtWriteProtoAddrSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hSub evs hp.1.2.2.2.2⟩, hp.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ec, he, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem hookSat_fmtWriteProtoAddrLsEnv_of_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {sym : String}
    (hsat : HookSat H sym (fmtWriteProtoAddrCliLsSpec M A lim))
    {Env : List AllocEvent → Prop}
    (hSub : ∀ evs, CliFmtWriteEnv evs → Env evs) :
    HookSat H sym
      (withCallGuard (fun (c, _) _ => CliFmtWriteEnv c.exactEvs)
        (fmtWriteProtoAddrLsEnvSpec M A lim Env)) := by
  rcases hsat with ⟨f, hfn, hok⟩
  exact ⟨f, hfn, hookOk_fmtWriteProtoAddrLsEnv_of_cli hok hSub⟩

/-- Project `cliFmtWriteProtoAddrSpec.post` directly onto `fmtWriteBudgetEnvSpec.post`. -/
theorem cliFmtWriteProtoAddrSpec_post_entails_budget [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (c : CliFmtWriteProtoAddrCall) (st0 : M.σ) (s0 sf : State) :
    (cliFmtWriteProtoAddrSpec M A lim (fun _ => Env)).post (c, st0) s0 sf ⊢
    ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
      (fmtWriteBudgetEnvSpec M A lim Env).post (c.v, c.bs, st0) s0 sf ∗
      fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
      c.clientSep := by
  dsimp only [cliFmtWriteProtoAddrSpec, fmtWriteBudgetEnvSpec]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_elim fun bs' => ?_
  refine Entails.pure_left fun ⟨hw0, hacp, hfs, htr, hEnv⟩ => ?_
  refine Entails.pure_right ⟨hacp, hfs⟩ ?_
  have hex : vecU8 A.repAlloc c.v bs' ⊢ ∃∗ b : List (BitVec 8), vecU8 A.repAlloc c.v b :=
    Entails.sepExists_right bs' (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hex) ?_
  have hinner :
      (∃∗ b : List (BitVec 8), vecU8 A.repAlloc c.v b) ∗
        (fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
          (c.clientSep ∗
            (A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack))) ⊢
      (⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ Env evs⌝ ∗
        (∃∗ b : List (BitVec 8), vecU8 A.repAlloc c.v b) ∗
        A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack) ∗
        fmtArgumentsAt c.argsRo c.x2 c.x3 dotTplBytes c.args ∗
        c.clientSep := by
    rw [pure_sepConj_of_true ⟨hw0, htr, hEnv⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  refine Entails.trans hinner ?_
  exact sepConj_mono_left (Entails.sepExists_right evs (Entails.refl _))

/-! ## 4. 13-Shape `[LibsignalPlacement]`-Native `alloc::fmt::format::format_inner` Contracts -/

/-- The 13 concrete `[LibsignalPlacement]`-native `alloc::fmt::format::format_inner` call shapes in
    `libsignal-cli` (pure `Type 0` data; no `Prop`, `Env`, or `.rodata` fields). -/
inductive CliFormatInnerLsShape where
  | empty
  | fromStr (litBs : List (BitVec 8))
  | lit0 (litBs : List (BitVec 8))
  | u8Display (valPtr : BitVec 64) (valRo : Bool) (val : BitVec 8)
  | u32Display (valPtr : BitVec 64) (valRo : Bool) (val : BitVec 32)
  | u8DisplayPrefixed (pfxBs : List (BitVec 8))
      (valPtr : BitVec 64) (valRo : Bool) (val : BitVec 8)
  | strRefDisplayShim (shimBlock : Nat)
      (valPtr strPtr : BitVec 64) (sbs : List (BitVec 8)) (refRo srcRo : Bool)
  | strRefDisplayPrefixedShim (pfxBs : List (BitVec 8)) (shimBlock : Nat)
      (valPtr strPtr : BitVec 64) (sbs : List (BitVec 8)) (refRo srcRo : Bool)
  | cliAesErrDisplayPrefixedShim (pfxBs : List (BitVec 8)) (shimBlock : Nat)
      (valPtr : BitVec 64) (isStr1 : Bool) (refRo : Bool)
  | spqrErrorDisplayPrefixed (pfxBs : List (BitVec 8)) (errPtr : BitVec 64)
      (d b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
  | protoAddrDisplay (addrPtr nameCap nameDataPtr : BitVec 64)
      (nameBs : List (BitVec 8)) (strRefRo strSrcRo devRo : Bool) (dev : BitVec 8)
  | dottedStringDevIdShim (shimBlock : Nat)
      (namePtr nameCap nameDataPtr devPtr : BitVec 64)
      (nameBs : List (BitVec 8)) (strRefRo strSrcRo devRo : Bool) (dev : BitVec 8)
  | dottedStringU32Shim (shimBlock : Nat)
      (namePtr nameCap nameDataPtr devPtr : BitVec 64)
      (nameBs : List (BitVec 8)) (strRefRo strSrcRo devRo : Bool) (dev : BitVec 32)

/-- Pure `Type 0` call descriptor for `alloc::fmt::format::format_inner`. -/
structure CliFormatInnerLsCall where
  ret : BitVec 64
  x0 : BitVec 64
  x1 : BitVec 64
  argsRo : Bool
  shape : CliFormatInnerLsShape

/-- Exact `AllocEvent` list emitted by `format_inner` on `c`. -/
@[expose] def CliFormatInnerLsCall.exactEvs (c : CliFormatInnerLsCall) : List AllocEvent :=
  match c.shape with
  | .empty => []
  | .fromStr litBs => if litBs.length = 0 then [] else rustAllocEvents litBs.length 1
  | .lit0 litBs => formatInnerKnownEvents (2 * litBs.length) [litBs.length]
  | .u8Display _ _ val => formatInnerKnownEvents 0 [(formatDecimalNat val.toNat).length]
  | .u32Display _ _ val => formatInnerKnownEvents 0 [(formatDecimalNat val.toNat).length]
  | .u8DisplayPrefixed pfxBs _ _ val =>
      formatInnerKnownEvents (2 * pfxBs.length)
        [pfxBs.length, (formatDecimalNat val.toNat).length]
  | .strRefDisplayShim _ _ _ sbs _ _ => formatInnerKnownEvents 0 [sbs.length]
  | .strRefDisplayPrefixedShim pfxBs _ _ _ sbs _ _ =>
      formatInnerKnownEvents (2 * pfxBs.length) [pfxBs.length, sbs.length]
  | .cliAesErrDisplayPrefixedShim pfxBs _ _ isStr1 _ =>
      formatInnerKnownEvents (2 * pfxBs.length) [pfxBs.length, if isStr1 then 51 else 17]
  | .spqrErrorDisplayPrefixed pfxBs _ d b1 u1 q1 q2 =>
      spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2
  | .protoAddrDisplay _ _ _ nameBs _ _ _ dev =>
      formatInnerKnownEvents 0 [nameBs.length, 1, (formatDecimalNat dev.toNat).length]
  | .dottedStringDevIdShim _ _ _ _ _ nameBs _ _ _ dev =>
      formatInnerKnownEvents 0 [nameBs.length, 1, (formatDecimalNat dev.toNat).length]
  | .dottedStringU32Shim _ _ _ _ _ nameBs _ _ _ dev =>
      formatInnerKnownEvents 0 [nameBs.length, 1, (formatDecimalNat dev.toNat).length]

/-- Template bytes `tpl` expected by `fmtArgumentsAt` for `c`. -/
@[expose] def CliFormatInnerLsCall.tpl (c : CliFormatInnerLsCall) : List (BitVec 8) :=
  match c.shape with
  | .empty => [0x00#8]
  | .fromStr litBs => litBs
  | .lit0 litBs => [BitVec.ofNat 8 litBs.length] ++ litBs ++ [0x00#8]
  | .u8Display _ _ _ => oneArgTplBytes
  | .u32Display _ _ _ => oneArgTplBytes
  | .u8DisplayPrefixed pfxBs _ _ _ => prefixedOneArgTplBytes pfxBs
  | .strRefDisplayShim _ _ _ _ _ _ => oneArgTplBytes
  | .strRefDisplayPrefixedShim pfxBs _ _ _ _ _ _ => prefixedOneArgTplBytes pfxBs
  | .cliAesErrDisplayPrefixedShim pfxBs _ _ _ _ => prefixedOneArgTplBytes pfxBs
  | .spqrErrorDisplayPrefixed pfxBs _ _ _ _ _ _ => prefixedOneArgTplBytes pfxBs
  | .protoAddrDisplay _ _ _ _ _ _ _ _ => oneArgTplBytes
  | .dottedStringDevIdShim _ _ _ _ _ _ _ _ _ _ => dotTplBytes
  | .dottedStringU32Shim _ _ _ _ _ _ _ _ _ _ => dotTplBytes

/-- Argument `(ptr, fmtFn)` pairs expected by `fmtArgumentsAt` for `c` under `[LibsignalPlacement]`. -/
@[expose] def CliFormatInnerLsCall.args [LibsignalPlacement] (c : CliFormatInnerLsCall) :
    List (BitVec 64 × BitVec 64) :=
  match c.shape with
  | .empty => []
  | .fromStr _ => []
  | .lit0 _ => []
  | .u8Display valPtr _ _ => [(valPtr, lsρ lsU8DisplayFmtSym)]
  | .u32Display valPtr _ _ => [(valPtr, lsρ lsU32DisplayFmtSym)]
  | .u8DisplayPrefixed _ valPtr _ _ => [(valPtr, lsρ lsU8DisplayFmtSym)]
  | .strRefDisplayShim shimBlock valPtr _ _ _ _ => [(valPtr, lsmpl.base shimBlock)]
  | .strRefDisplayPrefixedShim _ shimBlock valPtr _ _ _ _ => [(valPtr, lsmpl.base shimBlock)]
  | .cliAesErrDisplayPrefixedShim _ shimBlock valPtr _ _ => [(valPtr, lsmpl.base shimBlock)]
  | .spqrErrorDisplayPrefixed _ errPtr _ _ _ _ _ => [(errPtr, lsmpl.base lsSpqrErrorDisplayBlock)]
  | .protoAddrDisplay addrPtr _ _ _ _ _ _ _ => [(addrPtr, lsmpl.base lsProtocolAddressDisplayBlock)]
  | .dottedStringDevIdShim shimBlock namePtr _ _ devPtr _ _ _ _ _ =>
      [(namePtr, lsmpl.base shimBlock), (devPtr, lsmpl.base lsDeviceIdDisplayBlock)]
  | .dottedStringU32Shim shimBlock namePtr _ _ devPtr _ _ _ _ _ =>
      [(namePtr, lsmpl.base shimBlock), (devPtr, lsρ lsU32DisplayFmtSym)]

/-- Formattee memory assertion for `c` (zero `.rodata` obligations). -/
@[expose] def CliFormatInnerLsCall.clientSep (c : CliFormatInnerLsCall) : SepProp :=
  match c.shape with
  | .empty => emp
  | .fromStr _ => emp
  | .lit0 _ => emp
  | .u8Display valPtr valRo val => fmtRef8 valRo valPtr val
  | .u32Display valPtr valRo val => fmtRef32 valRo valPtr val
  | .u8DisplayPrefixed _ valPtr valRo val => fmtRef8 valRo valPtr val
  | .strRefDisplayShim _ valPtr strPtr sbs refRo srcRo =>
      fmtRefStr refRo valPtr strPtr (BitVec.ofNat 64 sbs.length) ∗
        fmtSrcBytes srcRo strPtr sbs
  | .strRefDisplayPrefixedShim _ _ valPtr strPtr sbs refRo srcRo =>
      fmtRefStr refRo valPtr strPtr (BitVec.ofNat 64 sbs.length) ∗
        fmtSrcBytes srcRo strPtr sbs
  | .cliAesErrDisplayPrefixedShim _ _ valPtr isStr1 refRo =>
      fmtRefStr refRo valPtr
        (if isStr1 then cliAesDecErrStr1Addr else cliAesDecErrStr2Addr)
        (if isStr1 then 0x33#64 else 0x11#64)
  | .spqrErrorDisplayPrefixed _ errPtr d b1 u1 q1 q2 =>
      spqrErrorCellsAt errPtr d b1 u1 q1 q2
  | .protoAddrDisplay addrPtr nameCap nameDataPtr nameBs strRefRo strSrcRo devRo dev =>
      (fmtRefString strRefRo addrPtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
        fmtSrcBytes strSrcRo nameDataPtr nameBs) ∗
      fmtRef8 devRo (addrPtr + 24#64) dev
  | .dottedStringDevIdShim _ namePtr nameCap nameDataPtr devPtr nameBs strRefRo strSrcRo devRo dev =>
      (fmtRefString strRefRo namePtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
        fmtSrcBytes strSrcRo nameDataPtr nameBs) ∗
      fmtRef8 devRo devPtr dev
  | .dottedStringU32Shim _ namePtr nameCap nameDataPtr devPtr nameBs strRefRo strSrcRo devRo dev =>
      (fmtRefString strRefRo namePtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
        fmtSrcBytes strSrcRo nameDataPtr nameBs) ∗
      fmtRef32 devRo devPtr dev

/-- Pure side-conditions on `(c.x1, c.shape)` required by the 13 `format_inner` specializations. -/
@[expose] def CliFormatInnerLsCall.shapePreOk (c : CliFormatInnerLsCall) : Prop :=
  match c.shape with
  | .empty => c.x1 = 0#64
  | .fromStr litBs =>
      c.x1.getLsbD 0 = true ∧ litBs.length = (c.x1 >>> 1).toNat ∧ litBs.length < 2 ^ 60
  | .lit0 litBs => c.x1 = 0#64 ∧ 1 ≤ litBs.length ∧ litBs.length ≤ 127
  | .u8Display _ _ _ => c.x1.getLsbD 0 = false
  | .u32Display _ _ _ => c.x1.getLsbD 0 = false
  | .u8DisplayPrefixed pfxBs _ _ _ =>
      c.x1.getLsbD 0 = false ∧ 1 ≤ pfxBs.length ∧ pfxBs.length ≤ 127
  | .strRefDisplayShim shimBlock _ _ sbs _ _ =>
      shimBlock ∈ cliStrRefDisplayShimBlocks ∧ c.x1.getLsbD 0 = false ∧ sbs.length < 2 ^ 60
  | .strRefDisplayPrefixedShim pfxBs shimBlock _ _ sbs _ _ =>
      shimBlock ∈ cliStrRefDisplayShimBlocks ∧ c.x1.getLsbD 0 = false ∧
      1 ≤ pfxBs.length ∧ pfxBs.length ≤ 127 ∧ sbs.length < 2 ^ 60
  | .cliAesErrDisplayPrefixedShim pfxBs shimBlock _ _ _ =>
      shimBlock ∈ cliStrRefDisplayShimBlocks ∧ c.x1.getLsbD 0 = false ∧
      1 ≤ pfxBs.length ∧ pfxBs.length ≤ 127
  | .spqrErrorDisplayPrefixed pfxBs _ d _ _ _ _ =>
      c.x1.getLsbD 0 = false ∧ SpqrErrorValidTag d ∧ 1 ≤ pfxBs.length ∧ pfxBs.length ≤ 127
  | .protoAddrDisplay _ _ _ nameBs _ _ _ _ =>
      c.x1.getLsbD 0 = false ∧ nameBs.length < 2 ^ 60
  | .dottedStringDevIdShim shimBlock _ _ _ _ nameBs _ _ _ _ =>
      shimBlock ∈ cliStringDisplayShimBlocks ∧ c.x1.getLsbD 0 = false ∧ nameBs.length < 2 ^ 60
  | .dottedStringU32Shim shimBlock _ _ _ _ nameBs _ _ _ _ =>
      shimBlock ∈ cliStringDisplayShimBlocks ∧ c.x1.getLsbD 0 = false ∧ nameBs.length < 2 ^ 60

/-- Unified 13-shape `[LibsignalPlacement]`-native `extHookStack` contract for
    `alloc::fmt::format::format_inner`, with no `.rodata` assertions in `.pre` and existential
    `∃∗ bs', vecU8 A.repAlloc c.ret bs'` in `.post`. -/
@[expose] def cliFormatInnerLsCallSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EnvOf : CliFormatInnerLsCall → List AllocEvent → Prop) :
    Spec (CliFormatInnerLsCall × M.σ) where
  pre := fun (c, st0) s =>
    ⌜s.readReg64 .x8 = c.ret ∧ s.readReg64 .x0 = c.x0 ∧ s.readReg64 .x1 = c.x1 ∧
      c.shapePreOk ∧ FitsEnv M lim st0 (EnvOf c) ∧ EnvOf c c.exactEvs⌝ ∗
    fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
    memRegion c.ret 24 ∗
    c.clientSep ∗
    A.pool lim st0 s ∗ stackAt s.sp extHookStack
  post := fun (c, st0) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bs' : List (BitVec 8),
      ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ EnvOf c evs⌝ ∗
      vecU8 A.repAlloc c.ret bs' ∗
      fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
      c.clientSep ∗
      A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack

/-- Placed `withLsRetFormatInner`-guarded `alloc::fmt::format::format_inner` call-descriptor contract
    at arbitrary caller `Env`. -/
@[expose] def formatInnerCallLsEnvSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop) :
    Spec (CliFormatInnerLsCall × M.σ) :=
  withLsRetFormatInner (cliFormatInnerLsCallSpec M A lim (fun _ => Env))

/-- Canonical CLI placed `alloc::fmt::format::format_inner` call-descriptor contract
    (`Env := CliFormatInnerEnv`). -/
@[expose] def formatInnerCallCliLsSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (CliFormatInnerLsCall × M.σ) :=
  formatInnerCallLsEnvSpec M A lim CliFormatInnerEnv

/-! ### Per-Shape `CliFormatInnerEnv` Membership Lemmas -/

theorem cliFormatInnerLsCall_exactEvs_mem_empty (ret x0 x1 : BitVec 64) (argsRo : Bool) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo, shape := .empty } :
        CliFormatInnerLsCall).exactEvs :=
  cliFormatInnerEnv_nil

theorem cliFormatInnerLsCall_exactEvs_mem_fromStr (ret x0 x1 : BitVec 64) (argsRo : Bool)
    (litBs : List (BitVec 8)) (hlen : litBs.length ≤ 127) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo, shape := .fromStr litBs } :
        CliFormatInnerLsCall).exactEvs :=
  cliFormatInnerEnv_of_fromStr hlen rfl

theorem cliFormatInnerLsCall_exactEvs_mem_lit0 (ret x0 x1 : BitVec 64) (argsRo : Bool)
    (litBs : List (BitVec 8)) (hlo : 1 ≤ litBs.length) (hhi : litBs.length ≤ 127) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo, shape := .lit0 litBs } :
        CliFormatInnerLsCall).exactEvs :=
  cliFormatInnerEnv_of_shortLit hlo hhi rfl

theorem cliFormatInnerLsCall_exactEvs_mem_u8Display (ret x0 x1 valPtr : BitVec 64)
    (argsRo valRo : Bool) (val : BitVec 8) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .u8Display valPtr valRo val } : CliFormatInnerLsCall).exactEvs :=
  cliFormatInnerEnv_of_u8 val rfl

theorem cliFormatInnerLsCall_exactEvs_mem_u32Display (ret x0 x1 valPtr : BitVec 64)
    (argsRo valRo : Bool) (val : BitVec 32) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .u32Display valPtr valRo val } : CliFormatInnerLsCall).exactEvs :=
  cliFormatInnerEnv_of_u32 val rfl

theorem cliFormatInnerLsCall_exactEvs_mem_u8DisplayPrefixed (ret x0 x1 valPtr : BitVec 64)
    (argsRo valRo : Bool) (pfxBs : List (BitVec 8)) (val : BitVec 8)
    (hpfx : pfxBs.length ≤ 40) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .u8DisplayPrefixed pfxBs valPtr valRo val } :
        CliFormatInnerLsCall).exactEvs := by
  have ⟨_, hd3⟩ := formatDecimalNat_u8_length val
  refine cliFormatInnerEnv_of_prefixed
    ⟨2 * pfxBs.length, pfxBs.length, by omega, by omega,
     [(formatDecimalNat val.toNat).length], by simp, ?_, rfl⟩
  simp only [List.sum_cons, List.sum_nil]
  omega

theorem cliFormatInnerLsCall_exactEvs_mem_strRefDisplayShim (ret x0 x1 valPtr strPtr : BitVec 64)
    (argsRo refRo srcRo : Bool) (shimBlock : Nat) (sbs : List (BitVec 8))
    (hlen : sbs.length ≤ 127) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .strRefDisplayShim shimBlock valPtr strPtr sbs refRo srcRo } :
        CliFormatInnerLsCall).exactEvs :=
  cliFormatInnerEnv_of_single hlen rfl

theorem cliFormatInnerLsCall_exactEvs_mem_strRefDisplayPrefixedShim
    (ret x0 x1 valPtr strPtr : BitVec 64) (argsRo refRo srcRo : Bool)
    (pfxBs sbs : List (BitVec 8)) (shimBlock : Nat)
    (hpfx : pfxBs.length ≤ 40) (htot : pfxBs.length + sbs.length ≤ 120) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .strRefDisplayPrefixedShim pfxBs shimBlock valPtr strPtr sbs refRo srcRo } :
        CliFormatInnerLsCall).exactEvs := by
  refine cliFormatInnerEnv_of_prefixed
    ⟨2 * pfxBs.length, pfxBs.length, by omega, by omega, [sbs.length], by simp, ?_, rfl⟩
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- Convert the 2-way `(p, len)` disjunction emitted by `cliAesDecBudgetSpecErrRo` on `.none`
    into a `Bool` selector `isStr1` matching `.cliAesErrDisplayPrefixedShim`. -/
theorem exists_cliAesErrIsStr1_of_disj {p len : BitVec 64}
    (h : (p = cliAesDecErrStr1Addr ∧ len = 0x33#64) ∨
         (p = cliAesDecErrStr2Addr ∧ len = 0x11#64)) :
    ∃ isStr1 : Bool,
      p = (if isStr1 then cliAesDecErrStr1Addr else cliAesDecErrStr2Addr) ∧
      len = (if isStr1 then 0x33#64 else 0x11#64) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨true, rfl, rfl⟩
  · exact ⟨false, rfl, rfl⟩

theorem cliFormatInnerLsCall_exactEvs_mem_cliAesErrDisplayPrefixedShim
    (ret x0 x1 valPtr : BitVec 64) (argsRo isStr1 refRo : Bool)
    (pfxBs : List (BitVec 8)) (shimBlock : Nat)
    (hpfx : pfxBs.length ≤ 40) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .cliAesErrDisplayPrefixedShim pfxBs shimBlock valPtr isStr1 refRo } :
        CliFormatInnerLsCall).exactEvs := by
  refine cliFormatInnerEnv_of_prefixed
    ⟨2 * pfxBs.length, pfxBs.length, by omega, by omega,
     [if isStr1 then 51 else 17], by simp, ?_, rfl⟩
  cases isStr1 <;> simp <;> omega

theorem cliFormatInnerLsCall_exactEvs_mem_spqrErrorDisplayPrefixed
    (ret x0 x1 errPtr : BitVec 64) (argsRo : Bool) (pfxBs : List (BitVec 8))
    (d b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hlo : 24 ≤ pfxBs.length) (hhi : pfxBs.length ≤ 40) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .spqrErrorDisplayPrefixed pfxBs errPtr d b1 u1 q1 q2 } :
        CliFormatInnerLsCall).exactEvs :=
  spqrErrorPrefixedExactEvs_mem_cli hlo hhi

theorem cliFormatInnerLsCall_exactEvs_mem_protoAddrDisplay
    (ret x0 x1 addrPtr nameCap nameDataPtr : BitVec 64)
    (argsRo strRefRo strSrcRo devRo : Bool) (nameBs : List (BitVec 8)) (dev : BitVec 8)
    (hlen : nameBs.length ≤ 40) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .protoAddrDisplay addrPtr nameCap nameDataPtr nameBs
           strRefRo strSrcRo devRo dev } : CliFormatInnerLsCall).exactEvs := by
  have ⟨hd1, hd3⟩ := formatDecimalNat_u8_length dev
  exact cliFormatInnerEnv_of_addr hlen hd1 (by omega) rfl

theorem cliFormatInnerLsCall_exactEvs_mem_dottedStringDevIdShim
    (ret x0 x1 namePtr nameCap nameDataPtr devPtr : BitVec 64)
    (argsRo strRefRo strSrcRo devRo : Bool) (shimBlock : Nat)
    (nameBs : List (BitVec 8)) (dev : BitVec 8)
    (hlen : nameBs.length ≤ 40) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .dottedStringDevIdShim shimBlock namePtr nameCap nameDataPtr devPtr nameBs
           strRefRo strSrcRo devRo dev } : CliFormatInnerLsCall).exactEvs := by
  have ⟨hd1, hd3⟩ := formatDecimalNat_u8_length dev
  exact cliFormatInnerEnv_of_addr hlen hd1 (by omega) rfl

theorem cliFormatInnerLsCall_exactEvs_mem_dottedStringU32Shim
    (ret x0 x1 namePtr nameCap nameDataPtr devPtr : BitVec 64)
    (argsRo strRefRo strSrcRo devRo : Bool) (shimBlock : Nat)
    (nameBs : List (BitVec 8)) (dev : BitVec 32)
    (hlen : nameBs.length ≤ 40) :
    CliFormatInnerEnv
      ({ ret := ret, x0 := x0, x1 := x1, argsRo := argsRo,
         shape := .dottedStringU32Shim shimBlock namePtr nameCap nameDataPtr devPtr nameBs
           strRefRo strSrcRo devRo dev } : CliFormatInnerLsCall).exactEvs := by
  have ⟨hd1, hd10⟩ := formatDecimalNat_u32_length dev
  exact cliFormatInnerEnv_of_addr hlen hd1 hd10 rfl

/-! ### Stub-Hook `HookOk`, `ExactOrNilEnv` Lift, Monotonicity, and Budget Post Projection -/

/-- Stub fallback `keepFsTraceFmt formatInnerHook0` satisfies
    `withFsTraceExact (cliFormatInnerLsCallSpec ...)` whenever `EnvOf c []` holds. -/
theorem formatInnerHook0_cliLsCallSpec_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {EnvOf : CliFormatInnerLsCall → List AllocEvent → Prop}
    (hNil : ∀ c, EnvOf c []) :
    HookOk (keepFsTraceFmt formatInnerHook0)
      (withFsTraceExact (cliFormatInnerLsCallSpec M A lim EnvOf)) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre _hsp
  rw [keepFsTraceFmt_formatInnerHook0]
  dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, _, _, _, _, _⟩, hm0⟩
  have hmReg :
      s0.mem ⊨ memRegion c.ret 24 ∗
        ((fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
          c.clientSep ∗
          A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  have hw := write_empty_vecU8 (A := A.repAlloc) hmReg
  have hmemEq : (formatInnerHook0 s0).mem = writeVecHeader s0.mem c.ret 0#64 1#64 0#64 := by
    simp [formatInnerHook0, retHook, State.setPC, State.setMem, hx8]
  have hkf : s0.mem.KeepsFrozen (formatInnerHook0 s0).mem := by
    rw [hmemEq]; exact hw.1
  have hret : Returned s0 (formatInnerHook0 s0) := ⟨rfl, rfl, hrun⟩
  have hacp : AllocCallPreserved s0 (formatInnerHook0 s0) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpool :
      A.pool lim (M.stepEvents [] st0) (formatInnerHook0 s0) = A.pool lim st0 s0 := by
    rw [AllocCostModel.stepEvents_nil]
    exact A.pool_transport lim st0 s0 (formatInnerHook0 s0) (vmPreserved_formatInnerHook0 s0)
  refine ⟨hkf, rfl,
    Or.inl ⟨hret, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  rw [hmemEq]
  have hwAssoc :
      writeVecHeader s0.mem c.ret 0#64 1#64 0#64 ⊨
        (vecU8 A.repAlloc c.ret [] ∗
          (fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
            c.clientSep ∗
            A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack)) ∗ R₀ := by
    rw [sepConj_assoc]
    exact hw.2.2
  refine Satisfies.mono (sepConj_mono_left ?_) hwAssoc
  dsimp only
  rw [pure_sepConj_of_true ⟨rfl, rfl⟩]
  refine Entails.sepExists_right ([] : List AllocEvent)
    (Entails.sepExists_right ([] : List (BitVec 8)) ?_)
  rw [hpool, pure_sepConj_of_true ⟨hacp, rfl, rfl, hNil c⟩]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Plain `formatInnerHook0` satisfies `cliFormatInnerLsCallSpec` whenever `EnvOf c []` holds. -/
theorem formatInnerHook0_cliLsCallSpec_plain_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {EnvOf : CliFormatInnerLsCall → List AllocEvent → Prop}
    (hNil : ∀ c, EnvOf c []) :
    HookOk formatInnerHook0 (cliFormatInnerLsCallSpec M A lim EnvOf) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre hsp
  have h0 := formatInnerHook0_cliLsCallSpec_ok M A lim hNil (c, st0) R₀ s0 hrun hpre hsp
  rw [keepFsTraceFmt_formatInnerHook0] at h0
  rcases h0 with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withFsTraceExact] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom; rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem formatInnerHook0_callLsEnv_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {Env : List AllocEvent → Prop}
    (hNil : Env []) :
    HookOk formatInnerHook0 (formatInnerCallLsEnvSpec M A lim Env) :=
  hookOk_withLsRetFormatInner (formatInnerHook0_cliLsCallSpec_plain_ok M A lim (fun _ => hNil))

theorem formatInnerHook0_callCliLs_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk formatInnerHook0 (formatInnerCallCliLsSpec M A lim) :=
  formatInnerHook0_callLsEnv_ok M A lim cliFormatInnerEnv_nil

/-- Lift `HookOk f` on `cliFormatInnerLsCallSpec` from `ExactOrNilEnv c.exactEvs` to any caller
    envelope `Env` containing `[]`. -/
theorem hookOk_cliFormatInnerLsCall_of_exactOrNil [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f
      (withFsTraceExact (cliFormatInnerLsCallSpec M A lim (fun c => ExactOrNilEnv c.exactEvs))))
    {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk f (withFsTraceExact (cliFormatInnerLsCallSpec M A lim (fun _ => Env))) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre hsp
  dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hshOk, hFit, hEx⟩, hm0⟩
  have hpre0 : s0.mem ⊨
      (withFsTraceExact
        (cliFormatInnerLsCallSpec M A lim (fun c => ExactOrNilEnv c.exactEvs))).pre (c, st0) s0 ∗
        R₀ := by
    dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hshOk, fitsEnv_exactOrNil hFit hEx,
      exactOrNilEnv_exact c.exactEvs⟩, hm0⟩
  obtain ⟨hkf, hsym, hout⟩ := hok (c, st0) R₀ s0 hrun hpre0 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hp := hpost.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1,
      exactOrNilEnv_imp hNil hEx evs hp.1.2.2.2⟩, hp.2⟩
  · dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withFsTraceExact] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom; rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- Monotonicity of `formatInnerCallLsEnvSpec` from `CliFormatInnerEnv` to any wider `Env`
    (such as `MsgDeserErrEnv` or `SeqEnv` phases) under `CliFormatInnerEnv c.exactEvs`. -/
theorem hookOk_formatInnerCallLsEnv_of_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (formatInnerCallCliLsSpec M A lim))
    {Env : List AllocEvent → Prop}
    (hSub : ∀ evs, CliFormatInnerEnv evs → Env evs) :
    HookOk f
      (withCallGuard (fun (c, _) _ => CliFormatInnerEnv c.exactEvs)
        (formatInnerCallLsEnvSpec M A lim Env)) := by
  rintro ⟨c, st0⟩ R₀ s0 hrun hpre hsp
  dsimp only [withCallGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hCliEx, hpre⟩
  obtain ⟨hlr, hpreInner⟩ := extract_withLsRetFormatInner hpre
  dsimp only [cliFormatInnerLsCallSpec] at hpreInner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreInner
  rcases hpreInner with ⟨⟨hx8, hx0, hx1, hshOk, hFit, _⟩, hm0⟩
  have hFitCli : FitsEnv M lim st0 CliFormatInnerEnv := fun evs hE => hFit evs (hSub evs hE)
  have hpreCli : s0.mem ⊨ (formatInnerCallCliLsSpec M A lim).pre (c, st0) s0 ∗ R₀ := by
    refine intro_withLsRetFormatInner hlr ?_
    dsimp only [cliFormatInnerLsCallSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hshOk, hFitCli, hCliEx⟩, hm0⟩
  obtain ⟨hkf, hsym, hout⟩ := hok (c, st0) R₀ s0 hrun hpreCli hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨ec, he, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withCallGuard, formatInnerCallLsEnvSpec, formatInnerCallCliLsSpec,
      withLsRetFormatInner, cliFormatInnerLsCallSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hSub evs hp.1.2.2.2⟩, hp.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ec, he, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem hookSat_formatInnerCallLsEnv_of_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {sym : String}
    (hsat : HookSat H sym (formatInnerCallCliLsSpec M A lim))
    {Env : List AllocEvent → Prop}
    (hSub : ∀ evs, CliFormatInnerEnv evs → Env evs) :
    HookSat H sym
      (withCallGuard (fun (c, _) _ => CliFormatInnerEnv c.exactEvs)
        (formatInnerCallLsEnvSpec M A lim Env)) := by
  rcases hsat with ⟨f, hfn, hok⟩
  exact ⟨f, hfn, hookOk_formatInnerCallLsEnv_of_cli hok hSub⟩

/-- Project `cliFormatInnerLsCallSpec.post` directly onto `formatInnerBudgetEnvSpec.post`. -/
theorem cliFormatInnerLsCallSpec_post_entails_budget [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (c : CliFormatInnerLsCall) (st0 : M.σ) (s0 sf : State) :
    (cliFormatInnerLsCallSpec M A lim (fun _ => Env)).post (c, st0) s0 sf ⊢
    ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
      (formatInnerBudgetEnvSpec M A lim Env).post (c.ret, st0) s0 sf ∗
      fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
      c.clientSep := by
  dsimp only [cliFormatInnerLsCallSpec, formatInnerBudgetEnvSpec]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_elim fun bs' => ?_
  refine Entails.pure_left fun ⟨hacp, hfs, htr, hEnv⟩ => ?_
  refine Entails.pure_right ⟨hacp, hfs⟩ ?_
  have hex : vecU8 A.repAlloc c.ret bs' ⊢ ∃∗ b : List (BitVec 8), vecU8 A.repAlloc c.ret b :=
    Entails.sepExists_right bs' (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hex) ?_
  have hinner :
      (∃∗ b : List (BitVec 8), vecU8 A.repAlloc c.ret b) ∗
        (fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
          (c.clientSep ∗
            (A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack))) ⊢
      (⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
        (∃∗ b : List (BitVec 8), vecU8 A.repAlloc c.ret b) ∗
        A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack) ∗
        fmtArgumentsAt c.argsRo c.x0 c.x1 c.tpl c.args ∗
        c.clientSep := by
    rw [pure_sepConj_of_true ⟨htr, hEnv⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  refine Entails.trans hinner ?_
  exact sepConj_mono_left (Entails.sepExists_right evs (Entails.refl _))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs

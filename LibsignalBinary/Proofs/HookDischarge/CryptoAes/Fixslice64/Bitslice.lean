/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
meta import ProofLib.StdStartup.StdDetect
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model

/-!
# Binary Contracts for `fixslice64::bitslice` and `fixslice64::inv_bitslice` (`Fixslice64.Bitslice`)

Placement-generic (`hasInstrs`) ARM64 `subroutine_ok` contracts for the 173-instruction `libaes`
packing (`bitslice`) and unpacking (`inv_bitslice`) routines:
- `step_bitslice`: unified `SepWP` stepping lemma over an arbitrary input assertion `P_in` with
  `SepLoad8` witnesses for four 16-byte input blocks (supporting both aliased pointers
  `x1 = x2 = x3 = x4 = src` in `aes256_key_schedule` and contiguous 4-block batches in
  `aes256_encrypt` / `aes256_decrypt`);
- `bitslice_rep_ok` (`bitsliceRepSpec`) and `bitslice4_ok` (`bitslice4Spec`);
- `invBitslice_ok` (`invBitsliceSpec`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (Blocks4 readReordered deltaSwap2 writeReorderedPair)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj step_str8_perm step_stp64_perm
   SepLoad8.sep_left SepLoad8.sep_right SepLoad8.of_bytesAt
   fsStateAt fsStateBytes fsStateAt_eq_pointsToBytes
   blocks4Bytes bytesAt_blocks4_split memRegion64_eq_exists_fsStateAt)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. Raw Instruction Words & Decode Templates -/

/-- Exact 173-instruction word sequence of `aes::soft::fixslice64::bitslice`. -/
@[expose] def bitsliceWords : List (BitVec 32) :=
  [0x39400428#32, 0x39400029#32, 0x3940082c#32, 0x3940044b#32, 0x39400c2d#32, 0x39401430#32,
   0xaa08412f#32, 0x39401031#32, 0x39400052#32, 0x3940202e#32, 0x39402429#32, 0x3940282a#32,
   0xaa0c81ec#32, 0xaa104230#32, 0xaa0b424b#32, 0x3940182f#32, 0x39400852#32, 0x39402c28#32,
   0xaa0dc18c#32, 0x39401c31#32, 0x3940302d#32, 0xaa0f820f#32, 0xaa12816b#32, 0x39400c50#32,
   0xaa0e218c#32, 0x3940144e#32, 0x39401052#32, 0xaa10c16b#32, 0xaa11c1ef#32, 0x39401850#32,
   0xaa096189#32, 0xaa0e424e#32, 0x39402052#32, 0x39403431#32, 0xaa0d21ed#32, 0x39401c4f#32,
   0xaa0aa129#32, 0x3940244a#32, 0xaa12216b#32, 0xaa1081ce#32, 0x3940382c#32, 0xaa1161ad#32,
   0xaa08e128#32, 0xaa0a6169#32, 0x3940046a#32, 0x3940006b#32, 0xaa0fc1ce#32, 0x3940304f#32,
   0x39402850#32, 0xaa0ca1ac#32, 0x39403c2d#32, 0xaa0a416a#32, 0x3940086b#32, 0xaa0f21ce#32,
   0x3940344f#32, 0x39401471#32, 0x39401072#32, 0xaa0b814a#32, 0x39400c6b#32, 0x39402065#32,
   0xaa10a129#32, 0x39402c50#32, 0xaa0f61ce#32, 0xaa0bc141#32, 0x3940384f#32, 0xaa114251#32,
   0x39401872#32, 0xaa0de18a#32, 0x3940246d#32, 0xaa05202c#32, 0xaa10e129#32, 0xaa0fa1cb#32,
   0xaa12822e#32, 0x39401c6f#32, 0x39400490#32, 0x39400091#32, 0xaa0d618c#32, 0x3940148d#32,
   0x39401092#32, 0xaa0fc1ce#32, 0x39402861#32, 0xaa10422f#32, 0x39400890#32, 0x39403071#32,
   0xaa0d424d#32, 0x39401892#32, 0xaa01a18c#32, 0xaa1081ef#32, 0x39400c90#32, 0xaa1121ce#32,
   0xaa1281ad#32, 0x39401c91#32, 0x39403472#32, 0xaa10c1ef#32, 0x39402090#32, 0x39403c41#32,
   0xaa11c1ad#32, 0x39403091#32, 0xaa1261ce#32, 0xaa1021ef#32, 0x39402490#32, 0x39403872#32,
   0xaa1121ad#32, 0x39403491#32, 0x39403c82#32, 0xaa1061ef#32, 0x39402890#32, 0xaa12a1ce#32,
   0xaa1161ad#32, 0x39403891#32, 0x39402c72#32, 0xaa10a1ef#32, 0x39402c90#32, 0xaa01e16b#32,
   0xaa11a1ad#32, 0x39403c71#32, 0xaa12e18c#32, 0xaa10e1ef#32, 0xca480530#32, 0xca4a0572#32,
   0xaa11e1ce#32, 0xaa02e1ad#32, 0xca4c05f1#32, 0x9200f210#32, 0x9200f252#32, 0xca4e05a1#32,
   0xca100508#32, 0xca12054a#32, 0x9200f231#32, 0xca090209#32, 0xca0b024b#32, 0x9200f021#32,
   0xca11058c#32, 0xca0f022f#32, 0xca0105ce#32, 0xca0d002d#32, 0xca4909f2#32, 0xca480990#32,
   0xca4b09a1#32, 0xca4a09d1#32, 0x9200e652#32, 0x9200e610#32, 0x9200e421#32, 0xca120929#32,
   0x9200e631#32, 0xca100908#32, 0xca01096b#32, 0xca11094a#32, 0xca0c020c#32, 0xca0e022e#32,
   0xca491171#32, 0xca0f024f#32, 0xca0d002d#32, 0xca481150#32, 0xca4c11d2#32, 0xca4f11a1#32,
   0x9200ce31#32, 0x9200ce10#32, 0xca111129#32, 0x9200ce52#32, 0xca101108#32, 0x9200cc21#32,
   0xca12118c#32, 0xa9002408#32, 0xca0111e8#32, 0xca0a0209#32, 0xa901200c#32, 0xca0b0228#32,
   0xa9022009#32, 0xca0e0249#32, 0xca0d0028#32, 0xa9032009#32, 0xd65f03c0#32]

private theorem map_decode_eq_map_some {ws : List (BitVec 32)}
    (h : (ws.all fun w => (Arm64.decode w).isSome) = true) :
    ws.map Arm64.decode = (decodeWords ws).map some := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, decodeWords, decodeWord]
    cases hd : Arm64.decode w with
    | none => simp [hd] at h
    | some i => exact congrArg (some i :: ·) (ih h.2)

/-- Decoded 173-instruction list of `aes::soft::fixslice64::bitslice`. -/
@[expose] def bitsliceInstrs : List Instr := decodeWords bitsliceWords

theorem bitsliceInstrs_template_eq :
    bitsliceWords.map Arm64.decode = bitsliceInstrs.map some :=
  map_decode_eq_map_some (by decide)

/-- Exact 173-instruction word sequence of `aes::soft::fixslice64::inv_bitslice`. -/
@[expose] def invBitsliceWords : List (BitVec 32) :=
  [0xa9404429#32, 0xa941202a#32, 0xa942402b#32, 0xa943342c#32, 0xca49062e#32, 0xca4a050f#32,
   0xca4b0612#32, 0x9200f1c2#32, 0xca4c05a1#32, 0x9200f1e4#32, 0xca02052e#32, 0x9200f245#32,
   0xca040549#32, 0xca110051#32, 0x9200f02f#32, 0xca050572#32, 0xca080088#32, 0xca0f058a#32,
   0xca4e092b#32, 0xca0d01ed#32, 0xca520941#32, 0x9200e56c#32, 0xca090189#32, 0x9200e42b#32,
   0xca0c09c1#32, 0xca0b0a4e#32, 0xca0a016a#32, 0xca4111d2#32, 0x9200ce52#32, 0xca0e024e#32,
   0xca121032#32, 0xca1000a1#32, 0xd350fdc3#32, 0xd360fdc2#32, 0xd370fdd0#32, 0xd350fe4f#32,
   0xca4109a4#32, 0xd370fe45#32, 0x39001403#32, 0xd360fe43#32, 0x39001802#32, 0xca510902#32,
   0x39001c10#32, 0x3900040f#32, 0x9200e450#32, 0x9200e48f#32, 0x39000803#32, 0xd348fe43#32,
   0xca100a31#32, 0xd358fe42#32, 0xca0f0821#32, 0x39000012#32, 0x39002003#32, 0xd368fe43#32,
   0xd378fe52#32, 0x39002402#32, 0xca511022#32, 0xca080208#32, 0x39002c12#32, 0xd358fdd2#32,
   0xca0d01ed#32, 0x9200cc42#32, 0x39002803#32, 0xd348fdc3#32, 0xca021231#32, 0x39003412#32,
   0xd368fdd2#32, 0x3900100e#32, 0xd378fdce#32, 0xca010041#32, 0xd368fe2c#32, 0xd378fe2b#32,
   0x39003812#32, 0x39003c0e#32, 0xd360fe2e#32, 0xd350fe32#32, 0x3900680c#32, 0xd348fc2c#32,
   0x3900480e#32, 0xd350fc2e#32, 0x39006c0b#32, 0xd358fc2b#32, 0x3900540e#32, 0xd370fc2e#32,
   0x3900700c#32, 0x39005c0e#32, 0xd358fe2e#32, 0x3900740b#32, 0xd368fc2b#32, 0x3900640e#32,
   0xca49114e#32, 0x3900780b#32, 0x9200cdcc#32, 0xd378fc2e#32, 0x39004412#32, 0xca0c1129#32,
   0xca0a018a#32, 0xd370fe32#32, 0xd350fd4c#32, 0x39007c0e#32, 0xd350fd2b#32, 0xd360fd2e#32,
   0x39008009#32, 0x3900940c#32, 0xd370fd4c#32, 0x3900840b#32, 0xd370fd2b#32, 0x39009c0c#32,
   0xd368fd2c#32, 0x39008c0b#32, 0xd360fd4b#32, 0x3900a80c#32, 0xd348fd4c#32, 0x3900980b#32,
   0xd348fd2b#32, 0x3900900a#32, 0x3900a00b#32, 0xd358fd2b#32, 0xd378fd29#32, 0x39004c12#32,
   0xd360fc32#32, 0x3900a40b#32, 0xca4811ab#32, 0x3900ac09#32, 0xd358fd49#32, 0x9200cd6b#32,
   0x39005812#32, 0xd348fe32#32, 0xca0b1108#32, 0x3900b409#32, 0xd368fd49#32, 0xd378fd4a#32,
   0xca0d016b#32, 0x39000c05#32, 0x3900b809#32, 0xd350fd09#32, 0x3900bc0a#32, 0xd360fd0a#32,
   0x3900c409#32, 0xd370fd09#32, 0x3900c80a#32, 0xd350fd6a#32, 0x3900cc09#32, 0xd360fd69#32,
   0x3900d40a#32, 0xd370fd6a#32, 0x3900d809#32, 0xd348fd09#32, 0x3900dc0a#32, 0xd358fd0a#32,
   0x3900e009#32, 0xd368fd09#32, 0x3900c008#32, 0xd378fd08#32, 0x3900e809#32, 0xd348fd69#32,
   0x3900ec08#32, 0xd358fd68#32, 0x3900f009#32, 0xd378fd69#32, 0x3900f408#32, 0xd368fd68#32,
   0x39003003#32, 0x39006012#32, 0x39004011#32, 0x39005001#32, 0x3900880e#32, 0x3900b00c#32,
   0x3900e40a#32, 0x3900d00b#32, 0x3900f808#32, 0x3900fc09#32, 0xd65f03c0#32]

/-- Decoded 173-instruction list of `aes::soft::fixslice64::inv_bitslice`. -/
@[expose] def invBitsliceInstrs : List Instr := decodeWords invBitsliceWords

theorem invBitsliceInstrs_template_eq :
    invBitsliceWords.map Arm64.decode = invBitsliceInstrs.map some :=
  map_decode_eq_map_some (by decide)

/-! ## 2. Public Specifications -/

/-- Contract for `bitslice(dst, src, src, src, src)` with a single 16-byte block replicated across
    all four input pointers (used by `aes256_key_schedule`). -/
@[expose] def bitsliceRepSpec : Spec (Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, dst, src, b) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ s0.readReg64 .x2 = src ∧
      s0.readReg64 .x3 = src ∧ s0.readReg64 .x4 = src ∧ b.length = 16⌝ ∗
    (bytesAt ro src b ∗ memRegion dst 64)
  post := fun (ro, dst, src, b) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (bytesAt ro src b ∗ fsStateAt dst (Model.bitslice (Blocks4.replicate b)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Contract for `bitslice(dst, src, src + 16, src + 32, src + 48)` over four contiguous 16-byte
    blocks `bs : Blocks4` (used by `aes256_encrypt` and `aes256_decrypt`). -/
@[expose] def bitslice4Spec : Spec (Bool × BitVec 64 × BitVec 64 × Blocks4) where
  pre := fun (ro, dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ s0.readReg64 .x2 = src + 16#64 ∧
      s0.readReg64 .x3 = src + 32#64 ∧ s0.readReg64 .x4 = src + 48#64 ∧ Blocks4.Wf bs⌝ ∗
    (bytesAt ro src (blocks4Bytes bs) ∗ memRegion dst 64)
  post := fun (ro, dst, src, bs) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (bytesAt ro src (blocks4Bytes bs) ∗ fsStateAt dst (Model.bitslice bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Contract for `inv_bitslice(dst, src)` unpacking `fsStateAt src st` into four contiguous
    16-byte blocks `blocks4Bytes (Model.invBitslice st)` at `dst`. -/
@[expose] def invBitsliceSpec : Spec (BitVec 64 × BitVec 64 × Model.FsState) where
  pre := fun (dst, src, st) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src⌝ ∗
    (fsStateAt src st ∗ memRegion dst 64)
  post := fun (dst, src, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (fsStateAt src st ∗ (dst ↦ₛ blocks4Bytes (Model.invBitslice st)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 3. Shared Chunk & Load/Store Combinators -/

private abbrev advanceWords (pc : BitVec 64) (ws : List (BitVec 32)) : BitVec 64 :=
  pc + BitVec.ofNat 64 (4 * ws.length)

private theorem split_decodeWords {P : Program} {pc : BitVec 64}
    {ws : List (BitVec 32)} {rest : List Instr}
    (h : hasInstrs P pc (decodeWords ws ++ rest)) :
    hasInstrs P pc (decodeWords ws) ∧ hasInstrs P (advanceWords pc ws) rest :=
  h.split_append (off := BitVec.ofNat 64 (4 * ws.length)) (by simp [decodeWords])

private structure ChunkPreserved (s sf : State) : Prop where
  x0 : sf.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5)
  x30 : sf.readReg64 (.gpr 30#5) = s.readReg64 (.gpr 30#5)
  sp : sf.sp = s.sp
  callee : CalleeSavedPreserved s sf
  purePres : PureStepPreserved s sf

private theorem ChunkPreserved.trans {s1 s2 s3 : State}
    (h1 : ChunkPreserved s1 s2) (h2 : ChunkPreserved s2 s3) : ChunkPreserved s1 s3 :=
  ⟨h2.x0.trans h1.x0, h2.x30.trans h1.x30, h2.sp.trans h1.sp,
   h1.callee.trans h2.callee, h1.purePres.trans h2.purePres⟩

private theorem writeReg_w32_zext8 (s : State) (rt : Reg) (v : BitVec 8) :
    s.writeReg .W32 rt (v.zeroExtend 64) = s.writeReg64 rt (v.zeroExtend 64) := by
  simp only [State.writeReg]
  congr 1
  bv_bits

private theorem step_ldrb_off {prog : Program} {target_pc pc ptr off : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {rn : BitVec 5} {v : BitVec 8}
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt (.Offset (.gpr rn) off)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hload : SepLoad8 (ptr + off) P v)
    (hrn : s.readReg64 (.gpr rn) = ptr)
    (hexec : (s.writeReg64 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr8 hpc hrun hfetch rfl (congrArg (fun x => (x + off, none)) hrn) hload
    ((congrArg (·.setPC (pc + 4#64)) (writeReg_w32_zext8 s rt v)).trans hexec) hnext

local macro "wp_ldrb " hf:term:max hl:term:max off:num hptr:term:max : tactic => `(tactic| (
  apply step_ldrb_off $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· exact $hl $off (by decide))
  (· wp_focus_close (first | wp_norm_lhs | simp only [wp_norm, arm64_norm, $hptr:term]))
  (· wp_focus_close wp_norm_lhs); try wp_norm_state))

/-! ## 4. `fixslice64::bitslice` Chunk Decomposition & Unified Stepping -/

private def bsChunk1Words : List (BitVec 32) :=
  [0x39400428#32, 0x39400029#32, 0x3940082c#32, 0x3940044b#32, 0x39400c2d#32, 0x39401430#32,
   0xaa08412f#32, 0x39401031#32, 0x39400052#32, 0x3940202e#32, 0x39402429#32, 0x3940282a#32,
   0xaa0c81ec#32, 0xaa104230#32, 0xaa0b424b#32, 0x3940182f#32, 0x39400852#32, 0x39402c28#32,
   0xaa0dc18c#32, 0x39401c31#32, 0x3940302d#32, 0xaa0f820f#32, 0xaa12816b#32, 0x39400c50#32,
   0xaa0e218c#32, 0x3940144e#32, 0x39401052#32, 0xaa10c16b#32, 0xaa11c1ef#32, 0x39401850#32,
   0xaa096189#32, 0xaa0e424e#32, 0x39402052#32, 0x39403431#32, 0xaa0d21ed#32, 0x39401c4f#32,
   0xaa0aa129#32, 0x3940244a#32, 0xaa12216b#32, 0xaa1081ce#32, 0x3940382c#32, 0xaa1161ad#32,
   0xaa08e128#32, 0xaa0a6169#32]

private def bsChunk2Words : List (BitVec 32) :=
  [0x3940046a#32, 0x3940006b#32, 0xaa0fc1ce#32, 0x3940304f#32, 0x39402850#32, 0xaa0ca1ac#32,
   0x39403c2d#32, 0xaa0a416a#32, 0x3940086b#32, 0xaa0f21ce#32, 0x3940344f#32, 0x39401471#32,
   0x39401072#32, 0xaa0b814a#32, 0x39400c6b#32, 0x39402065#32, 0xaa10a129#32, 0x39402c50#32,
   0xaa0f61ce#32, 0xaa0bc141#32, 0x3940384f#32, 0xaa114251#32, 0x39401872#32, 0xaa0de18a#32,
   0x3940246d#32, 0xaa05202c#32, 0xaa10e129#32, 0xaa0fa1cb#32, 0xaa12822e#32]

private def bsChunk3Words : List (BitVec 32) :=
  [0x39401c6f#32, 0x39400490#32, 0x39400091#32, 0xaa0d618c#32, 0x3940148d#32, 0x39401092#32,
   0xaa0fc1ce#32, 0x39402861#32, 0xaa10422f#32, 0x39400890#32, 0x39403071#32, 0xaa0d424d#32,
   0x39401892#32, 0xaa01a18c#32, 0xaa1081ef#32, 0x39400c90#32, 0xaa1121ce#32, 0xaa1281ad#32,
   0x39401c91#32, 0x39403472#32, 0xaa10c1ef#32, 0x39402090#32, 0x39403c41#32, 0xaa11c1ad#32,
   0x39403091#32, 0xaa1261ce#32, 0xaa1021ef#32, 0x39402490#32, 0x39403872#32, 0xaa1121ad#32,
   0x39403491#32, 0x39403c82#32, 0xaa1061ef#32, 0x39402890#32, 0xaa12a1ce#32, 0xaa1161ad#32,
   0x39403891#32, 0x39402c72#32, 0xaa10a1ef#32, 0x39402c90#32, 0xaa01e16b#32, 0xaa11a1ad#32,
   0x39403c71#32, 0xaa12e18c#32, 0xaa10e1ef#32, 0xca480530#32, 0xca4a0572#32, 0xaa11e1ce#32,
   0xaa02e1ad#32]

private def bsChunk4Words : List (BitVec 32) :=
  [0xca4c05f1#32, 0x9200f210#32, 0x9200f252#32, 0xca4e05a1#32, 0xca100508#32, 0xca12054a#32,
   0x9200f231#32, 0xca090209#32, 0xca0b024b#32, 0x9200f021#32, 0xca11058c#32, 0xca0f022f#32,
   0xca0105ce#32, 0xca0d002d#32]

private def bsChunk5Words : List (BitVec 32) :=
  [0xca4909f2#32, 0xca480990#32, 0xca4b09a1#32, 0xca4a09d1#32, 0x9200e652#32, 0x9200e610#32,
   0x9200e421#32, 0xca120929#32, 0x9200e631#32, 0xca100908#32, 0xca01096b#32, 0xca11094a#32,
   0xca0c020c#32, 0xca0e022e#32, 0xca491171#32, 0xca0f024f#32, 0xca0d002d#32]

private def bsChunk6Words : List (BitVec 32) :=
  [0xca481150#32, 0xca4c11d2#32, 0xca4f11a1#32, 0x9200ce31#32, 0x9200ce10#32, 0xca111129#32,
   0x9200ce52#32, 0xca101108#32, 0x9200cc21#32, 0xca12118c#32, 0xa9002408#32, 0xca0111e8#32,
   0xca0a0209#32, 0xa901200c#32, 0xca0b0228#32, 0xa9022009#32, 0xca0e0249#32, 0xca0d0028#32,
   0xa9032009#32, 0xd65f03c0#32]

private theorem bitsliceInstrs_chunks :
    bitsliceInstrs =
      decodeWords bsChunk1Words ++
      (decodeWords bsChunk2Words ++
      (decodeWords bsChunk3Words ++
      (decodeWords bsChunk4Words ++
      (decodeWords bsChunk5Words ++ decodeWords bsChunk6Words)))) := by
  have hw : bitsliceWords =
      bsChunk1Words ++ (bsChunk2Words ++ (bsChunk3Words ++
        (bsChunk4Words ++ (bsChunk5Words ++ bsChunk6Words)))) := rfl
  simp only [bitsliceInstrs, hw, decodeWords, List.map_append]

private def BsRegs1 (b0 b1 : List (BitVec 8)) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = ((((((((((b0.getD 0 0#8).zeroExtend 64)) ||| ((((b0.getD 1 0#8).zeroExtend 64)) <<< 16)) ||| ((((b0.getD 2 0#8).zeroExtend 64)) <<< 32)) ||| ((((b0.getD 3 0#8).zeroExtend 64)) <<< 48)) ||| ((((b0.getD 8 0#8).zeroExtend 64)) <<< 8)) ||| ((((b0.getD 9 0#8).zeroExtend 64)) <<< 24)) ||| ((((b0.getD 10 0#8).zeroExtend 64)) <<< 40)) ||| ((((b0.getD 11 0#8).zeroExtend 64)) <<< 56)) ∧
  s.readReg64 (.gpr 9#5) = ((((((((b1.getD 0 0#8).zeroExtend 64)) ||| ((((b1.getD 1 0#8).zeroExtend 64)) <<< 16)) ||| ((((b1.getD 2 0#8).zeroExtend 64)) <<< 32)) ||| ((((b1.getD 3 0#8).zeroExtend 64)) <<< 48)) ||| ((((b1.getD 8 0#8).zeroExtend 64)) <<< 8)) ||| ((((b1.getD 9 0#8).zeroExtend 64)) <<< 24)) ∧
  s.readReg64 (.gpr 12#5) = (((b0.getD 14 0#8).zeroExtend 64)) ∧
  s.readReg64 (.gpr 13#5) = ((((((((b0.getD 4 0#8).zeroExtend 64)) ||| ((((b0.getD 5 0#8).zeroExtend 64)) <<< 16)) ||| ((((b0.getD 6 0#8).zeroExtend 64)) <<< 32)) ||| ((((b0.getD 7 0#8).zeroExtend 64)) <<< 48)) ||| ((((b0.getD 12 0#8).zeroExtend 64)) <<< 8)) ||| ((((b0.getD 13 0#8).zeroExtend 64)) <<< 24)) ∧
  s.readReg64 (.gpr 14#5) = (((((b1.getD 4 0#8).zeroExtend 64)) ||| ((((b1.getD 5 0#8).zeroExtend 64)) <<< 16)) ||| ((((b1.getD 6 0#8).zeroExtend 64)) <<< 32)) ∧
  s.readReg64 (.gpr 15#5) = (((b1.getD 7 0#8).zeroExtend 64))

private def BsRegs2 (b0 b1 b2 : List (BitVec 8)) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = ((((((((((b0.getD 0 0#8).zeroExtend 64)) ||| ((((b0.getD 1 0#8).zeroExtend 64)) <<< 16)) ||| ((((b0.getD 2 0#8).zeroExtend 64)) <<< 32)) ||| ((((b0.getD 3 0#8).zeroExtend 64)) <<< 48)) ||| ((((b0.getD 8 0#8).zeroExtend 64)) <<< 8)) ||| ((((b0.getD 9 0#8).zeroExtend 64)) <<< 24)) ||| ((((b0.getD 10 0#8).zeroExtend 64)) <<< 40)) ||| ((((b0.getD 11 0#8).zeroExtend 64)) <<< 56)) ∧
  s.readReg64 (.gpr 9#5) = ((((((((((b1.getD 0 0#8).zeroExtend 64)) ||| ((((b1.getD 1 0#8).zeroExtend 64)) <<< 16)) ||| ((((b1.getD 2 0#8).zeroExtend 64)) <<< 32)) ||| ((((b1.getD 3 0#8).zeroExtend 64)) <<< 48)) ||| ((((b1.getD 8 0#8).zeroExtend 64)) <<< 8)) ||| ((((b1.getD 9 0#8).zeroExtend 64)) <<< 24)) ||| ((((b1.getD 10 0#8).zeroExtend 64)) <<< 40)) ||| ((((b1.getD 11 0#8).zeroExtend 64)) <<< 56)) ∧
  s.readReg64 (.gpr 10#5) = ((((((((((b0.getD 4 0#8).zeroExtend 64)) ||| ((((b0.getD 5 0#8).zeroExtend 64)) <<< 16)) ||| ((((b0.getD 6 0#8).zeroExtend 64)) <<< 32)) ||| ((((b0.getD 7 0#8).zeroExtend 64)) <<< 48)) ||| ((((b0.getD 12 0#8).zeroExtend 64)) <<< 8)) ||| ((((b0.getD 13 0#8).zeroExtend 64)) <<< 24)) ||| ((((b0.getD 14 0#8).zeroExtend 64)) <<< 40)) ||| ((((b0.getD 15 0#8).zeroExtend 64)) <<< 56)) ∧
  s.readReg64 (.gpr 11#5) = (((((((((b1.getD 4 0#8).zeroExtend 64)) ||| ((((b1.getD 5 0#8).zeroExtend 64)) <<< 16)) ||| ((((b1.getD 6 0#8).zeroExtend 64)) <<< 32)) ||| ((((b1.getD 7 0#8).zeroExtend 64)) <<< 48)) ||| ((((b1.getD 12 0#8).zeroExtend 64)) <<< 8)) ||| ((((b1.getD 13 0#8).zeroExtend 64)) <<< 24)) ||| ((((b1.getD 14 0#8).zeroExtend 64)) <<< 40)) ∧
  s.readReg64 (.gpr 12#5) = (((((((b2.getD 0 0#8).zeroExtend 64)) ||| ((((b2.getD 1 0#8).zeroExtend 64)) <<< 16)) ||| ((((b2.getD 2 0#8).zeroExtend 64)) <<< 32)) ||| ((((b2.getD 3 0#8).zeroExtend 64)) <<< 48)) ||| ((((b2.getD 8 0#8).zeroExtend 64)) <<< 8)) ∧
  s.readReg64 (.gpr 13#5) = (((b2.getD 9 0#8).zeroExtend 64)) ∧
  s.readReg64 (.gpr 14#5) = (((((b2.getD 4 0#8).zeroExtend 64)) ||| ((((b2.getD 5 0#8).zeroExtend 64)) <<< 16)) ||| ((((b2.getD 6 0#8).zeroExtend 64)) <<< 32))

private def BsRegs3 (r0 r1 r2 r3 r4 r5 r6 r7 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = r0 ∧
  s.readReg64 (.gpr 9#5) = r1 ∧
  s.readReg64 (.gpr 10#5) = r4 ∧
  s.readReg64 (.gpr 11#5) = r5 ∧
  s.readReg64 (.gpr 12#5) = r2 ∧
  s.readReg64 (.gpr 13#5) = r7 ∧
  s.readReg64 (.gpr 14#5) = r6 ∧
  s.readReg64 (.gpr 15#5) = r3 ∧
  s.readReg64 (.gpr 16#5) = r1 ^^^ (r0 >>> 1) ∧
  s.readReg64 (.gpr 18#5) = r5 ^^^ (r4 >>> 1)

private def BsRegs4 (u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = u0 ∧
  s.readReg64 (.gpr 9#5) = u1 ∧
  s.readReg64 (.gpr 10#5) = u4 ∧
  s.readReg64 (.gpr 11#5) = u5 ∧
  s.readReg64 (.gpr 12#5) = u2 ∧
  s.readReg64 (.gpr 13#5) = u7 ∧
  s.readReg64 (.gpr 14#5) = u6 ∧
  s.readReg64 (.gpr 15#5) = u3

private def BsRegs5 (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = w0 ∧
  s.readReg64 (.gpr 9#5) = w1 ∧
  s.readReg64 (.gpr 10#5) = w4 ∧
  s.readReg64 (.gpr 11#5) = w5 ∧
  s.readReg64 (.gpr 12#5) = w2 ∧
  s.readReg64 (.gpr 13#5) = w7 ∧
  s.readReg64 (.gpr 14#5) = w6 ∧
  s.readReg64 (.gpr 15#5) = w3 ∧
  s.readReg64 (.gpr 17#5) = w5 ^^^ (w1 >>> 4)

section
arm64_proof_prelude

private theorem bs_chunk1 {P : Program} {pc target_pc p0 p1 p2 p3 : BitVec 64}
    {s : State} {Pre : SepProp} {b0 b1 : List (BitVec 8)}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords bsChunk1Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx1 : s.readReg64 (.gpr 1#5) = p0) (hx2 : s.readReg64 (.gpr 2#5) = p1)
    (hx3 : s.readReg64 (.gpr 3#5) = p2) (hx4 : s.readReg64 (.gpr 4#5) = p3)
    (hl0 : ∀ i : Nat, i < 16 → SepLoad8 (p0 + BitVec.ofNat 64 i) Pre (b0.getD i 0#8))
    (hl1 : ∀ i : Nat, i < 16 → SepLoad8 (p1 + BitVec.ofNat 64 i) Pre (b1.getD i 0#8))
    (hnext : ∀ s1 : State, s1.pc = advanceWords pc bsChunk1Words → s1.status = .Running →
      s1.readReg64 (.gpr 1#5) = p0 → s1.readReg64 (.gpr 2#5) = p1 →
      s1.readReg64 (.gpr 3#5) = p2 → s1.readReg64 (.gpr 4#5) = p3 →
      BsRegs1 b0 b1 s1 → ChunkPreserved s s1 →
      SepWP P target_pc s1 Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 44
  wp_ldrb hf_0 hl0 1 hx1; wp_ldrb hf_1 hl0 0 hx1; wp_ldrb hf_2 hl0 2 hx1
  wp_ldrb hf_3 hl1 1 hx2; wp_ldrb hf_4 hl0 3 hx1; wp_ldrb hf_5 hl0 5 hx1
  wp_step; wp_ldrb hf_7 hl0 4 hx1; wp_ldrb hf_8 hl1 0 hx2
  wp_ldrb hf_9 hl0 8 hx1; wp_ldrb hf_10 hl0 9 hx1; wp_ldrb hf_11 hl0 10 hx1
  wp_steps 3; wp_ldrb hf_15 hl0 6 hx1; wp_ldrb hf_16 hl1 2 hx2
  wp_ldrb hf_17 hl0 11 hx1; wp_step; wp_ldrb hf_19 hl0 7 hx1
  wp_ldrb hf_20 hl0 12 hx1; wp_steps 2; wp_ldrb hf_23 hl1 3 hx2
  wp_step; wp_ldrb hf_25 hl1 5 hx2; wp_ldrb hf_26 hl1 4 hx2
  wp_steps 2; wp_ldrb hf_29 hl1 6 hx2; wp_steps 2
  wp_ldrb hf_32 hl1 8 hx2; wp_ldrb hf_33 hl0 13 hx1; wp_step
  wp_ldrb hf_35 hl1 7 hx2; wp_step; wp_ldrb hf_37 hl1 9 hx2
  wp_steps 2; wp_ldrb hf_40 hl0 14 hx1; wp_steps 3
  refine hnext _ (by simp [advanceWords, bsChunk1Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hx1]) (by simp [wp_norm, arm64_norm, hx2])
    (by simp [wp_norm, arm64_norm, hx3]) (by simp [wp_norm, arm64_norm, hx4]) ?_ ?_
  · simp only [BsRegs1, wp_norm, arm64_norm]
  · exact ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem bs_chunk2 {P : Program} {pc target_pc p0 p1 p2 p3 : BitVec 64}
    {s : State} {Pre : SepProp} {b0 b1 b2 : List (BitVec 8)}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords bsChunk2Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx1 : s.readReg64 (.gpr 1#5) = p0) (hx2 : s.readReg64 (.gpr 2#5) = p1)
    (hx3 : s.readReg64 (.gpr 3#5) = p2) (hx4 : s.readReg64 (.gpr 4#5) = p3)
    (hr1 : BsRegs1 b0 b1 s)
    (hl0 : ∀ i : Nat, i < 16 → SepLoad8 (p0 + BitVec.ofNat 64 i) Pre (b0.getD i 0#8))
    (hl1 : ∀ i : Nat, i < 16 → SepLoad8 (p1 + BitVec.ofNat 64 i) Pre (b1.getD i 0#8))
    (hl2 : ∀ i : Nat, i < 16 → SepLoad8 (p2 + BitVec.ofNat 64 i) Pre (b2.getD i 0#8))
    (hnext : ∀ s2 : State, s2.pc = advanceWords pc bsChunk2Words → s2.status = .Running →
      s2.readReg64 (.gpr 2#5) = p1 → s2.readReg64 (.gpr 3#5) = p2 →
      s2.readReg64 (.gpr 4#5) = p3 →
      BsRegs2 b0 b1 b2 s2 → ChunkPreserved s s2 →
      SepWP P target_pc s2 Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr1 with ⟨hx8, hx9, hx12, hx13, hx14, hx15⟩
  have_instrs hc 0 29
  wp_ldrb hf_0 hl2 1 hx3; wp_ldrb hf_1 hl2 0 hx3; wp_step
  wp_ldrb hf_3 hl1 12 hx2; wp_ldrb hf_4 hl1 10 hx2; wp_step
  wp_ldrb hf_6 hl0 15 hx1; wp_step; wp_ldrb hf_8 hl2 2 hx3
  wp_step; wp_ldrb hf_10 hl1 13 hx2; wp_ldrb hf_11 hl2 5 hx3
  wp_ldrb hf_12 hl2 4 hx3; wp_step; wp_ldrb hf_14 hl2 3 hx3
  wp_ldrb hf_15 hl2 8 hx3; wp_step; wp_ldrb hf_17 hl1 11 hx2
  wp_steps 2; wp_ldrb hf_20 hl1 14 hx2; wp_step
  wp_ldrb hf_22 hl2 6 hx3; wp_step; wp_ldrb hf_24 hl2 9 hx3
  wp_steps 4
  refine hnext _ (by simp [advanceWords, bsChunk2Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm, hx3])
    (by simp [wp_norm, arm64_norm, hx4]) ?_ ?_
  · simp only [BsRegs2, wp_norm, arm64_norm, hx8]
  · exact ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem bs_chunk3 {P : Program} {pc target_pc p1 p2 p3 : BitVec 64}
    {s : State} {Pre : SepProp} {b0 b1 b2 b3 : List (BitVec 8)}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords bsChunk3Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx2 : s.readReg64 (.gpr 2#5) = p1) (hx3 : s.readReg64 (.gpr 3#5) = p2)
    (hx4 : s.readReg64 (.gpr 4#5) = p3)
    (hr2 : BsRegs2 b0 b1 b2 s)
    (hl1 : ∀ i : Nat, i < 16 → SepLoad8 (p1 + BitVec.ofNat 64 i) Pre (b1.getD i 0#8))
    (hl2 : ∀ i : Nat, i < 16 → SepLoad8 (p2 + BitVec.ofNat 64 i) Pre (b2.getD i 0#8))
    (hl3 : ∀ i : Nat, i < 16 → SepLoad8 (p3 + BitVec.ofNat 64 i) Pre (b3.getD i 0#8))
    (hnext : ∀ s3 : State, s3.pc = advanceWords pc bsChunk3Words → s3.status = .Running →
      BsRegs3 (readReordered b0 0) (readReordered b1 0) (readReordered b2 0) (readReordered b3 0)
        (readReordered b0 4) (readReordered b1 4) (readReordered b2 4) (readReordered b3 4) s3 →
      ChunkPreserved s s3 →
      SepWP P target_pc s3 Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr2 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14⟩
  have_instrs hc 0 49
  wp_ldrb hf_0 hl2 7 hx3; wp_ldrb hf_1 hl3 1 hx4; wp_ldrb hf_2 hl3 0 hx4
  wp_step; wp_ldrb hf_4 hl3 5 hx4; wp_ldrb hf_5 hl3 4 hx4
  wp_step; wp_ldrb hf_7 hl2 10 hx3; wp_step
  wp_ldrb hf_9 hl3 2 hx4; wp_ldrb hf_10 hl2 12 hx3; wp_step
  wp_ldrb hf_12 hl3 6 hx4; wp_steps 2; wp_ldrb hf_15 hl3 3 hx4
  wp_steps 2; wp_ldrb hf_18 hl3 7 hx4; wp_ldrb hf_19 hl2 13 hx3
  wp_step; wp_ldrb hf_21 hl3 8 hx4; wp_ldrb hf_22 hl1 15 hx2
  wp_step; wp_ldrb hf_24 hl3 12 hx4; wp_steps 2
  wp_ldrb hf_27 hl3 9 hx4; wp_ldrb hf_28 hl2 14 hx3; wp_step
  wp_ldrb hf_30 hl3 13 hx4; wp_ldrb hf_31 hl3 15 hx4; wp_step
  wp_ldrb hf_33 hl3 10 hx4; wp_steps 2; wp_ldrb hf_36 hl3 14 hx4
  wp_ldrb hf_37 hl2 11 hx3; wp_step; wp_ldrb hf_39 hl3 11 hx4
  wp_steps 2; wp_ldrb hf_42 hl2 15 hx3; wp_steps 6
  refine hnext _ (by simp [advanceWords, bsChunk3Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [BsRegs3, readReordered, wp_norm, arm64_norm, hx8, hx9, hx10]
  · exact ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private def bsChunk4Instrs : List Instr :=
  [.logicalShift .W64 .EOR (.gpr 17#5) (.gpr 15#5) (.gpr 12#5) .LSR 1,
   .logicalImm .W64 .AND (.gpr 16#5) (.gpr 16#5) 0x5555555555555555#64,
   .logicalImm .W64 .AND (.gpr 18#5) (.gpr 18#5) 0x5555555555555555#64,
   .logicalShift .W64 .EOR (.gpr 1#5) (.gpr 13#5) (.gpr 14#5) .LSR 1,
   .logicalShift .W64 .EOR (.gpr 8#5) (.gpr 8#5) (.gpr 16#5) .LSL 1,
   .logicalShift .W64 .EOR (.gpr 10#5) (.gpr 10#5) (.gpr 18#5) .LSL 1,
   .logicalImm .W64 .AND (.gpr 17#5) (.gpr 17#5) 0x5555555555555555#64,
   .logicalShift .W64 .EOR (.gpr 9#5) (.gpr 16#5) (.gpr 9#5) .LSL 0,
   .logicalShift .W64 .EOR (.gpr 11#5) (.gpr 18#5) (.gpr 11#5) .LSL 0,
   .logicalImm .W64 .AND (.gpr 1#5) (.gpr 1#5) 0x5555555555555555#64,
   .logicalShift .W64 .EOR (.gpr 12#5) (.gpr 12#5) (.gpr 17#5) .LSL 1,
   .logicalShift .W64 .EOR (.gpr 15#5) (.gpr 17#5) (.gpr 15#5) .LSL 0,
   .logicalShift .W64 .EOR (.gpr 14#5) (.gpr 14#5) (.gpr 1#5) .LSL 1,
   .logicalShift .W64 .EOR (.gpr 13#5) (.gpr 1#5) (.gpr 13#5) .LSL 0]

private theorem decodeWords_bsChunk4Words : decodeWords bsChunk4Words = bsChunk4Instrs := by decide

private theorem bs_chunk4 {P : Program} {pc target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {r0 r1 r2 r3 r4 r5 r6 r7 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords bsChunk4Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hr3 : BsRegs3 r0 r1 r2 r3 r4 r5 r6 r7 s)
    (hnext : ∀ s4 : State, s4.pc = advanceWords pc bsChunk4Words → s4.status = .Running →
      (let m0 := 0x5555555555555555#64
       let d0 := deltaSwap2 r1 r0 1 m0
       let d1 := deltaSwap2 r3 r2 1 m0
       let d2 := deltaSwap2 r5 r4 1 m0
       let d3 := deltaSwap2 r7 r6 1 m0
       BsRegs4 d0.2 d0.1 d1.2 d1.1 d2.2 d2.1 d3.2 d3.1 s4) →
      ChunkPreserved s s4 →
      SepWP P target_pc s4 Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr3 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx18⟩
  rw [decodeWords_bsChunk4Words] at hc; dsimp only [bsChunk4Instrs] at hc
  have_instrs hc 0 14
  wp_steps 14
  refine hnext _ (by simp [advanceWords, bsChunk4Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · dsimp only [BsRegs4, deltaSwap2]
    simp only [wp_norm, arm64_norm]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  · exact ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem bs_chunk5 {P : Program} {pc target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords bsChunk5Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hr4 : BsRegs4 u0 u1 u2 u3 u4 u5 u6 u7 s)
    (hnext : ∀ s5 : State, s5.pc = advanceWords pc bsChunk5Words → s5.status = .Running →
      (let m1 := 0x3333333333333333#64
       let d0 := deltaSwap2 u2 u0 2 m1
       let d1 := deltaSwap2 u3 u1 2 m1
       let d2 := deltaSwap2 u6 u4 2 m1
       let d3 := deltaSwap2 u7 u5 2 m1
       BsRegs5 d0.2 d1.2 d0.1 d1.1 d2.2 d3.2 d2.1 d3.1 s5) →
      ChunkPreserved s s5 →
      SepWP P target_pc s5 Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr4 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15⟩
  have_instrs hc 0 17
  wp_steps 17
  refine hnext _ (by simp [advanceWords, bsChunk5Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · dsimp only [BsRegs5, deltaSwap2]
    simp only [wp_norm, arm64_norm]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  · exact ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem bs_chunk6 {P : Program} {pc target_pc dst : BitVec 64}
    {s : State} {F : SepProp} {stOld : Model.FsState}
    {w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords bsChunk6Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = dst)
    (hr5 : BsRegs5 w0 w1 w2 w3 w4 w5 w6 w7 s)
    (hnext : ∀ sf : State, sf.pc = s.readReg64 (.gpr 30#5) → sf.status = .Running →
      ChunkPreserved s sf →
      (let m2 := 0x0f0f0f0f0f0f0f0f#64
       let d0 := deltaSwap2 w4 w0 4 m2
       let d1 := deltaSwap2 w5 w1 4 m2
       let d2 := deltaSwap2 w6 w2 4 m2
       let d3 := deltaSwap2 w7 w3 4 m2
       SepWP P target_pc sf (F ∗ fsStateAt dst ⟨d0.2, d1.2, d2.2, d3.2, d0.1, d1.1, d2.1, d3.1⟩) post oom)) :
    SepWP P target_pc s (F ∗ fsStateAt dst stOld) post oom := by
  rcases hr5 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx17⟩
  have_instrs hc 0 20
  dsimp only [fsStateAt]
  wp_steps 10; wp_stp64 hf_10 m1 hm1; wp_steps 2
  wp_stp64 hf_13 m2 hm2; wp_step; wp_stp64 hf_15 m3 hm3
  wp_steps 2; wp_stp64 hf_18 m4 hm4; wp_step
  have hz4 := BitVec.xor_comm ((w4 ^^^ (w0 >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64) w4
  have hz5 := BitVec.xor_comm ((w5 ^^^ (w1 >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64) w5
  have hz6 := BitVec.xor_comm ((w6 ^^^ (w2 >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64) w6
  have hz7 := BitVec.xor_comm ((w7 ^^^ (w3 >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64) w7
  refine Eq.mp (congrArg (fun Q => SepWP P target_pc _ (F ∗ Q) post oom) ?_)
    (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
       by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
       PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
         (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1])⟩)
  dsimp only [fsStateAt, deltaSwap2]
  simp only [hz4, hz5, hz6, hz7]

/-- Unified `SepWP` stepping lemma for `fixslice64::bitslice` over any input assertion `P_in`
    supplying `SepLoad8` witnesses for the four 16-byte input blocks `b0, b1, b2, b3`. -/
theorem step_bitslice {P : Program} {entry target_pc dst p0 p1 p2 p3 : BitVec 64}
    {s0 : State} {P_in R : SepProp} {b0 b1 b2 b3 : List (BitVec 8)}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P entry bitsliceInstrs)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst)
    (hx1 : s0.readReg64 .x1 = p0) (hx2 : s0.readReg64 .x2 = p1)
    (hx3 : s0.readReg64 .x3 = p2) (hx4 : s0.readReg64 .x4 = p3)
    (_hb0 : b0.length = 16) (_hb1 : b1.length = 16)
    (_hb2 : b2.length = 16) (_hb3 : b3.length = 16)
    (hl0 : ∀ i : Nat, i < 16 → SepLoad8 (p0 + BitVec.ofNat 64 i) P_in (b0.getD i 0#8))
    (hl1 : ∀ i : Nat, i < 16 → SepLoad8 (p1 + BitVec.ofNat 64 i) P_in (b1.getD i 0#8))
    (hl2 : ∀ i : Nat, i < 16 → SepLoad8 (p2 + BitVec.ofNat 64 i) P_in (b2.getD i 0#8))
    (hl3 : ∀ i : Nat, i < 16 → SepLoad8 (p3 + BitVec.ofNat 64 i) P_in (b3.getD i 0#8))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      PureStepPreserved s0 sf → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      SepWP P target_pc sf ((P_in ∗ fsStateAt dst (Model.bitslice ⟨b0, b1, b2, b3⟩)) ∗ R) post oom) :
    SepWP P target_pc s0 ((P_in ∗ memRegion dst 64) ∗ R) post oom := by
  rw [bitsliceInstrs_chunks] at hc
  obtain ⟨hc1, hc⟩ := split_decodeWords hc; obtain ⟨hc2, hc⟩ := split_decodeWords hc
  obtain ⟨hc3, hc⟩ := split_decodeWords hc; obtain ⟨hc4, hc⟩ := split_decodeWords hc
  obtain ⟨hc5, hc6⟩ := split_decodeWords hc
  have hx0' : s0.readReg64 (.gpr 0#5) = dst := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = p0 := hx1
  have hx2' : s0.readReg64 (.gpr 2#5) = p1 := hx2
  have hx3' : s0.readReg64 (.gpr 3#5) = p2 := hx3
  have hx4' : s0.readReg64 (.gpr 4#5) = p3 := hx4
  have hl0' : ∀ i : Nat, i < 16 →
      SepLoad8 (p0 + BitVec.ofNat 64 i) ((P_in ∗ memRegion dst 64) ∗ R) (b0.getD i 0#8) :=
    fun i hi => SepLoad8.sep_left (SepLoad8.sep_left (hl0 i hi) (memRegion dst 64)) R
  have hl1' : ∀ i : Nat, i < 16 →
      SepLoad8 (p1 + BitVec.ofNat 64 i) ((P_in ∗ memRegion dst 64) ∗ R) (b1.getD i 0#8) :=
    fun i hi => SepLoad8.sep_left (SepLoad8.sep_left (hl1 i hi) (memRegion dst 64)) R
  have hl2' : ∀ i : Nat, i < 16 →
      SepLoad8 (p2 + BitVec.ofNat 64 i) ((P_in ∗ memRegion dst 64) ∗ R) (b2.getD i 0#8) :=
    fun i hi => SepLoad8.sep_left (SepLoad8.sep_left (hl2 i hi) (memRegion dst 64)) R
  have hl3' : ∀ i : Nat, i < 16 →
      SepLoad8 (p3 + BitVec.ofNat 64 i) ((P_in ∗ memRegion dst 64) ∗ R) (b3.getD i 0#8) :=
    fun i hi => SepLoad8.sep_left (SepLoad8.sep_left (hl3 i hi) (memRegion dst 64)) R
  refine bs_chunk1 hc1 hpc hrun hx1' hx2' hx3' hx4' hl0' hl1'
    fun s1 hpc1 hrun1 hx1_1 hx2_1 hx3_1 hx4_1 hr1 hk1 => ?_
  refine bs_chunk2 hc2 hpc1 hrun1 hx1_1 hx2_1 hx3_1 hx4_1 hr1 hl0' hl1' hl2'
    fun s2 hpc2 hrun2 hx2_2 hx3_2 hx4_2 hr2 hk2 => ?_
  refine bs_chunk3 hc3 hpc2 hrun2 hx2_2 hx3_2 hx4_2 hr2 hl1' hl2' hl3'
    fun s3 hpc3 hrun3 hr3 hk3 => ?_
  refine bs_chunk4 hc4 hpc3 hrun3 hr3 fun s4 hpc4 hrun4 hr4 hk4 => ?_
  refine bs_chunk5 hc5 hpc4 hrun4 hr4 fun s5 hpc5 hrun5 hr5 hk5 => ?_
  have hk15 := hk1.trans (hk2.trans (hk3.trans (hk4.trans hk5)))
  have hreord : ∀ Q : SepProp, (P_in ∗ Q) ∗ R = (P_in ∗ R) ∗ Q := fun Q => by sep_ac_rfl
  rw [hreord (memRegion dst 64), memRegion64_eq_exists_fsStateAt dst, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro stOld
  refine bs_chunk6 hc6 hpc5 hrun5 (hk15.x0.trans hx0') hr5 fun sf hpc_f hrun_f hk6 => ?_
  have hk := hk15.trans hk6
  change SepWP P target_pc sf ((P_in ∗ R) ∗ fsStateAt dst (Model.bitslice ⟨b0, b1, b2, b3⟩)) post oom
  rw [← hreord (fsStateAt dst (Model.bitslice ⟨b0, b1, b2, b3⟩))]
  exact hnext sf (hpc_f.trans hk15.x30) hrun_f hk.purePres hk.sp hk.callee

/-- `subroutine_ok` contract for `bitslice(dst, src, src, src, src)` with aliased input pointers. -/
theorem bitslice_rep_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry bitsliceInstrs) :
    subroutine_ok P entry bitsliceRepSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ro, dst, src, b⟩ R s0 hpc hrun hpre _hsp
  dsimp only [bitsliceRepSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hb⟩, hpre⟩
  refine ⟨bytesAt ro src b ∗ memRegion dst 64, hpre, ?_⟩
  rw [← sepConj_emp (bytesAt ro src b ∗ memRegion dst 64)]
  have hl : ∀ i : Nat, i < 16 → SepLoad8 (src + BitVec.ofNat 64 i) (bytesAt ro src b) (b.getD i 0#8) :=
    fun i hi => SepLoad8.of_bytesAt (sepConj_emp (bytesAt ro src b)).symm (hb ▸ hi) rfl
  refine step_bitslice hc hpc hrun hx0 hx1 hx2 hx3 hx4 hb hb hb hb hl hl hl hl
    fun sf hpc_f hrun_f hpres hsp_f hcs => ?_
  rw [sepConj_emp]
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpres, hm⟩

/-- `subroutine_ok` contract for `bitslice(dst, src, src + 16, src + 32, src + 48)` on four
    contiguous 16-byte blocks `bs : Blocks4`. -/
theorem bitslice4_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry bitsliceInstrs) :
    subroutine_ok P entry bitslice4Spec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ro, dst, src, bs⟩ R s0 hpc hrun hpre _hsp
  dsimp only [bitslice4Spec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hwf⟩, hpre⟩
  rcases hwf with ⟨hb0, hb1, hb2, hb3⟩
  refine ⟨bytesAt ro src (blocks4Bytes bs) ∗ memRegion dst 64, hpre, ?_⟩
  rw [← sepConj_emp (bytesAt ro src (blocks4Bytes bs) ∗ memRegion dst 64)]
  have hsplit := bytesAt_blocks4_split ro src ⟨hb0, hb1, hb2, hb3⟩
  have hl0 : ∀ i : Nat, i < 16 →
      SepLoad8 (src + BitVec.ofNat 64 i) (bytesAt ro src (blocks4Bytes bs)) (bs.b0.getD i 0#8) := by
    intro i hi; rw [hsplit]
    exact SepLoad8.sep_left (SepLoad8.of_bytesAt (sepConj_emp _).symm (hb0 ▸ hi) rfl) _
  have hl1 : ∀ i : Nat, i < 16 →
      SepLoad8 ((src + 16#64) + BitVec.ofNat 64 i) (bytesAt ro src (blocks4Bytes bs)) (bs.b1.getD i 0#8) := by
    intro i hi; rw [hsplit]
    exact SepLoad8.sep_right _ (SepLoad8.sep_left (SepLoad8.of_bytesAt (sepConj_emp _).symm (hb1 ▸ hi) rfl) _)
  have hl2 : ∀ i : Nat, i < 16 →
      SepLoad8 ((src + 32#64) + BitVec.ofNat 64 i) (bytesAt ro src (blocks4Bytes bs)) (bs.b2.getD i 0#8) := by
    intro i hi; rw [hsplit]
    exact SepLoad8.sep_right _ (SepLoad8.sep_right _
      (SepLoad8.sep_left (SepLoad8.of_bytesAt (sepConj_emp _).symm (hb2 ▸ hi) rfl) _))
  have hl3 : ∀ i : Nat, i < 16 →
      SepLoad8 ((src + 48#64) + BitVec.ofNat 64 i) (bytesAt ro src (blocks4Bytes bs)) (bs.b3.getD i 0#8) := by
    intro i hi; rw [hsplit]
    exact SepLoad8.sep_right _ (SepLoad8.sep_right _ (SepLoad8.sep_right _
      (SepLoad8.of_bytesAt (sepConj_emp _).symm (hb3 ▸ hi) rfl)))
  refine step_bitslice hc hpc hrun hx0 hx1 hx2 hx3 hx4 hb0 hb1 hb2 hb3 hl0 hl1 hl2 hl3
    fun sf hpc_f hrun_f hpres hsp_f hcs => ?_
  rw [sepConj_emp]
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpres, hm⟩

/-! ## 5. `fixslice64::inv_bitslice` Chunk Decomposition & Verification -/

private def ibsChunk1Words : List (BitVec 32) :=
  [0xa9404429#32, 0xa941202a#32, 0xa942402b#32, 0xa943342c#32, 0xca49062e#32, 0xca4a050f#32,
   0xca4b0612#32, 0x9200f1c2#32, 0xca4c05a1#32, 0x9200f1e4#32, 0xca02052e#32, 0x9200f245#32,
   0xca040549#32, 0xca110051#32, 0x9200f02f#32, 0xca050572#32, 0xca080088#32, 0xca0f058a#32]

private def ibsChunk2Words : List (BitVec 32) :=
  [0xca4e092b#32, 0xca0d01ed#32, 0xca520941#32, 0x9200e56c#32, 0xca090189#32, 0x9200e42b#32,
   0xca0c09c1#32, 0xca0b0a4e#32, 0xca0a016a#32, 0xca4111d2#32, 0x9200ce52#32, 0xca0e024e#32,
   0xca121032#32, 0xca1000a1#32]

private def ibsChunk3Words : List (BitVec 32) :=
  [0xd350fdc3#32, 0xd360fdc2#32, 0xd370fdd0#32, 0xd350fe4f#32, 0xca4109a4#32, 0xd370fe45#32,
   0x39001403#32, 0xd360fe43#32, 0x39001802#32, 0xca510902#32, 0x39001c10#32, 0x3900040f#32,
   0x9200e450#32, 0x9200e48f#32, 0x39000803#32, 0xd348fe43#32, 0xca100a31#32, 0xd358fe42#32,
   0xca0f0821#32, 0x39000012#32, 0x39002003#32, 0xd368fe43#32, 0xd378fe52#32, 0x39002402#32,
   0xca511022#32, 0xca080208#32, 0x39002c12#32, 0xd358fdd2#32, 0xca0d01ed#32]

private def ibsChunk4Words : List (BitVec 32) :=
  [0x9200cc42#32, 0x39002803#32, 0xd348fdc3#32, 0xca021231#32, 0x39003412#32, 0xd368fdd2#32,
   0x3900100e#32, 0xd378fdce#32, 0xca010041#32, 0xd368fe2c#32, 0xd378fe2b#32, 0x39003812#32,
   0x39003c0e#32, 0xd360fe2e#32, 0xd350fe32#32, 0x3900680c#32, 0xd348fc2c#32, 0x3900480e#32,
   0xd350fc2e#32, 0x39006c0b#32, 0xd358fc2b#32, 0x3900540e#32, 0xd370fc2e#32, 0x3900700c#32,
   0x39005c0e#32, 0xd358fe2e#32, 0x3900740b#32, 0xd368fc2b#32, 0x3900640e#32]

private def ibsChunk5Words : List (BitVec 32) :=
  [0xca49114e#32, 0x3900780b#32, 0x9200cdcc#32, 0xd378fc2e#32, 0x39004412#32, 0xca0c1129#32,
   0xca0a018a#32, 0xd370fe32#32, 0xd350fd4c#32, 0x39007c0e#32, 0xd350fd2b#32, 0xd360fd2e#32,
   0x39008009#32, 0x3900940c#32, 0xd370fd4c#32, 0x3900840b#32, 0xd370fd2b#32, 0x39009c0c#32,
   0xd368fd2c#32, 0x39008c0b#32, 0xd360fd4b#32, 0x3900a80c#32, 0xd348fd4c#32, 0x3900980b#32,
   0xd348fd2b#32, 0x3900900a#32, 0x3900a00b#32, 0xd358fd2b#32, 0xd378fd29#32, 0x39004c12#32,
   0xd360fc32#32, 0x3900a40b#32, 0xca4811ab#32, 0x3900ac09#32, 0xd358fd49#32, 0x9200cd6b#32,
   0x39005812#32, 0xd348fe32#32, 0xca0b1108#32, 0x3900b409#32, 0xd368fd49#32, 0xd378fd4a#32,
   0xca0d016b#32, 0x39000c05#32]

private def ibsChunk6Words : List (BitVec 32) :=
  [0x3900b809#32, 0xd350fd09#32, 0x3900bc0a#32, 0xd360fd0a#32, 0x3900c409#32, 0xd370fd09#32,
   0x3900c80a#32, 0xd350fd6a#32, 0x3900cc09#32, 0xd360fd69#32, 0x3900d40a#32, 0xd370fd6a#32,
   0x3900d809#32, 0xd348fd09#32, 0x3900dc0a#32, 0xd358fd0a#32, 0x3900e009#32, 0xd368fd09#32,
   0x3900c008#32, 0xd378fd08#32, 0x3900e809#32, 0xd348fd69#32, 0x3900ec08#32, 0xd358fd68#32,
   0x3900f009#32, 0xd378fd69#32, 0x3900f408#32, 0xd368fd68#32, 0x39003003#32, 0x39006012#32,
   0x39004011#32, 0x39005001#32, 0x3900880e#32, 0x3900b00c#32, 0x3900e40a#32, 0x3900d00b#32,
   0x3900f808#32, 0x3900fc09#32, 0xd65f03c0#32]

private theorem invBitsliceInstrs_chunks :
    invBitsliceInstrs =
      decodeWords ibsChunk1Words ++
      (decodeWords ibsChunk2Words ++
      (decodeWords ibsChunk3Words ++
      (decodeWords ibsChunk4Words ++
      (decodeWords ibsChunk5Words ++ decodeWords ibsChunk6Words)))) := by
  have hw : invBitsliceWords =
      ibsChunk1Words ++ (ibsChunk2Words ++ (ibsChunk3Words ++
        (ibsChunk4Words ++ (ibsChunk5Words ++ ibsChunk6Words)))) := rfl
  simp only [invBitsliceInstrs, hw, decodeWords, List.map_append]

private def ibsPre3 (dst : BitVec 64) (stOld : Model.FsState) : SepProp :=
  (dst ↦₈ (stOld.s0.extractLsb' 0 8)) ∗ ((dst + 1#64) ↦₈ (stOld.s0.extractLsb' 8 8)) ∗ ((dst + 2#64) ↦₈ (stOld.s0.extractLsb' 16 8)) ∗
  ((dst + 5#64) ↦₈ (stOld.s0.extractLsb' 40 8)) ∗ ((dst + 6#64) ↦₈ (stOld.s0.extractLsb' 48 8)) ∗ ((dst + 7#64) ↦₈ (stOld.s0.extractLsb' 56 8)) ∗
  ((dst + 8#64) ↦₈ (stOld.s1.extractLsb' 0 8)) ∗ ((dst + 9#64) ↦₈ (stOld.s1.extractLsb' 8 8)) ∗ ((dst + 11#64) ↦₈ (stOld.s1.extractLsb' 24 8))

private def ibsPre4 (dst : BitVec 64) (stOld : Model.FsState) : SepProp :=
  ((dst + 4#64) ↦₈ (stOld.s0.extractLsb' 32 8)) ∗ ((dst + 10#64) ↦₈ (stOld.s1.extractLsb' 16 8)) ∗ ((dst + 13#64) ↦₈ (stOld.s1.extractLsb' 40 8)) ∗
  ((dst + 14#64) ↦₈ (stOld.s1.extractLsb' 48 8)) ∗ ((dst + 15#64) ↦₈ (stOld.s1.extractLsb' 56 8)) ∗ ((dst + 18#64) ↦₈ (stOld.s2.extractLsb' 16 8)) ∗
  ((dst + 21#64) ↦₈ (stOld.s2.extractLsb' 40 8)) ∗ ((dst + 23#64) ↦₈ (stOld.s2.extractLsb' 56 8)) ∗ ((dst + 25#64) ↦₈ (stOld.s3.extractLsb' 8 8)) ∗
  ((dst + 26#64) ↦₈ (stOld.s3.extractLsb' 16 8)) ∗ ((dst + 27#64) ↦₈ (stOld.s3.extractLsb' 24 8)) ∗ ((dst + 28#64) ↦₈ (stOld.s3.extractLsb' 32 8)) ∗
  ((dst + 29#64) ↦₈ (stOld.s3.extractLsb' 40 8))

private def ibsPre5 (dst : BitVec 64) (stOld : Model.FsState) : SepProp :=
  ((dst + 3#64) ↦₈ (stOld.s0.extractLsb' 24 8)) ∗ ((dst + 17#64) ↦₈ (stOld.s2.extractLsb' 8 8)) ∗ ((dst + 19#64) ↦₈ (stOld.s2.extractLsb' 24 8)) ∗
  ((dst + 22#64) ↦₈ (stOld.s2.extractLsb' 48 8)) ∗ ((dst + 30#64) ↦₈ (stOld.s3.extractLsb' 48 8)) ∗ ((dst + 31#64) ↦₈ (stOld.s3.extractLsb' 56 8)) ∗
  ((dst + 32#64) ↦₈ (stOld.s4.extractLsb' 0 8)) ∗ ((dst + 33#64) ↦₈ (stOld.s4.extractLsb' 8 8)) ∗ ((dst + 35#64) ↦₈ (stOld.s4.extractLsb' 24 8)) ∗
  ((dst + 36#64) ↦₈ (stOld.s4.extractLsb' 32 8)) ∗ ((dst + 37#64) ↦₈ (stOld.s4.extractLsb' 40 8)) ∗ ((dst + 38#64) ↦₈ (stOld.s4.extractLsb' 48 8)) ∗
  ((dst + 39#64) ↦₈ (stOld.s4.extractLsb' 56 8)) ∗ ((dst + 40#64) ↦₈ (stOld.s5.extractLsb' 0 8)) ∗ ((dst + 41#64) ↦₈ (stOld.s5.extractLsb' 8 8)) ∗
  ((dst + 42#64) ↦₈ (stOld.s5.extractLsb' 16 8)) ∗ ((dst + 43#64) ↦₈ (stOld.s5.extractLsb' 24 8)) ∗ ((dst + 45#64) ↦₈ (stOld.s5.extractLsb' 40 8))

private def ibsPre6 (dst : BitVec 64) (stOld : Model.FsState) : SepProp :=
  ((dst + 12#64) ↦₈ (stOld.s1.extractLsb' 32 8)) ∗ ((dst + 16#64) ↦₈ (stOld.s2.extractLsb' 0 8)) ∗ ((dst + 20#64) ↦₈ (stOld.s2.extractLsb' 32 8)) ∗
  ((dst + 24#64) ↦₈ (stOld.s3.extractLsb' 0 8)) ∗ ((dst + 34#64) ↦₈ (stOld.s4.extractLsb' 16 8)) ∗ ((dst + 44#64) ↦₈ (stOld.s5.extractLsb' 32 8)) ∗
  ((dst + 46#64) ↦₈ (stOld.s5.extractLsb' 48 8)) ∗ ((dst + 47#64) ↦₈ (stOld.s5.extractLsb' 56 8)) ∗ ((dst + 48#64) ↦₈ (stOld.s6.extractLsb' 0 8)) ∗
  ((dst + 49#64) ↦₈ (stOld.s6.extractLsb' 8 8)) ∗ ((dst + 50#64) ↦₈ (stOld.s6.extractLsb' 16 8)) ∗ ((dst + 51#64) ↦₈ (stOld.s6.extractLsb' 24 8)) ∗
  ((dst + 52#64) ↦₈ (stOld.s6.extractLsb' 32 8)) ∗ ((dst + 53#64) ↦₈ (stOld.s6.extractLsb' 40 8)) ∗ ((dst + 54#64) ↦₈ (stOld.s6.extractLsb' 48 8)) ∗
  ((dst + 55#64) ↦₈ (stOld.s6.extractLsb' 56 8)) ∗ ((dst + 56#64) ↦₈ (stOld.s7.extractLsb' 0 8)) ∗ ((dst + 57#64) ↦₈ (stOld.s7.extractLsb' 8 8)) ∗
  ((dst + 58#64) ↦₈ (stOld.s7.extractLsb' 16 8)) ∗ ((dst + 59#64) ↦₈ (stOld.s7.extractLsb' 24 8)) ∗ ((dst + 60#64) ↦₈ (stOld.s7.extractLsb' 32 8)) ∗
  ((dst + 61#64) ↦₈ (stOld.s7.extractLsb' 40 8)) ∗ ((dst + 62#64) ↦₈ (stOld.s7.extractLsb' 48 8)) ∗ ((dst + 63#64) ↦₈ (stOld.s7.extractLsb' 56 8))

private def ibsPost3 (dst z0 z4 : BitVec 64) : SepProp :=
  (dst ↦₈ z0.truncate 8) ∗ ((dst + 1#64) ↦₈ (z0 >>> 16).truncate 8) ∗ ((dst + 2#64) ↦₈ (z0 >>> 32).truncate 8) ∗
  ((dst + 5#64) ↦₈ (z4 >>> 16).truncate 8) ∗ ((dst + 6#64) ↦₈ (z4 >>> 32).truncate 8) ∗ ((dst + 7#64) ↦₈ (z4 >>> 48).truncate 8) ∗
  ((dst + 8#64) ↦₈ (z0 >>> 8).truncate 8) ∗ ((dst + 9#64) ↦₈ (z0 >>> 24).truncate 8) ∗ ((dst + 11#64) ↦₈ (z0 >>> 56).truncate 8)

private def ibsPost4 (dst z0 z4 z1 z5 : BitVec 64) : SepProp :=
  ((dst + 4#64) ↦₈ z4.truncate 8) ∗ ((dst + 10#64) ↦₈ (z0 >>> 40).truncate 8) ∗ ((dst + 13#64) ↦₈ (z4 >>> 24).truncate 8) ∗
  ((dst + 14#64) ↦₈ (z4 >>> 40).truncate 8) ∗ ((dst + 15#64) ↦₈ (z4 >>> 56).truncate 8) ∗ ((dst + 18#64) ↦₈ (z1 >>> 32).truncate 8) ∗
  ((dst + 21#64) ↦₈ (z5 >>> 16).truncate 8) ∗ ((dst + 23#64) ↦₈ (z5 >>> 48).truncate 8) ∗ ((dst + 25#64) ↦₈ (z1 >>> 24).truncate 8) ∗
  ((dst + 26#64) ↦₈ (z1 >>> 40).truncate 8) ∗ ((dst + 27#64) ↦₈ (z1 >>> 56).truncate 8) ∗ ((dst + 28#64) ↦₈ (z5 >>> 8).truncate 8) ∗
  ((dst + 29#64) ↦₈ (z5 >>> 24).truncate 8)

private def ibsPost5 (dst z0 z1 z5 z2 z6 : BitVec 64) : SepProp :=
  ((dst + 3#64) ↦₈ (z0 >>> 48).truncate 8) ∗ ((dst + 17#64) ↦₈ (z1 >>> 16).truncate 8) ∗ ((dst + 19#64) ↦₈ (z1 >>> 48).truncate 8) ∗
  ((dst + 22#64) ↦₈ (z5 >>> 32).truncate 8) ∗ ((dst + 30#64) ↦₈ (z5 >>> 40).truncate 8) ∗ ((dst + 31#64) ↦₈ (z5 >>> 56).truncate 8) ∗
  ((dst + 32#64) ↦₈ z2.truncate 8) ∗ ((dst + 33#64) ↦₈ (z2 >>> 16).truncate 8) ∗ ((dst + 35#64) ↦₈ (z2 >>> 48).truncate 8) ∗
  ((dst + 36#64) ↦₈ z6.truncate 8) ∗ ((dst + 37#64) ↦₈ (z6 >>> 16).truncate 8) ∗ ((dst + 38#64) ↦₈ (z6 >>> 32).truncate 8) ∗
  ((dst + 39#64) ↦₈ (z6 >>> 48).truncate 8) ∗ ((dst + 40#64) ↦₈ (z2 >>> 8).truncate 8) ∗ ((dst + 41#64) ↦₈ (z2 >>> 24).truncate 8) ∗
  ((dst + 42#64) ↦₈ (z2 >>> 40).truncate 8) ∗ ((dst + 43#64) ↦₈ (z2 >>> 56).truncate 8) ∗ ((dst + 45#64) ↦₈ (z6 >>> 24).truncate 8)

private def ibsPost6 (dst z4 z1 z5 z2 z6 z3 z7 : BitVec 64) : SepProp :=
  ((dst + 12#64) ↦₈ (z4 >>> 8).truncate 8) ∗ ((dst + 16#64) ↦₈ z1.truncate 8) ∗ ((dst + 20#64) ↦₈ z5.truncate 8) ∗
  ((dst + 24#64) ↦₈ (z1 >>> 8).truncate 8) ∗ ((dst + 34#64) ↦₈ (z2 >>> 32).truncate 8) ∗ ((dst + 44#64) ↦₈ (z6 >>> 8).truncate 8) ∗
  ((dst + 46#64) ↦₈ (z6 >>> 40).truncate 8) ∗ ((dst + 47#64) ↦₈ (z6 >>> 56).truncate 8) ∗ ((dst + 48#64) ↦₈ z3.truncate 8) ∗
  ((dst + 49#64) ↦₈ (z3 >>> 16).truncate 8) ∗ ((dst + 50#64) ↦₈ (z3 >>> 32).truncate 8) ∗ ((dst + 51#64) ↦₈ (z3 >>> 48).truncate 8) ∗
  ((dst + 52#64) ↦₈ z7.truncate 8) ∗ ((dst + 53#64) ↦₈ (z7 >>> 16).truncate 8) ∗ ((dst + 54#64) ↦₈ (z7 >>> 32).truncate 8) ∗
  ((dst + 55#64) ↦₈ (z7 >>> 48).truncate 8) ∗ ((dst + 56#64) ↦₈ (z3 >>> 8).truncate 8) ∗ ((dst + 57#64) ↦₈ (z3 >>> 24).truncate 8) ∗
  ((dst + 58#64) ↦₈ (z3 >>> 40).truncate 8) ∗ ((dst + 59#64) ↦₈ (z3 >>> 56).truncate 8) ∗ ((dst + 60#64) ↦₈ (z7 >>> 8).truncate 8) ∗
  ((dst + 61#64) ↦₈ (z7 >>> 24).truncate 8) ∗ ((dst + 62#64) ↦₈ (z7 >>> 40).truncate 8) ∗ ((dst + 63#64) ↦₈ (z7 >>> 56).truncate 8)

private theorem fsStateAt_split_ibs (dst : BitVec 64) (stOld : Model.FsState) :
    fsStateAt dst stOld =
      ibsPre3 dst stOld ∗ (ibsPre4 dst stOld ∗ (ibsPre5 dst stOld ∗ ibsPre6 dst stOld)) := by
  rw [fsStateAt_eq_pointsToBytes]
  dsimp only [fsStateBytes, unpack64, List.cons_append, List.nil_append,
    ibsPre3, ibsPre4, ibsPre5, ibsPre6]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  sep_ac_rfl

private theorem ibsPost_merge (dst z0 z4 z1 z5 z2 z6 z3 z7 : BitVec 64) :
    ibsPost3 dst z0 z4 ∗
      (ibsPost4 dst z0 z4 z1 z5 ∗
      (ibsPost5 dst z0 z1 z5 z2 z6 ∗ ibsPost6 dst z4 z1 z5 z2 z6 z3 z7)) =
      (dst ↦ₛ (writeReorderedPair z0 z4 ++ writeReorderedPair z1 z5 ++
        writeReorderedPair z2 z6 ++ writeReorderedPair z3 z7)) := by
  dsimp only [writeReorderedPair, List.cons_append, List.nil_append,
    ibsPost3, ibsPost4, ibsPost5, ibsPost6]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ushiftRight_zero]
  sep_ac_rfl

private def IbsRegs1 (st : Model.FsState) (u0 u1 u2 u3 u4 u6 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 5#5) = (st.s5 ^^^ (st.s4 >>> 1)) &&& 0x5555555555555555#64 ∧
  s.readReg64 (.gpr 8#5) = u3 ∧
  s.readReg64 (.gpr 9#5) = u2 ∧
  s.readReg64 (.gpr 10#5) = u6 ∧
  s.readReg64 (.gpr 13#5) = st.s7 ∧
  s.readReg64 (.gpr 14#5) = u0 ∧
  s.readReg64 (.gpr 15#5) = (st.s7 ^^^ (st.s6 >>> 1)) &&& 0x5555555555555555#64 ∧
  s.readReg64 (.gpr 16#5) = st.s5 ∧
  s.readReg64 (.gpr 17#5) = u1 ∧
  s.readReg64 (.gpr 18#5) = u4

private def IbsRegs2 (u1 u3 u5 u7 w2 w6 z0 z4 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 1#5) = u5 ∧
  s.readReg64 (.gpr 8#5) = u3 ∧
  s.readReg64 (.gpr 9#5) = w2 ∧
  s.readReg64 (.gpr 10#5) = w6 ∧
  s.readReg64 (.gpr 13#5) = u7 ∧
  s.readReg64 (.gpr 14#5) = z4 ∧
  s.readReg64 (.gpr 17#5) = u1 ∧
  s.readReg64 (.gpr 18#5) = z0

private def IbsRegs3 (w1 w2 w3 w5 w6 w7 z0 z4 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 1#5) = w5 ∧
  s.readReg64 (.gpr 2#5) = w5 ^^^ (w1 >>> 4) ∧
  s.readReg64 (.gpr 3#5) = z0 >>> 40 ∧
  s.readReg64 (.gpr 5#5) = z0 >>> 48 ∧
  s.readReg64 (.gpr 8#5) = w3 ∧
  s.readReg64 (.gpr 9#5) = w2 ∧
  s.readReg64 (.gpr 10#5) = w6 ∧
  s.readReg64 (.gpr 13#5) = w7 ∧
  s.readReg64 (.gpr 14#5) = z4 ∧
  s.readReg64 (.gpr 17#5) = w1 ∧
  s.readReg64 (.gpr 18#5) = z4 >>> 24

private def IbsRegs4 (w2 w3 w6 w7 z0 z4 z1 z5 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 1#5) = z5 ∧
  s.readReg64 (.gpr 3#5) = z4 >>> 8 ∧
  s.readReg64 (.gpr 5#5) = z0 >>> 48 ∧
  s.readReg64 (.gpr 8#5) = w3 ∧
  s.readReg64 (.gpr 9#5) = w2 ∧
  s.readReg64 (.gpr 10#5) = w6 ∧
  s.readReg64 (.gpr 11#5) = z5 >>> 40 ∧
  s.readReg64 (.gpr 13#5) = w7 ∧
  s.readReg64 (.gpr 17#5) = z1 ∧
  s.readReg64 (.gpr 18#5) = z1 >>> 16

private def IbsRegs5 (z4 z1 z5 z2 z6 z3 z7 : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 1#5) = z5 ∧
  s.readReg64 (.gpr 3#5) = z4 >>> 8 ∧
  s.readReg64 (.gpr 8#5) = z3 ∧
  s.readReg64 (.gpr 9#5) = z6 >>> 40 ∧
  s.readReg64 (.gpr 10#5) = z6 >>> 56 ∧
  s.readReg64 (.gpr 11#5) = z7 ∧
  s.readReg64 (.gpr 12#5) = z6 >>> 8 ∧
  s.readReg64 (.gpr 14#5) = z2 >>> 32 ∧
  s.readReg64 (.gpr 17#5) = z1 ∧
  s.readReg64 (.gpr 18#5) = z1 >>> 8

private def ibsChunk1Instrs : List Instr :=
  [.ldp .W64 false (.gpr 9#5) (.gpr 17#5) (.Offset (.gpr 1#5) 0#64),
   .ldp .W64 false (.gpr 10#5) (.gpr 8#5) (.Offset (.gpr 1#5) 16#64),
   .ldp .W64 false (.gpr 11#5) (.gpr 16#5) (.Offset (.gpr 1#5) 32#64),
   .ldp .W64 false (.gpr 12#5) (.gpr 13#5) (.Offset (.gpr 1#5) 48#64),
   .logicalShift .W64 .EOR (.gpr 14#5) (.gpr 17#5) (.gpr 9#5) .LSR 1,
   .logicalShift .W64 .EOR (.gpr 15#5) (.gpr 8#5) (.gpr 10#5) .LSR 1,
   .logicalShift .W64 .EOR (.gpr 18#5) (.gpr 16#5) (.gpr 11#5) .LSR 1,
   .logicalImm .W64 .AND (.gpr 2#5) (.gpr 14#5) 0x5555555555555555#64,
   .logicalShift .W64 .EOR (.gpr 1#5) (.gpr 13#5) (.gpr 12#5) .LSR 1,
   .logicalImm .W64 .AND (.gpr 4#5) (.gpr 15#5) 0x5555555555555555#64,
   .logicalShift .W64 .EOR (.gpr 14#5) (.gpr 9#5) (.gpr 2#5) .LSL 1,
   .logicalImm .W64 .AND (.gpr 5#5) (.gpr 18#5) 0x5555555555555555#64,
   .logicalShift .W64 .EOR (.gpr 9#5) (.gpr 10#5) (.gpr 4#5) .LSL 1,
   .logicalShift .W64 .EOR (.gpr 17#5) (.gpr 2#5) (.gpr 17#5) .LSL 0,
   .logicalImm .W64 .AND (.gpr 15#5) (.gpr 1#5) 0x5555555555555555#64,
   .logicalShift .W64 .EOR (.gpr 18#5) (.gpr 11#5) (.gpr 5#5) .LSL 1,
   .logicalShift .W64 .EOR (.gpr 8#5) (.gpr 4#5) (.gpr 8#5) .LSL 0,
   .logicalShift .W64 .EOR (.gpr 10#5) (.gpr 12#5) (.gpr 15#5) .LSL 1]

private theorem decodeWords_ibsChunk1Words : decodeWords ibsChunk1Words = ibsChunk1Instrs := by decide

private theorem ibs_chunk1 {P : Program} {pc target_pc src : BitVec 64}
    {s : State} {F : SepProp} {st : Model.FsState}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords ibsChunk1Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx1 : s.readReg64 (.gpr 1#5) = src)
    (hnext : ∀ s1 : State, s1.pc = advanceWords pc ibsChunk1Words → s1.status = .Running →
      (let m0 := 0x5555555555555555#64
       let d0 := deltaSwap2 st.s1 st.s0 1 m0
       let d1 := deltaSwap2 st.s3 st.s2 1 m0
       let d2 := deltaSwap2 st.s5 st.s4 1 m0
       let d3 := deltaSwap2 st.s7 st.s6 1 m0
       IbsRegs1 st d0.2 d0.1 d1.2 d1.1 d2.2 d3.2 s1) →
      ChunkPreserved s s1 →
      SepWP P target_pc s1 (fsStateAt src st ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt src st ∗ F) post oom := by
  rw [decodeWords_ibsChunk1Words] at hc; dsimp only [ibsChunk1Instrs] at hc
  have_instrs hc 0 18
  dsimp only [fsStateAt]
  wp_steps 18
  change SepWP P target_pc _ (fsStateAt src st ∗ F) post oom
  refine hnext _ (by simp [advanceWords, ibsChunk1Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · dsimp only [IbsRegs1, deltaSwap2]
    simp only [wp_norm, arm64_norm]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  · exact ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem ibs_chunk2 {P : Program} {pc target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {st : Model.FsState} {u0 u1 u2 u3 u4 u6 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords ibsChunk2Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hr1 : IbsRegs1 st u0 u1 u2 u3 u4 u6 s)
    (hnext : ∀ s2 : State, s2.pc = advanceWords pc ibsChunk2Words → s2.status = .Running →
      (let m0 := 0x5555555555555555#64
       let d2 := deltaSwap2 st.s5 st.s4 1 m0
       let d3 := deltaSwap2 st.s7 st.s6 1 m0
       let m1 := 0x3333333333333333#64
       let dw0 := deltaSwap2 u2 u0 2 m1
       let dw2 := deltaSwap2 u6 u4 2 m1
       let m2 := 0x0f0f0f0f0f0f0f0f#64
       let dz0 := deltaSwap2 dw2.2 dw0.2 4 m2
       IbsRegs2 u1 u3 d2.1 d3.1 dw0.1 dw2.1 dz0.2 dz0.1 s2) →
      ChunkPreserved s s2 →
      SepWP P target_pc s2 Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr1 with ⟨hx5, hx8, hx9, hx10, hx13, hx14, hx15, hx16, hx17, hx18⟩
  have_instrs hc 0 14
  wp_steps 14
  refine hnext _ (by simp [advanceWords, ibsChunk2Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [IbsRegs2, deltaSwap2, wp_norm, arm64_norm, hx8, hx17, BitVec.xor_comm]
  · exact ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem ibs_chunk3 {P : Program} {pc target_pc dst : BitVec 64}
    {s : State} {F : SepProp} {stOld : Model.FsState}
    {u1 u3 u5 u7 w2 w6 z0 z4 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords ibsChunk3Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = dst)
    (hr2 : IbsRegs2 u1 u3 u5 u7 w2 w6 z0 z4 s)
    (hnext : ∀ s3 : State, s3.pc = advanceWords pc ibsChunk3Words → s3.status = .Running →
      (let m1 := 0x3333333333333333#64
       let dw1 := deltaSwap2 u3 u1 2 m1
       let dw3 := deltaSwap2 u7 u5 2 m1
       IbsRegs3 dw1.2 w2 dw1.1 dw3.2 w6 dw3.1 z0 z4 s3) →
      ChunkPreserved s s3 →
      SepWP P target_pc s3 (ibsPost3 dst z0 z4 ∗ F) post oom) :
    SepWP P target_pc s (ibsPre3 dst stOld ∗ F) post oom := by
  rcases hr2 with ⟨hx1, hx8, hx9, hx10, hx13, hx14, hx17, hx18⟩
  have_instrs hc 0 29
  dsimp only [ibsPre3]
  wp_steps 6; wp_str8 hf_6 m1 hm1; wp_step
  wp_str8 hf_8 m2 hm2; wp_step; wp_str8 hf_10 m3 hm3
  wp_str8 hf_11 m4 hm4; wp_steps 2; wp_str8 hf_14 m5 hm5
  wp_steps 4; wp_str8 hf_19 m6 hm6; wp_str8 hf_20 m7 hm7
  wp_steps 2; wp_str8 hf_23 m8 hm8; wp_steps 2
  wp_str8 hf_26 m9 hm9; wp_steps 2
  exact hnext _ (by simp [advanceWords, ibsChunk3Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by dsimp only [IbsRegs3, deltaSwap2]
        simp only [wp_norm, arm64_norm, hx9, hx10, hx14]
        exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩)
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
       (by simp [wp_norm, arm64_norm, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1])⟩

private theorem ibs_chunk4 {P : Program} {pc target_pc dst : BitVec 64}
    {s : State} {F : SepProp} {stOld : Model.FsState}
    {w1 w2 w3 w5 w6 w7 z0 z4 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords ibsChunk4Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = dst)
    (hr3 : IbsRegs3 w1 w2 w3 w5 w6 w7 z0 z4 s)
    (hnext : ∀ s4 : State, s4.pc = advanceWords pc ibsChunk4Words → s4.status = .Running →
      (let dz1 := deltaSwap2 w5 w1 4 0x0f0f0f0f0f0f0f0f#64
       IbsRegs4 w2 w3 w6 w7 z0 z4 dz1.2 dz1.1 s4) →
      ChunkPreserved s s4 →
      SepWP P target_pc s4
        (ibsPost4 dst z0 z4
          (deltaSwap2 w5 w1 4 0x0f0f0f0f0f0f0f0f#64).2
          (deltaSwap2 w5 w1 4 0x0f0f0f0f0f0f0f0f#64).1 ∗ F) post oom) :
    SepWP P target_pc s (ibsPre4 dst stOld ∗ F) post oom := by
  rcases hr3 with ⟨hx1, hx2, hx3, hx5, hx8, hx9, hx10, hx13, hx14, hx17, hx18⟩
  have_instrs hc 0 29
  dsimp only [ibsPre4]
  wp_step; wp_str8 hf_1 m1 hm1; wp_steps 2
  wp_str8 hf_4 m2 hm2; wp_step; wp_str8 hf_6 m3 hm3
  wp_steps 4; wp_str8 hf_11 m4 hm4; wp_str8 hf_12 m5 hm5
  wp_steps 2; wp_str8 hf_15 m6 hm6; wp_step
  wp_str8 hf_17 m7 hm7; wp_step; wp_str8 hf_19 m8 hm8
  wp_step; wp_str8 hf_21 m9 hm9; wp_step
  wp_str8 hf_23 m10 hm10; wp_str8 hf_24 m11 hm11; wp_step
  wp_str8 hf_26 m12 hm12; wp_step; wp_str8 hf_28 m13 hm13
  have hz5 := BitVec.xor_comm ((w5 ^^^ (w1 >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64) w5
  refine Eq.mp (congrArg (fun Q => SepWP P target_pc _ (Q ∗ F) post oom) ?_)
    (hnext _ (by simp [advanceWords, ibsChunk4Words, wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by dsimp only [IbsRegs4, deltaSwap2]
          simp only [wp_norm, arm64_norm, hx5, hx8, hx9, hx10, hx13, hz5])
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
       by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
       PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
         (by simp [wp_norm, arm64_norm, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1])⟩)
  dsimp only [ibsPost4, deltaSwap2]
  simp only [hz5.symm]

private theorem ibs_chunk5 {P : Program} {pc target_pc dst : BitVec 64}
    {s : State} {F : SepProp} {stOld : Model.FsState}
    {w2 w3 w6 w7 z0 z4 z1 z5 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords ibsChunk5Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = dst)
    (hr4 : IbsRegs4 w2 w3 w6 w7 z0 z4 z1 z5 s)
    (hnext : ∀ s5 : State, s5.pc = advanceWords pc ibsChunk5Words → s5.status = .Running →
      (let dz2 := deltaSwap2 w6 w2 4 0x0f0f0f0f0f0f0f0f#64
       let dz3 := deltaSwap2 w7 w3 4 0x0f0f0f0f0f0f0f0f#64
       IbsRegs5 z4 z1 z5 dz2.2 dz2.1 dz3.2 dz3.1 s5) →
      ChunkPreserved s s5 →
      SepWP P target_pc s5
        (ibsPost5 dst z0 z1 z5
          (deltaSwap2 w6 w2 4 0x0f0f0f0f0f0f0f0f#64).2
          (deltaSwap2 w6 w2 4 0x0f0f0f0f0f0f0f0f#64).1 ∗ F) post oom) :
    SepWP P target_pc s (ibsPre5 dst stOld ∗ F) post oom := by
  rcases hr4 with ⟨hx1, hx3, hx5, hx8, hx9, hx10, hx11, hx13, hx17, hx18⟩
  have_instrs hc 0 44
  dsimp only [ibsPre5]
  wp_step; wp_str8 hf_1 m1 hm1; wp_steps 2
  wp_str8 hf_4 m2 hm2; wp_steps 4; wp_str8 hf_9 m3 hm3
  wp_steps 2; wp_str8 hf_12 m4 hm4; wp_str8 hf_13 m5 hm5
  wp_step; wp_str8 hf_15 m6 hm6; wp_step
  wp_str8 hf_17 m7 hm7; wp_step; wp_str8 hf_19 m8 hm8
  wp_step; wp_str8 hf_21 m9 hm9; wp_step
  wp_str8 hf_23 m10 hm10; wp_step; wp_str8 hf_25 m11 hm11
  wp_str8 hf_26 m12 hm12; wp_steps 2; wp_str8 hf_29 m13 hm13
  wp_step; wp_str8 hf_31 m14 hm14; wp_step
  wp_str8 hf_33 m15 hm15; wp_steps 2; wp_str8 hf_36 m16 hm16
  wp_steps 2; wp_str8 hf_39 m17 hm17; wp_steps 3
  wp_str8 hf_43 m18 hm18
  have hz6 := BitVec.xor_comm ((w6 ^^^ (w2 >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64) w6
  have hz7 := BitVec.xor_comm ((w7 ^^^ (w3 >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64) w7
  refine Eq.mp (congrArg (fun Q => SepWP P target_pc _ (Q ∗ F) post oom) ?_)
    (hnext _ (by simp [advanceWords, ibsChunk5Words, wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by dsimp only [IbsRegs5, deltaSwap2]
          simp only [wp_norm, arm64_norm, hx1, hx3, hx17, hz6, hz7])
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
       by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
       PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
         (by simp [wp_norm, arm64_norm, hm18, hm17, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1])⟩)
  dsimp only [ibsPost5, deltaSwap2]
  simp only [hz6.symm, wp_norm, arm64_norm]

private theorem ibs_chunk6 {P : Program} {pc target_pc dst : BitVec 64}
    {s : State} {F : SepProp} {stOld : Model.FsState}
    {z4 z1 z5 z2 z6 z3 z7 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc (decodeWords ibsChunk6Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx0 : s.readReg64 (.gpr 0#5) = dst)
    (hr5 : IbsRegs5 z4 z1 z5 z2 z6 z3 z7 s)
    (hnext : ∀ sf : State, sf.pc = s.readReg64 (.gpr 30#5) → sf.status = .Running →
      ChunkPreserved s sf →
      SepWP P target_pc sf (ibsPost6 dst z4 z1 z5 z2 z6 z3 z7 ∗ F) post oom) :
    SepWP P target_pc s (ibsPre6 dst stOld ∗ F) post oom := by
  rcases hr5 with ⟨hx1, hx3, hx8, hx9, hx10, hx11, hx12, hx14, hx17, hx18⟩
  have_instrs hc 0 39
  dsimp only [ibsPre6]
  wp_str8 hf_0 m1 hm1; wp_step; wp_str8 hf_2 m2 hm2
  wp_step; wp_str8 hf_4 m3 hm3; wp_step
  wp_str8 hf_6 m4 hm4; wp_step; wp_str8 hf_8 m5 hm5
  wp_step; wp_str8 hf_10 m6 hm6; wp_step
  wp_str8 hf_12 m7 hm7; wp_step; wp_str8 hf_14 m8 hm8
  wp_step; wp_str8 hf_16 m9 hm9; wp_step
  wp_str8 hf_18 m10 hm10; wp_step; wp_str8 hf_20 m11 hm11
  wp_step; wp_str8 hf_22 m12 hm12; wp_step
  wp_str8 hf_24 m13 hm13; wp_step; wp_str8 hf_26 m14 hm14
  wp_step; wp_str8 hf_28 m15 hm15; wp_str8 hf_29 m16 hm16
  wp_str8 hf_30 m17 hm17; wp_str8 hf_31 m18 hm18; wp_str8 hf_32 m19 hm19
  wp_str8 hf_33 m20 hm20; wp_str8 hf_34 m21 hm21; wp_str8 hf_35 m22 hm22
  wp_str8 hf_36 m23 hm23; wp_str8 hf_37 m24 hm24; wp_step
  exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
       (by simp [wp_norm, arm64_norm, hm24, hm23, hm22, hm21, hm20, hm19, hm18, hm17, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1])⟩

/-- `subroutine_ok` contract for `fixslice64::inv_bitslice`. -/
theorem invBitslice_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry invBitsliceInstrs) :
    subroutine_ok P entry invBitsliceSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dst, src, st⟩ R s0 hpc hrun hpre _hsp
  dsimp only [invBitsliceSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  refine ⟨fsStateAt src st ∗ memRegion dst 64, hpre, ?_⟩
  rw [invBitsliceInstrs_chunks] at hc
  obtain ⟨hc1, hc⟩ := split_decodeWords hc; obtain ⟨hc2, hc⟩ := split_decodeWords hc
  obtain ⟨hc3, hc⟩ := split_decodeWords hc; obtain ⟨hc4, hc⟩ := split_decodeWords hc
  obtain ⟨hc5, hc6⟩ := split_decodeWords hc
  have hx0' : s0.readReg64 (.gpr 0#5) = dst := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = src := hx1
  refine ibs_chunk1 hc1 hpc hrun hx1' fun s1 hpc1 hrun1 hr1 hk1 => ?_
  refine ibs_chunk2 hc2 hpc1 hrun1 hr1 fun s2 hpc2 hrun2 hr2 hk2 => ?_
  rw [memRegion64_eq_exists_fsStateAt dst, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro stOld
  rw [fsStateAt_split_ibs dst stOld]
  have hrot3 : ∀ A B C D E : SepProp, A ∗ (B ∗ (C ∗ (D ∗ E))) = B ∗ (A ∗ C ∗ D ∗ E) :=
    fun _ _ _ _ _ => by sep_ac_rfl
  rw [hrot3]
  have hk12 := hk1.trans hk2
  refine ibs_chunk3 hc3 hpc2 hrun2 (hk12.x0.trans hx0') hr2 fun s3 hpc3 hrun3 hr3 hk3 => ?_
  have hrot4 : ∀ P3 A P4 P5 P6 : SepProp, P3 ∗ (A ∗ P4 ∗ P5 ∗ P6) = P4 ∗ (A ∗ P3 ∗ P5 ∗ P6) :=
    fun _ _ _ _ _ => by sep_ac_rfl
  rw [hrot4]
  have hk13 := hk12.trans hk3
  refine ibs_chunk4 hc4 hpc3 hrun3 (hk13.x0.trans hx0') hr3 fun s4 hpc4 hrun4 hr4 hk4 => ?_
  have hrot5 : ∀ P4 A P3 P5 P6 : SepProp, P4 ∗ (A ∗ P3 ∗ P5 ∗ P6) = P5 ∗ (A ∗ P3 ∗ P4 ∗ P6) :=
    fun _ _ _ _ _ => by sep_ac_rfl
  rw [hrot5]
  have hk14 := hk13.trans hk4
  refine ibs_chunk5 hc5 hpc4 hrun4 (hk14.x0.trans hx0') hr4 fun s5 hpc5 hrun5 hr5 hk5 => ?_
  have hrot6 : ∀ P5 A P3 P4 P6 : SepProp, P5 ∗ (A ∗ P3 ∗ P4 ∗ P6) = P6 ∗ (A ∗ P3 ∗ P4 ∗ P5) :=
    fun _ _ _ _ _ => by sep_ac_rfl
  rw [hrot6]
  have hk15 := hk14.trans hk5
  refine ibs_chunk6 hc6 hpc5 hrun5 (hk15.x0.trans hx0') hr5 fun sf hpc_f hrun_f hk6 => ?_
  have hk := hk15.trans hk6
  have hrotEnd : ∀ P6 A P3 P4 P5 : SepProp, P6 ∗ (A ∗ P3 ∗ P4 ∗ P5) = A ∗ (P3 ∗ (P4 ∗ (P5 ∗ P6))) :=
    fun _ _ _ _ _ => by sep_ac_rfl
  rw [hrotEnd, ibsPost_merge]
  change SepWP P (s0.readReg64 Reg.lr) sf
    (fsStateAt src st ∗ (dst ↦ₛ blocks4Bytes (Model.invBitslice st))) _ _
  refine SepWP.done (hpc_f.trans hk15.x30) hrun_f ⟨fun hm => ?_, hk.sp, hk.callee⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hk.purePres, hm⟩

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice

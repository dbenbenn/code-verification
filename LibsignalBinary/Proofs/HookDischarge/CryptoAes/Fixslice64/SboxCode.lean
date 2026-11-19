/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model
meta import ProofLib.StdStartup.StdDetect

/-!
# `fixslice64::sub_bytes` & `fixslice64::inv_sub_bytes` Binary Contracts (`Fixslice64.SboxCode`)

Placement-generic (`hasInstrs`) `subroutine_ok` contracts for `libaes` (`aes` 0.9.1 `fixslice64`):
- `subBytes_ok`: 132-instruction Boyar–Peralta–Calik S-box (`0x50` = `80` B stack frame);
- `invSubBytes_ok`: 145-instruction bitsliced inverse S-box (`0x60` = `96` B stack frame).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj fsStateAt)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. Machine-Code Templates & Decode Checks -/

private theorem map_decode_eq_of_all_isSome : ∀ ws : List (BitVec 32),
    ws.all (fun w => (Arm64.decode w).isSome) = true →
    ws.map Arm64.decode = (decodeWords ws).map some
  | [], _ => rfl
  | w :: ws, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      simp only [List.map_cons, decodeWords, decodeWord]
      cases hd : Arm64.decode w with
      | none => simp [hd] at h
      | some i => exact congrArg (some i :: ·) (map_decode_eq_of_all_isSome ws h.2)

/-- Exact 132 instruction words (`528` B) of `aes::soft::fixslice64::sub_bytes`. -/
@[expose] def subBytesWords : List (BitVec 32) :=
  [0xf81b0ffb#32, 0xa90167fa#32, 0xa9025ff8#32, 0xa90357f6#32, 0xa9044ff4#32, 0xa940ac06#32, 0xf9400c11#32, 0xa942340e#32, 0xf9400008#32, 0xa9430c10#32,
   0xca0b01c9#32, 0xca06006c#32, 0xca0d0205#32, 0xca0e006a#32, 0xca09018d#32, 0xca0b006f#32, 0xca0800a1#32, 0xca1101b2#32, 0xca0e002e#32, 0xca030039#32,
   0xca0b0251#32, 0xca100247#32, 0x8a0801d7#32, 0xca0a00eb#32, 0xca050222#32, 0x8a0d0233#32, 0xca0b0050#32, 0x8a0a0174#32, 0x8a0f0055#32, 0x8a090216#32,
   0xca1402b5#32, 0xca050165#32, 0xca1402d4#32, 0xca0f02f6#32, 0xca060037#32, 0x8a0102f8#32, 0x8a0c00a6#32, 0xca080232#32, 0xca1800b8#32, 0xca080164#32,
   0xca0202d6#32, 0xca0300c3#32, 0xca060318#32, 0xca0f02e6#32, 0xca1302d6#32, 0x8a19009a#32, 0xca1300e7#32, 0x8a060253#32, 0xca1a00ba#32, 0xca0c0318#32,
   0xca1300e7#32, 0xca030343#32, 0xca140313#32, 0xca1400e7#32, 0xca1502d4#32, 0xca150075#32, 0x8a070263#32, 0xca1302b8#32, 0xca1400e7#32, 0xca140076#32,
   0x8a1802d6#32, 0xca0302b8#32, 0xca0302c3#32, 0x8a07031a#32, 0x8a15007b#32, 0xca140354#32, 0xca1502d5#32, 0xca180363#32, 0xca130373#32, 0x8a0802a8#32,
   0x8a140078#32, 0x8a040284#32, 0x8a190283#32, 0xca070307#32, 0xca150278#32, 0x8a0d026d#32, 0xca1400f6#32, 0x8a060306#32, 0x8a0e02ae#32, 0x8a0502c5#32,
   0x8a0c02d6#32, 0x8a0100ec#32, 0xca1800e1#32, 0x8a1700e7#32, 0xca0c00b7#32, 0x8a0f002c#32, 0x8a11026f#32, 0x8a120311#32, 0xca150292#32, 0xca0801e8#32,
   0x8a020022#32, 0xca0f0231#32, 0xca120021#32, 0xca04010f#32, 0x8a100030#32, 0x8a090029#32, 0x8a0a024a#32, 0xca0501ef#32, 0xca080048#32, 0xca170210#32,
   0xca0a0129#32, 0xca0f00e1#32, 0xca160108#32, 0x8a0b024b#32, 0xca060132#32, 0xca010129#32, 0xca100108#32, 0xca0b020b#32, 0xca0e024e#32, 0xca0d024d#32,
   0xca160130#32, 0xca030112#32, 0xca080128#32, 0xca170231#32, 0xca1201ce#32, 0xa9002010#32, 0xca0a0188#32, 0xca0d0229#32, 0xca0b0108#32, 0xa9444ff4#32,
   0xca120108#32, 0xa94357f6#32, 0xa9425ff8#32, 0xca0f012a#32, 0xa94167fa#32, 0xa9022009#32, 0xca0b0129#32, 0xca0b01a8#32, 0xa901280e#32, 0xa9032009#32,
   0xf84507fb#32, 0xd65f03c0#32]

/-- Decoded instruction sequence of `sub_bytes`. -/
@[expose] def subBytesInstrs : List Instr := decodeWords subBytesWords

theorem subBytesInstrs_template_eq :
    subBytesWords.map Arm64.decode = subBytesInstrs.map some :=
  map_decode_eq_of_all_isSome _ (by decide)

/-- Exact 145 instruction words (`580` B) of `aes::soft::fixslice64::inv_sub_bytes`. -/
@[expose] def invSubBytesWords : List (BitVec 32) :=
  [0xf81a0ffe#32, 0xa9016ffc#32, 0xa90267fa#32, 0xa9035ff8#32, 0xa90457f6#32, 0xa9054ff4#32, 0xa941a414#32, 0xf9400807#32, 0xa9431410#32, 0xf9401404#32,
   0xa940040b#32, 0xca140123#32, 0xca09020e#32, 0xca1000aa#32, 0xca0900a8#32, 0xca0b0295#32, 0xca0b0032#32, 0xca0100f3#32, 0xca070087#32, 0xca15014c#32,
   0xca1201c6#32, 0xca010219#32, 0xca130061#32, 0xca0700a5#32, 0xca100109#32, 0xca0b006f#32, 0xca12014b#32, 0xca0701d0#32, 0xca010187#32, 0x8a0500dc#32,
   0xca14012d#32, 0x8a10017b#32, 0x8a0300fe#32, 0xca150387#32, 0xca140094#32, 0xca120071#32, 0xca150322#32, 0xca1b00f5#32, 0x8a0101bc#32, 0xca190287#32,
   0x8a080136#32, 0xca0400d2#32, 0xca1e0394#32, 0xca0c0279#32, 0x8a1100fc#32, 0x8a0f01d7#32, 0x8a02025a#32, 0xca160336#32, 0xaa1100f9#32, 0xca03039c#32,
   0x8a0a0198#32, 0xca1b02d6#32, 0xca170337#32, 0xca1a0399#32, 0xca1803d8#32, 0xca1402d6#32, 0xca1402f4#32, 0xca040324#32, 0xca1802b5#32, 0x8a1402d7#32,
   0xca180098#32, 0xca1502e4#32, 0xca1502db#32, 0xca180299#32, 0xca1802fa#32, 0x8a1402b4#32, 0x8a190084#32, 0xca18009c#32, 0x8a1b0344#32, 0xca15009a#32,
   0x8a060384#32, 0x8a1802c6#32, 0xca1c0356#32, 0x8a1b00c6#32, 0x8a120352#32, 0x8a0302d8#32, 0xca130183#32, 0xca1b02f3#32, 0xca060266#32, 0x8a340333#32,
   0xca040315#32, 0xca060358#32, 0xca170273#32, 0x8a020354#32, 0x8a070302#32, 0xca1300c7#32, 0x8a0302c3#32, 0xca0702d6#32, 0x8a110311#32, 0x8a0e00ce#32,
   0x8a0102c1#32, 0x8a0d02cd#32, 0xca130396#32, 0x8a0f00cf#32, 0xca0e0226#32, 0x8a1002d0#32, 0x8a050385#32, 0xca0300c6#32, 0xca0f0021#32, 0x8a0c00ec#32,
   0x8a0a00ea#32, 0xca120207#32, 0x8a0b02cb#32, 0x8a090269#32, 0x8a080268#32, 0xca060021#32, 0xca0201b7#32, 0xca0a00f8#32, 0xca0a016a#32, 0xca0901e9#32,
   0xca0800a8#32, 0xca140054#32, 0xca0c01ad#32, 0xca0102f7#32, 0xca0a02ab#32, 0xca07012f#32, 0xca030129#32, 0xca040103#32, 0xca0601a6#32, 0xca140129#32,
   0xa9005c0b#32, 0xca0801c8#32, 0xca03030b#32, 0xca03022e#32, 0xca050210#32, 0xca0f00cf#32, 0xca01016b#32, 0xca0c0108#32, 0xca0e012c#32, 0xca060210#32,
   0xa9012c0f#32, 0xca080128#32, 0xca0d0189#32, 0xca12004b#32, 0xca0a0108#32, 0xa9454ff4#32, 0xa9022410#32, 0xa94457f6#32, 0xca060169#32, 0xa9435ff8#32,
   0xa9032408#32, 0xa94267fa#32, 0xa9416ffc#32, 0xf84607fe#32, 0xd65f03c0#32]

/-- Decoded instruction sequence of `inv_sub_bytes`. -/
@[expose] def invSubBytesInstrs : List Instr := decodeWords invSubBytesWords

theorem invSubBytesInstrs_template_eq :
    invSubBytesWords.map Arm64.decode = invSubBytesInstrs.map some :=
  map_decode_eq_of_all_isSome _ (by decide)

/-! ## 2. Hoare Specifications (`subBytesSpec`, `invSubBytesSpec`) -/

/-- Hoare contract for `fixslice64::sub_bytes` (`80`-byte stack frame). -/
@[expose] def subBytesSpec : Spec (BitVec 64 × Model.FsState) where
  pre := fun (ptr, st) s0 => ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 80)
  post := fun (ptr, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (Model.subBytesFs st) ∗ stackFrameAt s0.sp 80)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Hoare contract for `fixslice64::inv_sub_bytes` (`96`-byte stack frame). -/
@[expose] def invSubBytesSpec : Spec (BitVec 64 × Model.FsState) where
  pre := fun (ptr, st) s0 => ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 96)
  post := fun (ptr, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (Model.invSubBytesFs st) ∗ stackFrameAt s0.sp 96)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 3. Staged Assembly-Schedule Circuits & Bit-Slice Equivalence to `Model` -/

private def strictBool {α : Type} (v : Bool) (k : Bool → α) : α :=
  match v with | true => k true | false => k false

private theorem strictBool_eq {α : Type} (v : Bool) (k : Bool → α) :
    strictBool v k = k v := by cases v <;> rfl

@[ext] private structure FsBool8 where
  (b0 b1 b2 b3 b4 b5 b6 b7 : Bool)
  deriving DecidableEq

private def extractBool8 (st : Model.FsState) (k : Nat) : FsBool8 :=
  ⟨st.s0.getLsbD k, st.s1.getLsbD k, st.s2.getLsbD k, st.s3.getLsbD k,
   st.s4.getLsbD k, st.s5.getLsbD k, st.s6.getLsbD k, st.s7.getLsbD k⟩

private theorem eq_of_extractBool8_eq {a b : Model.FsState}
    (h : ∀ k : Nat, k < 64 → extractBool8 a k = extractBool8 b k) : a = b := by
  ext1 <;> apply BitVec.eq_of_getLsbD_eq <;> intro k hk
  · exact congrArg FsBool8.b0 (h k hk)
  · exact congrArg FsBool8.b1 (h k hk)
  · exact congrArg FsBool8.b2 (h k hk)
  · exact congrArg FsBool8.b3 (h k hk)
  · exact congrArg FsBool8.b4 (h k hk)
  · exact congrArg FsBool8.b5 (h k hk)
  · exact congrArg FsBool8.b6 (h k hk)
  · exact congrArg FsBool8.b7 (h k hk)

private structure SubAsmW1 where (x1 x2 x3 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x25 : BitVec 64)
@[ext] private structure SubAsmBoolB1 where (x1 x2 x3 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x25 : Bool)
private def extractSubAsmW1 (w : SubAsmW1) (k : Nat) : SubAsmBoolB1 := ⟨w.x1.getLsbD k, w.x2.getLsbD k, w.x3.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x7.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k, w.x11.getLsbD k,
    w.x12.getLsbD k, w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x17.getLsbD k, w.x19.getLsbD k, w.x20.getLsbD k, w.x21.getLsbD k, w.x23.getLsbD k,
    w.x25.getLsbD k⟩
private def SubAsmRegs1 (s : State) (w : SubAsmW1) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 2#5) = w.x2 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧ s.readReg64 (.gpr 6#5) = w.x6 ∧
  s.readReg64 (.gpr 7#5) = w.x7 ∧ s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧ s.readReg64 (.gpr 11#5) = w.x11 ∧
  s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 13#5) = w.x13 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧ s.readReg64 (.gpr 16#5) = w.x16 ∧
  s.readReg64 (.gpr 17#5) = w.x17 ∧ s.readReg64 (.gpr 19#5) = w.x19 ∧ s.readReg64 (.gpr 20#5) = w.x20 ∧ s.readReg64 (.gpr 21#5) = w.x21 ∧ s.readReg64 (.gpr 23#5) = w.x23 ∧
  s.readReg64 (.gpr 25#5) = w.x25
private structure SubAsmW2 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : BitVec 64)
@[ext] private structure SubAsmBoolB2 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : Bool)
private def extractSubAsmW2 (w : SubAsmW2) (k : Nat) : SubAsmBoolB2 := ⟨w.x1.getLsbD k, w.x2.getLsbD k, w.x3.getLsbD k, w.x4.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x7.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k,
    w.x11.getLsbD k, w.x12.getLsbD k, w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x17.getLsbD k, w.x18.getLsbD k, w.x19.getLsbD k, w.x20.getLsbD k,
    w.x21.getLsbD k, w.x22.getLsbD k, w.x23.getLsbD k, w.x24.getLsbD k, w.x25.getLsbD k⟩
private def SubAsmRegs2 (s : State) (w : SubAsmW2) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 2#5) = w.x2 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 4#5) = w.x4 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧
  s.readReg64 (.gpr 6#5) = w.x6 ∧ s.readReg64 (.gpr 7#5) = w.x7 ∧ s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧
  s.readReg64 (.gpr 11#5) = w.x11 ∧ s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 13#5) = w.x13 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧
  s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 17#5) = w.x17 ∧ s.readReg64 (.gpr 18#5) = w.x18 ∧ s.readReg64 (.gpr 19#5) = w.x19 ∧ s.readReg64 (.gpr 20#5) = w.x20 ∧
  s.readReg64 (.gpr 21#5) = w.x21 ∧ s.readReg64 (.gpr 22#5) = w.x22 ∧ s.readReg64 (.gpr 23#5) = w.x23 ∧ s.readReg64 (.gpr 24#5) = w.x24 ∧ s.readReg64 (.gpr 25#5) = w.x25
private structure SubAsmW3 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x22 x23 x24 : BitVec 64)
@[ext] private structure SubAsmBoolB3 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x22 x23 x24 : Bool)
private def extractSubAsmW3 (w : SubAsmW3) (k : Nat) : SubAsmBoolB3 := ⟨w.x1.getLsbD k, w.x2.getLsbD k, w.x3.getLsbD k, w.x4.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x7.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k,
    w.x11.getLsbD k, w.x12.getLsbD k, w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x18.getLsbD k, w.x20.getLsbD k, w.x21.getLsbD k, w.x22.getLsbD k,
    w.x23.getLsbD k, w.x24.getLsbD k⟩
private def SubAsmRegs3 (s : State) (w : SubAsmW3) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 2#5) = w.x2 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 4#5) = w.x4 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧
  s.readReg64 (.gpr 6#5) = w.x6 ∧ s.readReg64 (.gpr 7#5) = w.x7 ∧ s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧
  s.readReg64 (.gpr 11#5) = w.x11 ∧ s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 13#5) = w.x13 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧
  s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 18#5) = w.x18 ∧ s.readReg64 (.gpr 20#5) = w.x20 ∧ s.readReg64 (.gpr 21#5) = w.x21 ∧ s.readReg64 (.gpr 22#5) = w.x22 ∧
  s.readReg64 (.gpr 23#5) = w.x23 ∧ s.readReg64 (.gpr 24#5) = w.x24
private structure SubAsmW4 where (x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 : BitVec 64)
@[ext] private structure SubAsmBoolB4 where (x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 : Bool)
private def extractSubAsmW4 (w : SubAsmW4) (k : Nat) : SubAsmBoolB4 := ⟨w.x8.getLsbD k, w.x10.getLsbD k, w.x11.getLsbD k, w.x12.getLsbD k, w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x17.getLsbD k, w.x18.getLsbD k⟩
private def SubAsmRegs4 (s : State) (w : SubAsmW4) : Prop :=
  s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧ s.readReg64 (.gpr 11#5) = w.x11 ∧ s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 13#5) = w.x13 ∧
  s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧ s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 17#5) = w.x17 ∧ s.readReg64 (.gpr 18#5) = w.x18
private def SubAsmStage1 (inp : Model.FsState) : SubAsmW1 :=
  let x6 := inp.s1; let x11 := inp.s2; let x17 := inp.s3; let x14 := inp.s4; let x13 := inp.s5; let x8 := inp.s0; let x16 := inp.s6; let x3 := inp.s7; let x9 := x14 ^^^ x11
  let x12 := x3 ^^^ x6; let x5 := x16 ^^^ x13; let x10 := x3 ^^^ x14; let x13 := x12 ^^^ x9; let x15 := x3 ^^^ x11; let x1 := x5 ^^^ x8; let x18 := x13 ^^^ x17; let x14 := x1 ^^^ x14; let x25 := x1 ^^^ x3
  let x17 := x18 ^^^ x11; let x7 := x18 ^^^ x16; let x23 := x14 &&& x8; let x11 := x7 ^^^ x10; let x2 := x17 ^^^ x5; let x19 := x17 &&& x13; let x16 := x2 ^^^ x11; let x20 := x11 &&& x10; let x21 := x2 &&& x15
  let x22 := x16 &&& x9; let x21 := x21 ^^^ x20; let x5 := x11 ^^^ x5; let x20 := x22 ^^^ x20
  ⟨x1, x2, x3, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x19, x20, x21, x23, x25⟩
private def SubAsmBoolStage1 (inp : FsBool8) : SubAsmBoolB1 :=
  strictBool inp.b1 fun x6 => strictBool inp.b2 fun x11 => strictBool inp.b3 fun x17 => strictBool inp.b4 fun x14 => strictBool inp.b5 fun x13 => strictBool inp.b0 fun x8 => strictBool inp.b6 fun x16 =>
  strictBool inp.b7 fun x3 => strictBool (x14 ^^ x11) fun x9 => strictBool (x3 ^^ x6) fun x12 => strictBool (x16 ^^ x13) fun x5 => strictBool (x3 ^^ x14) fun x10 => strictBool (x12 ^^ x9) fun x13 => strictBool (x3 ^^ x11) fun x15 =>
  strictBool (x5 ^^ x8) fun x1 => strictBool (x13 ^^ x17) fun x18 => strictBool (x1 ^^ x14) fun x14 => strictBool (x1 ^^ x3) fun x25 => strictBool (x18 ^^ x11) fun x17 => strictBool (x18 ^^ x16) fun x7 => strictBool (x14 && x8) fun x23 =>
  strictBool (x7 ^^ x10) fun x11 => strictBool (x17 ^^ x5) fun x2 => strictBool (x17 && x13) fun x19 => strictBool (x2 ^^ x11) fun x16 => strictBool (x11 && x10) fun x20 => strictBool (x2 && x15) fun x21 => strictBool (x16 && x9) fun x22 =>
  strictBool (x21 ^^ x20) fun x21 => strictBool (x11 ^^ x5) fun x5 => strictBool (x22 ^^ x20) fun x20 =>
  ⟨x1, x2, x3, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x19, x20, x21, x23, x25⟩
private theorem extract_SubAsmStage1 (inp : Model.FsState) (k : Nat) : extractSubAsmW1 (SubAsmStage1 inp) k = SubAsmBoolStage1 (extractBool8 inp k) := by
  ext1 <;> simp only [extractSubAsmW1, extractBool8, SubAsmStage1, SubAsmBoolStage1, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubAsmStage2 (inp : SubAsmW1) : SubAsmW2 :=
  let x1 := inp.x1; let x2 := inp.x2; let x3 := inp.x3; let x5 := inp.x5; let x6 := inp.x6; let x7 := inp.x7; let x8 := inp.x8; let x9 := inp.x9; let x10 := inp.x10
  let x11 := inp.x11; let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x17 := inp.x17; let x19 := inp.x19; let x20 := inp.x20
  let x21 := inp.x21; let x23 := inp.x23; let x25 := inp.x25; let x22 := x23 ^^^ x15; let x23 := x1 ^^^ x6; let x24 := x23 &&& x1; let x6 := x5 &&& x12; let x18 := x17 ^^^ x8; let x24 := x5 ^^^ x24
  let x4 := x11 ^^^ x8; let x22 := x22 ^^^ x2; let x3 := x6 ^^^ x3; let x24 := x24 ^^^ x6; let x6 := x23 ^^^ x15; let x22 := x22 ^^^ x19; let x26 := x4 &&& x25; let x7 := x7 ^^^ x19; let x19 := x18 &&& x6
  let x26 := x5 ^^^ x26; let x24 := x24 ^^^ x12; let x7 := x7 ^^^ x19; let x3 := x26 ^^^ x3; let x19 := x24 ^^^ x20; let x7 := x7 ^^^ x20; let x20 := x22 ^^^ x21; let x21 := x3 ^^^ x21; let x3 := x19 &&& x7
  let x24 := x21 ^^^ x19; let x7 := x7 ^^^ x20; let x22 := x3 ^^^ x20
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25⟩
private def SubAsmBoolStage2 (inp : SubAsmBoolB1) : SubAsmBoolB2 :=
  strictBool inp.x1 fun x1 => strictBool inp.x2 fun x2 => strictBool inp.x3 fun x3 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x7 fun x7 => strictBool inp.x8 fun x8 =>
  strictBool inp.x9 fun x9 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 => strictBool inp.x15 fun x15 =>
  strictBool inp.x16 fun x16 => strictBool inp.x17 fun x17 => strictBool inp.x19 fun x19 => strictBool inp.x20 fun x20 => strictBool inp.x21 fun x21 => strictBool inp.x23 fun x23 => strictBool inp.x25 fun x25 =>
  strictBool (x23 ^^ x15) fun x22 => strictBool (x1 ^^ x6) fun x23 => strictBool (x23 && x1) fun x24 => strictBool (x5 && x12) fun x6 => strictBool (x17 ^^ x8) fun x18 => strictBool (x5 ^^ x24) fun x24 => strictBool (x11 ^^ x8) fun x4 =>
  strictBool (x22 ^^ x2) fun x22 => strictBool (x6 ^^ x3) fun x3 => strictBool (x24 ^^ x6) fun x24 => strictBool (x23 ^^ x15) fun x6 => strictBool (x22 ^^ x19) fun x22 => strictBool (x4 && x25) fun x26 => strictBool (x7 ^^ x19) fun x7 =>
  strictBool (x18 && x6) fun x19 => strictBool (x5 ^^ x26) fun x26 => strictBool (x24 ^^ x12) fun x24 => strictBool (x7 ^^ x19) fun x7 => strictBool (x26 ^^ x3) fun x3 => strictBool (x24 ^^ x20) fun x19 => strictBool (x7 ^^ x20) fun x7 =>
  strictBool (x22 ^^ x21) fun x20 => strictBool (x3 ^^ x21) fun x21 => strictBool (x19 && x7) fun x3 => strictBool (x21 ^^ x19) fun x24 => strictBool (x7 ^^ x20) fun x7 => strictBool (x3 ^^ x20) fun x22 =>
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25⟩
private theorem extract_SubAsmStage2 (inp : SubAsmW1) (k : Nat) : extractSubAsmW2 (SubAsmStage2 inp) k = SubAsmBoolStage2 (extractSubAsmW1 inp k) := by
  ext1 <;> simp only [extractSubAsmW2, extractSubAsmW1, SubAsmStage2, SubAsmBoolStage2, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubAsmStage3 (inp : SubAsmW2) : SubAsmW3 :=
  let x1 := inp.x1; let x2 := inp.x2; let x3 := inp.x3; let x4 := inp.x4; let x5 := inp.x5; let x6 := inp.x6; let x7 := inp.x7; let x8 := inp.x8; let x9 := inp.x9
  let x10 := inp.x10; let x11 := inp.x11; let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x17 := inp.x17; let x18 := inp.x18
  let x19 := inp.x19; let x20 := inp.x20; let x21 := inp.x21; let x22 := inp.x22; let x23 := inp.x23; let x24 := inp.x24; let x25 := inp.x25; let x22 := x22 &&& x24; let x24 := x21 ^^^ x3
  let x3 := x22 ^^^ x3; let x26 := x24 &&& x7; let x27 := x3 &&& x21; let x20 := x26 ^^^ x20; let x21 := x22 ^^^ x21; let x3 := x27 ^^^ x24; let x19 := x27 ^^^ x19; let x8 := x21 &&& x8; let x24 := x3 &&& x20
  let x4 := x20 &&& x4; let x3 := x20 &&& x25; let x7 := x24 ^^^ x7; let x24 := x19 ^^^ x21; let x13 := x19 &&& x13; let x22 := x7 ^^^ x20; let x6 := x24 &&& x6; let x14 := x21 &&& x14; let x5 := x22 &&& x5
  let x22 := x22 &&& x12; let x12 := x7 &&& x1; let x1 := x7 ^^^ x24; let x7 := x7 &&& x23; let x23 := x5 ^^^ x12; let x12 := x1 &&& x15; let x15 := x19 &&& x17
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x18, x20, x21, x22, x23, x24⟩
private def SubAsmBoolStage3 (inp : SubAsmBoolB2) : SubAsmBoolB3 :=
  strictBool inp.x1 fun x1 => strictBool inp.x2 fun x2 => strictBool inp.x3 fun x3 => strictBool inp.x4 fun x4 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x7 fun x7 =>
  strictBool inp.x8 fun x8 => strictBool inp.x9 fun x9 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 =>
  strictBool inp.x15 fun x15 => strictBool inp.x16 fun x16 => strictBool inp.x17 fun x17 => strictBool inp.x18 fun x18 => strictBool inp.x19 fun x19 => strictBool inp.x20 fun x20 => strictBool inp.x21 fun x21 =>
  strictBool inp.x22 fun x22 => strictBool inp.x23 fun x23 => strictBool inp.x24 fun x24 => strictBool inp.x25 fun x25 => strictBool (x22 && x24) fun x22 => strictBool (x21 ^^ x3) fun x24 => strictBool (x22 ^^ x3) fun x3 =>
  strictBool (x24 && x7) fun x26 => strictBool (x3 && x21) fun x27 => strictBool (x26 ^^ x20) fun x20 => strictBool (x22 ^^ x21) fun x21 => strictBool (x27 ^^ x24) fun x3 => strictBool (x27 ^^ x19) fun x19 => strictBool (x21 && x8) fun x8 =>
  strictBool (x3 && x20) fun x24 => strictBool (x20 && x4) fun x4 => strictBool (x20 && x25) fun x3 => strictBool (x24 ^^ x7) fun x7 => strictBool (x19 ^^ x21) fun x24 => strictBool (x19 && x13) fun x13 => strictBool (x7 ^^ x20) fun x22 =>
  strictBool (x24 && x6) fun x6 => strictBool (x21 && x14) fun x14 => strictBool (x22 && x5) fun x5 => strictBool (x22 && x12) fun x22 => strictBool (x7 && x1) fun x12 => strictBool (x7 ^^ x24) fun x1 => strictBool (x7 && x23) fun x7 =>
  strictBool (x5 ^^ x12) fun x23 => strictBool (x1 && x15) fun x12 => strictBool (x19 && x17) fun x15 =>
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x18, x20, x21, x22, x23, x24⟩
private theorem extract_SubAsmStage3 (inp : SubAsmW2) (k : Nat) : extractSubAsmW3 (SubAsmStage3 inp) k = SubAsmBoolStage3 (extractSubAsmW2 inp k) := by
  ext1 <;> simp only [extractSubAsmW3, extractSubAsmW2, SubAsmStage3, SubAsmBoolStage3, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubAsmStage4 (inp : SubAsmW3) : SubAsmW4 :=
  let x1 := inp.x1; let x2 := inp.x2; let x3 := inp.x3; let x4 := inp.x4; let x5 := inp.x5; let x6 := inp.x6; let x7 := inp.x7; let x8 := inp.x8; let x9 := inp.x9
  let x10 := inp.x10; let x11 := inp.x11; let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x18 := inp.x18; let x20 := inp.x20
  let x21 := inp.x21; let x22 := inp.x22; let x23 := inp.x23; let x24 := inp.x24; let x17 := x24 &&& x18; let x18 := x20 ^^^ x21; let x8 := x15 ^^^ x8; let x2 := x1 &&& x2; let x17 := x17 ^^^ x15
  let x1 := x1 ^^^ x18; let x15 := x8 ^^^ x4; let x16 := x1 &&& x16; let x9 := x1 &&& x9; let x10 := x18 &&& x10; let x15 := x15 ^^^ x5; let x8 := x2 ^^^ x8; let x16 := x16 ^^^ x23; let x9 := x9 ^^^ x10
  let x1 := x7 ^^^ x15; let x8 := x8 ^^^ x22; let x11 := x18 &&& x11; let x18 := x9 ^^^ x6; let x9 := x9 ^^^ x1; let x8 := x8 ^^^ x16; let x11 := x16 ^^^ x11; let x14 := x18 ^^^ x14; let x13 := x18 ^^^ x13
  let x16 := x9 ^^^ x22; let x18 := x8 ^^^ x3; let x8 := x9 ^^^ x8; let x17 := x17 ^^^ x23; let x14 := x14 ^^^ x18
  ⟨x8, x10, x11, x12, x13, x14, x15, x16, x17, x18⟩
private def SubAsmBoolStage4 (inp : SubAsmBoolB3) : SubAsmBoolB4 :=
  strictBool inp.x1 fun x1 => strictBool inp.x2 fun x2 => strictBool inp.x3 fun x3 => strictBool inp.x4 fun x4 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x7 fun x7 =>
  strictBool inp.x8 fun x8 => strictBool inp.x9 fun x9 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 =>
  strictBool inp.x15 fun x15 => strictBool inp.x16 fun x16 => strictBool inp.x18 fun x18 => strictBool inp.x20 fun x20 => strictBool inp.x21 fun x21 => strictBool inp.x22 fun x22 => strictBool inp.x23 fun x23 =>
  strictBool inp.x24 fun x24 => strictBool (x24 && x18) fun x17 => strictBool (x20 ^^ x21) fun x18 => strictBool (x15 ^^ x8) fun x8 => strictBool (x1 && x2) fun x2 => strictBool (x17 ^^ x15) fun x17 => strictBool (x1 ^^ x18) fun x1 =>
  strictBool (x8 ^^ x4) fun x15 => strictBool (x1 && x16) fun x16 => strictBool (x1 && x9) fun x9 => strictBool (x18 && x10) fun x10 => strictBool (x15 ^^ x5) fun x15 => strictBool (x2 ^^ x8) fun x8 => strictBool (x16 ^^ x23) fun x16 =>
  strictBool (x9 ^^ x10) fun x9 => strictBool (x7 ^^ x15) fun x1 => strictBool (x8 ^^ x22) fun x8 => strictBool (x18 && x11) fun x11 => strictBool (x9 ^^ x6) fun x18 => strictBool (x9 ^^ x1) fun x9 => strictBool (x8 ^^ x16) fun x8 =>
  strictBool (x16 ^^ x11) fun x11 => strictBool (x18 ^^ x14) fun x14 => strictBool (x18 ^^ x13) fun x13 => strictBool (x9 ^^ x22) fun x16 => strictBool (x8 ^^ x3) fun x18 => strictBool (x9 ^^ x8) fun x8 => strictBool (x17 ^^ x23) fun x17 =>
  strictBool (x14 ^^ x18) fun x14 =>
  ⟨x8, x10, x11, x12, x13, x14, x15, x16, x17, x18⟩
private theorem extract_SubAsmStage4 (inp : SubAsmW3) (k : Nat) : extractSubAsmW4 (SubAsmStage4 inp) k = SubAsmBoolStage4 (extractSubAsmW3 inp k) := by
  ext1 <;> simp only [extractSubAsmW4, extractSubAsmW3, SubAsmStage4, SubAsmBoolStage4, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubAsmStage5 (inp : SubAsmW4) : Model.FsState :=
  let x8 := inp.x8; let x10 := inp.x10; let x11 := inp.x11; let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x17 := inp.x17
  let x18 := inp.x18; let out0 := x16; let out1 := x8; let x8 := x12 ^^^ x10; let x9 := x17 ^^^ x13; let x8 := x8 ^^^ x11; let x8 := x8 ^^^ x18; let x10 := x9 ^^^ x15; let out4 := x9
  let out5 := x8; let x9 := x9 ^^^ x11; let x8 := x13 ^^^ x11; let out2 := x14; let out3 := x10; let out6 := x9; let out7 := x8
  ⟨out0, out1, out2, out3, out4, out5, out6, out7⟩
private def SubAsmBoolStage5 (inp : SubAsmBoolB4) : FsBool8 :=
  strictBool inp.x8 fun x8 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 => strictBool inp.x15 fun x15 =>
  strictBool inp.x16 fun x16 => strictBool inp.x17 fun x17 => strictBool inp.x18 fun x18 => strictBool x16 fun out0 => strictBool x8 fun out1 => strictBool (x12 ^^ x10) fun x8 => strictBool (x17 ^^ x13) fun x9 =>
  strictBool (x8 ^^ x11) fun x8 => strictBool (x8 ^^ x18) fun x8 => strictBool (x9 ^^ x15) fun x10 => strictBool x9 fun out4 => strictBool x8 fun out5 => strictBool (x9 ^^ x11) fun x9 => strictBool (x13 ^^ x11) fun x8 =>
  strictBool x14 fun out2 => strictBool x10 fun out3 => strictBool x9 fun out6 => strictBool x8 fun out7 =>
  ⟨out0, out1, out2, out3, out4, out5, out6, out7⟩
private theorem extract_SubAsmStage5 (inp : SubAsmW4) (k : Nat) : extractBool8 (SubAsmStage5 inp) k = SubAsmBoolStage5 (extractSubAsmW4 inp k) := by
  ext1 <;> simp only [extractBool8, extractSubAsmW4, SubAsmStage5, SubAsmBoolStage5, strictBool_eq, BitVec.getLsbD_xor]
private def SubAsmFull (st : Model.FsState) : Model.FsState := SubAsmStage5 (SubAsmStage4 (SubAsmStage3 (SubAsmStage2 (SubAsmStage1 (st)))))
private def SubAsmBoolFull (x : FsBool8) : FsBool8 := SubAsmBoolStage5 (SubAsmBoolStage4 (SubAsmBoolStage3 (SubAsmBoolStage2 (SubAsmBoolStage1 (x)))))

@[ext] private structure SubModBoolB1 where (t0 t14 t16 t2 t7 u0 u3 u6 u7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y6 y7 y8 y9 : Bool)
private def extractSubModBoolW1 (w : Model.SubBytesW1) (k : Nat) : SubModBoolB1 := ⟨w.t0.getLsbD k, w.t14.getLsbD k, w.t16.getLsbD k, w.t2.getLsbD k, w.t7.getLsbD k, w.u0.getLsbD k, w.u3.getLsbD k, w.u6.getLsbD k, w.u7.getLsbD k, w.y10.getLsbD k,
    w.y11.getLsbD k, w.y12.getLsbD k, w.y13.getLsbD k, w.y14.getLsbD k, w.y15.getLsbD k, w.y16.getLsbD k, w.y17.getLsbD k, w.y18.getLsbD k, w.y19.getLsbD k, w.y20.getLsbD k,
    w.y21.getLsbD k, w.y6.getLsbD k, w.y7.getLsbD k, w.y8.getLsbD k, w.y9.getLsbD k⟩
@[ext] private structure SubModBoolB2 where (t22 t23 t24 t25 t27 t31 u7 y1 y10 y11 y12 y13 y14 y15 y16 y17 y2 y3 y4 y5 y6 y7 y8 y9 : Bool)
private def extractSubModBoolW2 (w : Model.SubBytesW2) (k : Nat) : SubModBoolB2 := ⟨w.t22.getLsbD k, w.t23.getLsbD k, w.t24.getLsbD k, w.t25.getLsbD k, w.t27.getLsbD k, w.t31.getLsbD k, w.u7.getLsbD k, w.y1.getLsbD k, w.y10.getLsbD k, w.y11.getLsbD k,
    w.y12.getLsbD k, w.y13.getLsbD k, w.y14.getLsbD k, w.y15.getLsbD k, w.y16.getLsbD k, w.y17.getLsbD k, w.y2.getLsbD k, w.y3.getLsbD k, w.y4.getLsbD k, w.y5.getLsbD k,
    w.y6.getLsbD k, w.y7.getLsbD k, w.y8.getLsbD k, w.y9.getLsbD k⟩
@[ext] private structure SubModBoolB3 where (t29 t33 t37 t41 t44 tc12 tc6 u7 y11 y12 y14 y15 y17 y3 y4 y6 y9 z12 z13 z14 z17 z8 : Bool)
private def extractSubModBoolW3 (w : Model.SubBytesW3) (k : Nat) : SubModBoolB3 := ⟨w.t29.getLsbD k, w.t33.getLsbD k, w.t37.getLsbD k, w.t41.getLsbD k, w.t44.getLsbD k, w.tc12.getLsbD k, w.tc6.getLsbD k, w.u7.getLsbD k, w.y11.getLsbD k, w.y12.getLsbD k,
    w.y14.getLsbD k, w.y15.getLsbD k, w.y17.getLsbD k, w.y3.getLsbD k, w.y4.getLsbD k, w.y6.getLsbD k, w.y9.getLsbD k, w.z12.getLsbD k, w.z13.getLsbD k, w.z14.getLsbD k,
    w.z17.getLsbD k, w.z8.getLsbD k⟩
@[ext] private structure SubModBoolB4 where (s0 s1 s3 tc12 tc13 tc20 tc21 tc8 z0 z12 z14 z17 z2 z8 : Bool)
private def extractSubModBoolW4 (w : Model.SubBytesW4) (k : Nat) : SubModBoolB4 := ⟨w.s0.getLsbD k, w.s1.getLsbD k, w.s3.getLsbD k, w.tc12.getLsbD k, w.tc13.getLsbD k, w.tc20.getLsbD k, w.tc21.getLsbD k, w.tc8.getLsbD k, w.z0.getLsbD k, w.z12.getLsbD k,
    w.z14.getLsbD k, w.z17.getLsbD k, w.z2.getLsbD k, w.z8.getLsbD k⟩
private def SubModBoolStage1 (inp : FsBool8) : SubModBoolB1 :=
  strictBool inp.b0 fun u7 => strictBool inp.b1 fun u6 => strictBool inp.b2 fun u5 => strictBool inp.b3 fun u4 => strictBool inp.b4 fun u3 => strictBool inp.b5 fun u2 => strictBool inp.b6 fun u1 =>
  strictBool inp.b7 fun u0 => strictBool (u3 ^^ u5) fun y14 => strictBool (u0 ^^ u6) fun y13 => strictBool (y13 ^^ y14) fun y12 => strictBool (u4 ^^ y12) fun t1 => strictBool (t1 ^^ u5) fun y15 => strictBool (y12 && y15) fun t2 =>
  strictBool (y15 ^^ u7) fun y6 => strictBool (t1 ^^ u1) fun y20 => strictBool (u0 ^^ u3) fun y9 => strictBool (y20 ^^ y9) fun y11 => strictBool (y9 && y11) fun t12 => strictBool (u7 ^^ y11) fun y7 => strictBool (u0 ^^ u5) fun y8 =>
  strictBool (u1 ^^ u2) fun t0 => strictBool (y15 ^^ t0) fun y10 => strictBool (y10 ^^ y11) fun y17 => strictBool (y14 && y17) fun t13 => strictBool (t13 ^^ t12) fun t14 => strictBool (y10 ^^ y8) fun y19 => strictBool (y8 && y10) fun t15 =>
  strictBool (t15 ^^ t12) fun t16 => strictBool (t0 ^^ y11) fun y16 => strictBool (y13 ^^ y16) fun y21 => strictBool (y13 && y16) fun t7 => strictBool (u0 ^^ y16) fun y18 =>
  ⟨t0, t14, t16, t2, t7, u0, u3, u6, u7, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y6, y7, y8, y9⟩
private theorem extract_SubModBoolStage1 (inp : Model.FsState) (k : Nat) : extractSubModBoolW1 (Model.subBytesFsStage1 inp) k = SubModBoolStage1 (extractBool8 inp k) := by
  ext1 <;> simp only [extractSubModBoolW1, extractBool8, Model.subBytesFsStage1, SubModBoolStage1, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubModBoolStage2 (inp : SubModBoolB1) : SubModBoolB2 :=
  strictBool inp.t0 fun t0 => strictBool inp.t14 fun t14 => strictBool inp.t16 fun t16 => strictBool inp.t2 fun t2 => strictBool inp.t7 fun t7 => strictBool inp.u0 fun u0 => strictBool inp.u3 fun u3 =>
  strictBool inp.u6 fun u6 => strictBool inp.u7 fun u7 => strictBool inp.y10 fun y10 => strictBool inp.y11 fun y11 => strictBool inp.y12 fun y12 => strictBool inp.y13 fun y13 => strictBool inp.y14 fun y14 =>
  strictBool inp.y15 fun y15 => strictBool inp.y16 fun y16 => strictBool inp.y17 fun y17 => strictBool inp.y18 fun y18 => strictBool inp.y19 fun y19 => strictBool inp.y20 fun y20 => strictBool inp.y21 fun y21 =>
  strictBool inp.y6 fun y6 => strictBool inp.y7 fun y7 => strictBool inp.y8 fun y8 => strictBool inp.y9 fun y9 => strictBool (t0 ^^ u7) fun y1 => strictBool (y1 ^^ u3) fun y4 => strictBool (y4 && u7) fun t5 =>
  strictBool (t5 ^^ t2) fun t6 => strictBool (t6 ^^ t16) fun t18 => strictBool (t18 ^^ y19) fun t22 => strictBool (y1 ^^ u0) fun y2 => strictBool (y2 && y7) fun t10 => strictBool (t10 ^^ t7) fun t11 => strictBool (t11 ^^ t16) fun t20 =>
  strictBool (t20 ^^ y18) fun t24 => strictBool (y1 ^^ u6) fun y5 => strictBool (y5 && y1) fun t8 => strictBool (t8 ^^ t7) fun t9 => strictBool (t9 ^^ t14) fun t19 => strictBool (t19 ^^ y21) fun t23 => strictBool (y5 ^^ y8) fun y3 =>
  strictBool (y3 && y6) fun t3 => strictBool (t3 ^^ t2) fun t4 => strictBool (t4 ^^ y20) fun t17 => strictBool (t17 ^^ t14) fun t21 => strictBool (t21 && t23) fun t26 => strictBool (t24 ^^ t26) fun t27 => strictBool (t22 ^^ t26) fun t31 =>
  strictBool (t21 ^^ t22) fun t25 =>
  ⟨t22, t23, t24, t25, t27, t31, u7, y1, y10, y11, y12, y13, y14, y15, y16, y17, y2, y3, y4, y5, y6, y7, y8, y9⟩
private theorem extract_SubModBoolStage2 (inp : Model.SubBytesW1) (k : Nat) : extractSubModBoolW2 (Model.subBytesFsStage2 inp) k = SubModBoolStage2 (extractSubModBoolW1 inp k) := by
  ext1 <;> simp only [extractSubModBoolW2, extractSubModBoolW1, Model.subBytesFsStage2, SubModBoolStage2, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubModBoolStage3 (inp : SubModBoolB2) : SubModBoolB3 :=
  strictBool inp.t22 fun t22 => strictBool inp.t23 fun t23 => strictBool inp.t24 fun t24 => strictBool inp.t25 fun t25 => strictBool inp.t27 fun t27 => strictBool inp.t31 fun t31 => strictBool inp.u7 fun u7 =>
  strictBool inp.y1 fun y1 => strictBool inp.y10 fun y10 => strictBool inp.y11 fun y11 => strictBool inp.y12 fun y12 => strictBool inp.y13 fun y13 => strictBool inp.y14 fun y14 => strictBool inp.y15 fun y15 =>
  strictBool inp.y16 fun y16 => strictBool inp.y17 fun y17 => strictBool inp.y2 fun y2 => strictBool inp.y3 fun y3 => strictBool inp.y4 fun y4 => strictBool inp.y5 fun y5 => strictBool inp.y6 fun y6 =>
  strictBool inp.y7 fun y7 => strictBool inp.y8 fun y8 => strictBool inp.y9 fun y9 => strictBool (t25 && t27) fun t28 => strictBool (t28 ^^ t22) fun t29 => strictBool (t29 && y2) fun z14 => strictBool (t29 && y7) fun z5 =>
  strictBool (t23 ^^ t24) fun t30 => strictBool (t31 && t30) fun t32 => strictBool (t32 ^^ t24) fun t33 => strictBool (t27 ^^ t33) fun t35 => strictBool (t24 && t35) fun t36 => strictBool (t27 ^^ t36) fun t38 => strictBool (t29 && t38) fun t39 =>
  strictBool (t25 ^^ t39) fun t40 => strictBool (t29 ^^ t40) fun t43 => strictBool (t43 && y16) fun z3 => strictBool (z3 ^^ z5) fun tc12 => strictBool (t43 && y13) fun z12 => strictBool (t40 && y5) fun z13 => strictBool (t40 && y1) fun z4 =>
  strictBool (z3 ^^ z4) fun tc6 => strictBool (t23 ^^ t33) fun t34 => strictBool (t36 ^^ t34) fun t37 => strictBool (t40 ^^ t37) fun t41 => strictBool (t41 && y10) fun z8 => strictBool (t41 && y8) fun z17 => strictBool (t33 ^^ t37) fun t44 =>
  ⟨t29, t33, t37, t41, t44, tc12, tc6, u7, y11, y12, y14, y15, y17, y3, y4, y6, y9, z12, z13, z14, z17, z8⟩
private theorem extract_SubModBoolStage3 (inp : Model.SubBytesW2) (k : Nat) : extractSubModBoolW3 (Model.subBytesFsStage3 inp) k = SubModBoolStage3 (extractSubModBoolW2 inp k) := by
  ext1 <;> simp only [extractSubModBoolW3, extractSubModBoolW2, Model.subBytesFsStage3, SubModBoolStage3, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubModBoolStage4 (inp : SubModBoolB3) : SubModBoolB4 :=
  strictBool inp.t29 fun t29 => strictBool inp.t33 fun t33 => strictBool inp.t37 fun t37 => strictBool inp.t41 fun t41 => strictBool inp.t44 fun t44 => strictBool inp.tc12 fun tc12 => strictBool inp.tc6 fun tc6 =>
  strictBool inp.u7 fun u7 => strictBool inp.y11 fun y11 => strictBool inp.y12 fun y12 => strictBool inp.y14 fun y14 => strictBool inp.y15 fun y15 => strictBool inp.y17 fun y17 => strictBool inp.y3 fun y3 =>
  strictBool inp.y4 fun y4 => strictBool inp.y6 fun y6 => strictBool inp.y9 fun y9 => strictBool inp.z12 fun z12 => strictBool inp.z13 fun z13 => strictBool inp.z14 fun z14 => strictBool inp.z17 fun z17 =>
  strictBool inp.z8 fun z8 => strictBool (t44 && y15) fun z0 => strictBool (t44 && y12) fun z9 => strictBool (t37 && y3) fun z10 => strictBool (t37 && y6) fun z1 => strictBool (z1 ^^ z0) fun tc5 => strictBool (tc6 ^^ tc5) fun tc11 =>
  strictBool (t33 && y4) fun z11 => strictBool (t29 ^^ t33) fun t42 => strictBool (t42 ^^ t41) fun t45 => strictBool (t45 && y17) fun z7 => strictBool (z7 ^^ tc6) fun tc8 => strictBool (t45 && y14) fun z16 => strictBool (t42 && y11) fun z6 =>
  strictBool (z6 ^^ tc8) fun tc16 => strictBool (t42 && y9) fun z15 => strictBool (z15 ^^ tc16) fun tc20 => strictBool (z15 ^^ z16) fun tc1 => strictBool (z10 ^^ tc1) fun tc2 => strictBool (tc2 ^^ z11) fun tc21 => strictBool (z9 ^^ tc2) fun tc3 =>
  strictBool (tc3 ^^ tc16) fun s0 => strictBool (tc3 ^^ tc11) fun s3 => strictBool (s3 ^^ tc16) fun s1 => strictBool (z13 ^^ tc1) fun tc13 => strictBool (t33 && u7) fun z2 =>
  ⟨s0, s1, s3, tc12, tc13, tc20, tc21, tc8, z0, z12, z14, z17, z2, z8⟩
private theorem extract_SubModBoolStage4 (inp : Model.SubBytesW3) (k : Nat) : extractSubModBoolW4 (Model.subBytesFsStage4 inp) k = SubModBoolStage4 (extractSubModBoolW3 inp k) := by
  ext1 <;> simp only [extractSubModBoolW4, extractSubModBoolW3, Model.subBytesFsStage4, SubModBoolStage4, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def SubModBoolStage5 (inp : SubModBoolB4) : FsBool8 :=
  strictBool inp.s0 fun s0 => strictBool inp.s1 fun s1 => strictBool inp.s3 fun s3 => strictBool inp.tc12 fun tc12 => strictBool inp.tc13 fun tc13 => strictBool inp.tc20 fun tc20 => strictBool inp.tc21 fun tc21 =>
  strictBool inp.tc8 fun tc8 => strictBool inp.z0 fun z0 => strictBool inp.z12 fun z12 => strictBool inp.z14 fun z14 => strictBool inp.z17 fun z17 => strictBool inp.z2 fun z2 => strictBool inp.z8 fun z8 =>
  strictBool (z0 ^^ z2) fun tc4 => strictBool (z12 ^^ tc4) fun tc7 => strictBool (z8 ^^ tc7) fun tc9 => strictBool (tc8 ^^ tc9) fun tc10 => strictBool (z14 ^^ tc10) fun tc17 => strictBool (tc21 ^^ tc17) fun s5 => strictBool (tc17 ^^ tc20) fun tc26 =>
  strictBool (tc26 ^^ z17) fun s2 => strictBool (tc4 ^^ tc12) fun tc14 => strictBool (tc13 ^^ tc14) fun tc18 => strictBool (tc10 ^^ tc18) fun s6 => strictBool (z12 ^^ tc18) fun s7 => strictBool (tc14 ^^ s3) fun s4 =>
  ⟨s7, s6, s5, s4, s3, s2, s1, s0⟩
private theorem extract_SubModBoolStage5 (inp : Model.SubBytesW4) (k : Nat) : extractBool8 (Model.subBytesFsStage5 inp) k = SubModBoolStage5 (extractSubModBoolW4 inp k) := by
  ext1 <;> simp only [extractBool8, extractSubModBoolW4, Model.subBytesFsStage5, SubModBoolStage5, strictBool_eq, BitVec.getLsbD_xor]
private def SubModBoolFull (x : FsBool8) : FsBool8 := SubModBoolStage5 (SubModBoolStage4 (SubModBoolStage3 (SubModBoolStage2 (SubModBoolStage1 (x)))))

private theorem subAsmBool_eq_subModBool :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      SubAsmBoolFull ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ =
        SubModBoolFull ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := by
  decide

private theorem subAsmFull_eq_subBytesFs (st : Model.FsState) :
    SubAsmFull st = Model.subBytesFs st := by
  apply eq_of_extractBool8_eq; intro k _
  rw [SubAsmFull, extract_SubAsmStage5, extract_SubAsmStage4, extract_SubAsmStage3,
    extract_SubAsmStage2, extract_SubAsmStage1, Model.subBytesFs, extract_SubModBoolStage5,
    extract_SubModBoolStage4, extract_SubModBoolStage3, extract_SubModBoolStage2,
    extract_SubModBoolStage1]
  cases hx : extractBool8 st k
  exact subAsmBool_eq_subModBool _ _ _ _ _ _ _ _

private structure InvAsmW1 where (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x18 x19 x20 x21 x25 : BitVec 64)
@[ext] private structure InvAsmBoolB1 where (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x18 x19 x20 x21 x25 : Bool)
private def extractInvAsmW1 (w : InvAsmW1) (k : Nat) : InvAsmBoolB1 := ⟨w.x1.getLsbD k, w.x3.getLsbD k, w.x4.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x7.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k, w.x11.getLsbD k,
    w.x12.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x18.getLsbD k, w.x19.getLsbD k, w.x20.getLsbD k, w.x21.getLsbD k, w.x25.getLsbD k⟩
private def InvAsmRegs1 (s : State) (w : InvAsmW1) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 4#5) = w.x4 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧ s.readReg64 (.gpr 6#5) = w.x6 ∧
  s.readReg64 (.gpr 7#5) = w.x7 ∧ s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧ s.readReg64 (.gpr 11#5) = w.x11 ∧
  s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧ s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 18#5) = w.x18 ∧
  s.readReg64 (.gpr 19#5) = w.x19 ∧ s.readReg64 (.gpr 20#5) = w.x20 ∧ s.readReg64 (.gpr 21#5) = w.x21 ∧ s.readReg64 (.gpr 25#5) = w.x25
private structure InvAsmW2 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x30 : BitVec 64)
@[ext] private structure InvAsmBoolB2 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x30 : Bool)
private def extractInvAsmW2 (w : InvAsmW2) (k : Nat) : InvAsmBoolB2 := ⟨w.x1.getLsbD k, w.x2.getLsbD k, w.x3.getLsbD k, w.x4.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x7.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k,
    w.x11.getLsbD k, w.x12.getLsbD k, w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x17.getLsbD k, w.x18.getLsbD k, w.x19.getLsbD k, w.x20.getLsbD k,
    w.x21.getLsbD k, w.x22.getLsbD k, w.x23.getLsbD k, w.x24.getLsbD k, w.x25.getLsbD k, w.x26.getLsbD k, w.x28.getLsbD k, w.x30.getLsbD k⟩
private def InvAsmRegs2 (s : State) (w : InvAsmW2) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 2#5) = w.x2 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 4#5) = w.x4 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧
  s.readReg64 (.gpr 6#5) = w.x6 ∧ s.readReg64 (.gpr 7#5) = w.x7 ∧ s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧
  s.readReg64 (.gpr 11#5) = w.x11 ∧ s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 13#5) = w.x13 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧
  s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 17#5) = w.x17 ∧ s.readReg64 (.gpr 18#5) = w.x18 ∧ s.readReg64 (.gpr 19#5) = w.x19 ∧ s.readReg64 (.gpr 20#5) = w.x20 ∧
  s.readReg64 (.gpr 21#5) = w.x21 ∧ s.readReg64 (.gpr 22#5) = w.x22 ∧ s.readReg64 (.gpr 23#5) = w.x23 ∧ s.readReg64 (.gpr 24#5) = w.x24 ∧ s.readReg64 (.gpr 25#5) = w.x25 ∧
  s.readReg64 (.gpr 26#5) = w.x26 ∧ s.readReg64 (.gpr 28#5) = w.x28 ∧ s.readReg64 (.gpr 30#5) = w.x30
private structure InvAsmW3 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x25 x26 x27 x28 : BitVec 64)
@[ext] private structure InvAsmBoolB3 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x25 x26 x27 x28 : Bool)
private def extractInvAsmW3 (w : InvAsmW3) (k : Nat) : InvAsmBoolB3 := ⟨w.x1.getLsbD k, w.x2.getLsbD k, w.x3.getLsbD k, w.x4.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x7.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k,
    w.x11.getLsbD k, w.x12.getLsbD k, w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x17.getLsbD k, w.x18.getLsbD k, w.x19.getLsbD k, w.x20.getLsbD k,
    w.x22.getLsbD k, w.x23.getLsbD k, w.x25.getLsbD k, w.x26.getLsbD k, w.x27.getLsbD k, w.x28.getLsbD k⟩
private def InvAsmRegs3 (s : State) (w : InvAsmW3) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 2#5) = w.x2 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 4#5) = w.x4 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧
  s.readReg64 (.gpr 6#5) = w.x6 ∧ s.readReg64 (.gpr 7#5) = w.x7 ∧ s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧
  s.readReg64 (.gpr 11#5) = w.x11 ∧ s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 13#5) = w.x13 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧
  s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 17#5) = w.x17 ∧ s.readReg64 (.gpr 18#5) = w.x18 ∧ s.readReg64 (.gpr 19#5) = w.x19 ∧ s.readReg64 (.gpr 20#5) = w.x20 ∧
  s.readReg64 (.gpr 22#5) = w.x22 ∧ s.readReg64 (.gpr 23#5) = w.x23 ∧ s.readReg64 (.gpr 25#5) = w.x25 ∧ s.readReg64 (.gpr 26#5) = w.x26 ∧ s.readReg64 (.gpr 27#5) = w.x27 ∧
  s.readReg64 (.gpr 28#5) = w.x28
private structure InvAsmW4 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : BitVec 64)
@[ext] private structure InvAsmBoolB4 where (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : Bool)
private def extractInvAsmW4 (w : InvAsmW4) (k : Nat) : InvAsmBoolB4 := ⟨w.x1.getLsbD k, w.x2.getLsbD k, w.x3.getLsbD k, w.x4.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x7.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k,
    w.x11.getLsbD k, w.x12.getLsbD k, w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x17.getLsbD k, w.x18.getLsbD k, w.x19.getLsbD k, w.x20.getLsbD k,
    w.x21.getLsbD k, w.x22.getLsbD k⟩
private def InvAsmRegs4 (s : State) (w : InvAsmW4) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 2#5) = w.x2 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 4#5) = w.x4 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧
  s.readReg64 (.gpr 6#5) = w.x6 ∧ s.readReg64 (.gpr 7#5) = w.x7 ∧ s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧
  s.readReg64 (.gpr 11#5) = w.x11 ∧ s.readReg64 (.gpr 12#5) = w.x12 ∧ s.readReg64 (.gpr 13#5) = w.x13 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧
  s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 17#5) = w.x17 ∧ s.readReg64 (.gpr 18#5) = w.x18 ∧ s.readReg64 (.gpr 19#5) = w.x19 ∧ s.readReg64 (.gpr 20#5) = w.x20 ∧
  s.readReg64 (.gpr 21#5) = w.x21 ∧ s.readReg64 (.gpr 22#5) = w.x22
private structure InvAsmW5 where (x1 x2 x3 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 : BitVec 64)
@[ext] private structure InvAsmBoolB5 where (x1 x2 x3 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 : Bool)
private def extractInvAsmW5 (w : InvAsmW5) (k : Nat) : InvAsmBoolB5 := ⟨w.x1.getLsbD k, w.x2.getLsbD k, w.x3.getLsbD k, w.x5.getLsbD k, w.x6.getLsbD k, w.x8.getLsbD k, w.x9.getLsbD k, w.x10.getLsbD k, w.x11.getLsbD k, w.x12.getLsbD k,
    w.x13.getLsbD k, w.x14.getLsbD k, w.x15.getLsbD k, w.x16.getLsbD k, w.x17.getLsbD k, w.x18.getLsbD k, w.x23.getLsbD k, w.x24.getLsbD k⟩
private def InvAsmRegs5 (s : State) (w : InvAsmW5) : Prop :=
  s.readReg64 (.gpr 1#5) = w.x1 ∧ s.readReg64 (.gpr 2#5) = w.x2 ∧ s.readReg64 (.gpr 3#5) = w.x3 ∧ s.readReg64 (.gpr 5#5) = w.x5 ∧ s.readReg64 (.gpr 6#5) = w.x6 ∧
  s.readReg64 (.gpr 8#5) = w.x8 ∧ s.readReg64 (.gpr 9#5) = w.x9 ∧ s.readReg64 (.gpr 10#5) = w.x10 ∧ s.readReg64 (.gpr 11#5) = w.x11 ∧ s.readReg64 (.gpr 12#5) = w.x12 ∧
  s.readReg64 (.gpr 13#5) = w.x13 ∧ s.readReg64 (.gpr 14#5) = w.x14 ∧ s.readReg64 (.gpr 15#5) = w.x15 ∧ s.readReg64 (.gpr 16#5) = w.x16 ∧ s.readReg64 (.gpr 17#5) = w.x17 ∧
  s.readReg64 (.gpr 18#5) = w.x18 ∧ s.readReg64 (.gpr 23#5) = w.x23 ∧ s.readReg64 (.gpr 24#5) = w.x24
private def InvAsmStage1 (inp : Model.FsState) : InvAsmW1 :=
  let x20 := inp.s3; let x9 := inp.s4; let x7 := inp.s2; let x16 := inp.s6; let x5 := inp.s7; let x4 := inp.s5; let x11 := inp.s0; let x1 := inp.s1; let x3 := x9 ^^^ x20
  let x14 := x16 ^^^ x9; let x10 := x5 ^^^ x16; let x8 := x5 ^^^ x9; let x21 := x20 ^^^ x11; let x18 := x1 ^^^ x11; let x19 := x7 ^^^ x1; let x7 := x4 ^^^ x7; let x12 := x10 ^^^ x21; let x6 := x14 ^^^ x18
  let x25 := x16 ^^^ x1; let x1 := x3 ^^^ x19; let x5 := x5 ^^^ x7; let x9 := x8 ^^^ x16; let x15 := x3 ^^^ x11; let x11 := x10 ^^^ x18; let x16 := x14 ^^^ x7; let x7 := x12 ^^^ x1
  ⟨x1, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x14, x15, x16, x18, x19, x20, x21, x25⟩
private def InvAsmBoolStage1 (inp : FsBool8) : InvAsmBoolB1 :=
  strictBool inp.b3 fun x20 => strictBool inp.b4 fun x9 => strictBool inp.b2 fun x7 => strictBool inp.b6 fun x16 => strictBool inp.b7 fun x5 => strictBool inp.b5 fun x4 => strictBool inp.b0 fun x11 =>
  strictBool inp.b1 fun x1 => strictBool (x9 ^^ x20) fun x3 => strictBool (x16 ^^ x9) fun x14 => strictBool (x5 ^^ x16) fun x10 => strictBool (x5 ^^ x9) fun x8 => strictBool (x20 ^^ x11) fun x21 => strictBool (x1 ^^ x11) fun x18 =>
  strictBool (x7 ^^ x1) fun x19 => strictBool (x4 ^^ x7) fun x7 => strictBool (x10 ^^ x21) fun x12 => strictBool (x14 ^^ x18) fun x6 => strictBool (x16 ^^ x1) fun x25 => strictBool (x3 ^^ x19) fun x1 => strictBool (x5 ^^ x7) fun x5 =>
  strictBool (x8 ^^ x16) fun x9 => strictBool (x3 ^^ x11) fun x15 => strictBool (x10 ^^ x18) fun x11 => strictBool (x14 ^^ x7) fun x16 => strictBool (x12 ^^ x1) fun x7 =>
  ⟨x1, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x14, x15, x16, x18, x19, x20, x21, x25⟩
private theorem extract_InvAsmStage1 (inp : Model.FsState) (k : Nat) : extractInvAsmW1 (InvAsmStage1 inp) k = InvAsmBoolStage1 (extractBool8 inp k) := by
  ext1 <;> simp only [extractInvAsmW1, extractBool8, InvAsmStage1, InvAsmBoolStage1, strictBool_eq, BitVec.getLsbD_xor]
private def InvAsmStage2 (inp : InvAsmW1) : InvAsmW2 :=
  let x1 := inp.x1; let x3 := inp.x3; let x4 := inp.x4; let x5 := inp.x5; let x6 := inp.x6; let x7 := inp.x7; let x8 := inp.x8; let x9 := inp.x9; let x10 := inp.x10
  let x11 := inp.x11; let x12 := inp.x12; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x18 := inp.x18; let x19 := inp.x19; let x20 := inp.x20; let x21 := inp.x21
  let x25 := inp.x25; let x28 := x6 &&& x5; let x13 := x9 ^^^ x20; let x27 := x11 &&& x16; let x30 := x7 &&& x3; let x7 := x28 ^^^ x21; let x20 := x4 ^^^ x20; let x17 := x3 ^^^ x18; let x2 := x25 ^^^ x21
  let x21 := x7 ^^^ x27; let x28 := x13 &&& x1; let x7 := x20 ^^^ x25; let x22 := x9 &&& x8; let x18 := x6 ^^^ x4; let x20 := x28 ^^^ x30; let x25 := x19 ^^^ x12; let x28 := x7 &&& x17; let x23 := x14 &&& x15
  let x26 := x18 &&& x2; let x22 := x25 ^^^ x22; let x25 := x7 ||| x17; let x28 := x28 ^^^ x3; let x24 := x12 &&& x10; let x22 := x22 ^^^ x27
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x28, x30⟩
private def InvAsmBoolStage2 (inp : InvAsmBoolB1) : InvAsmBoolB2 :=
  strictBool inp.x1 fun x1 => strictBool inp.x3 fun x3 => strictBool inp.x4 fun x4 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x7 fun x7 => strictBool inp.x8 fun x8 =>
  strictBool inp.x9 fun x9 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x14 fun x14 => strictBool inp.x15 fun x15 => strictBool inp.x16 fun x16 =>
  strictBool inp.x18 fun x18 => strictBool inp.x19 fun x19 => strictBool inp.x20 fun x20 => strictBool inp.x21 fun x21 => strictBool inp.x25 fun x25 => strictBool (x6 && x5) fun x28 => strictBool (x9 ^^ x20) fun x13 =>
  strictBool (x11 && x16) fun x27 => strictBool (x7 && x3) fun x30 => strictBool (x28 ^^ x21) fun x7 => strictBool (x4 ^^ x20) fun x20 => strictBool (x3 ^^ x18) fun x17 => strictBool (x25 ^^ x21) fun x2 => strictBool (x7 ^^ x27) fun x21 =>
  strictBool (x13 && x1) fun x28 => strictBool (x20 ^^ x25) fun x7 => strictBool (x9 && x8) fun x22 => strictBool (x6 ^^ x4) fun x18 => strictBool (x28 ^^ x30) fun x20 => strictBool (x19 ^^ x12) fun x25 => strictBool (x7 && x17) fun x28 =>
  strictBool (x14 && x15) fun x23 => strictBool (x18 && x2) fun x26 => strictBool (x25 ^^ x22) fun x22 => strictBool (x7 || x17) fun x25 => strictBool (x28 ^^ x3) fun x28 => strictBool (x12 && x10) fun x24 => strictBool (x22 ^^ x27) fun x22 =>
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x28, x30⟩
private theorem extract_InvAsmStage2 (inp : InvAsmW1) (k : Nat) : extractInvAsmW2 (InvAsmStage2 inp) k = InvAsmBoolStage2 (extractInvAsmW1 inp k) := by
  ext1 <;> simp only [extractInvAsmW2, extractInvAsmW1, InvAsmStage2, InvAsmBoolStage2, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
private def InvAsmStage3 (inp : InvAsmW2) : InvAsmW3 :=
  let x1 := inp.x1; let x2 := inp.x2; let x3 := inp.x3; let x4 := inp.x4; let x5 := inp.x5; let x6 := inp.x6; let x7 := inp.x7; let x8 := inp.x8; let x9 := inp.x9
  let x10 := inp.x10; let x11 := inp.x11; let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x17 := inp.x17; let x18 := inp.x18
  let x19 := inp.x19; let x20 := inp.x20; let x21 := inp.x21; let x22 := inp.x22; let x23 := inp.x23; let x24 := inp.x24; let x25 := inp.x25; let x26 := inp.x26; let x28 := inp.x28
  let x30 := inp.x30; let x23 := x25 ^^^ x23; let x25 := x28 ^^^ x26; let x24 := x30 ^^^ x24; let x22 := x22 ^^^ x20; let x20 := x23 ^^^ x20; let x4 := x25 ^^^ x4; let x21 := x21 ^^^ x24; let x23 := x22 &&& x20
  let x24 := x4 ^^^ x24; let x4 := x23 ^^^ x21; let x27 := x22 ^^^ x21; let x25 := x20 ^^^ x24; let x26 := x23 ^^^ x24; let x20 := x21 &&& x20; let x4 := x4 &&& x25; let x28 := x4 ^^^ x24; let x4 := x26 &&& x27
  let x26 := x4 ^^^ x21; let x4 := x28 &&& x6; let x6 := x22 &&& x24; let x22 := x26 ^^^ x28; let x6 := x6 &&& x27; let x18 := x26 &&& x18
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x22, x23, x25, x26, x27, x28⟩
private def InvAsmBoolStage3 (inp : InvAsmBoolB2) : InvAsmBoolB3 :=
  strictBool inp.x1 fun x1 => strictBool inp.x2 fun x2 => strictBool inp.x3 fun x3 => strictBool inp.x4 fun x4 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x7 fun x7 =>
  strictBool inp.x8 fun x8 => strictBool inp.x9 fun x9 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 =>
  strictBool inp.x15 fun x15 => strictBool inp.x16 fun x16 => strictBool inp.x17 fun x17 => strictBool inp.x18 fun x18 => strictBool inp.x19 fun x19 => strictBool inp.x20 fun x20 => strictBool inp.x21 fun x21 =>
  strictBool inp.x22 fun x22 => strictBool inp.x23 fun x23 => strictBool inp.x24 fun x24 => strictBool inp.x25 fun x25 => strictBool inp.x26 fun x26 => strictBool inp.x28 fun x28 => strictBool inp.x30 fun x30 =>
  strictBool (x25 ^^ x23) fun x23 => strictBool (x28 ^^ x26) fun x25 => strictBool (x30 ^^ x24) fun x24 => strictBool (x22 ^^ x20) fun x22 => strictBool (x23 ^^ x20) fun x20 => strictBool (x25 ^^ x4) fun x4 => strictBool (x21 ^^ x24) fun x21 =>
  strictBool (x22 && x20) fun x23 => strictBool (x4 ^^ x24) fun x24 => strictBool (x23 ^^ x21) fun x4 => strictBool (x22 ^^ x21) fun x27 => strictBool (x20 ^^ x24) fun x25 => strictBool (x23 ^^ x24) fun x26 => strictBool (x21 && x20) fun x20 =>
  strictBool (x4 && x25) fun x4 => strictBool (x4 ^^ x24) fun x28 => strictBool (x26 && x27) fun x4 => strictBool (x4 ^^ x21) fun x26 => strictBool (x28 && x6) fun x4 => strictBool (x22 && x24) fun x6 => strictBool (x26 ^^ x28) fun x22 =>
  strictBool (x6 && x27) fun x6 => strictBool (x26 && x18) fun x18 =>
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x22, x23, x25, x26, x27, x28⟩
private theorem extract_InvAsmStage3 (inp : InvAsmW2) (k : Nat) : extractInvAsmW3 (InvAsmStage3 inp) k = InvAsmBoolStage3 (extractInvAsmW2 inp k) := by
  ext1 <;> simp only [extractInvAsmW3, extractInvAsmW2, InvAsmStage3, InvAsmBoolStage3, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def InvAsmStage4 (inp : InvAsmW3) : InvAsmW4 :=
  let x1 := inp.x1; let x2 := inp.x2; let x3 := inp.x3; let x4 := inp.x4; let x5 := inp.x5; let x6 := inp.x6; let x7 := inp.x7; let x8 := inp.x8; let x9 := inp.x9
  let x10 := inp.x10; let x11 := inp.x11; let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x17 := inp.x17; let x18 := inp.x18
  let x19 := inp.x19; let x20 := inp.x20; let x22 := inp.x22; let x23 := inp.x23; let x25 := inp.x25; let x26 := inp.x26; let x27 := inp.x27; let x28 := inp.x28; let x24 := x22 &&& x3
  let x3 := x12 ^^^ x19; let x19 := x23 ^^^ x27; let x6 := x19 ^^^ x6; let x19 := x25 &&& ~~~x20; let x21 := x24 ^^^ x4; let x24 := x26 ^^^ x6; let x19 := x19 ^^^ x23; let x20 := x26 &&& x2; let x2 := x24 &&& x7
  let x7 := x6 ^^^ x19; let x3 := x22 &&& x3; let x22 := x22 ^^^ x7; let x17 := x24 &&& x17; let x14 := x6 &&& x14; let x1 := x22 &&& x1; let x13 := x22 &&& x13; let x22 := x28 ^^^ x19; let x15 := x6 &&& x15
  let x6 := x17 ^^^ x14; let x16 := x22 &&& x16; let x5 := x28 &&& x5; let x6 := x6 ^^^ x3
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22⟩
private def InvAsmBoolStage4 (inp : InvAsmBoolB3) : InvAsmBoolB4 :=
  strictBool inp.x1 fun x1 => strictBool inp.x2 fun x2 => strictBool inp.x3 fun x3 => strictBool inp.x4 fun x4 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x7 fun x7 =>
  strictBool inp.x8 fun x8 => strictBool inp.x9 fun x9 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 =>
  strictBool inp.x15 fun x15 => strictBool inp.x16 fun x16 => strictBool inp.x17 fun x17 => strictBool inp.x18 fun x18 => strictBool inp.x19 fun x19 => strictBool inp.x20 fun x20 => strictBool inp.x22 fun x22 =>
  strictBool inp.x23 fun x23 => strictBool inp.x25 fun x25 => strictBool inp.x26 fun x26 => strictBool inp.x27 fun x27 => strictBool inp.x28 fun x28 => strictBool (x22 && x3) fun x24 => strictBool (x12 ^^ x19) fun x3 =>
  strictBool (x23 ^^ x27) fun x19 => strictBool (x19 ^^ x6) fun x6 => strictBool (x25 && !x20) fun x19 => strictBool (x24 ^^ x4) fun x21 => strictBool (x26 ^^ x6) fun x24 => strictBool (x19 ^^ x23) fun x19 => strictBool (x26 && x2) fun x20 =>
  strictBool (x24 && x7) fun x2 => strictBool (x6 ^^ x19) fun x7 => strictBool (x22 && x3) fun x3 => strictBool (x22 ^^ x7) fun x22 => strictBool (x24 && x17) fun x17 => strictBool (x6 && x14) fun x14 => strictBool (x22 && x1) fun x1 =>
  strictBool (x22 && x13) fun x13 => strictBool (x28 ^^ x19) fun x22 => strictBool (x6 && x15) fun x15 => strictBool (x17 ^^ x14) fun x6 => strictBool (x22 && x16) fun x16 => strictBool (x28 && x5) fun x5 => strictBool (x6 ^^ x3) fun x6 =>
  ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22⟩
private theorem extract_InvAsmStage4 (inp : InvAsmW3) (k : Nat) (hk : k < 64) : extractInvAsmW4 (InvAsmStage4 inp) k = InvAsmBoolStage4 (extractInvAsmW3 inp k) := by
  ext1 <;> simp only [extractInvAsmW4, extractInvAsmW3, InvAsmStage4, InvAsmBoolStage4, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true, Bool.true_and]
private def InvAsmStage5 (inp : InvAsmW4) : InvAsmW5 :=
  let x1 := inp.x1; let x2 := inp.x2; let x3 := inp.x3; let x4 := inp.x4; let x5 := inp.x5; let x6 := inp.x6; let x7 := inp.x7; let x8 := inp.x8; let x9 := inp.x9
  let x10 := inp.x10; let x11 := inp.x11; let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x17 := inp.x17; let x18 := inp.x18
  let x19 := inp.x19; let x20 := inp.x20; let x21 := inp.x21; let x22 := inp.x22; let x1 := x1 ^^^ x15; let x12 := x7 &&& x12; let x10 := x7 &&& x10; let x7 := x16 ^^^ x18; let x11 := x22 &&& x11
  let x9 := x19 &&& x9; let x8 := x19 &&& x8; let x1 := x1 ^^^ x6; let x23 := x13 ^^^ x2; let x24 := x7 ^^^ x10; let x10 := x11 ^^^ x10; let x9 := x15 ^^^ x9; let x8 := x5 ^^^ x8; let x20 := x2 ^^^ x20
  let x13 := x13 ^^^ x12; let x23 := x23 ^^^ x1; let x11 := x21 ^^^ x10; let x15 := x9 ^^^ x7; let x9 := x9 ^^^ x3; let x3 := x8 ^^^ x4; let x6 := x13 ^^^ x6; let x9 := x9 ^^^ x20
  ⟨x1, x2, x3, x5, x6, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x23, x24⟩
private def InvAsmBoolStage5 (inp : InvAsmBoolB4) : InvAsmBoolB5 :=
  strictBool inp.x1 fun x1 => strictBool inp.x2 fun x2 => strictBool inp.x3 fun x3 => strictBool inp.x4 fun x4 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x7 fun x7 =>
  strictBool inp.x8 fun x8 => strictBool inp.x9 fun x9 => strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 =>
  strictBool inp.x15 fun x15 => strictBool inp.x16 fun x16 => strictBool inp.x17 fun x17 => strictBool inp.x18 fun x18 => strictBool inp.x19 fun x19 => strictBool inp.x20 fun x20 => strictBool inp.x21 fun x21 =>
  strictBool inp.x22 fun x22 => strictBool (x1 ^^ x15) fun x1 => strictBool (x7 && x12) fun x12 => strictBool (x7 && x10) fun x10 => strictBool (x16 ^^ x18) fun x7 => strictBool (x22 && x11) fun x11 => strictBool (x19 && x9) fun x9 =>
  strictBool (x19 && x8) fun x8 => strictBool (x1 ^^ x6) fun x1 => strictBool (x13 ^^ x2) fun x23 => strictBool (x7 ^^ x10) fun x24 => strictBool (x11 ^^ x10) fun x10 => strictBool (x15 ^^ x9) fun x9 => strictBool (x5 ^^ x8) fun x8 =>
  strictBool (x2 ^^ x20) fun x20 => strictBool (x13 ^^ x12) fun x13 => strictBool (x23 ^^ x1) fun x23 => strictBool (x21 ^^ x10) fun x11 => strictBool (x9 ^^ x7) fun x15 => strictBool (x9 ^^ x3) fun x9 => strictBool (x8 ^^ x4) fun x3 =>
  strictBool (x13 ^^ x6) fun x6 => strictBool (x9 ^^ x20) fun x9 =>
  ⟨x1, x2, x3, x5, x6, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x23, x24⟩
private theorem extract_InvAsmStage5 (inp : InvAsmW4) (k : Nat) : extractInvAsmW5 (InvAsmStage5 inp) k = InvAsmBoolStage5 (extractInvAsmW4 inp k) := by
  ext1 <;> simp only [extractInvAsmW5, extractInvAsmW4, InvAsmStage5, InvAsmBoolStage5, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def InvAsmStage6 (inp : InvAsmW5) : Model.FsState :=
  let x1 := inp.x1; let x2 := inp.x2; let x3 := inp.x3; let x5 := inp.x5; let x6 := inp.x6; let x8 := inp.x8; let x9 := inp.x9; let x10 := inp.x10; let x11 := inp.x11
  let x12 := inp.x12; let x13 := inp.x13; let x14 := inp.x14; let x15 := inp.x15; let x16 := inp.x16; let x17 := inp.x17; let x18 := inp.x18; let x23 := inp.x23; let x24 := inp.x24
  let out0 := x11; let out1 := x23; let x8 := x14 ^^^ x8; let x11 := x24 ^^^ x3; let x14 := x17 ^^^ x3; let x16 := x16 ^^^ x5; let x15 := x6 ^^^ x15; let x11 := x11 ^^^ x1; let x8 := x8 ^^^ x12
  let x12 := x9 ^^^ x14; let x16 := x16 ^^^ x6; let out2 := x15; let out3 := x11; let x8 := x9 ^^^ x8; let x9 := x12 ^^^ x13; let x11 := x2 ^^^ x18; let x8 := x8 ^^^ x10; let out4 := x16
  let out5 := x9; let x9 := x11 ^^^ x6; let out6 := x8; let out7 := x9
  ⟨out0, out1, out2, out3, out4, out5, out6, out7⟩
private def InvAsmBoolStage6 (inp : InvAsmBoolB5) : FsBool8 :=
  strictBool inp.x1 fun x1 => strictBool inp.x2 fun x2 => strictBool inp.x3 fun x3 => strictBool inp.x5 fun x5 => strictBool inp.x6 fun x6 => strictBool inp.x8 fun x8 => strictBool inp.x9 fun x9 =>
  strictBool inp.x10 fun x10 => strictBool inp.x11 fun x11 => strictBool inp.x12 fun x12 => strictBool inp.x13 fun x13 => strictBool inp.x14 fun x14 => strictBool inp.x15 fun x15 => strictBool inp.x16 fun x16 =>
  strictBool inp.x17 fun x17 => strictBool inp.x18 fun x18 => strictBool inp.x23 fun x23 => strictBool inp.x24 fun x24 => strictBool x11 fun out0 => strictBool x23 fun out1 => strictBool (x14 ^^ x8) fun x8 =>
  strictBool (x24 ^^ x3) fun x11 => strictBool (x17 ^^ x3) fun x14 => strictBool (x16 ^^ x5) fun x16 => strictBool (x6 ^^ x15) fun x15 => strictBool (x11 ^^ x1) fun x11 => strictBool (x8 ^^ x12) fun x8 => strictBool (x9 ^^ x14) fun x12 =>
  strictBool (x16 ^^ x6) fun x16 => strictBool x15 fun out2 => strictBool x11 fun out3 => strictBool (x9 ^^ x8) fun x8 => strictBool (x12 ^^ x13) fun x9 => strictBool (x2 ^^ x18) fun x11 => strictBool (x8 ^^ x10) fun x8 =>
  strictBool x16 fun out4 => strictBool x9 fun out5 => strictBool (x11 ^^ x6) fun x9 => strictBool x8 fun out6 => strictBool x9 fun out7 =>
  ⟨out0, out1, out2, out3, out4, out5, out6, out7⟩
private theorem extract_InvAsmStage6 (inp : InvAsmW5) (k : Nat) : extractBool8 (InvAsmStage6 inp) k = InvAsmBoolStage6 (extractInvAsmW5 inp k) := by
  ext1 <;> simp only [extractBool8, extractInvAsmW5, InvAsmStage6, InvAsmBoolStage6, strictBool_eq, BitVec.getLsbD_xor]
private def InvAsmFull (st : Model.FsState) : Model.FsState := InvAsmStage6 (InvAsmStage5 (InvAsmStage4 (InvAsmStage3 (InvAsmStage2 (InvAsmStage1 (st))))))
private def InvAsmBoolFull (x : FsBool8) : FsBool8 := InvAsmBoolStage6 (InvAsmBoolStage5 (InvAsmBoolStage4 (InvAsmBoolStage3 (InvAsmBoolStage2 (InvAsmBoolStage1 (x))))))

@[ext] private structure InvModBoolB1 where (m1 m14 m2 m7 m9 r13 t1 t10 t13 t17 t19 t2 t20 t22 t23 t24 t25 t3 t4 t6 t8 t9 u2 u4 u5 u6 y5 : Bool)
private def extractInvModBoolW1 (w : Model.InvSubBytesW1) (k : Nat) : InvModBoolB1 := ⟨w.m1.getLsbD k, w.m14.getLsbD k, w.m2.getLsbD k, w.m7.getLsbD k, w.m9.getLsbD k, w.r13.getLsbD k, w.t1.getLsbD k, w.t10.getLsbD k, w.t13.getLsbD k, w.t17.getLsbD k,
    w.t19.getLsbD k, w.t2.getLsbD k, w.t20.getLsbD k, w.t22.getLsbD k, w.t23.getLsbD k, w.t24.getLsbD k, w.t25.getLsbD k, w.t3.getLsbD k, w.t4.getLsbD k, w.t6.getLsbD k,
    w.t8.getLsbD k, w.t9.getLsbD k, w.u2.getLsbD k, w.u4.getLsbD k, w.u5.getLsbD k, w.u6.getLsbD k, w.y5.getLsbD k⟩
@[ext] private structure InvModBoolB2 where (m10 m15 m20 m21 m22 m25 m26 t1 t10 t13 t15 t16 t17 t19 t2 t20 t22 t23 t25 t27 t3 t4 t6 t8 t9 y5 : Bool)
private def extractInvModBoolW2 (w : Model.InvSubBytesW2) (k : Nat) : InvModBoolB2 := ⟨w.m10.getLsbD k, w.m15.getLsbD k, w.m20.getLsbD k, w.m21.getLsbD k, w.m22.getLsbD k, w.m25.getLsbD k, w.m26.getLsbD k, w.t1.getLsbD k, w.t10.getLsbD k, w.t13.getLsbD k,
    w.t15.getLsbD k, w.t16.getLsbD k, w.t17.getLsbD k, w.t19.getLsbD k, w.t2.getLsbD k, w.t20.getLsbD k, w.t22.getLsbD k, w.t23.getLsbD k, w.t25.getLsbD k, w.t27.getLsbD k,
    w.t3.getLsbD k, w.t4.getLsbD k, w.t6.getLsbD k, w.t8.getLsbD k, w.t9.getLsbD k, w.y5.getLsbD k⟩
@[ext] private structure InvModBoolB3 where (m21 m22 m24 m36 m38 m39 m42 m43 m48 m49 m51 m57 m60 p0 p16 t10 t13 t2 t22 t23 t27 t3 t4 t6 t8 t9 : Bool)
private def extractInvModBoolW3 (w : Model.InvSubBytesW3) (k : Nat) : InvModBoolB3 := ⟨w.m21.getLsbD k, w.m22.getLsbD k, w.m24.getLsbD k, w.m36.getLsbD k, w.m38.getLsbD k, w.m39.getLsbD k, w.m42.getLsbD k, w.m43.getLsbD k, w.m48.getLsbD k, w.m49.getLsbD k,
    w.m51.getLsbD k, w.m57.getLsbD k, w.m60.getLsbD k, w.p0.getLsbD k, w.p16.getLsbD k, w.t10.getLsbD k, w.t13.getLsbD k, w.t2.getLsbD k, w.t22.getLsbD k, w.t23.getLsbD k,
    w.t27.getLsbD k, w.t3.getLsbD k, w.t4.getLsbD k, w.t6.getLsbD k, w.t8.getLsbD k, w.t9.getLsbD k⟩
@[ext] private structure InvModBoolB4 where (m39 m40 m48 m50 m51 m57 m63 p0 p15 p16 p17 p2 p22 p23 p6 p7 s0 s6 t13 t23 t6 t8 : Bool)
private def extractInvModBoolW4 (w : Model.InvSubBytesW4) (k : Nat) : InvModBoolB4 := ⟨w.m39.getLsbD k, w.m40.getLsbD k, w.m48.getLsbD k, w.m50.getLsbD k, w.m51.getLsbD k, w.m57.getLsbD k, w.m63.getLsbD k, w.p0.getLsbD k, w.p15.getLsbD k, w.p16.getLsbD k,
    w.p17.getLsbD k, w.p2.getLsbD k, w.p22.getLsbD k, w.p23.getLsbD k, w.p6.getLsbD k, w.p7.getLsbD k, w.s0.getLsbD k, w.s6.getLsbD k, w.t13.getLsbD k, w.t23.getLsbD k,
    w.t6.getLsbD k, w.t8.getLsbD k⟩
@[ext] private structure InvModBoolB5 where (p11 p17 p25 s0 s1 s3 s4 s5 s6 s7 : Bool)
private def extractInvModBoolW5 (w : Model.InvSubBytesW5) (k : Nat) : InvModBoolB5 := ⟨w.p11.getLsbD k, w.p17.getLsbD k, w.p25.getLsbD k, w.s0.getLsbD k, w.s1.getLsbD k, w.s3.getLsbD k, w.s4.getLsbD k, w.s5.getLsbD k, w.s6.getLsbD k, w.s7.getLsbD k⟩
private def InvModBoolStage1 (inp : FsBool8) : InvModBoolB1 :=
  strictBool inp.b0 fun u7 => strictBool inp.b1 fun u6 => strictBool inp.b2 fun u5 => strictBool inp.b3 fun u4 => strictBool inp.b4 fun u3 => strictBool inp.b5 fun u2 => strictBool inp.b6 fun u1 =>
  strictBool inp.b7 fun u0 => strictBool (u0 ^^ u3) fun t23 => strictBool (u1 ^^ t23) fun t8 => strictBool (t23 && t8) fun m2 => strictBool (u4 ^^ t8) fun t4 => strictBool (u1 ^^ u3) fun t22 => strictBool (u0 ^^ u1) fun t2 =>
  strictBool (u3 ^^ u4) fun t1 => strictBool (u7 ^^ t1) fun t9 => strictBool (t22 && t9) fun m7 => strictBool (u4 ^^ u7) fun t24 => strictBool (t2 ^^ t24) fun t10 => strictBool (t2 && t10) fun m14 => strictBool (u6 ^^ u7) fun r5 =>
  strictBool (t1 ^^ r5) fun t3 => strictBool (t2 ^^ r5) fun t13 => strictBool (t22 ^^ r5) fun t19 => strictBool (u2 ^^ t19) fun t17 => strictBool (u2 ^^ t1) fun t25 => strictBool (u1 ^^ u6) fun r13 => strictBool (t24 ^^ r13) fun t20 =>
  strictBool (t20 && t17) fun m9 => strictBool (u2 ^^ u5) fun r17 => strictBool (t22 ^^ r17) fun t6 => strictBool (t13 && t6) fun m1 => strictBool (u0 ^^ r17) fun y5 =>
  ⟨m1, m14, m2, m7, m9, r13, t1, t10, t13, t17, t19, t2, t20, t22, t23, t24, t25, t3, t4, t6, t8, t9, u2, u4, u5, u6, y5⟩
private theorem extract_InvModBoolStage1 (inp : Model.FsState) (k : Nat) : extractInvModBoolW1 (Model.invSubBytesFsStage1 inp) k = InvModBoolStage1 (extractBool8 inp k) := by
  ext1 <;> simp only [extractInvModBoolW1, extractBool8, Model.invSubBytesFsStage1, InvModBoolStage1, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def InvModBoolStage2 (inp : InvModBoolB1) : InvModBoolB2 :=
  strictBool inp.m1 fun m1 => strictBool inp.m14 fun m14 => strictBool inp.m2 fun m2 => strictBool inp.m7 fun m7 => strictBool inp.m9 fun m9 => strictBool inp.r13 fun r13 => strictBool inp.t1 fun t1 =>
  strictBool inp.t10 fun t10 => strictBool inp.t13 fun t13 => strictBool inp.t17 fun t17 => strictBool inp.t19 fun t19 => strictBool inp.t2 fun t2 => strictBool inp.t20 fun t20 => strictBool inp.t22 fun t22 =>
  strictBool inp.t23 fun t23 => strictBool inp.t24 fun t24 => strictBool inp.t25 fun t25 => strictBool inp.t3 fun t3 => strictBool inp.t4 fun t4 => strictBool inp.t6 fun t6 => strictBool inp.t8 fun t8 =>
  strictBool inp.t9 fun t9 => strictBool inp.u2 fun u2 => strictBool inp.u4 fun u4 => strictBool inp.u5 fun u5 => strictBool inp.u6 fun u6 => strictBool inp.y5 fun y5 => strictBool (t19 && y5) fun m4 =>
  strictBool (m4 ^^ m1) fun m5 => strictBool (m5 ^^ t24) fun m17 => strictBool (u5 ^^ u6) fun r18 => strictBool (t1 ^^ r18) fun t27 => strictBool (t10 ^^ t27) fun t15 => strictBool (t1 && t15) fun m11 => strictBool (m14 ^^ m11) fun m15 =>
  strictBool (m17 ^^ m15) fun m21 => strictBool (t4 && t27) fun m12 => strictBool (m12 ^^ m11) fun m13 => strictBool (t10 ^^ r18) fun t14 => strictBool (t14 ^^ m1) fun m3 => strictBool (m3 ^^ m2) fun m16 => strictBool (m16 ^^ m13) fun m20 =>
  strictBool (u2 ^^ u4) fun r19 => strictBool (r13 ^^ r19) fun t16 => strictBool (t3 ^^ t16) fun t26 => strictBool (t3 && t16) fun m6 => strictBool (t26 ^^ m6) fun m8 => strictBool (m8 ^^ m7) fun m18 => strictBool (m18 ^^ m13) fun m22 =>
  strictBool (m22 && m20) fun m25 => strictBool (m21 ^^ m25) fun m26 => strictBool (m9 ^^ m6) fun m10 =>
  ⟨m10, m15, m20, m21, m22, m25, m26, t1, t10, t13, t15, t16, t17, t19, t2, t20, t22, t23, t25, t27, t3, t4, t6, t8, t9, y5⟩
private theorem extract_InvModBoolStage2 (inp : Model.InvSubBytesW1) (k : Nat) : extractInvModBoolW2 (Model.invSubBytesFsStage2 inp) k = InvModBoolStage2 (extractInvModBoolW1 inp k) := by
  ext1 <;> simp only [extractInvModBoolW2, extractInvModBoolW1, Model.invSubBytesFsStage2, InvModBoolStage2, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def InvModBoolStage3 (inp : InvModBoolB2) : InvModBoolB3 :=
  strictBool inp.m10 fun m10 => strictBool inp.m15 fun m15 => strictBool inp.m20 fun m20 => strictBool inp.m21 fun m21 => strictBool inp.m22 fun m22 => strictBool inp.m25 fun m25 => strictBool inp.m26 fun m26 =>
  strictBool inp.t1 fun t1 => strictBool inp.t10 fun t10 => strictBool inp.t13 fun t13 => strictBool inp.t15 fun t15 => strictBool inp.t16 fun t16 => strictBool inp.t17 fun t17 => strictBool inp.t19 fun t19 =>
  strictBool inp.t2 fun t2 => strictBool inp.t20 fun t20 => strictBool inp.t22 fun t22 => strictBool inp.t23 fun t23 => strictBool inp.t25 fun t25 => strictBool inp.t27 fun t27 => strictBool inp.t3 fun t3 =>
  strictBool inp.t4 fun t4 => strictBool inp.t6 fun t6 => strictBool inp.t8 fun t8 => strictBool inp.t9 fun t9 => strictBool inp.y5 fun y5 => strictBool (m10 ^^ m15) fun m19 => strictBool (m19 ^^ t25) fun m23 =>
  strictBool (m23 ^^ m25) fun m28 => strictBool (m22 ^^ m23) fun m24 => strictBool (m26 && m24) fun m30 => strictBool (m23 ^^ m30) fun m39 => strictBool (m39 && y5) fun m48 => strictBool (m39 && t19) fun m57 => strictBool (m24 ^^ m25) fun m36 =>
  strictBool (m20 && m23) fun m31 => strictBool (m20 ^^ m21) fun m27 => strictBool (m27 && m31) fun m32 => strictBool (m28 && m27) fun m29 => strictBool (m21 ^^ m29) fun m37 => strictBool (m37 ^^ m39) fun m42 => strictBool (m42 && t15) fun m52 =>
  strictBool (m42 && t1) fun m61 => strictBool (m52 ^^ m61) fun p0 => strictBool (m57 ^^ m61) fun p16 => strictBool (m37 && t20) fun m60 => strictBool (m37 && t17) fun m51 => strictBool (m27 ^^ m25) fun m33 => strictBool (m32 ^^ m33) fun m38 =>
  strictBool (m37 ^^ m38) fun m43 => strictBool (m43 && t16) fun m49 =>
  ⟨m21, m22, m24, m36, m38, m39, m42, m43, m48, m49, m51, m57, m60, p0, p16, t10, t13, t2, t22, t23, t27, t3, t4, t6, t8, t9⟩
private theorem extract_InvModBoolStage3 (inp : Model.InvSubBytesW2) (k : Nat) : extractInvModBoolW3 (Model.invSubBytesFsStage3 inp) k = InvModBoolStage3 (extractInvModBoolW2 inp k) := by
  ext1 <;> simp only [extractInvModBoolW3, extractInvModBoolW2, Model.invSubBytesFsStage3, InvModBoolStage3, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def InvModBoolStage4 (inp : InvModBoolB3) : InvModBoolB4 :=
  strictBool inp.m21 fun m21 => strictBool inp.m22 fun m22 => strictBool inp.m24 fun m24 => strictBool inp.m36 fun m36 => strictBool inp.m38 fun m38 => strictBool inp.m39 fun m39 => strictBool inp.m42 fun m42 =>
  strictBool inp.m43 fun m43 => strictBool inp.m48 fun m48 => strictBool inp.m49 fun m49 => strictBool inp.m51 fun m51 => strictBool inp.m57 fun m57 => strictBool inp.m60 fun m60 => strictBool inp.p0 fun p0 =>
  strictBool inp.p16 fun p16 => strictBool inp.t10 fun t10 => strictBool inp.t13 fun t13 => strictBool inp.t2 fun t2 => strictBool inp.t22 fun t22 => strictBool inp.t23 fun t23 => strictBool inp.t27 fun t27 =>
  strictBool inp.t3 fun t3 => strictBool inp.t4 fun t4 => strictBool inp.t6 fun t6 => strictBool inp.t8 fun t8 => strictBool inp.t9 fun t9 => strictBool (m49 ^^ m60) fun p6 => strictBool (m49 ^^ m51) fun p13 =>
  strictBool (m43 && t3) fun m58 => strictBool (m38 && t9) fun m50 => strictBool (m38 && t22) fun m59 => strictBool (m58 ^^ m59) fun p1 => strictBool (p0 ^^ p1) fun p7 => strictBool (m21 && m22) fun m34 => strictBool (m24 && m34) fun m35 =>
  strictBool (m35 ^^ m36) fun m40 => strictBool (m38 ^^ m40) fun m41 => strictBool (m42 ^^ m41) fun m45 => strictBool (m45 && t27) fun m53 => strictBool (m50 ^^ m53) fun p8 => strictBool (p7 ^^ p8) fun p23 => strictBool (m45 && t4) fun m62 =>
  strictBool (m49 ^^ m62) fun p14 => strictBool (p14 ^^ p23) fun s6 => strictBool (m41 && t10) fun m54 => strictBool (m54 ^^ m62) fun p2 => strictBool (p2 ^^ p7) fun p22 => strictBool (p13 ^^ p22) fun s0 => strictBool (m58 ^^ p2) fun p17 =>
  strictBool (m54 ^^ m59) fun p15 => strictBool (m41 && t2) fun m63 =>
  ⟨m39, m40, m48, m50, m51, m57, m63, p0, p15, p16, p17, p2, p22, p23, p6, p7, s0, s6, t13, t23, t6, t8⟩
private theorem extract_InvModBoolStage4 (inp : Model.InvSubBytesW3) (k : Nat) : extractInvModBoolW4 (Model.invSubBytesFsStage4 inp) k = InvModBoolStage4 (extractInvModBoolW3 inp k) := by
  ext1 <;> simp only [extractInvModBoolW4, extractInvModBoolW3, Model.invSubBytesFsStage4, InvModBoolStage4, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def InvModBoolStage5 (inp : InvModBoolB4) : InvModBoolB5 :=
  strictBool inp.m39 fun m39 => strictBool inp.m40 fun m40 => strictBool inp.m48 fun m48 => strictBool inp.m50 fun m50 => strictBool inp.m51 fun m51 => strictBool inp.m57 fun m57 => strictBool inp.m63 fun m63 =>
  strictBool inp.p0 fun p0 => strictBool inp.p15 fun p15 => strictBool inp.p16 fun p16 => strictBool inp.p17 fun p17 => strictBool inp.p2 fun p2 => strictBool inp.p22 fun p22 => strictBool inp.p23 fun p23 =>
  strictBool inp.p6 fun p6 => strictBool inp.p7 fun p7 => strictBool inp.s0 fun s0 => strictBool inp.s6 fun s6 => strictBool inp.t13 fun t13 => strictBool inp.t23 fun t23 => strictBool inp.t6 fun t6 =>
  strictBool inp.t8 fun t8 => strictBool (m39 ^^ m40) fun m44 => strictBool (m44 && t6) fun m46 => strictBool (m46 ^^ m51) fun p5 => strictBool (m63 ^^ p5) fun p18 => strictBool (p5 ^^ p7) fun p24 => strictBool (m46 ^^ m48) fun p12 =>
  strictBool (p12 ^^ p22) fun s3 => strictBool (m44 && t13) fun m55 => strictBool (m55 ^^ m63) fun p9 => strictBool (p9 ^^ p16) fun s7 => strictBool (m40 && t8) fun m47 => strictBool (m47 ^^ m50) fun p3 => strictBool (p2 ^^ p3) fun p19 =>
  strictBool (p19 ^^ p24) fun s5 => strictBool (p0 ^^ p3) fun p11 => strictBool (p9 ^^ p11) fun p26 => strictBool (m40 && t23) fun m56 => strictBool (m48 ^^ m56) fun p4 => strictBool (p4 ^^ p6) fun p20 => strictBool (p15 ^^ p20) fun p29 =>
  strictBool (p26 ^^ p29) fun s1 => strictBool (m57 ^^ p4) fun p10 => strictBool (p10 ^^ p18) fun p27 => strictBool (p23 ^^ p27) fun s4 => strictBool (p6 ^^ p10) fun p25 =>
  ⟨p11, p17, p25, s0, s1, s3, s4, s5, s6, s7⟩
private theorem extract_InvModBoolStage5 (inp : Model.InvSubBytesW4) (k : Nat) : extractInvModBoolW5 (Model.invSubBytesFsStage5 inp) k = InvModBoolStage5 (extractInvModBoolW4 inp k) := by
  ext1 <;> simp only [extractInvModBoolW5, extractInvModBoolW4, Model.invSubBytesFsStage5, InvModBoolStage5, strictBool_eq, BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def InvModBoolStage6 (inp : InvModBoolB5) : FsBool8 :=
  strictBool inp.p11 fun p11 => strictBool inp.p17 fun p17 => strictBool inp.p25 fun p25 => strictBool inp.s0 fun s0 => strictBool inp.s1 fun s1 => strictBool inp.s3 fun s3 => strictBool inp.s4 fun s4 =>
  strictBool inp.s5 fun s5 => strictBool inp.s6 fun s6 => strictBool inp.s7 fun s7 => strictBool (p11 ^^ p25) fun p28 => strictBool (p17 ^^ p28) fun s2 =>
  ⟨s7, s6, s5, s4, s3, s2, s1, s0⟩
private theorem extract_InvModBoolStage6 (inp : Model.InvSubBytesW5) (k : Nat) : extractBool8 (Model.invSubBytesFsStage6 inp) k = InvModBoolStage6 (extractInvModBoolW5 inp k) := by
  ext1 <;> simp only [extractBool8, extractInvModBoolW5, Model.invSubBytesFsStage6, InvModBoolStage6, strictBool_eq, BitVec.getLsbD_xor]
private def InvModBoolFull (x : FsBool8) : FsBool8 := InvModBoolStage6 (InvModBoolStage5 (InvModBoolStage4 (InvModBoolStage3 (InvModBoolStage2 (InvModBoolStage1 (x))))))

private theorem invAsmBool_eq_invModBool :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      InvAsmBoolFull ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ =
        InvModBoolFull ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := by
  decide

private theorem invAsmFull_eq_invSubBytesFs (st : Model.FsState) :
    InvAsmFull st = Model.invSubBytesFs st := by
  apply eq_of_extractBool8_eq; intro k hk
  rw [InvAsmFull, extract_InvAsmStage6, extract_InvAsmStage5, extract_InvAsmStage4 _ _ hk,
    extract_InvAsmStage3, extract_InvAsmStage2, extract_InvAsmStage1, Model.invSubBytesFs,
    extract_InvModBoolStage6, extract_InvModBoolStage5, extract_InvModBoolStage4,
    extract_InvModBoolStage3, extract_InvModBoolStage2, extract_InvModBoolStage1]
  cases hx : extractBool8 st k
  exact invAsmBool_eq_invModBool _ _ _ _ _ _ _ _

/-! ## 4. Chunk Decomposition & `SepWP` Proofs -/

private abbrev advanceWords (pc : BitVec 64) (ws : List (BitVec 32)) : BitVec 64 :=
  pc + BitVec.ofNat 64 (4 * ws.length)

private theorem split_decodeWords {P : Program} {pc : BitVec 64}
    {ws : List (BitVec 32)} {rest : List Instr}
    (h : hasInstrs P pc (decodeWords ws ++ rest)) :
    hasInstrs P pc (decodeWords ws) ∧ hasInstrs P (advanceWords pc ws) rest :=
  h.split_append (off := BitVec.ofNat 64 (4 * ws.length)) (by simp [decodeWords])

private structure ChunkKeep (keep2830 : Bool) (s sf : State) : Prop where
  x0 : sf.readReg64 (.gpr 0#5) = s.readReg64 (.gpr 0#5)
  x29 : sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5)
  x28 : keep2830 = true → sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5)
  x30 : keep2830 = true → sf.readReg64 (.gpr 30#5) = s.readReg64 (.gpr 30#5)
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s
  sp : sf.sp = s.sp
  purePres : PureStepPreserved s sf

private theorem ChunkKeep.trans {b : Bool} {s1 s2 s3 : State}
    (h1 : ChunkKeep b s1 s2) (h2 : ChunkKeep b s2 s3) : ChunkKeep b s1 s3 :=
  ⟨h2.x0.trans h1.x0, h2.x29.trans h1.x29,
   fun hb => (h2.x28 hb).trans (h1.x28 hb), fun hb => (h2.x30 hb).trans (h1.x30 hb),
   h2.vregs.trans h1.vregs, h2.sp.trans h1.sp, h1.purePres.trans h2.purePres⟩

private def subChunk1Words : List (BitVec 32) :=
  [0xf81b0ffb#32, 0xa90167fa#32, 0xa9025ff8#32, 0xa90357f6#32, 0xa9044ff4#32, 0xa940ac06#32, 0xf9400c11#32, 0xa942340e#32, 0xf9400008#32, 0xa9430c10#32,
   0xca0b01c9#32, 0xca06006c#32, 0xca0d0205#32, 0xca0e006a#32, 0xca09018d#32, 0xca0b006f#32, 0xca0800a1#32, 0xca1101b2#32, 0xca0e002e#32, 0xca030039#32,
   0xca0b0251#32, 0xca100247#32, 0x8a0801d7#32, 0xca0a00eb#32, 0xca050222#32, 0x8a0d0233#32, 0xca0b0050#32, 0x8a0a0174#32, 0x8a0f0055#32, 0x8a090216#32,
   0xca1402b5#32, 0xca050165#32, 0xca1402d4#32]
private def subChunk2Words : List (BitVec 32) :=
  [0xca0f02f6#32, 0xca060037#32, 0x8a0102f8#32, 0x8a0c00a6#32, 0xca080232#32, 0xca1800b8#32, 0xca080164#32, 0xca0202d6#32, 0xca0300c3#32, 0xca060318#32,
   0xca0f02e6#32, 0xca1302d6#32, 0x8a19009a#32, 0xca1300e7#32, 0x8a060253#32, 0xca1a00ba#32, 0xca0c0318#32, 0xca1300e7#32, 0xca030343#32, 0xca140313#32,
   0xca1400e7#32, 0xca1502d4#32, 0xca150075#32, 0x8a070263#32, 0xca1302b8#32, 0xca1400e7#32, 0xca140076#32]
private def subChunk3Words : List (BitVec 32) :=
  [0x8a1802d6#32, 0xca0302b8#32, 0xca0302c3#32, 0x8a07031a#32, 0x8a15007b#32, 0xca140354#32, 0xca1502d5#32, 0xca180363#32, 0xca130373#32, 0x8a0802a8#32,
   0x8a140078#32, 0x8a040284#32, 0x8a190283#32, 0xca070307#32, 0xca150278#32, 0x8a0d026d#32, 0xca1400f6#32, 0x8a060306#32, 0x8a0e02ae#32, 0x8a0502c5#32,
   0x8a0c02d6#32, 0x8a0100ec#32, 0xca1800e1#32, 0x8a1700e7#32, 0xca0c00b7#32, 0x8a0f002c#32, 0x8a11026f#32]
private def subChunk4Words : List (BitVec 32) :=
  [0x8a120311#32, 0xca150292#32, 0xca0801e8#32, 0x8a020022#32, 0xca0f0231#32, 0xca120021#32, 0xca04010f#32, 0x8a100030#32, 0x8a090029#32, 0x8a0a024a#32,
   0xca0501ef#32, 0xca080048#32, 0xca170210#32, 0xca0a0129#32, 0xca0f00e1#32, 0xca160108#32, 0x8a0b024b#32, 0xca060132#32, 0xca010129#32, 0xca100108#32,
   0xca0b020b#32, 0xca0e024e#32, 0xca0d024d#32, 0xca160130#32, 0xca030112#32, 0xca080128#32, 0xca170231#32, 0xca1201ce#32]
private def subChunk5Words : List (BitVec 32) :=
  [0xa9002010#32, 0xca0a0188#32, 0xca0d0229#32, 0xca0b0108#32, 0xa9444ff4#32, 0xca120108#32, 0xa94357f6#32, 0xa9425ff8#32, 0xca0f012a#32, 0xa94167fa#32,
   0xa9022009#32, 0xca0b0129#32, 0xca0b01a8#32, 0xa901280e#32, 0xa9032009#32, 0xf84507fb#32, 0xd65f03c0#32]

private theorem subBytesInstrs_chunks :
    subBytesInstrs =
      decodeWords subChunk1Words ++
      (decodeWords subChunk2Words ++
      (decodeWords subChunk3Words ++
      (decodeWords subChunk4Words ++ decodeWords subChunk5Words))) := by
  have hw : subBytesWords =
      subChunk1Words ++ (subChunk2Words ++ (subChunk3Words ++ (subChunk4Words ++ subChunk5Words))) := rfl
  simp only [subBytesInstrs, hw, decodeWords, List.map_append]

private def subStackCells (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) : SepProp :=
  ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
  ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗ ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
  ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)

private def subStackSaved (s0 : State) (pad : BitVec 64) : SepProp :=
  subStackCells s0.sp (s0.readReg64 (.gpr 27#5)) pad (s0.readReg64 (.gpr 26#5))
    (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
    (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5))
    (s0.readReg64 (.gpr 19#5))

private theorem stackFrameAt_80 (sp : BitVec 64) :
    stackFrameAt sp 80 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, subStackCells sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont, subStackCells]

section
arm64_proof_prelude

private theorem subBytes_chunk1 {P : Program} {pc target_pc ptr : BitVec 64} {st : Model.FsState}
    {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64}
    (hc : hasInstrs P pc (decodeWords subChunk1Words))
    (hpc : s0.pc = pc) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hsp : s0.spAligned = true)
    (hnext : ∀ s1 : State, s1.pc = advanceWords pc subChunk1Words → s1.status = .Running →
      SubAsmRegs1 s1 (SubAsmStage1 st) → s1.sp = s0.sp - 80#64 →
      s1.readReg64 (.gpr 0#5) = ptr → s1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) →
      s1.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) →
      s1.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → PureStepPreserved s0 s1 →
      SepWP P target_pc s1 (fsStateAt ptr st ∗ subStackSaved s0 w1) post oom) :
    SepWP P target_pc s0
      (fsStateAt ptr st ∗ subStackCells s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) post oom := by
  have hsp0 := sp_and_15_of_spAligned hsp
  have hsp80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hsp0; bv_bits
  have hx0' : s0.readReg64 (.gpr 0#5) = ptr := hx0
  have_instrs hc 0 33
  dsimp only [subStackCells]
  wp_str64 hf_0 m1 hm1
  wp_stp64 hf_1 m2 hm2
  wp_stp64 hf_2 m3 hm3
  wp_stp64 hf_3 m4 hm4
  wp_stp64 hf_4 m5 hm5
  dsimp only [fsStateAt]
  wp_steps 28
  change SepWP P target_pc _ (fsStateAt ptr st ∗ subStackSaved s0 w1) post oom
  refine hnext _ (by simp [advanceWords, subChunk1Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hx0'])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hm5, hm4, hm3, hm2, hm1]))
  simp only [SubAsmRegs1, SubAsmStage1, wp_norm, arm64_norm]

private theorem subBytes_chunk2 {P : Program} {pc target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : SubAsmW1}
    (hc : hasInstrs P pc (decodeWords subChunk2Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hregs : SubAsmRegs1 s w)
    (hnext : ∀ sf : State, sf.pc = advanceWords pc subChunk2Words → sf.status = .Running →
      SubAsmRegs2 sf (SubAsmStage2 w) → ChunkKeep true s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hregs with ⟨hx1, hx2, hx3, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx19, hx20, hx21, hx23, hx25⟩
  have_instrs hc 0 27; wp_steps 27
  refine hnext _ (by simp [advanceWords, subChunk2Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [SubAsmRegs2, SubAsmStage2, wp_norm, arm64_norm, *]
  · refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      fun _ => by simp [wp_norm, arm64_norm], fun _ => by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem subBytes_chunk3 {P : Program} {pc target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : SubAsmW2}
    (hc : hasInstrs P pc (decodeWords subChunk3Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hregs : SubAsmRegs2 s w)
    (hnext : ∀ sf : State, sf.pc = advanceWords pc subChunk3Words → sf.status = .Running →
      SubAsmRegs3 sf (SubAsmStage3 w) → ChunkKeep true s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hregs with ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25⟩
  have_instrs hc 0 27; wp_steps 27
  refine hnext _ (by simp [advanceWords, subChunk3Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [SubAsmRegs3, SubAsmStage3, wp_norm, arm64_norm, *]
  · refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      fun _ => by simp [wp_norm, arm64_norm], fun _ => by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem subBytes_chunk4 {P : Program} {pc target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : SubAsmW3}
    (hc : hasInstrs P pc (decodeWords subChunk4Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hregs : SubAsmRegs3 s w)
    (hnext : ∀ sf : State, sf.pc = advanceWords pc subChunk4Words → sf.status = .Running →
      SubAsmRegs4 sf (SubAsmStage4 w) → ChunkKeep true s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hregs with ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx18, hx20, hx21, hx22, hx23, hx24⟩
  have_instrs hc 0 28; wp_steps 28
  refine hnext _ (by simp [advanceWords, subChunk4Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [SubAsmRegs4, SubAsmStage4, wp_norm, arm64_norm, *]
  · refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      fun _ => by simp [wp_norm, arm64_norm], fun _ => by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem subBytes_chunk5 {P : Program} {pc ptr : BitVec 64} {st : Model.FsState}
    {s0 s4 : State} {R : SepProp} {w : SubAsmW4} {pad : BitVec 64}
    (hc : hasInstrs P pc (decodeWords subChunk5Words))
    (hpc : s4.pc = pc) (hrun : s4.status = .Running) (hregs : SubAsmRegs4 s4 w)
    (hsp_eq : s4.sp = s0.sp - 80#64) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx0 : s4.readReg64 (.gpr 0#5) = ptr)
    (hx28 : s4.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5))
    (hx29 : s4.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5))
    (hx30 : s4.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5))
    (hvregs : calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hpres : PureStepPreserved s0 s4)
    (hw_eq : SubAsmStage5 w = Model.subBytesFs st) :
    SepWP P (s0.readReg64 Reg.lr) s4 (fsStateAt ptr st ∗ subStackSaved s0 pad)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ subBytesSpec.post (ptr, st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  rcases hregs with ⟨hx8, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18⟩
  have hsp4_al : s4.spAligned = true := by
    simp only [State.spAligned, hsp_eq]; revert hsp0; bv_bits
  have hsp4_reg : s4.readReg64 .sp = s0.sp - 80#64 := hsp_eq
  have_instrs hc 0 17
  dsimp only [fsStateAt, subStackSaved, subStackCells]
  wp_stp64 hf_0 m1 hm1; wp_steps 9; wp_stp64 hf_10 m2 hm2; wp_steps 2
  wp_stp64 hf_13 m3 hm3; wp_stp64 hf_14 m4 hm4; wp_steps 2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm, *], ?_⟩
  · dsimp only [subBytesSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpres.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1])), Satisfies.mono (sepConj_mono_left ?_) hm⟩
    refine Entails.trans (Q := fsStateAt ptr (SubAsmStage5 w) ∗ subStackSaved s0 pad)
      (Entails.of_eq_explicit (by dsimp only [fsStateAt, SubAsmStage5, subStackSaved, subStackCells])) ?_
    rw [hw_eq, stackFrameAt_80]
    refine sepConj_mono_right ?_
    exact Entails.sepExists_right (s0.readReg64 (.gpr 27#5)) <| Entails.sepExists_right pad <|
      Entails.sepExists_right (s0.readReg64 (.gpr 26#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) <| Entails.refl _
  · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, *]

/-- Placement-generic `subroutine_ok` verification of `fixslice64::sub_bytes`. -/
theorem subBytes_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry subBytesInstrs) :
    subroutine_ok P entry subBytesSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [subBytesSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hx0, hpre⟩
  refine ⟨fsStateAt ptr st ∗ stackFrameAt s0.sp 80, hpre, ?_⟩
  rw [subBytesInstrs_chunks] at hc
  obtain ⟨hc1, hc⟩ := split_decodeWords hc; obtain ⟨hc2, hc⟩ := split_decodeWords hc
  obtain ⟨hc3, hc⟩ := split_decodeWords hc; obtain ⟨hc4, hc5⟩ := split_decodeWords hc
  wp_conv_pre => rw [stackFrameAt_80]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
  refine subBytes_chunk1 hc1 hpc hrun hx0 hsp
    fun s1 hpc1 hrun1 hr1 hsp1 hx0_1 hx28_1 hx29_1 hx30_1 hv1 hp1 => ?_
  refine subBytes_chunk2 hc2 hpc1 hrun1 hr1 fun s2 hpc2 hrun2 hr2 hk2 => ?_
  refine subBytes_chunk3 hc3 hpc2 hrun2 hr2 fun s3 hpc3 hrun3 hr3 hk3 => ?_
  refine subBytes_chunk4 hc4 hpc3 hrun3 hr3 fun s4 hpc4 hrun4 hr4 hk4 => ?_
  have hk := hk2.trans (hk3.trans hk4)
  exact subBytes_chunk5 hc5 hpc4 hrun4 hr4 (hk.sp.trans hsp1)
    (sp_and_15_of_spAligned hsp) (hk.x0.trans hx0_1)
    ((hk.x28 rfl).trans hx28_1) (hk.x29.trans hx29_1) ((hk.x30 rfl).trans hx30_1)
    (hk.vregs.trans hv1) (hp1.trans hk.purePres) (subAsmFull_eq_subBytesFs st)

/-! ## 5. `inv_sub_bytes` Chunk Decomposition & `SepWP` Proof -/

private def invChunk1Words : List (BitVec 32) :=
  [0xf81a0ffe#32, 0xa9016ffc#32, 0xa90267fa#32, 0xa9035ff8#32, 0xa90457f6#32, 0xa9054ff4#32, 0xa941a414#32, 0xf9400807#32, 0xa9431410#32, 0xf9401404#32,
   0xa940040b#32, 0xca140123#32, 0xca09020e#32, 0xca1000aa#32, 0xca0900a8#32, 0xca0b0295#32, 0xca0b0032#32, 0xca0100f3#32, 0xca070087#32, 0xca15014c#32,
   0xca1201c6#32, 0xca010219#32, 0xca130061#32, 0xca0700a5#32, 0xca100109#32, 0xca0b006f#32, 0xca12014b#32, 0xca0701d0#32, 0xca010187#32]
private def invChunk2Words : List (BitVec 32) :=
  [0x8a0500dc#32, 0xca14012d#32, 0x8a10017b#32, 0x8a0300fe#32, 0xca150387#32, 0xca140094#32, 0xca120071#32, 0xca150322#32, 0xca1b00f5#32, 0x8a0101bc#32,
   0xca190287#32, 0x8a080136#32, 0xca0400d2#32, 0xca1e0394#32, 0xca0c0279#32, 0x8a1100fc#32, 0x8a0f01d7#32, 0x8a02025a#32, 0xca160336#32, 0xaa1100f9#32,
   0xca03039c#32, 0x8a0a0198#32, 0xca1b02d6#32]
private def invChunk3Words : List (BitVec 32) :=
  [0xca170337#32, 0xca1a0399#32, 0xca1803d8#32, 0xca1402d6#32, 0xca1402f4#32, 0xca040324#32, 0xca1802b5#32, 0x8a1402d7#32, 0xca180098#32, 0xca1502e4#32,
   0xca1502db#32, 0xca180299#32, 0xca1802fa#32, 0x8a1402b4#32, 0x8a190084#32, 0xca18009c#32, 0x8a1b0344#32, 0xca15009a#32, 0x8a060384#32, 0x8a1802c6#32,
   0xca1c0356#32, 0x8a1b00c6#32, 0x8a120352#32]
private def invChunk4Words : List (BitVec 32) :=
  [0x8a0302d8#32, 0xca130183#32, 0xca1b02f3#32, 0xca060266#32, 0x8a340333#32, 0xca040315#32, 0xca060358#32, 0xca170273#32, 0x8a020354#32, 0x8a070302#32,
   0xca1300c7#32, 0x8a0302c3#32, 0xca0702d6#32, 0x8a110311#32, 0x8a0e00ce#32, 0x8a0102c1#32, 0x8a0d02cd#32, 0xca130396#32, 0x8a0f00cf#32, 0xca0e0226#32,
   0x8a1002d0#32, 0x8a050385#32, 0xca0300c6#32]
private def invChunk5Words : List (BitVec 32) :=
  [0xca0f0021#32, 0x8a0c00ec#32, 0x8a0a00ea#32, 0xca120207#32, 0x8a0b02cb#32, 0x8a090269#32, 0x8a080268#32, 0xca060021#32, 0xca0201b7#32, 0xca0a00f8#32,
   0xca0a016a#32, 0xca0901e9#32, 0xca0800a8#32, 0xca140054#32, 0xca0c01ad#32, 0xca0102f7#32, 0xca0a02ab#32, 0xca07012f#32, 0xca030129#32, 0xca040103#32,
   0xca0601a6#32, 0xca140129#32]
private def invChunk6Words : List (BitVec 32) :=
  [0xa9005c0b#32, 0xca0801c8#32, 0xca03030b#32, 0xca03022e#32, 0xca050210#32, 0xca0f00cf#32, 0xca01016b#32, 0xca0c0108#32, 0xca0e012c#32, 0xca060210#32,
   0xa9012c0f#32, 0xca080128#32, 0xca0d0189#32, 0xca12004b#32, 0xca0a0108#32, 0xa9454ff4#32, 0xa9022410#32, 0xa94457f6#32, 0xca060169#32, 0xa9435ff8#32,
   0xa9032408#32, 0xa94267fa#32, 0xa9416ffc#32, 0xf84607fe#32, 0xd65f03c0#32]

private theorem invSubBytesInstrs_chunks :
    invSubBytesInstrs =
      decodeWords invChunk1Words ++
      (decodeWords invChunk2Words ++
      (decodeWords invChunk3Words ++
      (decodeWords invChunk4Words ++
      (decodeWords invChunk5Words ++ decodeWords invChunk6Words)))) := by
  have hw : invSubBytesWords =
      invChunk1Words ++ (invChunk2Words ++ (invChunk3Words ++
      (invChunk4Words ++ (invChunk5Words ++ invChunk6Words)))) := rfl
  simp only [invSubBytesInstrs, hw, decodeWords, List.map_append]

private def invStackCells (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) : SepProp :=
  ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
  ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗ ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
  ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)

private def invStackSaved (s0 : State) (pad : BitVec 64) : SepProp :=
  invStackCells s0.sp (s0.readReg64 (.gpr 30#5)) pad (s0.readReg64 (.gpr 28#5))
    (s0.readReg64 (.gpr 27#5)) (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
    (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5)) (s0.readReg64 (.gpr 22#5))
    (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))

private theorem stackFrameAt_96 (sp : BitVec 64) :
    stackFrameAt sp 96 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        invStackCells sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont, invStackCells]

private theorem invSubBytes_chunk1 {P : Program} {pc target_pc ptr : BitVec 64} {st : Model.FsState}
    {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    (hc : hasInstrs P pc (decodeWords invChunk1Words))
    (hpc : s0.pc = pc) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hsp : s0.spAligned = true)
    (hnext : ∀ s1 : State, s1.pc = advanceWords pc invChunk1Words → s1.status = .Running →
      InvAsmRegs1 s1 (InvAsmStage1 st) → s1.sp = s0.sp - 96#64 →
      s1.readReg64 (.gpr 0#5) = ptr → s1.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → PureStepPreserved s0 s1 →
      SepWP P target_pc s1 (fsStateAt ptr st ∗ invStackSaved s0 w1) post oom) :
    SepWP P target_pc s0
      (fsStateAt ptr st ∗ invStackCells s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11) post oom := by
  have hsp0 := sp_and_15_of_spAligned hsp
  have hsp96 : (s0.sp - 96#64) &&& 15#64 = 0#64 := by revert hsp0; bv_bits
  have hx0' : s0.readReg64 (.gpr 0#5) = ptr := hx0
  have_instrs hc 0 29
  dsimp only [invStackCells]
  wp_str64 hf_0 m1 hm1; wp_stp64 hf_1 m2 hm2; wp_stp64 hf_2 m3 hm3
  wp_stp64 hf_3 m4 hm4; wp_stp64 hf_4 m5 hm5; wp_stp64 hf_5 m6 hm6
  dsimp only [fsStateAt]
  wp_steps 23
  change SepWP P target_pc _ (fsStateAt ptr st ∗ invStackSaved s0 w1) post oom
  refine hnext _ (by simp [advanceWords, invChunk1Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hx0'])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hm6, hm5, hm4, hm3, hm2, hm1]))
  simp only [InvAsmRegs1, InvAsmStage1, wp_norm, arm64_norm]

private theorem invSubBytes_chunk2 {P : Program} {pc target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : InvAsmW1}
    (hc : hasInstrs P pc (decodeWords invChunk2Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hregs : InvAsmRegs1 s w)
    (hnext : ∀ sf : State, sf.pc = advanceWords pc invChunk2Words → sf.status = .Running →
      InvAsmRegs2 sf (InvAsmStage2 w) → ChunkKeep false s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hregs with ⟨hx1, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx14, hx15, hx16, hx18, hx19, hx20, hx21, hx25⟩
  have_instrs hc 0 23; wp_steps 23
  refine hnext _ (by simp [advanceWords, invChunk2Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [InvAsmRegs2, InvAsmStage2, wp_norm, arm64_norm, *]
  · refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by rintro ⟨⟩, by rintro ⟨⟩,
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem invSubBytes_chunk3 {P : Program} {pc target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : InvAsmW2}
    (hc : hasInstrs P pc (decodeWords invChunk3Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hregs : InvAsmRegs2 s w)
    (hnext : ∀ sf : State, sf.pc = advanceWords pc invChunk3Words → sf.status = .Running →
      InvAsmRegs3 sf (InvAsmStage3 w) → ChunkKeep false s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hregs with ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx28, hx30⟩
  have_instrs hc 0 23; wp_steps 23
  refine hnext _ (by simp [advanceWords, invChunk3Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [InvAsmRegs3, InvAsmStage3, wp_norm, arm64_norm, *]
  · refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by rintro ⟨⟩, by rintro ⟨⟩,
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem invSubBytes_chunk4 {P : Program} {pc target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : InvAsmW3}
    (hc : hasInstrs P pc (decodeWords invChunk4Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hregs : InvAsmRegs3 s w)
    (hnext : ∀ sf : State, sf.pc = advanceWords pc invChunk4Words → sf.status = .Running →
      InvAsmRegs4 sf (InvAsmStage4 w) → ChunkKeep false s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hregs with ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx22, hx23, hx25, hx26, hx27, hx28⟩
  have_instrs hc 0 23; wp_steps 23
  refine hnext _ (by simp [advanceWords, invChunk4Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [InvAsmRegs4, InvAsmStage4, wp_norm, arm64_norm, *]
  · refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by rintro ⟨⟩, by rintro ⟨⟩,
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem invSubBytes_chunk5 {P : Program} {pc target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {w : InvAsmW4}
    (hc : hasInstrs P pc (decodeWords invChunk5Words))
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hregs : InvAsmRegs4 s w)
    (hnext : ∀ sf : State, sf.pc = advanceWords pc invChunk5Words → sf.status = .Running →
      InvAsmRegs5 sf (InvAsmStage5 w) → ChunkKeep false s sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hregs with ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22⟩
  have_instrs hc 0 22; wp_steps 22
  refine hnext _ (by simp [advanceWords, invChunk5Words, wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) ?_ ?_
  · simp only [InvAsmRegs5, InvAsmStage5, wp_norm, arm64_norm, *]
  · refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by rintro ⟨⟩, by rintro ⟨⟩,
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩

private theorem invSubBytes_chunk6 {P : Program} {pc ptr : BitVec 64} {st : Model.FsState}
    {s0 s5 : State} {R : SepProp} {w : InvAsmW5} {pad : BitVec 64}
    (hc : hasInstrs P pc (decodeWords invChunk6Words))
    (hpc : s5.pc = pc) (hrun : s5.status = .Running) (hregs : InvAsmRegs5 s5 w)
    (hsp_eq : s5.sp = s0.sp - 96#64) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx0 : s5.readReg64 (.gpr 0#5) = ptr)
    (hx29 : s5.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5))
    (hvregs : calleeSavedVRegs s5 = calleeSavedVRegs s0)
    (hpres : PureStepPreserved s0 s5)
    (hw_eq : InvAsmStage6 w = Model.invSubBytesFs st) :
    SepWP P (s0.readReg64 Reg.lr) s5 (fsStateAt ptr st ∗ invStackSaved s0 pad)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ invSubBytesSpec.post (ptr, st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  rcases hregs with ⟨hx1, hx2, hx3, hx5, hx6, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx23, hx24⟩
  have hsp5_al : s5.spAligned = true := by
    simp only [State.spAligned, hsp_eq]; revert hsp0; bv_bits
  have hsp5_reg : s5.readReg64 .sp = s0.sp - 96#64 := hsp_eq
  have_instrs hc 0 25
  dsimp only [fsStateAt, invStackSaved, invStackCells]
  wp_stp64 hf_0 m1 hm1; wp_steps 9; wp_stp64 hf_10 m2 hm2; wp_steps 5
  wp_stp64 hf_16 m3 hm3; wp_steps 3; wp_stp64 hf_20 m4 hm4; wp_steps 4
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm, *], ?_⟩
  · dsimp only [invSubBytesSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpres.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1])), Satisfies.mono (sepConj_mono_left ?_) hm⟩
    refine Entails.trans (Q := fsStateAt ptr (InvAsmStage6 w) ∗ invStackSaved s0 pad)
      (Entails.of_eq_explicit (by dsimp only [fsStateAt, InvAsmStage6, invStackSaved, invStackCells])) ?_
    rw [hw_eq, stackFrameAt_96]
    refine sepConj_mono_right ?_
    exact Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <| Entails.sepExists_right pad <|
      Entails.sepExists_right (s0.readReg64 (.gpr 28#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 27#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 26#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) <| Entails.refl _
  · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, *]

/-- Placement-generic `subroutine_ok` verification of `fixslice64::inv_sub_bytes`. -/
theorem invSubBytes_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry invSubBytesInstrs) :
    subroutine_ok P entry invSubBytesSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [invSubBytesSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hx0, hpre⟩
  refine ⟨fsStateAt ptr st ∗ stackFrameAt s0.sp 96, hpre, ?_⟩
  rw [invSubBytesInstrs_chunks] at hc
  obtain ⟨hc1, hc⟩ := split_decodeWords hc; obtain ⟨hc2, hc⟩ := split_decodeWords hc
  obtain ⟨hc3, hc⟩ := split_decodeWords hc; obtain ⟨hc4, hc⟩ := split_decodeWords hc
  obtain ⟨hc5, hc6⟩ := split_decodeWords hc
  wp_conv_pre => rw [stackFrameAt_96]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
  refine invSubBytes_chunk1 hc1 hpc hrun hx0 hsp
    fun s1 hpc1 hrun1 hr1 hsp1 hx0_1 hx29_1 hv1 hp1 => ?_
  refine invSubBytes_chunk2 hc2 hpc1 hrun1 hr1 fun s2 hpc2 hrun2 hr2 hk2 => ?_
  refine invSubBytes_chunk3 hc3 hpc2 hrun2 hr2 fun s3 hpc3 hrun3 hr3 hk3 => ?_
  refine invSubBytes_chunk4 hc4 hpc3 hrun3 hr3 fun s4 hpc4 hrun4 hr4 hk4 => ?_
  refine invSubBytes_chunk5 hc5 hpc4 hrun4 hr4 fun s5 hpc5 hrun5 hr5 hk5 => ?_
  have hk := hk2.trans (hk3.trans (hk4.trans hk5))
  exact invSubBytes_chunk6 hc6 hpc5 hrun5 hr5 (hk.sp.trans hsp1)
    (sp_and_15_of_spAligned hsp) (hk.x0.trans hx0_1)
    (hk.x29.trans hx29_1) (hk.vregs.trans hv1) (hp1.trans hk.purePres)
    (invAsmFull_eq_invSubBytesFs st)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode

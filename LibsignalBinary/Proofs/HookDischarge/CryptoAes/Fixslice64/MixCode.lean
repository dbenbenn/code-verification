/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.BV.Bits
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Fixslice64 `MixColumns` & `InvMixColumns` Code Verification (`Fixslice64.MixCode`)

`subroutine_ok` contracts for the 5 standalone compiled `MixColumns` / `InvMixColumns` functions in
`libaes` (`aes::soft::fixslice64`):
- `mixColumns1_ok` (`120` insns, `32` B stack) → `Model.mixColumns1`
- `mixColumns3_ok` (`120` insns, `32` B stack) → `Model.mixColumns3`
- `invMixColumns1_ok` (`139` insns, `16` B stack) → `Model.invMixColumns1`
- `invMixColumns2_ok` (`99` insns, `16` B stack) → `Model.invMixColumns2`
- `invMixColumns3_ok` (`139` insns, `16` B stack) → `Model.invMixColumns3`
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj fsStateAt step_str64_perm step_stp64_perm)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (ror64 rorDistance rotateRows2 rotateRowsAndColumns11 rotateRowsAndColumns12
   rotateRowsAndColumns13 rotateRowsAndColumns22 mixColumnsGen mixColumns1 mixColumns3
   invMixColumnsGen invMixColumns1 invMixColumns2 invMixColumns3)

/-! ## 1. `mix_columns_1` Words, Instructions & Spec -/

@[expose] def mixColumns1Words : List (BitVec 32) :=
  [0xa9be57f6#32, 0xa9014ff4#32, 0xa940400a#32, 0xa9412c0f#32, 0xa942340c#32, 0x93ca5149#32,
   0x93ca114e#32, 0x93d05212#32, 0x93d01201#32, 0x93cf51e2#32, 0x93cf11e4#32, 0x9200ad29#32,
   0x92048dce#32, 0x9200ae52#32, 0x92048c21#32, 0x9200ac45#32, 0xaa0e0123#32, 0x92048c89#32,
   0x93cb516e#32, 0xaa010242#32, 0xaa0900b2#32, 0x93cb1169#32, 0x93cc5184#32, 0xa9434408#32,
   0x93cc1185#32, 0x9200adce#32, 0x92048d29#32, 0x93cd51a6#32, 0x93cd11a7#32, 0xaa0901c1#32,
   0x9200ac89#32, 0x92048cae#32, 0xca0a0073#32, 0x93c81105#32, 0xaa0e012e#32, 0x9200acc9#32,
   0x92048ce4#32, 0x93d15226#32, 0x93d11227#32, 0xaa040129#32, 0x93c85104#32, 0x93d3a274#32,
   0x92048ca5#32, 0x9200acca#32, 0x92048ce6#32, 0x93d36267#32, 0xaa06014a#32, 0xca100046#32,
   0x9200ac84#32, 0x93c6a0d5#32, 0x93c660d6#32, 0x92009e94#32, 0x92089ce7#32, 0xca110151#32,
   0xaa050090#32, 0xaa070284#32, 0xca110063#32, 0x92009ea5#32, 0x92089ec7#32, 0xca0f024f#32,
   0xca020262#32, 0xca030083#32, 0xaa0700a4#32, 0x93cfa1e5#32, 0x93cf61e7#32, 0xca0b0033#32,
   0xca0d012b#32, 0xca11004d#32, 0x92009ca2#32, 0xca1200d2#32, 0xca0401ad#32, 0x92089ce5#32,
   0x93d36264#32, 0xa9003403#32, 0x93d3a263#32, 0xaa050042#32, 0xca0c01cc#32, 0xca02024d#32,
   0x92089c82#32, 0x92009c72#32, 0xca0101ef#32, 0x93cca181#32, 0xaa020252#32, 0xca1101ef#32,
   0xca080208#32, 0xca1201ef#32, 0x93cc6192#32, 0xca0e026e#32, 0xa9013c0d#32, 0x92009c2d#32,
   0x93cba16f#32, 0x93cb6161#32, 0x92089e52#32, 0xca1101ce#32, 0xaa1201ad#32, 0x92009def#32,
   0x93c86102#32, 0x92089c32#32, 0x93c8a101#32, 0xca0d01cd#32, 0xaa1201ee#32, 0xca090189#32,
   0x93d1a22f#32, 0x93d16231#32, 0xca0e0129#32, 0x92009c2c#32, 0x92089c4e#32, 0xa902240d#32,
   0xca10016b#32, 0xaa0e0189#32, 0x92009dec#32, 0x92089e2d#32, 0xca090169#32, 0xaa0d018b#32,
   0xca0a0108#32, 0xa9414ff4#32, 0xca0b0108#32, 0xa9032009#32, 0xa8c257f6#32, 0xd65f03c0#32]

@[expose] def mixColumns1Instrs : List Instr := decodeWords mixColumns1Words

theorem mixColumns1Instrs_template_eq :
    mixColumns1Words.map Arm64.decode = mixColumns1Instrs.map some := by decide

@[expose] def mixColumns1Spec : Spec (BitVec 64 × Model.FsState) where
  pre := fun (ptr, st) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 32)
  post := fun (ptr, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (Model.mixColumns1 st) ∗ stackFrameAt s0.sp 32)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 2. `mix_columns_3` Words, Instructions & Spec -/

@[expose] def mixColumns3Words : List (BitVec 32) :=
  [0xa9be57f6#32, 0xa9014ff4#32, 0xa940400a#32, 0xa9412c0f#32, 0xa942340c#32, 0x93ca7149#32,
   0x93ca314e#32, 0x93d07212#32, 0x93d03201#32, 0x93cf71e2#32, 0x93cf31e4#32, 0x92008d29#32,
   0x920cadce#32, 0x92008e52#32, 0x920cac21#32, 0x92008c45#32, 0xaa0e0123#32, 0x920cac89#32,
   0x93cb716e#32, 0xaa010242#32, 0xaa0900b2#32, 0x93cb3169#32, 0x93cc7184#32, 0xa9434408#32,
   0x93cc3185#32, 0x92008dce#32, 0x920cad29#32, 0x93cd71a6#32, 0x93cd31a7#32, 0xaa0901c1#32,
   0x92008c89#32, 0x920cacae#32, 0xca0a0073#32, 0x93c83105#32, 0xaa0e012e#32, 0x92008cc9#32,
   0x920cace4#32, 0x93d17226#32, 0x93d13227#32, 0xaa040129#32, 0x93c87104#32, 0x93d3a274#32,
   0x920caca5#32, 0x92008cca#32, 0x920cace6#32, 0x93d36267#32, 0xaa06014a#32, 0xca100046#32,
   0x92008c84#32, 0x93c6a0d5#32, 0x93c660d6#32, 0x92009e94#32, 0x92089ce7#32, 0xca110151#32,
   0xaa050090#32, 0xaa070284#32, 0xca110063#32, 0x92009ea5#32, 0x92089ec7#32, 0xca0f024f#32,
   0xca020262#32, 0xca030083#32, 0xaa0700a4#32, 0x93cfa1e5#32, 0x93cf61e7#32, 0xca0b0033#32,
   0xca0d012b#32, 0xca11004d#32, 0x92009ca2#32, 0xca1200d2#32, 0xca0401ad#32, 0x92089ce5#32,
   0x93d36264#32, 0xa9003403#32, 0x93d3a263#32, 0xaa050042#32, 0xca0c01cc#32, 0xca02024d#32,
   0x92089c82#32, 0x92009c72#32, 0xca0101ef#32, 0x93cca181#32, 0xaa020252#32, 0xca1101ef#32,
   0xca080208#32, 0xca1201ef#32, 0x93cc6192#32, 0xca0e026e#32, 0xa9013c0d#32, 0x92009c2d#32,
   0x93cba16f#32, 0x93cb6161#32, 0x92089e52#32, 0xca1101ce#32, 0xaa1201ad#32, 0x92009def#32,
   0x93c86102#32, 0x92089c32#32, 0x93c8a101#32, 0xca0d01cd#32, 0xaa1201ee#32, 0xca090189#32,
   0x93d1a22f#32, 0x93d16231#32, 0xca0e0129#32, 0x92009c2c#32, 0x92089c4e#32, 0xa902240d#32,
   0xca10016b#32, 0xaa0e0189#32, 0x92009dec#32, 0x92089e2d#32, 0xca090169#32, 0xaa0d018b#32,
   0xca0a0108#32, 0xa9414ff4#32, 0xca0b0108#32, 0xa9032009#32, 0xa8c257f6#32, 0xd65f03c0#32]

@[expose] def mixColumns3Instrs : List Instr := decodeWords mixColumns3Words

theorem mixColumns3Instrs_template_eq :
    mixColumns3Words.map Arm64.decode = mixColumns3Instrs.map some := by decide

@[expose] def mixColumns3Spec : Spec (BitVec 64 × Model.FsState) where
  pre := fun (ptr, st) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 32)
  post := fun (ptr, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (Model.mixColumns3 st) ∗ stackFrameAt s0.sp 32)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 3. `inv_mix_columns_1` Words, Instructions & Spec -/

@[expose] def invMixColumns1Words : List (BitVec 32) :=
  [0xa9bf4ff4#32, 0xa940240b#32, 0xa941300d#32, 0xa9423c0a#32, 0x93cb516e#32, 0x93cb1171#32,
   0x93c95132#32, 0x93c91121#32, 0x93cd11a3#32, 0x93cd51a2#32, 0x9200adce#32, 0x92048e31#32,
   0x9200ae52#32, 0x92048c21#32, 0xaa1101ce#32, 0x92048c71#32, 0x93cc5183#32, 0xa9434008#32,
   0x9200ac42#32, 0xaa010252#32, 0x93cc1181#32, 0xaa110051#32, 0x9200ac62#32, 0x93ca5143#32,
   0x93ca1144#32, 0x93cf51e5#32, 0x93cf11e6#32, 0x92048c21#32, 0x93c81107#32, 0x93d05213#32,
   0xaa010041#32, 0x9200ac62#32, 0x92048c83#32, 0x9200aca4#32, 0x92048cc5#32, 0x93c85106#32,
   0x93d01214#32, 0xaa030042#32, 0xaa050083#32, 0x9200acc4#32, 0x92048ce5#32, 0x9200ae66#32,
   0x92048e87#32, 0xaa050084#32, 0xca090252#32, 0xaa0700c5#32, 0xca0b01c6#32, 0xca0d0227#32,
   0xca0f0063#32, 0xca080091#32, 0xca0a0042#32, 0xca1000ae#32, 0xca0900c4#32, 0xca080069#32,
   0xca100228#32, 0xca0d0250#32, 0xca0f004d#32, 0xca09010f#32, 0xca060125#32, 0xca020202#32,
   0xca1201f2#32, 0xca0201ef#32, 0x93c5a0a2#32, 0x93c560a6#32, 0xca0c0021#32, 0xca0b01cb#32,
   0xca0c00ec#32, 0xca070107#32, 0x92009c42#32, 0x92089cc6#32, 0xca0b00e7#32, 0xca0b00ab#32,
   0xaa060042#32, 0x93d2a245#32, 0x93d26246#32, 0xca0a002a#32, 0xca0e0084#32, 0xca010121#32,
   0x92009ca5#32, 0x92089cc6#32, 0xca040021#32, 0xaa0600a5#32, 0x93c7a0e6#32, 0xca040252#32,
   0x93c760e4#32, 0xca02016b#32, 0xca050252#32, 0x92009cc2#32, 0x93c1a025#32, 0x93c16026#32,
   0x92089c84#32, 0xca0e018c#32, 0xca030103#32, 0xaa040042#32, 0x92009ca4#32, 0x92089cc5#32,
   0xca0c0063#32, 0xca070210#32, 0xaa050084#32, 0xca01018c#32, 0xa900480b#32, 0xca02020b#32,
   0xca04018c#32, 0x93cf61f0#32, 0xca0e014a#32, 0xa901300b#32, 0x93cfa1eb#32, 0x93c3a06c#32,
   0x93c36072#32, 0xca110151#32, 0x92089e10#32, 0x92009d6b#32, 0xca0a01ea#32, 0x92009d8c#32,
   0xaa10016b#32, 0x92089e4f#32, 0x93d1a230#32, 0xca0d01ce#32, 0x93d16232#32, 0xca0b014a#32,
   0xaa0f018b#32, 0xca0301ac#32, 0x93cea1cf#32, 0xca0b018b#32, 0x92009e0c#32, 0x93ce61d0#32,
   0x92089e4d#32, 0xa9022c0a#32, 0xca110129#32, 0xaa0d018a#32, 0x92009deb#32, 0x92089e0c#32,
   0xca0a0129#32, 0xaa0c016a#32, 0xca0e0108#32, 0xca0a0108#32, 0xa9032009#32, 0xa8c14ff4#32,
   0xd65f03c0#32]

@[expose] def invMixColumns1Instrs : List Instr := decodeWords invMixColumns1Words

theorem invMixColumns1Instrs_template_eq :
    invMixColumns1Words.map Arm64.decode = invMixColumns1Instrs.map some := by decide

@[expose] def invMixColumns1Spec : Spec (BitVec 64 × Model.FsState) where
  pre := fun (ptr, st) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 16)
  post := fun (ptr, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (Model.invMixColumns1 st) ∗ stackFrameAt s0.sp 16)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 4. `inv_mix_columns_2` Words, Instructions & Spec -/

@[expose] def invMixColumns2Words : List (BitVec 32) :=
  [0xf81f0ff3#32, 0xa940340b#32, 0xa9413009#32, 0xa942200a#32, 0x93cb6170#32, 0x93cb2171#32,
   0x93cd61b2#32, 0x93cd21a1#32, 0xa9433c0e#32, 0x92009e10#32, 0x92089e31#32, 0x92009e52#32,
   0x92089c21#32, 0x93c96122#32, 0x93c92123#32, 0xaa110210#32, 0xaa010251#32, 0x93cc6192#32,
   0x93cc2181#32, 0x93ca6144#32, 0x93ca2145#32, 0x92009c42#32, 0x92089c63#32, 0x92009e52#32,
   0x92089c21#32, 0x92009c84#32, 0x92089ca5#32, 0xaa030042#32, 0xaa010252#32, 0xaa050081#32,
   0x93c86103#32, 0x93c82104#32, 0x93ce61c5#32, 0x93ce21c6#32, 0x93cf61e7#32, 0x93cf21f3#32,
   0x92009c63#32, 0x92089c84#32, 0x92009ca5#32, 0x92089cc6#32, 0x92009ce7#32, 0x92089e73#32,
   0xaa040063#32, 0xaa0600a4#32, 0xaa1300e5#32, 0xca080063#32, 0xca0e0084#32, 0xca0f00a5#32,
   0xca0e006e#32, 0xca0f008f#32, 0xca0b0210#32, 0xca0d0231#32, 0xca0e01e6#32, 0xca090042#32,
   0xca0c0252#32, 0xca0d020d#32, 0xca090229#32, 0xca1001d0#32, 0xca1100d1#32, 0xca0a0021#32,
   0xca0b00ab#32, 0xca0501ad#32, 0xca0c004c#32, 0xca0a024a#32, 0xca0201e2#32, 0xca1201d2#32,
   0xcad08210#32, 0xcad18231#32, 0xca05018c#32, 0xca080028#32, 0xca0b0042#32, 0xca0d0252#32,
   0xca010121#32, 0xca0301e3#32, 0xca0b020b#32, 0xca0100c1#32, 0xca0c0063#32, 0xcac28129#32,
   0xca0d022d#32, 0xcad2818c#32, 0xca05014a#32, 0xa900340b#32, 0xcac1802b#32, 0xca040144#32,
   0xca0800a5#32, 0xca020129#32, 0xca12018c#32, 0xcac38108#32, 0xa9013009#32, 0xca0a0169#32,
   0xcac481ca#32, 0xcac581eb#32, 0xca030108#32, 0xa9022009#32, 0xca040148#32, 0xca050169#32,
   0xa9032408#32, 0xf84107f3#32, 0xd65f03c0#32]

@[expose] def invMixColumns2Instrs : List Instr := decodeWords invMixColumns2Words

theorem invMixColumns2Instrs_template_eq :
    invMixColumns2Words.map Arm64.decode = invMixColumns2Instrs.map some := by decide

@[expose] def invMixColumns2Spec : Spec (BitVec 64 × Model.FsState) where
  pre := fun (ptr, st) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 16)
  post := fun (ptr, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (Model.invMixColumns2 st) ∗ stackFrameAt s0.sp 16)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 5. `inv_mix_columns_3` Words, Instructions & Spec -/

@[expose] def invMixColumns3Words : List (BitVec 32) :=
  [0xa9bf4ff4#32, 0xa940240b#32, 0xa941300d#32, 0xa9423c0a#32, 0x93cb716e#32, 0x93cb3171#32,
   0x93c97132#32, 0x93c93121#32, 0x93cd31a3#32, 0x93cd71a2#32, 0x92008dce#32, 0x920cae31#32,
   0x92008e52#32, 0x920cac21#32, 0xaa1101ce#32, 0x920cac71#32, 0x93cc7183#32, 0xa9434008#32,
   0x92008c42#32, 0xaa010252#32, 0x93cc3181#32, 0xaa110051#32, 0x92008c62#32, 0x93ca7143#32,
   0x93ca3144#32, 0x93cf71e5#32, 0x93cf31e6#32, 0x920cac21#32, 0x93c83107#32, 0x93d07213#32,
   0xaa010041#32, 0x92008c62#32, 0x920cac83#32, 0x92008ca4#32, 0x920cacc5#32, 0x93c87106#32,
   0x93d03214#32, 0xaa030042#32, 0xaa050083#32, 0x92008cc4#32, 0x920cace5#32, 0x92008e66#32,
   0x920cae87#32, 0xaa050084#32, 0xca090252#32, 0xaa0700c5#32, 0xca0b01c6#32, 0xca0d0227#32,
   0xca0f0063#32, 0xca080091#32, 0xca0a0042#32, 0xca1000ae#32, 0xca0900c4#32, 0xca080069#32,
   0xca100228#32, 0xca0d0250#32, 0xca0f004d#32, 0xca09010f#32, 0xca060125#32, 0xca020202#32,
   0xca1201f2#32, 0xca0201ef#32, 0x93c5a0a2#32, 0x93c560a6#32, 0xca0c0021#32, 0xca0b01cb#32,
   0xca0c00ec#32, 0xca070107#32, 0x92009c42#32, 0x92089cc6#32, 0xca0b00e7#32, 0xca0b00ab#32,
   0xaa060042#32, 0x93d2a245#32, 0x93d26246#32, 0xca0a002a#32, 0xca0e0084#32, 0xca010121#32,
   0x92009ca5#32, 0x92089cc6#32, 0xca040021#32, 0xaa0600a5#32, 0x93c7a0e6#32, 0xca040252#32,
   0x93c760e4#32, 0xca02016b#32, 0xca050252#32, 0x92009cc2#32, 0x93c1a025#32, 0x93c16026#32,
   0x92089c84#32, 0xca0e018c#32, 0xca030103#32, 0xaa040042#32, 0x92009ca4#32, 0x92089cc5#32,
   0xca0c0063#32, 0xca070210#32, 0xaa050084#32, 0xca01018c#32, 0xa900480b#32, 0xca02020b#32,
   0xca04018c#32, 0x93cf61f0#32, 0xca0e014a#32, 0xa901300b#32, 0x93cfa1eb#32, 0x93c3a06c#32,
   0x93c36072#32, 0xca110151#32, 0x92089e10#32, 0x92009d6b#32, 0xca0a01ea#32, 0x92009d8c#32,
   0xaa10016b#32, 0x92089e4f#32, 0x93d1a230#32, 0xca0d01ce#32, 0x93d16232#32, 0xca0b014a#32,
   0xaa0f018b#32, 0xca0301ac#32, 0x93cea1cf#32, 0xca0b018b#32, 0x92009e0c#32, 0x93ce61d0#32,
   0x92089e4d#32, 0xa9022c0a#32, 0xca110129#32, 0xaa0d018a#32, 0x92009deb#32, 0x92089e0c#32,
   0xca0a0129#32, 0xaa0c016a#32, 0xca0e0108#32, 0xca0a0108#32, 0xa9032009#32, 0xa8c14ff4#32,
   0xd65f03c0#32]

@[expose] def invMixColumns3Instrs : List Instr := decodeWords invMixColumns3Words

theorem invMixColumns3Instrs_template_eq :
    invMixColumns3Words.map Arm64.decode = invMixColumns3Instrs.map some := by decide

@[expose] def invMixColumns3Spec : Spec (BitVec 64 × Model.FsState) where
  pre := fun (ptr, st) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 16)
  post := fun (ptr, st) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (Model.invMixColumns3 st) ∗ stackFrameAt s0.sp 16)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 6. Rotation Normalization & Shared Stepping Helpers -/

private theorem truncate64_append_self_ushiftRight (x : BitVec 64) {k : Nat} (hk : k < 64) :
    BitVec.truncate 64 ((x ++ x) >>> k) = x.rotateRight k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  dsimp only [BitVec.truncate]
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hk]
  split <;> split <;> first | rfl | omega | exact congrArg x.getLsbD (by omega)

namespace Simp

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem extr64_ror_4 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 4) = x.rotateRight 4 :=
  truncate64_append_self_ushiftRight x (by omega)

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem extr64_ror_8 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 8) = x.rotateRight 8 :=
  truncate64_append_self_ushiftRight x (by omega)

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem extr64_ror_12 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 12) = x.rotateRight 12 :=
  truncate64_append_self_ushiftRight x (by omega)

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem extr64_ror_20 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 20) = x.rotateRight 20 :=
  truncate64_append_self_ushiftRight x (by omega)

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem extr64_ror_24 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 24) = x.rotateRight 24 :=
  truncate64_append_self_ushiftRight x (by omega)

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem extr64_ror_28 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 28) = x.rotateRight 28 :=
  truncate64_append_self_ushiftRight x (by omega)

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem extr64_ror_40 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 40) = x.rotateRight 40 :=
  truncate64_append_self_ushiftRight x (by omega)

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem fold_rot11 (x : BitVec 64) :
    (x.rotateRight 20 &&& 0x0fff0fff0fff0fff#64) |||
    (x.rotateRight 4 &&& 0xf000f000f000f000#64) = rotateRowsAndColumns11 x := rfl

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem fold_rot12 (x : BitVec 64) :
    (x.rotateRight 24 &&& 0x00ff00ff00ff00ff#64) |||
    (x.rotateRight 8 &&& 0xff00ff00ff00ff00#64) = rotateRowsAndColumns12 x := rfl

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem fold_rot13 (x : BitVec 64) :
    (x.rotateRight 28 &&& 0x000f000f000f000f#64) |||
    (x.rotateRight 12 &&& 0xfff0fff0fff0fff0#64) = rotateRowsAndColumns13 x := rfl

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem fold_rot22 (x : BitVec 64) :
    (x.rotateRight 40 &&& 0x00ff00ff00ff00ff#64) |||
    (x.rotateRight 24 &&& 0xff00ff00ff00ff00#64) = rotateRowsAndColumns22 x := rfl

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem fold_rot2 (x : BitVec 64) :
    x.rotateRight 32 = rotateRows2 x := rfl

end Simp

open scoped Simp

private theorem stackFrameAt_32 (sp : BitVec 64) :
    stackFrameAt sp 32 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem stackFrameAt_16 (sp : BitVec 64) :
    stackFrameAt sp 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem sp_sub32_and_15 {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 32#64) &&& 15#64 = 0#64 := by bv_bits

private theorem sp_sub16_and_15 {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 16#64) &&& 15#64 = 0#64 := by bv_bits

private def HighRegsPreserved (s0 sf : State) : Prop :=
  sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  sf.readReg64 Reg.fp = s0.readReg64 Reg.fp ∧
  sf.readReg64 Reg.lr = s0.readReg64 Reg.lr ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
  pureStepProj sf = pureStepProj s0 ∧
  sf.mem.perm = s0.mem.perm

private theorem HighRegsPreserved.trans {s0 s1 s2 : State}
    (h01 : HighRegsPreserved s0 s1) (h12 : HighRegsPreserved s1 s2) :
    HighRegsPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2⟩

private theorem HighRegsPreserved.calleeSaved {s0 sf : State} (h : HighRegsPreserved s0 sf)
    (h19 : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (h20 : sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (h21 : sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (h22 : sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)) :
    CalleeSavedPreserved s0 sf :=
  ⟨h19, h20, h21, h22, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

private theorem HighRegsPreserved.pureStep {s0 sf : State} (h : HighRegsPreserved s0 sf) :
    PureStepPreserved s0 sf :=
  PureStepPreserved.of_proj_perm h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2

private theorem finish_post {s0 s_prev sf : State} {Q P_out R : SepProp}
    (hrel : HighRegsPreserved s0 s_prev) (hstep : HighRegsPreserved s_prev sf)
    (hsp : sf.sp = s0.sp)
    (h19 : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (h20 : sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (h21 : sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (h22 : sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5))
    (hent : Q ⊢ P_out) :
    (sf.mem ⊨ Q ∗ R → sf.mem ⊨ (⌜PureStepPreserved s0 sf⌝ ∗ P_out) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  have hfull := hrel.trans hstep
  refine ⟨fun hm => ?_, hsp, hfull.calleeSaved h19 h20 h21 h22⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfull.pureStep, Satisfies.mono (sepConj_mono_left hent) hm⟩

/-! ## 7. `mixColumns1` & `mixColumns3` Verification -/

private theorem mixColumnsGen_words_eq (rot1 rot2 : BitVec 64 → BitVec 64) (st : Model.FsState) :
    rot2 (rot1 st.s0 ^^^ st.s0) ^^^ (rot1 st.s0 ^^^ (rot1 st.s7 ^^^ st.s7)) =
      (mixColumnsGen rot1 rot2 st).s0 ∧
    (((rot1 st.s0 ^^^ st.s0) ^^^ rot1 st.s1) ^^^ (rot1 st.s7 ^^^ st.s7)) ^^^
      rot2 (rot1 st.s1 ^^^ st.s1) = (mixColumnsGen rot1 rot2 st).s1 ∧
    ((rot1 st.s1 ^^^ st.s1) ^^^ rot1 st.s2) ^^^ rot2 (rot1 st.s2 ^^^ st.s2) =
      (mixColumnsGen rot1 rot2 st).s2 ∧
    (((rot1 st.s2 ^^^ st.s2) ^^^ rot1 st.s3) ^^^ (rot1 st.s7 ^^^ st.s7)) ^^^
      rot2 (rot1 st.s3 ^^^ st.s3) = (mixColumnsGen rot1 rot2 st).s3 ∧
    (((rot1 st.s3 ^^^ st.s3) ^^^ rot1 st.s4) ^^^ (rot1 st.s7 ^^^ st.s7)) ^^^
      rot2 (rot1 st.s4 ^^^ st.s4) = (mixColumnsGen rot1 rot2 st).s4 ∧
    ((rot1 st.s4 ^^^ st.s4) ^^^ rot1 st.s5) ^^^ rot2 (rot1 st.s5 ^^^ st.s5) =
      (mixColumnsGen rot1 rot2 st).s5 ∧
    ((rot1 st.s5 ^^^ st.s5) ^^^ rot1 st.s6) ^^^ rot2 (rot1 st.s6 ^^^ st.s6) =
      (mixColumnsGen rot1 rot2 st).s6 ∧
    ((rot1 st.s6 ^^^ st.s6) ^^^ rot1 st.s7) ^^^ rot2 (rot1 st.s7 ^^^ st.s7) =
      (mixColumnsGen rot1 rot2 st).s7 := by
  dsimp only [mixColumnsGen]
  rw [BitVec.xor_comm (rot1 st.s0) st.s0, BitVec.xor_comm (rot1 st.s1) st.s1,
      BitVec.xor_comm (rot1 st.s2) st.s2, BitVec.xor_comm (rot1 st.s3) st.s3,
      BitVec.xor_comm (rot1 st.s4) st.s4, BitVec.xor_comm (rot1 st.s5) st.s5,
      BitVec.xor_comm (rot1 st.s6) st.s6, BitVec.xor_comm (rot1 st.s7) st.s7]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i hi; simp only [BitVec.getElem_xor]; grind)

private theorem add_220_136 (p : BitVec 64) : p + 220#64 + 136#64 = p + 356#64 := by bv_lin
private theorem add_184_240 (p : BitVec 64) : p + 184#64 + 240#64 = p + 424#64 := by bv_lin

private def mc1HeadWords : List (BitVec 32) := mixColumns1Words.take 55
private def mc3HeadWords : List (BitVec 32) := mixColumns3Words.take 55
private def mc13MidWords : List (BitVec 32) := (mixColumns1Words.drop 55).take 34
private def mc13TailWords : List (BitVec 32) := mixColumns1Words.drop 89

private theorem mixColumns1Instrs_parts {P : Program} {pc0 : BitVec 64}
    (hc : hasInstrs P pc0 mixColumns1Instrs) :
    hasInstrs P pc0 (decodeWords mc1HeadWords) ∧
    hasInstrs P (pc0 + 220#64) (decodeWords mc13MidWords) ∧
    hasInstrs P (pc0 + 356#64) (decodeWords mc13TailWords) := by
  have heq : mixColumns1Instrs =
      (decodeWords mc1HeadWords ++ decodeWords mc13MidWords) ++ decodeWords mc13TailWords := rfl
  rw [heq] at hc
  obtain ⟨hc01, hc2⟩ := hc.split_append (off := 356#64)
  obtain ⟨hc0, hc1⟩ := hc01.split_append (off := 220#64)
  exact ⟨hc0, hc1, hc2⟩

private theorem mixColumns3Instrs_parts {P : Program} {pc0 : BitVec 64}
    (hc : hasInstrs P pc0 mixColumns3Instrs) :
    hasInstrs P pc0 (decodeWords mc3HeadWords) ∧
    hasInstrs P (pc0 + 220#64) (decodeWords mc13MidWords) ∧
    hasInstrs P (pc0 + 356#64) (decodeWords mc13TailWords) := by
  have heq : mixColumns3Instrs =
      (decodeWords mc3HeadWords ++ decodeWords mc13MidWords) ++ decodeWords mc13TailWords := rfl
  rw [heq] at hc
  obtain ⟨hc01, hc2⟩ := hc.split_append (off := 356#64)
  obtain ⟨hc0, hc1⟩ := hc01.split_append (off := 220#64)
  exact ⟨hc0, hc1, hc2⟩

private def McMidRegs (rot1 : BitVec 64 → BitVec 64) (ptr : BitVec 64) (st : Model.FsState)
    (s : State) : Prop :=
  let c0 := rot1 st.s0 ^^^ st.s0
  let c1 := rot1 st.s1 ^^^ st.s1
  s.readReg64 (.gpr 0#5) = ptr ∧
  s.readReg64 (.gpr 1#5) = rot1 st.s3 ∧
  s.readReg64 (.gpr 2#5) = rot1 st.s1 ∧
  s.readReg64 (.gpr 3#5) = rot1 st.s0 ∧
  s.readReg64 (.gpr 6#5) = c1 ∧
  s.readReg64 (.gpr 7#5) = c0.rotateRight 24 &&& 0xff00ff00ff00ff00#64 ∧
  s.readReg64 (.gpr 8#5) = st.s6 ∧
  s.readReg64 (.gpr 9#5) = rot1 st.s5 ∧
  s.readReg64 (.gpr 10#5) = rot1 st.s7 ∧
  s.readReg64 (.gpr 11#5) = st.s3 ∧
  s.readReg64 (.gpr 12#5) = st.s4 ∧
  s.readReg64 (.gpr 13#5) = st.s5 ∧
  s.readReg64 (.gpr 14#5) = rot1 st.s4 ∧
  s.readReg64 (.gpr 15#5) = st.s2 ∧
  s.readReg64 (.gpr 16#5) = rot1 st.s6 ∧
  s.readReg64 (.gpr 17#5) = rot1 st.s7 ^^^ st.s7 ∧
  s.readReg64 (.gpr 18#5) = rot1 st.s2 ∧
  s.readReg64 (.gpr 19#5) = c0 ∧
  s.readReg64 (.gpr 20#5) = c0.rotateRight 40 &&& 0x00ff00ff00ff00ff#64 ∧
  s.readReg64 (.gpr 21#5) = c1.rotateRight 40 ∧
  s.readReg64 (.gpr 22#5) = c1.rotateRight 24

private def McTailRegs (rot1 : BitVec 64 → BitVec 64) (ptr : BitVec 64) (st : Model.FsState)
    (s : State) : Prop :=
  let c4 := rot1 st.s4 ^^^ st.s4
  s.readReg64 (.gpr 0#5) = ptr ∧
  s.readReg64 (.gpr 1#5) = c4.rotateRight 40 ∧
  s.readReg64 (.gpr 8#5) = rot1 st.s6 ^^^ st.s6 ∧
  s.readReg64 (.gpr 9#5) = rot1 st.s5 ∧
  s.readReg64 (.gpr 10#5) = rot1 st.s7 ∧
  s.readReg64 (.gpr 11#5) = rot1 st.s5 ^^^ st.s5 ∧
  s.readReg64 (.gpr 12#5) = c4 ∧
  s.readReg64 (.gpr 14#5) = (rot1 st.s3 ^^^ st.s3) ^^^ rot1 st.s4 ∧
  s.readReg64 (.gpr 16#5) = rot1 st.s6 ∧
  s.readReg64 (.gpr 17#5) = rot1 st.s7 ^^^ st.s7 ∧
  s.readReg64 (.gpr 18#5) = c4.rotateRight 24

section
arm64_proof_prelude

private theorem mc1_head {P : Program} {pc0 target_pc ptr w0 w1 w2 w3 : BitVec 64}
    {st : Model.FsState} {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords mc1HeadWords))
    (hpc : s0.pc = pc0) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hsp : s0.spAligned = true)
    (hnext : ∀ s1 : State,
      s1.pc = pc0 + 220#64 → s1.status = .Running → s1.sp = s0.sp - 32#64 →
      McMidRegs rotateRowsAndColumns11 ptr st s1 → HighRegsPreserved s0 s1 →
      SepWP P target_pc s1
        (fsStateAt ptr st ∗
         (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) post oom) :
    SepWP P target_pc s0
      (fsStateAt ptr st ∗
       (((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3))) post oom := by
  subst hx0
  have hsp0 := sp_and_15_of_spAligned hsp
  have_instrs hc 0 55
  dsimp only [fsStateAt]
  wp_stp64 hf_0 m1 hm1
  wp_stp64 hf_1 m2 hm2
  wp_steps 53
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [McMidRegs, wp_norm, arm64_norm])
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm2, hm1])

private theorem mc3_head {P : Program} {pc0 target_pc ptr w0 w1 w2 w3 : BitVec 64}
    {st : Model.FsState} {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords mc3HeadWords))
    (hpc : s0.pc = pc0) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hsp : s0.spAligned = true)
    (hnext : ∀ s1 : State,
      s1.pc = pc0 + 220#64 → s1.status = .Running → s1.sp = s0.sp - 32#64 →
      McMidRegs rotateRowsAndColumns13 ptr st s1 → HighRegsPreserved s0 s1 →
      SepWP P target_pc s1
        (fsStateAt ptr st ∗
         (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) post oom) :
    SepWP P target_pc s0
      (fsStateAt ptr st ∗
       (((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3))) post oom := by
  subst hx0
  have hsp0 := sp_and_15_of_spAligned hsp
  have_instrs hc 0 55
  dsimp only [fsStateAt]
  wp_stp64 hf_0 m1 hm1
  wp_stp64 hf_1 m2 hm2
  wp_steps 53
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [McMidRegs, wp_norm, arm64_norm])
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm2, hm1])

private theorem mc13_mid (rot1 : BitVec 64 → BitVec 64)
    {P : Program} {pc1 target_pc ptr : BitVec 64} {st : Model.FsState}
    {s1 : State} {Stack : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc1 (decodeWords mc13MidWords))
    (hpc : s1.pc = pc1) (hrun : s1.status = .Running)
    (hregs : McMidRegs rot1 ptr st s1)
    (hnext : ∀ s2 : State,
      s2.pc = pc1 + 136#64 → s2.status = .Running → s2.sp = s1.sp →
      McTailRegs rot1 ptr st s2 → HighRegsPreserved s1 s2 →
      SepWP P target_pc s2
        ((ptr ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s0) ∗
         ((ptr + 8#64) ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s1) ∗
         ((ptr + 16#64) ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s2) ∗
         ((ptr + 24#64) ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s3) ∗
         ((ptr + 32#64) ↦₆₄ st.s4) ∗ ((ptr + 40#64) ↦₆₄ st.s5) ∗
         ((ptr + 48#64) ↦₆₄ st.s6) ∗ ((ptr + 56#64) ↦₆₄ st.s7) ∗ Stack) post oom) :
    SepWP P target_pc s1 (fsStateAt ptr st ∗ Stack) post oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13,
    hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22⟩
  subst hx0
  have_instrs hc 0 34
  dsimp only [fsStateAt]
  wp_steps 18
  wp_stp64 hf_18 m1 hm1
  wp_steps 14
  wp_stp64 hf_33 m2 hm2
  rcases mixColumnsGen_words_eq rot1 rotateRowsAndColumns22 st with ⟨hw0, hw1, hw2, hw3, _, _, _, _⟩
  wp_simp_pre [hx1, hx2, hx3, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13,
    hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hw0, hw1, hw2, hw3]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
    (by simp [McTailRegs, wp_norm, arm64_norm, *])
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm2, hm1])

private theorem mc13_tail (rot1 : BitVec 64 → BitVec 64)
    {P : Program} {pc2 ptr : BitVec 64} {st : Model.FsState}
    {s0 s2 : State} {R : SepProp} {oom : State → SepProp}
    (hc : hasInstrs P pc2 (decodeWords mc13TailWords))
    (hpc : s2.pc = pc2) (hrun : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 32#64) (hsp0 : s0.spAligned = true)
    (hregs : McTailRegs rot1 ptr st s2) (hrel : HighRegsPreserved s0 s2) :
    SepWP P (s0.readReg64 .lr) s2
      ((ptr ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s0) ∗
       ((ptr + 8#64) ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s1) ∗
       ((ptr + 16#64) ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s2) ∗
       ((ptr + 24#64) ↦₆₄ (mixColumnsGen rot1 rotateRowsAndColumns22 st).s3) ∗
       ((ptr + 32#64) ↦₆₄ st.s4) ∗ ((ptr + 40#64) ↦₆₄ st.s5) ∗
       ((ptr + 48#64) ↦₆₄ st.s6) ∗ ((ptr + 56#64) ↦₆₄ st.s7) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))
      (fun sf Q =>
        (sf.mem ⊨ Q ∗ R →
          sf.mem ⊨ (⌜PureStepPreserved s0 sf⌝ ∗
            (fsStateAt ptr (mixColumnsGen rot1 rotateRowsAndColumns22 st) ∗
             stackFrameAt s0.sp 32)) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  rcases hregs with ⟨hx0, hx1, hx8, hx9, hx10, hx11, hx12, hx14, hx16, hx17, hx18⟩
  subst hx0
  have hsp_sub32 := sp_sub32_and_15 (sp_and_15_of_spAligned hsp0)
  have_instrs hc 0 31
  wp_steps 18
  wp_stp64 hf_18 m1 hm1
  wp_steps 7
  refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := none)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_26
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp2, hsp_sub32])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp2, bv_lin_norm]) (by bv_lin)
    (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_step
  wp_stp64 hf_28 m2 hm2
  refine SepWP.step_ldp64 (ea := s0.sp - 32#64) (ea2 := s0.sp - 24#64) (wb := some (.sp, s0.sp))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_29
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp2, hsp_sub32])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp2, bv_lin_norm]) (by bv_lin)
    (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_step
  rcases mixColumnsGen_words_eq rot1 rotateRowsAndColumns22 st with ⟨_, _, _, _, hw4, hw5, hw6, hw7⟩
  wp_simp_pre [hx1, hx8, hx9, hx10, hx11, hx12, hx14, hx16, hx17, hx18, hw4, hw5, hw6, hw7]
  apply SepWP.done (by simpa [wp_norm, arm64_norm] using hrel.2.2.2.2.2.2.2.1)
    (by simp [wp_norm, arm64_norm, hrun])
  refine finish_post hrel
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm2, hm1])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) ?_
  rw [stackFrameAt_32 s0.sp]; dsimp only [fsStateAt]; simp only [sepExists_sepConj_right]
  exact Entails.sepExists_right (s0.readReg64 (.gpr 22#5))
    (Entails.sepExists_right (s0.readReg64 (.gpr 21#5))
      (Entails.sepExists_right (s0.readReg64 (.gpr 20#5))
        (Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail))))

end

theorem mixColumns1_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry mixColumns1Instrs) :
    subroutine_ok P entry mixColumns1Spec := by
  obtain ⟨hc0, hc1, hc2⟩ := mixColumns1Instrs_parts hc
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [mixColumns1Spec, mixColumns1] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩
  refine ⟨fsStateAt ptr st ∗ stackFrameAt s0.sp 32, hpre, ?_⟩
  wp_conv_pre => rw [stackFrameAt_32 s0.sp]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  refine mc1_head hc0 hpc hrun hx0 hsp fun s1 hpc1 hrun1 hsp1 hregs1 hrel01 => ?_
  refine mc13_mid rotateRowsAndColumns11 hc1 hpc1 hrun1 hregs1
    fun s2 hpc2 hrun2 hsp2 hregs2 hrel12 => ?_
  exact mc13_tail rotateRowsAndColumns11 hc2 (by rw [hpc2, add_220_136]) hrun2
    (hsp2.trans hsp1) hsp hregs2 (hrel01.trans hrel12)

theorem mixColumns3_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry mixColumns3Instrs) :
    subroutine_ok P entry mixColumns3Spec := by
  obtain ⟨hc0, hc1, hc2⟩ := mixColumns3Instrs_parts hc
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [mixColumns3Spec, mixColumns3] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩
  refine ⟨fsStateAt ptr st ∗ stackFrameAt s0.sp 32, hpre, ?_⟩
  wp_conv_pre => rw [stackFrameAt_32 s0.sp]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  refine mc3_head hc0 hpc hrun hx0 hsp fun s1 hpc1 hrun1 hsp1 hregs1 hrel01 => ?_
  refine mc13_mid rotateRowsAndColumns13 hc1 hpc1 hrun1 hregs1
    fun s2 hpc2 hrun2 hsp2 hregs2 hrel12 => ?_
  exact mc13_tail rotateRowsAndColumns13 hc2 (by rw [hpc2, add_220_136]) hrun2
    (hsp2.trans hsp1) hsp hregs2 (hrel01.trans hrel12)

/-! ## 8. `invMixColumns1` & `invMixColumns3` Verification -/

private theorem xor_left_comm (x y z : BitVec 64) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc]

private theorem xor_right_comm (x y z : BitVec 64) : (x ^^^ y) ^^^ z = (x ^^^ z) ^^^ y := by
  rw [BitVec.xor_assoc, BitVec.xor_comm y z, ← BitVec.xor_assoc]

private theorem invMixColumns13_words_eq (rot1 rot2 : BitVec 64 → BitVec 64) (st : Model.FsState) :
    let c0 := rot1 st.s0 ^^^ st.s0
    let c1 := rot1 st.s1 ^^^ st.s1
    let c2 := rot1 st.s2 ^^^ st.s2
    let c3 := rot1 st.s3 ^^^ st.s3
    let c4 := rot1 st.s4 ^^^ st.s4
    let c5 := rot1 st.s5 ^^^ st.s5
    let c6 := rot1 st.s6 ^^^ st.s6
    let c7 := rot1 st.s7 ^^^ st.s7
    let d6' := c5 ^^^ st.s6
    let d7' := c6 ^^^ st.s7
    (((d6' ^^^ c0) ^^^ (c7 ^^^ st.s0)) ^^^ rot2 (d6' ^^^ c0) =
      (invMixColumnsGen rot1 rot2 st).s0) ∧
    ((((d7' ^^^ d6') ^^^ c1) ^^^ ((c0 ^^^ st.s1) ^^^ c7)) ^^^ rot2 ((d7' ^^^ d6') ^^^ c1) =
      (invMixColumnsGen rot1 rot2 st).s1) ∧
    (((c1 ^^^ st.s2) ^^^ ((d7' ^^^ c2) ^^^ (c7 ^^^ st.s0))) ^^^ rot2 ((d7' ^^^ c2) ^^^ (c7 ^^^ st.s0)) =
      (invMixColumnsGen rot1 rot2 st).s2) ∧
    ((((c2 ^^^ st.s3) ^^^ c7) ^^^ ((d6' ^^^ c3) ^^^ ((c0 ^^^ st.s1) ^^^ c7))) ^^^
        rot2 ((d6' ^^^ c3) ^^^ ((c0 ^^^ st.s1) ^^^ c7)) =
      (invMixColumnsGen rot1 rot2 st).s3) ∧
    ((((d7' ^^^ d6') ^^^ ((c1 ^^^ st.s2) ^^^ c4)) ^^^ ((c3 ^^^ st.s4) ^^^ c7)) ^^^
        rot2 ((d7' ^^^ d6') ^^^ ((c1 ^^^ st.s2) ^^^ c4)) =
      (invMixColumnsGen rot1 rot2 st).s4) ∧
    (((c4 ^^^ st.s5) ^^^ ((d7' ^^^ c5) ^^^ ((c2 ^^^ st.s3) ^^^ c7))) ^^^
        rot2 ((d7' ^^^ c5) ^^^ ((c2 ^^^ st.s3) ^^^ c7)) =
      (invMixColumnsGen rot1 rot2 st).s5) ∧
    ((d6' ^^^ (((c3 ^^^ st.s4) ^^^ c7) ^^^ c6)) ^^^ rot2 (((c3 ^^^ st.s4) ^^^ c7) ^^^ c6) =
      (invMixColumnsGen rot1 rot2 st).s6) ∧
    ((d7' ^^^ (c7 ^^^ (c4 ^^^ st.s5))) ^^^ rot2 (c7 ^^^ (c4 ^^^ st.s5)) =
      (invMixColumnsGen rot1 rot2 st).s7) := by
  rcases st with ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩
  dsimp only [invMixColumnsGen]
  rw [BitVec.xor_comm (rot1 s0) s0, BitVec.xor_comm (rot1 s1) s1,
      BitVec.xor_comm (rot1 s2) s2, BitVec.xor_comm (rot1 s3) s3,
      BitVec.xor_comm (rot1 s4) s4, BitVec.xor_comm (rot1 s5) s5,
      BitVec.xor_comm (rot1 s6) s6, BitVec.xor_comm (rot1 s7) s7]
  generalize s0 ^^^ rot1 s0 = c0, s1 ^^^ rot1 s1 = c1, s2 ^^^ rot1 s2 = c2,
    s3 ^^^ rot1 s3 = c3, s4 ^^^ rot1 s4 = c4, s5 ^^^ rot1 s5 = c5,
    s6 ^^^ rot1 s6 = c6, s7 ^^^ rot1 s7 = c7
  rw [BitVec.xor_comm c7 s0, BitVec.xor_comm c0 s1, BitVec.xor_comm c1 s2,
      BitVec.xor_comm c2 s3, BitVec.xor_comm c3 s4, BitVec.xor_comm c4 s5,
      BitVec.xor_comm c5 s6, BitVec.xor_comm c6 s7]
  generalize s0 ^^^ c7 = d0, (s1 ^^^ c0) ^^^ c7 = d1, s2 ^^^ c1 = d2,
    (s3 ^^^ c2) ^^^ c7 = d3, (s4 ^^^ c3) ^^^ c7 = d4, s5 ^^^ c4 = d5,
    s6 ^^^ c5 = d6, s7 ^^^ c6 = d7
  simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, and_self]

private def imc1HeadWords : List (BitVec 32) := invMixColumns1Words.take 46
private def imc3HeadWords : List (BitVec 32) := invMixColumns3Words.take 46
private def imc13MidWords : List (BitVec 32) := (invMixColumns1Words.drop 46).take 60
private def imc13TailWords : List (BitVec 32) := invMixColumns1Words.drop 106

private theorem invMixColumns1Instrs_parts {P : Program} {pc0 : BitVec 64}
    (hc : hasInstrs P pc0 invMixColumns1Instrs) :
    hasInstrs P pc0 (decodeWords imc1HeadWords) ∧
    hasInstrs P (pc0 + 184#64) (decodeWords imc13MidWords) ∧
    hasInstrs P (pc0 + 424#64) (decodeWords imc13TailWords) := by
  have heq : invMixColumns1Instrs =
      (decodeWords imc1HeadWords ++ decodeWords imc13MidWords) ++ decodeWords imc13TailWords := rfl
  rw [heq] at hc
  obtain ⟨hc01, hc2⟩ := hc.split_append (off := 424#64)
  obtain ⟨hc0, hc1⟩ := hc01.split_append (off := 184#64)
  exact ⟨hc0, hc1, hc2⟩

private theorem invMixColumns3Instrs_parts {P : Program} {pc0 : BitVec 64}
    (hc : hasInstrs P pc0 invMixColumns3Instrs) :
    hasInstrs P pc0 (decodeWords imc3HeadWords) ∧
    hasInstrs P (pc0 + 184#64) (decodeWords imc13MidWords) ∧
    hasInstrs P (pc0 + 424#64) (decodeWords imc13TailWords) := by
  have heq : invMixColumns3Instrs =
      (decodeWords imc3HeadWords ++ decodeWords imc13MidWords) ++ decodeWords imc13TailWords := rfl
  rw [heq] at hc
  obtain ⟨hc01, hc2⟩ := hc.split_append (off := 424#64)
  obtain ⟨hc0, hc1⟩ := hc01.split_append (off := 184#64)
  exact ⟨hc0, hc1, hc2⟩

private def Imc13MidRegs (rot1 : BitVec 64 → BitVec 64) (ptr : BitVec 64) (st : Model.FsState)
    (s0 s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = ptr ∧
  s.readReg64 (.gpr 1#5) = rot1 st.s3 ∧
  s.readReg64 (.gpr 2#5) = rot1 st.s4 ∧
  s.readReg64 (.gpr 3#5) = rot1 st.s5 ∧
  s.readReg64 (.gpr 4#5) = rot1 st.s6 ∧
  s.readReg64 (.gpr 5#5) = rot1 st.s7 ∧
  s.readReg64 (.gpr 8#5) = st.s6 ∧
  s.readReg64 (.gpr 9#5) = st.s1 ∧
  s.readReg64 (.gpr 10#5) = st.s4 ∧
  s.readReg64 (.gpr 11#5) = st.s0 ∧
  s.readReg64 (.gpr 12#5) = st.s3 ∧
  s.readReg64 (.gpr 13#5) = st.s2 ∧
  s.readReg64 (.gpr 14#5) = rot1 st.s0 ∧
  s.readReg64 (.gpr 15#5) = st.s5 ∧
  s.readReg64 (.gpr 16#5) = st.s7 ∧
  s.readReg64 (.gpr 17#5) = rot1 st.s2 ∧
  s.readReg64 (.gpr 18#5) = rot1 st.s1 ^^^ st.s1 ∧
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)

private def Imc13TailRegs (rot1 : BitVec 64 → BitVec 64) (ptr : BitVec 64) (st : Model.FsState)
    (s0 s : State) : Prop :=
  let c1 := rot1 st.s1 ^^^ st.s1
  let c2 := rot1 st.s2 ^^^ st.s2
  let c3 := rot1 st.s3 ^^^ st.s3
  let c4 := rot1 st.s4 ^^^ st.s4
  let c5 := rot1 st.s5 ^^^ st.s5
  let c6 := rot1 st.s6 ^^^ st.s6
  let c7 := rot1 st.s7 ^^^ st.s7
  let d6' := c5 ^^^ st.s6
  let d7' := c6 ^^^ st.s7
  let e4' := (d7' ^^^ d6') ^^^ ((c1 ^^^ st.s2) ^^^ c4)
  s.readReg64 (.gpr 0#5) = ptr ∧
  s.readReg64 (.gpr 3#5) = (d7' ^^^ c5) ^^^ ((c2 ^^^ st.s3) ^^^ c7) ∧
  s.readReg64 (.gpr 8#5) = d7' ∧
  s.readReg64 (.gpr 9#5) = d6' ∧
  s.readReg64 (.gpr 10#5) = (c3 ^^^ st.s4) ^^^ c7 ∧
  s.readReg64 (.gpr 13#5) = c4 ^^^ st.s5 ∧
  s.readReg64 (.gpr 14#5) = c7 ∧
  s.readReg64 (.gpr 15#5) = e4' ∧
  s.readReg64 (.gpr 16#5) = e4'.rotateRight 24 ∧
  s.readReg64 (.gpr 17#5) = c6 ∧
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)

section
arm64_proof_prelude

private theorem imc1_head {P : Program} {pc0 target_pc ptr w0 w1 : BitVec 64}
    {st : Model.FsState} {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords imc1HeadWords))
    (hpc : s0.pc = pc0) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hsp : s0.spAligned = true)
    (hnext : ∀ s1 : State,
      s1.pc = pc0 + 184#64 → s1.status = .Running → s1.sp = s0.sp - 16#64 →
      Imc13MidRegs rotateRowsAndColumns11 ptr st s0 s1 → HighRegsPreserved s0 s1 →
      SepWP P target_pc s1
        (fsStateAt ptr st ∗
         (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) post oom) :
    SepWP P target_pc s0
      (fsStateAt ptr st ∗
       (((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1))) post oom := by
  subst hx0
  have hsp0 := sp_and_15_of_spAligned hsp
  have_instrs hc 0 46
  dsimp only [fsStateAt]
  wp_stp64 hf_0 m1 hm1
  wp_steps 45
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [Imc13MidRegs, wp_norm, arm64_norm])
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm1])

private theorem imc3_head {P : Program} {pc0 target_pc ptr w0 w1 : BitVec 64}
    {st : Model.FsState} {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords imc3HeadWords))
    (hpc : s0.pc = pc0) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hsp : s0.spAligned = true)
    (hnext : ∀ s1 : State,
      s1.pc = pc0 + 184#64 → s1.status = .Running → s1.sp = s0.sp - 16#64 →
      Imc13MidRegs rotateRowsAndColumns13 ptr st s0 s1 → HighRegsPreserved s0 s1 →
      SepWP P target_pc s1
        (fsStateAt ptr st ∗
         (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) post oom) :
    SepWP P target_pc s0
      (fsStateAt ptr st ∗
       (((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1))) post oom := by
  subst hx0
  have hsp0 := sp_and_15_of_spAligned hsp
  have_instrs hc 0 46
  dsimp only [fsStateAt]
  wp_stp64 hf_0 m1 hm1
  wp_steps 45
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [Imc13MidRegs, wp_norm, arm64_norm])
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm1])

private theorem imc13_mid (rot1 : BitVec 64 → BitVec 64)
    {P : Program} {pc1 target_pc ptr : BitVec 64} {st : Model.FsState}
    {s0 s1 : State} {Stack : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc1 (decodeWords imc13MidWords))
    (hpc : s1.pc = pc1) (hrun : s1.status = .Running)
    (hregs : Imc13MidRegs rot1 ptr st s0 s1)
    (hnext : ∀ s2 : State,
      s2.pc = pc1 + 240#64 → s2.status = .Running → s2.sp = s1.sp →
      Imc13TailRegs rot1 ptr st s0 s2 → HighRegsPreserved s1 s2 →
      SepWP P target_pc s2
        ((ptr ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s0) ∗
         ((ptr + 8#64) ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s1) ∗
         ((ptr + 16#64) ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s2) ∗
         ((ptr + 24#64) ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s3) ∗
         ((ptr + 32#64) ↦₆₄ st.s4) ∗ ((ptr + 40#64) ↦₆₄ st.s5) ∗
         ((ptr + 48#64) ↦₆₄ st.s6) ∗ ((ptr + 56#64) ↦₆₄ st.s7) ∗ Stack) post oom) :
    SepWP P target_pc s1 (fsStateAt ptr st ∗ Stack) post oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hx9, hx10, hx11, hx12, hx13,
    hx14, hx15, hx16, hx17, hx18, hx21, hx22⟩
  subst hx0
  have_instrs hc 0 60
  dsimp only [fsStateAt]
  wp_steps 54
  wp_stp64 hf_54 m1 hm1
  wp_steps 4
  wp_stp64 hf_59 m2 hm2
  rcases invMixColumns13_words_eq rot1 rotateRowsAndColumns22 st with ⟨hw0, hw1, hw2, hw3, _, _, _, _⟩
  wp_simp_pre [hx1, hx2, hx3, hx4, hx5, hx8, hx9, hx10, hx11, hx12, hx13,
    hx14, hx15, hx16, hx17, hx18, hw0, hw1, hw2, hw3]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
    (by simp [Imc13TailRegs, wp_norm, arm64_norm, *])
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm2, hm1])

private theorem imc13_tail (rot1 : BitVec 64 → BitVec 64)
    {P : Program} {pc2 ptr : BitVec 64} {st : Model.FsState}
    {s0 s2 : State} {R : SepProp} {oom : State → SepProp}
    (hc : hasInstrs P pc2 (decodeWords imc13TailWords))
    (hpc : s2.pc = pc2) (hrun : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 16#64) (hsp0 : s0.spAligned = true)
    (hregs : Imc13TailRegs rot1 ptr st s0 s2) (hrel : HighRegsPreserved s0 s2) :
    SepWP P (s0.readReg64 .lr) s2
      ((ptr ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s0) ∗
       ((ptr + 8#64) ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s1) ∗
       ((ptr + 16#64) ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s2) ∗
       ((ptr + 24#64) ↦₆₄ (invMixColumnsGen rot1 rotateRowsAndColumns22 st).s3) ∗
       ((ptr + 32#64) ↦₆₄ st.s4) ∗ ((ptr + 40#64) ↦₆₄ st.s5) ∗
       ((ptr + 48#64) ↦₆₄ st.s6) ∗ ((ptr + 56#64) ↦₆₄ st.s7) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))
      (fun sf Q =>
        (sf.mem ⊨ Q ∗ R →
          sf.mem ⊨ (⌜PureStepPreserved s0 sf⌝ ∗
            (fsStateAt ptr (invMixColumnsGen rot1 rotateRowsAndColumns22 st) ∗
             stackFrameAt s0.sp 16)) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  rcases hregs with ⟨hx0, hx3, hx8, hx9, hx10, hx13, hx14, hx15, hx16, hx17, hx21, hx22⟩
  subst hx0
  have hsp_sub16 := sp_sub16_and_15 (sp_and_15_of_spAligned hsp0)
  have_instrs hc 0 33
  wp_steps 21
  wp_stp64 hf_21 m1 hm1
  wp_steps 8
  wp_stp64 hf_30 m2 hm2
  refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64) (wb := some (.sp, s0.sp))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_31
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp2, hsp_sub16])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp2, bv_lin_norm]) (by bv_lin)
    (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_step
  rcases invMixColumns13_words_eq rot1 rotateRowsAndColumns22 st with ⟨_, _, _, _, hw4, hw5, hw6, hw7⟩
  wp_simp_pre [hx3, hx8, hx9, hx10, hx13, hx14, hx15, hx16, hx17, hw4, hw5, hw6, hw7]
  apply SepWP.done (by simpa [wp_norm, arm64_norm] using hrel.2.2.2.2.2.2.2.1)
    (by simp [wp_norm, arm64_norm, hrun])
  refine finish_post hrel
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm2, hm1])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx21]) (by simp [wp_norm, arm64_norm, hx22]) ?_
  rw [stackFrameAt_16 s0.sp]; dsimp only [fsStateAt]; simp only [sepExists_sepConj_right]
  exact Entails.sepExists_right (s0.readReg64 (.gpr 20#5))
    (Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail))

end

theorem invMixColumns1_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry invMixColumns1Instrs) :
    subroutine_ok P entry invMixColumns1Spec := by
  obtain ⟨hc0, hc1, hc2⟩ := invMixColumns1Instrs_parts hc
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [invMixColumns1Spec, invMixColumns1] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩
  refine ⟨fsStateAt ptr st ∗ stackFrameAt s0.sp 16, hpre, ?_⟩
  wp_conv_pre => rw [stackFrameAt_16 s0.sp]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  refine imc1_head hc0 hpc hrun hx0 hsp fun s1 hpc1 hrun1 hsp1 hregs1 hrel01 => ?_
  refine imc13_mid rotateRowsAndColumns11 hc1 hpc1 hrun1 hregs1
    fun s2 hpc2 hrun2 hsp2 hregs2 hrel12 => ?_
  exact imc13_tail rotateRowsAndColumns11 hc2 (by rw [hpc2, add_184_240]) hrun2
    (hsp2.trans hsp1) hsp hregs2 (hrel01.trans hrel12)

theorem invMixColumns3_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry invMixColumns3Instrs) :
    subroutine_ok P entry invMixColumns3Spec := by
  obtain ⟨hc0, hc1, hc2⟩ := invMixColumns3Instrs_parts hc
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [invMixColumns3Spec, invMixColumns3] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩
  refine ⟨fsStateAt ptr st ∗ stackFrameAt s0.sp 16, hpre, ?_⟩
  wp_conv_pre => rw [stackFrameAt_16 s0.sp]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  refine imc3_head hc0 hpc hrun hx0 hsp fun s1 hpc1 hrun1 hsp1 hregs1 hrel01 => ?_
  refine imc13_mid rotateRowsAndColumns13 hc1 hpc1 hrun1 hregs1
    fun s2 hpc2 hrun2 hsp2 hregs2 hrel12 => ?_
  exact imc13_tail rotateRowsAndColumns13 hc2 (by rw [hpc2, add_184_240]) hrun2
    (hsp2.trans hsp1) hsp hregs2 (hrel01.trans hrel12)

/-! ## 9. `invMixColumns2` Verification -/

private theorem invMixColumns2_words_eq (st : Model.FsState) :
    let rot1 := rotateRowsAndColumns12
    let rot2 := rotateRows2
    let c0 := rot1 st.s0 ^^^ st.s0
    let c1 := rot1 st.s1 ^^^ st.s1
    let c2 := rot1 st.s2 ^^^ st.s2
    let c3 := rot1 st.s3 ^^^ st.s3
    let c4 := rot1 st.s4 ^^^ st.s4
    let c5 := rot1 st.s5 ^^^ st.s5
    let c6 := rot1 st.s6 ^^^ st.s6
    let c7 := rot1 st.s7 ^^^ st.s7
    let d6' := c5 ^^^ st.s6
    let d7' := c6 ^^^ st.s7
    (((d6' ^^^ c0) ^^^ rot2 (d6' ^^^ c0)) ^^^ (c7 ^^^ st.s0) =
      (invMixColumns2 st).s0) ∧
    ((((d7' ^^^ d6') ^^^ c1) ^^^ rot2 ((d7' ^^^ d6') ^^^ c1)) ^^^ ((c0 ^^^ st.s1) ^^^ c7) =
      (invMixColumns2 st).s1) ∧
    (((c1 ^^^ st.s2) ^^^ rot2 ((d7' ^^^ c2) ^^^ (c7 ^^^ st.s0))) ^^^ ((d7' ^^^ c2) ^^^ (c7 ^^^ st.s0)) =
      (invMixColumns2 st).s2) ∧
    ((((c2 ^^^ st.s3) ^^^ c7) ^^^ rot2 ((d6' ^^^ c3) ^^^ ((c0 ^^^ st.s1) ^^^ c7))) ^^^
        ((d6' ^^^ c3) ^^^ ((c0 ^^^ st.s1) ^^^ c7)) =
      (invMixColumns2 st).s3) ∧
    ((((d7' ^^^ d6') ^^^ ((c1 ^^^ st.s2) ^^^ c4)) ^^^
        rot2 ((d7' ^^^ d6') ^^^ ((c1 ^^^ st.s2) ^^^ c4))) ^^^ ((c3 ^^^ st.s4) ^^^ c7) =
      (invMixColumns2 st).s4) ∧
    (((c4 ^^^ st.s5) ^^^ rot2 ((d7' ^^^ c5) ^^^ ((c2 ^^^ st.s3) ^^^ c7))) ^^^
        ((d7' ^^^ c5) ^^^ ((c2 ^^^ st.s3) ^^^ c7)) =
      (invMixColumns2 st).s5) ∧
    ((d6' ^^^ rot2 (((c3 ^^^ st.s4) ^^^ c7) ^^^ c6)) ^^^ (((c3 ^^^ st.s4) ^^^ c7) ^^^ c6) =
      (invMixColumns2 st).s6) ∧
    ((d7' ^^^ rot2 (c7 ^^^ (c4 ^^^ st.s5))) ^^^ (c7 ^^^ (c4 ^^^ st.s5)) =
      (invMixColumns2 st).s7) := by
  dsimp only [invMixColumns2]
  rcases invMixColumns13_words_eq rotateRowsAndColumns12 rotateRows2 st with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨(xor_right_comm _ _ _).trans h0, (xor_right_comm _ _ _).trans h1,
    (xor_right_comm _ _ _).trans h2, (xor_right_comm _ _ _).trans h3,
    (xor_right_comm _ _ _).trans h4, (xor_right_comm _ _ _).trans h5,
    (xor_right_comm _ _ _).trans h6, (xor_right_comm _ _ _).trans h7⟩

private def imc2HeadWords : List (BitVec 32) := invMixColumns2Words.take 45
private def imc2TailWords : List (BitVec 32) := invMixColumns2Words.drop 45

private theorem invMixColumns2Instrs_parts {P : Program} {pc0 : BitVec 64}
    (hc : hasInstrs P pc0 invMixColumns2Instrs) :
    hasInstrs P pc0 (decodeWords imc2HeadWords) ∧
    hasInstrs P (pc0 + 180#64) (decodeWords imc2TailWords) := by
  have heq : invMixColumns2Instrs = decodeWords imc2HeadWords ++ decodeWords imc2TailWords := rfl
  rw [heq] at hc
  exact hc.split_append (off := 180#64)

private def Imc2TailRegs (ptr : BitVec 64) (st : Model.FsState) (s0 s : State) : Prop :=
  let rot1 := rotateRowsAndColumns12
  s.readReg64 (.gpr 0#5) = ptr ∧
  s.readReg64 (.gpr 1#5) = rot1 st.s4 ∧
  s.readReg64 (.gpr 2#5) = rot1 st.s2 ∧
  s.readReg64 (.gpr 3#5) = rot1 st.s5 ∧
  s.readReg64 (.gpr 4#5) = rot1 st.s6 ∧
  s.readReg64 (.gpr 5#5) = rot1 st.s7 ∧
  s.readReg64 (.gpr 8#5) = st.s5 ∧
  s.readReg64 (.gpr 9#5) = st.s2 ∧
  s.readReg64 (.gpr 10#5) = st.s4 ∧
  s.readReg64 (.gpr 11#5) = st.s0 ∧
  s.readReg64 (.gpr 12#5) = st.s3 ∧
  s.readReg64 (.gpr 13#5) = st.s1 ∧
  s.readReg64 (.gpr 14#5) = st.s6 ∧
  s.readReg64 (.gpr 15#5) = st.s7 ∧
  s.readReg64 (.gpr 16#5) = rot1 st.s0 ∧
  s.readReg64 (.gpr 17#5) = rot1 st.s1 ∧
  s.readReg64 (.gpr 18#5) = rot1 st.s3 ∧
  s.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) ∧
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)

section
arm64_proof_prelude

private theorem imc2_head {P : Program} {pc0 target_pc ptr w0 w1 : BitVec 64}
    {st : Model.FsState} {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords imc2HeadWords))
    (hpc : s0.pc = pc0) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ptr) (hsp : s0.spAligned = true)
    (hnext : ∀ s1 : State,
      s1.pc = pc0 + 180#64 → s1.status = .Running → s1.sp = s0.sp - 16#64 →
      Imc2TailRegs ptr st s0 s1 → HighRegsPreserved s0 s1 →
      SepWP P target_pc s1
        (fsStateAt ptr st ∗
         (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ w1))) post oom) :
    SepWP P target_pc s0
      (fsStateAt ptr st ∗
       (((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1))) post oom := by
  subst hx0
  have hsp0 := sp_and_15_of_spAligned hsp
  have_instrs hc 0 45
  dsimp only [fsStateAt]
  wp_str64 hf_0 m1 hm1
  wp_steps 44
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [Imc2TailRegs, wp_norm, arm64_norm])
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm1])

private theorem imc2_tail
    {P : Program} {pc1 ptr w1 : BitVec 64} {st : Model.FsState}
    {s0 s1 : State} {R : SepProp} {oom : State → SepProp}
    (hc : hasInstrs P pc1 (decodeWords imc2TailWords))
    (hpc : s1.pc = pc1) (hrun : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 16#64) (hsp0 : s0.spAligned = true)
    (hregs : Imc2TailRegs ptr st s0 s1) (hrel : HighRegsPreserved s0 s1) :
    SepWP P (s0.readReg64 .lr) s1
      (fsStateAt ptr st ∗
       (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ w1)))
      (fun sf Q =>
        (sf.mem ⊨ Q ∗ R →
          sf.mem ⊨ (⌜PureStepPreserved s0 sf⌝ ∗
            (fsStateAt ptr (invMixColumns2 st) ∗ stackFrameAt s0.sp 16)) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hx9, hx10, hx11, hx12, hx13,
    hx14, hx15, hx16, hx17, hx18, hx20, hx21, hx22⟩
  subst hx0
  have hsp_sub16 := sp_sub16_and_15 (sp_and_15_of_spAligned hsp0)
  have_instrs hc 0 54
  dsimp only [fsStateAt]
  wp_steps 36
  wp_stp64 hf_36 m1 hm1
  wp_steps 6
  wp_stp64 hf_43 m2 hm2
  wp_steps 4
  wp_stp64 hf_48 m3 hm3
  wp_steps 2
  wp_stp64 hf_51 m4 hm4
  refine SepWP.step_ldr64 (ea := s0.sp - 16#64) (wb := some (.sp, s0.sp))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_52
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, wp_norm, arm64_norm, hsp1, hsp_sub16])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp1, bv_lin_norm])
    (by wp_sep_access) (by wp_norm_lhs) ?_
  wp_step
  rcases invMixColumns2_words_eq st with ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩
  wp_simp_pre [hx1, hx2, hx3, hx4, hx5, hx8, hx9, hx10, hx11, hx12, hx13,
    hx14, hx15, hx16, hx17, hx18, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
  apply SepWP.done (by simpa [wp_norm, arm64_norm] using hrel.2.2.2.2.2.2.2.1)
    (by simp [wp_norm, arm64_norm, hrun])
  refine finish_post hrel
    (by simp [HighRegsPreserved, wp_norm, arm64_norm, hm4, hm3, hm2, hm1])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx20])
    (by simp [wp_norm, arm64_norm, hx21]) (by simp [wp_norm, arm64_norm, hx22]) ?_
  rw [stackFrameAt_16 s0.sp]; simp only [sepExists_sepConj_right]
  exact Entails.sepExists_right (s0.readReg64 (.gpr 19#5))
    (Entails.sepExists_right w1 (by sep_entail))

end

theorem invMixColumns2_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry invMixColumns2Instrs) :
    subroutine_ok P entry invMixColumns2Spec := by
  obtain ⟨hc0, hc1⟩ := invMixColumns2Instrs_parts hc
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [invMixColumns2Spec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩
  refine ⟨fsStateAt ptr st ∗ stackFrameAt s0.sp 16, hpre, ?_⟩
  wp_conv_pre => rw [stackFrameAt_16 s0.sp]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  refine imc2_head hc0 hpc hrun hx0 hsp fun s1 hpc1 hrun1 hsp1 hregs1 hrel01 => ?_
  exact imc2_tail hc1 hpc1 hrun1 hsp1 hsp hregs1 hrel01

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode

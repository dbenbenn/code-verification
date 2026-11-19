/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AllocZeroedHelpersFine
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers
meta import Lean
meta import ProofLib.StdStartup.StdDetect
import Arm64.Trusted.ISA.Eval
import ProofLib.BV
import ProofLib.BV.ReflectROBDD
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `fixslice64::aes256_key_schedule` Binary Contract (`Fixslice64.KeySchedule`)

Placement-generic (`hasInstrs`) `subroutine_ok` verification of the 510-instruction
`aes::soft::fixslice64::aes256_key_schedule` key-expansion routine (`1040` B own stack frame +
`80` B max callee stack = `1120` B total stack):
- `aes256KeyScheduleTemplateWords` and `aes256KeyScheduleInstrs`: exact 510-word `.rlib` template
  and relocation-parameterized instruction list across all 11 `BL` call sites (`memset`,
  `bitslice` × 2, `memshift32` × 3, `sub_bytes` × 2, `xor_columns` × 2, `memcpy`);
- `aes256KeyScheduleInstrs_template_eq`: `Obj.patchRelocs` decode equivalence against the `.rlib`
  template words;
- `Aes256KeyScheduleCallees` (with `.of_hasInstrs` and `.of_hasInstrs_full` constructors);
- `aes256KeySchedule_ok`: total-correctness `subroutine_ok` theorem establishing
  `aes256KeyScheduleSpec` (`fsKeys256At outPtr (Model.aes256KeyScheduleFs key)`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.Fine (allocMemsetVmSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (Blocks4 FsKeys256)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj bytesAt_append fsStateAt fsStateBytes fsStateAt_entails_memRegion
   pointsToBytes_zero64_eq_fsStateAt fsKeys256At fsKeys256Bytes fsKeys256Bytes_length
   fsKeys256At_eq_pointsToBytes fsKeys256At_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice (bitsliceInstrs bitsliceRepSpec bitslice_rep_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode (subBytesInstrs subBytesSpec subBytes_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers
  (memshift32ReachableInstrs Memshift32PanicSyms memshift32FullInstrs memshift32Spec memshift32_ok
   memshift32_full_ok xorColumnsReachableInstrs XorColumnsPanicSyms xorColumnsFullInstrs
   xorColumnsSpec xorColumns_ok xorColumns_full_ok)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. `.rlib` Instruction Template, Relocation Table & Callee Bundle -/

@[expose] def ksSeg0Words : List (BitVec 32) :=
  [0xa9bb7bfd#32, 0xf9000bfc#32, 0xa9025ff8#32, 0xa90357f6#32, 0xa9044ff4#32, 0x910003fd#32, 0xd10f03ff#32,
   0x910003f5#32, 0xaa0003f4#32, 0x2a1f03e1#32, 0x910202a0#32, 0x52806802#32, 0xaa0803f3#32]
@[expose] def ksSeg1Words : List (BitVec 32) := [0x910003e0#32, 0xaa1403e1#32, 0xaa1403e2#32, 0xaa1403e3#32, 0xaa1403e4#32]
@[expose] def ksSeg2Words : List (BitVec 32) := [0x910102a0#32, 0x91004281#32, 0x91004282#32, 0x91004283#32, 0x91004284#32]
@[expose] def ksSeg3Words : List (BitVec 32) := [0x910003e0#32, 0x52800f01#32, 0x52800102#32]
@[expose] def ksLoopInitWords : List (BitVec 32) := [0xaa1f03f4#32, 0x92800bf6#32, 0x52801017#32]
@[expose] def ksRconEvenPreWords : List (BitVec 32) := [0x8b1402b8#32, 0x91020300#32]
@[expose] def ksRconEvenMidWords : List (BitVec 32) :=
  [0xa9482708#32, 0x910003e0#32, 0xa94aaf0a#32, 0x9101c2c2#32, 0x52800f01#32, 0x52800203#32, 0x52800384#32, 0xaa2803e8#32,
   0xaa2903e9#32, 0xa9082708#32, 0xaa2a03e8#32, 0xaa2b03e9#32, 0xa90aa708#32, 0xf8776aa8#32, 0xd2640d08#32, 0xf8376aa8#32]
@[expose] def ksRconOddPre1Words : List (BitVec 32) := [0xb40003b6#32, 0x910003e0#32, 0x9101c2c2#32, 0x52800f01#32]
@[expose] def ksRconOddPre2Words : List (BitVec 32) := [0x91030300#32]
@[expose] def ksRconOddMidWords : List (BitVec 32) :=
  [0xa94c2708#32, 0x910003e0#32, 0xa94eaf0a#32, 0x9101e2c2#32, 0x52800f01#32, 0x52800203#32, 0x52800184#32,
   0xaa2803e8#32, 0xaa2903e9#32, 0xa90c2708#32, 0xaa2a03e8#32, 0xaa2b03e9#32, 0xa90ea708#32]
@[expose] def ksRconOddPostWords : List (BitVec 32) := [0x910003e0#32, 0x9101e2c2#32, 0x52800f01#32]
@[expose] def ksRconTailWords : List (BitVec 32) := [0x910042d6#32, 0x91020294#32, 0x910222f7#32, 0x17ffffd0#32]
@[expose] def ksIsrInitWords : List (BitVec 32) :=
  [0xd2a001eb#32, 0xd2a1e1e8#32, 0xb2009fe9#32, 0xf2c01feb#32, 0xaa1f03ea#32, 0xf2e1e1e8#32, 0xf2e01e0b#32, 0x926c7d29#32, 0x910003ec#32]
@[expose] def ksIsr1Words : List (BitVec 32) :=
  [0x8b0a018d#32, 0x9104014a#32, 0xa9443dae#32, 0xf10c015f#32, 0xa94549b1#32, 0xa94715a4#32, 0xca4e21d0#32, 0xca4f21e2#32, 0xca512223#32,
   0xca522246#32, 0x8a090200#32, 0xa94605b0#32, 0x8b002000#32, 0x8a0900c6#32, 0x8b0620c6#32, 0xca0e000e#32, 0x8a090040#32, 0x8a090062#32,
   0x8b002000#32, 0xca4e11c3#32, 0x8b022042#32, 0xca502207#32, 0xca1200d2#32, 0xca412026#32, 0xca0f000f#32, 0x8a080063#32, 0xca110051#32,
   0xca4f11e2#32, 0x8b031060#32, 0x8a0900e7#32, 0x8a0900c6#32, 0xca511223#32, 0x8b0720e7#32, 0x8a080042#32, 0xca0e000e#32, 0xca521240#32,
   0x8b021042#32, 0x8b0620c6#32, 0x8a080063#32, 0x8a080000#32, 0xca1000f0#32, 0x8b031063#32, 0xca0f004f#32, 0xca501202#32, 0xa9043dae#32]
@[expose] def ksIsr2Words : List (BitVec 32) :=
  [0x8b00100e#32, 0xca44208f#32, 0xca0100c0#32, 0xca4520a1#32, 0xca110071#32, 0x8a0901ef#32, 0xca1201ce#32, 0xca401003#32, 0x8a090032#32,
   0x8b0f21ef#32, 0x8a080041#32, 0x8b122252#32, 0x8b011021#32, 0x8a080062#32, 0xca0401ef#32, 0x8b021042#32, 0xa90539b1#32, 0xca050252#32,
   0xca4f11e3#32, 0xca10002e#32, 0xca521250#32, 0xca000051#32, 0x8a080060#32, 0xa94809a1#32, 0x8a080210#32, 0x8b001000#32, 0xa90645ae#32,
   0x8b101210#32, 0xca412023#32, 0xca0f000e#32, 0xca42204f#32, 0xca120210#32, 0xa94901b2#32, 0x92101c71#32, 0x92101def#32, 0xa90741ae#32]
@[expose] def ksIsr3Words : List (BitVec 32) :=
  [0xaa112231#32, 0xaa0f21ef#32, 0xca522243#32, 0xca40200e#32, 0xca010230#32, 0xca0201ef#32, 0x92101c71#32, 0xa94a09a1#32, 0xaa112231#32,
   0x92101dce#32, 0xa9083db0#32, 0xaa0e21ce#32, 0xca12022f#32, 0xca412030#32, 0xca422051#32, 0xca0001ce#32, 0xa90939af#32, 0x92101e0f#32,
   0x92101e30#32, 0xa94c49b1#32, 0xaa0f21ef#32, 0xa94b01ae#32, 0xaa102210#32, 0xca0101ef#32, 0xca512224#32, 0xca522241#32, 0xca020210#32,
   0xca4e21c3#32, 0xa90a41af#32]
@[expose] def ksIsr4Words : List (BitVec 32) :=
  [0x8a0b0084#32, 0x8a0b0021#32, 0x8b042084#32, 0x92101c62#32, 0xca402003#32, 0x8b012021#32, 0xaa022042#32, 0xca110091#32, 0xa94d11a5#32,
   0x92101c63#32, 0xca120032#32, 0xca511227#32, 0xaa032063#32, 0xca521241#32, 0xca0e004e#32, 0xca4520a6#32, 0xca000070#32, 0x8a0800e0#32,
   0x8a080021#32, 0x8a0b00c6#32, 0x8b001000#32, 0x8b011021#32, 0x8b0620cf#32, 0xca442083#32, 0xa90b41ae#32, 0xca11000e#32, 0xca120030#32,
   0xca0501ef#32, 0x8a0b0072#32, 0xa90c41ae#32, 0xca4f11e2#32, 0x8b122252#32, 0xa94f0da1#32, 0x8a080051#32, 0xca040250#32, 0x8b11122e#32,
   0xa94e45a0#32, 0xca412024#32, 0xca432065#32, 0xca0f01ce#32, 0xca50120f#32]
@[expose] def ksIsr5Words : List (BitVec 32) :=
  [0xca402012#32, 0xca512222#32, 0x8a0b00a5#32, 0x8a0801ef#32, 0x8a0b0252#32, 0x8a0b0042#32, 0x8b0f11ef#32, 0x8b122252#32, 0xca1001ef#32,
   0xca000252#32, 0x8b022040#32, 0x8a0b0082#32, 0xca521244#32, 0x8b022042#32, 0xa90d3dae#32, 0xca110010#32, 0x8b0520b1#32, 0x8a080080#32,
   0xca501204#32, 0xca010041#32, 0xca030231#32, 0x8b001000#32, 0xca411022#32, 0x8a080083#32, 0xca511224#32, 0x8b03106e#32, 0x8a08004f#32,
   0xca120012#32, 0x8a080080#32, 0x8b0f11ef#32, 0xca1001ce#32, 0x8b001010#32, 0xa90e39b2#32, 0xca0101ee#32, 0xca11020f#32, 0xa90f3dae#32,
   0x54ffe8a1#32]
@[expose] def ksRk13aWords : List (BitVec 32) :=
  [0xf941a3ea#32, 0xf941a7eb#32, 0x910003e1#32, 0xf941abec#32, 0xf941aff0#32, 0xaa1303e0#32, 0xca4a214d#32, 0xca4b216e#32, 0xf941b3f2#32,
   0xca4c218f#32, 0xca502211#32, 0x52807802#32, 0x8a0901ad#32, 0x8a0901ce#32, 0x8b0d21ad#32, 0x8a0901ef#32, 0x8b0e21ce#32, 0x8b0f21ef#32,
   0xca0a01aa#32, 0xca0b01cb#32, 0x8a09022e#32, 0xca4a114d#32, 0xca0c01ec#32, 0xca4b116f#32, 0xca4c1191#32, 0x8b0e21ce#32, 0x8a0801ad#32,
   0x8a0801ef#32, 0x8b0d11ad#32, 0x8a080231#32, 0xca1001ce#32, 0x8b0f11ef#32, 0x8b111230#32, 0xf941b7f1#32, 0xca0a01aa#32, 0xca52224d#32,
   0xca0b01eb#32, 0xf941bbef#32, 0xca0c020c#32, 0x8a0901ad#32, 0xf941bff0#32, 0xf901a3ea#32, 0x8b0d21ad#32]
@[expose] def ksRk13bWords : List (BitVec 32) :=
  [0xca51222a#32, 0xf901a7eb#32, 0xca4f21eb#32, 0xf901abec#32, 0xca4e11cc#32, 0xca1201ad#32, 0xca502212#32, 0x8a09014a#32, 0x8a08018c#32,
   0x8b0a214a#32, 0x8a09016b#32, 0x8a090249#32, 0x8b0c118c#32, 0x8b0b216b#32, 0x8b092129#32, 0xca11014a#32, 0xca4d11b1#32, 0xca0e018c#32,
   0xca4a114e#32, 0xca0f016b#32, 0xca100129#32, 0x8a08022f#32, 0xca4b1171#32, 0xca491130#32, 0x8a0801ce#32, 0xf901afec#32, 0x8b0e11cc#32,
   0x8a08022e#32, 0x8b0f11ef#32, 0x8a080208#32, 0x8b0e11ce#32, 0x8b081108#32, 0xca0a018a#32, 0xca0d01ed#32, 0xf901b7ea#32, 0xca0b01ca#32,
   0xca090108#32, 0xa94427eb#32, 0xf901bbea#32, 0xf901bfe8#32, 0xaa2b03e8#32, 0xa946afea#32, 0xaa2903e9#32, 0xf901b3ed#32]
@[expose] def ksNots1Words : List (BitVec 32) :=
  [0xa90427e8#32, 0xaa2a03e8#32, 0xaa2b03ea#32, 0xa9482fe9#32, 0xa906abe8#32, 0xaa2903e8#32, 0xaa2b03ea#32, 0xa94aafe9#32, 0xa9082be8#32,
   0xaa2903e8#32, 0xaa2b03ea#32, 0xa94c2fe9#32, 0xa90aabe8#32, 0xaa2903e8#32, 0xaa2b03ea#32, 0xa94eafe9#32, 0xa90c2be8#32, 0xaa2903e8#32,
   0xaa2b03ea#32, 0xa9502fe9#32, 0xa90eabe8#32, 0xaa2903e8#32, 0xaa2b03ea#32, 0xa952afe9#32, 0xa9102be8#32, 0xaa2903e8#32, 0xaa2b03ea#32,
   0xa9542fe9#32, 0xa912abe8#32]
@[expose] def ksNots2Words : List (BitVec 32) :=
  [0xaa2903e8#32, 0xaa2b03ea#32, 0xa956afe9#32, 0xa9142be8#32, 0xaa2903e8#32, 0xaa2b03ea#32, 0xa9582fe9#32, 0xa916abe8#32, 0xaa2903e8#32,
   0xaa2b03ea#32, 0xa95aafe9#32, 0xa9182be8#32, 0xaa2903e8#32, 0xaa2b03ea#32, 0xa95c2fe9#32, 0xa91aabe8#32, 0xaa2903e8#32, 0xaa2b03ea#32,
   0xa95eafe9#32, 0xa91c2be8#32, 0xaa2903e8#32, 0xf94103e9#32, 0xaa2b03ea#32, 0xf94107eb#32, 0xa91eabe8#32]
@[expose] def ksNots3Words : List (BitVec 32) :=
  [0xf9411bea#32, 0xaa2903e8#32, 0xf94117e9#32, 0xf90103e8#32, 0xaa2b03e8#32, 0xf90107e8#32, 0xaa2903e8#32, 0xf94123e9#32, 0xf90117e8#32,
   0xaa2a03e8#32, 0xf94127ea#32, 0xf9011be8#32, 0xaa2903e8#32, 0xf94137e9#32, 0xf90123e8#32, 0xaa2a03e8#32, 0xf9413bea#32, 0xf90127e8#32,
   0xaa2903e8#32, 0xf94143e9#32, 0xf90137e8#32, 0xaa2a03e8#32, 0xf94147ea#32, 0xf9013be8#32, 0xaa2903e8#32, 0xf94157e9#32, 0xf90143e8#32,
   0xaa2a03e8#32, 0xf9415bea#32, 0xf90147e8#32, 0xaa2903e8#32, 0xf94163e9#32, 0xf90157e8#32, 0xaa2a03e8#32, 0xf94167ea#32, 0xf9015be8#32]
@[expose] def ksNots4Words : List (BitVec 32) :=
  [0xaa2903e8#32, 0xf94177e9#32, 0xf90163e8#32, 0xaa2a03e8#32, 0xf9417bea#32, 0xf90167e8#32, 0xaa2903e8#32, 0xf94183e9#32, 0xf90177e8#32,
   0xaa2a03e8#32, 0xf94187ea#32, 0xf9017be8#32, 0xaa2903e8#32, 0xf94197e9#32, 0xf90183e8#32, 0xaa2a03e8#32, 0xf9419bea#32, 0xf90187e8#32,
   0xaa2903e8#32, 0xf941a3e9#32, 0xf90197e8#32, 0xaa2a03e8#32, 0xf941a7ea#32, 0xf9019be8#32, 0xaa2903e8#32, 0xf941b7e9#32, 0xf901a3e8#32,
   0xaa2a03e8#32, 0xf941bbea#32, 0xf901a7e8#32, 0xaa2903e8#32, 0xf941c3e9#32, 0xf901b7e8#32, 0xaa2a03e8#32, 0xf941c7ea#32, 0xf901bbe8#32,
   0xaa2903e8#32, 0xf941d7e9#32, 0xf901c3e8#32, 0xaa2a03e8#32, 0xf941dbea#32, 0xf901c7e8#32, 0xaa2903e8#32, 0xf901d7e8#32, 0xaa2a03e8#32,
   0xf901dbe8#32]
@[expose] def ksEpilogueWords : List (BitVec 32) :=
  [0x910f03ff#32, 0xa9444ff4#32, 0xf9400bfc#32, 0xa94357f6#32, 0xa9425ff8#32, 0xa8c57bfd#32, 0xd65f03c0#32]

/-- Complete 510-word (`2040`-byte) unrelocated `.rlib` template of `aes256_key_schedule`. -/
@[expose] def aes256KeyScheduleTemplateWords : List (BitVec 32) :=
  let init := ksSeg0Words ++ [0x94000000#32] ++ ksSeg1Words ++ [0x94000000#32] ++
    ksSeg2Words ++ [0x94000000#32] ++ ksSeg3Words ++ [0x94000000#32] ++ ksLoopInitWords
  let rcon := ksRconEvenPreWords ++ [0x94000000#32] ++ ksRconEvenMidWords ++ [0x94000000#32] ++
    ksRconOddPre1Words ++ [0x94000000#32] ++ ksRconOddPre2Words ++ [0x94000000#32] ++
    ksRconOddMidWords ++ [0x94000000#32] ++ ksRconOddPostWords ++ [0x94000000#32] ++ ksRconTailWords
  let isr := ksIsrInitWords ++ ksIsr1Words ++ ksIsr2Words ++ ksIsr3Words ++ ksIsr4Words ++ ksIsr5Words
  let tail := ksRk13aWords ++ ksRk13bWords ++ ksNots1Words ++ ksNots2Words ++ ksNots3Words ++
    ksNots4Words ++ [0x94000000#32] ++ ksEpilogueWords
  init ++ rcon ++ isr ++ tail

/-- Relocation-patched 510-instruction sequence of `fixslice64::aes256_key_schedule` at `fnAddr`. -/
@[expose] def aes256KeyScheduleInstrs
    (fnAddr memsetAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr memcpyAddr : BitVec 64) :
    List Instr :=
  let init := decodeWords ksSeg0Words ++ [ .bl (memsetAddr - (fnAddr + 0x034#64)) ] ++
    decodeWords ksSeg1Words ++ [ .bl (bitsliceAddr - (fnAddr + 0x04c#64)) ] ++
    decodeWords ksSeg2Words ++ [ .bl (bitsliceAddr - (fnAddr + 0x064#64)) ] ++
    decodeWords ksSeg3Words ++ [ .bl (memshift32Addr - (fnAddr + 0x074#64)) ] ++ decodeWords ksLoopInitWords
  let rcon := decodeWords ksRconEvenPreWords ++ [ .bl (subBytesAddr - (fnAddr + 0x08c#64)) ] ++
    decodeWords ksRconEvenMidWords ++ [ .bl (xorColumnsAddr - (fnAddr + 0x0d0#64)) ] ++
    decodeWords ksRconOddPre1Words ++ [ .bl (memshift32Addr - (fnAddr + 0x0e4#64)) ] ++
    decodeWords ksRconOddPre2Words ++ [ .bl (subBytesAddr - (fnAddr + 0x0ec#64)) ] ++
    decodeWords ksRconOddMidWords ++ [ .bl (xorColumnsAddr - (fnAddr + 0x124#64)) ] ++
    decodeWords ksRconOddPostWords ++ [ .bl (memshift32Addr - (fnAddr + 0x134#64)) ] ++ decodeWords ksRconTailWords
  let isr := decodeWords ksIsrInitWords ++ decodeWords ksIsr1Words ++ decodeWords ksIsr2Words ++
    decodeWords ksIsr3Words ++ decodeWords ksIsr4Words ++ decodeWords ksIsr5Words
  let tail := decodeWords ksRk13aWords ++ decodeWords ksRk13bWords ++ decodeWords ksNots1Words ++
    decodeWords ksNots2Words ++ decodeWords ksNots3Words ++ decodeWords ksNots4Words ++
    [ .bl (memcpyAddr - (fnAddr + 0x7d8#64)) ] ++ decodeWords ksEpilogueWords
  init ++ rcon ++ isr ++ tail

private theorem length_decodeWords (ws : List (BitVec 32)) : (decodeWords ws).length = ws.length := by
  simp [decodeWords]

theorem aes256KeyScheduleInstrs_length
    (fnAddr memsetAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr memcpyAddr : BitVec 64) :
    (aes256KeyScheduleInstrs fnAddr memsetAddr bitsliceAddr memshift32Addr subBytesAddr
      xorColumnsAddr memcpyAddr).length = 510 := by
  dsimp only [aes256KeyScheduleInstrs]
  simp only [List.length_append, List.length_singleton, length_decodeWords]; decide

/-- Exact 11 `R_AARCH64_CALL26` relocation entries of `fixslice64::aes256_key_schedule`. -/
@[expose] def aes256KeyScheduleRelocs : List Obj.RelocEntry :=
  [{ off := 0x034, kind := .call26, sym := "memset" },
   { off := 0x04c, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice8bitslice" },
   { off := 0x064, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice8bitslice" },
   { off := 0x074, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice10memshift32" },
   { off := 0x08c, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice9sub_bytes" },
   { off := 0x0d0, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice11xor_columns" },
   { off := 0x0e4, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice10memshift32" },
   { off := 0x0ec, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice9sub_bytes" },
   { off := 0x124, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice11xor_columns" },
   { off := 0x134, kind := .call26, sym := "_RNvNtNtCseLFX6RtqVKc_3aes4soft8fixslice10memshift32" },
   { off := 0x7d8, kind := .call26, sym := "memcpy" }]

private theorem map_decode_eq_map_some : ∀ {ws : List (BitVec 32)},
    (ws.all fun w => (Arm64.decode w).isSome) = true → ws.map Arm64.decode = (decodeWords ws).map some
  | [], _ => rfl
  | w :: ws, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h; simp only [List.map_cons, decodeWords, decodeWord]
      cases hd : Arm64.decode w with
      | none => simp [hd] at h
      | some i => exact congrArg (some i :: ·) (map_decode_eq_map_some h.2)

private def patchChunk (k : Nat) (ws : List (BitVec 32)) : List (BitVec 32) :=
  (ws.zipIdx k).map fun (w, j) =>
    match aes256KeyScheduleRelocs.find? (·.off == 4 * j) with
    | some r => Obj.patchRelocWord r.kind w (0#64 + BitVec.ofNat 64 (4 * j)) (Obj.addSignedAddr 0#64 r.addend)
    | none => w

private theorem patchChunk_step_seg {k k' : Nat} {xs ys : List (BitVec 32)} {rest : List Instr}
    (hlen : k + xs.length = k') (hp : patchChunk k xs = xs)
    (hd : (xs.all fun w => (Arm64.decode w).isSome) = true)
    (hrest : (patchChunk k' ys).map Arm64.decode = rest.map some) :
    (patchChunk k (xs ++ ys)).map Arm64.decode = (decodeWords xs ++ rest).map some := by
  have hsplit : patchChunk k (xs ++ ys) = patchChunk k xs ++ patchChunk (k + xs.length) ys := by
    simp only [patchChunk, List.zipIdx_append, List.map_append]
  rw [hsplit, hlen, hp, List.map_append, map_decode_eq_map_some hd, hrest, List.map_append]

private theorem patchChunk_step_bl {k k' : Nat} {ys : List (BitVec 32)} {i : Instr}
    {rest : List Instr} (hlen : k + 1 = k')
    (hbl : (patchChunk k [0x94000000#32]).map Arm64.decode = [some i])
    (hrest : (patchChunk k' ys).map Arm64.decode = rest.map some) :
    (patchChunk k ([0x94000000#32] ++ ys)).map Arm64.decode = ([i] ++ rest).map some := by
  have hsplit : patchChunk k ([0x94000000#32] ++ ys) = patchChunk k [0x94000000#32] ++ patchChunk (k + 1) ys := by
    simp only [patchChunk, List.zipIdx_append, List.map_append]; rfl
  rw [hsplit, List.map_append, hlen, hbl, hrest]; rfl

theorem aes256KeyScheduleInstrs_template_eq :
    (Obj.patchRelocs aes256KeyScheduleRelocs aes256KeyScheduleTemplateWords 0#64 (fun _ => 0#64)).map Arm64.decode =
      (aes256KeyScheduleInstrs 0#64 0#64 0#64 0#64 0#64 0#64 0#64).map some := by
  change (patchChunk 0 aes256KeyScheduleTemplateWords).map Arm64.decode = _
  dsimp only [aes256KeyScheduleTemplateWords, aes256KeyScheduleInstrs]; simp only [List.append_assoc]
  refine patchChunk_step_seg (k' := 13) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_bl (k' := 14) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 19) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_bl (k' := 20) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 25) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_bl (k' := 26) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 29) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_bl (k' := 30) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 33) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 35) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_bl (k' := 36) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 52) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_bl (k' := 53) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 57) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_bl (k' := 58) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 59) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_bl (k' := 60) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 73) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_bl (k' := 74) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 77) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_bl (k' := 78) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 82) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 91) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 136) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 172) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 201) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 242) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 279) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 322) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 366) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 395) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 420) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_seg (k' := 456) (by decide) (by decide) (by decide) ?_; refine patchChunk_step_seg (k' := 502) (by decide) (by decide) (by decide) ?_
  refine patchChunk_step_bl (k' := 503) (by decide) (by decide) ?_
  have hp : patchChunk 503 ksEpilogueWords = ksEpilogueWords := by decide
  rw [hp]; exact map_decode_eq_map_some (by decide)

/-- Bundle of `subroutine_ok` contracts for the six subroutines called by `aes256_key_schedule`. -/
structure Aes256KeyScheduleCallees (P : Program)
    (memsetAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr memcpyAddr : BitVec 64) : Prop where
  memset_ok : subroutine_ok P memsetAddr allocMemsetVmSpec
  bitslice_ok : subroutine_ok P bitsliceAddr bitsliceRepSpec
  memshift32_ok : subroutine_ok P memshift32Addr memshift32Spec
  subBytes_ok : subroutine_ok P subBytesAddr subBytesSpec
  xorColumns_ok : subroutine_ok P xorColumnsAddr xorColumnsSpec
  memcpy_ok : subroutine_ok P memcpyAddr allocMemcpyVmSpec

theorem Aes256KeyScheduleCallees.of_hasInstrs {P : Program}
    {memsetAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr memcpyAddr : BitVec 64}
    (hmemset : subroutine_ok P memsetAddr allocMemsetVmSpec) (hbitslice : hasInstrs P bitsliceAddr bitsliceInstrs)
    (hmemshift32 : hasInstrs P memshift32Addr memshift32ReachableInstrs)
    (hsubBytes : hasInstrs P subBytesAddr subBytesInstrs)
    (hxorColumns : hasInstrs P xorColumnsAddr xorColumnsReachableInstrs)
    (hmemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    Aes256KeyScheduleCallees P memsetAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr memcpyAddr :=
  ⟨hmemset, bitslice_rep_ok hbitslice, KsHelpers.memshift32_ok P memshift32Addr hmemshift32,
   SboxCode.subBytes_ok hsubBytes, KsHelpers.xorColumns_ok P xorColumnsAddr hxorColumns, hmemcpy⟩

theorem Aes256KeyScheduleCallees.of_hasInstrs_full {P : Program}
    {memsetAddr bitsliceAddr subBytesAddr memcpyAddr : BitVec 64} {pm : Memshift32PanicSyms} {px : XorColumnsPanicSyms}
    (hmemset : subroutine_ok P memsetAddr allocMemsetVmSpec) (hbitslice : hasInstrs P bitsliceAddr bitsliceInstrs)
    (hmemshift32 : hasInstrs P pm.fnAddr (memshift32FullInstrs pm))
    (hsubBytes : hasInstrs P subBytesAddr subBytesInstrs)
    (hxorColumns : hasInstrs P px.fnAddr (xorColumnsFullInstrs px))
    (hmemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    Aes256KeyScheduleCallees P memsetAddr bitsliceAddr pm.fnAddr subBytesAddr px.fnAddr memcpyAddr :=
  ⟨hmemset, bitslice_rep_ok hbitslice, KsHelpers.memshift32_full_ok P pm hmemshift32,
   SboxCode.subBytes_ok hsubBytes, KsHelpers.xorColumns_full_ok P px hxorColumns, hmemcpy⟩

/-- Total-correctness Hoare specification for `fixslice64::aes256_key_schedule`. -/
@[expose] def aes256KeyScheduleSpec : Spec (Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, outPtr, keyPtr, key) s0 =>
    ⌜s0.readReg64 .x0 = keyPtr ∧ s0.readReg64 .x8 = outPtr ∧ key.length = 32⌝ ∗
    (bytesAt ro keyPtr key ∗ memRegion outPtr 960 ∗ stackFrameAt s0.sp 1120)
  post := fun (ro, outPtr, keyPtr, key) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (bytesAt ro keyPtr key ∗ fsKeys256At outPtr (Model.aes256KeyScheduleFs key) ∗ stackFrameAt s0.sp 1120)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 2. Bitwise Normalization & Memory-Layout Lemmas -/

namespace Simp
@[scoped simp, scoped arm64_norm] theorem orn_xzr_eq_xor_ones (x : BitVec 64) :
    0#64 ||| ~~~x = x ^^^ 0xffffffffffffffff#64 := by bv_slice
@[scoped simp, scoped arm64_norm] theorem not_eq_xor_ones (x : BitVec 64) :
    ~~~x = x ^^^ 0xffffffffffffffff#64 := by bv_slice
@[scoped simp, scoped arm64_norm] theorem add_shl8_sr3_xor (x : BitVec 64) :
    (((x ^^^ (x >>> 8)) &&& 0x000f00ff00f00000#64) +
      (((x ^^^ (x >>> 8)) &&& 0x000f00ff00f00000#64) <<< 8)) ^^^ x =
      Model.deltaSwap1 x 8 0x000f00ff00f00000#64 := by dsimp only [Model.deltaSwap1]; bv_robdd
@[scoped simp, scoped arm64_norm] theorem add_shl8_sr1_xor (x : BitVec 64) :
    (((x ^^^ (x >>> 8)) &&& 0x00f000ff000f0000#64) +
      (((x ^^^ (x >>> 8)) &&& 0x00f000ff000f0000#64) <<< 8)) ^^^ x =
      Model.deltaSwap1 x 8 0x00f000ff000f0000#64 := by dsimp only [Model.deltaSwap1]; bv_robdd
@[scoped simp, scoped arm64_norm] theorem add_shl4_xor (x : BitVec 64) :
    (((x ^^^ (x >>> 4)) &&& 0x0f0f00000f0f0000#64) +
      (((x ^^^ (x >>> 4)) &&& 0x0f0f00000f0f0000#64) <<< 4)) ^^^ x =
      Model.deltaSwap1 x 4 0x0f0f00000f0f0000#64 := by dsimp only [Model.deltaSwap1]; bv_robdd
@[scoped simp, scoped arm64_norm] theorem orr_shl8_sr2_xor (x : BitVec 64) :
    (((x ^^^ (x >>> 8)) &&& 0x00ff000000ff0000#64) |||
      (((x ^^^ (x >>> 8)) &&& 0x00ff000000ff0000#64) <<< 8)) ^^^ x =
      Model.deltaSwap1 x 8 0x00ff000000ff0000#64 := by dsimp only [Model.deltaSwap1]; bv_slice
@[scoped simp, scoped arm64_norm] theorem sp_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl
@[scoped simp, scoped arm64_norm] theorem sp_setMem (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl
@[scoped simp, scoped arm64_norm] theorem sp_writeReg64_gpr (s : State) (n : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr n) v).sp = s.sp := by simp [State.writeReg64]
@[scoped simp, scoped arm64_norm] theorem sp_writeReg64_sp (s : State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := rfl
end Simp

private theorem subBytesNots_struct_eq (st : Model.FsState) :
    { st with s0 := st.s0 ^^^ 0xffffffffffffffff#64, s1 := st.s1 ^^^ 0xffffffffffffffff#64,
              s5 := st.s5 ^^^ 0xffffffffffffffff#64, s6 := st.s6 ^^^ 0xffffffffffffffff#64 } =
      Model.subBytesNots st := by
  cases st; simp [Model.subBytesNots, Model.FsState.zipWith, Model.notsMask]

private def ksStackCells (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) : SepProp :=
  ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
  ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗ ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
  ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)

private def ksSavedFrame (s0 : State) (pad : BitVec 64) : SepProp :=
  ksStackCells s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 (.gpr 28#5)) pad
    (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5)) (s0.readReg64 (.gpr 22#5))
    (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))

private theorem stackFrameAt_80 (sp : BitVec 64) :
    stackFrameAt sp 80 = (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64,
      ∃∗ v7 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
      ksStackCells sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont, ksStackCells]

private theorem stackFrameAt_80_split16 (sp : BitVec 64) :
    stackFrameAt sp 80 = stackFrameAt sp 16 ∗ stackFrameAt (sp - 16#64) 64 :=
  stackFrameAt_split sp 16 64

private theorem ksSavedFrame_entails_stackFrameAt80 (s0 : State) (pad : BitVec 64) :
    ksSavedFrame s0 pad ⊢ stackFrameAt s0.sp 80 := by
  rw [stackFrameAt_80]; dsimp only [ksSavedFrame]
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.refl _))))))))))

private theorem stackFrameAt_1120_split (sp0 : BitVec 64) :
    stackFrameAt sp0 1120 = stackFrameAt sp0 80 ∗ memRegion (sp0 - 1040#64) 64 ∗
      memRegion (sp0 - 1040#64 + 0x40#64) 64 ∗ memRegion (sp0 - 1040#64 + 0x80#64) 832 ∗
      stackFrameAt (sp0 - 1040#64) 80 := by
  have hsub : sp0 - 80#64 - 960#64 = sp0 - 1040#64 := by bv_lin
  rw [show (1120 : Nat) = 80 + (960 + 80) from rfl, stackFrameAt_split sp0 80 (960 + 80),
      stackFrameAt_split (sp0 - 80#64) 960 80, stackFrameAt_eq_memRegion (sp0 - 80#64) 960, hsub,
      show (960 : Nat) = 64 + (64 + 832) from rfl,
      memRegion_split (sp0 - 1040#64) 64 (64 + 832) (by decide),
      memRegion_split (sp0 - 1040#64 + 64#64) 64 832 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl

private theorem stackFrameAt_1120_merge (s0 : State) (pad : BitVec 64) (ks : FsKeys256) :
    ((s0.sp - 1040#64) ↦ₛ fsKeys256Bytes ks) ∗ stackFrameAt (s0.sp - 1040#64) 80 ∗
      ksSavedFrame s0 pad ⊢ stackFrameAt s0.sp 1120 := by
  have hsub : s0.sp - 80#64 - 960#64 = s0.sp - 1040#64 := by bv_lin
  have h1 : ((s0.sp - 1040#64) ↦ₛ fsKeys256Bytes ks) ⊢ stackFrameAt (s0.sp - 80#64) 960 := by
    rw [stackFrameAt_eq_memRegion (s0.sp - 80#64) 960, hsub, ← fsKeys256Bytes_length ks]
    exact pointsToBytes_entails_memRegion (s0.sp - 1040#64) (fsKeys256Bytes ks)
  rw [show (1120 : Nat) = 80 + (960 + 80) from rfl, stackFrameAt_split s0.sp 80 (960 + 80),
      stackFrameAt_split (s0.sp - 80#64) 960 80, hsub]
  have hreord : stackFrameAt s0.sp 80 ∗ (stackFrameAt (s0.sp - 80#64) 960 ∗ stackFrameAt (s0.sp - 1040#64) 80) =
      stackFrameAt (s0.sp - 80#64) 960 ∗ (stackFrameAt (s0.sp - 1040#64) 80 ∗ stackFrameAt s0.sp 80) := by
    sep_ac_rfl
  rw [hreord]; exact sepConj_mono h1 (sepConj_mono (Entails.refl _) (ksSavedFrame_entails_stackFrameAt80 s0 pad))

private def ksInitMemRegions (spLocal : BitVec 64) : SepProp :=
  memRegion (spLocal + 0x0c0#64) 64 ∗ memRegion (spLocal + 0x100#64) 64 ∗
  memRegion (spLocal + 0x140#64) 64 ∗ memRegion (spLocal + 0x180#64) 64 ∗
  memRegion (spLocal + 0x1c0#64) 64 ∗ memRegion (spLocal + 0x200#64) 64 ∗
  memRegion (spLocal + 0x240#64) 64 ∗ memRegion (spLocal + 0x280#64) 64 ∗
  memRegion (spLocal + 0x2c0#64) 64 ∗ memRegion (spLocal + 0x300#64) 64 ∗
  memRegion (spLocal + 0x340#64) 64 ∗ memRegion (spLocal + 0x380#64) 64

private theorem pointsToBytes_zero832_entails_slots (spLocal : BitVec 64) :
    ((spLocal + 0x080#64) ↦ₛ List.replicate 832 0#8) ⊢
      memRegion (spLocal + 0x080#64) 64 ∗ ksInitMemRegions spLocal := by
  have h1 : ((spLocal + 0x080#64) ↦ₛ List.replicate 832 0#8) ⊢ memRegion (spLocal + 0x080#64) 832 := by
    have h0 := pointsToBytes_entails_memRegion (spLocal + 0x080#64) (List.replicate 832 0#8)
    rwa [List.length_replicate] at h0
  have hsplit : memRegion (spLocal + 0x080#64) 832 =
      memRegion (spLocal + 0x080#64) 64 ∗ ksInitMemRegions spLocal := by
    dsimp only [ksInitMemRegions]
    rw [show (832 : Nat) = 64 + (64 + (64 + (64 + (64 + (64 + (64 + (64 + (64 + (64 + (64 + (64 + 64))))))))))) from rfl,
        memRegion_split _ 64 _ (by decide), memRegion_split _ 64 _ (by decide),
        memRegion_split _ 64 _ (by decide), memRegion_split _ 64 _ (by decide),
        memRegion_split _ 64 _ (by decide), memRegion_split _ 64 _ (by decide),
        memRegion_split _ 64 _ (by decide), memRegion_split _ 64 _ (by decide),
        memRegion_split _ 64 _ (by decide), memRegion_split _ 64 _ (by decide),
        memRegion_split _ 64 _ (by decide), memRegion_split _ 64 64 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rwa [hsplit] at h1

/-- Local state invariant maintained from `[7]` (`sp = s0.sp - 1040#64`) through `[502]`. -/
private structure KsInv (s0 s : State) : Prop where
  pure : PureStepPreserved s0 s
  sp_eq : s.sp = s0.sp - 1040#64
  sp_al : s.spAligned = true
  x25 : s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0

private theorem KsInv.of_step {s0 s1 s2 : State} (h1 : KsInv s0 s1)
    (hp : pureStepProj s2 = pureStepProj s1 := by simp [wp_norm, arm64_norm])
    (hm : s2.mem.perm = s1.mem.perm := by simp [wp_norm, arm64_norm])
    (hsp : s2.sp = s1.sp := by simp [wp_norm, arm64_norm])
    (hx25 : s2.readReg64 (.gpr 25#5) = s1.readReg64 (.gpr 25#5) := by simp [wp_norm, arm64_norm])
    (hx26 : s2.readReg64 (.gpr 26#5) = s1.readReg64 (.gpr 26#5) := by simp [wp_norm, arm64_norm])
    (hx27 : s2.readReg64 (.gpr 27#5) = s1.readReg64 (.gpr 27#5) := by simp [wp_norm, arm64_norm])
    (hv : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp [wp_norm, arm64_norm]) :
    KsInv s0 s2 :=
  ⟨h1.pure.trans (PureStepPreserved.of_proj_perm hp hm), hsp.trans h1.sp_eq,
   by simp only [State.spAligned, hsp]; exact h1.sp_al,
   hx25.trans h1.x25, hx26.trans h1.x26, hx27.trans h1.x27, hv.trans h1.vregs⟩

private theorem KsInv.of_call {s0 s1 s2 : State} (h1 : KsInv s0 s1)
    (hsp : s2.sp = s1.sp) (hcs : CalleeSavedPreserved s1 s2) (hpure : PureStepPreserved s1 s2) :
    KsInv s0 s2 :=
  ⟨h1.pure.trans hpure, hsp.trans h1.sp_eq, by simp only [State.spAligned, hsp]; exact h1.sp_al,
   hcs.readReg64_x25.trans h1.x25, hcs.readReg64_x26.trans h1.x26, hcs.readReg64_x27.trans h1.x27,
   hcs.vregs.trans h1.vregs⟩

private theorem KsInv.sp0_and_15 {s0 s : State} (h : KsInv s0 s) : s0.sp &&& 15#64 = 0#64 := by
  have h1 := sp_and_15_of_spAligned h.sp_al; rw [h.sp_eq] at h1; revert h1; bv_bits

private theorem KsInv.sp_local_and_15 {s0 s : State} (h : KsInv s0 s) :
    (s0.sp - 1040#64) &&& 15#64 = 0#64 := by
  rw [← h.sp_eq]; exact sp_and_15_of_spAligned h.sp_al

private meta partial def flattenSepConj (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    flattenSepConj (e.getArg! 1) (flattenSepConj (e.getArg! 0) acc)
  else if e.isConstOf ``Arm64.SepProp.emp then acc else acc.push e

private meta def mkSepConjProd (xs : Array Lean.Expr) : Lean.Expr :=
  if h : xs.size = 0 then Lean.mkConst ``Arm64.SepProp.emp
  else xs[1:].foldl (fun acc x => Lean.mkApp2 (Lean.mkConst ``Arm64.SepProp.sepConj) acc x) xs[0]

local elab "ks_focus" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq?
      | Lean.Meta.throwTacticEx `ks_focus g "expected equality `Full = A ∗ ?F`"
    let rhsAtoms := flattenSepConj rhs
    if rhsAtoms.size > 0 then
      let fExpr := rhsAtoms.back!.consumeMData
      if fExpr.isMVar then
        let mut pool := flattenSepConj lhs
        for req in rhsAtoms.pop do
          let mut found : Option Nat := none
          for idx in [:pool.size] do
            if found.isNone && pool[idx]! == req then found := some idx
          if found.isNone then
            for idx in [:pool.size] do
              if found.isNone then
                if (← Lean.Meta.isDefEq pool[idx]! req) then found := some idx
          if let some idx := found then pool := pool.eraseIdxIfInBounds idx
          else Lean.Meta.throwTacticEx `ks_focus g m!"missing atom in precondition: {req}"
        fExpr.mvarId!.assign (mkSepConjProd pool)
    Lean.Elab.Tactic.evalTactic (← `(tactic| sep_ac_rfl))

private theorem pureStepPreserved_of_bl_entry {s sf : State} {lrVal calleeAddr : BitVec 64}
    (h : PureStepPreserved ((s.writeReg64 .lr lrVal).setPC calleeAddr) sf) : PureStepPreserved s sf :=
  ⟨by cases s; exact h.1, by cases s; exact h.2⟩

private theorem step_bl_call {α : Type} {P : Program}
    {blPc calleeAddr target_pc : BitVec 64} {spec : Spec α}
    (hbl : hasInstrs P blPc [ .bl (calleeAddr - blPc) ]) (hcall : subroutine_ok P calleeAddr spec) (x : α)
    {s : State} {Full A A' F : SepProp} {φ : Prop} {ψ : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hpre_eq : spec.pre x ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) = (⌜φ⌝ ∗ A))
    (hpost_eq : ∀ sf, spec.post x ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) sf = (⌜ψ sf⌝ ∗ A'))
    (hFull : Full = A ∗ F) (hφ : φ)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ψ sf → SepWP P target_pc sf (A' ∗ F) post oom)
    (hno : ∀ se, spec.onPanic x se = (fun _ => ⌜False⌝) := by intro _; exact rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by exact rfl)
    (h_no_oom : ∀ se sf, spec.onOom x se sf = ⌜False⌝ := by intro _ _; exact rfl) :
    SepWP P target_pc s Full post oom := by
  have hf : P.fetch s.pc = some (.bl (calleeAddr - blPc)) := by
    rw [hpc]; simpa [hasInstrs] using hbl 0 (Nat.zero_lt_succ 0)
  apply SepWP.of_reaches_pc; intro R hm; apply reaches_pc_step hrun hf
  let s' : State := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  have hadd : blPc + (calleeAddr - blPc) = calleeAddr := by bv_lin
  have heval : P.evalInst (.bl (calleeAddr - blPc)) s = s' := by
    simp [Program.evalInst, execInstWithSvc, State.setPC, State.writeReg64, hpc, hadd, s']
  rw [heval]
  have hm' : s'.mem ⊨ Full ∗ R := by
    have : s'.mem = s.mem := by cases s; rfl
    rw [this]; exact hm
  refine SepWP.to_reaches_pc ?_ hm'
  refine SepWP.call_framed_mut hcall x hpre_eq hpost_eq hFull hφ
    (by cases s; rfl) (by cases s; exact hrun) (by cases s; exact hsp_al) (by cases s; rfl)
    ?_ (hno s') h_no_exit ?_
  · intro sf hpc' hrun' hsp' hcs' hψ
    have hsp_s : sf.sp = s.sp := hsp'.trans (by cases s; rfl)
    have hcs_s : CalleeSavedPreserved s sf :=
      (show CalleeSavedPreserved s' sf ↔ CalleeSavedPreserved s sf by cases s; rfl).mp hcs'
    exact hnext sf hpc' hrun' hsp_s hcs_s hψ
  · intro R' sf _ hsat; rw [h_no_oom s' sf] at hsat; exact False.elim (not_satisfies_false_sepConj hsat)

section
arm64_proof_prelude
open scoped CodeCommon.Simp Simp

/-! ## 3. Prologue, `memset`, `bitslice` × 2, and `memshift32` Initialization (`[0..32]`) -/

private theorem ks_prologue_memset {P : Program}
    {fnAddr memsetAddr target_pc keyPtr outPtr : BitVec 64}
    {ro : Bool} {key : List (BitVec 8)} {s0 : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc0 : hasInstrs P fnAddr (decodeWords ksSeg0Words))
    (hbl0 : hasInstrs P (fnAddr + 0x034#64) [ .bl (memsetAddr - (fnAddr + 0x034#64)) ])
    (hmemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = keyPtr) (hx8 : s0.readReg64 .x8 = outPtr)
    (hnext : ∀ (pad : BitVec 64) (s1 : State),
      s1.pc = fnAddr + 0x038#64 → s1.status = .Running → KsInv s0 s1 →
      s1.readReg64 (.gpr 19#5) = outPtr → s1.readReg64 (.gpr 20#5) = keyPtr →
      s1.readReg64 (.gpr 21#5) = s0.sp - 1040#64 →
      SepWP P target_pc s1
        (bytesAt ro keyPtr key ∗ memRegion outPtr 960 ∗ memRegion (s0.sp - 1040#64) 64 ∗
         memRegion (s0.sp - 1040#64 + 0x40#64) 64 ∗
         ((s0.sp - 1040#64 + 0x80#64) ↦ₛ List.replicate 832 0#8) ∗
         stackFrameAt (s0.sp - 1040#64) 80 ∗ ksSavedFrame s0 pad) post oom) :
    SepWP P target_pc s0
      (bytesAt ro keyPtr key ∗ memRegion outPtr 960 ∗ stackFrameAt s0.sp 1120) post oom := by
  have hsp_and := sp_and_15_of_spAligned hsp0
  have hsp80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hsp_and; bv_bits
  rw [stackFrameAt_1120_split s0.sp, stackFrameAt_80 s0.sp]
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v0; apply SepWP.exists_left; intro v1; apply SepWP.exists_left; intro v2
  apply SepWP.exists_left; intro pad; apply SepWP.exists_left; intro v4; apply SepWP.exists_left; intro v5
  apply SepWP.exists_left; intro v6; apply SepWP.exists_left; intro v7; apply SepWP.exists_left; intro v8
  apply SepWP.exists_left; intro v9; have_instrs hc0 0 13; dsimp only [ksStackCells]
  wp_stp64 hf_0 m0 hm0; wp_str64 hf_1 m1 hm1; wp_stp64 hf_2 m2 hm2
  wp_stp64 hf_3 m3 hm3; wp_stp64 hf_4 m4 hm4; wp_steps 8
  refine step_bl_call hbl0 hmemset (s0.sp - 1040#64 + 0x80#64, 0#8, 832)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm]) (hrun := by simp [wp_norm, arm64_norm, hrun])
    (hsp_al := by simp only [State.spAligned, wp_norm, arm64_norm]; revert hsp_and; bv_bits)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl) (hFull := by simp only [bv_lin_norm]; ks_focus)
    (hφ := ⟨by simp [wp_norm, arm64_norm, bv_lin_norm], by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm], by decide⟩) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 hψ1
  have hinv1 : KsInv s0 sf1 :=
    KsInv.of_call ⟨PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1, hm0]),
      by simp [wp_norm, arm64_norm, bv_lin_norm],
      by simp only [State.spAligned, wp_norm, arm64_norm]; revert hsp_and; bv_bits,
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
      hsp1 hcs1 (pureStepPreserved_of_bl_entry hψ1.2)
  refine (congrArg (fun Pre => SepWP P target_pc sf1 Pre post oom) ?_).mpr
    (hnext pad sf1 (by simpa [bv_lin_norm] using hpc1) hrun1 hinv1
      (by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm])
      (by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm])
      (by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm, bv_lin_norm]))
  dsimp only [ksSavedFrame, ksStackCells]; simp only [bv_lin_norm]; sep_ac_rfl

private theorem ks_bitslice_init {P : Program}
    {fnAddr bitsliceAddr memshift32Addr target_pc keyPtr outPtr : BitVec 64}
    {ro : Bool} {key : List (BitVec 8)} {s0 s1 : State} {Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc1 : hasInstrs P (fnAddr + 0x038#64) (decodeWords ksSeg1Words))
    (hbl1 : hasInstrs P (fnAddr + 0x04c#64) [ .bl (bitsliceAddr - (fnAddr + 0x04c#64)) ])
    (hc2 : hasInstrs P (fnAddr + 0x050#64) (decodeWords ksSeg2Words))
    (hbl2 : hasInstrs P (fnAddr + 0x064#64) [ .bl (bitsliceAddr - (fnAddr + 0x064#64)) ])
    (hc3 : hasInstrs P (fnAddr + 0x068#64) (decodeWords ksSeg3Words))
    (hbl3 : hasInstrs P (fnAddr + 0x074#64) [ .bl (memshift32Addr - (fnAddr + 0x074#64)) ])
    (hc4 : hasInstrs P (fnAddr + 0x078#64) (decodeWords ksLoopInitWords))
    (hbitslice : subroutine_ok P bitsliceAddr bitsliceRepSpec)
    (hmemshift : subroutine_ok P memshift32Addr memshift32Spec)
    (hpc : s1.pc = fnAddr + 0x038#64) (hrun : s1.status = .Running)
    (hinv1 : KsInv s0 s1) (hkey : key.length = 32)
    (hx19 : s1.readReg64 (.gpr 19#5) = outPtr) (hx20 : s1.readReg64 (.gpr 20#5) = keyPtr)
    (hx21 : s1.readReg64 (.gpr 21#5) = s0.sp - 1040#64)
    (hnext : ∀ s2 : State,
      s2.pc = fnAddr + 0x084#64 → s2.status = .Running → KsInv s0 s2 →
      s2.readReg64 (.gpr 19#5) = outPtr → s2.readReg64 (.gpr 20#5) = 0#64 →
      s2.readReg64 (.gpr 21#5) = s0.sp - 1040#64 →
      s2.readReg64 (.gpr 22#5) = 0xffffffffffffffa0#64 → s2.readReg64 (.gpr 23#5) = 0x80#64 →
      SepWP P target_pc s2
        (bytesAt ro keyPtr key ∗
         fsStateAt (s0.sp - 1040#64) (Model.bitslice (Blocks4.replicate (key.take 16))) ∗
         fsStateAt (s0.sp - 1040#64 + 0x040#64) (Model.bitslice (Blocks4.replicate (key.drop 16))) ∗
         fsStateAt (s0.sp - 1040#64 + 0x080#64) (Model.bitslice (Blocks4.replicate (key.drop 16))) ∗
         ksInitMemRegions (s0.sp - 1040#64) ∗ stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom) :
    SepWP P target_pc s1
      (bytesAt ro keyPtr key ∗ memRegion (s0.sp - 1040#64) 64 ∗
       memRegion (s0.sp - 1040#64 + 0x40#64) 64 ∗
       ((s0.sp - 1040#64 + 0x80#64) ↦ₛ List.replicate 832 0#8) ∗
       stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom := by
  let spLocal : BitVec 64 := s0.sp - 1040#64
  have hlen0 : (key.take 16).length = 16 := by simp [hkey]
  have hlen1 : (key.drop 16).length = 16 := by simp [hkey]
  have hkey_split : bytesAt ro keyPtr key =
      bytesAt ro keyPtr (key.take 16) ∗ bytesAt ro (keyPtr + 16#64) (key.drop 16) := by
    conv => lhs; rw [(List.take_append_drop 16 key).symm]
    rw [bytesAt_append, hlen0]
  refine SepWP.repack_pre (pointsToBytes_zero832_entails_slots spLocal) (by dsimp only [spLocal]; sep_ac_rfl) ?_
  rw [hkey_split]; have_instrs hc1 0 5; wp_steps 5
  refine step_bl_call hbl1 hbitslice (ro, spLocal, keyPtr, key.take 16)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm]) (hrun := by simp [wp_norm, arm64_norm, hrun])
    (hsp_al := by simpa [State.spAligned, wp_norm, arm64_norm] using hinv1.sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl) (hFull := by dsimp only [spLocal]; simp only [bv_lin_norm]; ks_focus)
    (hφ := ⟨by dsimp only [spLocal]; simp [wp_norm, arm64_norm, hinv1.sp_eq], by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], hlen0⟩) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 hψ1
  have hinv_a := KsInv.of_call (KsInv.of_step hinv1) hsp1 hcs1 (pureStepPreserved_of_bl_entry hψ1)
  have hx19_1 : sf1.readReg64 (.gpr 19#5) = outPtr := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]; exact hx19
  have hx20_1 : sf1.readReg64 (.gpr 20#5) = keyPtr := by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]; exact hx20
  have hx21_1 : sf1.readReg64 (.gpr 21#5) = spLocal := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm]; exact hx21
  have hpc1' : sf1.pc = fnAddr + 0x050#64 := by simpa [bv_lin_norm] using hpc1
  have_instrs hc2 0 5; wp_steps 5
  refine step_bl_call hbl2 hbitslice (ro, spLocal + 0x40#64, keyPtr + 16#64, key.drop 16)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm]) (hrun := by simp [wp_norm, arm64_norm, hrun1])
    (hsp_al := by simpa [State.spAligned, wp_norm, arm64_norm] using hinv_a.sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl) (hFull := by dsimp only [spLocal]; simp only [bv_lin_norm]; ks_focus)
    (hφ := ⟨by simp [wp_norm, arm64_norm, bv_lin_norm], by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], hlen1⟩) ?_
  intro sf2 hpc2 hrun2 hsp2 hcs2 hψ2
  have hinv_b := KsInv.of_call (KsInv.of_step hinv_a) hsp2 hcs2 (pureStepPreserved_of_bl_entry hψ2)
  have hx19_2 : sf2.readReg64 (.gpr 19#5) = outPtr := by rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm]; exact hx19_1
  have hx21_2 : sf2.readReg64 (.gpr 21#5) = spLocal := by rw [hcs2.readReg64_x21]; simp [wp_norm, arm64_norm]; exact hx21_1
  have hpc2' : sf2.pc = fnAddr + 0x068#64 := by simpa [bv_lin_norm] using hpc2
  have_instrs hc3 0 3; wp_steps 3
  refine step_bl_call hbl3 hmemshift (spLocal, 120, 8, Model.bitslice (Blocks4.replicate (key.drop 16)))
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm]) (hrun := by simp [wp_norm, arm64_norm, hrun2])
    (hsp_al := by simpa [State.spAligned, wp_norm, arm64_norm] using hinv_b.sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by
      dsimp only [spLocal]; rw [stackFrameAt_80_split16]
      simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, Nat.reduceAdd, Nat.reduceMul, hinv_b.sp_eq, bv_lin_norm]; ks_focus)
    (hφ := ⟨by dsimp only [spLocal]; simp [wp_norm, arm64_norm, hinv1.sp_eq],
            by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by decide, by decide, by decide⟩) ?_
  intro sf3 hpc3 hrun3 hsp3 hcs3 hψ3
  have hinv_c := KsInv.of_call (KsInv.of_step hinv_b) hsp3 hcs3 (pureStepPreserved_of_bl_entry hψ3)
  have hx19_3 : sf3.readReg64 (.gpr 19#5) = outPtr := by rw [hcs3.readReg64_x19]; simp [wp_norm, arm64_norm]; exact hx19_2
  have hx21_3' : sf3.readReg64 (.gpr 21#5) = spLocal := by rw [hcs3.readReg64_x21]; simp [wp_norm, arm64_norm]; exact hx21_2
  have hpc3' : sf3.pc = fnAddr + 0x078#64 := by simpa [bv_lin_norm] using hpc3
  have_instrs hc4 0 3; wp_steps 3
  refine SepWP.congr_pre ?_
    (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun3])
      (KsInv.of_step hinv_c) (by simp [wp_norm, arm64_norm]; exact hx19_3)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]; exact hx21_3')
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
  rw [hkey_split]; dsimp only [spLocal]; rw [stackFrameAt_80_split16]
  simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, Nat.reduceAdd, Nat.reduceMul, hinv_b.sp_eq, bv_lin_norm]; sep_ac_rfl

/-! ## 4. 7-Iteration `rcon` Key-Expansion Loop (`[33..81]`, `0x084..0x144`) -/

private theorem fsStateAt_unfold (ptr : BitVec 64) (st : Model.FsState) :
    fsStateAt ptr st = ((ptr ↦₆₄ st.s0) ∗ ((ptr + 8#64) ↦₆₄ st.s1) ∗ ((ptr + 16#64) ↦₆₄ st.s2) ∗
      ((ptr + 24#64) ↦₆₄ st.s3) ∗ ((ptr + 32#64) ↦₆₄ st.s4) ∗ ((ptr + 40#64) ↦₆₄ st.s5) ∗
      ((ptr + 48#64) ↦₆₄ st.s6) ∗ ((ptr + 56#64) ↦₆₄ st.s7)) := rfl

private theorem off8_eq (spLocal : BitVec 64) (i k : Nat) :
    spLocal + BitVec.ofNat 64 (8 * (16 * i + k)) =
      (spLocal + BitVec.ofNat 64 (128 * i)) + BitVec.ofNat 64 (8 * k) := by
  rw [Nat.left_distrib, show 8 * (16 * i) = 128 * i by omega, BitVec.ofNat_add, BitVec.add_assoc]

private theorem ks_rcon_bit_step {P : Program} {pc0 target_pc spLocal : BitVec 64}
    {i : Nat} (hi : i < 7) {st : Model.FsState} {s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc_mid : hasInstrs P pc0 (decodeWords ksRconEvenMidWords))
    (hpc : s.pc = pc0 + 52#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 (.gpr 21#5) = spLocal)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (128 + 136 * i))
    (hnext : ∀ s' : State, s'.pc = pc0 + 64#64 → s'.status = .Running →
      pureStepProj s' = pureStepProj s → s'.mem.perm = s.mem.perm → s'.sp = s.sp →
      (∀ r : BitVec 5, r ≠ 8#5 → s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      s'.readReg32 .x4 = s.readReg32 .x4 → calleeSavedVRegs s' = calleeSavedVRegs s →
      SepWP P target_pc s'
        (fsStateAt ((spLocal + BitVec.ofNat 64 (128 * i)) + 128#64)
          (Model.addRoundConstantBit st i) ∗ Rest) post oom) :
    SepWP P target_pc s (fsStateAt ((spLocal + BitVec.ofNat 64 (128 * i)) + 128#64) st ∗ Rest) post oom := by
  have_instrs hc_mid 13 3
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [fsStateAt_unfold]; wp_steps 2; wp_str64 hf_15 m3 hm3
    refine SepWP.congr_pre ?_
      (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm3])
        (by simp [wp_norm, arm64_norm]) (fun r hr => by simp [wp_norm, arm64_norm, hr])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
    rw [fsStateAt_unfold]; dsimp only [Model.addRoundConstantBit]; simp only [Nat.reduceMul, bv_lin_norm]

private theorem ks_rcon_even {P : Program}
    {fnAddr subBytesAddr xorColumnsAddr target_pc outPtr : BitVec 64}
    {i : Nat} (hi : i < 7) {rkPrev2 rkPrev1 : Model.FsState} {s0 s : State} {Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc_pre : hasInstrs P (fnAddr + 0x084#64) (decodeWords ksRconEvenPreWords))
    (hbl_sb : hasInstrs P (fnAddr + 0x08c#64) [ .bl (subBytesAddr - (fnAddr + 0x08c#64)) ])
    (hc_mid : hasInstrs P (fnAddr + 0x090#64) (decodeWords ksRconEvenMidWords))
    (hbl_xc : hasInstrs P (fnAddr + 0x0d0#64) [ .bl (xorColumnsAddr - (fnAddr + 0x0d0#64)) ])
    (hsub : subroutine_ok P subBytesAddr subBytesSpec)
    (hxor : subroutine_ok P xorColumnsAddr xorColumnsSpec)
    (hpc : s.pc = fnAddr + 0x084#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (128 * i))
    (hx21 : s.readReg64 (.gpr 21#5) = s0.sp - 1040#64)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (16 * i) - 96#64)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (128 + 136 * i))
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x0d4#64 → s'.status = .Running → KsInv s0 s' →
      s'.readReg64 (.gpr 19#5) = outPtr → s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (128 * i) →
      s'.readReg64 (.gpr 21#5) = s0.sp - 1040#64 →
      s'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (16 * i) - 96#64 →
      s'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (128 + 136 * i) →
      s'.readReg64 (.gpr 24#5) = (s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) →
      SepWP P target_pc s'
        (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i)) rkPrev2 ∗
         fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 128#64) (Model.ksEvenStep rkPrev2 rkPrev1 i) ∗
         stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom) :
    SepWP P target_pc s
      (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i)) rkPrev2 ∗
       fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 128#64) rkPrev1 ∗
       stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom := by
  let spLocal : BitVec 64 := s0.sp - 1040#64
  let baseI : BitVec 64 := spLocal + BitVec.ofNat 64 (128 * i)
  have_instrs hc_pre 0 2; wp_steps 2
  refine step_bl_call hbl_sb hsub (baseI + 128#64, rkPrev1)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm]) (hrun := by simp [wp_norm, arm64_norm, hrun])
    (hsp_al := by simpa [State.spAligned, wp_norm, arm64_norm] using hinv.sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by dsimp only [baseI, spLocal]; simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hinv.sp_eq, bv_lin_norm]; ks_focus)
    (hφ := by dsimp only [baseI, spLocal]; simp [wp_norm, arm64_norm, bv_lin_norm]) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 hψ1
  have hinv1 := KsInv.of_call (KsInv.of_step hinv) hsp1 hcs1 (pureStepPreserved_of_bl_entry hψ1)
  have hx19_1 : sf1.readReg64 (.gpr 19#5) = outPtr := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]; exact hx19
  have hx20_1 : sf1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (128 * i) := by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]; exact hx20
  have hx21_1 : sf1.readReg64 (.gpr 21#5) = spLocal := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm]; exact hx21
  have hx22_1 : sf1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (16 * i) - 96#64 := by rw [hcs1.readReg64_x22]; simp [wp_norm, arm64_norm]; exact hx22
  have hx23_1 : sf1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (128 + 136 * i) := by rw [hcs1.readReg64_x23]; simp [wp_norm, arm64_norm]; exact hx23
  have hx24_1 : sf1.readReg64 (.gpr 24#5) = baseI := by rw [hcs1.readReg64_x24]; dsimp only [baseI, spLocal]; simp [wp_norm, arm64_norm]
  have hpc1' : sf1.pc = fnAddr + 0x090#64 := by simpa [bv_lin_norm] using hpc1
  have hsp_sf1 : sf1.sp = spLocal := hinv1.sp_eq
  have_instrs hc_mid 0 13; rw [fsStateAt_unfold (baseI + 128#64)]
  wp_steps 9; wp_stp64 hf_9 m1 hm1; wp_steps 2; wp_stp64 hf_12 m2 hm2
  refine SepWP.congr_pre ?_
    (ks_rcon_bit_step (st := Model.subBytesNots (Model.subBytesFs rkPrev1))
      (Rest := stackFrameAt spLocal 80 ∗ (fsStateAt baseI rkPrev2 ∗ Frame)) hi hc_mid
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm]; exact hx21_1) (by simp [wp_norm, arm64_norm]; exact hx23_1) ?_)
  · rw [← subBytesNots_struct_eq, fsStateAt_unfold]; dsimp only [baseI, spLocal]
    simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hinv.sp_eq, bv_lin_norm]; sep_ac_rfl
  intro sb hpcb hrunb hpb hperm_b hsp_b hreg_b hx4_b hv_b
  have hinv_b : KsInv s0 sb :=
    KsInv.of_step hinv1 (hp := hpb.trans (by simp [wp_norm, arm64_norm]))
      (hm := hperm_b.trans (by simp [wp_norm, arm64_norm, hm2, hm1]))
      (hsp := hsp_b.trans (by simp [wp_norm, arm64_norm]))
      (hx25 := (hreg_b 25#5 (by decide)).trans (by simp [wp_norm, arm64_norm]))
      (hx26 := (hreg_b 26#5 (by decide)).trans (by simp [wp_norm, arm64_norm]))
      (hx27 := (hreg_b 27#5 (by decide)).trans (by simp [wp_norm, arm64_norm]))
      (hv := hv_b.trans (by simp [wp_norm, arm64_norm]))
  have hoff_prev : spLocal + BitVec.ofNat 64 (8 * (16 * i + 16 - 16)) = baseI := by
    rw [show 16 * i + 16 - 16 = 16 * i + 0 by omega, off8_eq]; dsimp only [baseI]; simp
  have hoff_cur : spLocal + BitVec.ofNat 64 (8 * (16 * i + 16)) = baseI + 128#64 := by rw [off8_eq]
  refine step_bl_call hbl_xc hxor
      (spLocal, 120, 16 * i + 16, 16, 28, rkPrev2, Model.addRoundConstantBit (Model.subBytesNots (Model.subBytesFs rkPrev1)) i)
    (hpc := by simpa [bv_lin_norm] using hpcb) (hrun := hrunb) (hsp_al := hinv_b.sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by rw [hoff_prev, hoff_cur, stackFrameAt_80_split16]; dsimp only [baseI, spLocal]
                 simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hinv_b.sp_eq, bv_lin_norm]; ks_focus)
    (hφ := ⟨by dsimp only [spLocal]; simp only [wp_norm, arm64_norm]; rw [hreg_b 0#5 (by decide)]; simp only [wp_norm, arm64_norm]; exact hinv.sp_eq,
            by simp only [wp_norm, arm64_norm]; rw [hreg_b 1#5 (by decide)]; simp [wp_norm, arm64_norm],
            by simp only [wp_norm, arm64_norm]; rw [hreg_b 2#5 (by decide)]; simp [wp_norm, arm64_norm, BitVec.ofNat_add],
            by simp only [wp_norm, arm64_norm]; rw [hreg_b 3#5 (by decide)]; simp [wp_norm, arm64_norm],
            by simp only [wp_norm, arm64_norm]; rw [hreg_b 4#5 (by decide)]; simp [wp_norm, arm64_norm],
            by omega, by omega, by omega, by omega, by decide, by decide⟩) ?_
  intro sf2 hpc2 hrun2 hsp2 hcs2 hψ2
  have hinv2 := KsInv.of_call hinv_b hsp2 hcs2 (pureStepPreserved_of_bl_entry hψ2)
  refine SepWP.congr_pre ?_
    (hnext sf2 (by simpa [bv_lin_norm] using hpc2) hrun2 hinv2
      (by rw [hcs2.readReg64_x19, hreg_b 19#5 (by decide)]; simp [wp_norm, arm64_norm]; exact hx19_1)
      (by rw [hcs2.readReg64_x20, hreg_b 20#5 (by decide)]; simp [wp_norm, arm64_norm]; exact hx20_1)
      (by rw [hcs2.readReg64_x21, hreg_b 21#5 (by decide)]; simp [wp_norm, arm64_norm]; exact hx21_1)
      (by rw [hcs2.readReg64_x22, hreg_b 22#5 (by decide)]; simp [wp_norm, arm64_norm]; exact hx22_1)
      (by rw [hcs2.readReg64_x23, hreg_b 23#5 (by decide)]; simp [wp_norm, arm64_norm]; exact hx23_1)
      (by rw [hcs2.readReg64_x24, hreg_b 24#5 (by decide)]; simp [wp_norm, arm64_norm]; exact hx24_1))
  rw [hoff_prev, hoff_cur, stackFrameAt_80_split16]; dsimp only [baseI, spLocal, Model.ksEvenStep, Model.rorDistance]
  simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, Nat.reduceShiftLeft, Nat.reduceAdd, hinv_b.sp_eq, bv_lin_norm]; sep_ac_rfl

private structure KsLoopRegs (s0 : State) (outPtr : BitVec 64) (i : Nat) (s : State) : Prop where
  inv : KsInv s0 s
  x19 : s.readReg64 (.gpr 19#5) = outPtr
  x20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (128 * i)
  x21 : s.readReg64 (.gpr 21#5) = s0.sp - 1040#64
  x22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (16 * i) - 96#64
  x23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (128 + 136 * i)

private theorem KsLoopRegs.of_call {s0 s sf : State} {outPtr : BitVec 64} {i : Nat}
    (hr : KsLoopRegs s0 outPtr i s) (hsp : sf.sp = s.sp)
    (hcs : CalleeSavedPreserved s sf) (hp : PureStepPreserved s sf) :
    KsLoopRegs s0 outPtr i sf :=
  ⟨KsInv.of_call hr.inv hsp hcs hp, hcs.readReg64_x19.trans hr.x19,
   hcs.readReg64_x20.trans hr.x20, hcs.readReg64_x21.trans hr.x21,
   hcs.readReg64_x22.trans hr.x22, hcs.readReg64_x23.trans hr.x23⟩

private structure KsRconCode (P : Program)
    (fnAddr memshift32Addr subBytesAddr xorColumnsAddr : BitVec 64) : Prop where
  epre  : hasInstrs P (fnAddr + 0x084#64) (decodeWords ksRconEvenPreWords)
  esb   : hasInstrs P (fnAddr + 0x08c#64) [ .bl (subBytesAddr - (fnAddr + 0x08c#64)) ]
  emid  : hasInstrs P (fnAddr + 0x090#64) (decodeWords ksRconEvenMidWords)
  exc   : hasInstrs P (fnAddr + 0x0d0#64) [ .bl (xorColumnsAddr - (fnAddr + 0x0d0#64)) ]
  opre1 : hasInstrs P (fnAddr + 0x0d4#64) (decodeWords ksRconOddPre1Words)
  oms1  : hasInstrs P (fnAddr + 0x0e4#64) [ .bl (memshift32Addr - (fnAddr + 0x0e4#64)) ]
  opre2 : hasInstrs P (fnAddr + 0x0e8#64) (decodeWords ksRconOddPre2Words)
  osb   : hasInstrs P (fnAddr + 0x0ec#64) [ .bl (subBytesAddr - (fnAddr + 0x0ec#64)) ]
  omid  : hasInstrs P (fnAddr + 0x0f0#64) (decodeWords ksRconOddMidWords)
  oxc   : hasInstrs P (fnAddr + 0x124#64) [ .bl (xorColumnsAddr - (fnAddr + 0x124#64)) ]
  opost : hasInstrs P (fnAddr + 0x128#64) (decodeWords ksRconOddPostWords)
  oms2  : hasInstrs P (fnAddr + 0x134#64) [ .bl (memshift32Addr - (fnAddr + 0x134#64)) ]
  otail : hasInstrs P (fnAddr + 0x138#64) (decodeWords ksRconTailWords)

private theorem ks_rcon_exit {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc_pre1 : hasInstrs P (fnAddr + 0x0d4#64) (decodeWords ksRconOddPre1Words))
    (hpc : s.pc = fnAddr + 0x0d4#64) (hrun : s.status = .Running)
    (hinv : KsInv s0 s) (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (16 * 6) - 96#64)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x148#64 → s'.status = .Running →
      KsInv s0 s' → s'.readReg64 (.gpr 19#5) = outPtr → SepWP P target_pc s' Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hx22_0 : s.readReg64 (.gpr 22#5) = 0#64 := by simpa using hx22
  have_instrs hc_pre1 0 1; wp_steps 1
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (KsInv.of_step hinv) (by simp [wp_norm, arm64_norm, hx19])

private theorem ks_odd_pre1 {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {i : Nat} (hi : i < 6) {s0 s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc_pre1 : hasInstrs P (fnAddr + 0x0d4#64) (decodeWords ksRconOddPre1Words))
    (hpc : s.pc = fnAddr + 0x0d4#64) (hrun : s.status = .Running) (hr : KsLoopRegs s0 outPtr i s)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i))
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x0e4#64 → s'.status = .Running →
      KsLoopRegs s0 outPtr i s' →
      s'.readReg64 (.gpr 24#5) = (s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) →
      s'.readReg64 (.gpr 0#5) = s0.sp - 1040#64 → s'.readReg64 (.gpr 1#5) = 120#64 →
      s'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 (16 * i + 16) → SepWP P target_pc s' Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr with ⟨hinv, hx19, hx20, hx21, hx22, hx23⟩; have hsp := hinv.sp_eq; have_instrs hc_pre1 0 4
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    wp_steps 4
    exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      ⟨KsInv.of_step hinv, by simp [wp_norm, arm64_norm]; exact hx19, by simp [wp_norm, arm64_norm]; exact hx20,
       by simp [wp_norm, arm64_norm]; exact hx21, by simp [wp_norm, arm64_norm]; exact hx22,
       by simp [wp_norm, arm64_norm]; exact hx23⟩
      (by simpa [wp_norm, arm64_norm, bv_lin_norm] using hx24)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])

private theorem ks_rcon_odd {P : Program}
    {fnAddr memshift32Addr subBytesAddr xorColumnsAddr target_pc outPtr : BitVec 64}
    {i : Nat} (hi : i < 6) {rkPrev1 rkEven : Model.FsState} {s0 s : State} {Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrc : KsRconCode P fnAddr memshift32Addr subBytesAddr xorColumnsAddr)
    (hms : subroutine_ok P memshift32Addr memshift32Spec)
    (hsub : subroutine_ok P subBytesAddr subBytesSpec)
    (hxor : subroutine_ok P xorColumnsAddr xorColumnsSpec)
    (hpc : s.pc = fnAddr + 0x0d4#64) (hrun : s.status = .Running) (hr : KsLoopRegs s0 outPtr i s)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i))
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x084#64 → s'.status = .Running →
      KsLoopRegs s0 outPtr (i + 1) s' →
      SepWP P target_pc s'
        (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 64#64) rkPrev1 ∗
         fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * (i + 1))) rkEven ∗
         fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 192#64) (Model.ksOddStep rkPrev1 rkEven) ∗
         fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * (i + 1)) + 128#64) (Model.ksOddStep rkPrev1 rkEven) ∗
         stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom) :
    SepWP P target_pc s
      (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 64#64) rkPrev1 ∗
       fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 128#64) rkEven ∗
       memRegion ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 192#64) 64 ∗
       memRegion ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 256#64) 64 ∗
       stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom := by
  let spLocal : BitVec 64 := s0.sp - 1040#64
  let baseI : BitVec 64 := spLocal + BitVec.ofNat 64 (128 * i)
  have hoff8 : spLocal + BitVec.ofNat 64 (8 * (16 * i + 8)) = baseI + 64#64 := by rw [off8_eq]
  have hoff16 : spLocal + BitVec.ofNat 64 (8 * (16 * i + 16)) = baseI + 128#64 := by rw [off8_eq]
  have hoff24 : spLocal + BitVec.ofNat 64 (8 * (16 * i + 24)) = baseI + 192#64 := by rw [off8_eq]
  have hoff32 : spLocal + BitVec.ofNat 64 (8 * (16 * i + 32)) = baseI + 256#64 := by rw [off8_eq]
  have hsub24 : 16 * i + 24 - 16 = 16 * i + 8 := by omega
  have hadd16 : 16 * i + 16 + 8 = 16 * i + 24 := by omega
  have hadd24 : 16 * i + 24 + 8 = 16 * i + 32 := by omega
  refine ks_odd_pre1 hi hrc.opre1 hpc hrun hr hx24 fun s1 hpc1 hrun1 hr1 hx24_1 hx0_1 hx1_1 hx2_1 => ?_
  refine step_bl_call hrc.oms1 hms (spLocal, 120, 16 * i + 16, rkEven)
    (hpc := hpc1) (hrun := hrun1) (hsp_al := hr1.inv.sp_al) (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by rw [hoff16, hadd16, hoff24, stackFrameAt_80_split16]; dsimp only [baseI, spLocal]
                 simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hr1.inv.sp_eq, bv_lin_norm]; ks_focus)
    (hφ := ⟨by dsimp only [spLocal]; simp [wp_norm, arm64_norm]; exact hx0_1, by simp [wp_norm, arm64_norm]; exact hx1_1,
            by simp [wp_norm, arm64_norm]; exact hx2_1, by omega, by omega, by decide⟩) ?_
  intro sf1 hpc_a hrun_a hsp_a hcs_a hψ_a
  have hr_a := hr1.of_call hsp_a hcs_a (pureStepPreserved_of_bl_entry hψ_a)
  have hx24_a : sf1.readReg64 (.gpr 24#5) = baseI := hcs_a.readReg64_x24.trans hx24_1
  have hpc_a' : sf1.pc = fnAddr + 0x0e8#64 := by simpa [bv_lin_norm] using hpc_a
  apply SepWP.congr_pre (P1 := fsStateAt (baseI + 64#64) rkPrev1 ∗ fsStateAt (baseI + 128#64) rkEven ∗
      fsStateAt (baseI + 192#64) rkEven ∗ memRegion (baseI + 256#64) 64 ∗ stackFrameAt spLocal 80 ∗ Frame)
  · rw [hoff16, hadd16, hoff24, stackFrameAt_80_split16]
    dsimp only [baseI, spLocal]
    simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hr1.inv.sp_eq, bv_lin_norm]; sep_ac_rfl
  have_instrs hrc.opre2 0 1; wp_steps 1
  refine step_bl_call hrc.osb hsub (baseI + 192#64, rkEven)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm])
    (hrun := by simp [wp_norm, arm64_norm, hrun_a])
    (hsp_al := by simpa [State.spAligned, wp_norm, arm64_norm] using hr_a.inv.sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by
      dsimp only [baseI, spLocal]
      simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hr_a.inv.sp_eq, bv_lin_norm]; ks_focus)
    (hφ := by dsimp only [baseI, spLocal]; simp [wp_norm, arm64_norm, bv_lin_norm]) ?_
  intro sf2 hpc_b hrun_b hsp_b hcs_b hψ_b
  have hr_b : KsLoopRegs s0 outPtr i sf2 :=
    (KsLoopRegs.mk (KsInv.of_step hr_a.inv)
      (by simp [wp_norm, arm64_norm]; exact hr_a.x19)
      (by simp [wp_norm, arm64_norm]; exact hr_a.x20)
      (by simp [wp_norm, arm64_norm]; exact hr_a.x21)
      (by simp [wp_norm, arm64_norm]; exact hr_a.x22)
      (by simp [wp_norm, arm64_norm]; exact hr_a.x23)).of_call
      hsp_b hcs_b (pureStepPreserved_of_bl_entry hψ_b)
  have hx24_b : sf2.readReg64 (.gpr 24#5) = baseI := by
    rw [hcs_b.readReg64_x24]; simp [wp_norm, arm64_norm]; exact hx24_a
  clear hsp_b
  have hpc_b' : sf2.pc = fnAddr + 0x0f0#64 := by simpa [bv_lin_norm] using hpc_b
  have hsp_sf2 : sf2.sp = s0.sp - 1040#64 := hr_b.inv.sp_eq
  have hx22_sf2 := hr_b.x22
  have_instrs hrc.omid 0 13; rw [fsStateAt_unfold (baseI + 192#64)]
  wp_steps 9; wp_stp64 hf_9 m1 hm1; wp_steps 2; wp_stp64 hf_12 m2 hm2
  refine step_bl_call hrc.oxc hxor
      (spLocal, 120, 16 * i + 24, 16, 12, rkPrev1, Model.subBytesNots (Model.subBytesFs rkEven))
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm]) (hrun := by simp [wp_norm, arm64_norm, hrun_b])
    (hsp_al := (KsInv.of_step hr_b.inv (hm := by simp [wp_norm, arm64_norm, hm2, hm1])).sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by
      rw [hsub24, hoff8, hoff24, ← subBytesNots_struct_eq, fsStateAt_unfold (baseI + 192#64), stackFrameAt_80_split16]
      dsimp only [baseI, spLocal]
      simp only [Simp.sp_setPC, Simp.sp_setMem, Simp.sp_writeReg64_gpr, hr_a.inv.sp_eq, hr_b.inv.sp_eq, bv_lin_norm]
      ks_focus)
    (hφ := ⟨by dsimp only [spLocal]; simp [wp_norm, arm64_norm, bv_lin_norm],
            by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, BitVec.ofNat_add],
            by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
            by omega, by omega, by omega, by omega, by decide, by decide⟩) ?_
  intro sf3 hpc_d hrun_d hsp_d hcs_d hψ_d
  have hr_d : KsLoopRegs s0 outPtr i sf3 :=
    (KsLoopRegs.mk (KsInv.of_step hr_b.inv (hm := by simp [wp_norm, arm64_norm, hm2, hm1]))
      (by simp [wp_norm, arm64_norm]; exact hr_b.x19) (by simp [wp_norm, arm64_norm]; exact hr_b.x20)
      (by simp [wp_norm, arm64_norm]; exact hr_b.x21) (by simp [wp_norm, arm64_norm]; exact hr_b.x22)
      (by simp [wp_norm, arm64_norm]; exact hr_b.x23)).of_call hsp_d hcs_d (pureStepPreserved_of_bl_entry hψ_d)
  clear hsp_d
  have hpc_d' : sf3.pc = fnAddr + 0x128#64 := by simpa [bv_lin_norm] using hpc_d
  have hsp_sf3 : sf3.sp = s0.sp - 1040#64 := hr_d.inv.sp_eq
  have hx22_sf3 := hr_d.x22
  apply SepWP.congr_pre (P1 := fsStateAt (baseI + 64#64) rkPrev1 ∗ fsStateAt (baseI + 128#64) rkEven ∗
      fsStateAt (baseI + 192#64) (Model.ksOddStep rkPrev1 rkEven) ∗ memRegion (baseI + 256#64) 64 ∗
      stackFrameAt spLocal 80 ∗ Frame)
  · rw [hsub24, hoff8, hoff24, stackFrameAt_80_split16]
    dsimp only [baseI, spLocal, Model.ksOddStep, Model.rorDistance]
    simp only [Simp.sp_setPC, Simp.sp_setMem, Simp.sp_writeReg64_gpr, Nat.reduceShiftLeft,
      Nat.reduceAdd, hr_b.inv.sp_eq, bv_lin_norm]; sep_ac_rfl
  have_instrs hrc.opost 0 3; wp_steps 3
  refine step_bl_call hrc.oms2 hms (spLocal, 120, 16 * i + 24, Model.ksOddStep rkPrev1 rkEven)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm]) (hrun := by simp [wp_norm, arm64_norm, hrun_d])
    (hsp_al := by simpa [State.spAligned, wp_norm, arm64_norm] using hr_d.inv.sp_al)
    (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by
      rw [hoff24, hadd24, hoff32, stackFrameAt_80_split16]; dsimp only [baseI, spLocal]
      simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hr_d.inv.sp_eq, bv_lin_norm]; ks_focus)
    (hφ := ⟨by dsimp only [spLocal]; simp [wp_norm, arm64_norm, bv_lin_norm],
            by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, BitVec.ofNat_add],
            by omega, by omega, by decide⟩) ?_
  intro sf4 hpc_e hrun_e hsp_e hcs_e hψ_e
  have hr_e : KsLoopRegs s0 outPtr i sf4 :=
    (KsLoopRegs.mk (KsInv.of_step hr_d.inv)
      (by simp [wp_norm, arm64_norm]; exact hr_d.x19) (by simp [wp_norm, arm64_norm]; exact hr_d.x20)
      (by simp [wp_norm, arm64_norm]; exact hr_d.x21) (by simp [wp_norm, arm64_norm]; exact hr_d.x22)
      (by simp [wp_norm, arm64_norm]; exact hr_d.x23)).of_call hsp_e hcs_e (pureStepPreserved_of_bl_entry hψ_e)
  have hpc_e' : sf4.pc = fnAddr + 0x138#64 := by simpa [bv_lin_norm] using hpc_e
  rcases hr_e with ⟨hinv_e, hx19_e, hx20_e, hx21_e, hx22_e, hx23_e⟩
  have_instrs hrc.otail 0 4; wp_steps 4
  have hbase_next : spLocal + BitVec.ofNat 64 (128 * (i + 1)) = baseI + 128#64 := by
    dsimp only [baseI]; rw [show 128 * (i + 1) = 128 * i + 128 by omega, BitVec.ofNat_add, BitVec.add_assoc]
  refine SepWP.congr_pre ?_
    (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_e])
      ⟨KsInv.of_step hinv_e, by simp [wp_norm, arm64_norm]; exact hx19_e,
       by simp only [wp_norm, arm64_norm]; rw [show 128 * (i + 1) = 128 * i + 128 by omega, BitVec.ofNat_add],
       by simp [wp_norm, arm64_norm]; exact hx21_e,
       by simp only [wp_norm, arm64_norm]; rw [show 16 * (i + 1) = 16 * i + 16 by omega, BitVec.ofNat_add]; bv_lin,
       by simp only [wp_norm, arm64_norm]; rw [show 128 + 136 * (i + 1) = (128 + 136 * i) + 136 by omega, BitVec.ofNat_add]; bv_lin⟩)
  rw [hoff24, hadd24, hoff32, hbase_next, stackFrameAt_80_split16]; dsimp only [baseI, spLocal]
  simp only [Simp.sp_setPC, Simp.sp_writeReg64_gpr, hr_d.inv.sp_eq, bv_lin_norm]; sep_ac_rfl

private def ksRawKeys (rk0 rk1Raw : Model.FsState) : FsKeys256 :=
  let rk2 := Model.ksEvenStep rk0 rk1Raw 0; let rk3 := Model.ksOddStep rk1Raw rk2
  let rk4 := Model.ksEvenStep rk2 rk3 1;    let rk5 := Model.ksOddStep rk3 rk4
  let rk6 := Model.ksEvenStep rk4 rk5 2;    let rk7 := Model.ksOddStep rk5 rk6
  let rk8 := Model.ksEvenStep rk6 rk7 3;    let rk9 := Model.ksOddStep rk7 rk8
  let rk10 := Model.ksEvenStep rk8 rk9 4;   let rk11 := Model.ksOddStep rk9 rk10
  let rk12 := Model.ksEvenStep rk10 rk11 5; let rk13 := Model.ksOddStep rk11 rk12
  let rk14 := Model.ksEvenStep rk12 rk13 6
  ⟨rk0, rk1Raw, rk2, rk3, rk4, rk5, rk6, rk7, rk8, rk9, rk10, rk11, rk12, rk13, rk14⟩

private theorem sepWP_focus {P : Program} {pc : BitVec 64} {s : State}
    {Sub Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (w : SepWP P pc s (Sub ∗ F) post oom) (h : Full = Sub ∗ F) : SepWP P pc s Full post oom :=
  SepWP.congr_pre h.symm w

private theorem sepWP_focus3 {P : Program} {pc : BitVec 64} {s : State}
    {A B C Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (w : SepWP P pc s (A ∗ B ∗ C ∗ F) post oom) (h : Full = (A ∗ B ∗ C) ∗ F) :
    SepWP P pc s Full post oom := SepWP.congr_pre (h.trans (by sep_ac_rfl)).symm w

private theorem sepWP_focus5 {P : Program} {pc : BitVec 64} {s : State}
    {A B C D E Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (w : SepWP P pc s (A ∗ B ∗ C ∗ D ∗ E ∗ F) post oom) (h : Full = (A ∗ B ∗ C ∗ D ∗ E) ∗ F) :
    SepWP P pc s Full post oom := SepWP.congr_pre (h.trans (by sep_ac_rfl)).symm w

private theorem ks_rcon_iter {P : Program}
    {fnAddr memshift32Addr subBytesAddr xorColumnsAddr target_pc outPtr : BitVec 64}
    {i : Nat} (hi : i < 6) {rkPrev2 rkPrev1 : Model.FsState} {s0 s : State} {Full F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrc : KsRconCode P fnAddr memshift32Addr subBytesAddr xorColumnsAddr)
    (hms : subroutine_ok P memshift32Addr memshift32Spec)
    (hsub : subroutine_ok P subBytesAddr subBytesSpec)
    (hxor : subroutine_ok P xorColumnsAddr xorColumnsSpec)
    (hpc : s.pc = fnAddr + 0x084#64) (hrun : s.status = .Running) (hr : KsLoopRegs s0 outPtr i s)
    (hFull : Full = (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i)) rkPrev2 ∗
      fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 64#64) rkPrev1 ∗
      fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 128#64) rkPrev1 ∗
      memRegion ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 192#64) 64 ∗
      memRegion ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 256#64) 64 ∗
      stackFrameAt (s0.sp - 1040#64) 80) ∗ F)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x084#64 → s'.status = .Running →
      KsLoopRegs s0 outPtr (i + 1) s' →
      SepWP P target_pc s'
        ((fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i)) rkPrev2 ∗
          fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 64#64) rkPrev1 ∗
          fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * (i + 1))) (Model.ksEvenStep rkPrev2 rkPrev1 i) ∗
          fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * i) + 192#64)
            (Model.ksOddStep rkPrev1 (Model.ksEvenStep rkPrev2 rkPrev1 i)) ∗
          fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (128 * (i + 1)) + 128#64)
            (Model.ksOddStep rkPrev1 (Model.ksEvenStep rkPrev2 rkPrev1 i)) ∗
          stackFrameAt (s0.sp - 1040#64) 80) ∗ F) post oom) :
    SepWP P target_pc s Full post oom := by
  rw [hFull]
  refine sepWP_focus3 (ks_rcon_even (rkPrev2 := rkPrev2) (rkPrev1 := rkPrev1) (by omega)
    hrc.epre hrc.esb hrc.emid hrc.exc hsub hxor hpc hrun hr.inv hr.x19 hr.x20 hr.x21 hr.x22 hr.x23 ?_) (by ks_focus)
  intro sm hpcm hrunm hinvm hx19m hx20m hx21m hx22m hx23m hx24m
  refine sepWP_focus5 (ks_rcon_odd (rkPrev1 := rkPrev1) (rkEven := Model.ksEvenStep rkPrev2 rkPrev1 i) hi
    hrc hms hsub hxor hpcm hrunm ⟨hinvm, hx19m, hx20m, hx21m, hx22m, hx23m⟩ hx24m ?_) (by ks_focus)
  intro s' hpc' hrun' hr'; exact SepWP.congr_pre (by sep_ac_rfl) (hnext s' hpc' hrun' hr')

private theorem ks_rcon_loop {P : Program}
    {fnAddr memshift32Addr subBytesAddr xorColumnsAddr target_pc outPtr : BitVec 64}
    {rk0 rk1Raw : Model.FsState} {s0 s : State} {Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hrc : KsRconCode P fnAddr memshift32Addr subBytesAddr xorColumnsAddr)
    (hms : subroutine_ok P memshift32Addr memshift32Spec)
    (hsub : subroutine_ok P subBytesAddr subBytesSpec)
    (hxor : subroutine_ok P xorColumnsAddr xorColumnsSpec)
    (hpc : s.pc = fnAddr + 0x084#64) (hrun : s.status = .Running) (hr0 : KsLoopRegs s0 outPtr 0 s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x148#64 → s'.status = .Running →
      KsInv s0 s' → s'.readReg64 (.gpr 19#5) = outPtr →
      SepWP P target_pc s' (fsKeys256At (s0.sp - 1040#64) (ksRawKeys rk0 rk1Raw) ∗
        stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 1040#64) rk0 ∗ fsStateAt (s0.sp - 1040#64 + 0x040#64) rk1Raw ∗
      fsStateAt (s0.sp - 1040#64 + 0x080#64) rk1Raw ∗ ksInitMemRegions (s0.sp - 1040#64) ∗
      stackFrameAt (s0.sp - 1040#64) 80 ∗ Frame) post oom := by
  let ks := ksRawKeys rk0 rk1Raw; dsimp only [ksInitMemRegions]
  refine ks_rcon_iter (i := 0) (by decide) hrc hms hsub hxor hpc hrun hr0 (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s1 hpc1 hrun1 hr1 => ?_
  refine ks_rcon_iter (i := 1) (by decide) hrc hms hsub hxor hpc1 hrun1 hr1 (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s2 hpc2 hrun2 hr2 => ?_
  refine ks_rcon_iter (i := 2) (by decide) hrc hms hsub hxor hpc2 hrun2 hr2 (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s3 hpc3 hrun3 hr3 => ?_
  refine ks_rcon_iter (i := 3) (by decide) hrc hms hsub hxor hpc3 hrun3 hr3 (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s4 hpc4 hrun4 hr4 => ?_
  refine ks_rcon_iter (i := 4) (by decide) hrc hms hsub hxor hpc4 hrun4 hr4 (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s5 hpc5 hrun5 hr5 => ?_
  refine ks_rcon_iter (i := 5) (by decide) hrc hms hsub hxor hpc5 hrun5 hr5 (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s6 hpc6 hrun6 hr6 => ?_
  refine sepWP_focus3 (ks_rcon_even (i := 6) (rkPrev2 := ks.rk12) (rkPrev1 := ks.rk13) (by decide)
    hrc.epre hrc.esb hrc.emid hrc.exc hsub hxor hpc6 hrun6 hr6.inv hr6.x19 hr6.x20 hr6.x21 hr6.x22 hr6.x23 ?_)
    (by dsimp only [ks, ksRawKeys]; simp only [Nat.reduceMul, bv_lin_norm]; ks_focus)
  intro s7 hpc7 hrun7 hinv7 hx19_7 _ _ hx22_7 _ _
  refine ks_rcon_exit hrc.opre1 hpc7 hrun7 hinv7 hx19_7 hx22_7 fun s8 hpc8 hrun8 hinv8 hx19_8 => ?_
  refine SepWP.congr_pre ?_ (hnext s8 hpc8 hrun8 hinv8 hx19_8)
  dsimp only [fsKeys256At, ks, ksRawKeys]; simp only [Nat.reduceMul, bv_lin_norm]; sep_ac_rfl

/-! ## 5. 3-Iteration `invShiftRows` Loop (`[82..278]`, `0x148..0x458`) -/

private structure KsIsrCode (P : Program) (fnAddr : BitVec 64) : Prop where
  c0 : hasInstrs P (fnAddr + 0x148#64) (decodeWords ksIsrInitWords)
  c1 : hasInstrs P (fnAddr + 0x16c#64) (decodeWords ksIsr1Words)
  c2 : hasInstrs P (fnAddr + 0x220#64) (decodeWords ksIsr2Words)
  c3 : hasInstrs P (fnAddr + 0x2b0#64) (decodeWords ksIsr3Words)
  c4 : hasInstrs P (fnAddr + 0x324#64) (decodeWords ksIsr4Words)
  c5 : hasInstrs P (fnAddr + 0x3c8#64) (decodeWords ksIsr5Words)

private def KsIsrMasks (s0 : State) (outPtr : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = 0x0f0f00000f0f0000#64 ∧
  s.readReg64 (.gpr 9#5) = 0x000f00ff00f00000#64 ∧
  s.readReg64 (.gpr 11#5) = 0x00f000ff000f0000#64 ∧
  s.readReg64 (.gpr 12#5) = s0.sp - 1040#64 ∧ s.readReg64 (.gpr 19#5) = outPtr

private def KsIsrCtx (s0 : State) (outPtr baseG x10v : BitVec 64) (zf : Bool) (s : State) : Prop :=
  KsIsrMasks s0 outPtr s ∧ s.readReg64 (.gpr 10#5) = x10v ∧
  s.readReg64 (.gpr 13#5) = baseG ∧ ConditionHolds .NE s.pstate = !zf

private def KsIsrR1 (a : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = ((Model.deltaSwap1 a.s3 8 0x000f00ff00f00000#64 ^^^
    (Model.deltaSwap1 a.s3 8 0x000f00ff00f00000#64 >>> 4)) &&& 0x0f0f00000f0f0000#64) ∧
  s.readReg64 (.gpr 1#5) = a.s5 ∧
  s.readReg64 (.gpr 2#5) = (Model.deltaSwap1 a.s4 8 0x000f00ff00f00000#64 ^^^
    (Model.deltaSwap1 a.s4 8 0x000f00ff00f00000#64 >>> 4)) ∧
  s.readReg64 (.gpr 3#5) = (((Model.deltaSwap1 a.s2 8 0x000f00ff00f00000#64 ^^^
      (Model.deltaSwap1 a.s2 8 0x000f00ff00f00000#64 >>> 4)) &&& 0x0f0f00000f0f0000#64) +
    (((Model.deltaSwap1 a.s2 8 0x000f00ff00f00000#64 ^^^
      (Model.deltaSwap1 a.s2 8 0x000f00ff00f00000#64 >>> 4)) &&& 0x0f0f00000f0f0000#64) <<< 4)) ∧
  s.readReg64 (.gpr 4#5) = a.s6 ∧ s.readReg64 (.gpr 5#5) = a.s7 ∧
  s.readReg64 (.gpr 6#5) = (((a.s5 ^^^ (a.s5 >>> 8)) &&& 0x000f00ff00f00000#64) +
    (((a.s5 ^^^ (a.s5 >>> 8)) &&& 0x000f00ff00f00000#64) <<< 8)) ∧
  s.readReg64 (.gpr 16#5) = Model.deltaSwap1 a.s4 8 0x000f00ff00f00000#64 ∧
  s.readReg64 (.gpr 17#5) = Model.deltaSwap1 a.s2 8 0x000f00ff00f00000#64 ∧
  s.readReg64 (.gpr 18#5) = Model.deltaSwap1 a.s3 8 0x000f00ff00f00000#64

private def KsIsrR2 (b : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = b.s3 ∧ s.readReg64 (.gpr 1#5) = b.s0 ∧ s.readReg64 (.gpr 2#5) = b.s1 ∧
  s.readReg64 (.gpr 15#5) = ((b.s1 ^^^ (b.s1 >>> 8)) &&& 0x00ff000000ff0000#64) ∧
  s.readReg64 (.gpr 17#5) = ((b.s0 ^^^ (b.s0 >>> 8)) &&& 0x00ff000000ff0000#64) ∧
  s.readReg64 (.gpr 18#5) = b.s2

private def KsIsrR3 (b c : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = b.s7 ∧ s.readReg64 (.gpr 1#5) = (c.s1 ^^^ (c.s1 >>> 8)) ∧
  s.readReg64 (.gpr 3#5) = (b.s6 ^^^ (b.s6 >>> 8)) ∧ s.readReg64 (.gpr 4#5) = (c.s0 ^^^ (c.s0 >>> 8)) ∧
  s.readReg64 (.gpr 14#5) = b.s6 ∧ s.readReg64 (.gpr 17#5) = c.s0 ∧ s.readReg64 (.gpr 18#5) = c.s1

private def KsIsrR4 (c : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = c.s4 ∧ s.readReg64 (.gpr 1#5) = c.s6 ∧ s.readReg64 (.gpr 3#5) = c.s7 ∧
  s.readReg64 (.gpr 4#5) = (c.s6 ^^^ (c.s6 >>> 8)) ∧ s.readReg64 (.gpr 5#5) = (c.s7 ^^^ (c.s7 >>> 8)) ∧
  s.readReg64 (.gpr 14#5) = (Model.invShiftRows3 c).s2 ∧
  s.readReg64 (.gpr 15#5) = (Model.deltaSwap1 c.s3 8 0x00f000ff000f0000#64 ^^^
    (Model.deltaSwap1 c.s3 8 0x00f000ff000f0000#64 >>> 4)) ∧
  s.readReg64 (.gpr 16#5) = Model.deltaSwap1 c.s3 8 0x00f000ff000f0000#64 ∧
  s.readReg64 (.gpr 17#5) = c.s5

private theorem ks_isr_init {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc0 : hasInstrs P (fnAddr + 0x148#64) (decodeWords ksIsrInitWords))
    (hpc : s.pc = fnAddr + 0x148#64) (hrun : s.status = .Running)
    (hinv : KsInv s0 s) (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x16c#64 → s'.status = .Running → KsInv s0 s' →
      KsIsrMasks s0 outPtr s' → s'.readReg64 (.gpr 10#5) = 0#64 → SepWP P target_pc s' Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hsp := hinv.sp_eq; have_instrs hc0 0 9; wp_steps 9
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (KsInv.of_step hinv) (by simp only [KsIsrMasks, wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm])

private theorem ks_isr_hdr {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {g : Nat} (hg : g < 3) {a : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc1 : hasInstrs P (fnAddr + 0x16c#64) (decodeWords ksIsr1Words))
    (hpc : s.pc = fnAddr + 0x16c#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (hm : KsIsrMasks s0 outPtr s) (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (256 * g))
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x17c#64 → s'.status = .Running → KsInv s0 s' →
      KsIsrCtx s0 outPtr ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g))
        (BitVec.ofNat 64 (256 * (g + 1))) (decide (g = 2)) s' →
      s'.readReg64 (.gpr 14#5) = a.s0 → s'.readReg64 (.gpr 15#5) = a.s1 →
      SepWP P target_pc s'
        (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0x40#64) a ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0x40#64) a ∗ Rest) post oom := by
  rcases hm with ⟨hx8, hx9, hx11, hx12, hx19⟩; have_instrs hc1 0 4
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl
  all_goals
    rw [fsStateAt_unfold]; wp_steps 4; rw [← fsStateAt_unfold]
    exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (KsInv.of_step hinv) (by simp only [KsIsrCtx, KsIsrMasks, wp_norm, arm64_norm, bv_lin_norm, *])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])

private theorem ks_isr_1 {P : Program} {fnAddr target_pc outPtr baseG x10v : BitVec 64} {zf : Bool}
    {a : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc1 : hasInstrs P (fnAddr + 0x16c#64) (decodeWords ksIsr1Words))
    (hpc : s.pc = fnAddr + 0x17c#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (hctx : KsIsrCtx s0 outPtr baseG x10v zf s)
    (hx14 : s.readReg64 (.gpr 14#5) = a.s0) (hx15 : s.readReg64 (.gpr 15#5) = a.s1)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x220#64 → s'.status = .Running → KsInv s0 s' →
      KsIsrCtx s0 outPtr baseG x10v zf s' → KsIsrR1 a s' →
      SepWP P target_pc s'
        (fsStateAt (baseG + 0x40#64)
          { a with s0 := (Model.invShiftRows1 a).s0, s1 := (Model.invShiftRows1 a).s1 } ∗ Rest) post oom) :
    SepWP P target_pc s (fsStateAt (baseG + 0x40#64) a ∗ Rest) post oom := by
  rcases hctx with ⟨⟨hx8, hx9, hx11, hx12, hx19⟩, hx10, hx13, hpz⟩
  have_instrs hc1 4 41; rw [fsStateAt_unfold]; wp_steps 40; wp_stp64 hf_44 m1 hm1
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsIsrCtx, KsIsrMasks, wp_norm, arm64_norm, *])
    (by simp only [KsIsrR1, wp_norm, arm64_norm, *]))
  rw [fsStateAt_unfold]; dsimp only [Model.invShiftRows1, Model.shiftRows3, Model.FsState.map]

private theorem ks_isr_2 {P : Program} {fnAddr target_pc outPtr baseG x10v : BitVec 64} {zf : Bool}
    {a b : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc2 : hasInstrs P (fnAddr + 0x220#64) (decodeWords ksIsr2Words))
    (hpc : s.pc = fnAddr + 0x220#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (hctx : KsIsrCtx s0 outPtr baseG x10v zf s) (hr1 : KsIsrR1 a s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x2b0#64 → s'.status = .Running → KsInv s0 s' →
      KsIsrCtx s0 outPtr baseG x10v zf s' → KsIsrR2 b s' →
      SepWP P target_pc s'
        (fsStateAt (baseG + 0x40#64) (Model.invShiftRows1 a) ∗
         fsStateAt (baseG + 0x80#64) b ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (baseG + 0x40#64)
        { a with s0 := (Model.invShiftRows1 a).s0, s1 := (Model.invShiftRows1 a).s1 } ∗
       fsStateAt (baseG + 0x80#64) b ∗ Rest) post oom := by
  rcases hctx with ⟨⟨hx8, hx9, hx11, hx12, hx19⟩, hx10, hx13, hpz⟩
  rcases hr1 with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx16, hx17, hx18⟩
  have_instrs hc2 0 36; rw [fsStateAt_unfold (baseG + 0x40#64), fsStateAt_unfold (baseG + 0x80#64)]
  wp_steps 16; wp_stp64 hf_16 m1 hm1; wp_steps 9; wp_stp64 hf_26 m2 hm2; wp_steps 8; wp_stp64 hf_35 m3 hm3
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsIsrCtx, KsIsrMasks, wp_norm, arm64_norm, *])
    (by simp only [KsIsrR2, wp_norm, arm64_norm, *]))
  rw [fsStateAt_unfold (baseG + 0x40#64), fsStateAt_unfold (baseG + 0x80#64)]
  dsimp only [Model.invShiftRows1, Model.shiftRows3, Model.FsState.map]

private theorem ks_isr_3 {P : Program} {fnAddr target_pc outPtr baseG x10v : BitVec 64} {zf : Bool}
    {b c : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc3 : hasInstrs P (fnAddr + 0x2b0#64) (decodeWords ksIsr3Words))
    (hpc : s.pc = fnAddr + 0x2b0#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (hctx : KsIsrCtx s0 outPtr baseG x10v zf s) (hr2 : KsIsrR2 b s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x324#64 → s'.status = .Running → KsInv s0 s' →
      KsIsrCtx s0 outPtr baseG x10v zf s' → KsIsrR3 b c s' →
      SepWP P target_pc s'
        (fsStateAt (baseG + 0x80#64) { Model.invShiftRows2 b with s6 := b.s6, s7 := b.s7 } ∗
         fsStateAt (baseG + 0xc0#64) c ∗ Rest) post oom) :
    SepWP P target_pc s (fsStateAt (baseG + 0x80#64) b ∗ fsStateAt (baseG + 0xc0#64) c ∗ Rest) post oom := by
  rcases hctx with ⟨⟨hx8, hx9, hx11, hx12, hx19⟩, hx10, hx13, hpz⟩
  rcases hr2 with ⟨hx0, hx1, hx2, hx15, hx17, hx18⟩
  have_instrs hc3 0 29; rw [fsStateAt_unfold (baseG + 0x80#64), fsStateAt_unfold (baseG + 0xc0#64)]
  wp_steps 10; wp_stp64 hf_10 m1 hm1; wp_steps 5; wp_stp64 hf_16 m2 hm2; wp_steps 11; wp_stp64 hf_28 m3 hm3
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsIsrCtx, KsIsrMasks, wp_norm, arm64_norm, *])
    (by simp only [KsIsrR3, wp_norm, arm64_norm, *]))
  rw [fsStateAt_unfold (baseG + 0x80#64), fsStateAt_unfold (baseG + 0xc0#64)]
  dsimp only [Model.invShiftRows2, Model.shiftRows2, Model.FsState.map]

private theorem ks_isr_4 {P : Program} {fnAddr target_pc outPtr baseG x10v : BitVec 64} {zf : Bool}
    {b c : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc4 : hasInstrs P (fnAddr + 0x324#64) (decodeWords ksIsr4Words))
    (hpc : s.pc = fnAddr + 0x324#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (hctx : KsIsrCtx s0 outPtr baseG x10v zf s) (hr3 : KsIsrR3 b c s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x3c8#64 → s'.status = .Running → KsInv s0 s' →
      KsIsrCtx s0 outPtr baseG x10v zf s' → KsIsrR4 c s' →
      SepWP P target_pc s'
        (fsStateAt (baseG + 0x80#64) (Model.invShiftRows2 b) ∗
         fsStateAt (baseG + 0xc0#64)
           { c with s0 := (Model.invShiftRows3 c).s0, s1 := (Model.invShiftRows3 c).s1 } ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (baseG + 0x80#64) { Model.invShiftRows2 b with s6 := b.s6, s7 := b.s7 } ∗
       fsStateAt (baseG + 0xc0#64) c ∗ Rest) post oom := by
  rcases hctx with ⟨⟨hx8, hx9, hx11, hx12, hx19⟩, hx10, hx13, hpz⟩
  rcases hr3 with ⟨hx0, hx1, hx3, hx4, hx14, hx17, hx18⟩
  have_instrs hc4 0 41; rw [fsStateAt_unfold (baseG + 0x80#64), fsStateAt_unfold (baseG + 0xc0#64)]
  wp_steps 24; wp_stp64 hf_24 m1 hm1; wp_steps 4; wp_stp64 hf_29 m2 hm2; wp_steps 11
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsIsrCtx, KsIsrMasks, wp_norm, arm64_norm, *])
    (by dsimp only [KsIsrR4, Model.invShiftRows3, Model.shiftRows1, Model.FsState.map]
        simp only [wp_norm, arm64_norm, *]))
  rw [fsStateAt_unfold (baseG + 0x80#64), fsStateAt_unfold (baseG + 0xc0#64)]
  dsimp only [Model.invShiftRows2, Model.shiftRows2, Model.invShiftRows3, Model.shiftRows1, Model.FsState.map]

private theorem ks_isr_5 {P : Program} {fnAddr target_pc outPtr baseG x10v : BitVec 64} {zf : Bool}
    {c : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc5 : hasInstrs P (fnAddr + 0x3c8#64) (decodeWords ksIsr5Words))
    (hpc : s.pc = fnAddr + 0x3c8#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (hctx : KsIsrCtx s0 outPtr baseG x10v zf s) (hr4 : KsIsrR4 c s)
    (hnext : ∀ s' : State, s'.pc = (if zf then fnAddr + 0x45c#64 else fnAddr + 0x16c#64) →
      s'.status = .Running → KsInv s0 s' → KsIsrMasks s0 outPtr s' →
      s'.readReg64 (.gpr 10#5) = x10v →
      SepWP P target_pc s' (fsStateAt (baseG + 0xc0#64) (Model.invShiftRows3 c) ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (baseG + 0xc0#64)
        { c with s0 := (Model.invShiftRows3 c).s0, s1 := (Model.invShiftRows3 c).s1 } ∗ Rest) post oom := by
  rcases hctx with ⟨⟨hx8, hx9, hx11, hx12, hx19⟩, hx10, hx13, hpz⟩
  rcases hr4 with ⟨hx0, hx1, hx3, hx4, hx5, hx14, hx15, hx16, hx17⟩
  dsimp only [Model.invShiftRows3, Model.shiftRows1, Model.FsState.map] at hx14
  have_instrs hc5 0 37; rw [fsStateAt_unfold (baseG + 0xc0#64)]
  wp_steps 14; wp_stp64 hf_14 m1 hm1; wp_steps 17; wp_stp64 hf_32 m2 hm2; wp_steps 2; wp_stp64 hf_35 m3 hm3
  cases zf <;> wp_steps 1
  all_goals
    refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
      (by simp only [KsIsrMasks, wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hx10]))
    rw [fsStateAt_unfold (baseG + 0xc0#64)]
    dsimp only [Model.invShiftRows3, Model.shiftRows1, Model.FsState.map]

private theorem ks_isr_iter {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {g : Nat} (hg : g < 3) {a b c : Model.FsState} {s0 s : State} {Full F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hic : KsIsrCode P fnAddr) (hpc : s.pc = fnAddr + 0x16c#64) (hrun : s.status = .Running)
    (hinv : KsInv s0 s) (hm : KsIsrMasks s0 outPtr s)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (256 * g))
    (hFull : Full = (fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0x40#64) a ∗
      fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0x80#64) b ∗
      fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0xc0#64) c) ∗ F)
    (hnext : ∀ s' : State, s'.pc = (if decide (g = 2) then fnAddr + 0x45c#64 else fnAddr + 0x16c#64) →
      s'.status = .Running → KsInv s0 s' → KsIsrMasks s0 outPtr s' →
      s'.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (256 * (g + 1)) →
      SepWP P target_pc s'
        ((fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0x40#64) (Model.invShiftRows1 a) ∗
          fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0x80#64) (Model.invShiftRows2 b) ∗
          fsStateAt ((s0.sp - 1040#64) + BitVec.ofNat 64 (256 * g) + 0xc0#64) (Model.invShiftRows3 c)) ∗ F) post oom) :
    SepWP P target_pc s Full post oom := by
  rw [hFull]
  refine sepWP_focus (ks_isr_hdr hg hic.c1 hpc hrun hinv hm hx10 fun s1 hpc1 hrun1 hinv1 hctx1 hx14 hx15 => ?_) (by ks_focus)
  refine ks_isr_1 hic.c1 hpc1 hrun1 hinv1 hctx1 hx14 hx15 fun s2 hpc2 hrun2 hinv2 hctx2 hr1 => ?_
  refine sepWP_focus (ks_isr_2 hic.c2 hpc2 hrun2 hinv2 hctx2 hr1 fun s3 hpc3 hrun3 hinv3 hctx3 hr2 => ?_) (by ks_focus)
  refine sepWP_focus (ks_isr_3 hic.c3 hpc3 hrun3 hinv3 hctx3 hr2 fun s4 hpc4 hrun4 hinv4 hctx4 hr3 => ?_) (by ks_focus)
  refine ks_isr_4 hic.c4 hpc4 hrun4 hinv4 hctx4 hr3 fun s5 hpc5 hrun5 hinv5 hctx5 hr4 => ?_
  refine sepWP_focus (ks_isr_5 hic.c5 hpc5 hrun5 hinv5 hctx5 hr4 fun s6 hpc6 hrun6 hinv6 hm6 hx10_6 => ?_) (by ks_focus)
  exact SepWP.congr_pre (by sep_ac_rfl) (hnext s6 hpc6 hrun6 hinv6 hm6 hx10_6)

private def ksIsrKeys (ks : FsKeys256) : FsKeys256 :=
  { ks with
    rk1 := Model.invShiftRows1 ks.rk1, rk2 := Model.invShiftRows2 ks.rk2, rk3 := Model.invShiftRows3 ks.rk3,
    rk5 := Model.invShiftRows1 ks.rk5, rk6 := Model.invShiftRows2 ks.rk6, rk7 := Model.invShiftRows3 ks.rk7,
    rk9 := Model.invShiftRows1 ks.rk9, rk10 := Model.invShiftRows2 ks.rk10, rk11 := Model.invShiftRows3 ks.rk11 }

private theorem ks_isr_loop {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {ks : FsKeys256} {s0 s : State} {Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hic : KsIsrCode P fnAddr) (hpc : s.pc = fnAddr + 0x148#64) (hrun : s.status = .Running)
    (hinv : KsInv s0 s) (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x45c#64 → s'.status = .Running → KsInv s0 s' →
      KsIsrMasks s0 outPtr s' →
      SepWP P target_pc s' (fsKeys256At (s0.sp - 1040#64) (ksIsrKeys ks) ∗ Frame) post oom) :
    SepWP P target_pc s (fsKeys256At (s0.sp - 1040#64) ks ∗ Frame) post oom := by
  dsimp only [fsKeys256At, ksIsrKeys]
  refine ks_isr_init hic.c0 hpc hrun hinv hx19 fun s1 hpc1 hrun1 hinv1 hm1 hx10_1 => ?_
  refine ks_isr_iter (g := 0) (a := ks.rk1) (b := ks.rk2) (c := ks.rk3) (by decide) hic hpc1 hrun1 hinv1 hm1 hx10_1
    (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s2 hpc2 hrun2 hinv2 hm2 hx10_2 => ?_
  refine ks_isr_iter (g := 1) (a := ks.rk5) (b := ks.rk6) (c := ks.rk7) (by decide) hic hpc2 hrun2 hinv2 hm2 hx10_2
    (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s3 hpc3 hrun3 hinv3 hm3 hx10_3 => ?_
  refine ks_isr_iter (g := 2) (a := ks.rk9) (b := ks.rk10) (c := ks.rk11) (by decide) hic hpc3 hrun3 hinv3 hm3 hx10_3
    (by simp only [Nat.reduceMul, bv_lin_norm]; ks_focus) fun s4 hpc4 hrun4 hinv4 hm4 _ => ?_
  refine SepWP.congr_pre ?_ (hnext s4 hpc4 hrun4 hinv4 hm4)
  dsimp only [fsKeys256At, ksIsrKeys]; simp only [Nat.reduceMul, bv_lin_norm]; sep_ac_rfl

/-! ## 6. `rk13` `invShiftRows1`, `subBytesNots` (`rk1..14`), `memcpy` & Epilogue (`[279..509]`) -/

private structure KsTailCode (P : Program) (fnAddr memcpyAddr : BitVec 64) : Prop where
  r13a : hasInstrs P (fnAddr + 0x45c#64) (decodeWords ksRk13aWords)
  r13b : hasInstrs P (fnAddr + 0x508#64) (decodeWords ksRk13bWords)
  n1   : hasInstrs P (fnAddr + 0x5b8#64) (decodeWords ksNots1Words)
  n2   : hasInstrs P (fnAddr + 0x62c#64) (decodeWords ksNots2Words)
  n3   : hasInstrs P (fnAddr + 0x690#64) (decodeWords ksNots3Words)
  n4   : hasInstrs P (fnAddr + 0x720#64) (decodeWords ksNots4Words)
  mcpy : hasInstrs P (fnAddr + 0x7d8#64) [ .bl (memcpyAddr - (fnAddr + 0x7d8#64)) ]
  epil : hasInstrs P (fnAddr + 0x7dc#64) (decodeWords ksEpilogueWords)

private def KsOutArgs (outPtr spLocal : BitVec 64) (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = outPtr ∧ s.readReg64 (.gpr 1#5) = spLocal ∧
  s.readReg64 (.gpr 2#5) = 960#64

private def KsRk13R (r : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = 0x0f0f00000f0f0000#64 ∧
  s.readReg64 (.gpr 9#5) = 0x000f00ff00f00000#64 ∧
  s.readReg64 (.gpr 11#5) = (Model.invShiftRows1 r).s1 ∧
  s.readReg64 (.gpr 12#5) = (Model.invShiftRows1 r).s2 ∧
  s.readReg64 (.gpr 13#5) = (((r.s4 ^^^ (r.s4 >>> 8)) &&& 0x000f00ff00f00000#64) +
    (((r.s4 ^^^ (r.s4 >>> 8)) &&& 0x000f00ff00f00000#64) <<< 8)) ∧
  s.readReg64 (.gpr 14#5) = Model.deltaSwap1 r.s3 8 0x000f00ff00f00000#64 ∧
  s.readReg64 (.gpr 15#5) = r.s6 ∧ s.readReg64 (.gpr 16#5) = r.s7 ∧
  s.readReg64 (.gpr 17#5) = r.s5 ∧ s.readReg64 (.gpr 18#5) = r.s4

private def KsNotsR0 (r1 : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 8#5) = (r1.s0 ^^^ 0xffffffffffffffff#64) ∧
  s.readReg64 (.gpr 9#5) = (r1.s1 ^^^ 0xffffffffffffffff#64) ∧
  s.readReg64 (.gpr 10#5) = r1.s5 ∧ s.readReg64 (.gpr 11#5) = r1.s6

private theorem ks_rk13a {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {r13 : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x45c#64) (decodeWords ksRk13aWords))
    (hpc : s.pc = fnAddr + 0x45c#64) (hrun : s.status = .Running)
    (hinv : KsInv s0 s) (hm : KsIsrMasks s0 outPtr s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x508#64 → s'.status = .Running → KsInv s0 s' →
      KsOutArgs outPtr (s0.sp - 1040#64) s' → KsRk13R r13 s' →
      SepWP P target_pc s'
        (fsStateAt (s0.sp - 1040#64 + 0x340#64)
          { r13 with s0 := (Model.invShiftRows1 r13).s0 } ∗ Rest) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 1040#64 + 0x340#64) r13 ∗ Rest) post oom := by
  rcases hm with ⟨hx8, hx9, hx11, hx12, hx19⟩
  have hsp := hinv.sp_eq; have hsp0_and := hinv.sp0_and_15; have hsp_loc := hinv.sp_local_and_15
  have_instrs hc 0 43; rw [fsStateAt_unfold]; wp_steps 41; wp_str64 hf_41 m1 hm1; wp_steps 1
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsOutArgs, wp_norm, arm64_norm, *])
    (by dsimp only [KsRk13R, Model.invShiftRows1, Model.shiftRows3, Model.FsState.map]
        simp only [wp_norm, arm64_norm, *]))
  rw [fsStateAt_unfold]; dsimp only [Model.invShiftRows1, Model.shiftRows3, Model.FsState.map]

private theorem ks_rk13b {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {r1 r13 : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x508#64) (decodeWords ksRk13bWords))
    (hpc : s.pc = fnAddr + 0x508#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (ha : KsOutArgs outPtr (s0.sp - 1040#64) s) (hr : KsRk13R r13 s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x5b8#64 → s'.status = .Running → KsInv s0 s' →
      KsOutArgs outPtr (s0.sp - 1040#64) s' → KsNotsR0 r1 s' →
      SepWP P target_pc s'
        (fsStateAt (s0.sp - 1040#64 + 0x040#64) r1 ∗
         fsStateAt (s0.sp - 1040#64 + 0x340#64) (Model.invShiftRows1 r13) ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (s0.sp - 1040#64 + 0x040#64) r1 ∗
       fsStateAt (s0.sp - 1040#64 + 0x340#64) { r13 with s0 := (Model.invShiftRows1 r13).s0 } ∗ Rest) post oom := by
  rcases ha with ⟨hx0, hx1, hx2⟩
  rcases hr with ⟨hx8, hx9, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18⟩
  have hsp := hinv.sp_eq; have hsp0_and := hinv.sp0_and_15; have hsp_loc := hinv.sp_local_and_15
  dsimp only [Model.invShiftRows1, Model.shiftRows3, Model.FsState.map] at hx11 hx12
  have_instrs hc 0 44
  rw [fsStateAt_unfold (s0.sp - 1040#64 + 0x040#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x340#64)]
  wp_steps 1; wp_str64 hf_1 m1 hm1; wp_steps 1; wp_str64 hf_3 m2 hm2; wp_steps 21; wp_str64 hf_25 m3 hm3
  wp_steps 8; wp_str64 hf_34 m4 hm4; wp_steps 3; wp_str64 hf_38 m5 hm5; wp_str64 hf_39 m6 hm6
  wp_steps 3; wp_str64 hf_43 m7 hm7
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsOutArgs, wp_norm, arm64_norm, *])
    (by simp only [KsNotsR0, wp_norm, arm64_norm, *]))
  rw [fsStateAt_unfold (s0.sp - 1040#64 + 0x040#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x340#64)]
  dsimp only [Model.invShiftRows1, Model.shiftRows3, Model.FsState.map]

private theorem ks_nots1 {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {r1 r2 r3 r4 r5 : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x5b8#64) (decodeWords ksNots1Words))
    (hpc : s.pc = fnAddr + 0x5b8#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (ha : KsOutArgs outPtr (s0.sp - 1040#64) s) (hr : KsNotsR0 r1 s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x62c#64 → s'.status = .Running → KsInv s0 s' →
      KsOutArgs outPtr (s0.sp - 1040#64) s' →
      s'.readReg64 (.gpr 9#5) = r5.s0 → s'.readReg64 (.gpr 11#5) = r5.s1 →
      SepWP P target_pc s'
        (fsStateAt (s0.sp - 1040#64 + 0x040#64) (Model.subBytesNots r1) ∗
         fsStateAt (s0.sp - 1040#64 + 0x080#64) (Model.subBytesNots r2) ∗
         fsStateAt (s0.sp - 1040#64 + 0x0c0#64) (Model.subBytesNots r3) ∗
         fsStateAt (s0.sp - 1040#64 + 0x100#64) (Model.subBytesNots r4) ∗
         fsStateAt (s0.sp - 1040#64 + 0x140#64) r5 ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (s0.sp - 1040#64 + 0x040#64) r1 ∗ fsStateAt (s0.sp - 1040#64 + 0x080#64) r2 ∗
       fsStateAt (s0.sp - 1040#64 + 0x0c0#64) r3 ∗ fsStateAt (s0.sp - 1040#64 + 0x100#64) r4 ∗
       fsStateAt (s0.sp - 1040#64 + 0x140#64) r5 ∗ Rest) post oom := by
  rcases ha with ⟨hx0, hx1, hx2⟩; rcases hr with ⟨hx8, hx9, hx10, hx11⟩
  have hsp := hinv.sp_eq; have hsp0_and := hinv.sp0_and_15; have hsp_loc := hinv.sp_local_and_15
  have_instrs hc 0 29
  rw [fsStateAt_unfold (s0.sp - 1040#64 + 0x040#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x080#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x0c0#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x100#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x140#64)]
  wp_stp64 hf_0 m1 hm1; wp_steps 3; wp_stp64 hf_4 m2 hm2; wp_steps 3; wp_stp64 hf_8 m3 hm3; wp_steps 3
  wp_stp64 hf_12 m4 hm4; wp_steps 3; wp_stp64 hf_16 m5 hm5; wp_steps 3; wp_stp64 hf_20 m6 hm6; wp_steps 3
  wp_stp64 hf_24 m7 hm7; wp_steps 3; wp_stp64 hf_28 m8 hm8
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsOutArgs, wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
  rw [← subBytesNots_struct_eq r1, ← subBytesNots_struct_eq r2, ← subBytesNots_struct_eq r3, ← subBytesNots_struct_eq r4,
      fsStateAt_unfold (s0.sp - 1040#64 + 0x040#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x080#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x0c0#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x100#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x140#64)]

private theorem ks_nots2 {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {r5 r6 r7 r8 : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x62c#64) (decodeWords ksNots2Words))
    (hpc : s.pc = fnAddr + 0x62c#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (ha : KsOutArgs outPtr (s0.sp - 1040#64) s)
    (hx9 : s.readReg64 (.gpr 9#5) = r5.s0) (hx11 : s.readReg64 (.gpr 11#5) = r5.s1)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x690#64 → s'.status = .Running → KsInv s0 s' →
      KsOutArgs outPtr (s0.sp - 1040#64) s' →
      s'.readReg64 (.gpr 9#5) = r8.s0 → s'.readReg64 (.gpr 11#5) = r8.s1 →
      SepWP P target_pc s'
        (fsStateAt (s0.sp - 1040#64 + 0x140#64) (Model.subBytesNots r5) ∗
         fsStateAt (s0.sp - 1040#64 + 0x180#64) (Model.subBytesNots r6) ∗
         fsStateAt (s0.sp - 1040#64 + 0x1c0#64) (Model.subBytesNots r7) ∗
         fsStateAt (s0.sp - 1040#64 + 0x200#64) r8 ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (s0.sp - 1040#64 + 0x140#64) r5 ∗ fsStateAt (s0.sp - 1040#64 + 0x180#64) r6 ∗
       fsStateAt (s0.sp - 1040#64 + 0x1c0#64) r7 ∗ fsStateAt (s0.sp - 1040#64 + 0x200#64) r8 ∗ Rest) post oom := by
  rcases ha with ⟨hx0, hx1, hx2⟩
  have hsp := hinv.sp_eq; have hsp0_and := hinv.sp0_and_15; have hsp_loc := hinv.sp_local_and_15
  have_instrs hc 0 25
  rw [fsStateAt_unfold (s0.sp - 1040#64 + 0x140#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x180#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x1c0#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x200#64)]
  wp_steps 3; wp_stp64 hf_3 m1 hm1; wp_steps 3; wp_stp64 hf_7 m2 hm2; wp_steps 3; wp_stp64 hf_11 m3 hm3
  wp_steps 3; wp_stp64 hf_15 m4 hm4; wp_steps 3; wp_stp64 hf_19 m5 hm5; wp_steps 4; wp_stp64 hf_24 m6 hm6
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsOutArgs, wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
  rw [← subBytesNots_struct_eq r5, ← subBytesNots_struct_eq r6, ← subBytesNots_struct_eq r7,
      fsStateAt_unfold (s0.sp - 1040#64 + 0x140#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x180#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x1c0#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x200#64)]

private theorem ks_nots3 {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {r8 r9 r10 r11 : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x690#64) (decodeWords ksNots3Words))
    (hpc : s.pc = fnAddr + 0x690#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (ha : KsOutArgs outPtr (s0.sp - 1040#64) s)
    (hx9 : s.readReg64 (.gpr 9#5) = r8.s0) (hx11 : s.readReg64 (.gpr 11#5) = r8.s1)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x720#64 → s'.status = .Running → KsInv s0 s' →
      KsOutArgs outPtr (s0.sp - 1040#64) s' →
      s'.readReg64 (.gpr 9#5) = r11.s0 → s'.readReg64 (.gpr 10#5) = r11.s1 →
      SepWP P target_pc s'
        (fsStateAt (s0.sp - 1040#64 + 0x200#64) (Model.subBytesNots r8) ∗
         fsStateAt (s0.sp - 1040#64 + 0x240#64) (Model.subBytesNots r9) ∗
         fsStateAt (s0.sp - 1040#64 + 0x280#64) (Model.subBytesNots r10) ∗
         fsStateAt (s0.sp - 1040#64 + 0x2c0#64) r11 ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (s0.sp - 1040#64 + 0x200#64) r8 ∗ fsStateAt (s0.sp - 1040#64 + 0x240#64) r9 ∗
       fsStateAt (s0.sp - 1040#64 + 0x280#64) r10 ∗ fsStateAt (s0.sp - 1040#64 + 0x2c0#64) r11 ∗ Rest) post oom := by
  rcases ha with ⟨hx0, hx1, hx2⟩
  have hsp := hinv.sp_eq; have hsp0_and := hinv.sp0_and_15; have hsp_loc := hinv.sp_local_and_15
  have_instrs hc 0 36
  rw [fsStateAt_unfold (s0.sp - 1040#64 + 0x200#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x240#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x280#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x2c0#64)]
  wp_steps 3; wp_str64 hf_3 m1 hm1; wp_steps 1; wp_str64 hf_5 m2 hm2; wp_steps 2; wp_str64 hf_8 m3 hm3
  wp_steps 2; wp_str64 hf_11 m4 hm4; wp_steps 2; wp_str64 hf_14 m5 hm5; wp_steps 2; wp_str64 hf_17 m6 hm6
  wp_steps 2; wp_str64 hf_20 m7 hm7; wp_steps 2; wp_str64 hf_23 m8 hm8; wp_steps 2; wp_str64 hf_26 m9 hm9
  wp_steps 2; wp_str64 hf_29 m10 hm10; wp_steps 2; wp_str64 hf_32 m11 hm11; wp_steps 2; wp_str64 hf_35 m12 hm12
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsOutArgs, wp_norm, arm64_norm, *])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
  rw [← subBytesNots_struct_eq r8, ← subBytesNots_struct_eq r9, ← subBytesNots_struct_eq r10,
      fsStateAt_unfold (s0.sp - 1040#64 + 0x200#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x240#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x280#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x2c0#64)]

private theorem ks_nots4 {P : Program} {fnAddr target_pc outPtr : BitVec 64}
    {r11 r12 r13 r14 : Model.FsState} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x720#64) (decodeWords ksNots4Words))
    (hpc : s.pc = fnAddr + 0x720#64) (hrun : s.status = .Running) (hinv : KsInv s0 s)
    (ha : KsOutArgs outPtr (s0.sp - 1040#64) s)
    (hx9 : s.readReg64 (.gpr 9#5) = r11.s0) (hx10 : s.readReg64 (.gpr 10#5) = r11.s1)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x7d8#64 → s'.status = .Running → KsInv s0 s' →
      KsOutArgs outPtr (s0.sp - 1040#64) s' →
      SepWP P target_pc s'
        (fsStateAt (s0.sp - 1040#64 + 0x2c0#64) (Model.subBytesNots r11) ∗
         fsStateAt (s0.sp - 1040#64 + 0x300#64) (Model.subBytesNots r12) ∗
         fsStateAt (s0.sp - 1040#64 + 0x340#64) (Model.subBytesNots r13) ∗
         fsStateAt (s0.sp - 1040#64 + 0x380#64) (Model.subBytesNots r14) ∗ Rest) post oom) :
    SepWP P target_pc s
      (fsStateAt (s0.sp - 1040#64 + 0x2c0#64) r11 ∗ fsStateAt (s0.sp - 1040#64 + 0x300#64) r12 ∗
       fsStateAt (s0.sp - 1040#64 + 0x340#64) r13 ∗ fsStateAt (s0.sp - 1040#64 + 0x380#64) r14 ∗ Rest) post oom := by
  rcases ha with ⟨hx0, hx1, hx2⟩
  have hsp := hinv.sp_eq; have hsp0_and := hinv.sp0_and_15; have hsp_loc := hinv.sp_local_and_15
  have_instrs hc 0 46
  rw [fsStateAt_unfold (s0.sp - 1040#64 + 0x2c0#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x300#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x340#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x380#64)]
  wp_steps 2; wp_str64 hf_2 m1 hm1; wp_steps 2; wp_str64 hf_5 m2 hm2; wp_steps 2; wp_str64 hf_8 m3 hm3
  wp_steps 2; wp_str64 hf_11 m4 hm4; wp_steps 2; wp_str64 hf_14 m5 hm5; wp_steps 2; wp_str64 hf_17 m6 hm6
  wp_steps 2; wp_str64 hf_20 m7 hm7; wp_steps 2; wp_str64 hf_23 m8 hm8; wp_steps 2; wp_str64 hf_26 m9 hm9
  wp_steps 2; wp_str64 hf_29 m10 hm10; wp_steps 2; wp_str64 hf_32 m11 hm11; wp_steps 2; wp_str64 hf_35 m12 hm12
  wp_steps 2; wp_str64 hf_38 m13 hm13; wp_steps 2; wp_str64 hf_41 m14 hm14; wp_steps 1; wp_str64 hf_43 m15 hm15
  wp_steps 1; wp_str64 hf_45 m16 hm16
  refine SepWP.congr_pre ?_ (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (KsInv.of_step hinv (hm := by simp [wp_norm, arm64_norm, *]))
    (by simp only [KsOutArgs, wp_norm, arm64_norm, *]))
  rw [← subBytesNots_struct_eq r11, ← subBytesNots_struct_eq r12, ← subBytesNots_struct_eq r13, ← subBytesNots_struct_eq r14,
      fsStateAt_unfold (s0.sp - 1040#64 + 0x2c0#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x300#64),
      fsStateAt_unfold (s0.sp - 1040#64 + 0x340#64), fsStateAt_unfold (s0.sp - 1040#64 + 0x380#64)]

private def ksFinalKeys (ks : FsKeys256) : FsKeys256 :=
  ⟨ks.rk0, Model.subBytesNots ks.rk1, Model.subBytesNots ks.rk2, Model.subBytesNots ks.rk3,
   Model.subBytesNots ks.rk4, Model.subBytesNots ks.rk5, Model.subBytesNots ks.rk6, Model.subBytesNots ks.rk7,
   Model.subBytesNots ks.rk8, Model.subBytesNots ks.rk9, Model.subBytesNots ks.rk10, Model.subBytesNots ks.rk11,
   Model.subBytesNots ks.rk12, Model.subBytesNots (Model.invShiftRows1 ks.rk13), Model.subBytesNots ks.rk14⟩

private theorem sepWP_focus2 {P : Program} {pc : BitVec 64} {s : State}
    {A B Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (w : SepWP P pc s (A ∗ B ∗ F) post oom) (h : Full = (A ∗ B) ∗ F) :
    SepWP P pc s Full post oom := SepWP.congr_pre (h.trans (by sep_ac_rfl)).symm w

private theorem sepWP_focus4 {P : Program} {pc : BitVec 64} {s : State}
    {A B C D Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (w : SepWP P pc s (A ∗ B ∗ C ∗ D ∗ F) post oom) (h : Full = (A ∗ B ∗ C ∗ D) ∗ F) :
    SepWP P pc s Full post oom := SepWP.congr_pre (h.trans (by sep_ac_rfl)).symm w

private theorem ks_tail_nots {P : Program} {fnAddr memcpyAddr target_pc outPtr : BitVec 64}
    {ks : FsKeys256} {s0 s : State} {Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (htc : KsTailCode P fnAddr memcpyAddr) (hpc : s.pc = fnAddr + 0x45c#64)
    (hrun : s.status = .Running) (hinv : KsInv s0 s) (hm : KsIsrMasks s0 outPtr s)
    (hnext : ∀ s' : State, s'.pc = fnAddr + 0x7d8#64 → s'.status = .Running → KsInv s0 s' →
      KsOutArgs outPtr (s0.sp - 1040#64) s' →
      SepWP P target_pc s' (fsKeys256At (s0.sp - 1040#64) (ksFinalKeys ks) ∗ Frame) post oom) :
    SepWP P target_pc s (fsKeys256At (s0.sp - 1040#64) ks ∗ Frame) post oom := by
  dsimp only [fsKeys256At, ksFinalKeys]
  refine sepWP_focus (ks_rk13a (r13 := ks.rk13) htc.r13a hpc hrun hinv hm fun s1 hpc1 hrun1 hinv1 ha1 hr1 => ?_) (by ks_focus)
  refine sepWP_focus2 (ks_rk13b (r1 := ks.rk1) (r13 := ks.rk13) htc.r13b hpc1 hrun1 hinv1 ha1 hr1 fun s2 hpc2 hrun2 hinv2 ha2 hr2 => ?_) (by ks_focus)
  refine sepWP_focus5 (ks_nots1 (r1 := ks.rk1) (r2 := ks.rk2) (r3 := ks.rk3) (r4 := ks.rk4) (r5 := ks.rk5)
    htc.n1 hpc2 hrun2 hinv2 ha2 hr2 fun s3 hpc3 hrun3 hinv3 ha3 hx9_3 hx11_3 => ?_) (by ks_focus)
  refine sepWP_focus4 (ks_nots2 (r5 := ks.rk5) (r6 := ks.rk6) (r7 := ks.rk7) (r8 := ks.rk8)
    htc.n2 hpc3 hrun3 hinv3 ha3 hx9_3 hx11_3 fun s4 hpc4 hrun4 hinv4 ha4 hx9_4 hx11_4 => ?_) (by ks_focus)
  refine sepWP_focus4 (ks_nots3 (r8 := ks.rk8) (r9 := ks.rk9) (r10 := ks.rk10) (r11 := ks.rk11)
    htc.n3 hpc4 hrun4 hinv4 ha4 hx9_4 hx11_4 fun s5 hpc5 hrun5 hinv5 ha5 hx9_5 hx10_5 => ?_) (by ks_focus)
  refine sepWP_focus4 (ks_nots4 (r11 := ks.rk11) (r12 := ks.rk12) (r13 := Model.invShiftRows1 ks.rk13) (r14 := ks.rk14)
    htc.n4 hpc5 hrun5 hinv5 ha5 hx9_5 hx10_5 fun s6 hpc6 hrun6 hinv6 ha6 => ?_) (by ks_focus)
  exact SepWP.congr_pre (by dsimp only [fsKeys256At, ksFinalKeys]; sep_ac_rfl) (hnext s6 hpc6 hrun6 hinv6 ha6)

private theorem ks_memcpy_epilogue {P : Program} {fnAddr memcpyAddr outPtr : BitVec 64}
    {ksOut : FsKeys256} {pad : BitVec 64} {s0 s : State} {Rest : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (htc : KsTailCode P fnAddr memcpyAddr) (hmemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hsp0 : s0.spAligned = true) (hpc : s.pc = fnAddr + 0x7d8#64)
    (hrun : s.status = .Running) (hinv : KsInv s0 s) (ha : KsOutArgs outPtr (s0.sp - 1040#64) s)
    (hnext : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      PureStepPreserved s0 sf → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      SepWP P (s0.readReg64 .lr) sf (Rest ∗ fsKeys256At outPtr ksOut ∗ stackFrameAt s0.sp 1120) post oom) :
    SepWP P (s0.readReg64 .lr) s
      (fsKeys256At (s0.sp - 1040#64) ksOut ∗ stackFrameAt (s0.sp - 1040#64) 80 ∗
       ksSavedFrame s0 pad ∗ memRegion outPtr 960 ∗ Rest) post oom := by
  rcases ha with ⟨hx0, hx1, hx2⟩
  have hsp_and := sp_and_15_of_spAligned hsp0
  have hsp80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hsp_and; bv_bits
  rw [fsKeys256At_eq_pointsToBytes (s0.sp - 1040#64) ksOut]
  refine step_bl_call htc.mcpy hmemcpy (outPtr, s0.sp - 1040#64, fsKeys256Bytes ksOut)
    (hpc := hpc) (hrun := hrun) (hsp_al := hinv.sp_al) (hpre_eq := rfl) (hpost_eq := fun _ => rfl)
    (hFull := by rw [fsKeys256Bytes_length]; ks_focus)
    (hφ := ⟨by simp [wp_norm, arm64_norm]; exact hx0, by simp [wp_norm, arm64_norm]; exact hx1,
            by rw [fsKeys256Bytes_length]; simp [wp_norm, arm64_norm]; exact hx2,
            by rw [fsKeys256Bytes_length]; decide⟩) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 hψ1
  have hinv1 := KsInv.of_call hinv hsp1 hcs1 (pureStepPreserved_of_bl_entry hψ1.2)
  clear hsp1
  have hpc1' : sf1.pc = fnAddr + 0x7dc#64 := by simpa [bv_lin_norm] using hpc1
  have hsp_sf1 : sf1.sp = s0.sp - 1040#64 := hinv1.sp_eq
  rw [← fsKeys256At_eq_pointsToBytes outPtr ksOut]
  have_instrs htc.epil 0 7; dsimp only [ksSavedFrame, ksStackCells]; wp_steps 7
  refine SepWP.repack_pre (stackFrameAt_1120_merge s0 pad ksOut)
    (by dsimp only [ksSavedFrame, ksStackCells]; sep_ac_rfl) ?_
  refine SepWP.congr_pre (by sep_ac_rfl)
    (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (hinv1.pure.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])))
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) ?_)
  exact (CalleeSavedPreserved.iff_regs s0 _).mpr
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm]; exact hinv1.x25, by simp [wp_norm, arm64_norm]; exact hinv1.x26,
     by simp [wp_norm, arm64_norm]; exact hinv1.x27, by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]; exact hinv1.vregs⟩

private theorem hasInstrs_step {P : Program} {fnAddr off off' : BitVec 64} {xs ys : List Instr}
    (h : hasInstrs P (fnAddr + off) (xs ++ ys))
    (hoff : off + BitVec.ofNat 64 (4 * xs.length) = off' := by
      simp only [length_decodeWords, List.length_singleton]; decide) :
    hasInstrs P (fnAddr + off) xs ∧ hasInstrs P (fnAddr + off') ys := by
  have ⟨h1, h2⟩ := h.split_append (off := BitVec.ofNat 64 (4 * xs.length)) rfl
  exact ⟨h1, by rwa [BitVec.add_assoc, hoff] at h2⟩

private theorem ksFinalKeys_eq (key : List (BitVec 8)) :
    ksFinalKeys (ksIsrKeys (ksRawKeys
      (Model.bitslice (Blocks4.replicate (key.take 16)))
      (Model.bitslice (Blocks4.replicate (key.drop 16))))) =
      Model.aes256KeyScheduleFs key := rfl

end

/-- Placement-generic `subroutine_ok` verification of `fixslice64::aes256_key_schedule`. -/
theorem aes256KeySchedule_ok {P : Program}
    {fnAddr memsetAddr bitsliceAddr memshift32Addr subBytesAddr xorColumnsAddr memcpyAddr :
      BitVec 64}
    (hc : hasInstrs P fnAddr
      (aes256KeyScheduleInstrs fnAddr memsetAddr bitsliceAddr memshift32Addr subBytesAddr
        xorColumnsAddr memcpyAddr))
    (hcallees : Aes256KeyScheduleCallees P memsetAddr bitsliceAddr memshift32Addr subBytesAddr
      xorColumnsAddr memcpyAddr) :
    subroutine_ok P fnAddr aes256KeyScheduleSpec := by
  have hc' : hasInstrs P (fnAddr + 0#64)
      (aes256KeyScheduleInstrs fnAddr memsetAddr bitsliceAddr memshift32Addr subBytesAddr
        xorColumnsAddr memcpyAddr) := by simpa only [BitVec.add_zero] using hc
  dsimp only [aes256KeyScheduleInstrs] at hc'; simp only [List.append_assoc] at hc'
  rcases hasInstrs_step (off' := 0x034#64) hc' with ⟨hc0, hc'⟩
  rcases hasInstrs_step (off' := 0x038#64) hc' with ⟨hbl0, hc'⟩
  rcases hasInstrs_step (off' := 0x04c#64) hc' with ⟨hc1, hc'⟩
  rcases hasInstrs_step (off' := 0x050#64) hc' with ⟨hbl1, hc'⟩
  rcases hasInstrs_step (off' := 0x064#64) hc' with ⟨hc2, hc'⟩
  rcases hasInstrs_step (off' := 0x068#64) hc' with ⟨hbl2, hc'⟩
  rcases hasInstrs_step (off' := 0x074#64) hc' with ⟨hc3, hc'⟩
  rcases hasInstrs_step (off' := 0x078#64) hc' with ⟨hbl3, hc'⟩
  rcases hasInstrs_step (off' := 0x084#64) hc' with ⟨hc4, hc'⟩
  rcases hasInstrs_step (off' := 0x08c#64) hc' with ⟨rc1, hc'⟩
  rcases hasInstrs_step (off' := 0x090#64) hc' with ⟨rc2, hc'⟩
  rcases hasInstrs_step (off' := 0x0d0#64) hc' with ⟨rc3, hc'⟩
  rcases hasInstrs_step (off' := 0x0d4#64) hc' with ⟨rc4, hc'⟩
  rcases hasInstrs_step (off' := 0x0e4#64) hc' with ⟨rc5, hc'⟩
  rcases hasInstrs_step (off' := 0x0e8#64) hc' with ⟨rc6, hc'⟩
  rcases hasInstrs_step (off' := 0x0ec#64) hc' with ⟨rc7, hc'⟩
  rcases hasInstrs_step (off' := 0x0f0#64) hc' with ⟨rc8, hc'⟩
  rcases hasInstrs_step (off' := 0x124#64) hc' with ⟨rc9, hc'⟩
  rcases hasInstrs_step (off' := 0x128#64) hc' with ⟨rc10, hc'⟩
  rcases hasInstrs_step (off' := 0x134#64) hc' with ⟨rc11, hc'⟩
  rcases hasInstrs_step (off' := 0x138#64) hc' with ⟨rc12, hc'⟩
  rcases hasInstrs_step (off' := 0x148#64) hc' with ⟨rc13, hc'⟩
  rcases hasInstrs_step (off' := 0x16c#64) hc' with ⟨ic0, hc'⟩
  rcases hasInstrs_step (off' := 0x220#64) hc' with ⟨ic1, hc'⟩
  rcases hasInstrs_step (off' := 0x2b0#64) hc' with ⟨ic2, hc'⟩
  rcases hasInstrs_step (off' := 0x324#64) hc' with ⟨ic3, hc'⟩
  rcases hasInstrs_step (off' := 0x3c8#64) hc' with ⟨ic4, hc'⟩
  rcases hasInstrs_step (off' := 0x45c#64) hc' with ⟨ic5, hc'⟩
  rcases hasInstrs_step (off' := 0x508#64) hc' with ⟨tc1, hc'⟩
  rcases hasInstrs_step (off' := 0x5b8#64) hc' with ⟨tc2, hc'⟩
  rcases hasInstrs_step (off' := 0x62c#64) hc' with ⟨tc3, hc'⟩
  rcases hasInstrs_step (off' := 0x690#64) hc' with ⟨tc4, hc'⟩
  rcases hasInstrs_step (off' := 0x720#64) hc' with ⟨tc5, hc'⟩
  rcases hasInstrs_step (off' := 0x7d8#64) hc' with ⟨tc6, hc'⟩
  rcases hasInstrs_step (off' := 0x7dc#64) hc' with ⟨tc7, tc8⟩
  have hc0' : hasInstrs P fnAddr (decodeWords ksSeg0Words) := by simpa using hc0
  have hrc : KsRconCode P fnAddr memshift32Addr subBytesAddr xorColumnsAddr :=
    ⟨rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, rc9, rc10, rc11, rc12, rc13⟩
  have hic : KsIsrCode P fnAddr := ⟨ic0, ic1, ic2, ic3, ic4, ic5⟩
  have htc : KsTailCode P fnAddr memcpyAddr := ⟨tc1, tc2, tc3, tc4, tc5, tc6, tc7, tc8⟩
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ro, outPtr, keyPtr, key⟩ R s0 hpc hrun hpre hsp0
  dsimp only [aes256KeyScheduleSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hkey⟩, hpre⟩
  refine ⟨bytesAt ro keyPtr key ∗ memRegion outPtr 960 ∗ stackFrameAt s0.sp 1120, hpre, ?_⟩
  refine ks_prologue_memset hc0' hbl0 hcallees.memset_ok hpc hrun hsp0 hx0 hx8
    fun pad s1 hpc1 hrun1 hinv1 hx19_1 hx20_1 hx21_1 => ?_
  refine SepWP.congr_pre (by sep_ac_rfl)
    (ks_bitslice_init (Frame := memRegion outPtr 960 ∗ ksSavedFrame s0 pad)
      hc1 hbl1 hc2 hbl2 hc3 hbl3 hc4 hcallees.bitslice_ok hcallees.memshift32_ok
      hpc1 hrun1 hinv1 hkey hx19_1 hx20_1 hx21_1
      fun s2 hpc2 hrun2 hinv2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 => ?_)
  let rk0 := Model.bitslice (Blocks4.replicate (key.take 16))
  let rk1 := Model.bitslice (Blocks4.replicate (key.drop 16))
  let tailFrame := stackFrameAt (s0.sp - 1040#64) 80 ∗
    bytesAt ro keyPtr key ∗ memRegion outPtr 960 ∗ ksSavedFrame s0 pad
  refine SepWP.congr_pre (by sep_ac_rfl)
    (ks_rcon_loop (rk0 := rk0) (rk1Raw := rk1)
      (Frame := bytesAt ro keyPtr key ∗ memRegion outPtr 960 ∗ ksSavedFrame s0 pad)
      hrc hcallees.memshift32_ok hcallees.subBytes_ok hcallees.xorColumns_ok
      hpc2 hrun2 ⟨hinv2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
      fun s3 hpc3 hrun3 hinv3 hx19_3 => ?_)
  refine SepWP.congr_pre rfl
    (ks_isr_loop (ks := ksRawKeys rk0 rk1) (Frame := tailFrame)
      hic hpc3 hrun3 hinv3 hx19_3 fun s4 hpc4 hrun4 hinv4 hm4 => ?_)
  refine ks_tail_nots (ks := ksIsrKeys (ksRawKeys rk0 rk1)) (Frame := tailFrame)
    htc hpc4 hrun4 hinv4 hm4 fun s5 hpc5 hrun5 hinv5 ha5 => ?_
  dsimp only [rk0, rk1, tailFrame]
  rw [ksFinalKeys_eq key]
  refine SepWP.congr_pre (by sep_ac_rfl)
    (ks_memcpy_epilogue (ksOut := Model.aes256KeyScheduleFs key) (pad := pad)
      (Rest := bytesAt ro keyPtr key) htc hcallees.memcpy_ok hsp0
      hpc5 hrun5 hinv5 ha5 fun sf hpc_f hrun_f hpure hsp_f hcs_f => ?_)
  refine SepWP.done hpc_f hrun_f ⟨fun hm => ?_, hsp_f, hcs_f⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpure, hm⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule

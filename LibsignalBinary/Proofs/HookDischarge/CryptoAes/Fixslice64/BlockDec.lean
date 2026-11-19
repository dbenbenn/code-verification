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
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
meta import ProofLib.StdStartup.StdDetect
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Equiv

/-! # `fixslice64::aes256_decrypt` Machine-Code Proof (`270` Instructions) -/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (Blocks4)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj fsStateAt fsKeys256At blocks4Bytes adrpAddPair hasInstrs_prefix
   memRegion64_eq_exists_fsStateAt)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open CryptoGames.CBC
  (Block bytesToBlock blockToBytesLE blockToBytesLE_bytesToBlock bytesToBlock_blockToBytesLE)
open CryptoGames.HKDF (bytesToKey32)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
  (bitsliceInstrs invBitsliceInstrs bitslice4Spec bitslice4_ok invBitsliceSpec invBitslice_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
  (invSubBytesInstrs invSubBytesSpec invSubBytes_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
  (invMixColumns1Instrs invMixColumns2Instrs invMixColumns3Instrs
   invMixColumns1Spec invMixColumns2Spec invMixColumns3Spec
   invMixColumns1_ok invMixColumns2_ok invMixColumns3_ok)

public section

/-! ## 1. Raw `.rlib` Template Words (`270` Instructions) -/

@[expose] def decPrologueWords : List (BitVec 32) :=
  [0xd101c3ff#32, 0xa9047bfd#32, 0xa90557f6#32, 0xa9064ff4#32, 0x910103fd#32, 0xaa0003f4#32, 0x910003e0#32, 0x91004022#32,
   0x91008023#32, 0x9100c024#32, 0xaa0803f3#32]
@[expose] def decArk14Words : List (BitVec 32) :=
  [0xa9402fe9#32, 0x910003e0#32, 0xf941c288#32, 0xf941c68a#32, 0xf941ca8c#32, 0xa94243ef#32, 0xf941d28d#32, 0xca080128#32,
   0xca0a016a#32, 0xf941ce89#32, 0xa9002be8#32, 0xf941d68e#32, 0xa9412fe8#32, 0xca0d01ea#32, 0xca0c0108#32, 0xca090169#32,
   0xca0e020b#32, 0xa90127e8#32, 0xa94333e9#32, 0xf941da88#32, 0xa9022fea#32, 0xf941de8a#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def decShiftAWords : List (BitVec 32) :=
  [0xa94027e8#32, 0x910de295#32, 0xa94137ec#32, 0x52800a16#32, 0xa9423fee#32, 0xca48210a#32, 0xca49212b#32, 0xca4c2190#32,
   0x92101d4a#32, 0x92101d6b#32, 0xaa0a214a#32, 0xaa0b216b#32, 0x92101e10#32, 0xaa102210#32, 0xca080148#32, 0xca4d21aa#32,
   0xca090169#32, 0xa90027e8#32]
@[expose] def decShiftBWords : List (BitVec 32) :=
  [0xa94327f1#32, 0x92101d4a#32, 0xca4e21cb#32, 0xca4f21e8#32, 0xaa0a214a#32, 0xca0c020c#32, 0xca492130#32, 0x92101d6b#32,
   0x92101d08#32, 0xca0d014a#32, 0xca51222d#32, 0xaa0b216b#32, 0xa9012bec#32, 0xaa082108#32, 0x92101e0c#32, 0x92101daa#32,
   0xaa0c218c#32, 0xca0e016b#32, 0xaa0a214a#32, 0xca0f0108#32, 0xa90223eb#32, 0xca090189#32, 0xca110148#32, 0xa90327e8#32]
@[expose] def decLoopArk1Words : List (BitVec 32) :=
  [0xa9402fe8#32, 0x910003e0#32, 0xa97caaa9#32, 0xa97ebaad#32, 0xa94243ef#32, 0xca090108#32, 0xca0a016a#32, 0xa97db2a9#32,
   0xa9002be8#32, 0xa9412fe8#32, 0xca0d01ea#32, 0xca090108#32, 0xca0c0169#32, 0xca0e020b#32, 0xa90127e8#32, 0xa94333e9#32,
   0xa9022fea#32, 0xa97faaa8#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def decImc0HeadWords : List (BitVec 32) :=
  [0xa978a6a8#32, 0xa9402fea#32, 0xa979b6ac#32, 0xa97abeae#32, 0xca080148#32, 0xca090169#32, 0xa9412fea#32, 0xa94247f0#32,
   0xa97b82b2#32, 0xa9430be1#32, 0xca0c014a#32, 0xca0d016b#32, 0xca0e020c#32, 0xca0f022d#32, 0xcacd41a3#32, 0xcac84110#32,
   0xcac94131#32, 0xca12002e#32, 0xca00004f#32, 0xcaca4152#32, 0xcace41c4#32, 0xcacb4160#32, 0xcacf41e2#32, 0xca0301ce#32,
   0xca100129#32, 0xcacc4181#32, 0xca0401ef#32, 0xca080048#32, 0xca020129#32, 0xca0e01e5#32, 0xca12016b#32, 0xca11014a#32,
   0xca00018c#32, 0xca1001d0#32]
@[expose] def decImc0TailWords : List (BitVec 32) :=
  [0xca1100b1#32, 0xca1201f2#32, 0xca0001c0#32, 0xca02016b#32, 0xca080252#32, 0xca090000#32, 0xca0301e3#32, 0xcad08210#32,
   0xcad18231#32, 0xca0101ad#32, 0xca0a0021#32, 0xca0b0063#32, 0xcad2814a#32, 0xcac0816b#32, 0xca02018c#32, 0xca050021#32,
   0xca080208#32, 0xca090229#32, 0xca040184#32, 0xa90027e8#32, 0xca120148#32, 0xcac18189#32, 0xca00016a#32, 0xcac381ab#32,
   0xca0d0042#32, 0xa9012be8#32, 0xca010128#32, 0xcac481c9#32, 0xca03016a#32, 0xcac281eb#32, 0x910003e0#32, 0xa9022be8#32,
   0xca040128#32, 0xca020169#32, 0xa90327e8#32]
@[expose] def decLoopArk3Words : List (BitVec 32) :=
  [0xa9402fe8#32, 0x910003e0#32, 0xa974aaa9#32, 0xa976baad#32, 0xa94243ef#32, 0xca090108#32, 0xca0a016a#32, 0xa975b2a9#32,
   0xa9002be8#32, 0xa9412fe8#32, 0xca0d01ea#32, 0xca090108#32, 0xca0c0169#32, 0xca0e020b#32, 0xa90127e8#32, 0xa94333e9#32,
   0xa9022fea#32, 0xa977aaa8#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def decLoopGuardWords : List (BitVec 32) := [0xb10022df#32, 0x540007e0#32, 0x910022c8#32, 0xeb16011f#32, 0x540007e3#32]
@[expose] def decLoopArk2Words : List (BitVec 32) :=
  [0xa9402fe8#32, 0x910003e0#32, 0xa970aaa9#32, 0xa972baad#32, 0xa94243ef#32, 0xca090108#32, 0xca0a016a#32, 0xa971b2a9#32,
   0xa9002be8#32, 0xa9412fe8#32, 0xca0d01ea#32, 0xca090108#32, 0xca0c0169#32, 0xca0e020b#32, 0xa90127e8#32, 0xa94333e9#32,
   0xa9022fea#32, 0xa973aaa8#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def decLoopLatchWords : List (BitVec 32) := [0xd10082d6#32, 0xd10402b5#32, 0xb10082df#32, 0x54ffed01#32]
@[expose] def decArk0Words : List (BitVec 32) :=
  [0xa9402fe8#32, 0x910003e1#32, 0xa9402a89#32, 0xaa1303e0#32, 0xa9423a8d#32, 0xa94243ef#32, 0xca090108#32, 0xca0a016a#32,
   0xa9413289#32, 0xa9002be8#32, 0xa9412fe8#32, 0xca0d01ea#32, 0xca090108#32, 0xca0c0169#32, 0xca0e020b#32, 0xa90127e8#32,
   0xa94333e9#32, 0xa9022fea#32, 0xa9432a88#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def decRetWords : List (BitVec 32) := [0xa9464ff4#32, 0xa94557f6#32, 0xa9447bfd#32, 0x9101c3ff#32, 0xd65f03c0#32]

/-- Exact 270 raw 32-bit words of `fixslice64::aes256_decrypt` from the `.rlib` object. -/
@[expose] def aes256DecryptTemplateWords : List (BitVec 32) :=
  decPrologueWords ++ [0x94000000#32] ++ decArk14Words ++ [0x94000000#32] ++ decShiftAWords ++ decShiftBWords ++
  decLoopArk1Words ++ [0x94000000#32, 0x910003e0#32, 0x94000000#32, 0xb10042df#32, 0x54001060#32] ++
  decImc0HeadWords ++ decImc0TailWords ++ [0x94000000#32] ++
  decLoopArk3Words ++ [0x94000000#32, 0x910003e0#32, 0x94000000#32] ++ decLoopGuardWords ++
  decLoopArk2Words ++ [0x94000000#32, 0x910003e0#32, 0x94000000#32] ++ decLoopLatchWords ++
  [0x90000000#32, 0x91000000#32, 0x94000000#32] ++ decArk0Words ++ [0x94000000#32] ++ decRetWords ++
  [0x90000000#32, 0x91000000#32, 0x94000000#32, 0x90000000#32, 0x91000000#32, 0x94000000#32]

/-! ## 2. Unreachable Panic-Site Relocation Parameters & Instruction Lists -/

/-- Relocation parameters for the three unreachable 3-instruction panic blocks (`+0x3a4`, `+0x420`, `+0x42c`). -/
structure Aes256DecryptPanicSyms where
  sym0 : BitVec 64
  relax0 : Bool := false
  target0 : BitVec 64
  sym1 : BitVec 64
  relax1 : Bool := false
  target1 : BitVec 64
  sym2 : BitVec 64
  relax2 : Bool := false
  target2 : BitVec 64

/-- Unrelocated `.rlib` panic-site parameters at `fnAddr`. -/
@[expose] def Aes256DecryptPanicSyms.template (fnAddr : BitVec 64 := 0#64) :
    Aes256DecryptPanicSyms where
  sym0 := (fnAddr + 0x3a4#64) &&& 0xfffffffffffff000#64; target0 := fnAddr + 0x3ac#64
  sym1 := (fnAddr + 0x420#64) &&& 0xfffffffffffff000#64; target1 := fnAddr + 0x428#64
  sym2 := (fnAddr + 0x42c#64) &&& 0xfffffffffffff000#64; target2 := fnAddr + 0x434#64

/-- Prefix instruction list `[0..263]` (`264` instructions through `ret`) of `aes256_decrypt`. -/
@[expose] def aes256DecryptPrefixInstrs
    (fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr panic0Sym : BitVec 64)
    (panic0Relax : Bool) (panic0Target : BitVec 64) : List Instr :=
  List.flatten
    [ decodeWords decPrologueWords, [.bl (bitsliceAddr - (fnAddr + 0x2c#64))],
      decodeWords decArk14Words, [.bl (invSubBytesAddr - (fnAddr + 0x94#64))],
      decodeWords decShiftAWords, decodeWords decShiftBWords,
      decodeWords decLoopArk1Words, [.bl (invMixColumns1Addr - (fnAddr + 0x194#64))],
      decodeWords [0x910003e0#32], [.bl (invSubBytesAddr - (fnAddr + 0x19c#64))],
      decodeWords [0xb10042df#32, 0x54001060#32], decodeWords decImc0HeadWords, decodeWords decImc0TailWords,
      [.bl (invSubBytesAddr - (fnAddr + 0x2bc#64))], decodeWords decLoopArk3Words,
      [.bl (invMixColumns3Addr - (fnAddr + 0x314#64))], decodeWords [0x910003e0#32],
      [.bl (invSubBytesAddr - (fnAddr + 0x31c#64))], decodeWords decLoopGuardWords, decodeWords decLoopArk2Words,
      [.bl (invMixColumns2Addr - (fnAddr + 0x388#64))], decodeWords [0x910003e0#32],
      [.bl (invSubBytesAddr - (fnAddr + 0x390#64))], decodeWords decLoopLatchWords,
      adrpAddPair (.gpr 0#5) (fnAddr + 0x3a4#64) panic0Sym panic0Relax, [.bl (panic0Target - (fnAddr + 0x3ac#64))],
      decodeWords decArk0Words, [.bl (invBitsliceAddr - (fnAddr + 0x408#64))], decodeWords decRetWords ]

/-- Full 270-instruction list `[0..269]` of `fixslice64::aes256_decrypt`. -/
@[expose] def aes256DecryptFullInstrs
    (fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr : BitVec 64) (syms : Aes256DecryptPanicSyms) : List Instr :=
  aes256DecryptPrefixInstrs fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr
    invMixColumns2Addr invMixColumns3Addr invBitsliceAddr syms.sym0 syms.relax0 syms.target0 ++
  (adrpAddPair (.gpr 0#5) (fnAddr + 0x420#64) syms.sym1 syms.relax1 ++ [.bl (syms.target1 - (fnAddr + 0x428#64))] ++
   adrpAddPair (.gpr 0#5) (fnAddr + 0x42c#64) syms.sym2 syms.relax2 ++ [.bl (syms.target2 - (fnAddr + 0x434#64))])

theorem aes256DecryptPrefixInstrs_length
    (fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr panic0Sym : BitVec 64) (panic0Relax : Bool) (panic0Target : BitVec 64) :
    (aes256DecryptPrefixInstrs fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr
      invMixColumns2Addr invMixColumns3Addr invBitsliceAddr panic0Sym panic0Relax panic0Target).length = 264 := by
  have hd : ∀ ws : List (BitVec 32), (decodeWords ws).length = ws.length := fun _ => List.length_map _
  simp only [aes256DecryptPrefixInstrs, List.length_flatten, List.map_cons, List.map_nil, hd,
    CodeCommon.adrpAddPair_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]; rfl

theorem aes256DecryptFullInstrs_length
    (fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr : BitVec 64) (syms : Aes256DecryptPanicSyms) :
    (aes256DecryptFullInstrs fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr
      invMixColumns2Addr invMixColumns3Addr invBitsliceAddr syms).length = 270 := by
  simp only [aes256DecryptFullInstrs, List.length_append, aes256DecryptPrefixInstrs_length,
    CodeCommon.adrpAddPair_length, List.length_cons, List.length_nil]

private theorem map_decode_eq_map_some {ws : List (BitVec 32)}
    (h : (ws.all fun w => (Arm64.decode w).isSome) = true) :
    ws.map Arm64.decode = (decodeWords ws).map some := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases Option.isSome_iff_exists.mp h.1 with ⟨i, hi⟩; simp [decodeWords, decodeWord, hi, ih h.2]

set_option maxRecDepth 2000 in
theorem aes256DecryptTemplateWords_decode_eq :
    aes256DecryptTemplateWords.map Arm64.decode = (decodeWords aes256DecryptTemplateWords).map some :=
  map_decode_eq_map_some (by decide)

set_option maxRecDepth 2000 in
theorem aes256DecryptFullInstrs_template_eq
    (bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr : BitVec 64) :
    (((((((((((decodeWords aes256DecryptTemplateWords)
        |>.set 11 (.bl (bitsliceAddr - 0x2c#64))) |>.set 37 (.bl (invSubBytesAddr - 0x94#64)))
        |>.set 101 (.bl (invMixColumns1Addr - 0x194#64))) |>.set 103 (.bl (invSubBytesAddr - 0x19c#64)))
        |>.set 175 (.bl (invSubBytesAddr - 0x2bc#64))) |>.set 197 (.bl (invMixColumns3Addr - 0x314#64)))
        |>.set 199 (.bl (invSubBytesAddr - 0x31c#64))) |>.set 226 (.bl (invMixColumns2Addr - 0x388#64)))
        |>.set 228 (.bl (invSubBytesAddr - 0x390#64))) |>.set 258 (.bl (invBitsliceAddr - 0x408#64))) =
      aes256DecryptFullInstrs 0#64 bitsliceAddr invSubBytesAddr invMixColumns1Addr
        invMixColumns2Addr invMixColumns3Addr invBitsliceAddr (Aes256DecryptPanicSyms.template 0#64) := by
  dsimp only [aes256DecryptFullInstrs, aes256DecryptPrefixInstrs]
  rw [show adrpAddPair (.gpr 0#5) (0#64 + 0x3a4#64) (Aes256DecryptPanicSyms.template 0#64).sym0
        (Aes256DecryptPanicSyms.template 0#64).relax0 = decodeWords [0x90000000#32, 0x91000000#32] by decide,
      show adrpAddPair (.gpr 0#5) (0#64 + 0x420#64) (Aes256DecryptPanicSyms.template 0#64).sym1
        (Aes256DecryptPanicSyms.template 0#64).relax1 = decodeWords [0x90000000#32, 0x91000000#32] by decide,
      show adrpAddPair (.gpr 0#5) (0#64 + 0x42c#64) (Aes256DecryptPanicSyms.template 0#64).sym2
        (Aes256DecryptPanicSyms.template 0#64).relax2 = decodeWords [0x90000000#32, 0x91000000#32] by decide]
  simp only [Aes256DecryptPanicSyms.template, BitVec.zero_add, BitVec.sub_self,
    show Instr.bl 0#64 = decodeWord 0x94000000#32 by decide]
  unfold decodeWords aes256DecryptTemplateWords decPrologueWords decArk14Words decShiftAWords
    decShiftBWords decLoopArk1Words decImc0HeadWords decImc0TailWords decLoopArk3Words
    decLoopGuardWords decLoopArk2Words decLoopLatchWords decArk0Words decRetWords
  generalize decodeWord = f; rfl

/-! ## 3. Callee Bundle & Subroutine Contract -/

/-- Bundles `subroutine_ok` contracts for the 6 fixslice64 leaf subroutines called by `aes256_decrypt`. -/
structure Aes256DecryptCallees (P : Program)
    (bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr : BitVec 64) : Prop where
  bitslice_ok : subroutine_ok P bitsliceAddr bitslice4Spec
  invSubBytes_ok : subroutine_ok P invSubBytesAddr invSubBytesSpec
  invMixColumns1_ok : subroutine_ok P invMixColumns1Addr invMixColumns1Spec
  invMixColumns2_ok : subroutine_ok P invMixColumns2Addr invMixColumns2Spec
  invMixColumns3_ok : subroutine_ok P invMixColumns3Addr invMixColumns3Spec
  invBitslice_ok : subroutine_ok P invBitsliceAddr invBitsliceSpec

theorem Aes256DecryptCallees.of_hasInstrs {P : Program}
    {bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr : BitVec 64}
    (hBs : hasInstrs P bitsliceAddr bitsliceInstrs) (hIsb : hasInstrs P invSubBytesAddr invSubBytesInstrs)
    (hImc1 : hasInstrs P invMixColumns1Addr invMixColumns1Instrs)
    (hImc2 : hasInstrs P invMixColumns2Addr invMixColumns2Instrs)
    (hImc3 : hasInstrs P invMixColumns3Addr invMixColumns3Instrs)
    (hIbs : hasInstrs P invBitsliceAddr invBitsliceInstrs) :
    Aes256DecryptCallees P bitsliceAddr invSubBytesAddr invMixColumns1Addr
      invMixColumns2Addr invMixColumns3Addr invBitsliceAddr :=
  ⟨bitslice4_ok hBs, SboxCode.invSubBytes_ok hIsb, MixCode.invMixColumns1_ok hImc1,
   MixCode.invMixColumns2_ok hImc2, MixCode.invMixColumns3_ok hImc3, Bitslice.invBitslice_ok hIbs⟩

/-- Separation-logic contract for `fixslice64::aes256_decrypt` (`112 + 96 = 208` B downward stack). -/
@[expose] def aes256DecryptSpec :
    Spec (Bool × BitVec 64 × BitVec 64 × BitVec 64 × Model.FsKeys256 × Blocks4) where
  pre := fun (ro, outPtr, keysPtr, inPtr, ks, bs) s0 =>
    ⌜s0.readReg64 .x0 = keysPtr ∧ s0.readReg64 .x1 = inPtr ∧ s0.readReg64 .x8 = outPtr ∧ Blocks4.Wf bs⌝ ∗
    (fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion outPtr 64 ∗ stackFrameAt s0.sp 208)
  post := fun (ro, outPtr, keysPtr, inPtr, ks, bs) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗
      (outPtr ↦ₛ blocks4Bytes (Model.aes256DecryptFs ks bs)) ∗ stackFrameAt s0.sp 208)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 4. Byte-Level Bridge Lemmas to `Spec.Aes256.aes256Dec` -/

theorem blocks4Bytes_aes256DecryptFs_quad {key : List (BitVec 8)} (hkey : key.length = 32)
    (b0 b1 b2 b3 : Block) :
    blocks4Bytes (Model.aes256DecryptFs (Model.aes256KeyScheduleFs key)
        ⟨blockToBytesLE b0, blockToBytesLE b1, blockToBytesLE b2, blockToBytesLE b3⟩) =
      blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) b0) ++
      blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) b1) ++
      blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) b2) ++
      blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) b3) := by
  rw [Equiv.aes256DecryptFs_le hkey b0 b1 b2 b3]; rfl

theorem blocks4Bytes_aes256DecryptFs_single {key : List (BitVec 8)} (hkey : key.length = 32)
    (b0 : Block) {b1 b2 b3 : List (BitVec 8)}
    (hb1 : b1.length = 16) (hb2 : b2.length = 16) (hb3 : b3.length = 16) :
    (blocks4Bytes (Model.aes256DecryptFs (Model.aes256KeyScheduleFs key)
        ⟨blockToBytesLE b0, b1, b2, b3⟩)).take 16 =
      blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) b0) := by
  rw [Equiv.aes256DecryptFs_eq hkey ⟨Equiv.length_blockToBytesLE b0, hb1, hb2, hb3⟩]
  dsimp only [Blocks4.map, blocks4Bytes, Spec.Aes256.aes256Dec]
  rw [Equiv.keyToBytes32_bytesToKey32 hkey]; simp only [List.append_assoc]
  have hlen := Aes256Roundtrip.length_aes256InvCipher key (blockToBytesLE b0)
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  exact (blockToBytesLE_bytesToBlock _ hlen).symm

/-! ## 5. Algebraic, Framing & Code-Splitting Helpers for `aes256_decrypt` -/

private theorem xor_left_comm (x y z : BitVec 64) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc]

private theorem mask_or_lsl8_eq_xor (y : BitVec 64) :
    ((y &&& 0x00ff000000ff0000#64) ||| ((y &&& 0x00ff000000ff0000#64) <<< 8)) =
      ((y &&& 0x00ff000000ff0000#64) ^^^ ((y &&& 0x00ff000000ff0000#64) <<< 8)) := by
  have hdisj : ∀ idx : Fin 64, !((0x00ff000000ff0000#64).getLsbD idx.val &&
      (!decide (idx.val < 8) && (0x00ff000000ff0000#64).getLsbD (idx.val - 8))) = true := by decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi; have hi' := hdisj ⟨i, hi⟩
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  revert hi'; generalize (0x00ff000000ff0000#64).getLsbD i = m0, (0x00ff000000ff0000#64).getLsbD (i - 8) = m1,
    decide (i < 8) = c8, y.getLsbD i = b0, y.getLsbD (i - 8) = b1
  cases m0 <;> cases m1 <;> cases c8 <;> cases b0 <;> cases b1 <;> decide

private theorem deltaSwap1_shiftRows2_eq (x : BitVec 64) :
    ((((x ^^^ (x >>> 8)) &&& 0x00ff000000ff0000#64) ||| (((x ^^^ (x >>> 8)) &&& 0x00ff000000ff0000#64) <<< 8)) ^^^ x) =
      Model.deltaSwap1 x 8 0x00ff000000ff0000#64 := by
  rw [mask_or_lsl8_eq_xor]; unfold Model.deltaSwap1; simp only [BitVec.xor_comm, xor_left_comm]

private theorem ror16_eq_rotateRows1 (x : BitVec 64) : x.rotateRight 16 = Model.rotateRows1 x := rfl
private theorem ror32_eq_rotateRows2 (x : BitVec 64) : x.rotateRight 32 = Model.rotateRows2 x := rfl

private def decImc0Asm (st rk : Model.FsState) : Model.FsState :=
  let a0 := st.s0 ^^^ rk.s0; let a1 := st.s1 ^^^ rk.s1; let a2 := st.s2 ^^^ rk.s2; let a3 := st.s3 ^^^ rk.s3
  let a4 := st.s4 ^^^ rk.s4; let a5 := st.s5 ^^^ rk.s5; let a6 := st.s6 ^^^ rk.s6; let a7 := st.s7 ^^^ rk.s7
  let c0 := a0 ^^^ a0.rotateRight 16; let c1 := a1 ^^^ a1.rotateRight 16; let c2 := a2 ^^^ a2.rotateRight 16
  let c3 := a3 ^^^ a3.rotateRight 16; let c4 := a4 ^^^ a4.rotateRight 16; let c5 := a5 ^^^ a5.rotateRight 16
  let c6 := a6 ^^^ a6.rotateRight 16; let c7 := a7 ^^^ a7.rotateRight 16
  let d6 := a6 ^^^ c5; let d7 := a7 ^^^ c6; let d0 := c7 ^^^ a0; let d1 := (a1 ^^^ c0) ^^^ c7
  let s67 := d7 ^^^ d6; let d2 := a2 ^^^ c1; let e0 := d6 ^^^ c0; let e1 := s67 ^^^ c1
  let d3 := (a3 ^^^ c2) ^^^ c7; let e2 := (d7 ^^^ c2) ^^^ d0; let e3 := (d6 ^^^ c3) ^^^ d1
  let d5 := a5 ^^^ c4; let e5 := (d7 ^^^ c5) ^^^ d3; let d4 := (a4 ^^^ c3) ^^^ c7
  let e4 := (c4 ^^^ d2) ^^^ s67; let e6 := d4 ^^^ c6; let e7 := c7 ^^^ d5
  ⟨(e0 ^^^ e0.rotateRight 32) ^^^ d0, (e1 ^^^ e1.rotateRight 32) ^^^ d1,
   (d2 ^^^ e2.rotateRight 32) ^^^ e2, (d3 ^^^ e3.rotateRight 32) ^^^ e3,
   (d4 ^^^ e4.rotateRight 32) ^^^ e4, (d5 ^^^ e5.rotateRight 32) ^^^ e5,
   (d6 ^^^ e6.rotateRight 32) ^^^ e6, (d7 ^^^ e7.rotateRight 32) ^^^ e7⟩

private theorem decImc0Asm_eq (st rk : Model.FsState) :
    decImc0Asm st rk = Model.invMixColumns0 (Model.addRoundKeyFs st rk) := by
  dsimp only [decImc0Asm, Model.invMixColumns0, Model.invMixColumnsGen, Model.addRoundKeyFs, Model.FsState.zipWith]
  simp only [ror16_eq_rotateRows1, ror32_eq_rotateRows2]
  generalize st.s0 ^^^ rk.s0 = a0, st.s1 ^^^ rk.s1 = a1, st.s2 ^^^ rk.s2 = a2, st.s3 ^^^ rk.s3 = a3,
    st.s4 ^^^ rk.s4 = a4, st.s5 ^^^ rk.s5 = a5, st.s6 ^^^ rk.s6 = a6, st.s7 ^^^ rk.s7 = a7
  generalize a0 ^^^ Model.rotateRows1 a0 = c0, a1 ^^^ Model.rotateRows1 a1 = c1,
    a2 ^^^ Model.rotateRows1 a2 = c2, a3 ^^^ Model.rotateRows1 a3 = c3,
    a4 ^^^ Model.rotateRows1 a4 = c4, a5 ^^^ Model.rotateRows1 a5 = c5,
    a6 ^^^ Model.rotateRows1 a6 = c6, a7 ^^^ Model.rotateRows1 a7 = c7
  generalize (a1 ^^^ c0) ^^^ c7 = d1, a2 ^^^ c1 = d2, (a3 ^^^ c2) ^^^ c7 = d3,
    (a4 ^^^ c3) ^^^ c7 = d4, a5 ^^^ c4 = d5, a6 ^^^ c5 = d6, a7 ^^^ c6 = d7
  ext1 <;> simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

private def decAfterRounds (ks : Model.FsKeys256) (st0 : Model.FsState) : Nat → Model.FsState
  | 0 => st0 | k + 1 => Model.decRoundFs ks (13 - k) (decAfterRounds ks st0 k)

private theorem decAfterRounds_13_eq (ks : Model.FsKeys256) (st0 : Model.FsState) :
    (List.range 13).foldl (fun st i => Model.decRoundFs ks (13 - i) st) st0 =
      decAfterRounds ks st0 13 := rfl

private theorem sep_focus_head (A B : SepProp) : ∃ F, A ∗ B = A ∗ F := ⟨B, rfl⟩
private theorem sep_focus_tail {A Target Rest : SepProp} (h : ∃ F, Rest = Target ∗ F) :
    ∃ F, A ∗ Rest = Target ∗ F := by rcases h with ⟨F, rfl⟩; exact ⟨A ∗ F, by sep_ac_rfl⟩
private theorem sep_focus_last (A : SepProp) : ∃ F, A = A ∗ F := ⟨SepProp.emp, (sepConj_emp A).symm⟩

private theorem fsKeys256At_focus (ptr : BitVec 64) (ks : Model.FsKeys256) (r : Nat) (hr : r ≤ 14) :
    ∃ F_ks, fsKeys256At ptr ks = fsStateAt (ptr + BitVec.ofNat 64 (64 * r)) (ks.getRound r) ∗ F_ks := by
  unfold fsKeys256At Model.FsKeys256.getRound; let t {A T R} := @sep_focus_tail A T R
  match r with
  | 0 => rw [BitVec.add_zero ptr]; exact sep_focus_head _ _
  | 1 => exact t (sep_focus_head _ _)
  | 2 => exact t (t (sep_focus_head _ _))
  | 3 => exact t (t (t (sep_focus_head _ _)))
  | 4 => exact t (t (t (t (sep_focus_head _ _))))
  | 5 => exact t (t (t (t (t (sep_focus_head _ _)))))
  | 6 => exact t (t (t (t (t (t (sep_focus_head _ _))))))
  | 7 => exact t (t (t (t (t (t (t (sep_focus_head _ _)))))))
  | 8 => exact t (t (t (t (t (t (t (t (sep_focus_head _ _))))))))
  | 9 => exact t (t (t (t (t (t (t (t (t (sep_focus_head _ _)))))))))
  | 10 => exact t (t (t (t (t (t (t (t (t (t (sep_focus_head _ _))))))))))
  | 11 => exact t (t (t (t (t (t (t (t (t (t (t (sep_focus_head _ _)))))))))))
  | 12 => exact t (t (t (t (t (t (t (t (t (t (t (t (sep_focus_head _ _))))))))))))
  | 13 => exact t (t (t (t (t (t (t (t (t (t (t (t (t (sep_focus_head _ _)))))))))))))
  | 14 => exact t (t (t (t (t (t (t (t (t (t (t (t (t (t (sep_focus_last _))))))))))))))
  | n + 15 => omega

private def decSavedAt (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem stackFrameAt_208_unpack (sp0 : BitVec 64) :
    stackFrameAt sp0 208 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (((sp0 - 48#64) ↦₆₄ w0) ∗ ((sp0 - 40#64) ↦₆₄ w1) ∗ ((sp0 - 32#64) ↦₆₄ w2) ∗
         ((sp0 - 24#64) ↦₆₄ w3) ∗ ((sp0 - 16#64) ↦₆₄ w4) ∗ ((sp0 - 8#64) ↦₆₄ w5)) ∗
        memRegion (sp0 - 112#64) 64 ∗ stackFrameAt (sp0 - 112#64) 96 := by
  rw [stackFrameAt_split sp0 112 96, stackFrameAt_split sp0 48 64,
      stackFrameAt_eq_memRegion (sp0 - 48#64) 64,
      show sp0 - 48#64 - BitVec.ofNat 64 64 = sp0 - 112#64 by bv_omega]
  simp only [wp_norm, sepExists_sepConj_left, sepConj_assoc]; exact Entails.refl _

private theorem stackFrameAt_208_repack (sp0 : BitVec 64) (s0 : State) (st : Model.FsState) :
    decSavedAt sp0 s0 ∗ fsStateAt (sp0 - 112#64) st ∗ stackFrameAt (sp0 - 112#64) 96 ⊢
      stackFrameAt sp0 208 := by
  rw [stackFrameAt_split sp0 112 96, stackFrameAt_split sp0 48 64,
      stackFrameAt_eq_memRegion (sp0 - 48#64) 64,
      show sp0 - 48#64 - BitVec.ofNat 64 64 = sp0 - 112#64 by bv_omega, ← sepConj_assoc]
  apply sepConj_mono_left; refine sepConj_mono ?_ (CodeCommon.fsStateAt_entails_memRegion _ st)
  unfold decSavedAt; simp only [wp_norm]
  exact Entails.sepExists_right _ <| Entails.sepExists_right _ <| Entails.sepExists_right _ <|
    Entails.sepExists_right _ <| Entails.sepExists_right _ <| Entails.sepExists_right _ <|
    Entails.refl _

private def DecPreserved (s0 s : State) : Prop :=
  PureStepPreserved s0 s ∧ s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧ s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧ s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧ calleeSavedVRegs s = calleeSavedVRegs s0

private theorem DecPreserved.refl (s0 : State) : DecPreserved s0 s0 :=
  ⟨PureStepPreserved.refl s0, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem DecPreserved.trans {s0 s1 s2 : State}
    (h01 : DecPreserved s0 s1) (h12 : DecPreserved s1 s2) : DecPreserved s0 s2 :=
  ⟨h01.1.trans h12.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

private theorem DecPreserved.of_callee {s1 s2 : State}
    (hp : PureStepPreserved s1 s2) (hcs : CalleeSavedPreserved s1 s2) : DecPreserved s1 s2 :=
  ⟨hp, hcs.2.2.2.2.1, hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem DecPreserved.to_calleeSaved {s0 sf : State} (h : DecPreserved s0 sf)
    (hx19 : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (hx20 : sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (hx21 : sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (hx22 : sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5))
    (hx29 : sf.readReg64 Reg.fp = s0.readReg64 Reg.fp) : CalleeSavedPreserved s0 sf :=
  ⟨hx19, hx20, hx21, hx22, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, hx29, h.2.2.2.2.2.2.2⟩

private theorem hasInstrs_split {P : Program} {base : BitVec 64} {xs ys : List Instr}
    (h : hasInstrs P base (xs ++ ys)) :
    hasInstrs P base xs ∧ hasInstrs P (base + BitVec.ofNat 64 (4 * xs.length)) ys := by
  refine ⟨hasInstrs_prefix h, fun j hj => ?_⟩
  have hf := h (xs.length + j) (by simp [List.length_append]; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at hf
  simpa [show base + BitVec.ofNat 64 (4 * xs.length) + BitVec.ofNat 64 (4 * j) =
      base + BitVec.ofNat 64 (4 * (xs.length + j)) by bv_omega, Nat.add_sub_cancel_left] using hf

private theorem hasInstrs_singleton {P : Program} {base : BitVec 64} {ins : Instr}
    (h : hasInstrs P base [ins]) : P.fetch base = some ins := by simpa using h 0 Nat.zero_lt_one

private structure DecCodeSegs (P : Program)
    (fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr : BitVec 64) : Prop where
  prologue : hasInstrs P fnAddr (decodeWords decPrologueWords)
  bl_bs : P.fetch (fnAddr + 0x2c#64) = some (.bl (bitsliceAddr - (fnAddr + 0x2c#64)))
  ark14 : hasInstrs P (fnAddr + 0x30#64) (decodeWords decArk14Words)
  bl_isb14 : P.fetch (fnAddr + 0x94#64) = some (.bl (invSubBytesAddr - (fnAddr + 0x94#64)))
  shiftA : hasInstrs P (fnAddr + 0x98#64) (decodeWords decShiftAWords)
  shiftB : hasInstrs P (fnAddr + 0xe0#64) (decodeWords decShiftBWords)
  ark1 : hasInstrs P (fnAddr + 0x140#64) (decodeWords decLoopArk1Words)
  bl_imc1 : P.fetch (fnAddr + 0x194#64) = some (.bl (invMixColumns1Addr - (fnAddr + 0x194#64)))
  mov1 : hasInstrs P (fnAddr + 0x198#64) (decodeWords [0x910003e0#32])
  bl_isb1 : P.fetch (fnAddr + 0x19c#64) = some (.bl (invSubBytesAddr - (fnAddr + 0x19c#64)))
  exit_br : hasInstrs P (fnAddr + 0x1a0#64) (decodeWords [0xb10042df#32, 0x54001060#32])
  imc0H : hasInstrs P (fnAddr + 0x1a8#64) (decodeWords decImc0HeadWords)
  imc0T : hasInstrs P (fnAddr + 0x230#64) (decodeWords decImc0TailWords)
  bl_isb0 : P.fetch (fnAddr + 0x2bc#64) = some (.bl (invSubBytesAddr - (fnAddr + 0x2bc#64)))
  ark3 : hasInstrs P (fnAddr + 0x2c0#64) (decodeWords decLoopArk3Words)
  bl_imc3 : P.fetch (fnAddr + 0x314#64) = some (.bl (invMixColumns3Addr - (fnAddr + 0x314#64)))
  mov3 : hasInstrs P (fnAddr + 0x318#64) (decodeWords [0x910003e0#32])
  bl_isb3 : P.fetch (fnAddr + 0x31c#64) = some (.bl (invSubBytesAddr - (fnAddr + 0x31c#64)))
  guard_br : hasInstrs P (fnAddr + 0x320#64) (decodeWords decLoopGuardWords)
  ark2 : hasInstrs P (fnAddr + 0x334#64) (decodeWords decLoopArk2Words)
  bl_imc2 : P.fetch (fnAddr + 0x388#64) = some (.bl (invMixColumns2Addr - (fnAddr + 0x388#64)))
  mov2 : hasInstrs P (fnAddr + 0x38c#64) (decodeWords [0x910003e0#32])
  bl_isb2 : P.fetch (fnAddr + 0x390#64) = some (.bl (invSubBytesAddr - (fnAddr + 0x390#64)))
  latch : hasInstrs P (fnAddr + 0x394#64) (decodeWords decLoopLatchWords)
  ark0 : hasInstrs P (fnAddr + 0x3b0#64) (decodeWords decArk0Words)
  bl_ibs : P.fetch (fnAddr + 0x408#64) = some (.bl (invBitsliceAddr - (fnAddr + 0x408#64)))
  ret_seg : hasInstrs P (fnAddr + 0x40c#64) (decodeWords decRetWords)

private theorem hasInstrs_split_next {P : Program} {fnAddr off1 : BitVec 64} (off2 : BitVec 64)
    {xs ys : List Instr} (h : hasInstrs P (fnAddr + off1) (xs ++ ys))
    (hoff : off1 + BitVec.ofNat 64 (4 * xs.length) = off2) :
    hasInstrs P (fnAddr + off1) xs ∧ hasInstrs P (fnAddr + off2) ys := by
  obtain ⟨h1, h2⟩ := hasInstrs_split h
  exact ⟨h1, (show fnAddr + off1 + BitVec.ofNat 64 (4 * xs.length) = fnAddr + off2 by
    rw [BitVec.add_assoc, hoff]) ▸ h2⟩

private theorem DecCodeSegs.of_hasInstrs {P : Program}
    {fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr panic0Sym : BitVec 64}
    {panic0Relax : Bool} {panic0Target : BitVec 64}
    (hc : hasInstrs P fnAddr (aes256DecryptPrefixInstrs fnAddr bitsliceAddr invSubBytesAddr
      invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr panic0Sym panic0Relax panic0Target)) :
    DecCodeSegs P fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
      invMixColumns3Addr invBitsliceAddr := by
  simp only [aes256DecryptPrefixInstrs, List.flatten_cons, List.flatten_nil, List.append_nil] at hc
  obtain ⟨s0, hc⟩ := hasInstrs_split hc; change hasInstrs P (fnAddr + 0x2c#64) _ at hc
  obtain ⟨s1, hc⟩ := hasInstrs_split_next 0x30#64 hc rfl; obtain ⟨s2, hc⟩ := hasInstrs_split_next 0x94#64 hc rfl
  obtain ⟨s3, hc⟩ := hasInstrs_split_next 0x98#64 hc rfl; obtain ⟨s4, hc⟩ := hasInstrs_split_next 0xe0#64 hc rfl
  obtain ⟨s5, hc⟩ := hasInstrs_split_next 0x140#64 hc rfl; obtain ⟨s6, hc⟩ := hasInstrs_split_next 0x194#64 hc rfl
  obtain ⟨s7, hc⟩ := hasInstrs_split_next 0x198#64 hc rfl; obtain ⟨s8, hc⟩ := hasInstrs_split_next 0x19c#64 hc rfl
  obtain ⟨s9, hc⟩ := hasInstrs_split_next 0x1a0#64 hc rfl; obtain ⟨s10, hc⟩ := hasInstrs_split_next 0x1a8#64 hc rfl
  obtain ⟨s11, hc⟩ := hasInstrs_split_next 0x230#64 hc rfl; obtain ⟨s12, hc⟩ := hasInstrs_split_next 0x2bc#64 hc rfl
  obtain ⟨s13, hc⟩ := hasInstrs_split_next 0x2c0#64 hc rfl; obtain ⟨s14, hc⟩ := hasInstrs_split_next 0x314#64 hc rfl
  obtain ⟨s15, hc⟩ := hasInstrs_split_next 0x318#64 hc rfl; obtain ⟨s16, hc⟩ := hasInstrs_split_next 0x31c#64 hc rfl
  obtain ⟨s17, hc⟩ := hasInstrs_split_next 0x320#64 hc rfl; obtain ⟨s18, hc⟩ := hasInstrs_split_next 0x334#64 hc rfl
  obtain ⟨s19, hc⟩ := hasInstrs_split_next 0x388#64 hc rfl; obtain ⟨s20, hc⟩ := hasInstrs_split_next 0x38c#64 hc rfl
  obtain ⟨s21, hc⟩ := hasInstrs_split_next 0x390#64 hc rfl; obtain ⟨s22, hc⟩ := hasInstrs_split_next 0x394#64 hc rfl
  obtain ⟨s23, hc⟩ := hasInstrs_split_next 0x3a4#64 hc rfl
  obtain ⟨_, hc⟩ := hasInstrs_split_next 0x3ac#64 hc (by simp [CodeCommon.adrpAddPair_length])
  obtain ⟨_, hc⟩ := hasInstrs_split_next 0x3b0#64 hc rfl; obtain ⟨s26, hc⟩ := hasInstrs_split_next 0x408#64 hc rfl
  obtain ⟨s27, s28⟩ := hasInstrs_split_next 0x40c#64 hc rfl
  exact ⟨s0, hasInstrs_singleton s1, s2, hasInstrs_singleton s3, s4, s5, s6, hasInstrs_singleton s7,
    s8, hasInstrs_singleton s9, s10, s11, s12, hasInstrs_singleton s13, s14, hasInstrs_singleton s15,
    s16, hasInstrs_singleton s17, s18, s19, hasInstrs_singleton s20, s21, hasInstrs_singleton s22,
    s23, s26, hasInstrs_singleton s27, s28⟩

/-! ## 6. Call Combinators & Straight-Line Chunk Lemmas -/

private structure DecAnchor (s0 : State) (outPtr keysPtr : BitVec 64) (s : State) : Prop where
  sp : s.sp = s0.sp - 112#64
  x19 : s.readReg64 (.gpr 19#5) = outPtr
  x20 : s.readReg64 (.gpr 20#5) = keysPtr
  pres : DecPreserved s0 s

private theorem DecAnchor.step {s0 s sf : State} {outPtr keysPtr : BitVec 64} (ha : DecAnchor s0 outPtr keysPtr s)
    (hsp : sf.sp = s0.sp - 112#64 := by first | exact ha.sp | simp [wp_norm, arm64_norm, ha.sp])
    (hx19 : sf.readReg64 (.gpr 19#5) = outPtr := by first | exact ha.x19 | simp [wp_norm, arm64_norm, ha.x19])
    (hx20 : sf.readReg64 (.gpr 20#5) = keysPtr := by first | exact ha.x20 | simp [wp_norm, arm64_norm, ha.x20])
    (hproj : pureStepProj sf = pureStepProj s)
    (hperm : sf.mem.perm = s.mem.perm := by first | rfl | simp [wp_norm, arm64_norm])
    (h23 : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by first | rfl | simp [wp_norm, arm64_norm])
    (h24 : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by first | rfl | simp [wp_norm, arm64_norm])
    (h25 : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := by first | rfl | simp [wp_norm, arm64_norm])
    (h26 : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) := by first | rfl | simp [wp_norm, arm64_norm])
    (h27 : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by first | rfl | simp [wp_norm, arm64_norm])
    (h28 : sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by first | rfl | simp [wp_norm, arm64_norm])
    (hv : calleeSavedVRegs sf = calleeSavedVRegs s := by first | rfl | simp [wp_norm, arm64_norm]) :
    DecAnchor s0 outPtr keysPtr sf :=
  ⟨hsp, hx19, hx20, ha.pres.trans ⟨PureStepPreserved.of_proj_perm hproj hperm, h23, h24, h25, h26, h27, h28, hv⟩⟩

private theorem DecAnchor.step_call {s0 s sf : State} {outPtr keysPtr : BitVec 64}
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp : sf.sp = s.sp)
    (hcs : CalleeSavedPreserved s sf) (hp : PureStepPreserved s sf) :
    DecAnchor s0 outPtr keysPtr sf ∧ sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
    sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) :=
  ⟨⟨hsp.trans ha.sp, hcs.1.trans ha.x19, hcs.2.1.trans ha.x20, ha.pres.trans (DecPreserved.of_callee hp hcs)⟩, hcs.2.2.1, hcs.2.2.2.1⟩

private theorem sp_sub112_and_15 {s0 : State} (hsp : s0.spAligned = true) :
    (s0.sp - 112#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub_of_dvd 112 hsp)
private theorem spAligned_of_eq {s : State} {sp_local : BitVec 64}
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) : s.spAligned = true := by
  simp [State.spAligned, hsp, hsp_loc]

private theorem step_bl_call {α : Type} {P : Program} {pc_bl calleeAddr target_pc : BitVec 64} {spec : Spec α}
    (hf : P.fetch pc_bl = some (.bl (calleeAddr - pc_bl))) (hcall : subroutine_ok P calleeAddr spec)
    (x : α) {s : State} {Pre F PreSpatial PostSpatial : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_al : s.spAligned = true) (hent : Pre ⊢ PreSpatial ∗ F)
    (hpre_call : ∀ sc, sc = P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl) → PreSpatial ⊢ spec.pre x sc)
    (hpost_call : ∀ sc sf, sc = P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl) →
      sf.sp = s.sp → spec.post x sc sf = (⌜PureStepPreserved sc sf⌝ ∗ PostSpatial))
    (hno_panic : ∀ sc sf, spec.onPanic x sc sf = ⌜False⌝ := by intros; rfl)
    (hno_exit : ∀ c sc sf, spec.onExit x c sc sf = ⌜False⌝ := by intros; rfl)
    (hno_oom : ∀ sc sf, spec.onOom x sc sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf → SepWP P target_pc sf (PostSpatial ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  let s_call := P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl)
  have hmem_sc : s_call.mem = s.mem := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hpc_sc : s_call.pc = calleeAddr := by
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; bv_omega
  have hsp_sc_eq : s_call.sp = s.sp := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hp_sc : PureStepPreserved s s_call := PureStepPreserved.of_proj_perm
    (by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]) (by simp [hmem_sc])
  have hcs_sc : CalleeSavedPreserved s s_call := by
    rw [CalleeSavedPreserved.iff_regs]; simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  apply SepWP.step_pure hpc hrun hf rfl hmem_sc
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc_sc
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun])
    (by simp only [State.spAligned]; exact hsp_al)
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; try rfl) ?_ ?_ ?_ ?_ ?_
  · intro R hm
    exact Satisfies.mono (by rw [← sepConj_assoc]; exact sepConj_mono_left (Entails.trans hent (sepConj_mono_left (hpre_call s_call rfl)))) hm
  · intro _ _ _; rw [hno_panic]; exact not_satisfies_false_sepConj
  · intro _ _ _ _; rw [hno_exit]; exact not_satisfies_false_sepConj
  · intro sf hpc_f hrun_f hsp_f hcs_f; have hsp_f' := hsp_f.trans hsp_sc_eq
    rw [hpost_call s_call sf rfl hsp_f', sepConj_assoc]; apply SepWP.pure_elim; intro hp_f
    exact hnext sf hpc_f hrun_f hsp_f' (hcs_sc.trans hcs_f) (hp_sc.trans hp_f)
  · intro _ _ _ ho; rw [hno_oom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem call_bitslice {P : Program} {pc_bl bitsliceAddr target_pc outPtr keysPtr inPtr : BitVec 64}
    {ro : Bool} {bs : Blocks4} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (bitsliceAddr - pc_bl))) (hbs : subroutine_ok P bitsliceAddr bitslice4Spec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (ha : DecAnchor s0 outPtr keysPtr s)
    (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hx0 : s.readReg64 (.gpr 0#5) = s0.sp - 112#64)
    (hx1 : s.readReg64 (.gpr 1#5) = inPtr) (hx2 : s.readReg64 (.gpr 2#5) = inPtr + 16#64)
    (hx3 : s.readReg64 (.gpr 3#5) = inPtr + 32#64) (hx4 : s.readReg64 (.gpr 4#5) = inPtr + 48#64) (hwf : Blocks4.Wf bs)
    (hnext : ∀ sf, sf.pc = pc_bl + 4#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.bitslice bs) ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ F) post oom) :
    SepWP P target_pc s (memRegion (s0.sp - 112#64) 64 ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ F) post oom := by
  refine step_bl_call hf hbs (ro, s0.sp - 112#64, inPtr, bs)
    (PreSpatial := bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion (s0.sp - 112#64) 64)
    (PostSpatial := bytesAt ro inPtr (blocks4Bytes bs) ∗ fsStateAt (s0.sp - 112#64) (Model.bitslice bs))
    (F := F) hpc hrun (spAligned_of_eq ha.sp hsp_loc) (Entails.of_eq_explicit (by sep_ac_rfl)) ?_ (fun _ _ _ _ => rfl) (hnext := ?_)
  · intro s_call hsc; dsimp only [bitslice4Spec]; refine Entails.pure_right ?_ (Entails.refl _)
    simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0, hx1, hx2, hx3, hx4, hwf]
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f
    exact SepWP.weaken_pre (Entails.of_eq_explicit (by sep_ac_rfl)) (hnext sf hpc_f hrun_f (ha.step_call hsp_f hcs_f hp_f).1)

private theorem call_inv_sub_bytes {P : Program} {pc_bl invSubBytesAddr target_pc outPtr keysPtr : BitVec 64}
    {st : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (invSubBytesAddr - pc_bl))) (hisb : subroutine_ok P invSubBytesAddr invSubBytesSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (ha : DecAnchor s0 outPtr keysPtr s)
    (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hx0 : s.readReg64 (.gpr 0#5) = s0.sp - 112#64)
    (hnext : ∀ sf, sf.pc = pc_bl + 4#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.invSubBytesFs st) ∗ stackFrameAt (s0.sp - 112#64) 96 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ stackFrameAt (s0.sp - 112#64) 96 ∗ F) post oom := by
  refine step_bl_call hf hisb (s0.sp - 112#64, st)
    (PreSpatial := fsStateAt (s0.sp - 112#64) st ∗ stackFrameAt (s0.sp - 112#64) 96)
    (PostSpatial := fsStateAt (s0.sp - 112#64) (Model.invSubBytesFs st) ∗ stackFrameAt (s0.sp - 112#64) 96)
    (F := F) hpc hrun (spAligned_of_eq ha.sp hsp_loc) (Entails.of_eq_explicit (by sep_ac_rfl)) ?_ ?_ (hnext := ?_)
  · intro s_call hsc; dsimp only [invSubBytesSpec]
    rw [show s_call.sp = s0.sp - 112#64 by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, ha.sp]]
    exact Entails.pure_right (by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0]) (Entails.refl _)
  · intro s_call _ hsc _; dsimp only [invSubBytesSpec]
    rw [show s_call.sp = s0.sp - 112#64 by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, ha.sp]]
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f; rcases ha.step_call hsp_f hcs_f hp_f with ⟨ha_f, hx21_f, hx22_f⟩
    rw [sepConj_assoc]; exact hnext sf hpc_f hrun_f ha_f hx21_f hx22_f

private theorem call_inv_mix_columns {P : Program} (imcFn : Model.FsState → Model.FsState)
    {imcSpec : Spec (BitVec 64 × Model.FsState)} {pc_bl imcAddr target_pc outPtr keysPtr : BitVec 64}
    {st : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (imcAddr - pc_bl))) (himc : subroutine_ok P imcAddr imcSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (ha : DecAnchor s0 outPtr keysPtr s)
    (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hx0 : s.readReg64 (.gpr 0#5) = s0.sp - 112#64)
    (hspec : imcSpec = {
      pre := fun (ptr, st) sc => ⌜sc.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt sc.sp 16)
      post := fun (ptr, st) sc sf => ⌜PureStepPreserved sc sf⌝ ∗ (fsStateAt ptr (imcFn st) ∗ stackFrameAt sc.sp 16)
      onPanic := fun _ _ _ => ⌜False⌝, onExit := fun _ _ _ _ => ⌜False⌝, onOom := fun _ _ _ => ⌜False⌝ } := by rfl)
    (hnext : ∀ sf, sf.pc = pc_bl + 4#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (imcFn st) ∗ stackFrameAt (s0.sp - 112#64) 96 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ stackFrameAt (s0.sp - 112#64) 96 ∗ F) post oom := by
  subst hspec; have hsplit := stackFrameAt_split (s0.sp - 112#64) 16 80
  refine step_bl_call hf himc (s0.sp - 112#64, st)
    (PreSpatial := fsStateAt (s0.sp - 112#64) st ∗ stackFrameAt (s0.sp - 112#64) 16)
    (PostSpatial := fsStateAt (s0.sp - 112#64) (imcFn st) ∗ stackFrameAt (s0.sp - 112#64) 16)
    (F := stackFrameAt (s0.sp - 112#64 - 16#64) 80 ∗ F) hpc hrun (spAligned_of_eq ha.sp hsp_loc)
    (Entails.of_eq_explicit (by rw [hsplit]; sep_ac_rfl)) ?_ ?_ (hnext := ?_)
  · intro s_call hsc; dsimp only
    rw [show s_call.sp = s0.sp - 112#64 by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, ha.sp]]
    exact Entails.pure_right (by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0]) (Entails.refl _)
  · intro s_call _ hsc _; dsimp only
    rw [show s_call.sp = s0.sp - 112#64 by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, ha.sp]]
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f; rcases ha.step_call hsp_f hcs_f hp_f with ⟨ha_f, hx21_f, hx22_f⟩
    exact SepWP.weaken_pre (Entails.of_eq_explicit (by rw [hsplit]; sep_ac_rfl)) (hnext sf hpc_f hrun_f ha_f hx21_f hx22_f)

private theorem call_inv_bitslice {P : Program} {pc_bl invBitsliceAddr target_pc outPtr keysPtr : BitVec 64}
    {st : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (invBitsliceAddr - pc_bl))) (hibs : subroutine_ok P invBitsliceAddr invBitsliceSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (ha : DecAnchor s0 outPtr keysPtr s)
    (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hx0 : s.readReg64 (.gpr 0#5) = outPtr) (hx1 : s.readReg64 (.gpr 1#5) = s0.sp - 112#64)
    (hnext : ∀ sf, sf.pc = pc_bl + 4#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      SepWP P target_pc sf ((outPtr ↦ₛ blocks4Bytes (Model.invBitslice st)) ∗ fsStateAt (s0.sp - 112#64) st ∗ F) post oom) :
    SepWP P target_pc s (memRegion outPtr 64 ∗ fsStateAt (s0.sp - 112#64) st ∗ F) post oom := by
  refine step_bl_call hf hibs (outPtr, s0.sp - 112#64, st)
    (PreSpatial := fsStateAt (s0.sp - 112#64) st ∗ memRegion outPtr 64)
    (PostSpatial := fsStateAt (s0.sp - 112#64) st ∗ (outPtr ↦ₛ blocks4Bytes (Model.invBitslice st)))
    (F := F) hpc hrun (spAligned_of_eq ha.sp hsp_loc) (Entails.of_eq_explicit (by sep_ac_rfl)) ?_ (fun _ _ _ _ => rfl) (hnext := ?_)
  · intro s_call hsc; dsimp only [invBitsliceSpec]; refine Entails.pure_right ?_ (Entails.refl _)
    simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0, hx1]
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f
    exact SepWP.weaken_pre (Entails.of_eq_explicit (by sep_ac_rfl)) (hnext sf hpc_f hrun_f (ha.step_call hsp_f hcs_f hp_f).1)

private def ShiftMidRegs (st : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 10#5) = st.s3 ^^^ (st.s3 >>> 8) ∧ s.readReg64 (.gpr 12#5) = st.s2 ∧
  s.readReg64 (.gpr 13#5) = st.s3 ∧ s.readReg64 (.gpr 14#5) = st.s4 ∧
  s.readReg64 (.gpr 15#5) = st.s5 ∧ s.readReg64 (.gpr 16#5) =
    (((st.s2 ^^^ (st.s2 >>> 8)) &&& 0x00ff000000ff0000#64) |||
      (((st.s2 ^^^ (st.s2 >>> 8)) &&& 0x00ff000000ff0000#64) <<< 8))

section
arm64_proof_prelude

private theorem dec_prologue_step {P : Program}
    {fnAddr target_pc outPtr keysPtr inPtr w0 w1 w2 w3 w4 w5 : BitVec 64}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P fnAddr (decodeWords decPrologueWords))
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = keysPtr) (hx1 : s0.readReg64 .x1 = inPtr) (hx8 : s0.readReg64 .x8 = outPtr)
    (hnext : ∀ s1 : State, s1.pc = fnAddr + 0x2c#64 → s1.status = .Running →
      DecAnchor s0 outPtr keysPtr s1 → s1.readReg64 (.gpr 0#5) = s0.sp - 112#64 →
      s1.readReg64 (.gpr 1#5) = inPtr → s1.readReg64 (.gpr 2#5) = inPtr + 16#64 →
      s1.readReg64 (.gpr 3#5) = inPtr + 32#64 → s1.readReg64 (.gpr 4#5) = inPtr + 48#64 →
      SepWP P target_pc s1 (decSavedAt s0.sp s0 ∗ F) post oom) :
    SepWP P target_pc s0
      ((((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗
        ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) ∗ F) post oom := by
  have hsp112 := sp_sub112_and_15 hsp; have_instrs hc 0 11; wp_steps 1
  wp_stp64 hf_1 m1 hm1; wp_stp64 hf_2 m2 hm2; wp_stp64 hf_3 m3 hm3; wp_steps 7
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     ⟨PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm3, hm2, hm1]), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx1])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])

private theorem dec_ark14_step {P : Program} {pc0 target_pc outPtr keysPtr : BitVec 64}
    {st rk14 : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decArk14Words)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x64#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 0#5) = s0.sp - 112#64 →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.addRoundKeyFs st rk14) ∗ fsStateAt (keysPtr + 0x380#64) rk14 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ fsStateAt (keysPtr + 0x380#64) rk14 ∗ F) post oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have hx20 := ha.x20; have_instrs hc 0 25; dsimp only [fsStateAt, Model.addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 10; wp_stp64 hf_10 m1 hm1; wp_steps 6; wp_stp64 hf_17 m2 hm2
  wp_steps 2; wp_stp64 hf_20 m3 hm3; wp_steps 3; wp_stp64 hf_24 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm]) (hperm := by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm])

private theorem dec_shiftA_step {P : Program} {pc0 target_pc outPtr keysPtr : BitVec 64}
    {st : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decShiftAWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x48#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 → sf.readReg64 (.gpr 22#5) = 0x50#64 → ShiftMidRegs st sf →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64)
        { st with s0 := (Model.invShiftRows2 st).s0, s1 := (Model.invShiftRows2 st).s1 } ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ F) post oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have hx20 := ha.x20; have_instrs hc 0 18; dsimp only [fsStateAt, Model.invShiftRows2, Model.shiftRows2, Model.FsState.map]
  wp_steps 17; wp_stp64 hf_17 m1 hm1; wp_conv_pre => simp only [deltaSwap1_shiftRows2_eq]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm]) (hperm := by simp [wp_norm, arm64_norm, hm1]))
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [ShiftMidRegs, wp_norm, arm64_norm])

private theorem dec_shiftB_step {P : Program} {pc0 target_pc outPtr keysPtr : BitVec 64}
    {st : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decShiftBWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64)
    (hx21 : s.readReg64 (.gpr 21#5) = keysPtr + 0x378#64) (hx22 : s.readReg64 (.gpr 22#5) = 0x50#64) (hregs : ShiftMidRegs st s)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x60#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 → sf.readReg64 (.gpr 22#5) = 0x50#64 →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.invShiftRows2 st) ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64)
      { st with s0 := (Model.invShiftRows2 st).s0, s1 := (Model.invShiftRows2 st).s1 } ∗ F) post oom := by
  rcases hregs with ⟨hx10, hx12, hx13, hx14, hx15, hx16⟩
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have_instrs hc 0 24; dsimp only [fsStateAt, Model.invShiftRows2, Model.shiftRows2, Model.FsState.map]
  wp_steps 12; wp_stp64 hf_12 m1 hm1; wp_steps 7; wp_stp64 hf_20 m2 hm2; wp_steps 2; wp_stp64 hf_23 m3 hm3
  wp_conv_pre => simp only [hx10, hx12, hx13, hx14, hx15, hx16, deltaSwap1_shiftRows2_eq]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm]) (hperm := by simp [wp_norm, arm64_norm, hm3, hm2, hm1])) hx21 hx22

private theorem dec_mov_sp_step {P : Program} {pc0 target_pc outPtr keysPtr : BitVec 64}
    {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords [0x910003e0#32])) (hpc : s.pc = pc0) (hrun : s.status = .Running) (ha : DecAnchor s0 outPtr keysPtr s)
    (hnext : ∀ sf : State, sf.pc = pc0 + 4#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 0#5) = s0.sp - 112#64 → sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hsp := ha.sp; have_instrs hc 0 1; wp_steps 1
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm])) (by simp [wp_norm, arm64_norm]) rfl rfl

private theorem dec_loop_ark1_step {P : Program} {pc0 target_pc outPtr keysPtr rkPtr : BitVec 64}
    {st rk : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decLoopArk1Words)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hx21 : s.readReg64 (.gpr 21#5) = rkPtr + 0x38#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x54#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 0#5) = s0.sp - 112#64 → sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.addRoundKeyFs st rk) ∗ fsStateAt rkPtr rk ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ fsStateAt rkPtr rk ∗ F) post oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have_instrs hc 0 21; dsimp only [fsStateAt, Model.addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 8; wp_stp64 hf_8 m1 hm1; wp_steps 5; wp_stp64 hf_14 m2 hm2; wp_steps 1; wp_stp64 hf_16 m3 hm3; wp_steps 3; wp_stp64 hf_20 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm]) (hperm := by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) rfl rfl

private theorem dec_loop_ark3_step {P : Program} {pc0 target_pc outPtr keysPtr rkPtr : BitVec 64}
    {st rk : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decLoopArk3Words)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hx21 : s.readReg64 (.gpr 21#5) = rkPtr + 0xb8#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x54#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 0#5) = s0.sp - 112#64 → sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.addRoundKeyFs st rk) ∗ fsStateAt rkPtr rk ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ fsStateAt rkPtr rk ∗ F) post oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have_instrs hc 0 21; dsimp only [fsStateAt, Model.addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 8; wp_stp64 hf_8 m1 hm1; wp_steps 5; wp_stp64 hf_14 m2 hm2; wp_steps 1; wp_stp64 hf_16 m3 hm3; wp_steps 3; wp_stp64 hf_20 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm]) (hperm := by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) rfl rfl

private theorem dec_loop_ark2_step {P : Program} {pc0 target_pc outPtr keysPtr rkPtr : BitVec 64}
    {st rk : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decLoopArk2Words)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hx21 : s.readReg64 (.gpr 21#5) = rkPtr + 0xf8#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x54#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 0#5) = s0.sp - 112#64 → sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.addRoundKeyFs st rk) ∗ fsStateAt rkPtr rk ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ fsStateAt rkPtr rk ∗ F) post oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have_instrs hc 0 21; dsimp only [fsStateAt, Model.addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 8; wp_stp64 hf_8 m1 hm1; wp_steps 5; wp_stp64 hf_14 m2 hm2; wp_steps 1; wp_stp64 hf_16 m3 hm3; wp_steps 3; wp_stp64 hf_20 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm]) (hperm := by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) rfl rfl

private def Imc0MidRegs (st rk : Model.FsState) (s : State) : Prop :=
  let a0 := st.s0 ^^^ rk.s0; let a1 := st.s1 ^^^ rk.s1; let a2 := st.s2 ^^^ rk.s2
  let a3 := st.s3 ^^^ rk.s3; let a4 := st.s4 ^^^ rk.s4; let a5 := st.s5 ^^^ rk.s5
  let a6 := st.s6 ^^^ rk.s6; let a7 := st.s7 ^^^ rk.s7
  let c0 := a0 ^^^ a0.rotateRight 16; let c1 := a1 ^^^ a1.rotateRight 16
  let c2 := a2 ^^^ a2.rotateRight 16; let c3 := a3 ^^^ a3.rotateRight 16
  let c4 := a4 ^^^ a4.rotateRight 16; let c5 := a5 ^^^ a5.rotateRight 16
  let c6 := a6 ^^^ a6.rotateRight 16; let c7 := a7 ^^^ a7.rotateRight 16
  let d6 := a6 ^^^ c5; let d7 := a7 ^^^ c6
  s.readReg64 (.gpr 0#5) = c3 ∧ s.readReg64 (.gpr 1#5) = c4 ∧ s.readReg64 (.gpr 2#5) = c7 ∧
  s.readReg64 (.gpr 3#5) = c5 ∧ s.readReg64 (.gpr 4#5) = c6 ∧ s.readReg64 (.gpr 5#5) = d7 ^^^ d6 ∧
  s.readReg64 (.gpr 8#5) = c7 ^^^ a0 ∧ s.readReg64 (.gpr 9#5) = (a1 ^^^ c0) ^^^ c7 ∧
  s.readReg64 (.gpr 10#5) = a2 ^^^ c1 ∧ s.readReg64 (.gpr 11#5) = a3 ^^^ c2 ∧
  s.readReg64 (.gpr 12#5) = a4 ^^^ c3 ∧ s.readReg64 (.gpr 13#5) = a5 ∧
  s.readReg64 (.gpr 14#5) = d6 ∧ s.readReg64 (.gpr 15#5) = d7 ∧
  s.readReg64 (.gpr 16#5) = d6 ^^^ c0 ∧ s.readReg64 (.gpr 17#5) = c1 ∧ s.readReg64 (.gpr 18#5) = c2

private theorem dec_imc0_head_step {P : Program} {pc0 target_pc outPtr keysPtr rkPtr : BitVec 64}
    {st rk : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decImc0HeadWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64)
    (hx21 : s.readReg64 (.gpr 21#5) = rkPtr + 0x78#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x88#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      Imc0MidRegs st rk sf →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) st ∗ fsStateAt rkPtr rk ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ fsStateAt rkPtr rk ∗ F) post oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have_instrs hc 0 34; dsimp only [fsStateAt]; wp_steps 34
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm])) rfl rfl (by simp [Imc0MidRegs, wp_norm, arm64_norm])

private theorem dec_imc0_tail_step {P : Program} {pc0 target_pc outPtr keysPtr : BitVec 64}
    {st rk : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decImc0TailWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64)
    (hregs : Imc0MidRegs st rk s)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x8c#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 0#5) = s0.sp - 112#64 → sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf
        (fsStateAt (s0.sp - 112#64) (Model.invMixColumns0 (Model.addRoundKeyFs st rk)) ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ F) post oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18⟩
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have_instrs hc 0 35; dsimp only [fsStateAt]
  wp_steps 19; wp_stp64 hf_19 m1 hm1; wp_steps 5; wp_stp64 hf_25 m2 hm2
  wp_steps 5; wp_stp64 hf_31 m3 hm3; wp_steps 2; wp_stp64 hf_34 m4 hm4
  wp_conv_pre => change fsStateAt (s0.sp - 112#64) (decImc0Asm st rk) ∗ F; rw [decImc0Asm_eq]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm])
      (hperm := by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1])) (by simp [wp_norm, arm64_norm]) rfl rfl

private theorem dec_exit_br_cont {P : Program} {fnAddr target_pc outPtr keysPtr : BitVec 64}
    {c : Nat} {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x1a0#64) (decodeWords [0xb10042df#32, 0x54001060#32]))
    (hpc : s.pc = fnAddr + 0x1a0#64) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hc_lt : c < 3)
    (hx22 : s.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * c))
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x1a8#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 2; wp_steps 2; wp_if h_eq
  · exfalso; rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> simp at h_eq
  · exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (ha.step (hproj := by simp [wp_norm, arm64_norm])) rfl rfl

private theorem dec_exit_br_exit {P : Program} {pc0 target_pc outPtr keysPtr : BitVec 64}
    {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords [0xb10042df#32, 0x54001060#32]))
    (hpc : s.pc = pc0) (hrun : s.status = .Running) (ha : DecAnchor s0 outPtr keysPtr s)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64 - 16#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x210#64 → sf.status = .Running →
      DecAnchor s0 outPtr keysPtr sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  generalize hv : (0#64 - 16#64) = v at hx22; have_instrs hc 0 2; wp_steps 2; wp_if h_eq
  · generalize hpc1 : pc0 + 0x210#64 = pc1
    exact hnext _ hpc1.symm (by simp [wp_norm, arm64_norm, hrun])
      (ha.step (hproj := by simp [wp_norm, arm64_norm]))
  · subst hv; simp at h_eq

private theorem dec_guard_step {P : Program} {fnAddr target_pc outPtr keysPtr : BitVec 64}
    {c : Nat} {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x320#64) (decodeWords decLoopGuardWords))
    (hpc : s.pc = fnAddr + 0x320#64) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hc_lt : c < 3)
    (hx22 : s.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * c))
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x334#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 5; wp_steps 2; wp_if h_eq8
  · exfalso; rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> simp at h_eq8
  · wp_steps 3; wp_if h_lo8
    · exfalso; rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> simp at h_lo8
    · exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (ha.step (hproj := by simp [wp_norm, arm64_norm])) rfl rfl

private theorem dec_latch_step {P : Program} {fnAddr target_pc outPtr keysPtr : BitVec 64}
    {c : Nat} {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x394#64) (decodeWords decLoopLatchWords))
    (hpc : s.pc = fnAddr + 0x394#64) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hc_lt : c < 3)
    (hx21 : s.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 - BitVec.ofNat 64 (256 * c))
    (hx22 : s.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * c))
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x140#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 - BitVec.ofNat 64 (256 * (c + 1)) →
      sf.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * (c + 1)) →
      SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 4; wp_steps 4; wp_if h_ne
  · refine hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (ha.step (hproj := by simp [wp_norm, arm64_norm])) ?_ ?_
    · simp only [wp_norm, arm64_norm]; try rw [hx21]
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> bv_lin
    · simp only [wp_norm, arm64_norm]; try rw [hx22]
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide
  · exfalso; rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> simp at h_ne

private theorem dec_ark0_step {P : Program} {pc0 target_pc outPtr keysPtr : BitVec 64}
    {st rk0 : Model.FsState} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decArk0Words)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x58#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 0#5) = outPtr → sf.readReg64 (.gpr 1#5) = s0.sp - 112#64 →
      SepWP P target_pc sf (fsStateAt (s0.sp - 112#64) (Model.addRoundKeyFs st rk0) ∗ fsStateAt keysPtr rk0 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt (s0.sp - 112#64) st ∗ fsStateAt keysPtr rk0 ∗ F) post oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have hx19 := ha.x19; have hx20 := ha.x20; have_instrs hc 0 22
  dsimp only [fsStateAt, Model.addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 9; wp_stp64 hf_9 m1 hm1; wp_steps 5; wp_stp64 hf_15 m2 hm2
  wp_steps 1; wp_stp64 hf_17 m3 hm3; wp_steps 3; wp_stp64 hf_21 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hproj := by simp [wp_norm, arm64_norm])
      (hperm := by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])

private theorem dec_ret_step {P : Program} {pc0 outPtr keysPtr inPtr : BitVec 64}
    {ro : Bool} {ks : Model.FsKeys256} {bs : Blocks4} {stFinal : Model.FsState}
    {R : SepProp} {s0 s : State} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords decRetWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) :
    SepWP P (s0.readReg64 .lr) s
      (decSavedAt s0.sp s0 ∗ fsStateAt (s0.sp - 112#64) stFinal ∗ stackFrameAt (s0.sp - 112#64) 96 ∗
       (fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗
        (outPtr ↦ₛ blocks4Bytes (Model.aes256DecryptFs ks bs))))
      (fun sf Q =>
        (sf.mem ⊨ Q ∗ R → sf.mem ⊨ aes256DecryptSpec.post (ro, outPtr, keysPtr, inPtr, ks, bs) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  have hsp := ha.sp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [ha.sp]; exact hsp_loc
  have_instrs hc 0 5; dsimp only [decSavedAt]; wp_steps 5
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
  · dsimp only [aes256DecryptSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨ha.pres.1.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl),
      Satisfies.mono (sepConj_mono_left ?_) hm⟩
    refine Entails.trans (Entails.of_eq_explicit (show _ =
        (decSavedAt s0.sp s0 ∗ fsStateAt (s0.sp - 112#64) stFinal ∗ stackFrameAt (s0.sp - 112#64) 96) ∗
        (fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗
          (outPtr ↦ₛ blocks4Bytes (Model.aes256DecryptFs ks bs))) by dsimp only [decSavedAt]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (stackFrameAt_208_repack s0.sp s0 stFinal))
        (Entails.of_eq_explicit (by sep_ac_rfl)))
  · refine DecPreserved.to_calleeSaved (ha.pres.trans ⟨PureStepPreserved.of_proj_perm ?_ rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) ?_ ?_ ?_ ?_ ?_ <;> simp [wp_norm, arm64_norm]

end

/-! ## 7. Loop Iteration & Top-Level `subroutine_ok` Proofs -/

private abbrev decLoopInvSpatial (sp0 outPtr keysPtr inPtr : BitVec 64)
    (ro : Bool) (ks : Model.FsKeys256) (bs : Blocks4) (s0 : State) (st : Model.FsState) : SepProp :=
  fsStateAt (sp0 - 112#64) st ∗ stackFrameAt (sp0 - 112#64) 96 ∗ fsKeys256At keysPtr ks ∗
  bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion outPtr 64 ∗ decSavedAt sp0 s0

private theorem decLoopInvSpatial_focus (sp0 outPtr keysPtr inPtr : BitVec 64)
    (ro : Bool) (ks : Model.FsKeys256) (bs : Blocks4) (s0 : State) (st : Model.FsState) (r : Nat) (hr : r ≤ 14) :
    ∃ F_ks,
      decLoopInvSpatial sp0 outPtr keysPtr inPtr ro ks bs s0 st =
        fsStateAt (sp0 - 112#64) st ∗ fsStateAt (keysPtr + BitVec.ofNat 64 (64 * r)) (ks.getRound r) ∗
          (stackFrameAt (sp0 - 112#64) 96 ∗ F_ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion outPtr 64 ∗ decSavedAt sp0 s0) ∧
      ∀ st',
        fsStateAt (sp0 - 112#64) st' ∗ fsStateAt (keysPtr + BitVec.ofNat 64 (64 * r)) (ks.getRound r) ∗
          (stackFrameAt (sp0 - 112#64) 96 ∗ F_ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion outPtr 64 ∗ decSavedAt sp0 s0) =
        decLoopInvSpatial sp0 outPtr keysPtr inPtr ro ks bs s0 st' := by
  obtain ⟨F_ks, hf⟩ := fsKeys256At_focus keysPtr ks r hr
  refine ⟨F_ks, ?_, fun st' => ?_⟩ <;> (dsimp only [decLoopInvSpatial]; rw [hf]; sep_ac_rfl)

private theorem dec_loop_common_step {P : Program}
    {fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr target_pc outPtr keysPtr inPtr : BitVec 64}
    {ro : Bool} {ks : Model.FsKeys256} {bs : Blocks4} {st0 : Model.FsState}
    {c : Nat} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : DecCodeSegs P fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr)
    (hcal : Aes256DecryptCallees P bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr)
    (hpc : s.pc = fnAddr + 0x140#64) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hc_le : c ≤ 3)
    (hx21 : s.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 - BitVec.ofNat 64 (256 * c))
    (hx22 : s.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * c))
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x1a0#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 - BitVec.ofNat 64 (256 * c) →
      sf.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * c) →
      SepWP P target_pc sf (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 (decAfterRounds ks st0 (4 * c + 1))) post oom) :
    SepWP P target_pc s (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 (decAfterRounds ks st0 (4 * c))) post oom := by
  obtain ⟨F_ks, h_in, h_out⟩ := decLoopInvSpatial_focus s0.sp outPtr keysPtr inPtr ro ks bs s0 _ (13 - 4 * c) (by omega)
  have hx21_r : s.readReg64 (.gpr 21#5) = (keysPtr + BitVec.ofNat 64 (64 * (13 - 4 * c))) + 0x38#64 := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> (rw [hx21]; bv_lin)
  have hrd : Model.invSubBytesFs (Model.invMixColumns1
      (Model.addRoundKeyFs (decAfterRounds ks st0 (4 * c)) (ks.getRound (13 - 4 * c)))) =
      decAfterRounds ks st0 (4 * c + 1) := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> rfl
  rw [h_in]; refine dec_loop_ark1_step hseg.ark1 hpc hrun ha hsp_loc hx21_r fun s1 hpc1 hrun1 ha1 hx0_1 hx21_1 hx22_1 => ?_
  rw [h_out]; refine call_inv_mix_columns Model.invMixColumns1 hseg.bl_imc1 hcal.invMixColumns1_ok
    (by simpa [bv_lin_norm] using hpc1) hrun1 ha1 hsp_loc hx0_1 (hnext := fun s2 hpc2 hrun2 ha2 hx21_2 hx22_2 => ?_)
  refine dec_mov_sp_step hseg.mov1 (by simpa [bv_lin_norm] using hpc2) hrun2 ha2 fun s3 hpc3 hrun3 ha3 hx0_3 hx21_3 hx22_3 => ?_
  refine call_inv_sub_bytes hseg.bl_isb1 hcal.invSubBytes_ok
    (by simpa [bv_lin_norm] using hpc3) hrun3 ha3 hsp_loc hx0_3 fun s4 hpc4 hrun4 ha4 hx21_4 hx22_4 => ?_
  rw [hrd]; exact hnext s4 (by simpa [bv_lin_norm] using hpc4) hrun4 ha4
    (hx21_4.trans (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21))))
    (hx22_4.trans (hx22_3.trans (hx22_2.trans (hx22_1.trans hx22))))

private theorem dec_loop_full_iter {P : Program}
    {fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr target_pc outPtr keysPtr inPtr : BitVec 64}
    {ro : Bool} {ks : Model.FsKeys256} {bs : Blocks4} {st0 : Model.FsState}
    {c : Nat} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : DecCodeSegs P fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr)
    (hcal : Aes256DecryptCallees P bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr)
    (hpc : s.pc = fnAddr + 0x140#64) (hrun : s.status = .Running)
    (ha : DecAnchor s0 outPtr keysPtr s) (hsp_loc : (s0.sp - 112#64) &&& 15#64 = 0#64) (hc_lt : c < 3)
    (hx21 : s.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 - BitVec.ofNat 64 (256 * c))
    (hx22 : s.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * c))
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x140#64 → sf.status = .Running → DecAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = keysPtr + 0x378#64 - BitVec.ofNat 64 (256 * (c + 1)) →
      sf.readReg64 (.gpr 22#5) = 0x50#64 - BitVec.ofNat 64 (32 * (c + 1)) →
      SepWP P target_pc sf (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 (decAfterRounds ks st0 (4 * (c + 1)))) post oom) :
    SepWP P target_pc s (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 (decAfterRounds ks st0 (4 * c))) post oom := by
  refine dec_loop_common_step hseg hcal hpc hrun ha hsp_loc (by omega) hx21 hx22 fun s1 hpc1 hrun1 ha1 hx21_1 hx22_1 => ?_
  refine dec_exit_br_cont hseg.exit_br hpc1 hrun1 ha1 hc_lt hx22_1 fun s2 hpc2 hrun2 ha2 hx21_2 hx22_2 => ?_
  have hx21_s2 := hx21_2.trans hx21_1; have hx22_s2 := hx22_2.trans hx22_1
  obtain ⟨F0, h0_in, h0_out⟩ := decLoopInvSpatial_focus s0.sp outPtr keysPtr inPtr ro ks bs s0 _ (12 - 4 * c) (by omega)
  have hx21_r0 : s2.readReg64 (.gpr 21#5) = (keysPtr + BitVec.ofNat 64 (64 * (12 - 4 * c))) + 0x78#64 := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> (rw [hx21_s2]; bv_lin)
  have hrd0 : Model.invSubBytesFs (Model.invMixColumns0
      (Model.addRoundKeyFs (decAfterRounds ks st0 (4 * c + 1)) (ks.getRound (12 - 4 * c)))) =
      decAfterRounds ks st0 (4 * c + 2) := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl
  change SepWP P target_pc s2 (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 _) post oom
  rw [h0_in]; refine dec_imc0_head_step hseg.imc0H hpc2 hrun2 ha2 hsp_loc hx21_r0 fun s3 hpc3 hrun3 ha3 hx21_3 hx22_3 hmid => ?_
  rw [h0_out]; refine dec_imc0_tail_step hseg.imc0T (by simpa [bv_lin_norm] using hpc3) hrun3 ha3 hsp_loc hmid
    fun s4 hpc4 hrun4 ha4 hx0_4 hx21_4 hx22_4 => ?_
  refine call_inv_sub_bytes hseg.bl_isb0 hcal.invSubBytes_ok (by simpa [bv_lin_norm] using hpc4) hrun4 ha4 hsp_loc hx0_4
    fun s5 hpc5 hrun5 ha5 hx21_5 hx22_5 => ?_
  rw [hrd0]
  have hx21_s5 := hx21_5.trans (hx21_4.trans (hx21_3.trans hx21_s2))
  have hx22_s5 := hx22_5.trans (hx22_4.trans (hx22_3.trans hx22_s2))
  obtain ⟨F3, h3_in, h3_out⟩ := decLoopInvSpatial_focus s0.sp outPtr keysPtr inPtr ro ks bs s0 _ (11 - 4 * c) (by omega)
  have hx21_r3 : s5.readReg64 (.gpr 21#5) = (keysPtr + BitVec.ofNat 64 (64 * (11 - 4 * c))) + 0xb8#64 := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> (rw [hx21_s5]; bv_lin)
  have hrd3 : Model.invSubBytesFs (Model.invMixColumns3
      (Model.addRoundKeyFs (decAfterRounds ks st0 (4 * c + 2)) (ks.getRound (11 - 4 * c)))) =
      decAfterRounds ks st0 (4 * c + 3) := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl
  change SepWP P target_pc s5 (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 _) post oom
  rw [h3_in]; refine dec_loop_ark3_step hseg.ark3 (by simpa [bv_lin_norm] using hpc5) hrun5 ha5 hsp_loc hx21_r3
    fun s6 hpc6 hrun6 ha6 hx0_6 hx21_6 hx22_6 => ?_
  rw [h3_out]; refine call_inv_mix_columns Model.invMixColumns3 hseg.bl_imc3 hcal.invMixColumns3_ok
    (by simpa [bv_lin_norm] using hpc6) hrun6 ha6 hsp_loc hx0_6 (hnext := fun s7 hpc7 hrun7 ha7 hx21_7 hx22_7 => ?_)
  refine dec_mov_sp_step hseg.mov3 (by simpa [bv_lin_norm] using hpc7) hrun7 ha7 fun s8 hpc8 hrun8 ha8 hx0_8 hx21_8 hx22_8 => ?_
  refine call_inv_sub_bytes hseg.bl_isb3 hcal.invSubBytes_ok (by simpa [bv_lin_norm] using hpc8) hrun8 ha8 hsp_loc hx0_8
    fun s9 hpc9 hrun9 ha9 hx21_9 hx22_9 => ?_
  rw [hrd3]
  have hx21_s9 := hx21_9.trans (hx21_8.trans (hx21_7.trans (hx21_6.trans hx21_s5)))
  have hx22_s9 := hx22_9.trans (hx22_8.trans (hx22_7.trans (hx22_6.trans hx22_s5)))
  refine dec_guard_step hseg.guard_br (by simpa [bv_lin_norm] using hpc9) hrun9 ha9 hc_lt hx22_s9
    fun s10 hpc10 hrun10 ha10 hx21_10 hx22_10 => ?_
  have hx21_s10 := hx21_10.trans hx21_s9; have hx22_s10 := hx22_10.trans hx22_s9
  obtain ⟨F2, h2_in, h2_out⟩ := decLoopInvSpatial_focus s0.sp outPtr keysPtr inPtr ro ks bs s0 _ (10 - 4 * c) (by omega)
  have hx21_r2 : s10.readReg64 (.gpr 21#5) = (keysPtr + BitVec.ofNat 64 (64 * (10 - 4 * c))) + 0xf8#64 := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> (rw [hx21_s10]; bv_lin)
  have hrd2 : Model.invSubBytesFs (Model.invMixColumns2
      (Model.addRoundKeyFs (decAfterRounds ks st0 (4 * c + 3)) (ks.getRound (10 - 4 * c)))) =
      decAfterRounds ks st0 (4 * (c + 1)) := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl
  change SepWP P target_pc s10 (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 _) post oom
  rw [h2_in]; refine dec_loop_ark2_step hseg.ark2 hpc10 hrun10 ha10 hsp_loc hx21_r2
    fun s11 hpc11 hrun11 ha11 hx0_11 hx21_11 hx22_11 => ?_
  rw [h2_out]; refine call_inv_mix_columns Model.invMixColumns2 hseg.bl_imc2 hcal.invMixColumns2_ok
    (by simpa [bv_lin_norm] using hpc11) hrun11 ha11 hsp_loc hx0_11 (hnext := fun s12 hpc12 hrun12 ha12 hx21_12 hx22_12 => ?_)
  refine dec_mov_sp_step hseg.mov2 (by simpa [bv_lin_norm] using hpc12) hrun12 ha12
    fun s13 hpc13 hrun13 ha13 hx0_13 hx21_13 hx22_13 => ?_
  refine call_inv_sub_bytes hseg.bl_isb2 hcal.invSubBytes_ok (by simpa [bv_lin_norm] using hpc13) hrun13 ha13 hsp_loc hx0_13
    fun s14 hpc14 hrun14 ha14 hx21_14 hx22_14 => ?_
  rw [hrd2]
  exact dec_latch_step hseg.latch (by simpa [bv_lin_norm] using hpc14) hrun14 ha14 hc_lt
    (hx21_14.trans (hx21_13.trans (hx21_12.trans (hx21_11.trans hx21_s10))))
    (hx22_14.trans (hx22_13.trans (hx22_12.trans (hx22_11.trans hx22_s10)))) hnext

/-- Total-correctness `subroutine_ok` theorem for `aes256_decrypt` on its 264-instruction prefix. -/
theorem aes256Decrypt_ok {P : Program}
    {fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr panic0Sym : BitVec 64}
    {panic0Relax : Bool} {panic0Target : BitVec 64}
    (hc : hasInstrs P fnAddr
      (aes256DecryptPrefixInstrs fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr
        invMixColumns2Addr invMixColumns3Addr invBitsliceAddr panic0Sym panic0Relax panic0Target))
    (hcal : Aes256DecryptCallees P bitsliceAddr invSubBytesAddr invMixColumns1Addr
      invMixColumns2Addr invMixColumns3Addr invBitsliceAddr) :
    subroutine_ok P fnAddr aes256DecryptSpec := by
  have hseg := DecCodeSegs.of_hasInstrs hc; apply subroutine_ok_of_sepWP_init
  rintro ⟨ro, outPtr, keysPtr, inPtr, ks, bs⟩ R s0 hpc hrun hpre hsp
  have hsp_loc := sp_sub112_and_15 hsp; dsimp only [aes256DecryptSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx1, hx8, hwf⟩, hpre⟩
  refine ⟨_, hpre, SepWP.weaken_pre (Entails.trans (Entails.of_eq_explicit (show _ =
      stackFrameAt s0.sp 208 ∗ (fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion outPtr 64)
      by sep_ac_rfl)) (sepConj_mono_left (stackFrameAt_208_unpack s0.sp))) ?_⟩
  wp_conv_pre => simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  refine SepWP.weaken_pre ?_ (dec_prologue_step (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (F := memRegion (s0.sp - 112#64) 64 ∗ stackFrameAt (s0.sp - 112#64) 96 ∗
      fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion outPtr 64)
    hseg.prologue hpc hrun hsp hx0 hx1 hx8 fun s1 hpc1 hrun1 ha1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 => ?_)
  · exact Entails.of_eq_explicit (by sep_ac_rfl)
  refine SepWP.weaken_pre ?_ (call_bitslice (ro := ro)
    (F := stackFrameAt (s0.sp - 112#64) 96 ∗ fsKeys256At keysPtr ks ∗ memRegion outPtr 64 ∗ decSavedAt s0.sp s0)
    hseg.bl_bs hcal.bitslice_ok hpc1 hrun1 ha1 hsp_loc hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hwf fun s2 hpc2 hrun2 ha2 => ?_)
  · exact Entails.of_eq_explicit (by sep_ac_rfl)
  obtain ⟨F14, h14_in, h14_out⟩ := decLoopInvSpatial_focus s0.sp outPtr keysPtr inPtr ro ks bs s0 (Model.bitslice bs) 14 (by omega)
  simp only [show BitVec.ofNat 64 (64 * 14) = 0x380#64 from rfl, show ks.getRound 14 = ks.rk14 from rfl] at h14_in h14_out
  refine SepWP.weaken_pre ?_ (dec_ark14_step (st := Model.bitslice bs) (rk14 := ks.rk14)
    (F := stackFrameAt (s0.sp - 112#64) 96 ∗ F14 ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion outPtr 64 ∗ decSavedAt s0.sp s0)
    hseg.ark14 (by simpa [bv_lin_norm] using hpc2) hrun2 ha2 hsp_loc fun s3 hpc3 hrun3 ha3 hx0_3 => ?_)
  · exact Entails.of_eq_explicit (by rw [← h14_in]; dsimp only [decLoopInvSpatial]; sep_ac_rfl)
  rw [h14_out]
  refine call_inv_sub_bytes hseg.bl_isb14 hcal.invSubBytes_ok (by simpa [bv_lin_norm] using hpc3) hrun3 ha3 hsp_loc hx0_3
    fun s4 hpc4 hrun4 ha4 _ _ => ?_
  refine dec_shiftA_step hseg.shiftA (by simpa [bv_lin_norm] using hpc4) hrun4 ha4 hsp_loc fun s5 hpc5 hrun5 ha5 hx21_5 hx22_5 hmid5 => ?_
  refine dec_shiftB_step hseg.shiftB (by simpa [bv_lin_norm] using hpc5) hrun5 ha5 hsp_loc hx21_5 hx22_5 hmid5
    fun s6 hpc6 hrun6 ha6 hx21_6 hx22_6 => ?_
  let st0 := Model.invShiftRows2 (Model.invSubBytesFs (Model.addRoundKeyFs (Model.bitslice bs) ks.rk14))
  change SepWP P (s0.readReg64 .lr) s6 (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 (decAfterRounds ks st0 (4 * 0))) _ _
  refine dec_loop_full_iter hseg hcal (by simpa [bv_lin_norm] using hpc6) hrun6 ha6 hsp_loc (c := 0) (by decide)
    (by simpa using hx21_6) (by simpa using hx22_6) fun s7 hpc7 hrun7 ha7 hx21_7 hx22_7 => ?_
  refine dec_loop_full_iter hseg hcal hpc7 hrun7 ha7 hsp_loc (c := 1) (by decide) hx21_7 hx22_7
    fun s8 hpc8 hrun8 ha8 hx21_8 hx22_8 => ?_
  refine dec_loop_full_iter hseg hcal hpc8 hrun8 ha8 hsp_loc (c := 2) (by decide) hx21_8 hx22_8
    fun s9 hpc9 hrun9 ha9 hx21_9 hx22_9 => ?_
  refine dec_loop_common_step hseg hcal hpc9 hrun9 ha9 hsp_loc (c := 3) (by decide) hx21_9 hx22_9
    fun s10 hpc10 hrun10 ha10 _ hx22_10 => ?_
  refine dec_exit_br_exit hseg.exit_br hpc10 hrun10 ha10 (by rw [hx22_10]; decide) fun s11 hpc11 hrun11 ha11 => ?_
  obtain ⟨F0, h0_in, h0_out⟩ := decLoopInvSpatial_focus s0.sp outPtr keysPtr inPtr ro ks bs s0 (decAfterRounds ks st0 13) 0 (by omega)
  dsimp only [Model.FsKeys256.getRound] at h0_in h0_out
  simp only [Nat.mul_zero, BitVec.add_zero] at h0_in h0_out
  change SepWP P (s0.readReg64 .lr) s11 (decLoopInvSpatial s0.sp outPtr keysPtr inPtr ro ks bs s0 (decAfterRounds ks st0 13)) _ _
  rw [h0_in]
  refine dec_ark0_step hseg.ark0 (by simpa [bv_lin_norm] using hpc11) hrun11 ha11 hsp_loc fun s12 hpc12 hrun12 ha12 hx0_12 hx1_12 => ?_
  rw [h0_out]
  refine SepWP.weaken_pre ?_ (call_inv_bitslice (st := Model.addRoundKeyFs (decAfterRounds ks st0 13) ks.rk0)
    (F := stackFrameAt (s0.sp - 112#64) 96 ∗ fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ decSavedAt s0.sp s0)
    hseg.bl_ibs hcal.invBitslice_ok (by simpa [bv_lin_norm] using hpc12) hrun12 ha12 hsp_loc hx0_12 hx1_12 fun s13 hpc13 hrun13 ha13 => ?_)
  · exact Entails.of_eq_explicit (by dsimp only [decLoopInvSpatial]; sep_ac_rfl)
  have haes : Model.invBitslice (Model.addRoundKeyFs (decAfterRounds ks st0 13) ks.rk0) = Model.aes256DecryptFs ks bs := by
    dsimp only [Model.aes256DecryptFs, st0]; rw [decAfterRounds_13_eq]
  rw [haes]
  refine SepWP.weaken_pre ?_ (dec_ret_step (stFinal := Model.addRoundKeyFs (decAfterRounds ks st0 13) ks.rk0)
    hseg.ret_seg (by simpa [bv_lin_norm] using hpc13) hrun13 ha13 hsp_loc)
  exact Entails.of_eq_explicit (by sep_ac_rfl)

/-- Total-correctness `subroutine_ok` theorem for the full 270-instruction `aes256DecryptFullInstrs`. -/
theorem aes256Decrypt_full_ok {P : Program}
    {fnAddr bitsliceAddr invSubBytesAddr invMixColumns1Addr invMixColumns2Addr
     invMixColumns3Addr invBitsliceAddr : BitVec 64} {panics : Aes256DecryptPanicSyms}
    (hc : hasInstrs P fnAddr (aes256DecryptFullInstrs fnAddr bitsliceAddr invSubBytesAddr
      invMixColumns1Addr invMixColumns2Addr invMixColumns3Addr invBitsliceAddr panics))
    (hcal : Aes256DecryptCallees P bitsliceAddr invSubBytesAddr invMixColumns1Addr
      invMixColumns2Addr invMixColumns3Addr invBitsliceAddr) :
    subroutine_ok P fnAddr aes256DecryptSpec :=
  aes256Decrypt_ok (hasInstrs_prefix hc) hcal

end
end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec

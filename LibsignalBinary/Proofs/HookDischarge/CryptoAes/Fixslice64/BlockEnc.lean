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
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Equiv
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
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
# Binary Contract for `fixslice64::aes256_encrypt` (`Fixslice64.BlockEnc`)

Placement-generic (`hasInstrs`) ARM64 `subroutine_ok` verification for the 308-instruction 4-block
fixsliced AES-256 encryption routine `aes::soft::fixslice64::aes256_encrypt` (`aes256Encrypt_ok`,
`aes256EncryptSpec`, `Aes256EncryptCallees`, and `Fixslice64.Equiv` byte-level bridge lemmas).
-/

public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (Blocks4 FsKeys256 ror64 rorDistance rotateRows1 rotateRows2 rotateRowsAndColumns12 deltaSwap1
   shiftRows2 mixColumnsGen mixColumns0 mixColumns1 mixColumns2 mixColumns3 addRoundKeyFs encRoundFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj fsStateAt fsStateAt_entails_memRegion
   memRegion64_eq_exists_fsStateAt blocks4Bytes fsKeys256At step_stp64_perm)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Bitslice
  (bitsliceInstrs invBitsliceInstrs bitslice4Spec invBitsliceSpec bitslice4_ok invBitslice_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxCode
  (subBytesInstrs subBytesSpec subBytes_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.MixCode
  (mixColumns1Instrs mixColumns3Instrs mixColumns1Spec mixColumns3Spec mixColumns1_ok mixColumns3_ok)
open CryptoGames.CBC (Block blockToBytesLE bytesToBlock blockToBytesLE_bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip (length_aes256Cipher)

/-! ## 1. Machine-Code Template Words & Relocated Instruction Sequence -/

@[expose] def encSlice0 : List (BitVec 32) :=
  [0xd10203ff#32, 0xa9047bfd#32, 0xa9055ff8#32, 0xa90657f6#32, 0xa9074ff4#32, 0x910103fd#32, 0xaa0003f4#32,
   0x910003e0#32, 0x91004022#32, 0x91008023#32, 0x9100c024#32, 0xaa0803f3#32]
@[expose] def encSlice1 : List (BitVec 32) :=
  [0xa9402fe8#32, 0x910003e0#32, 0xa9402a89#32, 0xa9423a8d#32, 0xa94243ef#32, 0xca090108#32, 0xca0a016a#32,
   0xa9413289#32, 0xa9002be8#32, 0xa9412fe8#32, 0xca0d01ea#32, 0xca090108#32, 0xca0c0169#32, 0xca0e020b#32,
   0xa90127e8#32, 0xa94333e9#32, 0xa9022fea#32, 0xa9432a88#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def encMovX0SpWords : List (BitVec 32) := [0x910003e0#32]
@[expose] def encLoopInitWords : List (BitVec 32) := [0x91028295#32, 0x52800c16#32]
@[expose] def encLoopArk1Words : List (BitVec 32) :=
  [0xa9402fe8#32, 0xa97a2aa9#32, 0xa97c46b0#32, 0xa94203f2#32, 0xca09010c#32, 0xa97b26a8#32, 0xca0a016d#32,
   0xa9412fea#32, 0xa90037ec#32, 0xca08014e#32, 0xca09016f#32, 0xca100249#32, 0xca110008#32, 0xa97d42aa#32,
   0xa94347eb#32, 0xa9013fee#32, 0xa90223e9#32, 0xca0a016a#32, 0xca10022b#32, 0xa9032fea#32]
@[expose] def encLoopCbzMovWords : List (BitVec 32) := [0xb4001656#32, 0x910003e0#32]
@[expose] def encSlice3 : List (BitVec 32) := encLoopInitWords ++ (encLoopArk1Words ++ encLoopCbzMovWords)
@[expose] def encMc2HeadWords : List (BitVec 32) :=
  [0xa9403fee#32, 0xa94133eb#32, 0xa94227ea#32, 0x93ce61cd#32, 0x93ce21d1#32, 0x93cf61f2#32, 0x93cf21e0#32,
   0x93cb6161#32, 0x93cb2163#32, 0x92009dad#32, 0x92089e31#32, 0x92009e52#32, 0xa94343e8#32, 0xaa1101a2#32,
   0x92089c0d#32, 0x93cc6180#32, 0x93cc2184#32, 0xaa0d0245#32, 0x92009c2d#32, 0x92089c71#32, 0xaa1101b1#32,
   0x92009c0d#32, 0x92089c92#32, 0xaa1201b2#32, 0x93ca614d#32, 0x93ca2140#32, 0x93c96121#32, 0x93c92123#32,
   0x93c86104#32, 0x93c82106#32, 0x93d06217#32, 0x93d02218#32, 0x92009dad#32, 0x92089c00#32, 0x92009c21#32,
   0x92089c67#32, 0x92009c84#32, 0x92089cc6#32, 0xaa0001a3#32, 0xaa070020#32, 0xaa06008d#32, 0x92009ee1#32,
   0x92089f04#32, 0xca0e004e#32, 0xaa040021#32]
@[expose] def encMc2TailWords : List (BitVec 32) :=
  [0xa97e12a6#32, 0xca0f00af#32, 0xca100030#32, 0xca0b022b#32, 0xca100042#32, 0xca0c024c#32, 0xca0a006a#32,
   0xcace80c6#32, 0xca0501ce#32, 0xcacf8084#32, 0xca1001ce#32, 0xca1101ef#32, 0xca090009#32, 0xca0200c2#32,
   0xca0e008e#32, 0xca0801a8#32, 0xa9003be2#32, 0xa97f0aa5#32, 0xcacb80ae#32, 0xcacc8051#32, 0xca12016b#32,
   0xca10016b#32, 0xca03018c#32, 0xca0f01ce#32, 0xca0b022b#32, 0xca10018c#32, 0xa9012fee#32, 0xa9403aaf#32,
   0xcaca81eb#32, 0xa94146af#32, 0xcac981ce#32, 0xca0d0129#32, 0xca00014a#32, 0xca0c016b#32, 0x910003e0#32,
   0xcac881ec#32, 0xcad0822d#32, 0xca010108#32, 0xca0a01ca#32, 0xca090189#32, 0xca0801a8#32, 0xa9022beb#32,
   0xa90323e9#32]
@[expose] def encSlice4 : List (BitVec 32) := encMc2HeadWords ++ encMc2TailWords
@[expose] def encSlice6 : List (BitVec 32) :=
  [0xa9402fe8#32, 0x910003e0#32, 0xa9422aa9#32, 0xa9443aad#32, 0xa94243ef#32, 0xca090108#32, 0xca0a016a#32,
   0xa94332a9#32, 0xa9002be8#32, 0xa9412fe8#32, 0xca0d01ea#32, 0xca090108#32, 0xca0c0169#32, 0xca0e020b#32,
   0xa90127e8#32, 0xa94333e9#32, 0xa9022fea#32, 0xa9452aa8#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def encMc0HeadWords : List (BitVec 32) :=
  [0xa94037ec#32, 0xa94307ea#32, 0xa94616a4#32, 0x93cc4192#32, 0x93cd41a0#32, 0x93c14028#32, 0xa9413fee#32,
   0xca0c024c#32, 0xca0d000d#32, 0xcacc8084#32, 0xca00018c#32, 0xca010101#32, 0xcacd80a5#32, 0xca010252#32,
   0xca01018c#32, 0xca120092#32, 0x93ce41c2#32, 0x93cf41e3#32, 0xca0c00ac#32, 0xa94247f0#32, 0xa90033f2#32,
   0xa9474aa4#32, 0xca0e004e#32, 0xca0f006f#32, 0xca0201ad#32, 0x93d0420b#32, 0x93d14229#32, 0x93ca4140#32]
@[expose] def encMc0TailWords : List (BitVec 32) :=
  [0xcace808c#32, 0xcacf8252#32, 0xca0301ce#32, 0xca100170#32, 0xca110131#32, 0xca0b01eb#32, 0xca0d018c#32,
   0xca0101cd#32, 0xca0a000a#32, 0xca0d024d#32, 0xca090209#32, 0xca01016b#32, 0xa90137ec#32, 0xa94832ae#32,
   0xca080148#32, 0xcad081cd#32, 0xa9493eae#32, 0xcad1818c#32, 0xca0b01ab#32, 0xca00022d#32, 0x910003e0#32,
   0xca090189#32, 0xcaca81cc#32, 0xcac181ee#32, 0xa90227eb#32, 0xca0d0189#32, 0xca0801c8#32, 0xa90323e9#32]
@[expose] def encSlice7 : List (BitVec 32) := encMc0HeadWords ++ encMc0TailWords
@[expose] def encLoopBackWords : List (BitVec 32) := [0xd10082d6#32, 0x910402b5#32, 0x17ffff3b#32]
@[expose] def encExitSr2Words : List (BitVec 32) :=
  [0xca4c2190#32, 0xca4d21b1#32, 0xca4e21d2#32, 0xca4f21e0#32, 0x92101e10#32, 0x92101e31#32, 0x92101e52#32,
   0xaa102210#32, 0xaa112231#32, 0x92101c00#32, 0xaa122252#32, 0xaa002000#32, 0xca0c020c#32, 0xca492130#32,
   0xca0d022d#32, 0xca482111#32, 0xa90037ec#32, 0xca4a214d#32, 0x92101e10#32, 0xca0e024e#32, 0xca0f000f#32,
   0xaa10220c#32, 0x92101e30#32, 0xca4b2171#32, 0x92101dad#32, 0xa9013fee#32, 0xaa10220e#32, 0xca090189#32,
   0xaa0d21ac#32, 0x92101e2d#32, 0xaa0d21ad#32, 0xca0801c8#32, 0x910003e0#32, 0xa90223e9#32, 0xca0a0188#32,
   0xca0b01a9#32, 0xa90327e8#32]
@[expose] def encSlice9 : List (BitVec 32) := encLoopBackWords ++ encExitSr2Words
@[expose] def encSlice10 : List (BitVec 32) :=
  [0xa9402fe9#32, 0x910003e1#32, 0xf941c288#32, 0xf941c68a#32, 0xaa1303e0#32, 0xf941ca8c#32, 0xa94243ef#32,
   0xca080128#32, 0xca0a016a#32, 0xf941ce89#32, 0xa9002be8#32, 0xa9412fe8#32, 0xf941d28d#32, 0xf941d68e#32,
   0xca0c0108#32, 0xca090169#32, 0xca0d01ea#32, 0xca0e020b#32, 0xa90127e8#32, 0xf941da88#32, 0xa94333e9#32,
   0xa9022fea#32, 0xf941de8a#32, 0xca080128#32, 0xca0a0189#32, 0xa90327e8#32]
@[expose] def encSlice11 : List (BitVec 32) :=
  [0xa9474ff4#32, 0xa94657f6#32, 0xa9455ff8#32, 0xa9447bfd#32, 0x910203ff#32, 0xd65f03c0#32]

/-- Exact 308 unrelocated `.rlib` instruction words (`0x000..0x4cc`) of `fixslice64::aes256_encrypt`. -/
@[expose] def aes256EncryptTemplateWords : List (BitVec 32) :=
  encSlice0 ++ [0x94000000#32] ++ encSlice1 ++ [0x94000000#32] ++ encMovX0SpWords ++ [0x94000000#32] ++
  encSlice3 ++ [0x94000000#32] ++ encSlice4 ++ [0x94000000#32] ++ encMovX0SpWords ++ [0x94000000#32] ++
  encSlice6 ++ [0x94000000#32] ++ encSlice7 ++ [0x94000000#32] ++ encMovX0SpWords ++ [0x94000000#32] ++
  encSlice9 ++ [0x94000000#32] ++ encSlice10 ++ [0x94000000#32] ++ encSlice11

/-- Relocated 308-instruction sequence of `aes::soft::fixslice64::aes256_encrypt` at `fnAddr`. -/
@[expose] def aes256EncryptInstrs
    (fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr : BitVec 64) :
    List Instr :=
  decodeWords encSlice0 ++ [.bl (bitsliceAddr - (fnAddr + 0x030#64))] ++
  decodeWords encSlice1 ++ [.bl (subBytesAddr - (fnAddr + 0x088#64))] ++
  decodeWords encMovX0SpWords ++ [.bl (mixColumns1Addr - (fnAddr + 0x090#64))] ++
  decodeWords encSlice3 ++ [.bl (subBytesAddr - (fnAddr + 0x0f4#64))] ++
  decodeWords encSlice4 ++ [.bl (subBytesAddr - (fnAddr + 0x258#64))] ++
  decodeWords encMovX0SpWords ++ [.bl (mixColumns3Addr - (fnAddr + 0x260#64))] ++
  decodeWords encSlice6 ++ [.bl (subBytesAddr - (fnAddr + 0x2b8#64))] ++
  decodeWords encSlice7 ++ [.bl (subBytesAddr - (fnAddr + 0x39c#64))] ++
  decodeWords encMovX0SpWords ++ [.bl (mixColumns1Addr - (fnAddr + 0x3a4#64))] ++
  decodeWords encSlice9 ++ [.bl (subBytesAddr - (fnAddr + 0x448#64))] ++
  decodeWords encSlice10 ++ [.bl (invBitsliceAddr - (fnAddr + 0x4b4#64))] ++ decodeWords encSlice11
theorem aes256EncryptInstrs_length
    (fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr : BitVec 64) :
    (aes256EncryptInstrs fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr
      invBitsliceAddr).length = 308 := by
  unfold aes256EncryptInstrs
  simp only [decodeWords, List.length_append, List.length_map, List.length_cons, List.length_nil]; rfl
private def isNonBlWord (w : BitVec 32) : Bool :=
  match Arm64.decode w with | some (.bl _) => false | some _ => true | none => false
private def zeroBlDisp : Instr → Instr | .bl _ => .bl 0#64 | x => x
private theorem map_zeroBlDisp_decodeWords : ∀ {ws : List (BitVec 32)}, ws.all isNonBlWord = true →
    ws.map Arm64.decode = (decodeWords ws).map (fun i => some (zeroBlDisp i))
  | [], _ => rfl
  | w :: ws, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h; rcases h with ⟨hw, hws⟩
      unfold isNonBlWord at hw
      cases hd : Arm64.decode w with
      | none => simp [hd] at hw
      | some inst =>
        rw [hd] at hw
        have hnb : zeroBlDisp inst = inst := by cases inst <;> first | rfl | cases hw
        have hhead : Arm64.decode w = some (zeroBlDisp (decodeWord w)) := by
          simp only [decodeWord, hd, Option.getD_some, hnb]
        exact congrArg₂ List.cons hhead (map_zeroBlDisp_decodeWords hws)
private theorem decode_bl_zero : Arm64.decode 0x94000000#32 = some (.bl 0#64) := by decide

/-- Every word in `aes256EncryptTemplateWords` decodes cleanly and matches `aes256EncryptInstrs`
    with zeroed `BL` displacements at the 11 `R_AARCH64_CALL26` relocation sites. -/
theorem aes256EncryptInstrs_template_eq
    (fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr : BitVec 64) :
    aes256EncryptTemplateWords.map Arm64.decode =
      (aes256EncryptInstrs fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr
        invBitsliceAddr).map (fun i => some (match i with | .bl _ => .bl 0#64 | x => x)) := by
  change aes256EncryptTemplateWords.map Arm64.decode =
    (aes256EncryptInstrs fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr
      invBitsliceAddr).map (fun i => some (zeroBlDisp i))
  have hs0 := map_zeroBlDisp_decodeWords (ws := encSlice0) (by decide)
  have hs1 := map_zeroBlDisp_decodeWords (ws := encSlice1) (by decide)
  have hsm := map_zeroBlDisp_decodeWords (ws := encMovX0SpWords) (by decide)
  have hs3 := map_zeroBlDisp_decodeWords (ws := encSlice3) (by decide)
  have hs4 := map_zeroBlDisp_decodeWords (ws := encSlice4) (by decide)
  have hs6 := map_zeroBlDisp_decodeWords (ws := encSlice6) (by decide)
  have hs7 := map_zeroBlDisp_decodeWords (ws := encSlice7) (by decide)
  have hs9 := map_zeroBlDisp_decodeWords (ws := encSlice9) (by decide)
  have hs10 := map_zeroBlDisp_decodeWords (ws := encSlice10) (by decide)
  have hs11 := map_zeroBlDisp_decodeWords (ws := encSlice11) (by decide)
  unfold aes256EncryptTemplateWords aes256EncryptInstrs
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, decode_bl_zero,
    hs0, hs1, hsm, hs3, hs4, hs6, hs7, hs9, hs10, hs11]; rfl

/-! ## 2. Callee Bundle & Public Hoare Specification -/

/-- Bundle of `subroutine_ok` contracts for the five `fixslice64` callees invoked by
    `aes256_encrypt`. -/
structure Aes256EncryptCallees (P : Program)
    (bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr :
      BitVec 64) : Prop where
  bitslice : subroutine_ok P bitsliceAddr bitslice4Spec
  subBytes : subroutine_ok P subBytesAddr subBytesSpec
  mixColumns1 : subroutine_ok P mixColumns1Addr mixColumns1Spec
  mixColumns3 : subroutine_ok P mixColumns3Addr mixColumns3Spec
  invBitslice : subroutine_ok P invBitsliceAddr invBitsliceSpec

/-- Discharge `Aes256EncryptCallees` from `hasInstrs` hypotheses for the five callees. -/
theorem Aes256EncryptCallees.of_hasInstrs {P : Program}
    {bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr : BitVec 64}
    (hbs : hasInstrs P bitsliceAddr bitsliceInstrs)
    (hsb : hasInstrs P subBytesAddr subBytesInstrs)
    (hmc1 : hasInstrs P mixColumns1Addr mixColumns1Instrs)
    (hmc3 : hasInstrs P mixColumns3Addr mixColumns3Instrs)
    (hibs : hasInstrs P invBitsliceAddr invBitsliceInstrs) :
    Aes256EncryptCallees P bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr
      invBitsliceAddr :=
  ⟨bitslice4_ok hbs, subBytes_ok hsb, mixColumns1_ok hmc1, mixColumns3_ok hmc3, invBitslice_ok hibs⟩

/-- Hoare contract for `fixslice64::aes256_encrypt` (`208`-byte stack frame = `128` B own frame +
    `80` B max callee frame). -/
@[expose] def aes256EncryptSpec :
    Spec (Bool × BitVec 64 × BitVec 64 × BitVec 64 × Model.FsKeys256 × Blocks4) where
  pre := fun (ro, outPtr, keysPtr, inPtr, ks, bs) s0 =>
    ⌜s0.readReg64 .x0 = keysPtr ∧ s0.readReg64 .x1 = inPtr ∧
      s0.readReg64 .x8 = outPtr ∧ Blocks4.Wf bs⌝ ∗
    (fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗
      memRegion outPtr 64 ∗ stackFrameAt s0.sp 208)
  post := fun (ro, outPtr, keysPtr, inPtr, ks, bs) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗
      (outPtr ↦ₛ blocks4Bytes (Model.aes256EncryptFs ks bs)) ∗ stackFrameAt s0.sp 208)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 3. Single-Block & 4-Block Byte-Level Bridge Lemmas (`Fixslice64.Equiv`) -/

/-- Single-block byte-level bridge for `CbcEncrypt.lean`: the first 16 bytes of `blocks4Bytes`
    of `aes256EncryptFs` equal `blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0)`
    and the remaining 48 padding bytes have length `48`. -/
theorem blocks4Bytes_aes256EncryptFs_single {key : List (BitVec 8)} (hkey : key.length = 32)
    (b0 : Block) {b1 b2 b3 : List (BitVec 8)}
    (hb1 : b1.length = 16) (hb2 : b2.length = 16) (hb3 : b3.length = 16) :
    (blocks4Bytes (Model.aes256EncryptFs (Model.aes256KeyScheduleFs key)
      ⟨blockToBytesLE b0, b1, b2, b3⟩)).take 16 =
      blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0) ∧
    ((blocks4Bytes (Model.aes256EncryptFs (Model.aes256KeyScheduleFs key)
      ⟨blockToBytesLE b0, b1, b2, b3⟩)).drop 16).length = 48 := by
  have hwf : Blocks4.Wf ⟨blockToBytesLE b0, b1, b2, b3⟩ :=
    ⟨Equiv.length_blockToBytesLE b0, hb1, hb2, hb3⟩
  have hb0 := Equiv.bytesToBlock_b0_aes256EncryptFs hkey b0 hb1 hb2 hb3
  rw [Equiv.aes256EncryptFs_eq hkey hwf] at hb0 ⊢
  dsimp only [Blocks4.map, blocks4Bytes] at hb0 ⊢
  have hlen0 : (Spec.Aes256.aes256Cipher key (blockToBytesLE b0)).length = 16 :=
    length_aes256Cipher key _
  have hlen1 : (Spec.Aes256.aes256Cipher key b1).length = 16 := length_aes256Cipher key _
  have hlen2 : (Spec.Aes256.aes256Cipher key b2).length = 16 := length_aes256Cipher key _
  have hlen3 : (Spec.Aes256.aes256Cipher key b3).length = 16 := length_aes256Cipher key _
  rw [List.append_assoc, List.append_assoc]
  constructor
  · rw [List.take_left' hlen0, ← hb0, blockToBytesLE_bytesToBlock _ hlen0]
  · rw [List.drop_left' hlen0]
    simp [hlen1, hlen2, hlen3]

/-- 4-block byte-level bridge for `CbcEncrypt.lean`: `blocks4Bytes` of `aes256EncryptFs` on four
    LE-encoded `Block`s equals the concatenation of their four `Spec.Aes256.aes256Enc` outputs. -/
theorem blocks4Bytes_aes256EncryptFs_quad {key : List (BitVec 8)} (hkey : key.length = 32)
    (b0 b1 b2 b3 : Block) :
    blocks4Bytes (Model.aes256EncryptFs (Model.aes256KeyScheduleFs key)
      ⟨blockToBytesLE b0, blockToBytesLE b1, blockToBytesLE b2, blockToBytesLE b3⟩) =
      blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b0) ++
      blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b1) ++
      blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b2) ++
      blockToBytesLE (Spec.Aes256.aes256Enc (bytesToKey32 key) b3) := by
  rw [Equiv.aes256EncryptFs_le hkey b0 b1 b2 b3]
  rfl

/-! ## 4. Rotation Normalization & Bit-Slice Algebra Lemmas -/

private theorem truncate64_append_self_ushiftRight (x : BitVec 64) {k : Nat} (hk : k < 64) :
    BitVec.truncate 64 ((x ++ x) >>> k) = x.rotateRight k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  dsimp only [BitVec.truncate]
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hk]
  split <;> split <;> first | rfl | omega | exact congrArg x.getLsbD (by omega)

namespace Simp
@[scoped arm64_norm, scoped wp_norm, scoped simp] theorem extr64_ror_8 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 8) = x.rotateRight 8 :=
  truncate64_append_self_ushiftRight x (by omega)
@[scoped arm64_norm, scoped wp_norm, scoped simp] theorem extr64_ror_16 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 16) = x.rotateRight 16 :=
  truncate64_append_self_ushiftRight x (by omega)
@[scoped arm64_norm, scoped wp_norm, scoped simp] theorem extr64_ror_24 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 24) = x.rotateRight 24 :=
  truncate64_append_self_ushiftRight x (by omega)
@[scoped arm64_norm, scoped wp_norm, scoped simp] theorem extr64_ror_32 (x : BitVec 64) :
    BitVec.truncate 64 ((x ++ x) >>> 32) = x.rotateRight 32 :=
  truncate64_append_self_ushiftRight x (by omega)
@[scoped arm64_norm, scoped wp_norm, scoped simp] theorem fold_rot1 (x : BitVec 64) :
    x.rotateRight 16 = rotateRows1 x := rfl
@[scoped arm64_norm, scoped wp_norm, scoped simp] theorem fold_rot2 (x : BitVec 64) :
    x.rotateRight 32 = rotateRows2 x := rfl
@[scoped arm64_norm, scoped wp_norm, scoped simp] theorem fold_rot12 (x : BitVec 64) :
    (x.rotateRight 24 &&& 0x00ff00ff00ff00ff#64) |||
    (x.rotateRight 8 &&& 0xff00ff00ff00ff00#64) = rotateRowsAndColumns12 x := rfl
end Simp

open scoped Simp

private theorem mixColumnsGen_addRk_words_eq (rot1 : BitVec 64 → BitVec 64) (st rk : Model.FsState) :
    (rk.s0 ^^^ rotateRows2 (rot1 st.s0 ^^^ st.s0)) ^^^ (rot1 st.s0 ^^^ (rot1 st.s7 ^^^ st.s7)) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s0 ∧
    (rk.s1 ^^^ rotateRows2 (rot1 st.s1 ^^^ st.s1)) ^^^
      (((rot1 st.s0 ^^^ st.s0) ^^^ rot1 st.s1) ^^^ (rot1 st.s7 ^^^ st.s7)) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s1 ∧
    (rk.s2 ^^^ rotateRows2 (rot1 st.s2 ^^^ st.s2)) ^^^ ((rot1 st.s1 ^^^ st.s1) ^^^ rot1 st.s2) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s2 ∧
    (rk.s3 ^^^ rotateRows2 (rot1 st.s3 ^^^ st.s3)) ^^^
      (((rot1 st.s2 ^^^ st.s2) ^^^ rot1 st.s3) ^^^ (rot1 st.s7 ^^^ st.s7)) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s3 ∧
    (rk.s4 ^^^ rotateRows2 (rot1 st.s4 ^^^ st.s4)) ^^^
      (((rot1 st.s3 ^^^ st.s3) ^^^ rot1 st.s4) ^^^ (rot1 st.s7 ^^^ st.s7)) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s4 ∧
    (rk.s5 ^^^ rotateRows2 (rot1 st.s5 ^^^ st.s5)) ^^^ ((rot1 st.s4 ^^^ st.s4) ^^^ rot1 st.s5) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s5 ∧
    (rk.s6 ^^^ rotateRows2 (rot1 st.s6 ^^^ st.s6)) ^^^ ((rot1 st.s5 ^^^ st.s5) ^^^ rot1 st.s6) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s6 ∧
    (rk.s7 ^^^ rotateRows2 (rot1 st.s7 ^^^ st.s7)) ^^^ ((rot1 st.s6 ^^^ st.s6) ^^^ rot1 st.s7) =
      (addRoundKeyFs (mixColumnsGen rot1 rotateRows2 st) rk).s7 := by
  dsimp only [addRoundKeyFs, Model.FsState.zipWith, mixColumnsGen]
  rw [BitVec.xor_comm (rot1 st.s0) st.s0, BitVec.xor_comm (rot1 st.s1) st.s1,
      BitVec.xor_comm (rot1 st.s2) st.s2, BitVec.xor_comm (rot1 st.s3) st.s3,
      BitVec.xor_comm (rot1 st.s4) st.s4, BitVec.xor_comm (rot1 st.s5) st.s5,
      BitVec.xor_comm (rot1 st.s6) st.s6, BitVec.xor_comm (rot1 st.s7) st.s7]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (ext i hi; simp only [BitVec.getElem_xor]; grind)

private theorem mask_sr2_disjoint :
    ∀ i : Fin 64,
      !((0x00ff000000ff0000#64).getLsbD i.val &&
        (decide (8 ≤ i.val) && (0x00ff000000ff0000#64).getLsbD (i.val - 8))) = true := by
  decide

namespace Simp

@[scoped arm64_norm, scoped wp_norm, scoped simp]
theorem deltaSwap1_sr2_hw_eq (x : BitVec 64) :
    ((((x ^^^ (x >>> 8)) &&& 0x00ff000000ff0000#64) |||
      (((x ^^^ (x >>> 8)) &&& 0x00ff000000ff0000#64) <<< 8)) ^^^ x) =
      deltaSwap1 x 8 0x00ff000000ff0000#64 := by
  dsimp only [deltaSwap1]
  set u := x ^^^ (x >>> 8)
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hdisj := mask_sr2_disjoint ⟨i, hi⟩
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, Bool.not_eq_true'] at hdisj ⊢
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.not_true, Bool.false_and, Bool.or_false]
    cases u.getLsbD i <;> cases (0x00ff000000ff0000#64).getLsbD i <;> cases x.getLsbD i <;> rfl
  · have h8' : 8 ≤ i := by omega
    simp only [h8, h8', decide_false, decide_true, Bool.not_false, Bool.true_and] at hdisj ⊢
    cases hm1 : (0x00ff000000ff0000#64).getLsbD i <;>
    cases hm2 : (0x00ff000000ff0000#64).getLsbD (i - 8) <;>
    cases u.getLsbD i <;> cases u.getLsbD (i - 8) <;> cases x.getLsbD i <;>
    simp_all

end Simp

/-! ## 5. Code Decomposition, Stack Frame Layout & Call Combinators -/

private structure EncCode (P : Program)
    (fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr :
      BitVec 64) : Prop where
  prolog : hasInstrs P fnAddr (decodeWords encSlice0)
  bl_bitslice : P.fetch (fnAddr + 0x030#64) = some (.bl (bitsliceAddr - (fnAddr + 0x030#64)))
  rk0 : hasInstrs P (fnAddr + 0x034#64) (decodeWords encSlice1)
  bl_sb0 : P.fetch (fnAddr + 0x088#64) = some (.bl (subBytesAddr - (fnAddr + 0x088#64)))
  mov_mc1_0 : hasInstrs P (fnAddr + 0x08c#64) (decodeWords encMovX0SpWords)
  bl_mc1_0 : P.fetch (fnAddr + 0x090#64) = some (.bl (mixColumns1Addr - (fnAddr + 0x090#64)))
  loop_init : hasInstrs P (fnAddr + 0x094#64) (decodeWords encLoopInitWords)
  loop_ark1 : hasInstrs P (fnAddr + 0x09c#64) (decodeWords encLoopArk1Words)
  loop_cbz_mov : hasInstrs P (fnAddr + 0x0ec#64) (decodeWords encLoopCbzMovWords)
  bl_sb_r2 : P.fetch (fnAddr + 0x0f4#64) = some (.bl (subBytesAddr - (fnAddr + 0x0f4#64)))
  mc2_head : hasInstrs P (fnAddr + 0x0f8#64) (decodeWords encMc2HeadWords)
  mc2_tail : hasInstrs P (fnAddr + 0x1ac#64) (decodeWords encMc2TailWords)
  bl_sb_r3 : P.fetch (fnAddr + 0x258#64) = some (.bl (subBytesAddr - (fnAddr + 0x258#64)))
  mov_mc3 : hasInstrs P (fnAddr + 0x25c#64) (decodeWords encMovX0SpWords)
  bl_mc3 : P.fetch (fnAddr + 0x260#64) = some (.bl (mixColumns3Addr - (fnAddr + 0x260#64)))
  loop_ark3 : hasInstrs P (fnAddr + 0x264#64) (decodeWords encSlice6)
  bl_sb_r4 : P.fetch (fnAddr + 0x2b8#64) = some (.bl (subBytesAddr - (fnAddr + 0x2b8#64)))
  mc0_head : hasInstrs P (fnAddr + 0x2bc#64) (decodeWords encMc0HeadWords)
  mc0_tail : hasInstrs P (fnAddr + 0x32c#64) (decodeWords encMc0TailWords)
  bl_sb_r5 : P.fetch (fnAddr + 0x39c#64) = some (.bl (subBytesAddr - (fnAddr + 0x39c#64)))
  mov_mc1_loop : hasInstrs P (fnAddr + 0x3a0#64) (decodeWords encMovX0SpWords)
  bl_mc1_loop : P.fetch (fnAddr + 0x3a4#64) = some (.bl (mixColumns1Addr - (fnAddr + 0x3a4#64)))
  loop_back : hasInstrs P (fnAddr + 0x3a8#64) (decodeWords encLoopBackWords)
  exit_sr2 : hasInstrs P (fnAddr + 0x3b4#64) (decodeWords encExitSr2Words)
  bl_sb_last : P.fetch (fnAddr + 0x448#64) = some (.bl (subBytesAddr - (fnAddr + 0x448#64)))
  exit_rk14 : hasInstrs P (fnAddr + 0x44c#64) (decodeWords encSlice10)
  bl_inv_bs : P.fetch (fnAddr + 0x4b4#64) = some (.bl (invBitsliceAddr - (fnAddr + 0x4b4#64)))
  epilog : hasInstrs P (fnAddr + 0x4b8#64) (decodeWords encSlice11)

private theorem split_words_at {P : Program} {fnAddr off : BitVec 64} (offNext : BitVec 64)
    {ws : List (BitVec 32)} {rest : List Instr}
    (h : hasInstrs P (fnAddr + off) (decodeWords ws ++ rest))
    (hoff : off + BitVec.ofNat 64 (4 * ws.length) = offNext := by rfl) :
    hasInstrs P (fnAddr + off) (decodeWords ws) ∧ hasInstrs P (fnAddr + offNext) rest := by
  have ⟨h1, h2⟩ := h.split_append (off := BitVec.ofNat 64 (4 * ws.length)) (by simp [decodeWords])
  rw [BitVec.add_assoc, hoff] at h2; exact ⟨h1, h2⟩

private theorem split_bl_at {P : Program} {fnAddr off : BitVec 64} (offNext : BitVec 64)
    {blInst : Instr} {rest : List Instr} (h : hasInstrs P (fnAddr + off) ([blInst] ++ rest))
    (hoff : off + 4#64 = offNext := by rfl) :
    P.fetch (fnAddr + off) = some blInst ∧ hasInstrs P (fnAddr + offNext) rest := by
  have ⟨h1, h2⟩ := h.split_append (off := 4#64) rfl
  rw [BitVec.add_assoc, hoff] at h2; exact ⟨h1.fetch_at_zero rfl, h2⟩

private theorem decodeWords_append (a b : List (BitVec 32)) :
    decodeWords (a ++ b) = decodeWords a ++ decodeWords b := List.map_append

private theorem EncCode.of_hasInstrs {P : Program}
    {fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (aes256EncryptInstrs fnAddr bitsliceAddr subBytesAddr
      mixColumns1Addr mixColumns3Addr invBitsliceAddr)) :
    EncCode P fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr := by
  unfold aes256EncryptInstrs at hc; dsimp only [encSlice3, encSlice4, encSlice7, encSlice9] at hc
  simp only [decodeWords_append, List.append_assoc] at hc
  conv at hc => arg 2; rw [← BitVec.add_zero fnAddr]
  obtain ⟨h_prolog, hc⟩ := split_words_at 0x030#64 (ws := encSlice0) hc
  obtain ⟨h_bl_bs, hc⟩ := split_bl_at 0x034#64 hc; obtain ⟨h_rk0, hc⟩ := split_words_at 0x088#64 hc
  obtain ⟨h_bl_sb0, hc⟩ := split_bl_at 0x08c#64 hc; obtain ⟨h_mov_mc1_0, hc⟩ := split_words_at 0x090#64 hc
  obtain ⟨h_bl_mc1_0, hc⟩ := split_bl_at 0x094#64 hc; obtain ⟨h_loop_init, hc⟩ := split_words_at 0x09c#64 hc
  obtain ⟨h_loop_ark1, hc⟩ := split_words_at 0x0ec#64 hc; obtain ⟨h_loop_cbz_mov, hc⟩ := split_words_at 0x0f4#64 hc
  obtain ⟨h_bl_sb_r2, hc⟩ := split_bl_at 0x0f8#64 hc; obtain ⟨h_mc2_head, hc⟩ := split_words_at 0x1ac#64 hc
  obtain ⟨h_mc2_tail, hc⟩ := split_words_at 0x258#64 hc; obtain ⟨h_bl_sb_r3, hc⟩ := split_bl_at 0x25c#64 hc
  obtain ⟨h_mov_mc3, hc⟩ := split_words_at 0x260#64 hc; obtain ⟨h_bl_mc3, hc⟩ := split_bl_at 0x264#64 hc
  obtain ⟨h_loop_ark3, hc⟩ := split_words_at 0x2b8#64 hc; obtain ⟨h_bl_sb_r4, hc⟩ := split_bl_at 0x2bc#64 hc
  obtain ⟨h_mc0_head, hc⟩ := split_words_at 0x32c#64 hc; obtain ⟨h_mc0_tail, hc⟩ := split_words_at 0x39c#64 hc
  obtain ⟨h_bl_sb_r5, hc⟩ := split_bl_at 0x3a0#64 hc; obtain ⟨h_mov_mc1_loop, hc⟩ := split_words_at 0x3a4#64 hc
  obtain ⟨h_bl_mc1_loop, hc⟩ := split_bl_at 0x3a8#64 hc; obtain ⟨h_loop_back, hc⟩ := split_words_at 0x3b4#64 hc
  obtain ⟨h_exit_sr2, hc⟩ := split_words_at 0x448#64 hc; obtain ⟨h_bl_sb_last, hc⟩ := split_bl_at 0x44c#64 hc
  obtain ⟨h_exit_rk14, hc⟩ := split_words_at 0x4b4#64 hc; obtain ⟨h_bl_inv_bs, h_epilog⟩ := split_bl_at 0x4b8#64 hc
  rw [BitVec.add_zero] at h_prolog
  exact ⟨h_prolog, h_bl_bs, h_rk0, h_bl_sb0, h_mov_mc1_0, h_bl_mc1_0, h_loop_init, h_loop_ark1,
    h_loop_cbz_mov, h_bl_sb_r2, h_mc2_head, h_mc2_tail, h_bl_sb_r3, h_mov_mc3, h_bl_mc3,
    h_loop_ark3, h_bl_sb_r4, h_mc0_head, h_mc0_tail, h_bl_sb_r5, h_mov_mc1_loop, h_bl_mc1_loop,
    h_loop_back, h_exit_sr2, h_bl_sb_last, h_exit_rk14, h_bl_inv_bs, h_epilog⟩

private def encSavedCells (sp_local v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) : SepProp :=
  ((sp_local + 64#64) ↦₆₄ v0) ∗ ((sp_local + 72#64) ↦₆₄ v1) ∗
  ((sp_local + 80#64) ↦₆₄ v2) ∗ ((sp_local + 88#64) ↦₆₄ v3) ∗
  ((sp_local + 96#64) ↦₆₄ v4) ∗ ((sp_local + 104#64) ↦₆₄ v5) ∗
  ((sp_local + 112#64) ↦₆₄ v6) ∗ ((sp_local + 120#64) ↦₆₄ v7)
private def encSavedRegs (s0 : State) : SepProp :=
  encSavedCells (s0.sp - 128#64) (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5)) (s0.readReg64 (.gpr 22#5))
    (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))

private theorem stackFrameAt_64_cells (sp0 : BitVec 64) :
    stackFrameAt sp0 64 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       encSavedCells (sp0 - 128#64) v0 v1 v2 v3 v4 v5 v6 v7) := by
  have ha0 : sp0 - 64#64 = (sp0 - 128#64) + 64#64 := by bv_omega
  have ha1 : sp0 - 56#64 = (sp0 - 128#64) + 72#64 := by bv_omega
  have ha2 : sp0 - 48#64 = (sp0 - 128#64) + 80#64 := by bv_omega
  have ha3 : sp0 - 40#64 = (sp0 - 128#64) + 88#64 := by bv_omega
  have ha4 : sp0 - 32#64 = (sp0 - 128#64) + 96#64 := by bv_omega
  have ha5 : sp0 - 24#64 = (sp0 - 128#64) + 104#64 := by bv_omega
  have ha6 : sp0 - 16#64 = (sp0 - 128#64) + 112#64 := by bv_omega
  have ha7 : sp0 - 8#64 = (sp0 - 128#64) + 120#64 := by bv_omega
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont, encSavedCells,
    ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]
private theorem encSavedRegs_entails_stackFrameAt_64 (s0 : State) :
    encSavedRegs s0 ⊢ stackFrameAt s0.sp 64 := by
  rw [stackFrameAt_64_cells]; iterate 8 apply Entails.sepExists_right
  exact Entails.refl _
private theorem stackFrameAt_208_eq (sp0 : BitVec 64) :
    stackFrameAt sp0 208 =
      stackFrameAt sp0 64 ∗ memRegion (sp0 - 128#64) 64 ∗ stackFrameAt (sp0 - 128#64) 80 := by
  rw [stackFrameAt_split sp0 64 144, stackFrameAt_split (sp0 - 64#64) 64 80,
      stackFrameAt_eq_memRegion (sp0 - 64#64) 64, show (sp0 - 64#64) - 64#64 = sp0 - 128#64 by bv_omega]

private structure EncFramePreserved (s sf : State) : Prop where
  x19 : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)
  x20 : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)
  x25 : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)
  x26 : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5)
  x27 : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)
  x28 : sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5)
  x29 : sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5)
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s
  sp : sf.sp = s.sp
  purePres : PureStepPreserved s sf
private theorem EncFramePreserved.of_calleeSaved {s sf : State}
    (hsp : sf.sp = s.sp) (hcs : CalleeSavedPreserved s sf) (hp : PureStepPreserved s sf) :
    EncFramePreserved s sf := by
  rw [CalleeSavedPreserved.iff_regs] at hcs
  rcases hcs with ⟨h19, h20, _, _, _, _, h25, h26, h27, h28, h29, hv⟩
  exact ⟨h19, h20, h25, h26, h27, h28, h29, hv, hsp, hp⟩
private theorem encStepPerm {s sf : State}
    (hp : pureStepProj sf = pureStepProj s) (hm : sf.mem.perm = s.mem.perm)
    (h19 : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by rfl)
    (h20 : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := by rfl)
    (h25 : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := by rfl)
    (h26 : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) := by rfl)
    (h27 : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by rfl)
    (h28 : sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by rfl)
    (h29 : sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) := by rfl)
    (hv : calleeSavedVRegs sf = calleeSavedVRegs s := by rfl)
    (hsp : sf.sp = s.sp := by rfl) : EncFramePreserved s sf :=
  ⟨h19, h20, h25, h26, h27, h28, h29, hv, hsp, PureStepPreserved.of_proj_perm hp hm⟩

private theorem step_bl_call {α : Type} {P : Program} {pc_bl calleeAddr target_pc : BitVec 64}
    {spec : Spec α} (hf : P.fetch pc_bl = some (.bl (calleeAddr - pc_bl)))
    (hcall : subroutine_ok P calleeAddr spec) (x : α)
    {s : State} {Pre F PreSpatial PostSpatial : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hent : Pre ⊢ PreSpatial ∗ F)
    (hpre_call : ∀ s_call, s_call = P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl) →
      PreSpatial ⊢ spec.pre x s_call)
    (hpost_call : ∀ s_call sf, s_call = P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl) →
      sf.sp = s.sp → spec.post x s_call sf = (⌜PureStepPreserved s_call sf⌝ ∗ PostSpatial))
    (hno_panic : ∀ s_call sf, spec.onPanic x s_call sf = ⌜False⌝ := by intros; rfl)
    (hno_exit : ∀ c s_call sf, spec.onExit x c s_call sf = ⌜False⌝ := by intros; rfl)
    (hno_oom : ∀ s_call sf, spec.onOom x s_call sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (PostSpatial ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  let s_call := P.evalInst (.bl (calleeAddr - pc_bl)) (s.setPC pc_bl)
  have hmem_sc : s_call.mem = s.mem := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hpc_sc : s_call.pc = calleeAddr := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; bv_omega
  have hrun_sc : s_call.status = .Running := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun]
  have hsp_sc_eq : s_call.sp = s.sp := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hsp_sc : s_call.spAligned = true := by simp only [State.spAligned, hsp_sc_eq]; exact hsp_al
  have hlr_sc : s_call.readReg64 Reg.lr = pc_bl + 4#64 := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hp_sc : PureStepPreserved s s_call := PureStepPreserved.of_proj_perm
    (by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]) (by simp [hmem_sc])
  have hcs_sc : CalleeSavedPreserved s s_call := by
    rw [CalleeSavedPreserved.iff_regs]; simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  apply SepWP.step_pure hpc hrun hf rfl hmem_sc
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc_sc hrun_sc hsp_sc hlr_sc ?_ ?_ ?_ ?_ ?_
  · intro R hm; have hent_all := Entails.trans hent (sepConj_mono_left (hpre_call s_call rfl))
    exact Satisfies.mono (by rw [← sepConj_assoc]; exact sepConj_mono_left hent_all) hm
  · intro R' sf _; rw [hno_panic]; exact not_satisfies_false_sepConj
  · intro R' c sf _; rw [hno_exit]; exact not_satisfies_false_sepConj
  · intro sf hpc_f hrun_f hsp_f hcs_f; have hsp_f' : sf.sp = s.sp := hsp_f.trans hsp_sc_eq
    rw [hpost_call s_call sf rfl hsp_f', sepConj_assoc]; apply SepWP.pure_elim; intro hp_f
    exact hnext sf hpc_f hrun_f hsp_f' (hcs_sc.trans hcs_f) (hp_sc.trans hp_f)
  · intro R' sf _ ho; rw [hno_oom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem call_sub_bytes {P : Program} {pc_bl subBytesAddr target_pc sp_local : BitVec 64}
    {st : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (subBytesAddr - pc_bl))) (hsub : subroutine_ok P subBytesAddr subBytesSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_eq : s.sp = sp_local) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 (.gpr 0#5) = sp_local)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = sp_local →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (fsStateAt sp_local (Model.subBytesFs st) ∗ stackFrameAt sp_local 80 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ stackFrameAt sp_local 80 ∗ F) post oom := by
  refine step_bl_call hf hsub (sp_local, st)
    (PreSpatial := fsStateAt sp_local st ∗ stackFrameAt sp_local 80)
    (PostSpatial := fsStateAt sp_local (Model.subBytesFs st) ∗ stackFrameAt sp_local 80)
    (F := F) hpc hrun hsp_al (Entails.of_eq_explicit (by sep_ac_rfl)) ?_ ?_ (hnext := ?_)
  · intro s_call hsc
    have hx0_sc : s_call.readReg64 .x0 = sp_local := by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0]
    have hsp_sc : s_call.sp = sp_local := by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp_eq]
    dsimp only [subBytesSpec]; rw [hsp_sc]; exact Entails.pure_right hx0_sc (Entails.refl _)
  · intro s_call _ hsc _
    have hsp_sc : s_call.sp = sp_local := by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp_eq]
    dsimp only [subBytesSpec]; rw [hsp_sc]
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f; rw [sepConj_assoc]; exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hp_f

private theorem call_mix_columns_32 {P : Program} (mcFn : Model.FsState → Model.FsState)
    {mcSpec : Spec (BitVec 64 × Model.FsState)} {pc_bl mcAddr target_pc sp_local : BitVec 64}
    {st : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (mcAddr - pc_bl))) (hmc : subroutine_ok P mcAddr mcSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_eq : s.sp = sp_local) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 (.gpr 0#5) = sp_local)
    (hspec : mcSpec = {
      pre := fun (ptr, st) s0 => ⌜s0.readReg64 .x0 = ptr⌝ ∗ (fsStateAt ptr st ∗ stackFrameAt s0.sp 32)
      post := fun (ptr, st) s0 sf => ⌜PureStepPreserved s0 sf⌝ ∗ (fsStateAt ptr (mcFn st) ∗ stackFrameAt s0.sp 32)
      onPanic := fun _ _ _ => ⌜False⌝, onExit := fun _ _ _ _ => ⌜False⌝, onOom := fun _ _ _ => ⌜False⌝ } := by rfl)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = sp_local →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (fsStateAt sp_local (mcFn st) ∗ stackFrameAt sp_local 80 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ stackFrameAt sp_local 80 ∗ F) post oom := by
  subst hspec; have hsplit80 := stackFrameAt_split sp_local 32 48
  refine step_bl_call hf hmc (sp_local, st)
    (PreSpatial := fsStateAt sp_local st ∗ stackFrameAt sp_local 32)
    (PostSpatial := fsStateAt sp_local (mcFn st) ∗ stackFrameAt sp_local 32)
    (F := stackFrameAt (sp_local - 32#64) 48 ∗ F)
    hpc hrun hsp_al (Entails.of_eq_explicit (by rw [hsplit80]; sep_ac_rfl)) ?_ ?_ (hnext := ?_)
  · intro s_call hsc
    have hx0_sc : s_call.readReg64 .x0 = sp_local := by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0]
    have hsp_sc : s_call.sp = sp_local := by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp_eq]
    dsimp only; rw [hsp_sc]; exact Entails.pure_right hx0_sc (Entails.refl _)
  · intro s_call _ hsc _
    have hsp_sc : s_call.sp = sp_local := by simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp_eq]
    dsimp only; rw [hsp_sc]
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f
    exact SepWP.weaken_pre (Entails.of_eq_explicit (by rw [hsplit80]; sep_ac_rfl))
      (hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hp_f)

private theorem call_bitslice {P : Program}
    {pc_bl bitsliceAddr target_pc sp_local inPtr : BitVec 64} {ro : Bool} {bs : Blocks4}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (bitsliceAddr - pc_bl))) (hbs : subroutine_ok P bitsliceAddr bitslice4Spec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_eq : s.sp = sp_local) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 (.gpr 0#5) = sp_local) (hx1 : s.readReg64 (.gpr 1#5) = inPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = inPtr + 16#64) (hx3 : s.readReg64 (.gpr 3#5) = inPtr + 32#64)
    (hx4 : s.readReg64 (.gpr 4#5) = inPtr + 48#64) (hwf : Blocks4.Wf bs)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = sp_local →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        (fsStateAt sp_local (Model.bitslice bs) ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ F) post oom) :
    SepWP P target_pc s (memRegion sp_local 64 ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗ F) post oom := by
  refine step_bl_call hf hbs (ro, sp_local, inPtr, bs)
    (PreSpatial := bytesAt ro inPtr (blocks4Bytes bs) ∗ memRegion sp_local 64)
    (PostSpatial := bytesAt ro inPtr (blocks4Bytes bs) ∗ fsStateAt sp_local (Model.bitslice bs))
    (F := F) hpc hrun hsp_al (Entails.of_eq_explicit (by sep_ac_rfl)) ?_ ?_ (hnext := ?_)
  · intro s_call hsc
    have hpure : s_call.readReg64 .x0 = sp_local ∧ s_call.readReg64 .x1 = inPtr ∧
        s_call.readReg64 .x2 = inPtr + 16#64 ∧ s_call.readReg64 .x3 = inPtr + 32#64 ∧
        s_call.readReg64 .x4 = inPtr + 48#64 ∧ Blocks4.Wf bs := by
      simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0, hx1, hx2, hx3, hx4, hwf]
    dsimp only [bitslice4Spec]; exact Entails.pure_right hpure (Entails.refl _)
  · intro _ _ _ _; rfl
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f
    exact SepWP.weaken_pre (Entails.of_eq_explicit (by sep_ac_rfl))
      (hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hp_f)

private theorem call_inv_bitslice {P : Program}
    {pc_bl invBitsliceAddr target_pc outPtr sp_local : BitVec 64} {st : Model.FsState}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc_bl = some (.bl (invBitsliceAddr - pc_bl))) (hibs : subroutine_ok P invBitsliceAddr invBitsliceSpec)
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_eq : s.sp = sp_local) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 (.gpr 0#5) = outPtr) (hx1 : s.readReg64 (.gpr 1#5) = sp_local)
    (hnext : ∀ sf : State, sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = sp_local →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((outPtr ↦ₛ blocks4Bytes (Model.invBitslice st)) ∗ fsStateAt sp_local st ∗ F) post oom) :
    SepWP P target_pc s (memRegion outPtr 64 ∗ fsStateAt sp_local st ∗ F) post oom := by
  refine step_bl_call hf hibs (outPtr, sp_local, st)
    (PreSpatial := fsStateAt sp_local st ∗ memRegion outPtr 64)
    (PostSpatial := fsStateAt sp_local st ∗ (outPtr ↦ₛ blocks4Bytes (Model.invBitslice st)))
    (F := F) hpc hrun hsp_al (Entails.of_eq_explicit (by sep_ac_rfl)) ?_ ?_ (hnext := ?_)
  · intro s_call hsc
    have hpure : s_call.readReg64 .x0 = outPtr ∧ s_call.readReg64 .x1 = sp_local := by
      simp [hsc, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0, hx1]
    dsimp only [invBitsliceSpec]; exact Entails.pure_right hpure (Entails.refl _)
  · intro _ _ _ _; rfl
  · intro sf hpc_f hrun_f hsp_f hcs_f hp_f
    exact SepWP.weaken_pre (Entails.of_eq_explicit (by sep_ac_rfl))
      (hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hp_f)

/-! ## 6. Chunk `SepWP` Step Lemmas -/

private theorem sp_sub128_and_15 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 128#64) &&& 15#64 = 0#64 := by revert h; bv_bits
private theorem spAligned_of_eq {s : State} {sp_local : BitVec 64}
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) : s.spAligned = true := by
  simp [State.spAligned, hsp, hsp_loc]
private theorem cs_x21 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) := ((CalleeSavedPreserved.iff_regs s sf).1 h).2.2.1
private theorem cs_x22 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) := ((CalleeSavedPreserved.iff_regs s sf).1 h).2.2.2.1

private structure PrologAnchor (s0 : State) (outPtr keysPtr : BitVec 64) (s : State) : Prop where
  sp : s.sp = s0.sp - 128#64
  x19 : s.readReg64 (.gpr 19#5) = outPtr
  x20 : s.readReg64 (.gpr 20#5) = keysPtr
  x25 : s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  x28 : s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  purePres : PureStepPreserved s0 s
private theorem PrologAnchor.step_frame {s0 s sf : State} {outPtr keysPtr : BitVec 64}
    (ha : PrologAnchor s0 outPtr keysPtr s) (hf : EncFramePreserved s sf) :
    PrologAnchor s0 outPtr keysPtr sf :=
  ⟨hf.sp.trans ha.sp, hf.x19.trans ha.x19, hf.x20.trans ha.x20, hf.x25.trans ha.x25,
   hf.x26.trans ha.x26, hf.x27.trans ha.x27, hf.x28.trans ha.x28,
   hf.vregs.trans ha.vregs, ha.purePres.trans hf.purePres⟩
private theorem PrologAnchor.step_call {s0 s sf : State} {outPtr keysPtr : BitVec 64}
    (ha : PrologAnchor s0 outPtr keysPtr s) (hsp : sf.sp = s0.sp - 128#64)
    (hcs : CalleeSavedPreserved s sf) (hp : PureStepPreserved s sf) :
    PrologAnchor s0 outPtr keysPtr sf :=
  ha.step_frame (EncFramePreserved.of_calleeSaved (hsp.trans ha.sp.symm) hcs hp)

private def Ark1LiveRegs (st : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 12#5) = st.s0 ∧ s.readReg64 (.gpr 13#5) = st.s1 ∧
  s.readReg64 (.gpr 14#5) = st.s2 ∧ s.readReg64 (.gpr 15#5) = st.s3 ∧
  s.readReg64 (.gpr 9#5) = st.s4 ∧ s.readReg64 (.gpr 8#5) = st.s5 ∧
  s.readReg64 (.gpr 10#5) = st.s6 ∧ s.readReg64 (.gpr 11#5) = st.s7
private def Mc2MidRegs (st : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = rotateRowsAndColumns12 st.s5 ∧ s.readReg64 (.gpr 1#5) = rotateRowsAndColumns12 st.s7 ∧
  s.readReg64 (.gpr 2#5) = rotateRowsAndColumns12 st.s0 ∧ s.readReg64 (.gpr 3#5) = rotateRowsAndColumns12 st.s4 ∧
  s.readReg64 (.gpr 5#5) = rotateRowsAndColumns12 st.s1 ∧ s.readReg64 (.gpr 8#5) = st.s6 ∧
  s.readReg64 (.gpr 9#5) = st.s5 ∧ s.readReg64 (.gpr 10#5) = st.s4 ∧ s.readReg64 (.gpr 11#5) = st.s2 ∧
  s.readReg64 (.gpr 12#5) = st.s3 ∧ s.readReg64 (.gpr 13#5) = rotateRowsAndColumns12 st.s6 ∧
  s.readReg64 (.gpr 14#5) = rotateRowsAndColumns12 st.s0 ^^^ st.s0 ∧ s.readReg64 (.gpr 15#5) = st.s1 ∧
  s.readReg64 (.gpr 16#5) = st.s7 ∧ s.readReg64 (.gpr 17#5) = rotateRowsAndColumns12 st.s2 ∧
  s.readReg64 (.gpr 18#5) = rotateRowsAndColumns12 st.s3
private def Mc0MidRegs (st rk4 : Model.FsState) (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = rotateRows1 st.s6 ∧ s.readReg64 (.gpr 1#5) = rotateRows1 st.s7 ^^^ st.s7 ∧
  s.readReg64 (.gpr 3#5) = rotateRows1 st.s3 ∧ s.readReg64 (.gpr 4#5) = rk4.s2 ∧
  s.readReg64 (.gpr 8#5) = rotateRows1 st.s7 ∧ s.readReg64 (.gpr 9#5) = rotateRows1 st.s5 ∧
  s.readReg64 (.gpr 10#5) = st.s6 ∧ s.readReg64 (.gpr 11#5) = rotateRows1 st.s4 ∧
  s.readReg64 (.gpr 13#5) = (rotateRows1 st.s1 ^^^ st.s1) ^^^ rotateRows1 st.s2 ∧
  s.readReg64 (.gpr 14#5) = rotateRows1 st.s2 ^^^ st.s2 ∧ s.readReg64 (.gpr 15#5) = rotateRows1 st.s3 ^^^ st.s3 ∧
  s.readReg64 (.gpr 16#5) = st.s4 ∧ s.readReg64 (.gpr 17#5) = st.s5 ∧ s.readReg64 (.gpr 18#5) = rk4.s3
private def rkQuadAt (rkBase : BitVec 64) (rk1 rk2 rk3 rk4 : Model.FsState) : SepProp :=
  fsStateAt rkBase rk1 ∗ fsStateAt (rkBase + 0x040#64) rk2 ∗
  fsStateAt (rkBase + 0x080#64) rk3 ∗ fsStateAt (rkBase + 0x0c0#64) rk4
private theorem fsKeys256At_quads (ptr : BitVec 64) (ks : FsKeys256) :
    fsKeys256At ptr ks =
      fsStateAt ptr ks.rk0 ∗ rkQuadAt (ptr + 0x040#64) ks.rk1 ks.rk2 ks.rk3 ks.rk4 ∗
      rkQuadAt (ptr + 0x140#64) ks.rk5 ks.rk6 ks.rk7 ks.rk8 ∗
      rkQuadAt (ptr + 0x240#64) ks.rk9 ks.rk10 ks.rk11 ks.rk12 ∗
      fsStateAt (ptr + 0x340#64) ks.rk13 ∗ fsStateAt (ptr + 0x380#64) ks.rk14 := by
  unfold fsKeys256At rkQuadAt; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
private def encLoop4Rounds (rk1 rk2 rk3 rk4 st_pre : Model.FsState) : Model.FsState :=
  let st_b := addRoundKeyFs (mixColumns2 (Model.subBytesFs (addRoundKeyFs st_pre rk1))) rk2
  let st_c := addRoundKeyFs (Model.mixColumns3 (Model.subBytesFs st_b)) rk3
  Model.mixColumns1 (Model.subBytesFs (addRoundKeyFs (mixColumns0 (Model.subBytesFs st_c)) rk4))
private theorem aes256EncryptFs_unroll (ks : FsKeys256) (bs : Blocks4) :
    Model.invBitslice (addRoundKeyFs (Model.subBytesFs (shiftRows2 (addRoundKeyFs
      (encLoop4Rounds ks.rk9 ks.rk10 ks.rk11 ks.rk12
        (encLoop4Rounds ks.rk5 ks.rk6 ks.rk7 ks.rk8
          (encLoop4Rounds ks.rk1 ks.rk2 ks.rk3 ks.rk4
            (Model.mixColumns1 (Model.subBytesFs (addRoundKeyFs (Model.bitslice bs) ks.rk0))))))
      ks.rk13))) ks.rk14) = Model.aes256EncryptFs ks bs := rfl

section
arm64_proof_prelude
local macro "bv_off" : tactic =>
  `(tactic| simp only [BitVec.add_assoc, BitVec.sub_eq_add_neg, BitVec.reduceNeg, BitVec.reduceAdd])
local macro "wp_apply_pre " e:term : tactic =>
  `(tactic| (refine' SepWP.weaken_pre ?_ $e; · sep_frame (disch := bv_off)))

private theorem step_prolog {P : Program}
    {fnAddr target_pc outPtr keysPtr inPtr v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P fnAddr (decodeWords encSlice0)) (hpc : s0.pc = fnAddr)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = keysPtr) (hx1 : s0.readReg64 .x1 = inPtr) (hx8 : s0.readReg64 .x8 = outPtr)
    (hnext : ∀ s1 : State, s1.pc = fnAddr + 0x030#64 → s1.status = .Running → PrologAnchor s0 outPtr keysPtr s1 →
      s1.readReg64 (.gpr 0#5) = s0.sp - 128#64 → s1.readReg64 (.gpr 1#5) = inPtr →
      s1.readReg64 (.gpr 2#5) = inPtr + 16#64 → s1.readReg64 (.gpr 3#5) = inPtr + 32#64 →
      s1.readReg64 (.gpr 4#5) = inPtr + 48#64 → SepWP P target_pc s1 (encSavedRegs s0 ∗ F) post oom) :
    SepWP P target_pc s0 (encSavedCells (s0.sp - 128#64) v0 v1 v2 v3 v4 v5 v6 v7 ∗ F) post oom := by
  have hsp128 := sp_sub128_and_15 (sp_and_15_of_spAligned hsp)
  have_instrs hc 0 12; dsimp only [encSavedCells, encSavedRegs]
  wp_steps 1; wp_stp64 hf_1 m1 hm1; wp_stp64 hf_2 m2 hm2; wp_stp64 hf_3 m3 hm3; wp_stp64 hf_4 m4 hm4; wp_steps 7
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1])⟩
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx1])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])

private theorem step_rk0 {P : Program} {pc0 target_pc sp_local keysPtr : BitVec 64}
    {st rk0 : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encSlice1)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) (hx20 : s.readReg64 (.gpr 20#5) = keysPtr)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x054#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = sp_local →
      SepWP P target_pc sf (fsStateAt sp_local (addRoundKeyFs st rk0) ∗ fsStateAt keysPtr rk0 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ fsStateAt keysPtr rk0 ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  subst hx20; have_instrs hc 0 21; dsimp only [fsStateAt, addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 8; wp_stp64 hf_8 m1 hm1; wp_steps 5; wp_stp64 hf_14 m2 hm2
  wp_steps 1; wp_stp64 hf_16 m3 hm3; wp_steps 3; wp_stp64 hf_20 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm])

private theorem step_mov_x0_sp {P : Program} {pc0 target_pc sp_local : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encMovX0SpWords))
    (hpc : s.pc = pc0) (hrun : s.status = .Running) (hsp : s.sp = sp_local)
    (hnext : ∀ sf : State, sf.pc = pc0 + 4#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = sp_local → sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have_instrs hc 0 1; wp_steps 1
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) rfl) (by simp [wp_norm, arm64_norm]) rfl rfl

private theorem step_cbz_mov_ne {P : Program} {fnAddr target_pc sp_local cnt : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x0ec#64) (decodeWords encLoopCbzMovWords))
    (hpc : s.pc = fnAddr + 0x0ec#64) (hrun : s.status = .Running) (hsp : s.sp = sp_local)
    (hx22 : s.readReg64 (.gpr 22#5) = cnt) (hcnt : cnt ≠ 0#64)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x0f4#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = sp_local → sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 22#5) = cnt → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 2
  have hs_cbz : P.evalInst (.cbz .W64 false (.gpr 22#5) 712#64) (s.setPC (fnAddr + 0x0ec#64)) =
      s.setPC (fnAddr + 0x0f0#64) := by
    have hne : cnt ≠ 0 := hcnt; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, bv_lin_norm, hx22, hne]
  apply SepWP.step_pure hpc hrun hf_0 rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  rw [hs_cbz]; have hsp_reg : (s.setPC (fnAddr + 0x0f0#64)).readReg64 .sp = sp_local := hsp; wp_steps 1
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) rfl) (by simp [wp_norm, arm64_norm]) rfl hx22

private theorem step_cbz_eq {P : Program} {fnAddr target_pc : BitVec 64} {st : Model.FsState}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x0ec#64) (decodeWords encLoopCbzMovWords))
    (hpc : s.pc = fnAddr + 0x0ec#64) (hrun : s.status = .Running)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64) (hlive : Ark1LiveRegs st s)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x3b4#64 → sf.status = .Running →
      EncFramePreserved s sf → Ark1LiveRegs st sf → SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  have_instrs hc 0 1
  have hs_cbz : P.evalInst (.cbz .W64 false (.gpr 22#5) 712#64) (s.setPC (fnAddr + 0x0ec#64)) =
      s.setPC (fnAddr + 0x3b4#64) := by
    simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, bv_lin_norm, hx22]
  apply SepWP.step_pure hpc hrun hf_0 rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  rw [hs_cbz]
  refine hnext _ (by simp [arm64_norm, wp_norm]) (by simp [arm64_norm, wp_norm, hrun])
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, PureStepPreserved.of_proj_perm ?_ ?_⟩
    (by simpa [Ark1LiveRegs, arm64_norm, wp_norm] using hlive) <;> simp [arm64_norm, wp_norm]

private theorem step_loop_ark1 {P : Program} {pc0 target_pc sp_local rk1Ptr : BitVec 64}
    {st rk1 : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encLoopArk1Words)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) (hx21 : s.readReg64 (.gpr 21#5) = rk1Ptr + 0x060#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x050#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 21#5) = rk1Ptr + 0x060#64 → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      Ark1LiveRegs (addRoundKeyFs st rk1) sf →
      SepWP P target_pc sf (fsStateAt sp_local (addRoundKeyFs st rk1) ∗ fsStateAt rk1Ptr rk1 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ fsStateAt rk1Ptr rk1 ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 20; dsimp only [fsStateAt, addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 8; wp_stp64 hf_8 m1 hm1; wp_steps 6; wp_stp64 hf_15 m2 hm2
  wp_stp64 hf_16 m3 hm3; wp_steps 2; wp_stp64 hf_19 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    hx21 rfl (by simp [Ark1LiveRegs, addRoundKeyFs, Model.FsState.zipWith, wp_norm, arm64_norm])

private theorem step_mc2_head {P : Program} {pc0 target_pc sp_local : BitVec 64}
    {st : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encMc2HeadWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x0b4#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      Mc2MidRegs st sf → SepWP P target_pc sf (fsStateAt sp_local st ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 45; dsimp only [fsStateAt]; wp_steps 45
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) rfl) rfl rfl (by simp [Mc2MidRegs, wp_norm, arm64_norm])

private theorem step_mc2_tail {P : Program} {pc0 target_pc sp_local rk2Ptr : BitVec 64}
    {st rk2 : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encMc2TailWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64)
    (hx21 : s.readReg64 (.gpr 21#5) = rk2Ptr + 0x020#64) (hregs : Mc2MidRegs st s)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x0ac#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = sp_local → sf.readReg64 (.gpr 21#5) = rk2Ptr + 0x020#64 →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt sp_local (addRoundKeyFs (mixColumns2 st) rk2) ∗ fsStateAt rk2Ptr rk2 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ fsStateAt rk2Ptr rk2 ∗ F) post oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx5, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18⟩
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 43; dsimp only [fsStateAt, mixColumns2] at hnext ⊢
  wp_steps 16; wp_stp64 hf_16 m1 hm1; wp_steps 9; wp_stp64 hf_26 m2 hm2; wp_steps 14; wp_stp64 hf_41 m3 hm3; wp_stp64 hf_42 m4 hm4
  rcases mixColumnsGen_addRk_words_eq rotateRowsAndColumns12 st rk2 with ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩
  wp_conv_pre => simp only [hx0, hx1, hx2, hx3, hx5, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15,
    hx16, hx17, hx18, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) hx21 rfl

private theorem step_loop_ark3 {P : Program} {pc0 target_pc sp_local rk3Ptr : BitVec 64}
    {st rk3 : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encSlice6)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) (hx21 : s.readReg64 (.gpr 21#5) = rk3Ptr - 0x020#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x054#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = sp_local → sf.readReg64 (.gpr 21#5) = rk3Ptr - 0x020#64 →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt sp_local (addRoundKeyFs st rk3) ∗ fsStateAt rk3Ptr rk3 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ fsStateAt rk3Ptr rk3 ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 21; dsimp only [fsStateAt, addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 8; wp_stp64 hf_8 m1 hm1; wp_steps 5; wp_stp64 hf_14 m2 hm2; wp_steps 1; wp_stp64 hf_16 m3 hm3; wp_steps 3; wp_stp64 hf_20 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) hx21 rfl

private theorem step_mc0_head {P : Program} {pc0 target_pc sp_local rk4Ptr : BitVec 64}
    {st rk4 : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encMc0HeadWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) (hx21 : s.readReg64 (.gpr 21#5) = rk4Ptr - 0x060#64)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x070#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 21#5) = rk4Ptr - 0x060#64 → sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      Mc0MidRegs st rk4 sf → SepWP P target_pc sf
        (((sp_local ↦₆₄ (addRoundKeyFs (mixColumns0 st) rk4).s0) ∗
          ((sp_local + 8#64) ↦₆₄ (addRoundKeyFs (mixColumns0 st) rk4).s1) ∗
          ((sp_local + 16#64) ↦₆₄ st.s2) ∗ ((sp_local + 24#64) ↦₆₄ st.s3) ∗
          ((sp_local + 32#64) ↦₆₄ st.s4) ∗ ((sp_local + 40#64) ↦₆₄ st.s5) ∗
          ((sp_local + 48#64) ↦₆₄ st.s6) ∗ ((sp_local + 56#64) ↦₆₄ st.s7)) ∗ fsStateAt rk4Ptr rk4 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ fsStateAt rk4Ptr rk4 ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 28; dsimp only [fsStateAt, mixColumns0] at hnext ⊢; wp_steps 20; wp_stp64 hf_20 m1 hm1; wp_steps 7
  rcases mixColumnsGen_addRk_words_eq rotateRows1 st rk4 with ⟨hw0, hw1, _, _, _, _, _, _⟩; wp_conv_pre => rw [hw0, hw1]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm1])) hx21 rfl (by simp [Mc0MidRegs, wp_norm, arm64_norm])

private theorem step_mc0_tail {P : Program} {pc0 target_pc sp_local rk4Ptr : BitVec 64}
    {st rk4 : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encMc0TailWords)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64)
    (hx21 : s.readReg64 (.gpr 21#5) = rk4Ptr - 0x060#64) (hregs : Mc0MidRegs st rk4 s)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x070#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = sp_local → sf.readReg64 (.gpr 21#5) = rk4Ptr - 0x060#64 →
      sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      SepWP P target_pc sf (fsStateAt sp_local (addRoundKeyFs (mixColumns0 st) rk4) ∗ fsStateAt rk4Ptr rk4 ∗ F) post oom) :
    SepWP P target_pc s
      (((sp_local ↦₆₄ (addRoundKeyFs (mixColumns0 st) rk4).s0) ∗
        ((sp_local + 8#64) ↦₆₄ (addRoundKeyFs (mixColumns0 st) rk4).s1) ∗
        ((sp_local + 16#64) ↦₆₄ st.s2) ∗ ((sp_local + 24#64) ↦₆₄ st.s3) ∗
        ((sp_local + 32#64) ↦₆₄ st.s4) ∗ ((sp_local + 40#64) ↦₆₄ st.s5) ∗
        ((sp_local + 48#64) ↦₆₄ st.s6) ∗ ((sp_local + 56#64) ↦₆₄ st.s7)) ∗ fsStateAt rk4Ptr rk4 ∗ F) post oom := by
  rcases hregs with ⟨hx0, hx1, hx3, hx4, hx8, hx9, hx10, hx11, hx13, hx14, hx15, hx16, hx17, hx18⟩
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 28; dsimp only [fsStateAt, mixColumns0] at hnext ⊢
  wp_steps 12; wp_stp64 hf_12 m1 hm1; wp_steps 11; wp_stp64 hf_24 m2 hm2; wp_steps 2; wp_stp64 hf_27 m3 hm3
  rcases mixColumnsGen_addRk_words_eq rotateRows1 st rk4 with ⟨_, _, hw2, hw3, hw4, hw5, hw6, hw7⟩
  wp_conv_pre => simp only [hx0, hx1, hx3, hx4, hx8, hx9, hx10, hx11, hx13, hx14, hx15, hx16, hx17, hx18, hw2, hw3, hw4, hw5, hw6, hw7]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) hx21 rfl

private theorem step_exit_sr2 {P : Program} {pc0 target_pc sp_local : BitVec 64}
    {st stOld : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encExitSr2Words)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) (hregs : Ark1LiveRegs st s)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x094#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = sp_local → SepWP P target_pc sf (fsStateAt sp_local (shiftRows2 st) ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local stOld ∗ F) post oom := by
  rcases hregs with ⟨hx12, hx13, hx14, hx15, hx9, hx8, hx10, hx11⟩
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 37; dsimp only [fsStateAt, shiftRows2, Model.FsState.map] at hnext ⊢
  wp_steps 16; wp_stp64 hf_16 m1 hm1; wp_steps 8; wp_stp64 hf_25 m2 hm2; wp_steps 7; wp_stp64 hf_33 m3 hm3; wp_steps 2; wp_stp64 hf_36 m4 hm4
  wp_conv_pre => simp only [hx12, hx13, hx14, hx15, hx9, hx8, hx10, hx11]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm])

private theorem step_exit_rk14 {P : Program} {pc0 target_pc sp_local outPtr keysPtr : BitVec 64}
    {st rk14 : Model.FsState} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 (decodeWords encSlice10)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr) (hx20 : s.readReg64 (.gpr 20#5) = keysPtr)
    (hnext : ∀ sf : State, sf.pc = pc0 + 0x068#64 → sf.status = .Running → EncFramePreserved s sf →
      sf.readReg64 (.gpr 0#5) = outPtr → sf.readReg64 (.gpr 1#5) = sp_local →
      SepWP P target_pc sf (fsStateAt sp_local (addRoundKeyFs st rk14) ∗ fsStateAt (keysPtr + 0x380#64) rk14 ∗ F) post oom) :
    SepWP P target_pc s (fsStateAt sp_local st ∗ fsStateAt (keysPtr + 0x380#64) rk14 ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp_local := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  subst hx19 hx20; have_instrs hc 0 26; dsimp only [fsStateAt, addRoundKeyFs, Model.FsState.zipWith]
  wp_steps 10; wp_stp64 hf_10 m1 hm1; wp_steps 7; wp_stp64 hf_18 m2 hm2; wp_steps 2; wp_stp64 hf_21 m3 hm3; wp_steps 3; wp_stp64 hf_25 m4 hm4
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (encStepPerm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1]))
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])

private theorem step_epilog {P : Program} {pc0 outPtr keysPtr inPtr : BitVec 64}
    {ro : Bool} {ks : FsKeys256} {bs : Blocks4} {stFinal : Model.FsState} {s0 s : State} {R : SepProp}
    (hc : hasInstrs P pc0 (decodeWords encSlice11)) (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsp_loc : (s0.sp - 128#64) &&& 15#64 = 0#64) (hanc : PrologAnchor s0 outPtr keysPtr s) :
    SepWP P (s0.readReg64 Reg.lr) s
      ((outPtr ↦ₛ blocks4Bytes (Model.aes256EncryptFs ks bs)) ∗ fsStateAt (s0.sp - 128#64) stFinal ∗
       encSavedRegs s0 ∗ stackFrameAt (s0.sp - 128#64) 80 ∗ fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs))
      (fun sf Q => (sf.mem ⊨ Q ∗ R → sf.mem ⊨ aes256EncryptSpec.post (ro, outPtr, keysPtr, inPtr, ks, bs) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) (fun _ => ⌜False⌝) := by
  rcases hanc with ⟨hsp, _, _, hx25, hx26, hx27, hx28, hvregs, hpure⟩
  have hsp_reg : s.readReg64 .sp = s0.sp - 128#64 := hsp; have hsp_and : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact hsp_loc
  have_instrs hc 0 6; dsimp only [encSavedRegs, encSavedCells]; wp_steps 6
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
  · dsimp only [aes256EncryptSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl),
      Satisfies.mono (sepConj_mono_left ?_) hm⟩
    have hent_saved := encSavedRegs_entails_stackFrameAt_64 s0
    have hent_st := fsStateAt_entails_memRegion (s0.sp - 128#64) stFinal
    refine Entails.trans (Q := (outPtr ↦ₛ blocks4Bytes (Model.aes256EncryptFs ks bs)) ∗
        fsStateAt (s0.sp - 128#64) stFinal ∗ encSavedRegs s0 ∗
        stackFrameAt (s0.sp - 128#64) 80 ∗ fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs))
      (Entails.of_eq_explicit (by dsimp only [encSavedRegs, encSavedCells])) ?_
    rw [stackFrameAt_208_eq s0.sp]
    exact Entails.trans (sepConj_mono_right (sepConj_mono hent_st (sepConj_mono_left hent_saved)))
      (Entails.of_eq_explicit (by sep_ac_rfl))
  · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, hx25, hx26, hx27, hx28, hvregs]

private theorem step_loop_iter {P : Program}
    {fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr : BitVec 64}
    {target_pc outPtr keysPtr rkBase cnt : BitVec 64}
    {rk1 rk2 rk3 rk4 st_pre : Model.FsState} {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : EncCode P fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr)
    (hcallees : Aes256EncryptCallees P bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr
      invBitsliceAddr)
    (hpc : s.pc = fnAddr + 0x09c#64) (hrun : s.status = .Running)
    (hsp_loc : (s0.sp - 128#64) &&& 15#64 = 0#64) (hanc : PrologAnchor s0 outPtr keysPtr s)
    (hx21 : s.readReg64 (.gpr 21#5) = rkBase + 0x060#64)
    (hx22 : s.readReg64 (.gpr 22#5) = cnt) (hcnt : cnt ≠ 0#64 := by decide)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x09c#64 → sf.status = .Running →
      PrologAnchor s0 outPtr keysPtr sf →
      sf.readReg64 (.gpr 21#5) = (rkBase + 0x100#64) + 0x060#64 →
      sf.readReg64 (.gpr 22#5) = cnt - 0x020#64 →
      SepWP P target_pc sf
        (fsStateAt (s0.sp - 128#64) (encLoop4Rounds rk1 rk2 rk3 rk4 st_pre) ∗
         rkQuadAt rkBase rk1 rk2 rk3 rk4 ∗ stackFrameAt (s0.sp - 128#64) 80 ∗ F) post oom) :
    SepWP P target_pc s
      (fsStateAt (s0.sp - 128#64) st_pre ∗ rkQuadAt rkBase rk1 rk2 rk3 rk4 ∗
       stackFrameAt (s0.sp - 128#64) 80 ∗ F) post oom := by
  dsimp only [rkQuadAt, encLoop4Rounds] at hnext ⊢
  wp_apply_pre (step_loop_ark1 hc.loop_ark1 hpc hrun hanc.sp hsp_loc hx21 ?_)
  intro s1 hpc1 hrun1 hfr1 hx21_1 hx22_1 _; have hanc1 := hanc.step_frame hfr1
  refine step_cbz_mov_ne hc.loop_cbz_mov (by rw [hpc1]; bv_off) hrun1 hanc1.sp
    (hx22_1.trans hx22) hcnt fun s2 hpc2 hrun2 hfr2 hx0_2 hx21_2 hx22_2 => ?_
  have hanc2 := hanc1.step_frame hfr2
  wp_apply_pre (call_sub_bytes hc.bl_sb_r2 hcallees.subBytes hpc2 hrun2
    hanc2.sp (spAligned_of_eq hanc2.sp hsp_loc) hx0_2 ?_)
  intro s3 hpc3 hrun3 hsp3 hcs3 hp3; have hanc3 := hanc2.step_call hsp3 hcs3 hp3
  have hx21_3 := (cs_x21 hcs3).trans (hx21_2.trans hx21_1)
  have hx22_3 := (cs_x22 hcs3).trans hx22_2
  wp_apply_pre (step_mc2_head hc.mc2_head (by rw [hpc3]; bv_off) hrun3 hanc3.sp hsp_loc ?_)
  intro s4 hpc4 hrun4 hfr4 hx21_4 hx22_4 hmid2; have hanc4 := hanc3.step_frame hfr4
  wp_apply_pre (step_mc2_tail hc.mc2_tail (by rw [hpc4]; bv_off) hrun4 hanc4.sp hsp_loc
    (rk2Ptr := rkBase + 0x040#64) (by rw [hx21_4, hx21_3]; bv_off) hmid2 ?_)
  intro s5 hpc5 hrun5 hfr5 hx0_5 hx21_5 hx22_5; have hanc5 := hanc4.step_frame hfr5
  wp_apply_pre (call_sub_bytes hc.bl_sb_r3 hcallees.subBytes (by rw [hpc5]; bv_off) hrun5
    hanc5.sp (spAligned_of_eq hanc5.sp hsp_loc) hx0_5 ?_)
  intro s6 hpc6 hrun6 hsp6 hcs6 hp6; have hanc6 := hanc5.step_call hsp6 hcs6 hp6
  have hx21_6 : s6.readReg64 (.gpr 21#5) = rkBase + 0x060#64 := by rw [cs_x21 hcs6, hx21_5]; bv_off
  have hx22_6 := (cs_x22 hcs6).trans (hx22_5.trans hx22_4 |>.trans hx22_3)
  refine step_mov_x0_sp hc.mov_mc3 (by rw [hpc6]; bv_off) hrun6 hanc6.sp
    fun s7 hpc7 hrun7 hfr7 hx0_7 hx21_7 hx22_7 => ?_
  have hanc7 := hanc6.step_frame hfr7
  wp_apply_pre (call_mix_columns_32 Model.mixColumns3 hc.bl_mc3 hcallees.mixColumns3
    (by rw [hpc7]; bv_off) hrun7 hanc7.sp (spAligned_of_eq hanc7.sp hsp_loc) hx0_7 rfl ?_)
  intro s8 hpc8 hrun8 hsp8 hcs8 hp8; have hanc8 := hanc7.step_call hsp8 hcs8 hp8
  have hx21_8 := (cs_x21 hcs8).trans (hx21_7.trans hx21_6)
  have hx22_8 := (cs_x22 hcs8).trans (hx22_7.trans hx22_6)
  wp_apply_pre (step_loop_ark3 hc.loop_ark3 (by rw [hpc8]; bv_off) hrun8 hanc8.sp hsp_loc
    (rk3Ptr := rkBase + 0x080#64) (by rw [hx21_8]; bv_off) ?_)
  intro s9 hpc9 hrun9 hfr9 hx0_9 hx21_9 hx22_9; have hanc9 := hanc8.step_frame hfr9
  wp_apply_pre (call_sub_bytes hc.bl_sb_r4 hcallees.subBytes (by rw [hpc9]; bv_off) hrun9
    hanc9.sp (spAligned_of_eq hanc9.sp hsp_loc) hx0_9 ?_)
  intro s10 hpc10 hrun10 hsp10 hcs10 hp10; have hanc10 := hanc9.step_call hsp10 hcs10 hp10
  have hx21_10 : s10.readReg64 (.gpr 21#5) = (rkBase + 0x0c0#64) - 0x060#64 := by
    rw [cs_x21 hcs10, hx21_9]; bv_off
  have hx22_10 := (cs_x22 hcs10).trans (hx22_9.trans hx22_8)
  wp_apply_pre (step_mc0_head hc.mc0_head (by rw [hpc10]; bv_off) hrun10 hanc10.sp hsp_loc hx21_10 ?_)
  intro s11 hpc11 hrun11 hfr11 hx21_11 hx22_11 hmid0; have hanc11 := hanc10.step_frame hfr11
  wp_apply_pre (step_mc0_tail hc.mc0_tail (by rw [hpc11]; bv_off) hrun11 hanc11.sp hsp_loc
    hx21_11 hmid0 ?_)
  intro s12 hpc12 hrun12 hfr12 hx0_12 hx21_12 hx22_12; have hanc12 := hanc11.step_frame hfr12
  wp_apply_pre (call_sub_bytes hc.bl_sb_r5 hcallees.subBytes (by rw [hpc12]; bv_off) hrun12
    hanc12.sp (spAligned_of_eq hanc12.sp hsp_loc) hx0_12 ?_)
  intro s13 hpc13 hrun13 hsp13 hcs13 hp13; have hanc13 := hanc12.step_call hsp13 hcs13 hp13
  have hx21_13 : s13.readReg64 (.gpr 21#5) = rkBase + 0x060#64 := by
    rw [cs_x21 hcs13, hx21_12]; bv_off
  have hx22_13 := (cs_x22 hcs13).trans (hx22_12.trans hx22_11 |>.trans hx22_10)
  refine step_mov_x0_sp hc.mov_mc1_loop (by rw [hpc13]; bv_off) hrun13 hanc13.sp
    fun s14 hpc14 hrun14 hfr14 hx0_14 hx21_14 hx22_14 => ?_
  have hanc14 := hanc13.step_frame hfr14
  wp_apply_pre (call_mix_columns_32 Model.mixColumns1 hc.bl_mc1_loop hcallees.mixColumns1
    (by rw [hpc14]; bv_off) hrun14 hanc14.sp (spAligned_of_eq hanc14.sp hsp_loc) hx0_14 rfl ?_)
  intro s15 hpc15 hrun15 hsp15 hcs15 hp15; have hanc15 := hanc14.step_call hsp15 hcs15 hp15
  have hx21_15 : s15.readReg64 (.gpr 21#5) = rkBase + 0x060#64 :=
    (cs_x21 hcs15).trans (hx21_14.trans hx21_13)
  have hx22_15 : s15.readReg64 (.gpr 22#5) = cnt := (cs_x22 hcs15).trans (hx22_14.trans hx22_13)
  have hpc15' : s15.pc = fnAddr + 0x3a8#64 := by rw [hpc15]; bv_off
  have_instrs hc.loop_back 0 3; wp_steps 3
  exact SepWP.weaken_pre (Entails.of_eq_explicit (by sep_ac_rfl))
    (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun15])
      (hanc15.step_frame ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl⟩)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))

/-! ## 7. Top-Level `aes256Encrypt_ok` Proof -/

attribute [local irreducible]
  Model.bitslice addRoundKeyFs Model.subBytesFs Model.mixColumns1
  encLoop4Rounds shiftRows2 Model.invBitslice Model.aes256EncryptFs

/-- Placement-generic `subroutine_ok` verification of `fixslice64::aes256_encrypt`. -/
theorem aes256Encrypt_ok {P : Program}
    {fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr invBitsliceAddr : BitVec 64}
    (hc : hasInstrs P fnAddr
      (aes256EncryptInstrs fnAddr bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr
        invBitsliceAddr))
    (hcallees : Aes256EncryptCallees P bitsliceAddr subBytesAddr mixColumns1Addr mixColumns3Addr
      invBitsliceAddr) :
    subroutine_ok P fnAddr aes256EncryptSpec := by
  have hcode := EncCode.of_hasInstrs hc
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ro, outPtr, keysPtr, inPtr, ks, bs⟩ R s0 hpc hrun hpre hsp
  dsimp only [aes256EncryptSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx1, hx8, hwf⟩, hpre⟩
  refine ⟨fsKeys256At keysPtr ks ∗ bytesAt ro inPtr (blocks4Bytes bs) ∗
    memRegion outPtr 64 ∗ stackFrameAt s0.sp 208, hpre, ?_⟩
  have hsp_loc := sp_sub128_and_15 (sp_and_15_of_spAligned hsp)
  wp_conv_pre =>
    rw [stackFrameAt_208_eq s0.sp, stackFrameAt_64_cells s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7
  wp_apply_pre (step_prolog hcode.prolog hpc hrun hsp hx0 hx1 hx8 ?_)
  intro s1 hpc1 hrun1 hanc1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1
  wp_apply_pre (call_bitslice hcode.bl_bitslice hcallees.bitslice hpc1 hrun1
    hanc1.sp (spAligned_of_eq hanc1.sp hsp_loc) hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hwf ?_)
  intro s2 hpc2 hrun2 hsp2 hcs2 hp2; have hanc2 := hanc1.step_call hsp2 hcs2 hp2
  wp_conv_pre => rw [fsKeys256At_quads keysPtr ks]
  wp_apply_pre (step_rk0 hcode.rk0 (by rw [hpc2]; bv_off) hrun2 hanc2.sp hsp_loc hanc2.x20 ?_)
  intro s3 hpc3 hrun3 hfr3 hx0_3; have hanc3 := hanc2.step_frame hfr3
  wp_apply_pre (call_sub_bytes hcode.bl_sb0 hcallees.subBytes (by rw [hpc3]; bv_off) hrun3
    hanc3.sp (spAligned_of_eq hanc3.sp hsp_loc) hx0_3 ?_)
  intro s4 hpc4 hrun4 hsp4 hcs4 hp4; have hanc4 := hanc3.step_call hsp4 hcs4 hp4
  refine step_mov_x0_sp hcode.mov_mc1_0 (by rw [hpc4]; bv_off) hrun4 hanc4.sp
    fun s5 hpc5 hrun5 hfr5 hx0_5 _ _ => ?_
  have hanc5 := hanc4.step_frame hfr5
  wp_apply_pre (call_mix_columns_32 Model.mixColumns1 hcode.bl_mc1_0 hcallees.mixColumns1
    (by rw [hpc5]; bv_off) hrun5 hanc5.sp (spAligned_of_eq hanc5.sp hsp_loc) hx0_5 rfl ?_)
  intro s6 hpc6 hrun6 hsp6 hcs6 hp6; have hanc6 := hanc5.step_call hsp6 hcs6 hp6
  have hpc6' : s6.pc = fnAddr + 0x094#64 := by rw [hpc6]; bv_off
  have hx20_6 : s6.readReg64 (.gpr 20#5) = keysPtr := hanc6.x20
  have_instrs hcode.loop_init 0 2; wp_steps 2
  wp_apply_pre (step_loop_iter hcode hcallees (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun6]) hsp_loc
    (hanc6.step_frame ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl⟩)
    (rkBase := keysPtr + 0x040#64) (cnt := 96#64)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm]) (by decide) ?_)
  intro s7 hpc7 hrun7 hanc7 hx21_7 hx22_7
  wp_apply_pre (step_loop_iter hcode hcallees hpc7 hrun7 hsp_loc hanc7 (rkBase := keysPtr + 0x140#64)
    (cnt := 64#64) (by rw [hx21_7]; bv_off) (by rw [hx22_7]; rfl) (by decide) ?_)
  intro s8 hpc8 hrun8 hanc8 hx21_8 hx22_8
  wp_apply_pre (step_loop_iter hcode hcallees hpc8 hrun8 hsp_loc hanc8 (rkBase := keysPtr + 0x240#64)
    (cnt := 32#64) (by rw [hx21_8]; bv_off) (by rw [hx22_8]; rfl) (by decide) ?_)
  intro s9 hpc9 hrun9 hanc9 hx21_9 hx22_9
  wp_apply_pre (step_loop_ark1 hcode.loop_ark1 hpc9 hrun9 hanc9.sp hsp_loc
    (rk1Ptr := keysPtr + 0x340#64) (by rw [hx21_9]; bv_off) ?_)
  intro s10 hpc10 hrun10 hfr10 _ hx22_10 hlive10; have hanc10 := hanc9.step_frame hfr10
  refine step_cbz_eq hcode.loop_cbz_mov (by rw [hpc10]; bv_off) hrun10
    (by rw [hx22_10, hx22_9]; rfl) hlive10 fun s11 hpc11 hrun11 hfr11 hlive11 => ?_
  have hanc11 := hanc10.step_frame hfr11
  wp_apply_pre (step_exit_sr2 hcode.exit_sr2 hpc11 hrun11 hanc11.sp hsp_loc hlive11 ?_)
  intro s12 hpc12 hrun12 hfr12 hx0_12; have hanc12 := hanc11.step_frame hfr12
  wp_apply_pre (call_sub_bytes hcode.bl_sb_last hcallees.subBytes (by rw [hpc12]; bv_off) hrun12
    hanc12.sp (spAligned_of_eq hanc12.sp hsp_loc) hx0_12 ?_)
  intro s13 hpc13 hrun13 hsp13 hcs13 hp13; have hanc13 := hanc12.step_call hsp13 hcs13 hp13
  wp_apply_pre (step_exit_rk14 hcode.exit_rk14 (by rw [hpc13]; bv_off) hrun13 hanc13.sp hsp_loc
    hanc13.x19 hanc13.x20 ?_)
  intro s14 hpc14 hrun14 hfr14 hx0_14 hx1_14; have hanc14 := hanc13.step_frame hfr14
  wp_apply_pre (call_inv_bitslice hcode.bl_inv_bs hcallees.invBitslice (by rw [hpc14]; bv_off)
    hrun14 hanc14.sp (spAligned_of_eq hanc14.sp hsp_loc) hx0_14 hx1_14 ?_)
  intro s15 hpc15 hrun15 hsp15 hcs15 hp15; have hanc15 := hanc14.step_call hsp15 hcs15 hp15
  wp_conv_pre => rw [aes256EncryptFs_unroll ks bs]
  refine' SepWP.weaken_pre ?_
    (step_epilog hcode.epilog (by rw [hpc15]; bv_off) hrun15 hsp_loc hanc15)
  rw [fsKeys256At_quads keysPtr ks]; sep_frame

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockEnc

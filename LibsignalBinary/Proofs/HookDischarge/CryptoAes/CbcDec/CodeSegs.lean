/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.StdDetect
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code

/-!
# Instruction Segment Decomposition (`CbcDec.CodeSegs`)
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs

open Arm64
open ProofLib.StdStartup (adrpOff decodeWords hasInstrs pageLo12)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (adrpAddPair adrpAddPair_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcPrologueWords cbcPostStorageAdrpWords cbcStorageCheckWords cbcPostSoftKsWords
   cbcFastRejectWords cbcPostInitWords cbcPreInvExpandWords cbcHwCopyEkWords
   cbcSroaCopy960Words cbcSroaCopy952Words cbcSroaStage968Words cbcPreAllocWords
   cbcPostAllocWords cbcLoopDispatchWords cbcBadKeyIvWords cbcRetEpilogueWords
   cbcSoftQuadSetupWords cbcSoftQuadPre1Words cbcSoftQuadPre2Words
   cbcSoftQuadPost1aWords cbcSoftQuadPost1bWords cbcSoftQuadPost2Words
   cbcSoftQuadPost3Words cbcSoftQuadPost4Words cbcSoftQuadPost5Words
   cbcSoftTailSetupWords cbcSoftTailPreWords cbcSoftTailPost1Words cbcSoftTailPost2Words
   cbcUnpadWords cbcErrDeallocArgsWords cbcErrRetPreWords cbcErrRetPostWords
   cbcOkPreDropWords cbcOkRetWords cbcPanic1MidWords cbcSlicePanicMidWords cbcHandleErrPreWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptPanicSyms cbcDecPrologInstrs cbcDecPrologInstrs_length
   cbcDecHwLoopInstrs_length cbcDecPostHwInstrs aes256CbcDecryptInstrs hasInstrs_split)

private theorem length_decodeWords (ws : List (BitVec 32)) :
    (decodeWords ws).length = ws.length := List.length_map _

private theorem hasInstrs_step {P : Program} {fnAddr off off' : BitVec 64} {xs ys : List Instr}
    (h : hasInstrs P (fnAddr + off) (xs ++ ys))
    (hoff : off + BitVec.ofNat 64 (4 * xs.length) = off' := by
      simp only [length_decodeWords, adrpAddPair_length, List.length_cons, List.length_nil]; decide) :
    hasInstrs P (fnAddr + off) xs ∧ hasInstrs P (fnAddr + off') ys := by
  have ⟨h1, h2⟩ := hasInstrs_split h
  exact ⟨h1, by rwa [BitVec.add_assoc, hoff] at h2⟩

/-- Decomposed instruction segments for all non-`HwLoop` slices of `aes_256_cbc_decrypt`. -/
structure CbcDecCodeSegs (P : Program) (fnAddr : BitVec 64) (hw : Aes256DecHwAddrs)
    (keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64)
    (errStr1Relax errStr2Relax : Bool) : Prop where
  prologue          : hasInstrs P (fnAddr + 0x000#64) (decodeWords cbcPrologueWords)
  adrpStorage       : hasInstrs P (fnAddr + 0x040#64) [.adr true (.gpr 19#5) (adrpOff (fnAddr + 0x040#64) hw.storageAddr)]
  postStorageAdrp   : hasInstrs P (fnAddr + 0x044#64) (decodeWords cbcPostStorageAdrpWords)
  ldrbStorage0      : hasInstrs P (fnAddr + 0x048#64) [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 19#5) (pageLo12 hw.storageAddr))]
  storageCheck      : hasInstrs P (fnAddr + 0x04c#64) (decodeWords cbcStorageCheckWords)
  bl_ks             : hasInstrs P (fnAddr + 0x070#64) [.bl (keyScheduleAddr - (fnAddr + 0x070#64))]
  postSoftKs        : hasInstrs P (fnAddr + 0x074#64) (decodeWords cbcPostSoftKsWords)
  errStr1Pair       : hasInstrs P (fnAddr + 0x07c#64) (adrpAddPair (.gpr 10#5) (fnAddr + 0x07c#64) errStr1Addr errStr1Relax)
  fastReject        : hasInstrs P (fnAddr + 0x084#64) (decodeWords cbcFastRejectWords)
  bl_initInner      : hasInstrs P (fnAddr + 0x098#64) [.bl (hw.initInnerAddr - (fnAddr + 0x098#64))]
  postInit          : hasInstrs P (fnAddr + 0x09c#64) (decodeWords cbcPostInitWords)
  bl_expandKey      : hasInstrs P (fnAddr + 0x0ac#64) [.bl (hw.expandKeyAddr - (fnAddr + 0x0ac#64))]
  preInvExpand      : hasInstrs P (fnAddr + 0x0b0#64) (decodeWords cbcPreInvExpandWords)
  bl_invExpand      : hasInstrs P (fnAddr + 0x0bc#64) [.bl (hw.invExpandAddr - (fnAddr + 0x0bc#64))]
  hwCopyEk          : hasInstrs P (fnAddr + 0x0c0#64) (decodeWords cbcHwCopyEkWords)
  bl_memcpy480      : hasInstrs P (fnAddr + 0x13c#64) [.bl (memcpyAddr - (fnAddr + 0x13c#64))]
  sroaCopy960       : hasInstrs P (fnAddr + 0x140#64) (decodeWords cbcSroaCopy960Words)
  bl_memcpy960      : hasInstrs P (fnAddr + 0x154#64) [.bl (memcpyAddr - (fnAddr + 0x154#64))]
  sroaCopy952       : hasInstrs P (fnAddr + 0x158#64) (decodeWords cbcSroaCopy952Words)
  bl_memcpy952      : hasInstrs P (fnAddr + 0x170#64) [.bl (memcpyAddr - (fnAddr + 0x170#64))]
  sroaStage968      : hasInstrs P (fnAddr + 0x174#64) (decodeWords cbcSroaStage968Words)
  bl_memcpyStage968 : hasInstrs P (fnAddr + 0x18c#64) [.bl (memcpyAddr - (fnAddr + 0x18c#64))]
  bl_shim           : hasInstrs P (fnAddr + 0x190#64) [.bl (shimAddr - (fnAddr + 0x190#64))]
  preAlloc          : hasInstrs P (fnAddr + 0x194#64) (decodeWords cbcPreAllocWords)
  bl_alloc          : hasInstrs P (fnAddr + 0x19c#64) [.bl (allocZeroedAddr - (fnAddr + 0x19c#64))]
  postAlloc         : hasInstrs P (fnAddr + 0x1a0#64) (decodeWords cbcPostAllocWords)
  bl_memcpyUnstage  : hasInstrs P (fnAddr + 0x1bc#64) [.bl (memcpyAddr - (fnAddr + 0x1bc#64))]
  ldrbStorage1      : hasInstrs P (fnAddr + 0x1c0#64) [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 19#5) (pageLo12 hw.storageAddr))]
  loopDispatch      : hasInstrs P (fnAddr + 0x1c4#64) (decodeWords cbcLoopDispatchWords)
  retEpilogue       : hasInstrs P (fnAddr + 0x65c#64) (decodeWords cbcRetEpilogueWords)
  softQuadSetup     : hasInstrs P (fnAddr + 0x67c#64) (decodeWords cbcSoftQuadSetupWords)
  softQuadPre1      : hasInstrs P (fnAddr + 0x694#64) (decodeWords cbcSoftQuadPre1Words)
  softQuadPre2      : hasInstrs P (fnAddr + 0x73c#64) (decodeWords cbcSoftQuadPre2Words)
  bl_decQuad        : hasInstrs P (fnAddr + 0x7e8#64) [.bl (decryptAddr - (fnAddr + 0x7e8#64))]
  softQuadPost1a    : hasInstrs P (fnAddr + 0x7ec#64) (decodeWords cbcSoftQuadPost1aWords)
  softQuadPost1b    : hasInstrs P (fnAddr + 0x874#64) (decodeWords cbcSoftQuadPost1bWords)
  softQuadPost2     : hasInstrs P (fnAddr + 0x900#64) (decodeWords cbcSoftQuadPost2Words)
  softQuadPost3     : hasInstrs P (fnAddr + 0x9d4#64) (decodeWords cbcSoftQuadPost3Words)
  softQuadPost4     : hasInstrs P (fnAddr + 0xacc#64) (decodeWords cbcSoftQuadPost4Words)
  softQuadPost5     : hasInstrs P (fnAddr + 0xb9c#64) (decodeWords cbcSoftQuadPost5Words)
  softTailSetup     : hasInstrs P (fnAddr + 0xbc0#64) (decodeWords cbcSoftTailSetupWords)
  softTailPre       : hasInstrs P (fnAddr + 0xbe4#64) (decodeWords cbcSoftTailPreWords)
  bl_decTail        : hasInstrs P (fnAddr + 0xc04#64) [.bl (decryptAddr - (fnAddr + 0xc04#64))]
  softTailPost1     : hasInstrs P (fnAddr + 0xc08#64) (decodeWords cbcSoftTailPost1Words)
  softTailPost2     : hasInstrs P (fnAddr + 0xc94#64) (decodeWords cbcSoftTailPost2Words)
  unpad             : hasInstrs P (fnAddr + 0xd20#64) (decodeWords cbcUnpadWords)
  bl_dropErr        : hasInstrs P (fnAddr + 0xd64#64) [.bl (hw.dropDecryptorAddr - (fnAddr + 0xd64#64))]
  errDeallocArgs    : hasInstrs P (fnAddr + 0xd68#64) (decodeWords cbcErrDeallocArgsWords)
  bl_dealloc        : hasInstrs P (fnAddr + 0xd74#64) [.bl (deallocAddr - (fnAddr + 0xd74#64))]
  errRetPre         : hasInstrs P (fnAddr + 0xd78#64) (decodeWords cbcErrRetPreWords)
  errStr2Pair       : hasInstrs P (fnAddr + 0xd80#64) (adrpAddPair (.gpr 9#5) (fnAddr + 0xd80#64) errStr2Addr errStr2Relax)
  errRetPost        : hasInstrs P (fnAddr + 0xd88#64) (decodeWords cbcErrRetPostWords)
  okPreDrop         : hasInstrs P (fnAddr + 0xd98#64) (decodeWords cbcOkPreDropWords)
  bl_dropOk         : hasInstrs P (fnAddr + 0xda8#64) [.bl (hw.dropDecryptorAddr - (fnAddr + 0xda8#64))]
  okRet             : hasInstrs P (fnAddr + 0xdac#64) (decodeWords cbcOkRetWords)
  handleErrPre      : hasInstrs P (fnAddr + 0xdf8#64) (decodeWords cbcHandleErrPreWords)
  bl_handleErr      : hasInstrs P (fnAddr + 0xe00#64) [.bl (handleErrorAddr - (fnAddr + 0xe00#64))]

theorem CbcDecCodeSegs.of_hasInstrs {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
    {panics : Aes256CbcDecryptPanicSyms} {errStr1Relax errStr2Relax : Bool}
    (hc : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax)) :
    CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr
      memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax := by
  unfold aes256CbcDecryptInstrs at hc
  rw [List.append_assoc] at hc
  obtain ⟨hp0, hrest⟩ := hasInstrs_split hc
  rw [cbcDecPrologInstrs_length] at hrest
  obtain ⟨_, hpost0⟩ := hasInstrs_split hrest
  rw [cbcDecHwLoopInstrs_length, BitVec.add_assoc,
      show (0x1d4#64 : BitVec 64) + BitVec.ofNat 64 (4 * 266) = 0x5fc#64 from by decide] at hpost0
  have hp : hasInstrs P (fnAddr + 0x000#64)
      (cbcDecPrologInstrs fnAddr hw keyScheduleAddr shimAddr allocZeroedAddr
        memcpyAddr errStr1Addr errStr1Relax) := by
    simpa only [BitVec.add_zero] using hp0
  dsimp only [cbcDecPrologInstrs, List.flatten] at hp
  have h1 := hasInstrs_step (off' := 0x040#64) hp
  have h2 := hasInstrs_step (xs := [_]) (off' := 0x044#64) h1.2
  have h3 := hasInstrs_step (off' := 0x048#64) h2.2
  have h4 := hasInstrs_step (xs := [_]) (off' := 0x04c#64) h3.2
  have h5 := hasInstrs_step (off' := 0x070#64) h4.2
  have h6 := hasInstrs_step (xs := [_]) (off' := 0x074#64) h5.2
  have h7 := hasInstrs_step (off' := 0x07c#64) h6.2
  have h8 := hasInstrs_step (off' := 0x084#64) h7.2
  have h9 := hasInstrs_step (off' := 0x098#64) h8.2
  have h10 := hasInstrs_step (xs := [_]) (off' := 0x09c#64) h9.2
  have h11 := hasInstrs_step (off' := 0x0ac#64) h10.2
  have h12 := hasInstrs_step (xs := [_]) (off' := 0x0b0#64) h11.2
  have h13 := hasInstrs_step (off' := 0x0bc#64) h12.2
  have h14 := hasInstrs_step (xs := [_]) (off' := 0x0c0#64) h13.2
  have h15 := hasInstrs_step (off' := 0x13c#64) h14.2
  have h16 := hasInstrs_step (xs := [_]) (off' := 0x140#64) h15.2
  have h17 := hasInstrs_step (off' := 0x154#64) h16.2
  have h18 := hasInstrs_step (xs := [_]) (off' := 0x158#64) h17.2
  have h19 := hasInstrs_step (off' := 0x170#64) h18.2
  have h20 := hasInstrs_step (xs := [_]) (off' := 0x174#64) h19.2
  have h21 := hasInstrs_step (off' := 0x18c#64) h20.2
  have h22 := hasInstrs_step (xs := [_]) (off' := 0x190#64) h21.2
  have h23 := hasInstrs_step (xs := [_]) (off' := 0x194#64) h22.2
  have h24 := hasInstrs_step (off' := 0x19c#64) h23.2
  have h25 := hasInstrs_step (xs := [_]) (off' := 0x1a0#64) h24.2
  have h26 := hasInstrs_step (off' := 0x1bc#64) h25.2
  have h27 := hasInstrs_step (xs := [_]) (off' := 0x1c0#64) h26.2
  have h28 := hasInstrs_step (xs := [_]) (off' := 0x1c4#64) h27.2
  have h29 := (hasInstrs_step (off' := 0x1d4#64) h28.2).1
  dsimp only [cbcDecPostHwInstrs, List.flatten] at hpost0
  have q1 := hasInstrs_step (xs := [_]) (off' := 0x600#64) hpost0
  have q2 := hasInstrs_step (off' := 0x65c#64) q1.2
  have q3 := hasInstrs_step (off' := 0x67c#64) q2.2
  have q4 := hasInstrs_step (off' := 0x694#64) q3.2
  have q5 := hasInstrs_step (off' := 0x73c#64) q4.2
  have q6 := hasInstrs_step (off' := 0x7e8#64) q5.2
  have q7 := hasInstrs_step (xs := [_]) (off' := 0x7ec#64) q6.2
  have q8 := hasInstrs_step (off' := 0x874#64) q7.2
  have q9 := hasInstrs_step (off' := 0x900#64) q8.2
  have q10 := hasInstrs_step (off' := 0x9d4#64) q9.2
  have q11 := hasInstrs_step (off' := 0xacc#64) q10.2
  have q12 := hasInstrs_step (off' := 0xb9c#64) q11.2
  have q13 := hasInstrs_step (off' := 0xbc0#64) q12.2
  have q14 := hasInstrs_step (off' := 0xbe4#64) q13.2
  have q15 := hasInstrs_step (off' := 0xc04#64) q14.2
  have q16 := hasInstrs_step (xs := [_]) (off' := 0xc08#64) q15.2
  have q17 := hasInstrs_step (off' := 0xc94#64) q16.2
  have q18 := hasInstrs_step (off' := 0xd20#64) q17.2
  have q19 := hasInstrs_step (off' := 0xd64#64) q18.2
  have q20 := hasInstrs_step (xs := [_]) (off' := 0xd68#64) q19.2
  have q21 := hasInstrs_step (off' := 0xd74#64) q20.2
  have q22 := hasInstrs_step (xs := [_]) (off' := 0xd78#64) q21.2
  have q23 := hasInstrs_step (off' := 0xd80#64) q22.2
  have q24 := hasInstrs_step (off' := 0xd88#64) q23.2
  have q25 := hasInstrs_step (off' := 0xd98#64) q24.2
  have q26 := hasInstrs_step (off' := 0xda8#64) q25.2
  have q27 := hasInstrs_step (xs := [_]) (off' := 0xdac#64) q26.2
  have q28 := hasInstrs_step (off' := 0xdbc#64) q27.2
  have q29 := hasInstrs_step (off' := 0xdc4#64) q28.2
  have q30 := hasInstrs_step (off' := 0xdcc#64) q29.2
  have q31 := hasInstrs_step (off' := 0xdd0#64) q30.2
  have q32 := hasInstrs_step (xs := [_]) (off' := 0xdd4#64) q31.2
  have q33 := hasInstrs_step (off' := 0xddc#64) q32.2
  have q34 := hasInstrs_step (off' := 0xde8#64) q33.2
  have q35 := hasInstrs_step (xs := [_]) (off' := 0xdec#64) q34.2
  have q36 := hasInstrs_step (off' := 0xdf4#64) q35.2
  have q37 := hasInstrs_step (xs := [_]) (off' := 0xdf8#64) q36.2
  have q38 := hasInstrs_step (off' := 0xe00#64) q37.2
  have q39 := hasInstrs_step (xs := [_]) (off' := 0xe04#64) q38.2
  exact ⟨h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1, h8.1, h9.1, h10.1, h11.1, h12.1, h13.1,
    h14.1, h15.1, h16.1, h17.1, h18.1, h19.1, h20.1, h21.1, h22.1, h23.1, h24.1, h25.1,
    h26.1, h27.1, h28.1, h29, q3.1, q4.1, q5.1, q6.1, q7.1, q8.1, q9.1, q10.1, q11.1,
    q12.1, q13.1, q14.1, q15.1, q16.1, q17.1, q18.1, q19.1, q20.1, q21.1, q22.1, q23.1,
    q24.1, q25.1, q26.1, q27.1, q28.1, q38.1, q39.1⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs

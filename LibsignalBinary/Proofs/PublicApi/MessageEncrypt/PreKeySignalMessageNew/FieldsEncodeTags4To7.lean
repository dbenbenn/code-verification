/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4 -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `PreKeySignalMessage::new` Field Encoding: Tags 4–7

Symbolic execution steps for protobuf tags 4 (`message`), 5 (`registration_id`),
6 (`signed_pre_key_id`), and 7 (`kyber_pre_key_id`) (`+0x35c..+0x450`).
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

set_option maxHeartbeats 400000

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open scoped EncodeVarintNorm

/-! ## Tag 4 (`message`, `+0x35c..+0x3b8`) -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?

theorem step_preKeyMsg_tag4_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 860#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 952#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hvar_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hmsg_lt : x.msg.serialized.length < 2 ^ 64 := by
    have : x.msg.serialized.length ≤ (serPrefix4 x).length := by
      simp [serPrefix4, LibsignalSessionApi.Prost.bytesField]; omega
    omega
  have hser4 : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)) ++
      x.msg.serialized = serPrefix4 x := by
    rw [serPrefix4, prost_bytesField_some 4 x.msg.serialized hmsg_lt, prost_key_4_2]
    simp only [← List.append_assoc, List.singleton_append]
  have h4_len : (serPrefix4 x).length = (serPrefix3 x).length + 1 +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length + x.msg.serialized.length := by
    rw [← hser4, List.length_append, List.length_append, List.length_cons]; omega
  have hlt3 : (serPrefix3 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq3 := cap_beq_len_false hlt3
  have hle_var : (serPrefix3 x ++ [34#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hle_slice : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
      x.msg.serialized.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) hlt3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) 34#8 hlt3,
    bv_len_add_one (serPrefix3 x) 34#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    (BitVec.ofNat 64 x.msg.serialized.length) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 900#64) (serPrefix3 x ++ [34#8]) s_base s hle_var (by omega)
    (F := (sp ↦₆₄ g.msgCopyPtr) ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx27_1 : sf1.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  by_cases hmsg_nil : x.msg.serialized = []
  · have hser4_nil : serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length) = serPrefix4 x := by
      simpa [hmsg_nil] using hser4
    have hmsg_bv0 : BitVec.ofNat 64 x.msg.serialized.length = 0#64 := by simp [hmsg_nil]
    clear hmsg_nil h4_len hser4
    rw [hser4_nil] at hult1 hule1 ⊢
    rw [hmsg_bv0] at hx27_1 hult1 hule1
    apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 952#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclf2
    have hpost_nil :
        (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
        ((sp ↦₆₄ g.msgCopyPtr) ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F) =
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
    rw [hpost_nil]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf2
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
  · have hmsg_pos : 0 < x.msg.serialized.length := List.length_pos_of_ne_nil hmsg_nil
    have hmsg_beq := bv_len_beq_zero_false hmsg_pos hmsg_lt
    have hmsg_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmsg_lt]
    rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
      x.msg.serialized.length hle_slice hcap_pos,
      boxU8Buf_nonempty_eq A g.msgCopyPtr x.msg.serialized hmsg_nil]
    apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ "memcpy"); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclf1'
    refine step_call_memcpy_placed hmemcpy
      (g.serPtr + BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      g.msgCopyPtr sp ((blkPl_41).base + 944#64)
      (BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      (BitVec.ofNat 64 x.model.serialized.length)
      x.msg.serialized s_base.trace s
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄
          BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
          x.msg.serialized.length ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack ∗
        (⌜g.msgCopyPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63⌝ ∗
          A.live g.msgCopyPtr x.msg.serialized.length 1) ∗ F)
      hclf1' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign1)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)
      fun sf2 hpcf2 hrunf2 hspf2 htrf2 hclf2 hregs2 hx23_2 hx26_2 => ?_
    have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx27_2 : sf2.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
    simp only [arm64_norm] at hx23_2 hx27_2
    have hadd_len :
        BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
          BitVec.ofNat 64 x.msg.serialized.length =
        BitVec.ofNat 64 (serPrefix4 x).length := by
      simp only [h4_len, List.length_append, List.length_cons, BitVec.ofNat_add]
      ac_rfl
    clear h4_len
    have hpost_eq :
        (((g.serPtr + BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ↦ₛ
            x.msg.serialized) ∗
          (g.msgCopyPtr ↦ₛ x.msg.serialized)) ∗
        ((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
          vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
            x.msg.serialized.length ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack ∗
          (⌜g.msgCopyPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63⌝ ∗
            A.live g.msgCopyPtr x.msg.serialized.length 1) ∗ F) =
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
      rw [← hser4,
        ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
          x.msg.serialized hcap_pos,
        boxU8Buf_nonempty_eq A g.msgCopyPtr x.msg.serialized hmsg_nil]
      ac_rfl
    rw [hpost_eq]
    apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 952#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclf3
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag5_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 952#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1004#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length →
      sm.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 24#64) ↦₃₂ x.regId) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hvar_pos : 1 ≤ (encodeVarint (x.regId.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser5 : (serPrefix4 x ++ [40#8]) ++ encodeVarint (x.regId.zeroExtend 64) = serPrefix5 x := by
    simp [serPrefix5, prost_uint32Field_some, prost_key_5_0, List.append_assoc]
  have h5_len : (serPrefix5 x).length = (serPrefix4 x).length + 1 +
      (encodeVarint (x.regId.zeroExtend 64)).length := by
    rw [← hser5, List.length_append, List.length_append, List.length_singleton]
  have hlt4 : (serPrefix4 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq4 := cap_beq_len_false hlt4
  have hle_var : (serPrefix4 x ++ [40#8]).length +
      (encodeVarint (x.regId.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) hlt4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) 40#8 hlt4,
    bv_len_add_one (serPrefix4 x) 40#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    (x.regId.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 996#64) (serPrefix4 x ++ [40#8]) s_base s hle_var (by omega)
    (F := ((sp + 24#64) ↦₃₂ x.regId) ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  rw [hser5]
  have hpost_eq :
      (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
      (((sp + 24#64) ↦₃₂ x.regId) ∗ F) =
      ((((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
  rw [hpost_eq]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 1004#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclf2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf2
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag6_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1004#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length)
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1044#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hw21 : s.readReg32 .x21 = x.spk := by simpa [State.readReg32] using hx21
  have hvar_pos : 1 ≤ (encodeVarint (x.spk.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser6 : (serPrefix5 x ++ [48#8]) ++ encodeVarint (x.spk.zeroExtend 64) = serPrefix6 x := by
    simp [serPrefix6, prost_uint32Field_some, prost_key_6_0, List.append_assoc]
  have h6_len : (serPrefix6 x).length = (serPrefix5 x).length + 1 +
      (encodeVarint (x.spk.zeroExtend 64)).length := by
    rw [← hser6, List.length_append, List.length_append, List.length_singleton]
  have hlt5 : (serPrefix5 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq5 := cap_beq_len_false hlt5
  have hle_var : (serPrefix5 x ++ [48#8]).length +
      (encodeVarint (x.spk.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) hlt5]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) 48#8 hlt5,
    bv_len_add_one (serPrefix5 x) 48#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    (x.spk.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 1044#64) (serPrefix5 x ++ [48#8]) s_base s hle_var (by omega)
    (F := F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  rw [hser6]
  exact hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1

theorem step_preKeyMsg_tag7_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1044#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hP : P = (((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1104#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _, _, hkp_val⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hkp : x.kp with
  | none =>
    have hser7 : serPrefix7 x = serPrefix6 x := by
      simp [serPrefix7, hkp, LibsignalSessionApi.Prost.uint32Field]
    simp only [hkp, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hnext ⊢
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 1104#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [← hser7]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some k =>
    have hkid : g.kyberId32 = k.preKeyId := hkp_val k hkp
    have hser7 : (serPrefix6 x ++ [56#8]) ++ encodeVarint (k.preKeyId.zeroExtend 64) = serPrefix7 x := by
      simp [serPrefix7, hkp, prost_uint32Field_some, prost_key_7_0, List.append_assoc]
    have h7_len : (serPrefix7 x).length = (serPrefix6 x).length + 1 +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      rw [← hser7, List.length_append, List.length_append, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt6 : (serPrefix6 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq6 := cap_beq_len_false hlt6
    have hle_var : (serPrefix6 x ++ [56#8]).length +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_singleton]; omega
    simp only [hkp, Option.isSome, ↓reduceIte] at hnext ⊢
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) hlt6]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
    intro hcl0
    rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) 56#8 hlt6,
      bv_len_add_one (serPrefix6 x) 56#8]
    refine step_call_encVarint_placed hshim halloc hrealloc hpanic
      (k.preKeyId.zeroExtend 64) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 1104#64) (serPrefix6 x ++ [56#8]) s_base s hle_var (by omega)
      (F := ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ 1#32) ∗ F) hcl0
      (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    rw [hser7]
    have hpost_eq :
        (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
        (((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ 1#32) ∗ F) =
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ 1#32) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
    rw [hpost_eq]
    exact hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1

end Placed

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

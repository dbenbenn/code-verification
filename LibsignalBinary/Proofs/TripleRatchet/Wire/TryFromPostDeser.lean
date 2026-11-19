/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp

/-!
# `PublicKey::deserialize` error/ok paths (`+0x4c4..+0x63c`), `PublicKey` non-aligned copy layout, `counter` and `ciphertext = none` paths
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``RustAlloc.live, #[1]), (``stackAt, #[0]), (``vecHeader, #[0]), (``vecU8Buf, #[1, 2]), (``optU32At, #[0]), (``speAt, #[2]), (``errResultAt, #[3]), (``signalMessageResultAt, #[2]), (``deserializeResult33At, #[0])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

private theorem frame_post {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P' F R Q : SepProp} {S : State → Prop}
    (h : SepWPp prog ret s P' (fun sf Pf => S sf ∧ (Pf ⊢ R)) (tryFromQp s0))
    (hpre : P ⊢ P' ∗ F := by bi_frame)
    (hpost : R ∗ F ⊢ Q := by first | sep_interval | bi_entail) :
    SepWPp prog ret s P (fun sf Pf => S sf ∧ (Pf ⊢ Q)) (tryFromQp s0) :=
  SepWPp.mono_pre hpre
    (SepWPp.frame_tryFrom h fun _ _ ⟨hs, hr⟩ =>
      ⟨hs, Entails.trans (sepConj_mono_left hr) hpost⟩)

private theorem trans_sub {P Sub Out F Q : SepProp} (hsub : Sub ⊢ Out)
    (hpre : P ⊢ Sub ∗ F := by bi_frame)
    (hpost : Out ∗ F ⊢ Q := by first | sep_interval | bi_entail) : P ⊢ Q :=
  Entails.trans hpre (Entails.trans (sepConj_mono_left hsub) hpost)

theorem optU32At_entails_cells (a : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At a opt ⊢
      ∃∗ tag : BitVec 32, ∃∗ val : BitVec 32, (a ↦₃₂ tag) ∗ ((a + 4#64) ↦₃₂ val) := by
  cases opt <;> (dsimp only [optU32At]; sep_interval)

theorem spe_noKeyType_intro (A : RustAlloc) (x19 w2 : BitVec 64)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error .noKeyTypeIdentifier) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 7) ∗
      ((x19 + 16#64) ↦₆₄ w2) ∗ memRegion (x19 + 24#64) 96 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  simp only [signalMessageResultAt, errResultAt, speAt, Nat.reduceSub]
  sep_interval

theorem pointsTo64_zext8_entails_byte_region7 (a : BitVec 64) (t : BitVec 8) :
    (a ↦₆₄ t.zeroExtend 64) ⊢ (a ↦₈ t) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes]
  dsimp only [unpack64]
  rw [pointsToBytes_cons]
  have hb0 : (t.zeroExtend 64).extractLsb' 0 8 = t := by bv_kernel
  rw [hb0]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (a + 1#64) _)

theorem spe_badKeyType_intro (A : RustAlloc) (x19 : BitVec 64) (t : BitVec 8)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error (.badKeyType t)) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 8) ∗
      ((x19 + 16#64) ↦₆₄ t.zeroExtend 64) ∗ memRegion (x19 + 24#64) 96 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  simp only [signalMessageResultAt, errResultAt, speAt, Nat.reduceSub]
  exact trans_sub (pointsTo64_zext8_entails_byte_region7 (x19 + 16#64) t) (hpost := by sep_interval)

theorem spe_badKeyLength_intro (A : RustAlloc) (x19 : BitVec 64) (n : Nat)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error (.badKeyLength n)) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 9) ∗
      ((x19 + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (x19 + 24#64) 96 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  simp only [signalMessageResultAt, errResultAt, speAt, Nat.reduceSub]
  sep_interval

theorem memRegion33_of_err_base (sret : BitVec 64) (b8 : BitVec 8) :
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ b8) ∗ memRegion (sret + 9#64) 24 ⊢
      memRegion sret 33 := by
  sep_interval

theorem memRegion33_of_err_badKeyType (sret : BitVec 64) (t : BitVec 8) :
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 1#8) ∗ ((sret + 9#64) ↦₈ t) ∗ memRegion (sret + 10#64) 23 ⊢
      memRegion sret 33 := by
  sep_interval

theorem memRegion33_of_err_badKeyLength (sret : BitVec 64) (n : Nat) :
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 2#8) ∗ memRegion (sret + 9#64) 7 ∗
      ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (sret + 24#64) 9 ⊢
      memRegion sret 33 := by
  sep_interval

@[local simp, local arm64_norm, local wp_norm]
theorem bv_reconstruct_low8 (w : BitVec 64) :
    (w &&& 0xffffffffffffff00#64) ||| (w &&& 0xff#64) = w := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem bv_reconstruct_low8_dec (w : BitVec 64) :
    (w &&& -256#64) ||| (w &&& 255#64) = w := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem bv_zext8_mask (t : BitVec 8) :
    0#64 ||| ((t.zeroExtend 32).zeroExtend 64 &&& 0xff#64) = t.zeroExtend 64 := by bv_kernel

section DeserOpaqueAtoms

theorem post_rk_none_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {m' : ProtoSignalMessage} (hrk : m'.ratchetKey = none)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error .invalidProtobufEncoding)
    (hst : LoopExitStatePlaced s0 sp' x19 x20 x21 x23 s)
    (hpc : s.pc = (blkPl_85).base + 0x3b0#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (wireSignalMessageOf A (sp' + 176#64) m' ∗
        memRegion (sp' + 88#64) 16 ∗
        memRegion x19 120 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx19 : s.readReg64 .x19 = x19 := hregs.x19_eq
  have hx26 : s.readReg64 .x26 = speWord 2 := hregs.x26
  unfold wireSignalMessageOf
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun g => ?_
  unfold wireSignalMessageAt
  rw [hrk]
  have hent_rk : optVecU8At A g.rk (sp' + 176#64) none ⊢
      ∃∗ rkLen : BitVec 64, ∃∗ rkPtr : BitVec 64,
        vecHeader (sp' + 176#64) noneCap rkPtr rkLen := by
    dsimp only [optVecU8At, vecHeader]; sep_interval
  have hent_wire :
      optVecU8At A g.rk (sp' + 176#64) none ∗
      optVecU8At A g.ct (sp' + 176#64 + 0x18#64) m'.ciphertext ∗
      optVecU8At A g.pq (sp' + 176#64 + 0x30#64) m'.pqRatchet ∗
      optVecU8At A g.addr (sp' + 176#64 + 0x48#64) m'.addresses ∗
      optU32At (sp' + 176#64 + 0x60#64) m'.counter ∗
      optU32At (sp' + 176#64 + 0x68#64) m'.previousCounter ⊢
      (∃∗ rkLen, ∃∗ rkPtr, vecHeader (sp' + 176#64) noneCap rkPtr rkLen) ∗
      (∃∗ ctCap, ∃∗ ctPtr, ∃∗ ctLen, ∃∗ ctAct,
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗ deallocSlot A ctCap ctPtr ctAct) ∗
      (∃∗ pqCap, ∃∗ pqPtr, ∃∗ pqLen, ∃∗ pqAct,
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗ deallocSlot A pqCap pqPtr pqAct) ∗
      (∃∗ adCap, ∃∗ adPtr, ∃∗ adLen, ∃∗ adAct,
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗ deallocSlot A adCap adPtr adAct) ∗
      (∃∗ cTag, ∃∗ cVal, ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal)) ∗
      (∃∗ pcTag, ∃∗ pcVal, ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono hent_rk
      (sepConj_mono (optVecU8At_entails_header_dealloc A g.ct (sp' + 200#64) m'.ciphertext)
        (sepConj_mono (optVecU8At_entails_header_dealloc A g.pq (sp' + 224#64) m'.pqRatchet)
          (sepConj_mono (optVecU8At_entails_header_dealloc A g.addr (sp' + 248#64) m'.addresses)
            (sepConj_mono (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_cells (sp' + 272#64) m'.counter)
              (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_cells (sp' + 280#64) m'.previousCounter)))))
  refine SepWPp.mono_pre (sepConj_mono hent_wire
    (sepConj_mono (memRegion16_split8_8 (sp' + 88#64))
      (sepConj_mono_left (memRegion120_split16 x19)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 =>
    SepWPp.exists_pre fun s96 => SepWPp.exists_pre fun s88 =>
    SepWPp.exists_pre fun pcTag => SepWPp.exists_pre fun pcVal =>
    SepWPp.exists_pre fun cTag => SepWPp.exists_pre fun cVal =>
    SepWPp.exists_pre fun adCap => SepWPp.exists_pre fun adPtr =>
    SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun adAct =>
    SepWPp.exists_pre fun pqCap => SepWPp.exists_pre fun pqPtr =>
    SepWPp.exists_pre fun pqLen => SepWPp.exists_pre fun pqAct =>
    SepWPp.exists_pre fun ctCap => SepWPp.exists_pre fun ctPtr =>
    SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun ctAct =>
    SepWPp.exists_pre fun rkLen => SepWPp.exists_pre fun rkPtr => ?_
  have hvh :
      vecHeader (sp' + 176#64) noneCap rkPtr rkLen =
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∧
      vecHeader (sp' + 176#64) (speWord 2) rkPtr rkLen =
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∧
      vecHeader (sp' + 200#64) ctCap ctPtr ctLen =
        ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∧
      vecHeader (sp' + 224#64) pqCap pqPtr pqLen =
        ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∧
      vecHeader (sp' + 248#64) adCap adPtr adLen =
        ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) := by
    simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, and_self]
  rcases hvh with ⟨hvh1, _, hvh2, hvh3, hvh4⟩
  rw [hvh1, hvh2, hvh3, hvh4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1612)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have hnext := fun {s} => @cleanup_64c_wp_placed _ A H hS s0 s sp' ctCap ctPtr pqCap pqPtr adCap adPtr
  have hspe := spe_invalidProto_intro A x19 herr
  generalize skipFieldStackX 100 = nStk, signalMessageResultAt A [] x19 out = resOut at hnext hspe ⊢
  exact frame_post
    (hnext ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
    (hpre := by bi_frame)
    (hpost := trans_sub hspe
      (hpre := by simp only [errTag, speWord, arm64_norm]; bi_frame)
      (hpost := by sep_interval))

theorem post_deser_err_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' x19 w0 w1 w2 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (ctAct pqAct adAct : Bool)
    (e : SignalProtocolError) (herr_deser : PublicKey.deserialize rk = .error e)
    {out : Except SignalProtocolError SignalMessage} (hout : out = .error e)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x4c4#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deserializeResult33At (sp' + 176#64) (.error e) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
        memRegion (x19 + 24#64) 96 ∗
        vecU8Buf A rkCap rkPtr rk ∗
        deallocSlot A ctCap ctPtr ctAct ∗
        deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion (sp' + 176#64) 33 ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          signalMessageResultAt A [] x19 out ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_640_wp_placed _ A H hS s0 s sp' rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr rk
  generalize skipFieldStackX 100 = nStk, vecU8Buf A rkCap rkPtr rk = rkBuf at hnext ⊢
  cases e with
  | noKeyTypeIdentifier =>
    have hspe := spe_noKeyType_intro A x19 (s.readReg64 (Reg.gpr 10#5) &&& 255#64) hout
    generalize signalMessageResultAt A [] x19 out = resOut at hspe ⊢
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1600)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext ctAct pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      (hpre := by bi_frame)
      (hpost := trans_sub hspe
        (hpre := by simp only [errTag, speWord, arm64_norm]; bi_frame)
        (hpost := by sep_interval))
  | badKeyType t =>
    have hspe := spe_badKeyType_intro A x19 t hout
    generalize signalMessageResultAt A [] x19 out = resOut at hspe ⊢
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1600)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext ctAct pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      (hpre := by bi_frame)
      (hpost := trans_sub hspe
        (hpre := by simp only [errTag, speWord, arm64_norm]; bi_frame)
        (hpost := by sep_interval))
  | badKeyLength n =>
    have hspe := spe_badKeyLength_intro A x19 n hout
    generalize signalMessageResultAt A [] x19 out = resOut at hspe ⊢
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1600)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext ctAct pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      (hpre := by bi_frame)
      (hpost := trans_sub hspe
        (hpre := by simp only [errTag, speWord, arm64_norm]; bi_frame)
        (hpost := by sep_interval))
  | _ =>
    dsimp only [deserializeResult33At]
    exact SepWPp.pure_pre fun hfalse => False.elim hfalse

/-! ## 32-byte `PublicKey` non-aligned copy layout helpers (`+0x4fc..+0x548` and `+0x6d0..+0x738`) -/

@[expose] def sevenBytesHeadAt (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
    ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)

@[expose] def sevenBytesTailAt (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
    ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))

theorem unpack32_append4 (b0 b1 b2 b3 : BitVec 8) :
    unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
  have h0 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
  have h1 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
  have h2 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_kernel
  have h3 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_kernel
  simp only [unpack32, h0, h1, h2, h3]

theorem pointsTo32_append4 (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_append4]
  simp only [pointsToBytes_cons, pointsToBytes_nil, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

theorem sevenBytesHeadAt_eq_tailAt (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    sevenBytesHeadAt a b0 b1 b2 b3 b4 b5 b6 = sevenBytesTailAt a b0 b1 b2 b3 b4 b5 b6 := by
  dsimp only [sevenBytesHeadAt, sevenBytesTailAt]
  rw [pointsTo32_append4 a b0 b1 b2 b3, pointsTo32_append4 (a + 3#64) b3 b4 b5 b6]
  sep_interval_eq

theorem pointsTo64_eq_sevenBytesHeadAt (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) =
      sevenBytesHeadAt a
        (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
        (w.extractLsb' 32 8) (w.extractLsb' 40 8) (w.extractLsb' 48 8) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  dsimp only [sevenBytesHeadAt]
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_append4]
  simp only [unpack64, pointsToBytes_cons, pointsToBytes_nil]
  sep_interval_eq

theorem unpack64_append8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  have h0 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
  have h1 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
  have h2 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_kernel
  have h3 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_kernel
  have h4 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 32 8 = b4 := by bv_kernel
  have h5 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 40 8 = b5 := by bv_kernel
  have h6 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 48 8 = b6 := by bv_kernel
  have h7 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 56 8 = b7 := by bv_kernel
  simp only [unpack64, h0, h1, h2, h3, h4, h5, h6, h7]

theorem sevenBytesHeadAt_byte_eq_pointsTo64 (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 c7 : BitVec 8) :
    sevenBytesHeadAt a b0 b1 b2 b3 b4 b5 b6 ∗ ((a + 7#64) ↦₈ c7) =
      (a ↦₆₄ (c7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)) := by
  dsimp only [sevenBytesHeadAt]
  rw [pointsTo64_eq_pointsToBytes, unpack64_append8, pointsTo32_append4]
  simp only [pointsToBytes_cons, pointsToBytes_nil]
  sep_interval_eq

@[expose] def pkRestAt (a : BitVec 64)
    (b7 b8 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  ((a + 7#64) ↦₈ b7) ∗ ((a + 8#64) ↦₈ b8) ∗
    ((a + 9#64) ↦₃₂ w9) ∗ ((a + 13#64) ↦₁₆ w13) ∗
    ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₆₄ w23) ∗
    ((a + 31#64) ↦₈ b31)

@[expose] def pkLayoutAt (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  sevenBytesHeadAt a b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt a b7 b8 w9 w13 w15 w23 b31

@[expose] def pkBytesOf (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) : List (BitVec 8) :=
  [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++
    unpack32 w9 ++ unpack16 w13 ++ unpack64 w15 ++ unpack64 w23 ++ [b31]

theorem pkLayoutAt_eq_pointsToBytes (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    pkLayoutAt a b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 =
      (a ↦ₛ pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31) := by
  dsimp only [pkLayoutAt, sevenBytesHeadAt, pkRestAt, pkBytesOf]
  rw [pointsTo32_append4, pointsTo32_eq_pointsToBytes, pointsTo16_eq_pointsToBytes,
    pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes]
  simp only [unpack32, unpack16, unpack64, List.cons_append, List.nil_append,
    pointsToBytes_cons, pointsToBytes_nil]
  sep_interval_eq

theorem pkLayoutAt_entails_memRegion32 (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    pkLayoutAt a b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ⊢ memRegion a 32 := by
  dsimp only [pkLayoutAt, sevenBytesHeadAt, pkRestAt]; sep_interval

theorem exists_eight_bytes (xs : List (BitVec 8)) (h : xs.length = 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7, xs = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rcases xs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩

theorem unpack16_append2 (b0 b1 : BitVec 8) :
    unpack16 (b1 ++ b0) = [b0, b1] := by
  have h0 : (b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
  have h1 : (b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
  simp only [unpack16, h0, h1]

theorem exists_pkBytesOf (bs : List (BitVec 8)) (h : bs.length = 32) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31,
      bs = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0⟩ :=
    exists_eight_bytes (bs.take 8) (by simp [h])
  obtain ⟨b8, b9, b10, b11, b12, b13, b14, b15, h1⟩ :=
    exists_eight_bytes ((bs.drop 8).take 8) (by simp [h])
  obtain ⟨b16, b17, b18, b19, b20, b21, b22, b23, h2⟩ :=
    exists_eight_bytes ((bs.drop 16).take 8) (by simp [h])
  obtain ⟨b24, b25, b26, b27, b28, b29, b30, b31, h3⟩ :=
    exists_eight_bytes (bs.drop 24) (by simp [h])
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8,
    b12 ++ b11 ++ b10 ++ b9,
    b14 ++ b13,
    b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15,
    b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23,
    b31, ?_⟩
  have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp
  have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp
  have hbs : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    rw [h24, List.take_append_drop 8 (bs.drop 16),
      h16, List.take_append_drop 8 (bs.drop 8),
      List.take_append_drop 8 bs]
  rw [hbs, h0, h1, h2, h3]
  simp only [pkBytesOf, unpack32_append4, unpack16_append2, unpack64_append8,
    List.cons_append, List.nil_append]

theorem byte_sevenBytesHeadAt_eq_pointsTo64 (a : BitVec 64)
    (c0 b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    (a ↦₈ c0) ∗ sevenBytesHeadAt (a + 1#64) b0 b1 b2 b3 b4 b5 b6 =
      (a ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ c0)) := by
  dsimp only [sevenBytesHeadAt]
  rw [pointsTo64_eq_pointsToBytes, unpack64_append8, pointsTo32_append4]
  simp only [pointsToBytes_cons, pointsToBytes_nil]
  sep_interval_eq

theorem pkRestAt_entails_memRegion25 (a : BitVec 64)
    (b7 b8 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    pkRestAt a b7 b8 w9 w13 w15 w23 b31 ⊢ memRegion (a + 7#64) 25 := by
  dsimp only [pkRestAt]; sep_interval

theorem deser_ok_entails_spe_region (sret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    (sret ↦₈ 0#8) ∗
      sevenBytesHeadAt (sret + 1#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sret + 1#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sret + 33#64) 15 ⊢
      (sret ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗
        memRegion (sret + 8#64) 40 := by
  rw [← sepConj_assoc (sret ↦₈ 0#8), byte_sevenBytesHeadAt_eq_pointsTo64]
  dsimp only [pkRestAt]; sep_interval

theorem pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    (a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_split32 a (hi ++ lo)]
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_kernel
  have hhi : (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel
  rw [hlo, hhi]

@[local simp, local arm64_norm, local wp_norm]
theorem truncate16_zext32 (w : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 w) = w := by bv_kernel

theorem post_deser_ok_head_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' w104 w15 w23 : BitVec 64}
    {cTag w68 w9 w120 : BitVec 32} {w13 w124 : BitVec 16}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 b112 c0 c1 c2 c3 c4 c5 c6 : BitVec 8}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x4c4#64)
    (hrun : s.status = .Running) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x54c#64) s
      (((sp' + 176#64) ↦₈ 0#8) ∗
        pkLayoutAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
        memRegion (sp' + 209#64) 15 ∗
        ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
        ((sp' + 104#64) ↦₆₄ w104) ∗
        ((sp' + 112#64) ↦₈ b112) ∗
        ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
        sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pc = (blkPl_85).base + 0x54c#64 ∧
        sf.status = .Running ∧
        sf.pstate = subsPState32 cTag 1#32 ∧
        sf.readReg64 .x8 = w15 ∧
        sf.readReg64 .x9 = (b8.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x24 = (b7.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x26 = speWord 2 ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x24 → r ≠ .x26 →
          sf.readReg64 r = s.readReg64 r) ∧
        (Pf ⊢ ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          ((sp' + 64#64) ↦₆₄ (w68 ++ cTag)) ∗
          ((sp' + 104#64) ↦₆₄ w23) ∗
          ((sp' + 112#64) ↦₈ b31) ∗
          ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  dsimp only [pkLayoutAt]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1280)) ?_
  dsimp only [sevenBytesHeadAt]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have h177_tail :
      ((sp' + 177#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((sp' + 177#64 + 4#64) ↦₈ b4) ∗
        ((sp' + 177#64 + 5#64) ↦₈ b5) ∗
        ((sp' + 177#64 + 6#64) ↦₈ b6) =
      sevenBytesTailAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 :=
    sevenBytesHeadAt_eq_tailAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 176#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 177#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 209#64) 15 ∗
      ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
      ((sp' + 104#64) ↦₆₄ w104) ∗
      ((sp' + 112#64) ↦₈ b112) ∗
      ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
      sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6)
    (by
      rw [← h177_tail]
      dsimp only [sevenBytesHeadAt, pkRestAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; bi_entail) ?_
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).base + bv% (1304)) ?_
  dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl2
  have h128_tail := sevenBytesHeadAt_eq_tailAt (sp' + 128#64) b0 b1 b2 b3 c4 c5 c6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 176#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 177#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 209#64) 15 ∗
      ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
      ((sp' + 104#64) ↦₆₄ w104) ∗
      ((sp' + 112#64) ↦₈ b112) ∗
      ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
      sevenBytesTailAt (sp' + 128#64) b0 b1 b2 b3 c4 c5 c6)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 177#64), ← h128_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [arm64_norm]) ?_
  refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + bv% (1352)) ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl3
  have hspe := deser_ok_entails_spe_region (sp' + 176#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hspe
  have h128_head := sevenBytesHeadAt_eq_tailAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6
  have h64_pair := pointsTo32_pair_eq_pointsTo64 (sp' + 64#64) cTag w68
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h64_pair
  refine SepWPp.mono_pre (P' :=
      (((sp' + 176#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗
        memRegion (sp' + 184#64) 40) ∗
      ((sp' + 64#64) ↦₆₄ (w68 ++ cTag)) ∗
      ((sp' + 104#64) ↦₆₄ w23) ∗
      ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6)
    (by
      refine Entails.trans ?_
        (sepConj_mono_left hspe)
      rw [← h64_pair, h128_head]
      dsimp only [sevenBytesTailAt, pkRestAt]
      apply entails_of_eq; simp only [arm64_norm]) ?_
  refine SepWPp.of_sepWP_end_placed hcl3 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl4
  refine ⟨PostEpilogueStatePlaced.of_steps hcl4 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]),
    by simp [arm64_norm], by simp [hrun, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [speWord, arm64_norm],
    fun r hr8 hr9 hr10 hr11 hr24 hr26 => ?_,
    ?_⟩
  · cases r with
    | gpr idx =>
      have h8 : idx ≠ 8#5 := fun h => hr8 (congrArg Reg.gpr h)
      have h9 : idx ≠ 9#5 := fun h => hr9 (congrArg Reg.gpr h)
      have h10 : idx ≠ 10#5 := fun h => hr10 (congrArg Reg.gpr h)
      have h11 : idx ≠ 11#5 := fun h => hr11 (congrArg Reg.gpr h)
      have h24 : idx ≠ 24#5 := fun h => hr24 (congrArg Reg.gpr h)
      have h26 : idx ≠ 26#5 := fun h => hr26 (congrArg Reg.gpr h)
      simp [h8, h9, h10, h11, h24, h26, arm64_norm]
    | sp | xzr => simp [arm64_norm]
  · dsimp only [sevenBytesHeadAt]
    apply entails_of_eq; simp only [BitVec.reduceAdd, speWord, arm64_norm]

theorem post_counter_none_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' x19 w0 w1 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (ctAct pqAct adAct : Bool)
    {out : Except SignalProtocolError SignalMessage} (hout : out = .error .invalidProtobufEncoding)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x54c#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx19 : s.readReg64 .x19 = x19) (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A rkCap rkPtr rk ∗
        deallocSlot A ctCap ctPtr ctAct ∗
        deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          signalMessageResultAt A [] x19 out ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_640_wp_placed _ A H hS s0 s sp' rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr rk
  have hspe := spe_invalidProto_intro A x19 hout
  generalize skipFieldStackX 100 = nStk, vecU8Buf A rkCap rkPtr rk = rkBuf,
    signalMessageResultAt A [] x19 out = resOut at hnext hspe ⊢
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1600)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  exact frame_post
    (hnext ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
      (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
    (hpre := by bi_frame)
    (hpost := trans_sub hspe
      (hpre := by simp only [errTag, speWord, arm64_norm]; bi_frame)
      (hpost := by bi_entail))

theorem post_counter_some_head_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDropSpe : DropSpeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x22 x23 x24 x25 x27 x28 w64 w15 : BitVec 64}
    {w12 pcTag pcVal : BitVec 32} {b8 : BitVec 8}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x54c#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 1#32 1#32)
    (hx8 : s.readReg64 .x8 = w15)
    (hx9 : s.readReg64 .x9 = (b8.zeroExtend 32).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = x20)
    (hx21 : s.readReg64 .x21 = x21) (hx22 : s.readReg64 .x22 = x22)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg64 .x24 = x24)
    (hx25 : s.readReg64 .x25 = x25) (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = x28) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x578#64) s
      (((sp' + 12#64) ↦₃₂ w12) ∗
        ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₆₄ w64) ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pc = (blkPl_85).base + 0x578#64 ∧
        sf.status = .Running ∧
        sf.pstate = addsPState64 x27 1#64 ∧
        sf.readReg64 .x8 = (if (pcTag &&& 1#32) != 0#32 then pcVal else 0#32).zeroExtend 64 ∧
        sf.readReg64 .x19 = x19 ∧ sf.readReg64 .x20 = x20 ∧
        sf.readReg64 .x21 = x21 ∧ sf.readReg64 .x22 = x22 ∧
        sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x24 = x24 ∧
        sf.readReg64 .x25 = x25 ∧ sf.readReg64 .x26 = speWord 2 ∧
        sf.readReg64 .x27 = x27 ∧ sf.readReg64 .x28 = x28 ∧
        (Pf ⊢ ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
          ((sp' + 64#64) ↦₆₄ w15) ∗
          ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcall := hDropSpe
  clear hDropSpe
  have hstack := stackAt_sub_split sp' dropSpeStackX (skipFieldStackX 100)
  generalize skipFieldStackX 100 = nStk at hstack ⊢
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropSpeName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have hspe_eq : speAt A [] (sp' + 176#64) .invalidProtobufEncoding =
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 := by
    dsimp only [speAt]
    have ha : sp' + 176#64 + 8#64 = sp' + 184#64 := by bv_omega
    rw [ha]
  refine SepWPp.call_noPanic_tryFrom_placed (⟨sp' + 176#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_85).base + bv% (1376)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 176#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp dropSpeStackX)
    (φ := sp' + 176#64 = sp' + 176#64)
    (by simp [dropSpeSpecX, hsp_eq, arm64_norm])
    rfl
    (by rw [hspe_eq, hstack, hsp_eq]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, hsp_eq, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = x20 := by simp [hx20_cs, hx20, arm64_norm]
  have hx21_2 : s2.readReg64 .x21 = x21 := by simp [hx21_cs, hx21, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = x22 := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = x23 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = x25 := by simp [hx25_cs, hx25, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = x27 := by simp [hx27_cs, hx27, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = x28 := by simp [hx28_cs, hx28, arm64_norm]
  have h48 : memRegion (sp' + 176#64) 48 =
      (∃∗ w176 : BitVec 64, ((sp' + 176#64) ↦₆₄ w176)) ∗ memRegion (sp' + 184#64) 40 := by
    sep_interval_eq
  rw [h48]
  generalize memRegion (sp' + 184#64) 40 = reg40
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w176 => ?_
  refine SepWPp.of_sepWP_end_placed hcl2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  refine ⟨PostEpilogueStatePlaced.of_steps hcl3 (by simp [hsp2_eq, arm64_norm]) hsp_eq hsp
      (by simp [htr2, htr, arm64_norm]),
    by simp [arm64_norm], by simp [hrun2, arm64_norm],
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx19_2, arm64_norm], by simp [hx20_2, arm64_norm],
    by simp [hx21_2, arm64_norm], by simp [hx22_2, arm64_norm],
    by simp [hx23_2, arm64_norm], by simp [hx24_2, arm64_norm],
    by simp [hx25_2, arm64_norm], by simp [hx26_2, arm64_norm],
    by simp [hx27_2, arm64_norm], by simp [hx28_2, arm64_norm],
    ?_⟩
  simp only [hstack, hsp_eq, arm64_norm]; bi_entail

theorem post_ct_none_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' x19 w0 w1 rkCap rkPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (pqAct adAct : Bool)
    {out : Except SignalProtocolError SignalMessage} (hout : out = .error .invalidProtobufEncoding)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x578#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = addsPState64 noneCap 1#64)
    (hx19 : s.readReg64 .x19 = x19) (hx26 : s.readReg64 .x26 = speWord 2)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A rkCap rkPtr rk ∗
        deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          signalMessageResultAt A [] x19 out ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_668_wp_placed _ A H hS s0 s sp' pqCap pqPtr adCap adPtr
  have hspe := spe_invalidProto_intro A x19 hout
  have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
  generalize skipFieldStackX 100 = nStk, signalMessageResultAt A [] x19 out = resOut at hnext hspe hstack ⊢
  have hcall := hS.alloc.dealloc
  by_cases hcap : rkCap = 0#64
  · clear hcall hstack
    subst hcap
    rw [vecU8Buf_zero]
    refine SepWPp.mono_pre (P' := ⌜rk = [] ∧ rkPtr ≠ 0⌝ ∗
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ 0#64) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' nStk))
      (Entails.of_eq (by simp only [sepConj_assoc, sepConj_comm, sepConj_left_comm])) ?_
    refine SepWPp.pure_pre (fun _ => ?_)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1640)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext pqAct adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm]))
      (hpre := by bi_frame)
      (hpost := trans_sub hspe
        (hpre := by simp only [errTag, speWord, arm64_norm]; bi_frame)
        (hpost := by bi_entail))
  · have hdealloc := vecU8Buf_dealloc A rkCap rkPtr rk hcap
    generalize vecU8Buf A rkCap rkPtr rk = rkBuf at hdealloc ⊢
    refine SepWPp.mono_pre (P' := ⌜0 < rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0#64⌝ ∗
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' nStk))
      (trans_sub hdealloc (hpre := by bi_frame) (hpost := by bi_entail)) ?_
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (rkPtr, rkCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (1640)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := rkPtr = rkPtr ∧ rkCap.toNat = rkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk rkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨_, _, _, hx22_cs, _, _, hx25_cs, _⟩
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    exact frame_post
      (hnext pqAct adAct
        ⟨by simp [hsp2, hsp_eq, arm64_norm], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx25_2 hx22_2)
      (hpre := by simp only [hstack, hsp_eq, arm64_norm]; bi_frame)
      (hpost := trans_sub hspe
        (hpre := by simp only [errTag, speWord, arm64_norm]; bi_frame)
        (hpost := by bi_entail))

end DeserOpaqueAtoms

end CryptoVerification.LibsignalTripleRatchet.Wire

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 4 (`outMsg = none` Paths)

Verifies the two `outMsg = none` paths from `0x58ae4` (`+13968`):
- Path 4a (`ack = false`): `.stillReceivingStillSending` → `States.ct1Sampled`.
- Path 4b (`ack = true`): `.stillReceiving` → `States.ct1Acknowledged`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[reducible] private def ct1s4MemcpySpec (Inv : State → Prop) (calleeStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun x s => ⌜Inv s⌝ ∗ sessionMemcpyRegionSpec.pre x s ∗ stackAt s.sp calleeStack
  post := fun x s0 sf => sessionMemcpyRegionSpec.post x s0 sf ∗ stackAt s0.sp calleeStack

private theorem ct1s4_stackAt_zero_sep (fsp : BitVec 64) (Rest : SepProp) :
    stackAt fsp 0 ∗ Rest = Rest := by
  simp only [stackAt, memRegion_zero, emp_sepConj]

private theorem ct1s4_stackAt_statesRecvCallee_sep (fsp : BitVec 64) (Rest : SepProp) :
    stackAt fsp statesRecvCalleeStackX ∗ Rest =
      stackAt fsp extHookStack ∗ (memRegion (fsp - 19552#64) 3168 ∗ Rest) := by
  rw [stackAt_split_bottom_of_eq fsp statesRecvCalleeStackX extHookStack 3168]
  ac_rfl

private theorem ct1s4_seq_inv {prog : Program} {Inv : State → Prop}
    (hstep : ∀ {s s' : State}, Inv s → Steps prog s s' → Inv s')
    {mid target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hinv : Inv s)
    (h : SepWP prog mid s P (fun sm Pm => Inv sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · rcases (hnext (hstep hinv hsteps)).elim hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hpost⟩ | ⟨hoom, hf⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hpost⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr ⟨hoom, hf⟩⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hf⟩⟩

private theorem ct1s4_seq_inv_lr {prog : Program} {Inv : State → Prop}
    (hstep : ∀ {s s' : State}, Inv s → Steps prog s s' → Inv s')
    {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hinv : Inv s)
    (h : SepWP prog (s.readReg64 .x30) s P (fun sm Pm => Inv sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  ct1s4_seq_inv hstep (mid := s.readReg64 .x30) hinv h

local macro "ct1s4_call_memcpy " hstep:term:max hmemcpy:ident hinv:ident hnext_inv:ident g:term : tactic =>
  `(tactic| (
    apply ct1s4_seq_inv_lr $hstep $hinv
    wp_call $hmemcpy (x := $g)
    all_goals try exact $hinv
    refine SepWP.done (by simp only [arm64_norm]; assumption) (by assumption) fun $hnext_inv => ?_))

/-! ## 1. `mid376At` and `Split400` Byte/Word Decompositions -/

@[expose] def mid376Bytes (w512 w520 w528 : BitVec 64) (bs352 : List (BitVec 8)) : List (BitVec 8) :=
  unpack64 w512 ++ (unpack64 w520 ++ (unpack64 w528 ++ bs352))

@[expose] def mid376At (a : BitVec 64) (w512 w520 w528 : BitVec 64) (bs352 : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ w512) ∗ ((a + 8#64) ↦₆₄ w520) ∗ ((a + 16#64) ↦₆₄ w528) ∗ ((a + 24#64) ↦ₛ bs352)

theorem mid376Bytes_length (w512 w520 w528 : BitVec 64) {bs352 : List (BitVec 8)}
    (h : bs352.length = 352) :
    (mid376Bytes w512 w520 w528 bs352).length = 376 := by
  dsimp only [mid376Bytes]
  simp only [List.length_append, unpack64_length, h]

theorem mid376At_eq_pointsToBytes (a : BitVec 64) (w512 w520 w528 : BitVec 64)
    (bs352 : List (BitVec 8)) :
    mid376At a w512 w520 w528 bs352 = (a ↦ₛ mid376Bytes w512 w520 w528 bs352) := by
  dsimp only [mid376At, mid376Bytes]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes]
  have ha1 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha2 : a + 8#64 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha3 : a + 16#64 + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
  rw [ha1, ha2, ha3]

structure Split400 where
  w0 : BitVec 64
  mid352 : List (BitVec 8)
  tail : Words5

@[expose] def Split400.tailBytes (d : Split400) : List (BitVec 8) :=
  d.mid352 ++ wordsBytes d.tail.toList

@[expose] def Split400.toBytes (d : Split400) : List (BitVec 8) :=
  unpack64 d.w0 ++ d.tailBytes

@[expose] def split400At (a : BitVec 64) (d : Split400) : SepProp :=
  (a ↦₆₄ d.w0) ∗ ((a + 8#64) ↦ₛ d.mid352) ∗ wordsAt (a + 360#64) d.tail.toList

theorem Split400.tailBytes_length (d : Split400) (hmid : d.mid352.length = 352) :
    d.tailBytes.length = 392 := by
  dsimp only [Split400.tailBytes]
  simp only [List.length_append, hmid, length_wordsBytes, Words5.toList_length]

theorem Split400.toBytes_length (d : Split400) (hmid : d.mid352.length = 352) :
    d.toBytes.length = 400 := by
  dsimp only [Split400.toBytes]
  rw [List.length_append, unpack64_length, d.tailBytes_length hmid]

theorem split400At_eq_w0_tailBytes (a : BitVec 64) (d : Split400) (hmid : d.mid352.length = 352) :
    split400At a d = ((a ↦₆₄ d.w0) ∗ ((a + 8#64) ↦ₛ d.tailBytes)) := by
  dsimp only [split400At, Split400.tailBytes]
  rw [pointsToBytes_append (a + 8#64) d.mid352 (wordsBytes d.tail.toList),
      hmid, ← wordsAt_eq_pointsToBytes]
  have ha : (a + 8#64) + BitVec.ofNat 64 352 = a + 360#64 := by bv_omega
  rw [ha]

theorem split400At_eq_pointsToBytes (a : BitVec 64) (d : Split400) (hmid : d.mid352.length = 352) :
    split400At a d = (a ↦ₛ d.toBytes) := by
  rw [split400At_eq_w0_tailBytes a d hmid]
  dsimp only [Split400.toBytes]
  rw [pointsToBytes_append a (unpack64 d.w0) d.tailBytes,
      unpack64_length, ← pointsTo64_eq_pointsToBytes a d.w0]

theorem exists_split400_of_length_400 {bs : List (BitVec 8)} (h : bs.length = 400) :
    ∃ d : Split400, d.mid352.length = 352 ∧ bs = d.toBytes := by
  have h0 : (bs.take 8).length = 8 * 1 := by simp [List.length_take]; omega
  have hmid : ((bs.drop 8).take 352).length = 352 := by
    simp [List.length_take, List.length_drop]; omega
  have htail : ((bs.drop 8).drop 352).length = 40 := by
    simp [List.length_drop]; omega
  obtain ⟨ws0, hlen0, hws0⟩ := exists_words_of_length 1 (bs.take 8) h0
  rcases ws0 with _ | ⟨w0, _ | _⟩ <;> try simp at hlen0
  obtain ⟨tail, htail_eq⟩ := exists_words5_of_length_40 htail
  refine ⟨⟨w0, (bs.drop 8).take 352, tail⟩, hmid, ?_⟩
  dsimp only [Split400.toBytes, Split400.tailBytes]
  have hw0 : bs.take 8 = unpack64 w0 := by
    simpa [wordsBytes, List.append_nil] using hws0
  rw [← hw0, ← htail_eq]
  simp only [List.take_append_drop]

theorem split400At_entails_memRegion (a : BitVec 64) (d : Split400) (hmid : d.mid352.length = 352) :
    split400At a d ⊢ memRegion a 400 := by
  rw [split400At_eq_pointsToBytes a d hmid]
  have h := ProofLib.pointsToBytes_entails_memRegion a d.toBytes
  rwa [d.toBytes_length hmid] at h

theorem Relocatable.extract_split400 {F : BitVec 64 → SepProp} (hrel : Relocatable 400 F) (a : BitVec 64) :
    F a ⊢ ∃∗ d : Split400, ⌜d.mid352.length = 352⌝ ∗ split400At a d ∗ relocatedHeap F d.toBytes := by
  refine Entails.trans (hrel a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨d, hmid, rfl⟩ := exists_split400_of_length_400 hlen
  refine Entails.sepExists_right d ?_
  refine Entails.pure_right hmid ?_
  rw [split400At_eq_pointsToBytes a d hmid]
  exact Entails.refl _

@[expose] def copyFullScratch (sc : CopyScratchStack) (d : Split928) : CopyScratchStack where
  c0 := { sc.c0 with
    w1 := d.c3.w5
    w2 := d.c2.w4
    w3 := d.c2.w0
    w4 := d.c1.w14
    w5 := d.c2.w1
    w6 := d.c2.w10
    w7 := d.c2.w9
    w8 := d.c2.w7
    w9 := d.c2.w3
    w10 := d.c2.w2
    w11 := d.c3.w10
    w12 := d.c3.w8
    w13 := d.c2.w8
    w14 := d.c2.w5
    w15 := d.c3.w6
  }
  w80 := d.c2.w6
  w88 := d.c0.w1
  w90 := d.c3.w12
  w98 := d.c1.w0
  wa0 := d.c1.w1
  wa8 := d.c3.w0
  wb0 := d.c3.w4
  wb8 := d.c3.w2
  wc0 := d.c2.w12
  wc8 := d.c2.w14
  wd0 := d.c0.w2
  wd8 := d.c3.w1
  wf0 := d.c2.w11

@[expose] def mkSplit928From528And400 (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400) : Split928 where
  c0 := c0
  c1 := c1
  c2 := c2
  c3 := c3
  mid := mid376Bytes w512 w520 d400.w0 d400.mid352
  tail := d400.tail

theorem mkSplit928From528And400_mid_length (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64)
    {d400 : Split400} (hmid : d400.mid352.length = 352) :
    (mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400).mid.length = 376 :=
  mid376Bytes_length w512 w520 d400.w0 hmid

/-! ## 2. Branch on `w22` (`ack`) at `0x58ae4` (`+13968`) -/

theorem polyEncoderBodyAt_entails_vecs_tail (A : RustAlloc) (stA : BitVec 64) (enc : PolyEncoder) :
    polyEncoderBodyAt A (stA + 8#64) enc ⊢
      ∃∗ vecs : List (List GF16),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecGF16ListOf A (stA + 8#64) vecs ∗
        memRegion (stA + 392#64) 8 := by
  unfold polyEncoderBodyAt
  have htail := polyEncoderTail_entails_memRegion_8 stA enc.idx
  unfold polyEncoderIdxOff polyEncoderPadOff at htail
  have h392 : (stA + 8#64) + 384#64 = stA + 0x188#64 := by bv_omega
  have h396 : (stA + 8#64) + 388#64 = stA + 0x18c#64 := by bv_omega
  rw [h392, h396]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf]
    refine Entails.sepExists_right (pts.map Point.value) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hlen => ?_
    have hlen' : (pts.map Point.value).length = NUM_POLYS := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    exact sepConj_mono_right htail
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf]
    refine Entails.sepExists_right (ps.map LibsignalSpqrV1.Poly.coefficients) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hlen => ?_
    have hlen' : (ps.map LibsignalSpqrV1.Poly.coefficients).length = NUM_POLYS := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    exact sepConj_mono_right htail

@[expose] def mkSplit928Ct1Acknowledged (c_uc : Words16) (c_dec : Words50)
    (bs352 : List (BitVec 8)) (tail5 : Words5) : Split928 where
  c0 := {
    w0 := 11#64
    w1 := c_uc.w0
    w2 := c_uc.w1
    w3 := c_uc.w2
    w4 := c_uc.w3
    w5 := c_uc.w4
    w6 := c_uc.w5
    w7 := c_uc.w6
    w8 := c_uc.w7
    w9 := c_uc.w8
    w10 := c_uc.w9
    w11 := c_uc.w10
    w12 := c_uc.w11
    w13 := c_uc.w12
    w14 := c_uc.w13
    w15 := c_uc.w14
  }
  c1 := {
    w0 := c_uc.w15
    w1 := c_dec.c0.w0
    w2 := c_dec.c0.w1
    w3 := c_dec.c0.w2
    w4 := c_dec.c0.w3
    w5 := c_dec.c0.w4
    w6 := c_dec.c0.w5
    w7 := c_dec.c0.w6
    w8 := c_dec.c0.w7
    w9 := c_dec.c0.w8
    w10 := c_dec.c0.w9
    w11 := c_dec.c0.w10
    w12 := c_dec.c0.w11
    w13 := c_dec.c0.w12
    w14 := c_dec.c0.w13
    w15 := c_dec.c0.w14
  }
  c2 := {
    w0 := c_dec.c0.w15
    w1 := c_dec.c1.w0
    w2 := c_dec.c1.w1
    w3 := c_dec.c1.w2
    w4 := c_dec.c1.w3
    w5 := c_dec.c1.w4
    w6 := c_dec.c1.w5
    w7 := c_dec.c1.w6
    w8 := c_dec.c1.w7
    w9 := c_dec.c1.w8
    w10 := c_dec.c1.w9
    w11 := c_dec.c1.w10
    w12 := c_dec.c1.w11
    w13 := c_dec.c1.w12
    w14 := c_dec.c1.w13
    w15 := c_dec.c1.w14
  }
  c3 := {
    w0 := c_dec.c1.w15
    w1 := c_dec.c2.w0
    w2 := c_dec.c2.w1
    w3 := c_dec.c2.w2
    w4 := c_dec.c2.w3
    w5 := c_dec.c2.w4
    w6 := c_dec.c2.w5
    w7 := c_dec.c2.w6
    w8 := c_dec.c2.w7
    w9 := c_dec.c2.w8
    w10 := c_dec.c2.w9
    w11 := c_dec.c2.w10
    w12 := c_dec.c2.w11
    w13 := c_dec.c2.w12
    w14 := c_dec.c2.w13
    w15 := c_dec.c2.w14
  }
  mid := mid376Bytes c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352
  tail := tail5

theorem mkSplit928Ct1Acknowledged_mid_length (c_uc : Words16) (c_dec : Words50)
    {bs352 : List (BitVec 8)} (tail5 : Words5) (h : bs352.length = 352) :
    (mkSplit928Ct1Acknowledged c_uc c_dec bs352 tail5).mid.length = 376 :=
  mid376Bytes_length c_dec.c2.w15 c_dec.w48 c_dec.w49 h

end CryptoVerification.SpqrV1.States.Recv

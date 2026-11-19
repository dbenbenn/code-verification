/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep
public import ProofLib.FsTrace

/-!
# `Hkdf<Sha256>::expand_multi_info` (`0x1a874`) for 96-Byte Output and 46-Byte Info

Proves `expand_multi_info_96_46_runsTo` for `<hkdf::Hkdf<sha2::Sha256>>::expand_multi_info`
(`b + 0x1a874`) when `okmLen = 96` and `info.length = 46` (`INFO_PQXDH`).
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet.Expand

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

variable {b : BitVec 64}
theorem hkdfExpand_96_eq (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 96 =
      t1 F prk info ++ t2 F prk info ++ t3 F prk info := by
  dsimp only [hkdfExpand]
  have h3 : (96 + 31) / 32 = 3 := rfl
  have hblocks : (hkdfBlocks F prk info 3).flatten =
      t1 F prk info ++ t2 F prk info ++ t3 F prk info := by
    simp [hkdfBlocks, t1, t2, t3, List.append_assoc]
  rw [h3, hblocks, List.take_of_length_le]
  simp [t1, t2, t3, length_hmacWith]

/-- Bundled preconditions of `expand_multi_info` (`b + 0x1a874`) for `okmLen = 96` and
`info.length = 46`. -/
structure ExpandPre96_46 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (s₀ : State) : Prop where
  pc_eq         : s₀.pc = b + 0x1a874#64
  status        : s₀.status = .Running
  x3_eq         : s₀.readReg64 .x3 = 96#64
  prk_le        : prk.length ≤ 64
  info_len_eq   : info.length = 46
  hmac_st       : HmacSt s₀.mem (s₀.readReg64 .x0) F prk []
  info_ptr      : s₀.mem.read64 (s₀.readReg64 .x1) = infoPtr
  info_len      : s₀.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64
  info_bytes    : s₀.mem.readBytes infoPtr 46 = info
  read_x0       : s₀.mem.Readable (s₀.readReg64 .x0) 0x90
  read_x1       : s₀.mem.Readable (s₀.readReg64 .x1) 16
  rw_x2         : RW s₀.mem (s₀.readReg64 .x2) 96
  rw_stack      : RW s₀.mem (s₀.sp - 640#64) 640
  disj_x2_stack : DisjointRegions (s₀.readReg64 .x2) 96 (s₀.sp - 640#64) 640
  disj_x0_stack : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.sp - 640#64) 640
  disj_x0_x2    : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.readReg64 .x2) 96
  disj_x1_stack : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.sp - 640#64) 640
  disj_x1_x2    : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.readReg64 .x2) 96
  out_info_stk  : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.sp - 640#64) 640 a
  out_info_x2   : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.readReg64 .x2) 96 a
  sp_aligned    : (s₀.sp &&& 15#64) = 0#64

namespace ExpandPre96_46

variable {F : ShaState → List (BitVec 8) → ShaState}
  {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State} {m : Memory}

theorem rw_esp (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.RW (esp s₀) 496 := by
  have hrw : m.RW (s₀.sp - 640#64) 640 := (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_stack
  unfold esp
  exact hrw.sub (by bv_omega)

theorem rw_x2_frame (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.RW (s₀.readReg64 .x2) 96 :=
  (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_x2

theorem readable_x0 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.Readable (s₀.readReg64 .x0) 0x90 :=
  (Expand.Frame.readable_iff hf _ _).mpr hpre.read_x0

theorem readable_x1 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.Readable (s₀.readReg64 .x1) 16 :=
  (Expand.Frame.readable_iff hf _ _).mpr hpre.read_x1

theorem hmac_x0 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    HmacSt m (s₀.readReg64 .x0) F prk [] := by
  have hd : ∀ r ∈ [(s₀.readReg64 .x2, 96), (s₀.sp - 640#64, 640)],
      DisjointRegions r.1 r.2 (s₀.readReg64 .x0) 0x90 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x0_x2.symm
    · exact hpre.disj_x0_stack.symm
  rcases hpre.hmac_st with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hf.1 _ (fun r hr => ?_)).trans hpos
    exact (hd r hr).outside (by unfold InRegion; bv_omega) (by decide)
  · refine (Expand.Frame.readBytes_eq hf (fun r hr => ?_) (by decide)).trans hin
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x40#64) ⟨by decide, by bv_omega⟩
  · refine (Expand.Frame.read64_eq hf (fun r hr => ?_)).trans hcnt1
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x60#64) ⟨by decide, by bv_omega⟩
  · refine (Expand.Frame.readBytes_eq hf (fun r hr => ?_) (by decide)).trans hout
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x68#64) ⟨by decide, by bv_omega⟩
  · refine (Expand.Frame.read64_eq hf (fun r hr => ?_)).trans hcnt2
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x88#64) ⟨by decide, by bv_omega⟩

theorem info_ptr_eq (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.read64 (s₀.readReg64 .x1) = infoPtr := by
  rw [Expand.Frame.read64_eq hf]
  · exact hpre.info_ptr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem info_len_eq_46 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 := by
  rw [Expand.Frame.read64_eq hf]
  · exact hpre.info_len
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem info_bytes_eq (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.readBytes infoPtr 46 = info := by
  refine (List.ext_getElem (by simp [hpre.info_len_eq]) fun i h1 h2 => ?_).trans hpre.info_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < 46 := by simpa using h1
  have hin : InRegion infoPtr 46 (infoPtr + BitVec.ofNat 64 i) :=
    inRegion_base_add infoPtr 46 i hi (by decide)
  refine hf.1 _ (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hpre.out_info_x2 _ hin
  · exact hpre.out_info_stk _ hin

theorem saved_of_agreesOutside_x2 {m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre96_46 b F prk info infoPtr s₀)
    (hs : ExpandSaved s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x2 + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 96) :
    ExpandSaved s₀ m' := by
  have hd_x2_saved : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀ + 400#64) 96 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; bv_omega⟩
    unfold esp
    exact hd1.sub_right (s₀.sp - 496#64 + 400#64) ⟨by decide, by bv_omega⟩
  have hread (k : BitVec 64) (hk : 400 ≤ k.toNat ∧ k.toNat + 8 ≤ 496) :
      m'.read64 (esp s₀ + k) = m.read64 (esp s₀ + k) := by
    refine hA.read64_eq ?_
    exact hd_x2_saved.sub_right (esp s₀ + k) ⟨by decide, by bv_omega⟩
  exact
    { m400 := (hread 400#64 (by decide)).trans hs.m400
      m408 := (hread 408#64 (by decide)).trans hs.m408
      m416 := (hread 416#64 (by decide)).trans hs.m416
      m424 := (hread 424#64 (by decide)).trans hs.m424
      m432 := (hread 432#64 (by decide)).trans hs.m432
      m440 := (hread 440#64 (by decide)).trans hs.m440
      m448 := (hread 448#64 (by decide)).trans hs.m448
      m456 := (hread 456#64 (by decide)).trans hs.m456
      m464 := (hread 464#64 (by decide)).trans hs.m464
      m472 := (hread 472#64 (by decide)).trans hs.m472
      m480 := (hread 480#64 (by decide)).trans hs.m480
      m488 := (hread 488#64 (by decide)).trans hs.m488 }

theorem common_of_agreesOutside_x2 {s s' : State} {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre96_46 b F prk info infoPtr s₀)
    (hc : ExpandCommon 96 s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hA    : AgreesOutside s.mem s'.mem (s₀.readReg64 .x2 + off) sz)
    (hoff  : 0 < sz ∧ off.toNat + sz ≤ 96) :
    ExpandCommon 96 s₀ s' := by
  have hd_x2_esp : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀) 32 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; bv_omega⟩
    unfold esp
    exact hd1.sub_right (s₀.sp - 496#64) ⟨by decide, by bv_omega⟩
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA.read64_eq (hd_x2_esp.sub_right (esp s₀ + 8#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA.read64_eq (hd_x2_esp.sub_right (esp s₀ + 16#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    hpre.saved_of_agreesOutside_x2 hc.saved hA hoff,
    ExpandFrame.of_agreesOutside_x2 hc.frame hA hoff.2⟩

theorem read64_x0_write64_esp (hpre : ExpandPre96_46 b F prk info infoPtr s₀) :
    (∀ (m : Memory) (off v : BitVec 64) (hoff : decide (off.toNat + 8 ≤ 496) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x0) = m.read64 (s₀.readReg64 .x0)) ∧
    (∀ (m : Memory) (off x0_off v : BitVec 64)
        (hoff : decide (off.toNat + 8 ≤ 496) = true)
        (hx0 : decide (x0_off.toNat + 8 ≤ 0x90) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x0 + x0_off) =
        m.read64 (s₀.readReg64 .x0 + x0_off)) := by
  refine ⟨fun m off v hoff => ?_, fun m off x0_off v hoff hx0 => ?_⟩
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 0x90 :=
      hpre.disj_x0_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 8 :=
      h1.sub_right (s₀.readReg64 .x0) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have hx0' : x0_off.toNat + 8 ≤ 0x90 := of_decide_eq_true hx0
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 0x90 :=
      hpre.disj_x0_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0 + x0_off) 8 :=
      h1.sub_right (s₀.readReg64 .x0 + x0_off) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd

theorem read64_x1_write_esp (hpre : ExpandPre96_46 b F prk info infoPtr s₀) :
    (∀ (m : Memory) (off v : BitVec 64) (hoff : decide (off.toNat + 8 ≤ 496) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x1) = m.read64 (s₀.readReg64 .x1)) ∧
    (∀ (m : Memory) (off v : BitVec 64) (hoff : decide (off.toNat + 8 ≤ 496) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x1 + 8#64) =
        m.read64 (s₀.readReg64 .x1 + 8#64)) ∧
    (∀ (m : Memory) (off : BitVec 64) (v : BitVec 8) (hoff : decide (off.toNat < 496) = true),
      (m.write8 (esp s₀ + off) v).read64 (s₀.readReg64 .x1) = m.read64 (s₀.readReg64 .x1)) ∧
    (∀ (m : Memory) (off : BitVec 64) (v : BitVec 8) (hoff : decide (off.toNat < 496) = true),
      (m.write8 (esp s₀ + off) v).read64 (s₀.readReg64 .x1 + 8#64) =
        m.read64 (s₀.readReg64 .x1 + 8#64)) := by
  refine ⟨fun m off v hoff => ?_, fun m off v hoff => ?_,
          fun m off v hoff => ?_, fun m off v hoff => ?_⟩
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 8 :=
      h1.sub_right (s₀.readReg64 .x1) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1 + 8#64) 8 :=
      h1.sub_right (s₀.readReg64 .x1 + 8#64) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat < 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 8 :=
      h1.sub_right (s₀.readReg64 .x1) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 1 |>.write8 (by simp [InRegion])).read64_eq hd
  · have hoff' : off.toNat < 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1 + 8#64) 8 :=
      h1.sub_right (s₀.readReg64 .x1 + 8#64) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 1 |>.write8 (by simp [InRegion])).read64_eq hd

theorem fin_side_conditions {s : State}
    (hpre : ExpandPre96_46 b F prk info infoPtr s₀)
    (hf : ExpandFrame 96 s₀ s.mem) :
    RW s.mem (esp s₀ + 208#64) 32 ∧
    RW s.mem (esp s₀ + 240#64) 0x90 ∧
    RW s.mem (esp s₀ - 144#64) 144 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ + 240#64) 0x90 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 144#64) 144 ∧
    DisjointRegions (esp s₀ + 240#64) 0x90 (esp s₀ - 144#64) 144 := by
  have hrw_stack : s.mem.RW (s₀.sp - 640#64) 640 :=
    (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_stack
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hf
  refine ⟨hrw_esp.sub (by bv_omega), hrw_esp.sub (by bv_omega),
    hrw_stack.sub (by unfold esp; bv_omega),
    by unfold DisjointRegions; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega⟩

end ExpandPre96_46

/-! ## Block 1 (`T(1)`) -/

theorem HmacSt.of_memcpy_counter_64_0_46 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key info : List (BitVec 8)}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key [])
    (hinfo : info.length = 46) :
    HmacSt (((((m₀.writeBytes (esp s₀ + 64#64) info).write8
      (esp s₀ + 127#64) 46#8).write8
      (esp s₀ + 240#64) 1#8).write8
      (esp s₀ + 110#64) 1#8).write8
      (esp s₀ + 127#64) 47#8)
      (esp s₀ + 64#64) F key (info ++ [1#8]) := by
  let a := esp s₀ + 64#64
  let m₁ := m₀.writeBytes a info
  let m₂ := (((m₁.write8 (a + 63#64) 46#8).write8 (a + 176#64) 1#8).write8
    (a + 46#64) 1#8).write8 (a + 63#64) 47#8
  have h127 : esp s₀ + 127#64 = a + 63#64 := by dsimp [a]; bv_lin
  have h240 : esp s₀ + 240#64 = a + 176#64 := by dsimp [a]; bv_lin
  have h110 : esp s₀ + 110#64 = a + 46#64 := by dsimp [a]; bv_lin
  rw [h127, h240, h110]
  change HmacSt m₂ a F key (info ++ [1#8])
  rcases h₀ with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  have hlen : (info ++ [1#8]).length = 47 := by simp [hinfo]
  have hag_w : AgreesOutside m₁ m₂ (a + 46#64) 177 := by
    dsimp only [m₂]
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    exact AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, show (47 : ℕ) = 46 + 1 from rfl, Bytes.readBytes_add m₂ a 46 1]
    have h_info : m₂.readBytes a 46 = info := by
      have hd2 : DisjointRegions (a + 46#64) 177 a 46 := by
        unfold DisjointRegions; bv_omega
      rw [hag_w.readBytes_eq hd2 (by decide)]
      dsimp only [m₁]
      have h := Bytes.readBytes_writeBytes_same m₀ a info (by omega)
      rwa [hinfo] at h
    have h_c : m₂.readBytes (a + BitVec.ofNat 64 46) 1 = [1#8] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_info, h_c]
  · rw [hlen, show (0x3f#64 : BitVec 64) = 63#64 from rfl]
    dsimp only [m₂]
    exact Memory.read8_write8_same _ _ _
  · have h_ag_st : ∀ (off : BitVec 64) (sz : ℕ),
        0 < sz → 64 ≤ off.toNat → off.toNat + sz ≤ 144 →
        m₂.readBytes (a + off) sz = m₀.readBytes (a + off) sz := by
      intro off sz hsz0 h64 h144
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          writeBytes_readBytes_disj m₀ _ info (a + off) sz
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by omega)]
    exact (h_ag_st 0x40#64 32 (by decide) (by decide) (by decide)).trans hin
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        writeBytes_read64_disj m₀ _ info (a + 0x60#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt1]
  · have h_ag_out : m₂.readBytes (a + 0x68#64) 32 = m₀.readBytes (a + 0x68#64) 32 := by
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          writeBytes_readBytes_disj m₀ _ info (a + 0x68#64) 32
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide)]
    exact h_ag_out.trans hout
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        writeBytes_read64_disj m₀ _ info (a + 0x88#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt2]

/-- Cut `LoopB_96` at `b + 0x1aad0` (after `memcpy` of `info.drop 32` and appending `(i + 1)#8`). -/
structure StateLoopB_96 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8))
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x1aad0#64
  common  : ExpandCommon 96 s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = 32#64
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacStGen s.mem (esp s₀ + 64#64) F prk (tPrev ++ info.take 32)
              (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopC_96` at `b + 0x30680` (`finalize_fixed` entry in loop). -/
structure StateLoopC_96 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8))
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + 0x30764#64
  common   : ExpandCommon 96 s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x1ab14#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq   : s.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + 32)
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x24_eq   : s.readReg64 .x24 = 64#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x28_eq   : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_240 : HmacStGen s.mem (esp s₀ + 240#64) F prk (tPrev ++ info.take 32)
               (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

theorem ExpandCommon.of_write64_esp0_and_low64 {s₀ s s' : State} {v : BitVec 64} {m_mid : Memory}
    (hc : ExpandCommon 96 s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hmid  : AgreesOutside s.mem m_mid (esp s₀ + 64#64) 64)
    (hmem' : s'.mem = m_mid.write64 (esp s₀) v) :
    ExpandCommon 96 s₀ s' := by
  have hc_mid : ExpandCommon 96 s₀ (s.setMem m_mid) :=
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 64) hc
      (by rw [State.status_setMem]; exact hc.status)
      (by rw [State.sp_setMem]; exact hc.sp_eq)
      (by rw [State.readReg64_setMem]; exact hc.x29_eq)
      (by rw [State.readReg64_setMem]; exact hc.x27_eq)
      (by rw [State.readReg64_setMem]; exact hc.x20_eq)
      (by rw [mem_setMem]; exact hmid) (by decide)
  have hA0 : AgreesOutside m_mid s'.mem (esp s₀ + 0#64) 8 := by
    rw [hmem', BitVec.add_zero]
    exact (AgreesOutside.rfl' m_mid (esp s₀) 8).write64 (by bv_omega) (by decide)
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA0.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc_mid.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA0.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc_mid.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    ExpandSaved.of_agreesOutside_low hc_mid.saved hA0 (by decide),
    ExpandFrame.of_agreesOutside_esp hc_mid.frame hA0 (by decide)⟩

theorem HmacStGen.of_memcpy14_counter {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key tPrev info : List (BitVec 8)} {i : ℕ}
    (ht_len : tPrev.length = 32)
    (hinfo_len : info.length = 46)
    (hist : m₀.readBytes (esp s₀ + 128#64) 32 =
      shaStateBytes (F (hmacInnerInit F key) (tPrev ++ info.take 32)))
    (hcnt1 : m₀.read64 (esp s₀ + 160#64) = 2#64)
    (hout : m₀.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m₀.read64 (esp s₀ + 200#64) = 1#64) :
    let m₁ := m₀.writeBytes (esp s₀ + 64#64) (info.drop 32)
    let c := BitVec.ofNat 8 (i + 1)
    let m₂ :=
      ((m₁.write8 (esp s₀ + 240#64) c).write8 (esp s₀ + 78#64) c).write8 (esp s₀ + 127#64) 15#8
    HmacStGen m₂ (esp s₀ + 64#64) F key (tPrev ++ info.take 32) (info.drop 32 ++ [c]) := by
  intro m₁ c m₂
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by simp [ht_len, hinfo_len]
  have hdrop_len : (info.drop 32).length = 14 := by simp [hinfo_len]
  have hrem_len : (info.drop 32 ++ [c]).length = 15 := by simp [hdrop_len]
  have hA1 : AgreesOutside m₀ m₁ (esp s₀ + 64#64) 14 :=
    agreesOutside_writeBytes_le m₀ (esp s₀ + 64#64) (info.drop 32) 14 (by rw [hdrop_len])
  have hag_w : AgreesOutside m₁ m₂ (esp s₀ + 78#64) 163 := by
    dsimp only [m₂]
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    exact AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega)
  refine ⟨by rw [hblk_len], by rw [hblk_len]; decide, by rw [hrem_len]; decide,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrem_len, show (15 : ℕ) = 14 + 1 from rfl,
        Bytes.readBytes_add m₂ (esp s₀ + 64#64) 14 1,
        show esp s₀ + 64#64 + BitVec.ofNat 64 14 = esp s₀ + 78#64 by bv_lin]
    have h_drop : m₂.readBytes (esp s₀ + 64#64) 14 = info.drop 32 := by
      refine (hag_w.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
      dsimp only [m₁]
      have h := Bytes.readBytes_writeBytes_same m₀ (esp s₀ + 64#64) (info.drop 32) (by omega)
      rwa [hdrop_len] at h
    have h_c : m₂.readBytes (esp s₀ + 78#64) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_drop, h_c]
  · rw [hrem_len, show esp s₀ + 64#64 + 0x3f#64 = esp s₀ + 127#64 by bv_lin]
    dsimp only [m₂]
    exact Memory.read8_write8_same _ _ _
  · rw [show esp s₀ + 64#64 + 0x40#64 = esp s₀ + 128#64 by bv_lin,
        chunks64_single hblk_len, List.foldl]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hist
  · rw [show esp s₀ + 64#64 + 0x60#64 = esp s₀ + 160#64 by bv_lin, hblk_len]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hcnt1
  · rw [show esp s₀ + 64#64 + 0x68#64 = esp s₀ + 168#64 by bv_lin]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hout
  · rw [show esp s₀ + 64#64 + 0x88#64 = esp s₀ + 200#64 by bv_lin]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hcnt2

theorem HmacStGen.of_copy_esp_64_240 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    (hsrc : HmacStGen m₀ (esp s₀ + 64#64) F key blocks rem)
    (h0   : m.read64 (esp s₀ + 240#64) = m₀.read64 (esp s₀ + 64#64))
    (h8   : m.read64 (esp s₀ + 248#64) = m₀.read64 (esp s₀ + 72#64))
    (h16  : m.read64 (esp s₀ + 256#64) = m₀.read64 (esp s₀ + 80#64))
    (h24  : m.read64 (esp s₀ + 264#64) = m₀.read64 (esp s₀ + 88#64))
    (h32  : m.read64 (esp s₀ + 272#64) = m₀.read64 (esp s₀ + 96#64))
    (h40  : m.read64 (esp s₀ + 280#64) = m₀.read64 (esp s₀ + 104#64))
    (h48  : m.read64 (esp s₀ + 288#64) = m₀.read64 (esp s₀ + 112#64))
    (h56  : m.read64 (esp s₀ + 296#64) = m₀.read64 (esp s₀ + 120#64))
    (h64  : m.read64 (esp s₀ + 304#64) = m₀.read64 (esp s₀ + 128#64))
    (h72  : m.read64 (esp s₀ + 312#64) = m₀.read64 (esp s₀ + 136#64))
    (h80  : m.read64 (esp s₀ + 320#64) = m₀.read64 (esp s₀ + 144#64))
    (h88  : m.read64 (esp s₀ + 328#64) = m₀.read64 (esp s₀ + 152#64))
    (h96  : m.read64 (esp s₀ + 336#64) = m₀.read64 (esp s₀ + 160#64))
    (h104 : m.read64 (esp s₀ + 344#64) = m₀.read64 (esp s₀ + 168#64))
    (h112 : m.read64 (esp s₀ + 352#64) = m₀.read64 (esp s₀ + 176#64))
    (h120 : m.read64 (esp s₀ + 360#64) = m₀.read64 (esp s₀ + 184#64))
    (h128 : m.read64 (esp s₀ + 368#64) = m₀.read64 (esp s₀ + 192#64))
    (h136 : m.read64 (esp s₀ + 376#64) = m₀.read64 (esp s₀ + 200#64)) :
    HmacStGen m (esp s₀ + 240#64) F key blocks rem :=
  HmacStGen.of_copy_19 hsrc h0
    (read64_add_off h8)
    (read64_add_off h16)
    (read64_add_off h24)
    (read64_add_off h32)
    (read64_add_off h40)
    (read64_add_off h48)
    (read64_add_off h56)
    (read64_add_off h64)
    (read64_add_off h72)
    (read64_add_off h80)
    (read64_add_off h88)
    (read64_add_off h96)
    (read64_add_off h104)
    (read64_add_off h112)
    (read64_add_off h120)
    (read64_add_off h128)
    (read64_add_off h136)


end CryptoVerification.E2E.Pqxdh.ResponderCore

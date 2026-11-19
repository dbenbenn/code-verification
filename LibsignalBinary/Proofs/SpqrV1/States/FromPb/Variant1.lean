/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Jump-Table Dispatch and Variant 0 (`KeysUnsampled`)

Proves:
- `states_from_pb_dispatch_tagged`: jump-table dispatch (`+36 -> target`) for tagged variants
- `states_from_pb_dispatch_ct1Sampled`: jump-table dispatch (`+36 -> +1056`) for niche `ct1Sampled`
- `states_from_pb_keysUnsampled_ok_ext`: Variant 0 (`InnerState.keysUnsampled`) proof
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Jump-Table Decomposition (`0x8242e`) and Dispatch (`+36 -> target`) -/

/-- Unpacked 11-entry (`22`-byte) `.rodata` half-word jump table at `roBase` (`b + 0xa142e#64`). -/
@[expose] def statesFromPbJumpTableBytesAt (roBase : BitVec 64) : SepProp :=
  (roBase ↦₁₆ᵣ 0x0000#16) ∗ ((roBase + 2#64) ↦₁₆ᵣ 0x00ed#16) ∗
  ((roBase + 4#64) ↦₁₆ᵣ 0x0058#16) ∗ ((roBase + 6#64) ↦₁₆ᵣ 0x0086#16) ∗
  ((roBase + 8#64) ↦₁₆ᵣ 0x0017#16) ∗ ((roBase + 10#64) ↦₁₆ᵣ 0x0129#16) ∗
  ((roBase + 12#64) ↦₁₆ᵣ 0x0147#16) ∗ ((roBase + 14#64) ↦₁₆ᵣ 0x00e1#16) ∗
  ((roBase + 16#64) ↦₁₆ᵣ 0x0192#16) ∗ ((roBase + 18#64) ↦₁₆ᵣ 0x0048#16) ∗
  ((roBase + 20#64) ↦₁₆ᵣ 0x0171#16)

/-- Tag-to-target-offset table for the 10 tagged `V1State.InnerState` variants. -/
inductive TaggedVariantDispatch : BitVec 64 → BitVec 64 → Prop
  | keysUnsampled : TaggedVariantDispatch 0x8000000000000000#64 156#64
  | keysSampled : TaggedVariantDispatch 0x8000000000000001#64 1104#64
  | headerSent : TaggedVariantDispatch 0x8000000000000002#64 508#64
  | ct1Received : TaggedVariantDispatch 0x8000000000000003#64 692#64
  | ekSentCt1Received : TaggedVariantDispatch 0x8000000000000004#64 248#64
  | noHeaderReceived : TaggedVariantDispatch 0x8000000000000005#64 1344#64
  | headerReceived : TaggedVariantDispatch 0x8000000000000006#64 1464#64
  | ekReceivedCt1Sampled : TaggedVariantDispatch 0x8000000000000008#64 1764#64
  | ct1Acknowledged : TaggedVariantDispatch 0x8000000000000009#64 444#64
  | ct2Sampled : TaggedVariantDispatch 0x800000000000000a#64 1632#64

theorem vecU8Payload_zero (A : RustAlloc) :
    emp ⊢ vecU8Payload A 0#64 1#64 [] := by
  unfold vecU8Payload
  simp only [List.length_nil, BitVec.toNat_ofNat, Nat.zero_mod, Nat.le_refl, ↓reduceIte]
  exact Entails.pure_right ⟨trivial, by decide, by decide⟩ (Entails.refl _)

theorem vecU8Payload_pos (A : RustAlloc) (p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8Payload A (BitVec.ofNat 64 bs.length) p' bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8Payload
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

theorem cap_ne_zero_of_pos {cap : BitVec 64} {n : Nat} (hpos : 0 < n) (hle : n ≤ cap.toNat) :
    cap ≠ 0#64 := by
  intro h
  subst h
  change n ≤ 0 at hle
  omega

/-- Complete 928-byte output layout of `out` (`x19`) after the shared `Ok` epilogue (`+8180..+8496`). -/
@[expose] def epilogueOutFull (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : BitVec 64)
    (b96 : BitVec 8) (d97 : BitVec 32) (h101 : BitVec 16) (b103 : BitVec 8)
    (w104 w112 : BitVec 64) (b120 : BitVec 8) (w121 w128 w136 : BitVec 64) (b144 : BitVec 8)
    (q145 : BitVec 128) (w160 : BitVec 64)
    (q168 q184 q200 q216 q232 q248 q264 q280 q296 q312 q328 q344 q360 q376 : BitVec 128)
    (w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8))
    (q888 q904 : BitVec 128) (w920 : BitVec 64) : SepProp :=
  (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
  ((out + 32#64) ↦₆₄ w32) ∗ ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗ ((out + 56#64) ↦₆₄ w56) ∗
  ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗ ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
  ((out + 96#64) ↦₈ b96) ∗ ((out + 97#64) ↦₃₂ d97) ∗ ((out + 101#64) ↦₁₆ h101) ∗ ((out + 103#64) ↦₈ b103) ∗
  ((out + 104#64) ↦₆₄ w104) ∗ ((out + 112#64) ↦₆₄ w112) ∗
  ((out + 120#64) ↦₈ b120) ∗ ((out + 121#64) ↦₆₄ w121) ∗
  ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗
  ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₈ b144) ∗
  ((out + 145#64) ↦₆₄ q145.extractLsb' 0 64) ∗
  ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q145.extractLsb' 64 64)) ∗
  ((out + 160#64) ↦₆₄ w160) ∗
  ((out + 168#64) ↦₁₂₈ q168) ∗ ((out + 184#64) ↦₁₂₈ q184) ∗
  ((out + 200#64) ↦₁₂₈ q200) ∗ ((out + 216#64) ↦₁₂₈ q216) ∗
  ((out + 232#64) ↦₁₂₈ q232) ∗ ((out + 248#64) ↦₁₂₈ q248) ∗
  ((out + 264#64) ↦₁₂₈ q264) ∗ ((out + 280#64) ↦₁₂₈ q280) ∗
  ((out + 296#64) ↦₁₂₈ q296) ∗ ((out + 312#64) ↦₁₂₈ q312) ∗
  ((out + 328#64) ↦₁₂₈ q328) ∗ ((out + 344#64) ↦₁₂₈ q344) ∗
  ((out + 360#64) ↦₁₂₈ q360) ∗ ((out + 376#64) ↦₁₂₈ q376) ∗
  ((out + 392#64) ↦₆₄ w392) ∗ ((out + 400#64) ↦₆₄ w400) ∗
  ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗
  ((out + 424#64) ↦₆₄ w424) ∗ ((out + 432#64) ↦₆₄ w432) ∗
  ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗
  ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
  ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗
  ((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗
  ((out + 504#64) ↦₆₄ w504) ∗ ((out + 512#64) ↦₆₄ w512) ∗
  ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
  ((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
  ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗
  ((out + 560#64) ↦ₛ bs240) ∗
  ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗
  ((out + 920#64) ↦₆₄ w920)

theorem memRegion_15_entails_loBytes7_and_64_at (a o1 o2 : BitVec 64)
    (ho : o1 + 7#64 = o2 := by rfl) :
    ProofLib.memRegion (a + o1) 15 ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗
      (∃∗ u7 : BitVec 64, ((a + o2) ↦₆₄ u7)) := by
  have h := memRegion_15_entails_loBytes7_and_64 (a + o1)
  have ha : (a + o1) + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  rwa [ha] at h

theorem stackAt_encoderFromPb_split_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack :=
  ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)

/-- Active stack slots in `[fsp .. fsp + 2304)` read by the shared `Ok` epilogue (`+8180..+8496`). -/
@[expose] def epilogueStackSlots (fsp : BitVec 64)
    (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8))
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) : SepProp :=
  ((fsp + 92#64) ↦₃₂ d92) ∗
  ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
  ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
  ((fsp + 208#64) ↦₆₄ w208) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
  ((fsp + 240#64) ↦ₛ bs240) ∗
  ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
  ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
  ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
  ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
  ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
  ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
  ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
  ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
  ((fsp + 832#64) ↦₆₄ w832) ∗
  ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
  ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
  ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
  ((fsp + 1920#64) ↦₆₄ w1920)

/-- Unused stack regions in `[fsp .. fsp + 2304)` around `epilogueStackSlots`. -/
@[expose] def epilogueStackGaps (fsp : BitVec 64) : SepProp :=
  memRegion fsp 92 ∗
  memRegion (fsp + 96#64) 8 ∗
  memRegion (fsp + 128#64) 32 ∗
  memRegion (fsp + 168#64) 4 ∗
  memRegion (fsp + 176#64) 16 ∗
  memRegion (fsp + 200#64) 8 ∗
  memRegion (fsp + 216#64) 8 ∗
  memRegion (fsp + 568#64) 8 ∗
  memRegion (fsp + 599#64) 9 ∗
  memRegion (fsp + 840#64) 8 ∗
  memRegion (fsp + 871#64) 9 ∗
  memRegion (fsp + 895#64) 993 ∗
  memRegion (fsp + 1928#64) 376

theorem bs328_entails_memRegion_328 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 328) :
    (a ↦ₛ bs) ⊢ memRegion a 328 :=
  h ▸ ProofLib.pointsToBytes_entails_memRegion a bs

/-- Collapse the post-Step-C stack frame at `+64` back into `memRegion fsp 2304`. -/
theorem epilogueStackPost_entails_2304 (fsp : BitVec 64)
    (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) :
    memRegion fsp 92 ∗
    ((fsp + 92#64) ↦₃₂ d92) ∗
    memRegion (fsp + 96#64) 8 ∗
    ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
    memRegion (fsp + 128#64) 32 ∗
    ((fsp + 160#64) ↦₆₄ w160) ∗
    memRegion (fsp + 168#64) 4 ∗
    ((fsp + 172#64) ↦₃₂ d172) ∗
    memRegion (fsp + 176#64) 16 ∗
    ((fsp + 192#64) ↦₆₄ w192) ∗
    memRegion (fsp + 200#64) 8 ∗
    ((fsp + 208#64) ↦₆₄ w208) ∗
    memRegion (fsp + 216#64) 8 ∗
    ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
    ((fsp + 240#64) ↦ₛ bs240) ∗
    memRegion (fsp + 568#64) 8 ∗
    (((fsp + 576#64) ↦₆₄ q576.extractLsb' 0 64) ∗
     ((fsp + 584#64) ↦ₛ EncoderFromPb.loBytes7 (q576.extractLsb' 64 64)) ∗
     ((fsp + 591#64) ↦₆₄ overlapWord7 (q576.extractLsb' 64 64) w592)) ∗
    memRegion (fsp + 599#64) 9 ∗
    ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
    ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
    ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
    ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
    ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
    ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
    ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
    ((fsp + 832#64) ↦₆₄ w832) ∗
    memRegion (fsp + 840#64) 8 ∗
    (((fsp + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
     ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
     ((fsp + 863#64) ↦₆₄ overlapWord7 (q848.extractLsb' 64 64) w864)) ∗
    memRegion (fsp + 871#64) 9 ∗
    (((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
     ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888)) ∗
    memRegion (fsp + 895#64) 993 ∗
    ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
    ((fsp + 1920#64) ↦₆₄ w1920) ∗
    memRegion (fsp + 1928#64) 376 ⊢
    memRegion fsp 2304 := by
  have h576 : ((fsp + 576#64) ↦₆₄ q576.extractLsb' 0 64) ∗
      ((fsp + 584#64) ↦ₛ EncoderFromPb.loBytes7 (q576.extractLsb' 64 64)) ∗
      ((fsp + 591#64) ↦₆₄ overlapWord7 (q576.extractLsb' 64 64) w592) ⊢
      memRegion (fsp + 576#64) 23 := by
    have h := mid128_overlapWord7_entails_memRegion_23 (fsp + 576#64) q576 w592
    have ha1 : fsp + 576#64 + 8#64 = fsp + 584#64 := by bv_omega
    have ha2 : fsp + 576#64 + 15#64 = fsp + 591#64 := by bv_omega
    rwa [ha1, ha2] at h
  have h848 : ((fsp + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 (q848.extractLsb' 64 64) w864) ⊢
      memRegion (fsp + 848#64) 23 := by
    have h := mid128_overlapWord7_entails_memRegion_23 (fsp + 848#64) q848 w864
    have ha1 : fsp + 848#64 + 8#64 = fsp + 856#64 := by bv_omega
    have ha2 : fsp + 848#64 + 15#64 = fsp + 863#64 := by bv_omega
    rwa [ha1, ha2] at h
  have h880 : ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) ⊢
      memRegion (fsp + 880#64) 15 := by
    have h := loBytes7_overlapWord7_entails_memRegion_15 (fsp + 880#64) w880 w888
    have ha : fsp + 880#64 + 7#64 = fsp + 887#64 := by bv_omega
    rwa [ha] at h
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <| collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (bs328_entails_memRegion_328 _ bs240 hbs240) <|
    collapse_step (Entails.refl _) <| collapse_step h576 <| collapse_step (Entails.refl _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step h848 <| collapse_step (Entails.refl _) <| collapse_step h880 <| collapse_step (Entails.refl _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

/-- Split `memRegion out 928` into the 8 regional blocks consumed by Steps A, B, and C. -/
theorem memRegion_out_928_split_8 (out : BitVec 64) :
    memRegion out chunkedStatesSize ⊢
      memRegion out 103 ∗
      memRegion (out + 103#64) 42 ∗
      memRegion (out + 145#64) 16 ∗
      memRegion (out + 161#64) 7 ∗
      memRegion (out + 168#64) 96 ∗
      memRegion (out + 264#64) 128 ∗
      memRegion (out + 392#64) 168 ∗
      memRegion (out + 560#64) 368 := by
  exact split_top <|
    split_step0 (Entails.refl _) <| split_step (Entails.refl _) <| split_step (Entails.refl _) <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <| split_step (Entails.refl _) <|
    split_step (Entails.refl _) <| Entails.refl _

@[expose] def epilogueOutPartANo145 (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : BitVec 64)
    (b96 : BitVec 8) (d97 : BitVec 32) (h101 : BitVec 16)
    (q264 q280 q296 q312 q328 q344 q360 q376 : BitVec 128) : SepProp :=
  (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
  ((out + 32#64) ↦₆₄ w32) ∗ ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗ ((out + 56#64) ↦₆₄ w56) ∗
  ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗ ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
  ((out + 96#64) ↦₈ b96) ∗ ((out + 97#64) ↦₃₂ d97) ∗ ((out + 101#64) ↦₁₆ h101) ∗
  ((out + 264#64) ↦₁₂₈ q264) ∗ ((out + 280#64) ↦₁₂₈ q280) ∗
  ((out + 296#64) ↦₁₂₈ q296) ∗ ((out + 312#64) ↦₁₂₈ q312) ∗
  ((out + 328#64) ↦₁₂₈ q328) ∗ ((out + 344#64) ↦₁₂₈ q344) ∗
  ((out + 360#64) ↦₁₂₈ q360) ∗ ((out + 376#64) ↦₁₂₈ q376)

theorem epilogueOutPartA_eq_no145 (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : BitVec 64)
    (b96 : BitVec 8) (d97 : BitVec 32) (h101 : BitVec 16)
    (q145 q264 q280 q296 q312 q328 q344 q360 q376 : BitVec 128) :
    epilogueOutPartA out w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88
      b96 d97 h101 q145 q264 q280 q296 q312 q328 q344 q360 q376 =
    epilogueOutPartANo145 out w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88
      b96 d97 h101 q264 q280 q296 q312 q328 q344 q360 q376 ∗
    ((out + 145#64) ↦₁₂₈ q145) := by
  unfold epilogueOutPartA epilogueOutPartANo145
  ac_rfl

theorem memRegion_out_partA_split (out : BitVec 64) :
    memRegion out 103 ∗ memRegion (out + 145#64) 16 ∗ memRegion (out + 264#64) 128 ⊢
      ((∃∗ u0 : BitVec 64, (out ↦₆₄ u0)) ∗
       (∃∗ u8 : BitVec 64, ((out + 8#64) ↦₆₄ u8)) ∗
       (∃∗ u16 : BitVec 64, ((out + 16#64) ↦₆₄ u16)) ∗
       (∃∗ u24 : BitVec 64, ((out + 24#64) ↦₆₄ u24)) ∗
       (∃∗ u32 : BitVec 64, ((out + 32#64) ↦₆₄ u32)) ∗
       (∃∗ u40 : BitVec 64, ((out + 40#64) ↦₆₄ u40)) ∗
       (∃∗ u48 : BitVec 64, ((out + 48#64) ↦₆₄ u48)) ∗
       (∃∗ u56 : BitVec 64, ((out + 56#64) ↦₆₄ u56)) ∗
       (∃∗ u64 : BitVec 64, ((out + 64#64) ↦₆₄ u64)) ∗
       (∃∗ u72 : BitVec 64, ((out + 72#64) ↦₆₄ u72)) ∗
       (∃∗ u80 : BitVec 64, ((out + 80#64) ↦₆₄ u80)) ∗
       (∃∗ u88 : BitVec 64, ((out + 88#64) ↦₆₄ u88)) ∗
       (∃∗ ub96 : BitVec 8, ((out + 96#64) ↦₈ ub96)) ∗
       (∃∗ ud97 : BitVec 32, ((out + 97#64) ↦₃₂ ud97)) ∗
       (∃∗ uh101 : BitVec 16, ((out + 101#64) ↦₁₆ uh101))) ∗
      (∃∗ uq145 : BitVec 128, ((out + 145#64) ↦₁₂₈ uq145)) ∗
      ((∃∗ uq264 : BitVec 128, ((out + 264#64) ↦₁₂₈ uq264)) ∗
       (∃∗ uq280 : BitVec 128, ((out + 280#64) ↦₁₂₈ uq280)) ∗
       (∃∗ uq296 : BitVec 128, ((out + 296#64) ↦₁₂₈ uq296)) ∗
       (∃∗ uq312 : BitVec 128, ((out + 312#64) ↦₁₂₈ uq312)) ∗
       (∃∗ uq328 : BitVec 128, ((out + 328#64) ↦₁₂₈ uq328)) ∗
       (∃∗ uq344 : BitVec 128, ((out + 344#64) ↦₁₂₈ uq344)) ∗
       (∃∗ uq360 : BitVec 128, ((out + 360#64) ↦₁₂₈ uq360)) ∗
       (∃∗ uq376 : BitVec 128, ((out + 376#64) ↦₁₂₈ uq376))) := by
  refine sepConj_mono ?_ (sepConj_mono (mem128_entails (out + 145#64)) ?_)
  · exact split_top <|
      split_step0 (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem8_entails _) <| split_step (mem32_entails _) <| mem16_entails _
  · exact split_top <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| mem128_entails _

theorem memRegion_out_partB_split (out : BitVec 64) (q848 : BitVec 128) :
    memRegion (out + 103#64) 42 ∗
      (((out + 145#64) ↦₁₂₈ q848) ∗ memRegion (out + 161#64) 7) ∗
      memRegion (out + 168#64) 96 ∗
      memRegion (out + 392#64) 168 ⊢
      ((∃∗ ub103 : BitVec 8, ((out + 103#64) ↦₈ ub103)) ∗
       (∃∗ u104 : BitVec 64, ((out + 104#64) ↦₆₄ u104)) ∗
       (∃∗ u112 : BitVec 64, ((out + 112#64) ↦₆₄ u112)) ∗
       (∃∗ ub120 : BitVec 8, ((out + 120#64) ↦₈ ub120)) ∗
       ((∃∗ u121 : BitVec 64, ((out + 121#64) ↦ₛ EncoderFromPb.loBytes7 u121)) ∗
        (∃∗ u128 : BitVec 64, ((out + 128#64) ↦₆₄ u128))) ∗
       (∃∗ u136 : BitVec 64, ((out + 136#64) ↦₆₄ u136)) ∗
       (∃∗ ub144 : BitVec 8, ((out + 144#64) ↦₈ ub144))) ∗
      (∃∗ u160 : BitVec 64, ((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
        ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗ ((out + 160#64) ↦₆₄ u160)) ∗
      ((∃∗ uq168 : BitVec 128, ((out + 168#64) ↦₁₂₈ uq168)) ∗ (∃∗ uq184 : BitVec 128, ((out + 184#64) ↦₁₂₈ uq184)) ∗
       (∃∗ uq200 : BitVec 128, ((out + 200#64) ↦₁₂₈ uq200)) ∗ (∃∗ uq216 : BitVec 128, ((out + 216#64) ↦₁₂₈ uq216)) ∗
       (∃∗ uq232 : BitVec 128, ((out + 232#64) ↦₁₂₈ uq232)) ∗ (∃∗ uq248 : BitVec 128, ((out + 248#64) ↦₁₂₈ uq248))) ∗
      ((∃∗ u392 : BitVec 64, ((out + 392#64) ↦₆₄ u392)) ∗ (∃∗ u400 : BitVec 64, ((out + 400#64) ↦₆₄ u400)) ∗
       (∃∗ u408 : BitVec 64, ((out + 408#64) ↦₆₄ u408)) ∗ (∃∗ u416 : BitVec 64, ((out + 416#64) ↦₆₄ u416)) ∗
       (∃∗ u424 : BitVec 64, ((out + 424#64) ↦₆₄ u424)) ∗ (∃∗ u432 : BitVec 64, ((out + 432#64) ↦₆₄ u432)) ∗
       (∃∗ u440 : BitVec 64, ((out + 440#64) ↦₆₄ u440)) ∗ (∃∗ u448 : BitVec 64, ((out + 448#64) ↦₆₄ u448)) ∗
       (∃∗ u456 : BitVec 64, ((out + 456#64) ↦₆₄ u456)) ∗ (∃∗ u464 : BitVec 64, ((out + 464#64) ↦₆₄ u464)) ∗
       (∃∗ u472 : BitVec 64, ((out + 472#64) ↦₆₄ u472)) ∗ (∃∗ u480 : BitVec 64, ((out + 480#64) ↦₆₄ u480)) ∗
       (∃∗ u488 : BitVec 64, ((out + 488#64) ↦₆₄ u488)) ∗ (∃∗ u496 : BitVec 64, ((out + 496#64) ↦₆₄ u496)) ∗
       (∃∗ u504 : BitVec 64, ((out + 504#64) ↦₆₄ u504)) ∗ (∃∗ u512 : BitVec 64, ((out + 512#64) ↦₆₄ u512)) ∗
       (∃∗ u520 : BitVec 64, ((out + 520#64) ↦₆₄ u520)) ∗ (∃∗ u528 : BitVec 64, ((out + 528#64) ↦₆₄ u528)) ∗
       (∃∗ ub536 : BitVec 8, ((out + 536#64) ↦₈ ub536)) ∗ (∃∗ u537 : BitVec 64, ((out + 537#64) ↦₆₄ u537)) ∗
       ((∃∗ u545 : BitVec 64, ((out + 545#64) ↦ₛ EncoderFromPb.loBytes7 u545)) ∗
        (∃∗ u552 : BitVec 64, ((out + 552#64) ↦₆₄ u552)))) := by
  refine sepConj_mono ?_ (sepConj_mono (out_145_168_realign out q848) (sepConj_mono ?_ ?_))
  · exact split_top <|
      split_step (mem8_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem8_entails _) <| split_step (memRegion_15_entails_loBytes7_and_64_at out _ _) <|
      split_step (mem64_entails _) <| mem8_entails _
  · exact split_top <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <| mem128_entails _
  · exact split_top <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem8_entails _) <| split_step (mem64_entails _) <|
      memRegion_15_entails_loBytes7_and_64_at out _ _

theorem memRegion_out_partC_split (out : BitVec 64) :
    memRegion (out + 560#64) 368 ⊢
      memRegion (out + 560#64) 328 ∗ (∃∗ uq888 : BitVec 128, ((out + 888#64) ↦₁₂₈ uq888)) ∗
      (∃∗ uq904 : BitVec 128, ((out + 904#64) ↦₁₂₈ uq904)) ∗ (∃∗ u920 : BitVec 64, ((out + 920#64) ↦₆₄ u920)) := by
  exact split_top <|
    split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| mem64_entails _

theorem epilogueOut_tail_888_entails_40 (out : BitVec 64)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920) ⊢
    memRegion (out + 888#64) 40 := by
  exact collapse_top <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem epilogueOut_tail_536_entails_392 (out : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    ((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
    ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
    ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920) ⊢
    memRegion (out + 536#64) 392 := by
  exact collapse_top <|
    collapse_step (pointsTo8_entails_memRegion _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (hiBytes7_entails_memRegion_7 _ _) <|
    collapse_step (bs328_entails_memRegion_328 _ bs240 hbs240) <|
    epilogueOut_tail_888_entails_40 out q888 q904 w920

theorem epilogueOut_tail_512_entails_416 (out : BitVec 64)
    (w512 w520 w528 : BitVec 64) (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    ((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
    (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
     ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
     ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920)) ⊢
    memRegion (out + 512#64) 416 := by
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    epilogueOut_tail_536_entails_392 out b536 q537 w552 bs240 hbs240 q888 q904 w920

theorem epilogueOut_tail_488_entails_440 (out : BitVec 64)
    (w488 w496 w504 w512 w520 w528 : BitVec 64) (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    ((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗ ((out + 504#64) ↦₆₄ w504) ∗
    (((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
     (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
      ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920))) ⊢
    memRegion (out + 488#64) 440 := by
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    epilogueOut_tail_512_entails_416 out w512 w520 w528 b536 q537 w552 bs240 hbs240 q888 q904 w920

theorem epilogueOut_tail_464_entails_464 (out : BitVec 64)
    (w464 w472 w480 w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    ((out + 464#64) ↦₆₄ w464) ∗ ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗
    (((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗ ((out + 504#64) ↦₆₄ w504) ∗
     (((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
      (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
       ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
       ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920)))) ⊢
    memRegion (out + 464#64) 464 := by
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    epilogueOut_tail_488_entails_440 out w488 w496 w504 w512 w520 w528 b536 q537 w552 bs240 hbs240 q888 q904 w920

theorem epilogueOutFull_entails_64_864 (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : BitVec 64)
    (b96 : BitVec 8) (d97 : BitVec 32) (h101 : BitVec 16) (b103 : BitVec 8)
    (w104 w112 : BitVec 64) (b120 : BitVec 8) (w121 w128 w136 : BitVec 64) (b144 : BitVec 8)
    (q145 : BitVec 128) (w160 : BitVec 64)
    (q168 q184 q200 q216 q232 q248 q264 q280 q296 q312 q328 q344 q360 q376 : BitVec 128)
    (w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88
      b96 d97 h101 b103 w104 w112 b120 w121 w128 w136 b144 q145 w160
      q168 q184 q200 q216 q232 q248 q264 q280 q296 q312 q328 q344 q360 q376
      w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528
      b536 q537 w552 bs240 q888 q904 w920 ⊢
    (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
    ((out + 32#64) ↦₆₄ w32) ∗ ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗ ((out + 56#64) ↦₆₄ w56) ∗
    memRegion (out + 64#64) 864 := by
  unfold epilogueOutFull
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))))
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo8_entails_memRegion _ _) <| collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (pointsTo16_entails_memRegion_2 _ _) <| collapse_step (pointsTo8_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo8_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (hiBytes7_entails_memRegion_7 _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo8_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (loBytes7_entails_memRegion_7 _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (pointsTo128_entails_memRegion_16 _ _) <| collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    epilogueOut_tail_464_entails_464 out w464 w472 w480 w488 w496 w504 w512 w520 w528
      b536 q537 w552 bs240 hbs240 q888 q904 w920

theorem fsp_848_871_realign_eq (fsp : BitVec 64) (q848 : BitVec 128) (w864 : BitVec 64) :
    ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) =
      ((fsp + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 (q848.extractLsb' 64 64) w864) := by
  have h := pointsTo128_loBytes7_eq (fsp + 848#64) q848 w864
  have ha16 : fsp + 848#64 + 16#64 = fsp + 864#64 := by bv_omega
  have ha8 : fsp + 848#64 + 8#64 = fsp + 856#64 := by bv_omega
  have ha15 : fsp + 848#64 + 15#64 = fsp + 863#64 := by bv_omega
  rwa [ha16, ha8, ha15] at h

theorem fsp_880_895_realign_eq (fsp w880 w888 : BitVec 64) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 880#64) w880 w888
  have ha8 : fsp + 880#64 + 8#64 = fsp + 888#64 := by bv_omega
  have ha7 : fsp + 880#64 + 7#64 = fsp + 887#64 := by bv_omega
  rwa [ha8, ha7] at h

theorem epilogueStackPartA_realign_eq (fsp w208 w864 w880 w888 : BitVec 64)
    (q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128) :
    (epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864)) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) =
    ((fsp + 208#64) ↦₆₄ w208) ∗
      ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
      ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
      ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
      ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
      (((fsp + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
       ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
       ((fsp + 863#64) ↦₆₄ overlapWord7 (q848.extractLsb' 64 64) w864)) ∗
      (((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
       ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888)) := by
  unfold epilogueStackPartA
  rw [← fsp_848_871_realign_eq fsp q848 w864, ← fsp_880_895_realign_eq fsp w880 w888]
  ac_rfl

theorem sp_sub_2400_align (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 2400#64) &&& 15#64 == 0#64) = true := by bv_kernel

end CryptoVerification.SpqrV1.States.FromPb


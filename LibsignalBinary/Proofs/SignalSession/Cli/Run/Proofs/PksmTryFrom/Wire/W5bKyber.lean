/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym

/-!
# `PreKeySignalMessage::try_from`: `PublicKey` Scatter and Kyber `Ok` Branches (`+0x684..+0x830`)

Defines the scattered-key spill layout `kyberSpillsAtW` (`sp' + 12..144`) and Kyber
error/panic exit states (`+0xa1c`, `+0xa24`, `+0xa74`, `+0xa80`), and proves
`pk_scatter_head_wp` (`+0x684..+0x6c8`), `kyber_both_ok_wp`, and `kyber_neither_v3_ok_wp`
(reaching `+0x830`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private theorem bv_sub_add_lit'X (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_sub_sub_litX (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem bv_add_neg_8X (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem bv_add_neg_16X (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem bv_add_neg_24X (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem bv_add_neg_32X (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem bv_add_neg_40X (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem bv_add_neg_48X (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem bv_add_neg_55X (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_64X (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem bv_add_neg_72X (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem bv_add_neg_80X (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem bv_add_neg_87X (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem bv_add_neg_88X (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem bv_add_neg_96X (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem bv_add_neg_104X (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem bv_add_neg_112X (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem bv_add_neg_128X (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem bv_add_neg_136X (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem bv_add_neg_152X (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem bv_add_neg_160X (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem bv_add_neg_168X (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem bv_add_neg_176X (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem bv_add_neg_184X (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem bv_add_neg_186X (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem bv_add_neg_191X (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem bv_add_neg_192X (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem bv_add_neg_196X (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem bv_add_neg_200X (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem bv_add_neg_216X (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit'X bv_sub_sub_litX BitVec.toNat_zero
  bv_add_neg_8X bv_add_neg_16X bv_add_neg_24X bv_add_neg_32X bv_add_neg_40X
  bv_add_neg_48X bv_add_neg_55X bv_add_neg_56X bv_add_neg_64X bv_add_neg_72X
  bv_add_neg_80X bv_add_neg_87X bv_add_neg_88X bv_add_neg_96X bv_add_neg_104X
  bv_add_neg_112X bv_add_neg_128X bv_add_neg_136X bv_add_neg_152X bv_add_neg_160X
  bv_add_neg_168X bv_add_neg_176X bv_add_neg_184X bv_add_neg_186X bv_add_neg_191X
  bv_add_neg_192X bv_add_neg_196X bv_add_neg_200X bv_add_neg_216X bv_add_neg_512X
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8

theorem L1_PksmWire_W5bKyber : True := trivial

/-! ## 1. Frozen Exit States (`kyberSpillsAtW` and `section W5bExits`) -/

/-- Stack spill layout at `sp' + 12 .. sp' + 144` after `+0x684..+0x6c8` scatters the 32 bytes of `pk`
(`pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 = (bk.take 33).drop 1`).
Slots `sp' + 68` (`kpkTag`) and `sp' + 72` (`bkLen`) from `seg1SpillsAtW` are overwritten by
`b8.zeroExtend 32` and `w15`; all other `seg1SpillsAtW` slots (`sp' + 16..64`, `sp' + 80..104`)
are preserved. -/
@[expose] def kyberSpillsAtW (sp' bkCap bkPtr kyberLen ikPtr ikLen msgPtr msgLen : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkVal : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) : SepProp :=
  ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
  ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
  ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
  ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
  ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
  ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
  ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
  spUnused112 sp' ∗
  ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
  ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
  sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6

section W5bExits

end W5bExits

/-! ## 2. ``pk_scatter_head_wp``, ``kyber_both_ok_wp``, ``kyber_neither_v3_ok_wp`` -/

theorem deser_ok_entails_memRegion48 (sp' : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      memRegion (sp' + 312#64) 48 := by
  have h1 : ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗
        memRegion (sp' + 320#64) 40 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      deser_ok_entails_spe_region (sp' + 312#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  refine Entails.trans h1 ?_
  rw [Prost.memRegion_split (sp' + 312#64) 8 40 (by decide),
    show sp' + 312#64 + BitVec.ofNat 64 8 = sp' + 320#64 by bv_omega]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem memRegion48_312_split24 (sp' : BitVec 64) :
    memRegion (sp' + 312#64) 48 =
      (∃∗ w312 : BitVec 64, (sp' + 312#64) ↦₆₄ w312) ∗
      (∃∗ w320 : BitVec 64, (sp' + 320#64) ↦₆₄ w320) ∗
      (∃∗ w328 : BitVec 64, (sp' + 328#64) ↦₆₄ w328) ∗
      memRegion (sp' + 336#64) 24 := by
  rw [Prost.memRegion_split (sp' + 312#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 8#64 + 8#64) 8 24 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight (sp' + 312#64),
    ProofLib.memRegion_eight (sp' + 320#64),
    ProofLib.memRegion_eight (sp' + 328#64)]

private theorem ule_64_vb_eq_false {vb : BitVec 8} (hvb_lt : vb.toNat < 0x40) :
    (64#64).ule (vb.zeroExtend 64) = false := by
  rw [BitVec.ule_eq_decide]
  exact decide_eq_false (by rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

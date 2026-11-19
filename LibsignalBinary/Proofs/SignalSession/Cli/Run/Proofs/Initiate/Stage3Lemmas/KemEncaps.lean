/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy

/-!
# Stage 3 KEM Seed Packing & `kyber::encapsulate` (`+0x0ee8 → +0x0fb4`)

Packs all 32 low coin bytes `(coinWord t i _).truncate 8` into `[fsp + 0xfe0 .. fsp + 0x1000)`,
folds `[fsp + 0xfe0 .. fsp + 0x1000)` to `(fsp + 0xfe0) ↦ₛ (initiateKemCoins t).toList`, collapses
scratch slots `[fsp .. fsp + 0x70)`, invokes `kyberEncaps_ok_at_init`, and splits the `1600`-byte
output at `fsp + 0x1600` into `(fsp + 0x1600) ↦ₛ ct.toList` and `(fsp + 0x1c20) ↦ₛ ss.toList`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem memRegion4_split1 (p : BitVec 64) :
    memRegion p 4 =
      (∃∗ b0, p ↦₈ b0) ∗ (∃∗ b1, (p + 1#64) ↦₈ b1) ∗
      (∃∗ b2, (p + 2#64) ↦₈ b2) ∗ (∃∗ b3, (p + 3#64) ↦₈ b3) := by
  rw [← memRegion_merge_at p 1 3 (p + 1#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 1#64) 1 2 (p + 2#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 2#64) 1 1 (p + 3#64) (by bv_omega) (by decide),
      ProofLib.memRegion_one, ProofLib.memRegion_one, ProofLib.memRegion_one, ProofLib.memRegion_one]

private theorem pack4_bytes_eq (p : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) =
      (p ↦ₛ [b0, b1, b2, b3]) := by
  rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_nil]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]

private theorem vec32_chunks4_eq (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get ⟨0, by decide⟩, v.get ⟨1, by decide⟩, v.get ⟨2, by decide⟩, v.get ⟨3, by decide⟩] ++
      ([v.get ⟨4, by decide⟩, v.get ⟨5, by decide⟩, v.get ⟨6, by decide⟩, v.get ⟨7, by decide⟩] ++
      ([v.get ⟨8, by decide⟩, v.get ⟨9, by decide⟩, v.get ⟨10, by decide⟩, v.get ⟨11, by decide⟩] ++
      ([v.get ⟨12, by decide⟩, v.get ⟨13, by decide⟩, v.get ⟨14, by decide⟩, v.get ⟨15, by decide⟩] ++
      ([v.get ⟨16, by decide⟩, v.get ⟨17, by decide⟩, v.get ⟨18, by decide⟩, v.get ⟨19, by decide⟩] ++
      ([v.get ⟨20, by decide⟩, v.get ⟨21, by decide⟩, v.get ⟨22, by decide⟩, v.get ⟨23, by decide⟩] ++
      ([v.get ⟨24, by decide⟩, v.get ⟨25, by decide⟩, v.get ⟨26, by decide⟩, v.get ⟨27, by decide⟩] ++
       [v.get ⟨28, by decide⟩, v.get ⟨29, by decide⟩, v.get ⟨30, by decide⟩, v.get ⟨31, by decide⟩])))))) := by
  apply List.ext_getElem
  · simp [v.toList_length]
  · intro i hi1 hi2
    have hi : i < 32 := by simpa [v.toList_length] using hi1
    simp only [List.Vector.get]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | rfl | omega

private theorem kemCoins32_pointsTo_eq (fsp : BitVec 64)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ((fsp + 0xfe0#64) ↦₈ (coinWord t 0 (by decide)).truncate 8) ∗
    ((fsp + 0xfe1#64) ↦₈ (coinWord t 1 (by decide)).truncate 8) ∗
    ((fsp + 0xfe2#64) ↦₈ (coinWord t 2 (by decide)).truncate 8) ∗
    ((fsp + 0xfe3#64) ↦₈ (coinWord t 3 (by decide)).truncate 8) ∗
    ((fsp + 0xfe4#64) ↦₈ (coinWord t 4 (by decide)).truncate 8) ∗
    ((fsp + 0xfe5#64) ↦₈ (coinWord t 5 (by decide)).truncate 8) ∗
    ((fsp + 0xfe6#64) ↦₈ (coinWord t 6 (by decide)).truncate 8) ∗
    ((fsp + 0xfe7#64) ↦₈ (coinWord t 7 (by decide)).truncate 8) ∗
    ((fsp + 0xfe8#64) ↦₈ (coinWord t 8 (by decide)).truncate 8) ∗
    ((fsp + 0xfe9#64) ↦₈ (coinWord t 9 (by decide)).truncate 8) ∗
    ((fsp + 0xfea#64) ↦₈ (coinWord t 10 (by decide)).truncate 8) ∗
    ((fsp + 0xfeb#64) ↦₈ (coinWord t 11 (by decide)).truncate 8) ∗
    ((fsp + 0xfec#64) ↦₈ (coinWord t 12 (by decide)).truncate 8) ∗
    ((fsp + 0xfed#64) ↦₈ (coinWord t 13 (by decide)).truncate 8) ∗
    ((fsp + 0xfee#64) ↦₈ (coinWord t 14 (by decide)).truncate 8) ∗
    ((fsp + 0xfef#64) ↦₈ (coinWord t 15 (by decide)).truncate 8) ∗
    ((fsp + 0xff0#64) ↦₈ (coinWord t 16 (by decide)).truncate 8) ∗
    ((fsp + 0xff1#64) ↦₈ (coinWord t 17 (by decide)).truncate 8) ∗
    ((fsp + 0xff2#64) ↦₈ (coinWord t 18 (by decide)).truncate 8) ∗
    ((fsp + 0xff3#64) ↦₈ (coinWord t 19 (by decide)).truncate 8) ∗
    ((fsp + 0xff4#64) ↦₈ (coinWord t 20 (by decide)).truncate 8) ∗
    ((fsp + 0xff5#64) ↦₈ (coinWord t 21 (by decide)).truncate 8) ∗
    ((fsp + 0xff6#64) ↦₈ (coinWord t 22 (by decide)).truncate 8) ∗
    ((fsp + 0xff7#64) ↦₈ (coinWord t 23 (by decide)).truncate 8) ∗
    ((fsp + 0xff8#64) ↦₈ (coinWord t 24 (by decide)).truncate 8) ∗
    ((fsp + 0xff9#64) ↦₈ (coinWord t 25 (by decide)).truncate 8) ∗
    ((fsp + 0xffa#64) ↦₈ (coinWord t 26 (by decide)).truncate 8) ∗
    ((fsp + 0xffb#64) ↦₈ (coinWord t 27 (by decide)).truncate 8) ∗
    ((fsp + 0xffc#64) ↦₈ (coinWord t 28 (by decide)).truncate 8) ∗
    ((fsp + 0xffd#64) ↦₈ (coinWord t 29 (by decide)).truncate 8) ∗
    ((fsp + 0xffe#64) ↦₈ (coinWord t 30 (by decide)).truncate 8) ∗
    ((fsp + 0xfff#64) ↦₈ (coinWord t 31 (by decide)).truncate 8) =
      ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) := by
  simp only [coinWord_truncate8]
  conv_rhs => rw [vec32_chunks4_eq (initiateKemCoins t)]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  dsimp only [List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  simp only [← pack4_bytes_eq, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem p32_4 {p0 p1 p2 p3 : BitVec 64} {w0 w1 w2 w3 : BitVec 32} {R R' : SepProp}
    (h : R ⊢ R') :
    (p0 ↦₃₂ w0) ∗ (p1 ↦₃₂ w1) ∗ (p2 ↦₃₂ w2) ∗ (p3 ↦₃₂ w3) ∗ R ⊢
      memRegion p0 4 ∗ memRegion p1 4 ∗ memRegion p2 4 ∗ memRegion p3 4 ∗ R' :=
  sepConj_mono (pointsTo32_entails_memRegion p0 w0)
    (sepConj_mono (pointsTo32_entails_memRegion p1 w1)
      (sepConj_mono (pointsTo32_entails_memRegion p2 w2)
        (sepConj_mono (pointsTo32_entails_memRegion p3 w3) h)))

private theorem mem4_elim_bytes {prog : Program} {ret : BitVec 64} {s : State}
    {p : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ u0 u1 u2 u3 : BitVec 8,
      SepWPp prog ret s
        (B ∗ ((p ↦₈ u0) ∗ ((p + 1#64) ↦₈ u1) ∗ ((p + 2#64) ↦₈ u2) ∗ ((p + 3#64) ↦₈ u3) ∗ R))
        Q Qp oom) :
    SepWPp prog ret s ((memRegion p 4 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, memRegion4_split1 p]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact sepWPp_exists_elim_oom fun u0 => sepWPp_exists_elim_oom fun u1 =>
    sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun u3 =>
      sepWPp_conseq_oom (by sep_frame) (h u3 u2 u1 u0)

private theorem scratch96_collapse (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
      w22 w23 : BitVec 32) :
    memRegion fsp 8 ∗
      ((fsp + 0x68#64) ↦₃₂ w0) ∗ ((fsp + 0x60#64) ↦₃₂ w1) ∗
      ((fsp + 0x5c#64) ↦₃₂ w2) ∗ ((fsp + 0x58#64) ↦₃₂ w3) ∗
      ((fsp + 0x54#64) ↦₃₂ w4) ∗ ((fsp + 0x50#64) ↦₃₂ w5) ∗
      ((fsp + 0x4c#64) ↦₃₂ w6) ∗ ((fsp + 0x48#64) ↦₃₂ w7) ∗
      ((fsp + 0x44#64) ↦₃₂ w8) ∗ ((fsp + 0x40#64) ↦₃₂ w9) ∗
      ((fsp + 0x3c#64) ↦₃₂ w10) ∗ ((fsp + 0x38#64) ↦₃₂ w11) ∗
      ((fsp + 0x34#64) ↦₃₂ w12) ∗ ((fsp + 0x30#64) ↦₃₂ w13) ∗
      ((fsp + 0x2c#64) ↦₃₂ w14) ∗ ((fsp + 0x28#64) ↦₃₂ w15) ∗
      ((fsp + 0x24#64) ↦₃₂ w16) ∗ ((fsp + 0x20#64) ↦₃₂ w17) ∗
      ((fsp + 0x1c#64) ↦₃₂ w18) ∗ ((fsp + 0x18#64) ↦₃₂ w19) ∗
      ((fsp + 0x14#64) ↦₃₂ w20) ∗ ((fsp + 0x10#64) ↦₃₂ w21) ∗
      ((fsp + 0x0c#64) ↦₃₂ w22) ∗ ((fsp + 0x08#64) ↦₃₂ w23) ∗
      memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ⊢
      memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
      (p32_4 (p32_4 (p32_4 (p32_4 (p32_4 (p32_4 (Entails.refl _)))))))) ?_
  have hlow :
      memRegion fsp 8 ∗ memRegion (fsp + 0x08#64) 4 ∗ memRegion (fsp + 0x0c#64) 4 ∗
      memRegion (fsp + 0x10#64) 4 ∗ memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x20#64) 4 ∗ memRegion (fsp + 0x24#64) 4 ∗
      memRegion (fsp + 0x28#64) 4 ∗ memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x38#64) 4 ∗ memRegion (fsp + 0x3c#64) 4 ∗
      memRegion (fsp + 0x40#64) 4 ∗ memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x50#64) 4 ∗ memRegion (fsp + 0x54#64) 4 ∗
      memRegion (fsp + 0x58#64) 4 ∗ memRegion (fsp + 0x5c#64) 4 = memRegion fsp 0x60 := by
    rw [memRegion_merge_at (fsp + 0x58#64) 4 4 (fsp + 0x5c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x54#64) 4 8 (fsp + 0x58#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x50#64) 4 12 (fsp + 0x54#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x4c#64) 4 16 (fsp + 0x50#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x48#64) 4 20 (fsp + 0x4c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x44#64) 4 24 (fsp + 0x48#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x40#64) 4 28 (fsp + 0x44#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x3c#64) 4 32 (fsp + 0x40#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x38#64) 4 36 (fsp + 0x3c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x34#64) 4 40 (fsp + 0x38#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x30#64) 4 44 (fsp + 0x34#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x2c#64) 4 48 (fsp + 0x30#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x28#64) 4 52 (fsp + 0x2c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x24#64) 4 56 (fsp + 0x28#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x20#64) 4 60 (fsp + 0x24#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x1c#64) 4 64 (fsp + 0x20#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x18#64) 4 68 (fsp + 0x1c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x14#64) 4 72 (fsp + 0x18#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x10#64) 4 76 (fsp + 0x14#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x0c#64) 4 80 (fsp + 0x10#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x08#64) 4 84 (fsp + 0x0c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at fsp 8 88 (fsp + 0x08#64) (by clear * -; bv_omega) (by decide)]
  have h60 := memRegion_merge_at (fsp + 0x60#64) 4 4 (fsp + 0x64#64) (by clear * -; bv_omega) (by decide)
  have h68 := memRegion_merge_at (fsp + 0x68#64) 4 4 (fsp + 0x6c#64) (by clear * -; bv_omega) (by decide)
  rw [← hlow, ← h60, ← h68]; sep_frame

private theorem s3_pc_sub_entry (a b : BitVec 64) :
    a = b + BitVec.ofNat 64 (a - b).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

/-- `byVal` randomness handoff (`memRegion (fsp + 0xfe0#64) 32` + `0x600` → `1568` B) from
`kem_encaps_ok_ext` to `DeriveKeysA1.derive_keys_a1_ok_ext`. -/
theorem kemEncaps_byVal_handoff_to_deriveKeysA1 (fsp : BitVec 64) :
    memRegion (fsp + 0xfe0#64) 32 ∗ memRegion (fsp + 0x1000#64) 0x600 ⊢
      memRegion (fsp + 0xfe0#64) 1568 := by
  rw [memRegion_merge_at (fsp + 0xfe0#64) 32 0x600 (fsp + 0x1000#64)
    (by bv_omega) (by decide)]
  exact Entails.refl _

attribute [local irreducible] Program.fnOff
end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

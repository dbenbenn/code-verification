/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Specifications.AsmConstants
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.CodeLayout

/-!
# Callee Cell Wrappers and Inner Specification for `get_signed_pre_key::{closure#0}`

Cell-level wrappers for `decimal`, `Dir::get`, `decode_kyber_pre_key` (`decodeSignedPreKeySpec`),
`__rust_dealloc`, and `dropSpeWordSpec`, together with the inner poll specification
`spkGetPollInnerSpec` and outer framing bridge `spkGetPoll_of_inner`.
-/

/-!
# Callee Cell Wrappers and Inner Specification for `get_signed_pre_key::{closure#0}`

Cell-level wrappers for `decimal`, `Dir::get`, `decode_kyber_pre_key` (`decodeSignedPreKeySpec`),
`__rust_dealloc`, and `dropSpeWordSpec`, together with the inner poll specification
`spkGetPollInnerSpec` and outer framing bridge `spkGetPoll_of_inner`.
-/

/-!
# Callee Cell Wrappers and Inner Specification for `get_signed_pre_key::{closure#0}`

Cell-level wrappers for `decimal`, `Dir::get`, `decode_kyber_pre_key` (`decodeSignedPreKeySpec`),
`__rust_dealloc`, and `dropSpeWordSpec`, together with the inner poll specification
`spkGetPollInnerSpec` and outer framing bridge `spkGetPoll_of_inner`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession.Cli

/-! ## 1. Cell-level wrapper for `decimal` carrying `FsInv` -/

abbrev DecimalCellsGhost :=
  BitVec 32 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def decimalCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DecimalCellsGhost where
  pre := fun (id, ret, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = id ∧ s.sp = fsp⌝ ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (id, ret, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.fs.files = s0.fs.files⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName id).length) ∗
      SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def dirGetDetached (A : RustAlloc) :
    Except Unit (List (BitVec 8)) →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | .error (), g0, g1, g2, g3, g4, g5 =>
    ⌜g0 = speWord 1⌝ ∗ speDetached A (utf8 "read") g0 g1 g2 g3 g4 g5 .invalidState
  | .ok bs, g0, g1, g2, g3, _, _ =>
    ⌜g0 = okTagVec ∧ g3 = BitVec.ofNat 64 bs.length⌝ ∗ SpqrV1.Alloc.vecU8Buf A g1 g2 bs

private theorem getResultAt_unpack (A : RustAlloc) (ret : BitVec 64)
    (gr : Except Unit (List (BitVec 8))) :
    getResultAt A ret gr ⊢
      ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64,
      ∃∗ g3 : BitVec 64, ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64,
        words6At ret g0 g1 g2 g3 g4 g5 ∗ dirGetDetached A gr g0 g1 g2 g3 g4 g5 := by
  cases gr with
  | error u =>
    cases u
    dsimp only [getResultAt, dirGetDetached]
    refine Entails.trans (speAt_unpack A (utf8 "read") ret .invalidState) ?_
    refine Entails.sepExists_elim fun g0 => Entails.sepExists_elim fun g1 =>
      Entails.sepExists_elim fun g2 => Entails.sepExists_elim fun g3 =>
      Entails.sepExists_elim fun g4 => Entails.sepExists_elim fun g5 => ?_
    refine Entails.sepExists_right g0 (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right g3
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    dsimp only [speDetached]
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    have hpull :
        (words6At ret g0 g1 g2 g3 g4 g5 ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) =
        (⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hg0, hg3, hg5⟩ => ?_
    have hgoal :
        words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") ⊢
        ⌜g0 = speWord 1⌝ ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") :=
      Entails.pure_right hg0 (Entails.pure_right ⟨hg0, hg3, hg5⟩ (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by ac_rfl))
  | ok bs =>
    dsimp only [getResultAt, vecResultAt, dirGetDetached, words6At]
    have h8 : asm64% decResultVecOff = 8#64 := rfl
    have h32 : asm64% (decResultVecOff + vecSize) = 32#64 := rfl
    have hs : asm% (speSize - (decResultVecOff + vecSize)) = 16 := rfl
    rw [h8, h32, hs, memRegion_16_cells (ret + 32#64)]
    dsimp only [vecU8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun g5 => Entails.sepExists_elim fun g4 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_elim fun g2 => ?_
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right okTagVec (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    rw [show (okTagVec = okTagVec ∧ BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length) = True from
      eq_true ⟨rfl, rfl⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)

abbrev DirGetCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 64 × BitVec 64 × BitVec 32 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def dirGetCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (F0 : FsFiles) (calleeStk : Nat) : Spec DirGetCellsGhost where
  pre := fun (ret, self, dir, nCap, nPtr, id, o0, o1, o2, o3, o4, o5, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (keyName id).length ∧
      s.sp = fsp ∧ s.fs.files = F0 ∧ PkNameOk pathOk dir id⌝ ∗
    dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
    words6At ret o0 o1 o2 o3 o4 o5 ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, nCap, nPtr, id, _o0, _o1, _o2, _o3, _o4, _o5, fsp) s0 sf =>
    ∃∗ gr : Except Unit (List (BitVec 8)),
    ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64,
    ∃∗ g3 : BitVec 64, ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64,
      ⌜gr = dir.get rd F0 (keyName id) ∧ sf.trace = s0.trace⌝ ∗
      words6At ret g0 g1 g2 g3 g4 g5 ∗
      dirGetDetached A gr g0 g1 g2 g3 g4 g5 ∗
      dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def decodeSpkDetached (A : RustAlloc) :
    Except SignalProtocolError SignedPreKeyRecord →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | .error e, w0, w1, w2, w3, w4, w5, w6, _, _, _, _ =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝ ∗ speDetached A [] w1 w2 w3 w4 w5 w6 e
  | .ok r, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10 =>
    ⌜w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
    spkStructDetached A r.signedPreKey w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10

private theorem signedPreKeyResultAt_unpack (A : RustAlloc) (ret : BitVec 64)
    (res : Except SignalProtocolError SignedPreKeyRecord) :
    signedPreKeyResultAt A ret res ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
        decodeSpkDetached A res w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 := by
  cases res with
  | error e =>
    dsimp only [signedPreKeyResultAt, errResultAt, decodeSpkDetached]
    have htag : errTag = 0xFFFFFFFFFFFFFFFF#64 := rfl
    have hoff8 : asm64% resultErrSpeOff = 8#64 := rfl
    have hoff56 : asm64% (resultErrSpeOff + speSize) = 56#64 := rfl
    have hsz : 88 - asm% (resultErrSpeOff + speSize) = 32 := rfl
    rw [htag, hoff8, hoff56, hsz, memRegion_32_cells (ret + 56#64)]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (speAt_unpack A [] (ret + 8#64) e))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w10 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
      Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
      Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64 (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4
      (Entails.sepExists_right u5 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [words6At, words11At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  | ok r =>
    dsimp only [signedPreKeyResultAt, decodeSpkDetached]
    refine Entails.trans (spkStruct_unpack A ret r.signedPreKey) ?_
    refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
      Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
      Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
      Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w10 => ?_
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right w6 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [spkStructDetached]
    have hpull :
        (words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature) =
        (⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hprops => ?_
    have hgoal :
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature ⊢
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature :=
      Entails.pure_right hprops.2.2.2.2.2 (Entails.pure_right hprops (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by ac_rfl))

abbrev DecodeCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def decodeSpkCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DecodeCellsGhost where
  pre := fun (ret, bCap, bPtr, bytes, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = bPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bytes.length ∧
      s.sp = fsp ∧ 0 < bytes.length ∧ bytes.length < 2 ^ 32⌝ ∗
    SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
    words11At ret c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, bCap, bPtr, bytes, _c0, _c1, _c2, _c3, _c4, _c5, _c6, _c7, _c8, _c9, _c10, fsp)
      s0 sf =>
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
    ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
    ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
      decodeSpkDetached A (SignedPreKeyRecord.deserialize bytes) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev DeallocBufGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

@[expose] def deallocBufCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DeallocBufGhost where
  pre := fun (cap, ptr, bytes, fsp) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64⌝ ∗
    SpqrV1.Alloc.vecU8Buf A cap ptr bytes ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (_cap, _ptr, _bytes, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ stackAt fsp calleeStk ∗ A.pool

abbrev DropSpeCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def dropSpeWordCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DropSpeCellsGhost where
  pre := fun (a, d1, d2, d3, d4, d5, fsp) s =>
    ⌜s.readReg64 .x0 = a ∧ s.sp = fsp⌝ ∗
    words6At a (speWord 14) d1 d2 d3 d4 d5 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (a, _d1, _d2, _d3, _d4, _d5, fsp) s0 sf =>
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
    ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      words6At a c0 c1 c2 c3 c4 c5 ∗
      stackAt fsp calleeStk ∗ A.pool

@[expose] def spkGetPollInnerSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) : Spec PkPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.dir x.id ∧ PkSizeOk rd s.fs.files x.dir x.id⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.out 88 ∗
      A.pool ∗ stackAt (s.sp - 384#64) calleeStk ∗ cells (s.sp - 384#64) 48
  post := fun x s0 sf =>
    (∃∗ ans : PkAns SignedPreKeyRecord,
      ⌜ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace⌝ ∗
      spkAnsAt A x.out ans) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
      dirAt A x.self x.dir ∗
      A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗ cells (s0.sp - 384#64) 48
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

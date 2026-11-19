/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFrom -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Root Assembly for `<SignalMessage as TryFrom<&[u8]>>::try_from` (`0x25868`)

Combines the prologue, `len = 9` fast path, protobuf decode loop, and shared epilogue
(`TryFrom`) with the post-loop validation, boxing, and cleanup proofs (`TryFromPost`) into
`tryFrom_subroutine_ok`, `tryFrom_run_stmt`, and `tryFrom_subroutine_ok_placed` (Block `85`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- Discharges `TryFromPostOk_placed` via `tryFrom_post_wp_placed`. -/
theorem tryFromPost_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H) :
    TryFromPostOk_placed A H := by
  intro x s0 s hgt9 hlt hge3 hle4 hpc hrun hst
  refine SepWPp.mono_pre ?_
    (tryFrom_post_wp_placed hS hDropErr hDropSpe hIntoBox hTryClone
      hgt9 hlt hge3 hle4 hpc hrun hst)
  unfold loopPostMem
  simp only [sepConj_assoc]
  exact Entails.refl _

/-- Full relocatable subroutine correctness theorem for `<SignalMessage as TryFrom<&[u8]>>::try_from`
(block `85`) on `tryFromPlacedProg H`. -/
theorem tryFrom_subroutine_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A)) :=
  tryFrom_subroutine_ok_of_post_placed hS hvarint hint32 hskip hbytes
    (tryFromPost_ok_placed hS hDropErr hDropSpe hIntoBox hTryClone)

theorem tryFrom_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A)) :=
  tryFrom_subroutine_ok_placed hS hvarint hint32 hskip hbytes hDropErr hDropSpe hIntoBox hTryClone

theorem tryFrom_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (d : TryFromDepsPlaced A H) :
    subroutine_ok (tryFromPlacedProg H) (blkPl_85).base
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A)) :=
  tryFrom_subroutine_ok_placed hS
    d.varintSlice d.int32Merge d.skipField d.bytesMerge
    d.dropDecodeError d.dropSpe d.intoBoxed d.tryClone

end CryptoVerification.LibsignalTripleRatchet.Wire

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.PublicApiCodeSymA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLen
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Fields
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
import LibsignalBinary.Proofs.CodeLayout

/-!
# `PreKeySignalMessage::new` Top-Level Composition

Composes `prologue_ok`, `encodedLen_ok`, and `fields_ok` to establish `preKeyMsgNewSpec` for
`<libsignal_protocol::protocol::PreKeySignalMessage>::new` (`0x15130`), in both fixed-image and
relocatable `[LibsignalPlacement]` forms.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Fields
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLen

open CryptoVerification.LibsignalPublicApi.Placed

/-- Relocatable `PreKeySignalMessage::new` (block `41`) satisfies
`withLsCodeLoaded lsmpl (preKeyMsgNewSpec A)`. -/
theorem preKeyMsgNew_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_41 H) (blkPl_41).base
      (withLsCodeLoaded lsmpl (preKeyMsgNewSpec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hs hpre hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  exact (preKeyMsgSegExit_placed_chain
    (prologue_placed_ok hshim halloc hmemcpy hpanic encodedLen_placed_ok x R s0 hcl hs hpc hsp hpre)
    (fun s' ⟨g, hA⟩ => fields_placed_ok hshim halloc hdealloc hrealloc hmemcpy hpanic x g R s0 s' hA)).mono_outcome
      fun _ hout => hout

theorem preKeySignalMessageNew_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_41 H) (blkPl_41).base
      (withLsCodeLoaded lsmpl (preKeyMsgNewSpec A)) :=
  preKeyMsgNew_placed_ok hshim halloc hdealloc hrealloc hmemcpy hpanic

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose

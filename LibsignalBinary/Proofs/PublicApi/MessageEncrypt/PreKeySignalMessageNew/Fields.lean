/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTag8
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDealloc

/-!
# `PreKeySignalMessage::new` Field Encoding and Epilogue

Composes protobuf field encoding across tags 1–8 (`SeamA → SeamB`, `+0x25c..+0x4c4`) with the
`into_boxed_slice` conversion, 248-byte `sret` write, temporary buffer deallocations, and epilogue
(`SeamB → exit`, `+0x4c4..+0x608`).
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Fields

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open CryptoVerification.LibsignalPublicApi.Placed

theorem fields_encode_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A x g R s0 s) :
    PreKeyMsgSegExit_placed A H x R s0 s (SeamB_placed A x g R s0) :=
  fields_encode_core_placed_ok hshim halloc hrealloc hmemcpy hpanic x g R s0 s hA

theorem fields_epilogue_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hB : SeamB_placed A x g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s :=
  FieldsEpilogue.fields_epilogue_placed_ok_aux hdealloc hB

theorem fields_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A x g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s :=
  preKeyMsgSegExit_placed_chain
    (fields_encode_placed_ok hshim halloc hrealloc hmemcpy hpanic x g R s0 s hA)
    (fun s' hB => fields_epilogue_placed_ok hdealloc x g R s0 s' hB)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Fields

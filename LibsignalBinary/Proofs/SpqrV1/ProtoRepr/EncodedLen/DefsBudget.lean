/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs

/-!
# `VmPreserved` Specifications for `V1State.Unchunked.*::encoded_len`

`VmPreserved`-augmented parametric (`unchunked{2,3,4,5}EncodedLen{Pinned,}Spec`) and concrete
Hoare contracts for the zero-allocation `V1State.Unchunked.*::encoded_len` leaf subroutines.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget

open _root_.Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open CryptoVerification.SpqrV1.ProtoRepr
  (Unchunked2EncodedLenPinnedGhost Unchunked2EncodedLenGhost
   Unchunked3EncodedLenPinnedGhost Unchunked3EncodedLenGhost
   Unchunked4EncodedLenPinnedGhost Unchunked4EncodedLenGhost
   Unchunked5EncodedLenPinnedGhost Unchunked5EncodedLenGhost
   KeysUnsampledEncodedLenPinnedGhost KeysUnsampledEncodedLenGhost
   NoHeaderReceivedEncodedLenPinnedGhost NoHeaderReceivedEncodedLenGhost
   Ct2SentEncodedLenPinnedGhost Ct2SentEncodedLenGhost
   EkSentEncodedLenPinnedGhost EkSentEncodedLenGhost
   HeaderReceivedEncodedLenPinnedGhost HeaderReceivedEncodedLenGhost
   HeaderSentEncodedLenPinnedGhost HeaderSentEncodedLenGhost
   EkSentCt1ReceivedEncodedLenPinnedGhost EkSentCt1ReceivedEncodedLenGhost
   Ct1SentEncodedLenPinnedGhost Ct1SentEncodedLenGhost
   Ct1SentEkReceivedEncodedLenPinnedGhost Ct1SentEkReceivedEncodedLenGhost)

/-! ## 1. Parametric `V1State.Unchunked.*::encoded_len` `VmPreserved` Specs -/

@[expose] def unchunked2EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked2EncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked2EncodedLenPinnedSpec A)

@[expose] def unchunked2EncodedLenSpec (A : RustAlloc) : Spec Unchunked2EncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked2EncodedLenSpec A)

@[expose] def unchunked3EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked3EncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked3EncodedLenPinnedSpec A)

@[expose] def unchunked3EncodedLenSpec (A : RustAlloc) : Spec Unchunked3EncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked3EncodedLenSpec A)

@[expose] def unchunked4EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked4EncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked4EncodedLenPinnedSpec A)

@[expose] def unchunked4EncodedLenSpec (A : RustAlloc) : Spec Unchunked4EncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked4EncodedLenSpec A)

@[expose] def unchunked5EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked5EncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked5EncodedLenPinnedSpec A)

@[expose] def unchunked5EncodedLenSpec (A : RustAlloc) : Spec Unchunked5EncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.unchunked5EncodedLenSpec A)

/-! ## 2. Concrete `V1State.Unchunked.*::encoded_len` `VmPreserved` Specs -/

@[expose] def keysUnsampledEncodedLenPinnedSpec (A : RustAlloc) : Spec KeysUnsampledEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.keysUnsampledEncodedLenPinnedSpec A)

@[expose] def keysUnsampledEncodedLenSpec (A : RustAlloc) : Spec KeysUnsampledEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.keysUnsampledEncodedLenSpec A)

@[expose] def noHeaderReceivedEncodedLenPinnedSpec (A : RustAlloc) :
    Spec NoHeaderReceivedEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLenPinnedSpec A)

@[expose] def noHeaderReceivedEncodedLenSpec (A : RustAlloc) : Spec NoHeaderReceivedEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLenSpec A)

@[expose] def ct2SentEncodedLenPinnedSpec (A : RustAlloc) : Spec Ct2SentEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ct2SentEncodedLenPinnedSpec A)

@[expose] def ct2SentEncodedLenSpec (A : RustAlloc) : Spec Ct2SentEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ct2SentEncodedLenSpec A)

@[expose] def ekSentEncodedLenPinnedSpec (A : RustAlloc) : Spec EkSentEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ekSentEncodedLenPinnedSpec A)

@[expose] def ekSentEncodedLenSpec (A : RustAlloc) : Spec EkSentEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ekSentEncodedLenSpec A)

@[expose] def headerReceivedEncodedLenPinnedSpec (A : RustAlloc) : Spec HeaderReceivedEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.headerReceivedEncodedLenPinnedSpec A)

@[expose] def headerReceivedEncodedLenSpec (A : RustAlloc) : Spec HeaderReceivedEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.headerReceivedEncodedLenSpec A)

@[expose] def headerSentEncodedLenPinnedSpec (A : RustAlloc) : Spec HeaderSentEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.headerSentEncodedLenPinnedSpec A)

@[expose] def headerSentEncodedLenSpec (A : RustAlloc) : Spec HeaderSentEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.headerSentEncodedLenSpec A)

@[expose] def ekSentCt1ReceivedEncodedLenPinnedSpec (A : RustAlloc) :
    Spec EkSentCt1ReceivedEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenPinnedSpec A)

@[expose] def ekSentCt1ReceivedEncodedLenSpec (A : RustAlloc) : Spec EkSentCt1ReceivedEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenSpec A)

@[expose] def ct1SentEncodedLenPinnedSpec (A : RustAlloc) : Spec Ct1SentEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ct1SentEncodedLenPinnedSpec A)

@[expose] def ct1SentEncodedLenSpec (A : RustAlloc) : Spec Ct1SentEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ct1SentEncodedLenSpec A)

@[expose] def ct1SentEkReceivedEncodedLenPinnedSpec (A : RustAlloc) :
    Spec Ct1SentEkReceivedEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLenPinnedSpec A)

@[expose] def ct1SentEkReceivedEncodedLenSpec (A : RustAlloc) : Spec Ct1SentEkReceivedEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLenSpec A)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core

/-!
# Root Theorems for `OutgoingTripleRatchet::encrypt`

Instantiates `otrEncrypt_body_ok` and its relocatable `[LibsignalPlacement]` counterparts to establish:
- `otrEncrypt_run`: general `SpqrModel` contract given `SpqrSendOk`;
- `otrEncryptEmpty_run`: empty post-quantum state (`pqrState = []`) via `SpqrSendEmpty`;
- `otrEncryptV1_run`: SPQR v1 state via `SpqrSendV1Stmt`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Encrypt

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1

open CryptoVerification

theorem otrEncrypt_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 124) (withLsCodeRoLoaded lsmpl (spqrSendPlacedSpec A ctl S)))
    (hMK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_125).rebase (blkPl_125).base H) (blkPl_125).base
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpec C A ctl uuidTryParse S)) := by
  have h := otrEncrypt_placed_body_ok (fun _ => True) C A ctl S H
    h_aes h_fmt h_dealloc
    (by simpa only [spec_pre_true] using hSend) hMK hGK hNew hNCK
  simpa only [spec_pre_true] using h

theorem otrEncryptEmpty_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 124)
      (withLsCodeRoLoaded lsmpl
        { spqrSendPlacedSpec A ctl S with
          pre := fun x s => ⌜x.st.bytes = []⌝ ∗ (spqrSendPlacedSpec A ctl S).pre x s }))
    (hMK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_125).rebase (blkPl_125).base H) (blkPl_125).base
      (withLsCodeRoLoaded lsmpl
        { otrEncryptPlacedSpec C A ctl uuidTryParse S with
          pre := fun x s => ⌜x.ot.pqrState = []⌝ ∗ (otrEncryptPlacedSpec C A ctl uuidTryParse S).pre x s }) :=
  otrEncrypt_placed_body_ok (· = []) C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

theorem otrEncrypt_coins_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427) (withLsCodeRoLoaded lsmpl (spqrSendPlacedSpec A ctl S)))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpec C A ctl uuidTryParse S)) := by
  have h := otrEncrypt_coins_placed_body_ok (fun _ => True) C A ctl S H
    h_aes h_fmt h_dealloc
    (by simpa only [spec_pre_true] using hSend) hMK hGK hNew hNCK
  simpa only [spec_pre_true] using h

end CryptoVerification.LibsignalTripleRatchet.Encrypt

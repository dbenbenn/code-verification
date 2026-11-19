/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2NoOomBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# `¬ CliReachesOOMPlaced` Bridge for `CliPqxdhElfCorrectStrictPlaced2`

Specializes `T2NoOomBridge.not_cliReachesOOMPlaced_of_strict` to `CliPqxdhElfCorrectStrictPlaced2`
to discharge the `_hAlloc` premise of `CliPqxdhElfSecurePlaced`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced (CliReachesOOMPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2NoOomBridge
  (not_cliReachesOOMPlaced_of_strict)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (CliPqxdhElfCorrectStrictPlaced2 CliPqxdhElfCorrectStrictPlaced2Aes)

theorem not_cliReachesOOMPlaced_of_strict2
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hStrict : CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf)
    (W : CliHooks) (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  not_cliReachesOOMPlaced_of_strict (hStrict.2 W) i hi

/-- `_hAlloc` hypothesis of `CliPqxdhElfSecurePlaced` derived from
`CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf`. -/
theorem hAlloc_of_cliPqxdhElfCorrectStrictPlaced2
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hStrict : CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf)
    (W : CliHooks) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  not_cliReachesOOMPlaced_of_strict2 hStrict W

theorem not_cliReachesOOMPlaced_of_strict2Aes
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hStrict : CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf)
    (W : CliHooks)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  not_cliReachesOOMPlaced_of_strict (hStrict.2 W hE hD hX hPub hF512 hEnc hDec hK) i hi

/-- `_hAlloc` hypothesis of `CliPqxdhElfSecurePlaced` derived from
`CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf`. -/
theorem hAlloc_of_cliPqxdhElfCorrectStrictPlaced2Aes
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hStrict : CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf)
    (W : CliHooks)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  not_cliReachesOOMPlaced_of_strict2Aes hStrict W hE hD hX hPub hF512 hEnc hDec hK

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge

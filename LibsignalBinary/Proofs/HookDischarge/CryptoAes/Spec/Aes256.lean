/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.CryptoGames.AEAD.Aes256

/-!
# FIPS 197 AES-256 Re-Export Shim (`CryptoAes.Spec.Aes256`)

Re-exports the trusted FIPS 197 AES-256 definitions from
`LibsignalBinary.Specifications.CryptoGames.AEAD.Aes256` (`CryptoGames.AES256`) under
`LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256` for the `CryptoAes` proof modules.
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256

export CryptoGames.AES256 (State Word sboxTable invSboxTable sbox)
export CryptoGames.AES256 (invSbox xtime gfMul subBytes invSubBytes)
export CryptoGames.AES256 (shiftRows invShiftRows mixColumn mixColumns invMixColumn)
export CryptoGames.AES256 (invMixColumns addRoundKey rotWord subWord xorWord)
export CryptoGames.AES256 (rcon expandKey256 roundKey aes256Cipher aes256InvCipher)
export CryptoGames.AES256 (aes256Enc aes256Dec)

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256

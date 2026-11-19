/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs
public import LibsignalBinary.Specifications.CryptoGames.Hash.Keccak
public meta import LibsignalBinary.Specifications.CryptoGames.Hash.Keccak

/-!
# FIPS 202 Keccak-f[1600], SHA3-256/512, and SHAKE-128/256 Re-Export Shim (`CryptoMlKem.Spec.Keccak`)

Re-exports the trusted FIPS 202 definitions from
`LibsignalBinary.Specifications.CryptoGames.Hash.Keccak` (`CryptoGames.SHA3`) under
`LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak` (and parent `.Spec` via
`-- AUTO-BRIDGE`), plus compile-time NIST FIPS 202 Known-Answer Tests.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak

export CryptoGames.SHA3 (KeccakState keccakRoundConstants keccakRhoOffset laneGet keccakF1600Round)
export CryptoGames.SHA3 (keccakF1600 keccakZeroState packLane64 unpackLane64 keccakAbsorbBlock)
export CryptoGames.SHA3 (keccakPadBlocks keccakAbsorb keccakExtractRate keccakSqueezeBlocks keccakSponge)
export CryptoGames.SHA3 (sha3_256List sha3_256 sha3_512List sha3_512 shake256List)
export CryptoGames.SHA3 (shake256 shake128List keccakPermuteN shake128BlockAt)

-- NIST FIPS 202 compile-time Known-Answer Tests (`""` and `"abc"`):
#guard sha3_256List [] ==
  [0xa7#8, 0xff#8, 0xc6#8, 0xf8#8, 0xbf#8, 0x1e#8, 0xd7#8, 0x66#8,
   0x51#8, 0xc1#8, 0x47#8, 0x56#8, 0xa0#8, 0x61#8, 0xd6#8, 0x62#8,
   0xf5#8, 0x80#8, 0xff#8, 0x4d#8, 0xe4#8, 0x3b#8, 0x49#8, 0xfa#8,
   0x82#8, 0xd8#8, 0x0a#8, 0x4b#8, 0x80#8, 0xf8#8, 0x43#8, 0x4a#8]

#guard sha3_256List [0x61#8, 0x62#8, 0x63#8] ==
  [0x3a#8, 0x98#8, 0x5d#8, 0xa7#8, 0x4f#8, 0xe2#8, 0x25#8, 0xb2#8,
   0x04#8, 0x5c#8, 0x17#8, 0x2d#8, 0x6b#8, 0xd3#8, 0x90#8, 0xbd#8,
   0x85#8, 0x5f#8, 0x08#8, 0x6e#8, 0x3e#8, 0x9d#8, 0x52#8, 0x5b#8,
   0x46#8, 0xbf#8, 0xe2#8, 0x45#8, 0x11#8, 0x43#8, 0x15#8, 0x32#8]

#guard (sha3_512List []).take 8 ==
  [0xa6#8, 0x9f#8, 0x73#8, 0xcc#8, 0xa2#8, 0x3a#8, 0x9a#8, 0xc5#8]

#guard (shake128List 8 []) ==
  [0x7f#8, 0x9c#8, 0x2b#8, 0xa4#8, 0xe8#8, 0x8f#8, 0x82#8, 0x7d#8]

#guard (shake256List 8 []) ==
  [0x46#8, 0xb9#8, 0xdd#8, 0x2b#8, 0x0b#8, 0xa8#8, 0x8d#8, 0x13#8]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak

-- AUTO-BRIDGE BEGIN
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
export Keccak (
  KeccakState
  keccakRoundConstants
  keccakRhoOffset
  laneGet
  keccakF1600Round
  keccakF1600
  keccakZeroState
  packLane64
  unpackLane64
  keccakAbsorbBlock
  keccakPadBlocks
  keccakAbsorb
  keccakExtractRate
  keccakSqueezeBlocks
  keccakSponge
  sha3_256List
  sha3_256
  sha3_512List
  sha3_512
  shake256List
  shake256
  shake128List
  keccakPermuteN
  shake128BlockAt
)
end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
-- AUTO-BRIDGE END

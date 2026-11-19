/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Symbolic.Specifications.Security.Binary
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityElf
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrims

/-!
# Symbolic Security of the `libsignal-cli` Binary

**Trusted: the statement.**

Main symbolic security theorem for the SHA-256-pinned AArch64 `libsignal-cli` binary
(`cliElfBytes`, `LibsignalBinary/Specifications/SignalSession/CliElf.lean`), covering PQXDH session
setup with SPQR V1 composed with the Triple Ratchet. Built by `lake build CliElfLib`; see
`Symbolic/README.md` for the proof architecture.

`signal_session_secure` combines:
- `Symbolic/Theorems/ModelSecurity.lean`: the ten protocol security properties in the composed
  symbolic model;
- `Symbolic/Theorems/Refinement.lean` (`comp_refines_cli`): trace refinement and progress of
  `cliElfBytes` up to cryptographic collisions;
- `Symbolic/Theorems/RefinementPreservation.lean` (`comp_refinement_preservation_cli`): transfer of
  the ten security properties across trace refinement.

Non-vacuity of the extern and hook hypotheses is proved by `comp_externsSatisfiable_cli` and
`realAes256ContractsSatisfiable_cli` (`Symbolic/Tests/ExternWitness.lean`).

**Trusted computing base.** Every instruction except the 18 Rust panic entry points (DEV-E7)
executes directly from plain loaded ELF memory (`ElfImage.loadState`, zero initial memory patches),
including `aes` and `spqr` CPU-feature probes against the pinned auxv (`AT_HWCAP = 0x1b`,
`AT_HWCAP2 = 0`, `AT_RANDOM = 0^16`). The 18 panic interception and 5 `SampleNTT`
progress-exception addresses are resolved from the pinned ELF's `.symtab` (`resolveCliElfAddrs` in
`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`; see
`Computational/docs/TRUSTED_BASE.md`).
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.Security

open CryptoVerification.SignalSession (cliElfBytes)
open DY.Libsignal.Composed.Security (SignalSessionSecure)

/-- Symbolic security and progress for the SHA-256-pinned `libsignal-cli` AArch64 binary
(`SignalSessionSecure cliElfBytes`, `Symbolic/Specifications/Security/Binary.lean`).
`cliElfBytes` parses as an AArch64 ELF image whose 18 panic and 5 `SampleNTT` addresses resolve
from `.symtab` (`resolveCliElfAddrs`), every reachable guarded CLI call running from plain ELF
memory terminates with a process outcome except on a non-terminating `SampleNTT` matrix seed
(`CliElfProgress`, DEV-CLI22), and under any valid cryptographic extern interpretation and matching
CLI hooks, every guarded, coin-fresh execution trace of `cliRunElf` from `initDirs` is either
explained by a reachable model run with all ten protocol security queries holding against
`HwAttackerKnows`, or encounters a cryptographic collision after an explained prefix on which all
ten queries hold over that prefix's `vis` (`SignalSessionSecureFor`,
`Symbolic/Specifications/Security/Binary.lean`). -/
theorem signal_session_secure :
    SignalSessionSecure cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.signal_session_secure_proof

open DY.Libsignal.Composed.Security (SignalSessionSecureReal)

/-- Symbolic security and progress for the SHA-256-pinned `libsignal-cli` AArch64 binary at the
real primitives (`SignalSessionSecureReal cliElfBytes`,
`Symbolic/Specifications/Security/Binary.lean`): the real primitives obey the symbolic laws
(`RealPrimsAdmissible`); `cliElfBytes` parses and resolves its `.symtab` addresses; every reachable
guarded CLI call terminates except on a non-terminating `SampleNTT` seed (DEV-CLI22); and for every
extern interpretation that satisfies the symbolic laws and agrees with `realCliHooks`, every guarded,
coin-fresh execution trace of `cliRunElf` from `initDirs` (no `RealHooksAgreeOnInput` filter) is
either explained by a reachable model run with all ten protocol security queries holding, or
encounters a cryptographic collision after an explained prefix on which all ten queries hold. -/
theorem signal_session_secure_real :
    SignalSessionSecureReal cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.signal_session_secure_real_proof

end Proven.Security

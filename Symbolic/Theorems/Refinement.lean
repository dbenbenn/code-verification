/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Symbolic.Specifications.Refinement.ElfBinding
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementElf
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrims

/-!
# Trace Refinement for the `libsignal-cli` Binary

**Trusted: the statement.**

Proves `comp_refines_cli` (`CompRefinesCliBinary cliElfBytes`,
`Symbolic/Specifications/Refinement/ElfBinding.lean`), built by `lake build CliElfLib`. For the
parsed AArch64 `libsignal-cli` ELF image (`cliElfBytes`,
`LibsignalBinary/Specifications/SignalSession/CliElf.lean`) executing from plain loaded ELF memory
(`ElfImage.loadState`, zero initial memory patches) under `cliProgElf addrs`, with its 18 Rust
panic and 5 `SampleNTT` addresses resolved from `.symtab` (`resolveCliElfAddrs`), the binary
refines the composed `PQXDH ∘ SPQR ∘ Triple Ratchet` symbolic model up to cryptographic byte
collisions, and every reachable guarded CLI call either terminates with a process outcome or reaches
a non-terminating `SampleNTT` matrix seed (`CliElfProgress`: no fault, trap, or unexcused
divergence, DEV-CLI22; `SIGABRT` aborts terminate the trace at `CliTraces.stop`).

Combined with `Symbolic/Theorems/ModelSecurity.lean` via `comp_refinement_preservation_cli`
(`Symbolic/Theorems/RefinementPreservation.lean`), this yields `signal_session_secure`
(`Symbolic/Theorems/Security.lean`). Non-vacuity of the extern and hook hypotheses (including
`HooksMatchPlaced` at FIPS 197 `aes256Enc` / `aes256Dec`) is proved in
`Symbolic/Tests/ExternWitness.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.Refinement

open CryptoVerification.SignalSession (cliElfBytes)
open DY.Libsignal.Composed.Refinement.Cli (CompRefinesCliBinary)

/-- Trace refinement and progress for the SHA-256-pinned `libsignal-cli` AArch64 binary
(`CompRefinesCliBinary cliElfBytes`, `Symbolic/Specifications/Refinement/ElfBinding.lean`).
`cliElfBytes` parses as an ELF image whose 18 panic and 5 `SampleNTT` addresses resolve from
`.symtab` (`resolveCliElfAddrs`); every reachable guarded CLI call running from plain ELF memory
terminates with a process outcome except on a non-terminating `SampleNTT` matrix seed
(`CliElfProgress`, DEV-CLI22); and under any valid cryptographic extern interpretation and matching
CLI hooks, every guarded execution trace of `cliRunElf` from `initDirs` is explained by a reachable
model run (`Explains`) or encounters a cryptographic collision after an explained prefix
(`CollisionAfterExplainedPrefix`). -/
theorem comp_refines_cli :
    CompRefinesCliBinary cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_refines_cli_proof

open DY.Libsignal.Composed.Refinement.Cli (CompRefinesCliBinaryReal RealPrimsAdmissible)

/-- The closed primitives executed by the linked ELF (`realCliHooks`) obey the symbolic laws:
some extern interpretation satisfies `ExternContractsHoldCli` and agrees with `realCliHooks`
(`RealPrimsAdmissible`, `Symbolic/Specifications/Refinement/ElfBinding.lean`). -/
theorem real_prims_admissible :
    RealPrimsAdmissible :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.real_prims_admissible_proof

/-- Trace refinement and progress for the SHA-256-pinned `libsignal-cli` AArch64 binary at the
real primitives (`CompRefinesCliBinaryReal cliElfBytes`,
`Symbolic/Specifications/Refinement/ElfBinding.lean`): the real primitives obey the symbolic laws;
`cliElfBytes` parses and resolves its `.symtab` addresses; every reachable guarded CLI call
terminates except on a non-terminating `SampleNTT` seed (DEV-CLI22); and for every extern
interpretation that satisfies the symbolic laws and agrees with `realCliHooks`, every guarded
execution trace of `cliRunElf` from `initDirs` (no `RealHooksAgreeOnInput` filter) is explained by
a reachable model run or encounters a cryptographic collision after an explained prefix. -/
theorem comp_refines_cli_real :
    CompRefinesCliBinaryReal cliElfBytes :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_refines_cli_real_proof

end Proven.Refinement

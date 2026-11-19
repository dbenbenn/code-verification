/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.LibsignalCli.StatementPqElfAnyKem
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Computational.Proofs.LibsignalCli.ElfHeadlinePq

/-!
# Lemma 4 and Main Theorem: Computational Correctness and Security of the `libsignal-cli` Binary

**Trusted: the statement.** Built by `lake build CliElfLib`. Each theorem below states an
ELF-direct proposition from `Computational/Specifications/` or `LibsignalBinary/Specifications/`
on the SHA-256-pinned AArch64 binary `cliElfBytes`
(`LibsignalBinary/Specifications/SignalSession/CliElf.lean`) and is proved by a corresponding
`*_proof` theorem in `Computational/Proofs/`. See `Computational/docs/TRUSTED_BASE.md` for the
trusted definitions and kernel axioms of each theorem, and `Computational/docs/DEVIATIONS.md` for
the specification deviations referenced below.

Lemmas 1–3 (`Computational/Theorems/Lemmas.lean`), ELF-direct Lemma 4, and freedom from
`.OutOfMemory` in PQXDH mode imply the KEM-generic security theorem
`libsignal_cli_pq_secure_elf_binary_any_kem` (`main_of_lemmas`,
`Computational/Proofs/LibsignalCli/MainOfLemmas.lean`), which combined with the concrete
Round-3 CRYSTALS-Kyber-1024 `δ_kem` bound `kyber1024_kem_delta_correct`
(`Computational/Theorems/Lemmas.lean`, DEV-PQ21) yields the Main Theorem
`libsignal_cli_pq_secure_elf_binary`; for `cliElfBytes`, `.OutOfMemory` freedom is discharged
unconditionally under the 1 GiB dynamic-mapping budget.

| Result | Theorem | Statement | Proof |
|---|---|---|---|
| Lemma 4 | `libsignal_cli_pq_binary_correct` | `CliPqxdhBinaryCorrect cliElfBytes` (`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |
| KEM-generic CLI security (intermediate) | `libsignal_cli_pq_secure_elf_binary_any_kem` | `CliPqxdhBinaryCorrectAndSecureAnyKem cliElfBytes` (`Computational/Specifications/LibsignalCli/StatementPqElfAnyKem.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |
| Main Theorem | `libsignal_cli_pq_secure_elf_binary` | `CliPqxdhBinaryCorrectAndSecure cliElfBytes` (`Computational/Specifications/LibsignalCli/StatementPqElf.lean`) | `Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean` |

**Trusted computing base.** The statements reference `cliElfBytes` directly without any library
placement (`Obj.MultiPlacement` / `libsignalSessionLib`): every instruction except the 18 Rust
panic entry points (DEV-E7) executes from plain loaded ELF memory (`ElfImage.loadState`, zero
initial memory patches), including `aes` and `spqr` CPU-feature probes against the pinned auxv
(`AT_HWCAP = 0x1b`, `AT_HWCAP2 = 0`, `AT_RANDOM = 0^16`). The `.symtab` trust point is that the
ELF `.symtab` labels the 18 panic entry points and 5 `SampleNTT` entries accurately
(`resolveCliElfAddrs`; `Computational/docs/TRUSTED_BASE.md`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

/-- **Lemma 4 (binary refinement, ELF-direct)** (`CliPqxdhBinaryCorrect cliElfBytes`,
`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`). `cliElfBytes` parses as an
AArch64 ELF image, resolves the 23 `.symtab` addresses (18 panic + 5 `SampleNTT`) via
`resolveCliElfAddrs`, and for all model extras `X`, the ELF-direct process `cliRunElf` (starting
from plain `ElfImage.loadState`) satisfies `CliSpecPqxdh` and `CliSpecPqxdhNoMatch` (DEV-CLI11) at
the closed primitives `realPEParams` (SPQR V1) except on runs that reach `.OutOfMemory`
(`CliReachesOOMElf`, DEV-CLI15) or a non-terminating `libcrux_ml_kem` `SampleNTT` matrix seed
(`CliReachesSampleNttStuckElf`, DEV-CLI22). -/
theorem libsignal_cli_pq_binary_correct :
    CliPqxdhBinaryCorrect cliElfBytes :=
  libsignal_cli_pq_binary_correct_proof

end CryptoVerification.SignalSession

namespace CryptoVerification.LibsignalCli

open CryptoVerification.SignalSession (cliElfBytes)

/-- **KEM-generic binary correctness and security (intermediate lemma)**
(`CliPqxdhBinaryCorrectAndSecureAnyKem cliElfBytes`,
`Computational/Specifications/LibsignalCli/StatementPqElfAnyKem.lean`). `cliElfBytes` parses as an
AArch64 ELF image, resolves the 23 `.symtab` addresses via `resolveCliElfAddrs`, satisfies
`CliPqxdhElfCorrect` (allowing `.OutOfMemory`, DEV-CLI15, and divergent `SampleNTT` seeds,
DEV-CLI22), and for every setup `S` and plaintext length `ℓ` satisfies `CliPqxdhElfSecureAnyKem` on
`cliRunElf elf addrs` (starting from plain `ElfImage.loadState`) at the closed primitives
`realPEParams`, the concrete Curve25519 prime-order x-only subgroup (`X25519Pt`, `x25519Dh`,
`x25519Delta = 1 / 2 ^ 250`), and the concrete Curve25519/XEdDSA unreached operations
`realUnreachedPrims kemKeyGen` for every valid, collision-bounded, `δ_kem`-correct Kyber-1024
`kemKeyGen` (with no `.OutOfMemory` premise, and additive excused-abort term on divergent
`SampleNTT` seeds `CliReachesSampleNttStuckElf`, DEV-CLI22). -/
theorem libsignal_cli_pq_secure_elf_binary_any_kem :
    CliPqxdhBinaryCorrectAndSecureAnyKem cliElfBytes :=
  libsignal_cli_pq_secure_elf_binary_any_kem_proof

/-- **Main Theorem (binary correctness and security, ELF-direct, concrete Kyber-1024)**
(`CliPqxdhBinaryCorrectAndSecure cliElfBytes`,
`Computational/Specifications/LibsignalCli/StatementPqElf.lean`). `cliElfBytes` parses as an
AArch64 ELF image, resolves the 23 `.symtab` addresses via `resolveCliElfAddrs`, satisfies
`CliPqxdhElfCorrect` (allowing `.OutOfMemory`, DEV-CLI15, and divergent `SampleNTT` seeds,
DEV-CLI22), and for every setup `S` and plaintext length `ℓ` satisfies `CliPqxdhElfSecure` on
`cliRunElf elf addrs` (starting from plain `ElfImage.loadState`) at the closed primitives
`realPEParams`, the concrete Curve25519 prime-order x-only subgroup (`X25519Pt`, `x25519Dh`,
`x25519Delta = 1 / 2 ^ 250`), and the concrete Curve25519/XEdDSA and round-3 CRYSTALS-Kyber-1024
unreached operations `realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen` with concrete
decapsulation failure parameter `δ_kem = ε + 1 / 2 ^ 112` under `KyberNoiseGap ε` (DEV-PQ21;
key-generation wire lengths `(1568, 3168)` proved unconditionally, public-key collision bound
`≤ 1 / 2 ^ 255` retained as a premise, Clause 2 conditional on `KeyIndRoGap`, DEV-CLI16, with no
`.OutOfMemory` premise and additive excused-abort term on divergent `SampleNTT` seeds
`CliReachesSampleNttStuckElf`, DEV-CLI22). -/
theorem libsignal_cli_pq_secure_elf_binary :
    CliPqxdhBinaryCorrectAndSecure cliElfBytes :=
  libsignal_cli_pq_secure_elf_binary_proof

end CryptoVerification.LibsignalCli

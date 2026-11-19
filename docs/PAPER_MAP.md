# Paper → code map

This document maps each section, figure, table, theorem, and lemma of the paper
*AlphaProof Code: Verifying Signal's Security at the Machine-Code Level* to the Lean declarations
and repository files that formalize it. Sections follow the paper's order (§1–§9 and Appendices
A–C). Each row gives a **status**:

* **proved**: a theorem on `main` whose transitive axioms are only Lean's three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), fail-closed enforced end-to-end by
  [`comparator/run.sh`](../comparator/run.sh) and reported per theorem by
  [`scripts/trusted-closure.sh`](../scripts/trusted-closure.sh).
* **conditional**: proved under an explicit named hypothesis that is not discharged (specifically,
  Clause 2 of Theorem 2 under the HKDF random-oracle idealization `KeyIndRoGap`).
* **open**: stated on `main` with `sorry` (only the 17 non-default synthetic mutation stubs under
  [`Symbolic/BugInjection/Synthetic/Disproofs/`](../Symbolic/BugInjection/Synthetic/Disproofs/); no
  headline or main-body theorem uses `sorryAx`).
* **trusted**: a definition or specification in the trusted computing base (audited by
  [`scripts/trusted-closure.sh`](../scripts/trusted-closure.sh) and catalogued in
  [`Computational/docs/TRUSTED_BASE.md`](../Computational/docs/TRUSTED_BASE.md)).
* **disproof**: a proved theorem refuting the security specification on a deliberately broken binary
  ($\neg\mathrm{Sec}(\mathit{Asm}_{\mathrm{bug}})$, i.e., `¬ SignalSessionSecure mutantCliElfBytes`;
  none yet on `main`, §6).
* **pending retarget**: a carrier theorem with `0` `sorry` in source that was kernel-checked
  against an earlier 36-hook version of the untrusted placed helper `SignalSessionSecurePlaced`
  rather than Theorem 1's trusted `SignalSessionSecure`. It lives in the non-default
  `BugInjectionDisproofs` library, which CI does not build and `comparator` does not replay;
  its committed checkpoints predate the zero-hook cutover (`fastHookTablePlaced := []`), so
  regenerating them and retargeting to `SignalSessionSecure` remains open (§6).

Names are stable; line numbers are omitted. Related guides:
* [`Computational/docs/TRUSTED_BASE.md`](../Computational/docs/TRUSTED_BASE.md) — exact trusted
  closure, tiered line counts, external hook inventory, and reproduction commands.
* [`Computational/docs/README.md`](../Computational/docs/README.md) and
  [`Computational/docs/READING_THE_THEOREMS.md`](../Computational/docs/READING_THE_THEOREMS.md) —
  computational proof guide and ACD19 (Alwen, Coretti, Dodis 2019) game mapping.
* [`Computational/docs/DEVIATIONS.md`](../Computational/docs/DEVIATIONS.md) and
  [`docs/Symbolic/PAPER_DIFFERENCES.md`](Symbolic/PAPER_DIFFERENCES.md) — catalogued differences
  from prior computational and symbolic Signal papers.
* [`Symbolic/BugInjection/README.md`](../Symbolic/BugInjection/README.md) — historical and synthetic
  bug-injection harness and witnesses.

---

## Quick index of numbered theorems and lemmas

| Paper item | Location | Lean theorem | Trusted statement | Status |
|---|---|---|---|---|
| **Theorem 1** (*Binary symbolic security*) | §5.1.5 | `Proven.Security.signal_session_secure` ([`Symbolic/Theorems/Security.lean`](../Symbolic/Theorems/Security.lean)); real-primitive unfiltered counterpart `signal_session_secure_real` (with `comp_refines_cli_real` and `real_prims_admissible` in [`Symbolic/Theorems/Refinement.lean`](../Symbolic/Theorems/Refinement.lean)) | `SignalSessionSecure cliElfBytes` / `SignalSessionSecureReal cliElfBytes` ([`Symbolic/Specifications/Security/Binary.lean`](../Symbolic/Specifications/Security/Binary.lean)) | proved (`CliElfLib`) |
| **Theorem 2** (*Binary security*, Clause 1 = $H_{\mathrm{lib}}$, Clause 2 = $H_{\mathrm{ro}}$) | §5.2.3 & App. C.4 | `CryptoVerification.LibsignalCli.libsignal_cli_pq_secure_elf_binary` ([`Computational/Theorems/Main.lean`](../Computational/Theorems/Main.lean)) | `CliPqxdhBinaryCorrectAndSecure cliElfBytes` ([`Computational/Specifications/LibsignalCli/StatementPqElf.lean`](../Computational/Specifications/LibsignalCli/StatementPqElf.lean)) | proved (`CliElfLib`; Clause 2 conditional on `KeyIndRoGap`, **G1**; `δ_kem = ε + 1 / 2 ^ 112` under `KyberNoiseGap ε`, `_hKemColl` assumed, `2·CliPqxdhFlagProb` SampleNTT term not bounded in Lean, DEV-CLI22) |
| **Lemma 1** (*PQXDH*) | App. C.3 | `SignalPqxdh.Security.headlineδ` ([`Computational/Theorems/Lemmas.lean`](../Computational/Theorems/Lemmas.lean)) | `PqxdhCorrectAndSecureδ` ([`Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean`](../Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean), [`Auth/Headline.lean`](../Computational/Specifications/Pqxdh/Security/Auth/Headline.lean)) | proved |
| **Lemma 2** (*Single session*) | App. C.3 | `CryptoVerification.E2E.session_secure` ([`Computational/Theorems/Lemmas.lean`](../Computational/Theorems/Lemmas.lean)) | `SessionSecure` ([`Computational/Specifications/Session/StatementSession.lean`](../Computational/Specifications/Session/StatementSession.lean)) | proved |
| **Lemma 3** (*Composition*) | App. C.3 | `CryptoVerification.E2E.model_secure_costed` ([`Computational/Theorems/Lemmas.lean`](../Computational/Theorems/Lemmas.lean)) | `ModelSecure` ([`Computational/Specifications/Composition/StatementModel.lean`](../Computational/Specifications/Composition/StatementModel.lean)) | proved |
| **Kyber-1024 $\delta_{\mathrm{kem}}$** (*KEM correctness*) | App. C.3–C.4 | `CryptoVerification.E2E.kyber1024_kem_delta_correct` ([`Computational/Theorems/Lemmas.lean`](../Computational/Theorems/Lemmas.lean)) | `Kyber1024KemDeltaCorrect` ([`Computational/Specifications/LibsignalCli/Kyber1024Delta.lean`](../Computational/Specifications/LibsignalCli/Kyber1024Delta.lean)) | proved (`δ_kem = ε + 1 / 2 ^ 112` under `KyberNoiseGap ε`, DEV-PQ21) |
| **Lemma 4** (*Machine code refines the model*) | App. C.3 | `CryptoVerification.SignalSession.libsignal_cli_pq_binary_correct` ([`Computational/Theorems/Main.lean`](../Computational/Theorems/Main.lean)) | `CliPqxdhBinaryCorrect cliElfBytes` ([`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`](../LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean)) | proved (`CliElfLib`) |

---

## §1 Introduction

| Paper | Code | Notes |
|---|---|---|
| **Fig. 1**: AlphaProof Code workflow (specification assurance, AArch64 semantics, multi-agent proof synthesis, deterministic gatekeeping) | Headline theorems in [`Symbolic/Theorems/`](../Symbolic/Theorems/) and [`Computational/Theorems/`](../Computational/Theorems/); AArch64 semantics in [`arm64-semantics/Arm64/Trusted/`](../arm64-semantics/Arm64/Trusted/); gatekeeper in [`comparator/`](../comparator/) | Detailed in §2.1–§2.4 |

---

## §2 AlphaProof Code

### §2.1 Specification Writing

| Paper | Code | Status / notes |
|---|---|---|
| Thin theorem entrypoints & transitive specification closure | [`Symbolic/Theorems/`](../Symbolic/Theorems/), [`Computational/Theorems/`](../Computational/Theorems/), [`scripts/TrustedClosure.lean`](../scripts/TrustedClosure.lean), [`scripts/trusted-closure.sh`](../scripts/trusted-closure.sh), [`scripts/trust_banner_headlines.txt`](../scripts/trust_banner_headlines.txt) | Trusted-base audit tooling (§5.3) |
| Non-vacuity and premise-satisfiability sanity theorems | Symbolic model: [`Symbolic/Tests/ModelNonVacuity.lean`](../Symbolic/Tests/ModelNonVacuity.lean), [`Symbolic/Proofs/Tests/Model/ComposedNonVacuity.lean`](../Symbolic/Proofs/Tests/Model/ComposedNonVacuity.lean); Symbolic CLI & externs: [`Symbolic/Tests/CliNonvacuity.lean`](../Symbolic/Tests/CliNonvacuity.lean), [`Symbolic/Tests/ExternWitness.lean`](../Symbolic/Tests/ExternWitness.lean); Computational: [`Computational/Tests/NonVacuity/PrimeOrderX25519Satisfiable.lean`](../Computational/Tests/NonVacuity/PrimeOrderX25519Satisfiable.lean), [`PqHeadlineSatisfiable.lean`](../Computational/Tests/NonVacuity/PqHeadlineSatisfiable.lean), [`FirstMessageRoundtrip.lean`](../Computational/Tests/NonVacuity/FirstMessageRoundtrip.lean), [`Computational/Tests/Sanity/InOrder.lean`](../Computational/Tests/Sanity/InOrder.lean), [`Window.lean`](../Computational/Tests/Sanity/Window.lean) | proved |
| Synthetic Mutants (e.g., skipping MAC verification) | [`third_party/libsignal/bug-injection/synthetic/bugs.toml`](../third_party/libsignal/bug-injection/synthetic/bugs.toml), [`Symbolic/BugInjection/Synthetic/NonVacuity/`](../Symbolic/BugInjection/Synthetic/NonVacuity/), [`Symbolic/BugInjection/Proofs/`](../Symbolic/BugInjection/Proofs/) (e.g., [`SyntheticImplicitRejectMac/Top.lean`](../Symbolic/BugInjection/Proofs/SyntheticImplicitRejectMac/Top.lean)), [`Symbolic/BugInjection/Synthetic/Disproofs/`](../Symbolic/BugInjection/Synthetic/Disproofs/) (e.g., [`VerifyMacSkipCli.lean`](../Symbolic/BugInjection/Synthetic/Disproofs/VerifyMacSkipCli.lean)) | 17 Synthetic Mutants (`Synthetic/NonVacuity/*.lean` proved for all 17, and machine-free `(S)` spec halves proved for 16 of 17 in `Proofs/Synthetic*/Top.lean` — all except `PreAbortStdoutExfil` — at `CliSetupMatchesPinned` or per-mutant pinned predicates; all 17 full binary disproof obligations in `Synthetic/Disproofs/*.lean`, stated against `SignalSessionSecurePlaced`, are **open** with `sorry` in the non-default library, so no synthetic mutant is refuted on `main`) |
| Historical bug injection | [`Symbolic/BugInjection/README.md`](../Symbolic/BugInjection/README.md), [`Symbolic/BugInjection/Disproofs/`](../Symbolic/BugInjection/Disproofs/), [`Symbolic/Proofs/SpecLemmas/SecurityBinaryPlaced.lean`](../Symbolic/Proofs/SpecLemmas/SecurityBinaryPlaced.lean) | **pending retarget** (carriers in non-default `BugInjectionDisproofs` were kernel-checked against an earlier 36-hook version of untrusted `SignalSessionSecurePlaced`; checkpoints predate the zero-hook cutover; §6) |

### §2.2 Machine-Code Semantics

These live in the [`arm64-semantics`](../arm64-semantics/) submodule (`v0.56.1`). Everything under
[`arm64-semantics/Arm64/Trusted/`](../arm64-semantics/Arm64/Trusted/) is trusted.

| Paper | Code | Status / notes |
|---|---|---|
| `ElfRunsTo bin pre post` (and hooked `ElfRunsToWithOverrides`) | `Arm64.Process.ElfRunsTo` ([`arm64-semantics/Arm64/Trusted/Process/Semantics.lean`](../arm64-semantics/Arm64/Trusted/Process/Semantics.lean)), `Arm64.Process.ElfRunsToWithOverrides` ([`Overrides.lean`](../arm64-semantics/Arm64/Trusted/Process/Overrides.lean)); re-exported in [`Arm64/Trusted/Process.lean`](../arm64-semantics/Arm64/Trusted/Process.lean) and [`LibsignalBinary/Specifications/SignalSession/Process.lean`](../LibsignalBinary/Specifications/SignalSession/Process.lean) | trusted (41-file import closure, 7,801 non-comment SLOC; see [`review-site/paper/scripts/apcode_stats.py`](../review-site/paper/scripts/apcode_stats.py) and [`arm64-semantics/scripts/tcb-map`](../arm64-semantics/scripts/tcb-map)) |
| Machine state, memory permissions, and step relation (`State`, `Program`, `Steps`) | `State` ([`ISA/State.lean`](../arm64-semantics/Arm64/Trusted/ISA/State.lean)), `Memory` ([`ISA/Memory.lean`](../arm64-semantics/Arm64/Trusted/ISA/Memory.lean)), `Program`, `Step`, `Steps` ([`ISA/Semantics.lean`](../arm64-semantics/Arm64/Trusted/ISA/Semantics.lean)) | trusted |
| A64 instruction syntax, decoder, and ASL-derived instruction semantics (467 non-alias A64 instructions = 215 base + 252 FPSIMD; 91 `Instr` constructors) | `Instr` ([`ISA/Syntax.lean`](../arm64-semantics/Arm64/Trusted/ISA/Syntax.lean)), `decode` ([`ISA/Decode.lean`](../arm64-semantics/Arm64/Trusted/ISA/Decode.lean)), `execInst` / `execInstWithSvc` ([`ISA/Semantics.lean`](../arm64-semantics/Arm64/Trusted/ISA/Semantics.lean), [`ISA/Eval.lean`](../arm64-semantics/Arm64/Trusted/ISA/Eval.lean)) | trusted |
| Static ELF64 loader and System V stack/AUXV setup | `ElfImage.parse`, `buildInitialStack`, `ElfImage.loadState`, `loadElf` ([`Process/Loader.lean`](../arm64-semantics/Arm64/Trusted/Process/Loader.lean), [`Process/Types.lean`](../arm64-semantics/Arm64/Trusted/Process/Types.lean)) | trusted |
| Linux AArch64 syscall model (32 syscalls: memory management, file/stream I/O, `futex`, `getrandom`, `exit`/`exit_group`, signal/abort paths) | `Syscall.standardTable` ([`Arm64/Trusted/Syscalls.lean`](../arm64-semantics/Arm64/Trusted/Syscalls.lean) and [`Arm64/Trusted/Syscalls/`](../arm64-semantics/Arm64/Trusted/Syscalls/)) | trusted |
| Relocatable object & multi-library placement (`LinkedAt`, `LinkedIn`) | `Obj.MultiPlacedLib.LinkedAt`, `LinkedIn`, `MultiPlacement` ([`Object/Placed.lean`](../arm64-semantics/Arm64/Trusted/Object/Placed.lean), [`Object/Reloc.lean`](../arm64-semantics/Arm64/Trusted/Object/Reloc.lean), [`Object/Labels.lean`](../arm64-semantics/Arm64/Trusted/Object/Labels.lean)) | trusted |
| Separation-logic assertion language & `subroutine_ok` | [`Spec/SepLogic.lean`](../arm64-semantics/Arm64/Trusted/Spec/SepLogic.lean), [`Spec/SepLogicModel.lean`](../arm64-semantics/Arm64/Trusted/Spec/SepLogicModel.lean), `subroutine_ok` ([`Spec/Hoare.lean`](../arm64-semantics/Arm64/Trusted/Spec/Hoare.lean)) | trusted |
| Separation-logic rules, weakest-precondition calculus, and proof automation | [`arm64-semantics/ProofLib/`](../arm64-semantics/ProofLib/) | **not trusted** — proved sound against `Arm64/Trusted/` in Lean |
| Differential validation against Unicorn, Sail Armv9.4-A, and `qemu-aarch64` (25,000 single-instruction + 225 multi-instruction lockstep cases; 199 static ELFs + 6 negative parser fixtures) | [`arm64-semantics/tools/run-trusted-tests/src/main.rs`](../arm64-semantics/tools/run-trusted-tests/src/main.rs), [`arm64-semantics/Arm64/Testing/Generators/TrustedSuite.lean`](../arm64-semantics/Arm64/Testing/Generators/TrustedSuite.lean), [`arm64-semantics/Arm64/Testing/Regression/SyscallDiff.lean`](../arm64-semantics/Arm64/Testing/Regression/SyscallDiff.lean), [`arm64-semantics/Arm64/Testing/ProcessE2E/expected_vectors.json`](../arm64-semantics/Arm64/Testing/ProcessE2E/expected_vectors.json) | empirical validation suite (`apcode_stats.py`) |

### §2.3 Proof Synthesis & §2.4 Gatekeeping

| Paper | Code | Notes |
|---|---|---|
| Spec-amendment protocol example (`memcpy` reading read-only `.rodata`) | [`arm64-semantics/VerifiedLibraries/Musl/Spec.lean`](../arm64-semantics/VerifiedLibraries/Musl/Spec.lean) | Proved in `arm64-semantics` |
| Deterministic gatekeeper (`leanprover/comparator` + `lean4checker --fresh`) | [`comparator/README.md`](../comparator/README.md), [`comparator/run.sh`](../comparator/run.sh), [`comparator/computational.json`](../comparator/computational.json), [`comparator/symbolic.json`](../comparator/symbolic.json); engine axiom audit [`arm64-semantics/scripts/axiom-audit`](../arm64-semantics/scripts/axiom-audit) | Verifies syntactic identity of theorem statements and transitive definitions, permits only `[propext, Classical.choice, Quot.sound]`, and replays kernel proofs from scratch |

---

## §3 Background on Signal

| Paper | Code | Notes |
|---|---|---|
| **Fig. 2**: Signal session (PQXDH handshake followed by Triple Ratchet = Double Ratchet + SPQR) | Upstream Rust implementation in [`third_party/libsignal/README.md`](../third_party/libsignal/README.md) (`libsignal` v0.105.4 + `spqr` v1.6.0) | Protocol details in Appendix A |
| **Table 1**: Summary of verification results (Symbolic vs. Computational attacker, guarantee, assumptions, trusted model, and out-of-scope items) | Symbolic headline: [`Symbolic/Theorems/Security.lean`](../Symbolic/Theorems/Security.lean) (§5.1); Computational headline: [`Computational/Theorems/Main.lean`](../Computational/Theorems/Main.lean) (§5.2); TCB comparison: [`Computational/docs/TRUSTED_BASE.md`](../Computational/docs/TRUSTED_BASE.md) (§5.3) | |

---

## §4 Setup for Verification (`libsignal-cli`)

Both the paper and the repository name the verified binary `libsignal-cli` (an audit harness
wrapping `libsignal` v0.105.4, distinct from the community Java `signal-cli` client).

| Paper | Code | Status / notes |
|---|---|---|
| `libsignal-cli` Rust wrapper (`init`, `send`, `recv`; unverified `keygen` helper) | [`third_party/libsignal/libsignal-session/cli/src/main.rs`](../third_party/libsignal/libsignal-session/cli/src/main.rs), [`lib.rs`](../third_party/libsignal/libsignal-session/cli/src/lib.rs), [`stores.rs`](../third_party/libsignal/libsignal-session/cli/src/stores.rs), [`coins.rs`](../third_party/libsignal/libsignal-session/cli/src/coins.rs), [`public.rs`](../third_party/libsignal/libsignal-session/cli/src/public.rs); crate [`third_party/libsignal/libsignal-session/src/lib.rs`](../third_party/libsignal/libsignal-session/src/lib.rs); roundtrip tests [`tests/cli_pqxdh_roundtrip.rs`](../third_party/libsignal/libsignal-session/tests/cli_pqxdh_roundtrip.rs) | Subject under verification (untrusted source compiled to AArch64 ELF) |
| Verified AArch64 ELF executable ($\mathit{Asm}$) | `cliElfBytes` in [`LibsignalBinary/Specifications/SignalSession/CliElf.lean`](../LibsignalBinary/Specifications/SignalSession/CliElf.lean) | Loaded via `file_bytes%` and pinned by SHA-256; built reproducibly with `rustc 1.98.1`, musl, and stock LLVM `ld.lld` via [`scripts/cli-elf-stock`](../scripts/cli-elf-stock) (`--stdbin --build`) |
| **Fig. 3**: Verification boundary (state directory, stdin/stdout, attacker-controlled environment) | `CliRun`, `CliHooks` ([`CliRun.lean`](../LibsignalBinary/Specifications/SignalSession/CliRun.lean)); `cliRunElf elf addrs` ([`CliBinaryPq.lean`](../LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean)); [`CliProcess.lean`](../LibsignalBinary/Specifications/SignalSession/CliProcess.lean), [`Process.lean`](../LibsignalBinary/Specifications/SignalSession/Process.lean) | trusted |
| **Fig. 4**: Bob's state directory before and after `m1` (`ik`, `spk/1`, `opk/2`, `kyber/3`, `sessions/alice`) | `Dir`, `encodeDir`, `PqParty` in [`Run.lean`](../LibsignalBinary/Specifications/SignalSession/Run.lean), [`PqDir.lean`](../LibsignalBinary/Specifications/SignalSession/PqDir.lean), [`PqDirNoMatch.lean`](../LibsignalBinary/Specifications/SignalSession/PqDirNoMatch.lean), [`SmDir.lean`](../LibsignalBinary/Specifications/SignalSession/SmDir.lean) | trusted |
| **Fig. 5**: Bash script scenario (`keygen`, `init`, `send`, `recv`; 15.6M AArch64 instructions across 10 invocations) | `pqInitInputs`, `pqSendInputs`, `pqRecvInputs` ([`PqDir.lean`](../LibsignalBinary/Specifications/SignalSession/PqDir.lean)); concrete CLI traces in [`Symbolic/Tests/CliNonvacuity.lean`](../Symbolic/Tests/CliNonvacuity.lean) | trusted / proved |
| Verified runtime libraries (`mallocng` allocator, musl string/memory routines, Rust `std` helpers, CLI I/O & Rust formatting, Ed25519/Curve25519, X25519, SHA-256 & HMAC-SHA256, SHA-512, AES-256-CBC, Kyber-1024 & ML-KEM-768) | [`arm64-semantics/VerifiedLibraries/Mallocng/Spec/Top.lean`](../arm64-semantics/VerifiedLibraries/Mallocng/Spec/Top.lean), [`arm64-semantics/VerifiedLibraries/Musl/Spec.lean`](../arm64-semantics/VerifiedLibraries/Musl/Spec.lean), [`arm64-semantics/VerifiedLibraries/RustStd/Spec.lean`](../arm64-semantics/VerifiedLibraries/RustStd/Spec.lean), [`arm64-semantics/VerifiedLibraries/README.md`](../arm64-semantics/VerifiedLibraries/README.md), [`LibsignalBinary/Proofs/SignalSession/CliIo/`](../LibsignalBinary/Proofs/SignalSession/CliIo/), [`LibsignalBinary/Proofs/HookDischarge/CliIoFmt/`](../LibsignalBinary/Proofs/HookDischarge/CliIoFmt/), [`LibsignalBinary/Proofs/HookDischarge/EdwardsPoint/`](../LibsignalBinary/Proofs/HookDischarge/EdwardsPoint/), [`LibsignalBinary/Proofs/HookDischarge/CryptoX25519/`](../LibsignalBinary/Proofs/HookDischarge/CryptoX25519/), [`LibsignalBinary/Proofs/HookDischarge/CryptoSha256/`](../LibsignalBinary/Proofs/HookDischarge/CryptoSha256/), [`LibsignalBinary/Proofs/HookDischarge/CryptoSha512/`](../LibsignalBinary/Proofs/HookDischarge/CryptoSha512/), [`LibsignalBinary/Proofs/HookDischarge/CryptoAes/`](../LibsignalBinary/Proofs/HookDischarge/CryptoAes/), [`LibsignalBinary/Proofs/HookDischarge/CryptoMlKem/`](../LibsignalBinary/Proofs/HookDischarge/CryptoMlKem/) | **not trusted** — machine code verified in Lean |
| Verified `libsignal` machine-code components with **0 hooked routines** and **18 `SIGABRT` panic overrides** (`cliProgElf`, `cliPanicSymbolsPlaced`) | [`LibsignalBinary/README.md`](../LibsignalBinary/README.md), `resolveCliElfAddrs`, `cliProgElf`, `cliPanicSymbolsPlaced` ([`CliBinaryPq.lean`](../LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean)), [`RecordCodecs/Proto.lean`](../LibsignalBinary/Specifications/RecordCodecs/Proto.lean) | Shared binary specs (`0` external hooks; DEV-E8, DEV-PQ1, DEV-CLI19 in [`Computational/docs/DEVIATIONS.md`](../Computational/docs/DEVIATIONS.md)) |

### §4.1 Binary-Level Guarantees

| Paper | Code | Status / notes |
|---|---|---|
| ELF-direct execution on `cliElfBytes` (no library placement; 23 `.symtab` addresses resolved fail-closed; plain `ElfImage.loadState` with zero initial memory patches) | `resolveCliElfAddrs`, `cliProgElf`, `cliRunElf` ([`CliBinaryPq.lean`](../LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean), [`ElfBinding.lean`](../Symbolic/Specifications/Refinement/ElfBinding.lean)); untrusted cross-check `cliElf_symtab_agrees_with_placement` in [`ElfDirectBridge.lean`](../LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfDirectBridge.lean) | trusted statement + proved bridge (`CliElfLib`) |
| Termination (up to `SampleNTT` seed divergence, DEV-CLI22), exit codes (`0` ok, `1` clean reject, `2` bad usage/oversized, `SIGABRT` assertion abort), input caps ($2^{20}$ B stdin, $10^6$ B plaintext), and **unconditional no-OOM proof** (1 GiB RAM + 8 MiB stack; reachable session record $\le 1{,}209{,}331\text{ B}$) | Symbolic progress: `CliElfProgress`, `CliReachesSampleNttStuckElf` ([`ElfBinding.lean`](../Symbolic/Specifications/Refinement/ElfBinding.lean), DEV-CLI22); Computational caps & no-OOM: `stdinCapBytes = 2^20`, `maxPlaintextBytes = 10^6` ([`Run.lean`](../LibsignalBinary/Specifications/SignalSession/Run.lean)), `cliElf_noOOM_elf` ([`Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean`](../Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean)) | proved (`CliElfLib`) |

---

## §5 Verifying Signal

### §5.1 Symbolic Proofs

**Fig. 6** illustrates the five-part symbolic architecture: composed protocol model (§5.1.1), ten
model security theorems (§5.1.2), hardware events (§5.1.3), trace refinement $\mathit{Asm}
\sqsubseteq \mathit{Model}$ (§5.1.4), and refinement preservation yielding **Theorem 1** (§5.1.5).

#### §5.1.1 Symbolic Model

| Paper | Code | Status / notes |
|---|---|---|
| DyLean framework (`Traceful`, `ExecTrace`, `AttackerKnows`, `genRand`, `sendMessage`, `storeLocalState`, `LocalStateCompromised`, `logEvent`, `dh`/`dhPk`) | External `DY` (`DyLean`), instantiated in [`Symbolic/Specifications/Model/Composed.lean`](../Symbolic/Specifications/Model/Composed.lean) and [`Instance.lean`](../Symbolic/Specifications/Model/Instance.lean) (`BytesFunctor`, `attackerKnowledge`, `ExecEntryT`) | trusted |
| Equational theories: `symEnc`/`symDec` (AES-256-CBC), 8-byte MAC truncation (`trunc8`), and wire formats | [`EquationalTheory/SymEnc.lean`](../Symbolic/Specifications/Model/EquationalTheory/SymEnc.lean), [`Trunc.lean`](../Symbolic/Specifications/Model/EquationalTheory/Trunc.lean), [`TrWireMsg.lean`](../Symbolic/Specifications/Model/EquationalTheory/TrWireMsg.lean) | trusted |
| X25519 non-canonical high-bit encodings and small-subgroup / 8-torsion variants | `Variant.SubF` (`Fin 4`, `Fin 8`), `normalizeX25519Key`, `isLowOrderKey`, `x25519TorsionVariant` in [`EquationalTheory/X25519.lean`](../Symbolic/Specifications/Model/EquationalTheory/X25519.lean) | trusted; models the non-canonical and 8-torsion keys exercised in §6 |
| Kyber-1024 FO binding of the public key into the shared secret | `CanPQKem`, `Encap.SubF`, `SharedSecret.SubF`, `invertKemPublicKey` in [`EquationalTheory/Kem.lean`](../Symbolic/Specifications/Model/EquationalTheory/Kem.lean) | trusted |
| PQXDH handshake, dynamic compromises, and `breakDH`/`breakKEM` + `invertDH`/`invertKEM` | `registerIdentity`, `registerCorruptIdentity`, `genSignedPrekey`, `genPQPrekey`, `genOneTimePrekey`, `aliceHandshake`, `bobHandshake`, `compromiseIK`/`compromiseSPK`/`compromisePQSPK`/`compromiseOPK`, `breakDH`/`breakKEM`, `invertDH`/`invertKEM`, `PQXDHEvent` in [`Model/PQXDH.lean`](../Symbolic/Specifications/Model/PQXDH.lean) | trusted |
| Triple Ratchet (Double Ratchet coupled with SPQR V1, Cheval et al. 2026) | `trMsgKeys` ([`Model/MsgKeys.lean`](../Symbolic/Specifications/Model/MsgKeys.lean)); `TRState`, `messageEncrypt`, `messageDecrypt`, `messageDecryptSkipped`, `exposeKey`, `exposeSkipped`, `exposeSpqr`, `TREvent` ([`Model/TripleRatchet.lean`](../Symbolic/Specifications/Model/TripleRatchet.lean)); SPQR algebra ([`EquationalTheory/Spqr.lean`](../Symbolic/Specifications/Model/EquationalTheory/Spqr.lean)) | trusted |
| Composed state machine $\mathit{Model}$ (`PQXDH ∘ SPQR ∘ Triple Ratchet`) | `aliceStart`, `bobStart`, `HandshakeSession`, `reachability` in [`Model/Composed.lean`](../Symbolic/Specifications/Model/Composed.lean) and [`Model/Instance.lean`](../Symbolic/Specifications/Model/Instance.lean) | trusted (all 23 transitions in Table 3, App. B.1) |

#### §5.1.2 Security Theorems (**Table 2**)

Role names follow `libsignal`: Alice (`AliceDone`) processes Bob's prekey bundle and sends first
(initiator), while Bob (`BobDone`) publishes prekeys and receives first (responder).

| Table 2 row | Lean theorem ([`Symbolic/Theorems/ModelSecurity.lean`](../Symbolic/Theorems/ModelSecurity.lean)) | Statement & query ([`Symbolic/Specifications/Security/Model.lean`](../Symbolic/Specifications/Security/Model.lean)) | Proof | Status |
|---|---|---|---|---|
| Message secrecy (FS, PCS; Cheval et al. 2026) | `Proven.ForwardSecrecy.forward_secrecy`, `Proven.PostCompromiseSecurity.post_compromise_security` | `ForwardSecrecy` (`FSQuery`), `PostCompromiseSecurity` (`PCSQuery`) | [`TopLevelHelpers/Composed/FS.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/FS.lean), [`PCS.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/PCS.lean) | proved |
| Handshake secrecy (Alice = initiator, Bob = responder; Bhargavan et al. 2024 Thms. 7 & 9) | `Proven.Handshake.alice_initiator_secrecy`, `Proven.Handshake.bob_responder_secrecy` | `AliceInitiatorSecrecy` (`AliceInitiatorSecrecyQuery`), `BobResponderSecrecy` (`BobResponderSecrecyQuery`) | [`TopLevelHelpers/Composed/Handshake.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Handshake.lean) | proved |
| Authentication & Peer authentication (Bhargavan et al. Thm. 8 & Thm. 1) | `Proven.Handshake.authentication`, `Proven.Handshake.peer_authentication` | `Authentication` (`AuthenticationQuery`), `PeerAuthentication` (`PeerAuthenticationQuery`) | [`TopLevelHelpers/Composed/Handshake.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Handshake.lean) | proved |
| Handshake forward secrecy & KCI resistance (Bhargavan et al. Thm. 1) | `Proven.Handshake.handshake_forward_secrecy`, `Proven.Handshake.kci_resistance` | `HandshakeForwardSecrecy` (`ForwardSecrecyQuery`), `KCIResistance` (`KCIQuery`) | [`TopLevelHelpers/Composed/Handshake.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Handshake.lean) | proved |
| Session independence (Bhargavan et al. Thm. 1) | `Proven.Handshake.session_independence` | `SessionIndependence` (`SessionIndependenceQuery`) | [`TopLevelHelpers/Composed/Handshake.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Handshake.lean) | proved |
| HNDL resistance (Bhargavan et al. Thm. 1) | `Proven.Handshake.hndl_resistance` | `HNDLResistance` (`HNDLQuery`) | [`TopLevelHelpers/Composed/Handshake.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Handshake.lean) | proved |
| Model & CLI non-vacuity sanity witnesses | `Proven.ExternWitness.comp_externsSatisfiable_cli` ([`Symbolic/Tests/ExternWitness.lean`](../Symbolic/Tests/ExternWitness.lean)), [`Symbolic/Tests/CliNonvacuity.lean`](../Symbolic/Tests/CliNonvacuity.lean), [`Symbolic/Tests/Nonvacuity.lean`](../Symbolic/Tests/Nonvacuity.lean) | `SanityHonestSession`, `SanityHonestWithOPK`, `SanityHonestWithoutOPK`, `FSPremiseSatisfiable`, `HandshakeSecrecyPremiseSatisfiable` ([`Symbolic/Tests/ModelNonVacuity.lean`](../Symbolic/Tests/ModelNonVacuity.lean)) | [`Proofs/Tests/Model/ComposedNonVacuity.lean`](../Symbolic/Proofs/Tests/Model/ComposedNonVacuity.lean) | proved |

#### §5.1.3 Assembly-Layer Events

| Paper | Code | Status / notes |
|---|---|---|
| Hardware byte strings vs. symbolic terms | `HwBytes` vs. `DY.Bytes` ([`Concrete/MachineEvents.lean`](../Symbolic/Specifications/Concrete/MachineEvents.lean)) | trusted |
| Hardware trace events `CliEvent` (`.run` `RunEvent` \| `.env` `EnvEvent`) | `CliEvent`, `RunEvent`, `EnvEvent` ([`Concrete/MachineEvents.lean`](../Symbolic/Specifications/Concrete/MachineEvents.lean)); `CliCall`, `InputsFor`, `runEventOf` ([`Refinement/Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)) | trusted (all 8 event kinds in Table 4, App. B.2) |
| Provisioned setup $r$, initial party directories, and session-file clearing | `ProtocolSetup` ([`Refinement/ModelTraces.lean`](../Symbolic/Specifications/Refinement/ModelTraces.lean)); `initDirs`, `DirectorySnapshot` ([`Refinement/CliSetup.lean`](../Symbolic/Specifications/Refinement/CliSetup.lean)); `CliTraces.clear` ([`Refinement/Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)) | trusted |
| Secrets revealed by `leak` and guarded hardware traces $\mathrm{Traces}_{\mathcal{I},W}(r)$ | `RecordRec`, `KeyInRecord` ([`Concrete/SessionRecord.lean`](../Symbolic/Specifications/Concrete/SessionRecord.lean)); `KeyInDir`, `LeaksFrom`, `CliTraces`, `ValidCall`, `InvertsGuarded`, `CoinsFresh` ([`Refinement/Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)) | trusted |

#### §5.1.4 Refinement & §5.1.5 Main Theorem (**Theorem 1**)

| Paper | Lean theorem / declaration | Statement (trusted) | Proof | Status |
|---|---|---|---|---|
| Concretization $\gamma_{\mathcal{I},S,g}$, extern contracts $\mathcal{I}$, opaque $S$, ghost $g$, explanations $\mathrm{Expl}(\tau)$, and collision excuse $\mathrm{Collision}(\tau)$ | `gamma`, `OpaqueSymbolSemantics`, `Ghost` ([`Refinement/Concretization.lean`](../Symbolic/Specifications/Refinement/Concretization.lean)); `ExternInterpretation`, `ExternCryptoLawsHold` ([`Concrete/ExternInterpretation.lean`](../Symbolic/Specifications/Concrete/ExternInterpretation.lean)); `HooksMatchPlaced`, `RealHooksAgreeOnInput`, `elfRel` ([`Refinement/ElfBinding.lean`](../Symbolic/Specifications/Refinement/ElfBinding.lean)); `MatchesEvents`, `Explains` ([`Refinement/TraceExplanation.lean`](../Symbolic/Specifications/Refinement/TraceExplanation.lean)); `CollisionAfterExplainedPrefix`, `NextEventCollides` ([`Refinement/Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)) | — | — | trusted |
| **$\mathit{Asm} \sqsubseteq \mathit{Model}$** (binary trace refinement & progress up to collisions) | `Proven.Refinement.comp_refines_cli` ([`Symbolic/Theorems/Refinement.lean`](../Symbolic/Theorems/Refinement.lean), `CliElfLib`); real-primitive unfiltered counterpart `comp_refines_cli_real` and admissibility `real_prims_admissible` | `CompRefinesCliBinary cliElfBytes` (`CliElfProgress`) and `CompRefinesCliBinaryReal cliElfBytes` (`CliElfProgressReal`, `RealPrimsAdmissible`, `elfRelReal`) ([`Refinement/ElfBinding.lean`](../Symbolic/Specifications/Refinement/ElfBinding.lean)) | [`TopLevelHelpers/Composed/Cli/RefinementElf.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Cli/RefinementElf.lean), [`RealPrims.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Cli/RealPrims.lean) | proved (`SymRefines`, `CliElfLib`) |
| **Refinement preservation** ($\mathrm{Sec}(\mathit{Model}) \wedge \mathit{Asm} \sqsubseteq \mathit{Model} \Rightarrow \mathrm{Sec}(\mathit{Asm})$) | `Proven.RefinementPreservation.comp_refinement_preservation_cli` ([`Symbolic/Theorems/RefinementPreservation.lean`](../Symbolic/Theorems/RefinementPreservation.lean)) | `CompRefinementPreservationCli` ([`Refinement/RefinementPreservation.lean`](../Symbolic/Specifications/Refinement/RefinementPreservation.lean)) | [`TopLevelHelpers/Composed/Cli/RefinementPreservation.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Cli/RefinementPreservation.lean) | proved |
| **Theorem 1 (*Binary symbolic security*)** ($\mathrm{Sec}(\mathit{Asm})$) | `Proven.Security.signal_session_secure` ([`Symbolic/Theorems/Security.lean`](../Symbolic/Theorems/Security.lean), `CliElfLib`); real-primitive unfiltered counterpart `signal_session_secure_real` | `SignalSessionSecure cliElfBytes` and `SignalSessionSecureReal cliElfBytes` ([`Security/Binary.lean`](../Symbolic/Specifications/Security/Binary.lean), [`AsmSecure.lean`](../Symbolic/Specifications/Security/AsmSecure.lean)) | [`TopLevelHelpers/Composed/Cli/AsmLevelSecurityElf.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Cli/AsmLevelSecurityElf.lean), [`RealPrims.lean`](../Symbolic/Proofs/TopLevelHelpers/Composed/Cli/RealPrims.lean) | proved (`SymSecure`, `CliElfLib`) |

#### §5.1.6 Limitations

| Paper | Code |
|---|---|
| Cryptographic byte collisions excused symbolically rather than bounded probabilistically | `CollisionAfterExplainedPrefix` ([`Symbolic/Specifications/Refinement/Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)) |
| Closed primitive specifications and algebraic extern laws trusted (`0` external hooks on `cliElfBytes`) | `HooksMatchPlaced`, `RealHooksAgreeOnInput` ([`ElfBinding.lean`](../Symbolic/Specifications/Refinement/ElfBinding.lean)), `ExternContractsHoldCli` ([`Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)) |
| XEdDSA and SPQR opaque in $\gamma$; authentic prekey bundles and honest SPQR headers | `OpaqueSymbolSemantics` ([`Concretization.lean`](../Symbolic/Specifications/Refinement/Concretization.lean)), `HonestBundleFiles` ([`Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)), `PqFromHonest` ([`TraceExplanation.lean`](../Symbolic/Specifications/Refinement/TraceExplanation.lean)) |
| Two provisioned honest parties (`alice ≠ bob`) with fixed roles, $\le 1$ prekey per kind, one active session per file; aborted runs stop the trace | `initDirs` ([`CliSetup.lean`](../Symbolic/Specifications/Refinement/CliSetup.lean)), `ValidCall`, `CliTraces.stop` ([`Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean)) |
| Detailed comparison with Cheval et al. (2026), Bhargavan et al. (2024), and Kobeissi et al. (~35 catalogued differences) | [`docs/Symbolic/PAPER_DIFFERENCES.md`](Symbolic/PAPER_DIFFERENCES.md) |

---

### §5.2 Computational Proofs

**Fig. 7** shows the four-lemma computational architecture: Lemma 1 (PQXDH) and Lemma 2 (single
Triple Ratchet session) combine into Lemma 3 (multi-session composed model $G(\Sigma_{\mathrm{model}})$),
which combines with Lemma 4 (binary refinement $\Sigma_{\mathrm{bin}} \equiv \Sigma_{\mathrm{model}}$)
and unconditional `.OutOfMemory` freedom to yield **Theorem 2** on $G(\Sigma_{\mathrm{bin}})$.

#### §5.2.1 The Security Game

| Paper | Code | Status / notes |
|---|---|---|
| Generic multi-session game $G(\Sigma)$ | `composedExp` over `ComposedIface`, `ComposedAdvantage` ([`GenericGame.lean`](../Computational/Specifications/Game/GenericGame.lean)); driver `bhDrvKeyInd`, `bhDrvGuard`, `bhInjOK`, `allTestedSessionsFresh`, `driverSomeInstanceWon` ([`StatementBinaryHarnessCore.lean`](../Computational/Specifications/Game/StatementBinaryHarnessCore.lean)) | trusted |
| Binary game $G(\Sigma_{\mathrm{bin}})$ (every ratchet operation is a `libsignal-cli` ELF run) | `cliPqExp`, `CliPqxdhAdvantage` ([`StatementPq.lean`](../Computational/Specifications/Game/StatementPq.lean)); `CliKemFailProb`, `CliPqxdhFlagProb` ([`StatementPqOomGame.lean`](../Computational/Specifications/Game/StatementPqOomGame.lean)); `rfl` equivalence check in [`Computational/Tests/Guards/GenericGameGuard.lean`](../Computational/Tests/Guards/GenericGameGuard.lean) | trusted |
| Handshake oracles ($H_{\mathrm{lib}}$ standard-model real HKDF vs. $H_{\mathrm{ro}}$ random-oracle HKDF) | `pqxdhKeyIndImpl` ([`Pqxdh/Game.lean`](../Computational/Specifications/Pqxdh/Game.lean)); `pqxdhKeyIndImpl1KeyReal` ([`Assumptions/KeyInd1KeyReal.lean`](../Computational/Specifications/Assumptions/KeyInd1KeyReal.lean)); `pqxdhKeyIndImpl1KeyRo` ([`Assumptions/KeyInd1KeyRo.lean`](../Computational/Specifications/Assumptions/KeyInd1KeyRo.lean)) | trusted (DEV-CLI16) |
| Budgets ($N_{\mathrm{id}}, N_{\mathrm{spk}}, N_{\mathrm{opk}}, N_{\mathrm{send}}, q_{\mathrm{start}}, q_k, q_{\mathrm{ep}}$; online vs. offline RO queries) | `SignalPqxdh.Setup`, `QueryBudget`, `CliGameAdversaryPerInstanceBounded` ([`StatementBinaryHarnessCore.lean`](../Computational/Specifications/Game/StatementBinaryHarnessCore.lean)) | trusted (DEV-C13) |

#### §5.2.2 Reductions as Programs

| Paper | Code | Notes |
|---|---|---|
| Deeply embedded `ReductionDsl` (`CostedReduction`, `TwoStageCostedReduction`, syntactic step cost & AST node budgets) | [`Computational/Specifications/Reductions/ReductionDsl/Core.lean`](../Computational/Specifications/Reductions/ReductionDsl/Core.lean), [`AtomicOps.lean`](../Computational/Specifications/Reductions/ReductionDsl/AtomicOps.lean), [`Samplers.lean`](../Computational/Specifications/Reductions/ReductionDsl/Samplers.lean), [`TargetCodecs.lean`](../Computational/Specifications/Reductions/ReductionDsl/TargetCodecs.lean), [`StatementPqReds.lean`](../Computational/Specifications/Reductions/Pqxdh/StatementPqReds.lean) | Trusted definitions; tutorial in [`Computational/docs/REDUCTION_DSL_TUTORIAL.md`](../Computational/docs/REDUCTION_DSL_TUTORIAL.md) |

#### §5.2.3 Main Theorem (**Theorem 2**)

| Paper | Lean theorem | Statement (trusted) | Proof | Status |
|---|---|---|---|---|
| **Theorem 2 (*Binary security*)** — Clause 1 ($H_{\mathrm{lib}}$, standard model) and Clause 2 ($H_{\mathrm{ro}}$, under `KeyIndRoGap` **G1**) | `CryptoVerification.LibsignalCli.libsignal_cli_pq_secure_elf_binary` ([`Computational/Theorems/Main.lean`](../Computational/Theorems/Main.lean), `CliElfLib`) | `CliPqxdhBinaryCorrectAndSecure cliElfBytes` ([`StatementPqElf.lean`](../Computational/Specifications/LibsignalCli/StatementPqElf.lean): concrete `kyber1024KemKeyGen`, `δ_kem = ε + 1 / 2 ^ 112` under `KyberNoiseGap ε`, `_hKemColl` retained, `2 * CliPqxdhFlagProb` `SampleNTT` seed-divergence term not bounded in Lean, DEV-CLI22); advantages and bounds in `ℝ≥0∞` | [`Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean`](../Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean) from `libsignal_cli_pq_secure_elf_binary_any_kem` ([`StatementPqElfAnyKem.lean`](../Computational/Specifications/LibsignalCli/StatementPqElfAnyKem.lean), via `main_of_lemmas` in [`MainOfLemmas.lean`](../Computational/Proofs/LibsignalCli/MainOfLemmas.lean) and `cliElf_noOOM_elf`) + `kyber1024_kem_delta_correct` ([`HeadlineProof.lean`](../Computational/Proofs/Kyber1024Delta/HeadlineProof.lean)) | proved (headline `Main`; Clause 2 **conditional** on `KeyIndRoGap`; no `.OutOfMemory` premise or abort term; `2 * CliPqxdhFlagProb` `SampleNTT` term is not bounded in Lean — zero only under an idealized random XOF as the adversary influences the seeds, DEV-CLI22) |
| Assembly from Lemmas 1–4 (`main_of_lemmas`) | `main_of_lemmas` ([`MainOfLemmas.lean`](../Computational/Proofs/LibsignalCli/MainOfLemmas.lean)) | `PqxdhCorrectAndSecureδ → (∀ …, SessionSecure ℓ) → (∀ …, ModelSecure S ℓ) → CliPqxdhBinaryCorrect bytes → (∀ …, ¬ CliReachesOOMElf …) → … → CliPqxdhBinaryCorrectAndSecureAnyKem bytes` | [`MainOfLemmas.lean`](../Computational/Proofs/LibsignalCli/MainOfLemmas.lean) | proved |
| Generic CLI runner specialization | `libsignalCliPqSecure_holds` ([`HeadlinePqCliClosed.lean`](../Computational/Proofs/LibsignalCli/HeadlinePqCliClosed.lean)) | `LibsignalCliPqSecure` ([`StatementPqSecure.lean`](../Computational/Proofs/LibsignalCli/StatementPqSecure.lean)) | [`HeadlinePqCliClosed.lean`](../Computational/Proofs/LibsignalCli/HeadlinePqCliClosed.lean) | proved |
| Lemmas 1–4 & Kyber-1024 $\delta_{\mathrm{kem}}$ (**Fig. 7** proof sketch) | `headlineδ`, `session_secure`, `model_secure_costed`, `kyber1024_kem_delta_correct` ([`Computational/Theorems/Lemmas.lean`](../Computational/Theorems/Lemmas.lean)); `libsignal_cli_pq_binary_correct` ([`Computational/Theorems/Main.lean`](../Computational/Theorems/Main.lean)) | Detailed in Appendix C.3 below; step-by-step walkthrough in [`Computational/docs/READING_THE_THEOREMS.md`](../Computational/docs/READING_THE_THEOREMS.md), [`GLOSSARY.md`](../Computational/docs/GLOSSARY.md), and [`PQXDH.md`](../Computational/docs/PQXDH.md) | | proved |

#### §5.2.4 Assumptions and Idealizations & §5.2.5 Limitations

| Paper | Code | Notes |
|---|---|---|
| Cryptographic assumptions (`GapDhWithSign`, `GapSigEufCma`, `GapDH`, `KemShCr`, ML-KEM-768 IND-CCA, HMAC-SHA256 PRF/PRG, AES-256-CBC IND-CPA) | [`Computational/Specifications/Assumptions/Assumptions.lean`](../Computational/Specifications/Assumptions/Assumptions.lean), [`LibsignalSpqrV1/MlKem.lean`](../LibsignalBinary/Specifications/LibsignalSpqrV1/MlKem.lean), [`CryptoGames/Primitives.lean`](../LibsignalBinary/Specifications/CryptoGames/Primitives.lean), [`AEAD/HMACDefs.lean`](../LibsignalBinary/Specifications/CryptoGames/AEAD/HMACDefs.lean), [`AEAD/HKDFDefs.lean`](../LibsignalBinary/Specifications/CryptoGames/AEAD/HKDFDefs.lean), [`AEAD/CBCDefs.lean`](../LibsignalBinary/Specifications/CryptoGames/AEAD/CBCDefs.lean) | Trusted game definitions |
| SHA-512 random-oracle reductions from `GapDhWithSignRo` and `GapSigEufCmaRo` to plain `GapDH` | [`Computational/Proofs/SignalPqxdh/XeddsaRom/Statements.lean`](../Computational/Proofs/SignalPqxdh/XeddsaRom/Statements.lean) | Proved standalone (outside headline TCB; Appendix C.10) |
| HKDF random-oracle idealization (`KeyIndRoGap`, **G1**) | `KeyIndRoGap` in [`Computational/Specifications/Assumptions/KeyInd1KeyRo.lean`](../Computational/Specifications/Assumptions/KeyInd1KeyRo.lean) | Premise of Theorem 2 Clause 2 ($\varepsilon_{\mathrm{ro}} = 0$ in the ROM, DEV-CLI16) |
| Computational limitations and specification deviations | [`Computational/docs/DEVIATIONS.md`](../Computational/docs/DEVIATIONS.md), [`Computational/docs/TRUSTED_BASE.md`](../Computational/docs/TRUSTED_BASE.md) | Detailed in Appendix C.6 |

---

### §5.3 Trusted Computing Base

| Paper | Code |
|---|---|
| Tiered TCB inventory, file/line counts, external hook breakdown, and reproduction commands | [`Computational/docs/TRUSTED_BASE.md`](../Computational/docs/TRUSTED_BASE.md) |
| Transitive declaration-closure tool & headline list | [`scripts/TrustedClosure.lean`](../scripts/TrustedClosure.lean), [`scripts/trusted-closure.sh`](../scripts/trusted-closure.sh), [`scripts/trust_banner_headlines.txt`](../scripts/trust_banner_headlines.txt) |
| Symbolic TCB, Computational TCB, and Shared binary TCB | [`Symbolic/Specifications/`](../Symbolic/Specifications/), [`Computational/Specifications/`](../Computational/Specifications/), [`LibsignalBinary/Specifications/`](../LibsignalBinary/Specifications/) |
| AArch64 ISA, loader, and Linux syscall TCB | [`arm64-semantics/Arm64/Trusted/`](../arm64-semantics/Arm64/Trusted/), [`arm64-semantics/scripts/tcb-map`](../arm64-semantics/scripts/tcb-map), [`arm64-semantics/scripts/trusted-closure`](../arm64-semantics/scripts/trusted-closure) |
| Reproducible stock `ld.lld` ELF build & pre-link `.o` symbol verification (`A-LINK`) | [`scripts/cli-elf-stock`](../scripts/cli-elf-stock), [`scripts/stock-pin/alink_check.py`](../scripts/stock-pin/alink_check.py), [`arm64-semantics/tools/rust-obj2lean/`](../arm64-semantics/tools/rust-obj2lean/) |
| Independent kernel replay & axiom gatekeeper | [`comparator/README.md`](../comparator/README.md), [`comparator/run.sh`](../comparator/run.sh), [`arm64-semantics/scripts/axiom-audit`](../arm64-semantics/scripts/axiom-audit) |

---

## §6 Finding Historical Bugs

Both vulnerabilities reported by Cheval et al. (2026) are reintroduced by reverse-applying their
upstream fix commits onto `libsignal` v0.105.4 and compiling static AArch64 ELF binaries
$\mathit{Asm}_{\mathrm{bug}}$ (`mutantCliElfBytes`). The Cheval '26 carrier theorems in source
state `¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced mutantCliElfBytes` (`0` `sorry`
in source) and were kernel-checked against an earlier 36-hook version of the untrusted placed helper
`SignalSessionSecurePlaced`
([`SecurityBinaryPlaced.lean`](../Symbolic/Proofs/SpecLemmas/SecurityBinaryPlaced.lean)) rather than
Theorem 1's trusted ELF-direct `SignalSessionSecure` statement
([`Security/Binary.lean`](../Symbolic/Specifications/Security/Binary.lean)). No bridge from
`¬ SignalSessionSecurePlaced mutantCliElfBytes` to `¬ SignalSessionSecure mutantCliElfBytes` exists
on `main`
([`ElfDirectBridge.lean`](../LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfDirectBridge.lean)
covers only the clean `cliElfBytes`), so no bug-injection result on `main` refutes Theorem 1's
trusted statement. The placed formulation is intentional (it keeps the proofs portable across link
layouts); only the disproofs' target statement differs from Theorem 1.

The default `BugInjection` target builds the Cheval '26 witnesses' machine-free `(S)` spec halves
(one carrier witness per bug at `CliSetupMatchesPinned`) and non-vacuity checks, whereas the carrier
modules live in the non-default Lake library
`BugInjectionDisproofs` ([`lakefile.lean`](../lakefile.lean)), which CI does not build. Each carrier
was elaborated per mutant via `scripts/bug_injection.py disproof` (`CV_BUG_INJECTION=<bug>`) with
gitignored `gen-ckpt` chunks; the committed `(I)` checkpoints on `main` predate the 0-hook
cutover and record a `36`-entry hook table (stale against `fastHookTablePlaced := []`).

**Pending:** regenerating the Cheval '26 checkpoints for the 0-hook binary and retargeting the
harness to Theorem 1's ELF-direct statement `¬ SignalSessionSecure mutantCliElfBytes`. See [`Symbolic/BugInjection/README.md`](../Symbolic/BugInjection/README.md),
[`Symbolic/BugInjection/`](../Symbolic/BugInjection/)
([`Disproofs/`](../Symbolic/BugInjection/Disproofs/), [`Witnesses/`](../Symbolic/BugInjection/Witnesses/),
[`Proofs/`](../Symbolic/BugInjection/Proofs/), and [`Split.lean`](../Symbolic/BugInjection/Split.lean)),
and [`third_party/libsignal/bug-injection/README.md`](../third_party/libsignal/bug-injection/README.md)
(manifests [`bugs.toml`](../third_party/libsignal/bug-injection/bugs.toml) and
[`synthetic/bugs.toml`](../third_party/libsignal/bug-injection/synthetic/bugs.toml)).

| Paper bug & upstream fix | Patch & witness JSON | Statement on `main` (`¬ SignalSessionSecurePlaced mutantCliElfBytes`, untrusted placed helper) | Status & proof structure |
|---|---|---|---|
| **Weak state** (Cheval et al. §3.2.1, fix `cd36118`: failed prekey trial-decryption on older session stores unconfirmed state) | [`patches/cheval26-weak-state/v0.105.4.diff`](../third_party/libsignal/bug-injection/patches/cheval26-weak-state/v0.105.4.diff), [`witnesses/cheval26-weak-state-idx1-cli.json`](../third_party/libsignal/bug-injection/witnesses/cheval26-weak-state-idx1-cli.json), [`witnesses/cheval26-weak-state-cli.json`](../third_party/libsignal/bug-injection/witnesses/cheval26-weak-state-cli.json) | `Symbolic.BugInjection.Disproofs.Cheval26WeakStateIdx1Cli.disproof` ([`Cheval26WeakStateIdx1Cli.lean`](../Symbolic/BugInjection/Disproofs/Cheval26WeakStateIdx1Cli.lean)) and [`Cheval26WeakStateCli.lean`](../Symbolic/BugInjection/Disproofs/Cheval26WeakStateCli.lean); carrier [`Impl/Cheval26WeakStateIdx1Cli.lean`](../Symbolic/BugInjection/Disproofs/Impl/Cheval26WeakStateIdx1Cli.lean) | **pending retarget** — `(S)` proved in default build at `CliSetupMatchesPinned` in [`Proofs/Cheval26WeakStateIdx1/CliBridge.lean`](../Symbolic/BugInjection/Proofs/Cheval26WeakStateIdx1/CliBridge.lean); carrier in non-default `BugInjectionDisproofs` (`0` `sorry` in source) was kernel-checked against the earlier 36-hook placed helper across 7 CLI runs via [`Witnesses/CliShapePlaced.lean`](../Symbolic/BugInjection/Witnesses/CliShapePlaced.lean) + [`Split.lean`](../Symbolic/BugInjection/Split.lean) where $\mathit{Asm}_{\mathrm{bug}}$ accepts a spliced prekey message with no model explanation or collision excuse (checkpoints predate the 0-hook cutover) |
| **Small subgroup** (Cheval et al. §3.2.2, fix `5293caa`: responder omits canonical/torsion-free check on initiator X25519 base key) | [`patches/cheval26-small-subgroup/v0.105.4.diff`](../third_party/libsignal/bug-injection/patches/cheval26-small-subgroup/v0.105.4.diff), [`witnesses/cheval26-small-subgroup-high-bit-cli.json`](../third_party/libsignal/bug-injection/witnesses/cheval26-small-subgroup-high-bit-cli.json), [`witnesses/cheval26-small-subgroup-torsion-cli.json`](../third_party/libsignal/bug-injection/witnesses/cheval26-small-subgroup-torsion-cli.json) | `Symbolic.BugInjection.Disproofs.Cheval26SmallSubgroupHighBitCli.disproof` ([`Cheval26SmallSubgroupHighBitCli.lean`](../Symbolic/BugInjection/Disproofs/Cheval26SmallSubgroupHighBitCli.lean)) and [`Cheval26SmallSubgroupTorsionCli.lean`](../Symbolic/BugInjection/Disproofs/Cheval26SmallSubgroupTorsionCli.lean); carrier [`Impl/Cheval26SmallSubgroupHighBitCli.lean`](../Symbolic/BugInjection/Disproofs/Impl/Cheval26SmallSubgroupHighBitCli.lean) | **pending retarget** — `(S)` proved in default build at `CliSetupMatchesPinned` in [`Proofs/Cheval26SmallSubgroupHighBitComp443/CliBridge.lean`](../Symbolic/BugInjection/Proofs/Cheval26SmallSubgroupHighBitComp443/CliBridge.lean); carrier in non-default `BugInjectionDisproofs` (`0` `sorry` in source) was kernel-checked against the earlier 36-hook placed helper across 3 CLI runs where $\mathit{Asm}_{\mathrm{bug}}$ accepts a bit-255-modified base key rejected by the model's `isCanonicalKey` check (checkpoints predate the 0-hook cutover) |

---

## §7 AlphaProof Code in Practice, §8 Related Work & §9 Discussion

| Paper | Code | Status / notes |
|---|---|---|
| §7: Computational specification deviations (`>200` catalogued items, including 15 ACD19 fixes) | [`Computational/docs/DEVIATIONS.md`](../Computational/docs/DEVIATIONS.md) | Documentation |
| §7: Proved reductions from original ACD19 paper rules (`DEV-SM6` corruption rule, `DEV-CKA3` plain-send in $t^*$) | [`Computational/Tests/Deviations/PaperCorrRuleProof.lean`](../Computational/Tests/Deviations/PaperCorrRuleProof.lean), [`PaperFaithfulSendProof.lean`](../Computational/Tests/Deviations/PaperFaithfulSendProof.lean) | proved |
| §7: Symbolic literature differences (~35 items across Cheval et al., Bhargavan et al., Kobeissi et al.) | [`docs/Symbolic/PAPER_DIFFERENCES.md`](Symbolic/PAPER_DIFFERENCES.md) | Documentation |
| §8: Standalone two-key PQXDH `KeyInd` and first-message `Auth` reductions matching Fiedler–Günther / BJKS24 | `Pqxdh2KeyKeyIndSecureδ`, `PqxdhAuthSecureδ`, `Pqxdh2KeyCorrectAndSecureδ` in [`Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean`](../Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean) and [`Computational/Proofs/SpecLemmas/Pqxdh/Security/HeadlineDelta.lean`](../Computational/Proofs/SpecLemmas/Pqxdh/Security/HeadlineDelta.lean); guide [`Computational/docs/PQXDH.md`](../Computational/docs/PQXDH.md) | proved (standalone, outside headline TCB; DEV-PQ13) |

---

## Appendix A: The Signal Protocol in Detail

| Paper | Code |
|---|---|
| **Fig. 8**: PQXDH (`DH1`–`DH4`, Kyber-1024 KEM, HKDF `"WhisperText…"` key derivation, SPQR initial handshake) | [`LibsignalBinary/Specifications/SignalPqxdh/Model.lean`](../LibsignalBinary/Specifications/SignalPqxdh/Model.lean), [`Symbolic/Specifications/Model/PQXDH.lean`](../Symbolic/Specifications/Model/PQXDH.lean) |
| **Fig. 8**: Triple Ratchet (Double Ratchet root/sending/receiving chains + SPQR ML-KEM-768 epochs + AES-256-CBC / HMAC-SHA256-64 Encrypt-then-MAC) | [`LibsignalBinary/Specifications/LibsignalTripleRatchet.lean`](../LibsignalBinary/Specifications/LibsignalTripleRatchet.lean), [`LibsignalSpqrV1/Model.lean`](../LibsignalBinary/Specifications/LibsignalSpqrV1/Model.lean), [`CryptoGames/AEAD/LibsignalAead.lean`](../LibsignalBinary/Specifications/CryptoGames/AEAD/LibsignalAead.lean), [`Symbolic/Specifications/Model/TripleRatchet.lean`](../Symbolic/Specifications/Model/TripleRatchet.lean); KAT checks in [`Computational/Tests/Binary/Kat.lean`](../Computational/Tests/Binary/Kat.lean), [`ProtoCodecKatTest.lean`](../Computational/Tests/Binary/ProtoCodecKatTest.lean), [`third_party/libsignal/test-vectors/`](../third_party/libsignal/test-vectors/) |

---

## Appendix B: Symbolic Proofs

| Subsection | Paper | Code |
|---|---|---|
| **B.1 The Composed Model** | **Table 3**: all 23 transitions of `ReachabilityConfig` (4 registration, 2 handshake/promotion `aliceStart`/`bobStart`, 4 messaging, 7 corruption, 4 cryptographic break/inversion, 2 DyLean network/derivation) | [`Symbolic/Specifications/Model/Composed.lean`](../Symbolic/Specifications/Model/Composed.lean), [`PQXDH.lean`](../Symbolic/Specifications/Model/PQXDH.lean), [`TripleRatchet.lean`](../Symbolic/Specifications/Model/TripleRatchet.lean) |
| **B.2 Hardware Events** | **Table 4**: all 8 `CliEvent` kinds (`RunEvent` + `EnvEvent`), `CliTraces`, `InvertsGuarded`, `CoinsFresh` | [`Symbolic/Specifications/Concrete/MachineEvents.lean`](../Symbolic/Specifications/Concrete/MachineEvents.lean), [`Symbolic/Specifications/Refinement/Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean), [`CliSetup.lean`](../Symbolic/Specifications/Refinement/CliSetup.lean) |
| **B.3 Concretization** | $\gamma_{\mathcal{I},S,g}$ (`gamma`), `ExternContractsHoldCli`, joint satisfiability witness `comp_externsSatisfiable_cli` | [`Symbolic/Specifications/Refinement/Concretization.lean`](../Symbolic/Specifications/Refinement/Concretization.lean), [`Concrete/ExternInterpretation.lean`](../Symbolic/Specifications/Concrete/ExternInterpretation.lean), [`Concrete/ByteSpecs.lean`](../Symbolic/Specifications/Concrete/ByteSpecs.lean), [`Symbolic/Tests/ExternWitness.lean`](../Symbolic/Tests/ExternWitness.lean) |
| **B.4 Explanations** | `MatchesEvents` (`RunMatches`, `RunRejected`, `EnvMatches`), `Explains`, linear state discipline `StepsStateFaithful` | [`Symbolic/Specifications/Refinement/TraceExplanation.lean`](../Symbolic/Specifications/Refinement/TraceExplanation.lean), [`ModelTraces.lean`](../Symbolic/Specifications/Refinement/ModelTraces.lean) |
| **B.5 The Collision Clause** | `CollisionAfterExplainedPrefix`, `NextEventCollides` (`assumedInjective`, `MemoCollisionOn`, `MacTagForgeryOrCollision`, `RecvCollisionOn`, Kyber implicit rejection) | [`Symbolic/Specifications/Refinement/Statement.lean`](../Symbolic/Specifications/Refinement/Statement.lean), [`TraceExplanation.lean`](../Symbolic/Specifications/Refinement/TraceExplanation.lean), [`Symbolic/Tests/RejKeyNonDerivability.lean`](../Symbolic/Tests/RejKeyNonDerivability.lean) |
| **B.6 The Security Statement** | **Table 5**: all 10 whole-trace queries in `AllSecurityQueriesHold`, lifted to `AllSecurityQueriesHoldOnHwTrace` (`HwAttackerKnows`) and `SignalSessionSecure` | [`Symbolic/Specifications/Security/Model.lean`](../Symbolic/Specifications/Security/Model.lean), [`AsmSecure.lean`](../Symbolic/Specifications/Security/AsmSecure.lean), [`Binary.lean`](../Symbolic/Specifications/Security/Binary.lean); walkthrough [`Symbolic/Tests/ForwardSecrecyTour.lean`](../Symbolic/Tests/ForwardSecrecyTour.lean) |
| **B.7 Scope of the Binary Theorem** | Per-invocation process isolation, closed-primitive agreement `HooksMatchPlaced` / `RealHooksAgreeOnInput`, directory persistence, session-record decoding | [`Symbolic/Specifications/Refinement/ElfBinding.lean`](../Symbolic/Specifications/Refinement/ElfBinding.lean), [`Concrete/SessionRecord.lean`](../Symbolic/Specifications/Concrete/SessionRecord.lean), [`Concrete/ImageSymbols.lean`](../Symbolic/Specifications/Concrete/ImageSymbols.lean) |
| **B.8 Refinement Preservation** | Proof of `comp_refinement_preservation_cli` (`CompRefinementPreservationCli`) | Statement: [`Symbolic/Specifications/Refinement/RefinementPreservation.lean`](../Symbolic/Specifications/Refinement/RefinementPreservation.lean); proof: [`Symbolic/Theorems/RefinementPreservation.lean`](../Symbolic/Theorems/RefinementPreservation.lean) |

---

## Appendix C: Computational Proofs

| Subsection | Paper | Code |
|---|---|---|
| **C.1 The Composed Game** | Full definition of $G(\Sigma)$, $G(\Sigma_{\mathrm{model}}^H)$, $G(\Sigma_{\mathrm{bin}})$, handshake/promotion/ratchet oracles, SPQR integration, and query budgets | [`Computational/Specifications/Game/GenericGame.lean`](../Computational/Specifications/Game/GenericGame.lean), [`ModelIface.lean`](../Computational/Specifications/Game/ModelIface.lean), [`StatementPq.lean`](../Computational/Specifications/Game/StatementPq.lean), [`StatementPqOomGame.lean`](../Computational/Specifications/Game/StatementPqOomGame.lean), [`StatementBinaryHarnessCore.lean`](../Computational/Specifications/Game/StatementBinaryHarnessCore.lean), [`Pqxdh/Game.lean`](../Computational/Specifications/Pqxdh/Game.lean), [`CryptoGames/SM/Game.lean`](../LibsignalBinary/Specifications/CryptoGames/SM/Game.lean) |
| **C.2 Reductions and Their Costs** | Syntactic step cost $c_{\mathrm{init}} + q\cdot\max(c_{\mathrm{coin}}, c_{\mathrm{handle}} + c_{\mathrm{codec}}) + c_{\mathrm{finish}}$ and AST node budgets | [`Computational/Specifications/Reductions/ReductionDsl/Core.lean`](../Computational/Specifications/Reductions/ReductionDsl/Core.lean), [`Pqxdh/Security/CostedBudgets.lean`](../Computational/Specifications/Pqxdh/Security/CostedBudgets.lean), [`Reductions/Pqxdh/StatementPqReds.lean`](../Computational/Specifications/Reductions/Pqxdh/StatementPqReds.lean) |
| **C.3 Lemmas** | **Lemma 1** (*PQXDH*, `headlineδ`), **Lemma 2** (*Single session*, `session_secure`), **Lemma 3** (*Composition*, `model_secure_costed`; lazy-sampling condition in [`ModelLazyCond.lean`](../Computational/Proofs/SpecLemmas/Composition/ModelLazyCond.lean)), **Kyber-1024 $\delta_{\mathrm{kem}}$** (`kyber1024_kem_delta_correct`), **Lemma 4** (*Machine code refines the model*, `libsignal_cli_pq_binary_correct` over `CliSpecPqxdh` / `CliSpecPqxdhNoMatch`) | Lemmas 1–3 & Kyber-1024 $\delta_{\mathrm{kem}}$: [`Computational/Theorems/Lemmas.lean`](../Computational/Theorems/Lemmas.lean) (statements [`HeadlineDelta.lean`](../Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean), [`Auth/Headline.lean`](../Computational/Specifications/Pqxdh/Security/Auth/Headline.lean), [`StatementSession.lean`](../Computational/Specifications/Session/StatementSession.lean), [`StatementModel.lean`](../Computational/Specifications/Composition/StatementModel.lean), [`Kyber1024Delta.lean`](../Computational/Specifications/LibsignalCli/Kyber1024Delta.lean); proofs [`Delta/Statements.lean`](../Computational/Proofs/SignalPqxdh/Delta/Statements.lean), [`HeadlineSession.lean`](../Computational/Proofs/LibsignalCli/HeadlineSession.lean), [`HeadlineModel.lean`](../Computational/Proofs/LibsignalCli/HeadlineModel.lean), [`HeadlineProof.lean`](../Computational/Proofs/Kyber1024Delta/HeadlineProof.lean)); Lemma 4: [`Computational/Theorems/Main.lean`](../Computational/Theorems/Main.lean) (statement [`CliBinaryPq.lean`](../LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean), [`PqDir.lean`](../LibsignalBinary/Specifications/SignalSession/PqDir.lean), [`PqDirNoMatch.lean`](../LibsignalBinary/Specifications/SignalSession/PqDirNoMatch.lean); proof [`ElfHeadlinePq.lean`](../Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean)) |
| **C.4 The Main Theorem in Full** | Full statement and proof of **Theorem 2** (`libsignal_cli_pq_secure_elf_binary`), including `prefixSum`, `kemDecapsFailureTerm` at concrete `δ_kem = ε + 1 / 2 ^ 112` under `KyberNoiseGap ε`, `_hKemColl` retained, `2 * CliPqxdhFlagProb` `SampleNTT` seed-divergence term (not bounded in Lean; zero only under an idealized random XOF as the adversary influences the seeds, DEV-CLI22), and the SPQR ML-KEM-768 decapsulation-failure term `2 * CliKemFailProb` | Theorem: [`Computational/Theorems/Main.lean`](../Computational/Theorems/Main.lean); statements: [`StatementPqElf.lean`](../Computational/Specifications/LibsignalCli/StatementPqElf.lean), [`StatementPqElfAnyKem.lean`](../Computational/Specifications/LibsignalCli/StatementPqElfAnyKem.lean); proof: [`MainOfLemmas.lean`](../Computational/Proofs/LibsignalCli/MainOfLemmas.lean), [`ElfHeadlinePq.lean`](../Computational/Proofs/LibsignalCli/ElfHeadlinePq.lean), [`HeadlineProof.lean`](../Computational/Proofs/Kyber1024Delta/HeadlineProof.lean), [`KemFailFind.lean`](../LibsignalBinary/Specifications/LibsignalSpqrV1/KemFailFind.lean) |
| **C.5 Assumptions in Detail** | Joint X25519/XEdDSA security (`GapDhWithSign`, `GapSigEufCma`, domain separation via `0xFF^32` prefix) and execution environment | [`Computational/Specifications/Assumptions/Assumptions.lean`](../Computational/Specifications/Assumptions/Assumptions.lean), [`KeyInd1KeyReal.lean`](../Computational/Specifications/Assumptions/KeyInd1KeyReal.lean), [`KeyInd1KeyRo.lean`](../Computational/Specifications/Assumptions/KeyInd1KeyRo.lean), [`Kyber1024Correct.lean`](../Computational/Specifications/Assumptions/Kyber1024Correct.lean) |
| **C.6 Restrictions in Detail** | Adversary/game restrictions (`2 * (qs k + 1) + 25002 < 2^32`, `ℓ < 10^6`, `stdinCapBytes = 2^20`), setting (bucket-partitioned bilinear MAC bound incomparable with the quartic bound, `DEV-C14`), binary checks (`alink_check.py`, `0` non-panic hooks, `18` panic `SIGABRT` overrides per `DEV-E7`, plain `ElfImage.loadState` with pinned auxv `AT_HWCAP = 0x1b`, `AT_HWCAP2 = 0`, `LSE = 0`), and cost model | [`scripts/stock-pin/alink_check.py`](../scripts/stock-pin/alink_check.py), [`scripts/stock_elf_prep/alpha_checks.py`](../scripts/stock_elf_prep/alpha_checks.py), [`CliBinaryPq.lean`](../LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean), [`CliElf.lean`](../LibsignalBinary/Specifications/SignalSession/CliElf.lean), [`Computational/docs/DEVIATIONS.md`](../Computational/docs/DEVIATIONS.md) |
| **C.7 Well-Formedness of the Handshake Primitives** | Conditions **W1–W6** (`WellFormedPrimitivesδ`, `CryptoWellFormedDh`, `CryptoWellFormedKemδ`, `CryptoWellFormedPrimitivesδ`) and $\delta_{\mathrm{kem}}$-correctness (`KemDeltaCorrect`) | [`LibsignalBinary/Specifications/SignalPqxdh/Model.lean`](../LibsignalBinary/Specifications/SignalPqxdh/Model.lean), [`Computational/Specifications/Assumptions/KemCorrect.lean`](../Computational/Specifications/Assumptions/KemCorrect.lean) |
| **C.8 Primitive and X25519 Premises** | Lemma 2 premises **P1–P10** (`Encaps1Total`, AES roundtrip, `ℓ < 10^6`, `Dh.Commutes`, `X25519RealizesDh`, `decT`/`encT`, `dummyKey`, `Dh.dh x 0 = 0`, `DhKerUniform`, point-fiber bound $\delta$) live on `StatementSession.lean` and `Computational/Proofs/LibsignalCli/StatementPqSecure.lean`; the proofs (`ConcreteX25519Prims.lean`, `MainOfLemmas.lean`, `ElfHeadlinePq.lean`) discharge **P1, P2 and P4–P10** (`Encaps1Total`, AES roundtrip, `X25519RealizesDh`, `Dh.*`), `KemDeltaCorrect`, and `CryptoWellFormedPrimitivesδ` (W1–W5 and the X25519 half of W6) at concrete `X25519Pt`/`x25519Dh`/`kyber1024KemKeyGen`, while `StatementPqElf.lean` retains **P3** (`_hℓ : ℓ < 10^6`), `_hKemColl`, `KyberNoiseGap ε`, and Clause 2's **G1** (`KeyIndRoGap`) | Premises: [`StatementSession.lean`](../Computational/Specifications/Session/StatementSession.lean), [`StatementComposed.lean`](../Computational/Specifications/Session/StatementComposed.lean), [`Computational/Proofs/LibsignalCli/StatementPqSecure.lean`](../Computational/Proofs/LibsignalCli/StatementPqSecure.lean), [`StatementPqElf.lean`](../Computational/Specifications/LibsignalCli/StatementPqElf.lean), [`Kyber1024Correct.lean`](../Computational/Specifications/Assumptions/Kyber1024Correct.lean), [`X25519Group.lean`](../LibsignalBinary/Specifications/CryptoGames/DH/X25519Group.lean), [`Encaps1Total.lean`](../LibsignalBinary/Proofs/SpqrV1Sync/SendTotal/Encaps1Total.lean), [`Ratchet/LibsignalSMInstance.lean`](../LibsignalBinary/Specifications/CryptoGames/Ratchet/LibsignalSMInstance.lean); satisfiability (`session_hypotheses_satisfiable_prime_order`, `cli_pq_headline_hypotheses_satisfiable_prime_order`): [`PrimeOrderX25519Satisfiable.lean`](../Computational/Tests/NonVacuity/PrimeOrderX25519Satisfiable.lean), [`PqHeadlineSatisfiable.lean`](../Computational/Tests/NonVacuity/PqHeadlineSatisfiable.lean); **G1**: [`KeyInd1KeyRo.lean`](../Computational/Specifications/Assumptions/KeyInd1KeyRo.lean) |
| **C.9 The Terms of $\mathsf{Sess}$** | Exact single-session bound `sessionAdvantageBound`, `uniformStartMixtureBound`, ACD19 Theorems 8 & 12, and statistical collision/forgery terms | [`Computational/Specifications/Session/StatementSession.lean`](../Computational/Specifications/Session/StatementSession.lean), [`StatementComposed.lean`](../Computational/Specifications/Session/StatementComposed.lean), [`StatementIdsModel.lean`](../Computational/Specifications/Session/StatementIdsModel.lean), [`StatementSpkModel.lean`](../Computational/Specifications/Session/StatementSpkModel.lean), [`SpkHop2Red.lean`](../Computational/Specifications/Session/SpkHop2Red.lean), [`ACD19/Ratchet/LibsignalBound.lean`](../Computational/Specifications/Session/ACD19/Ratchet/LibsignalBound.lean), [`ACD19/Ratchet/LibsignalSim.lean`](../Computational/Specifications/Session/ACD19/Ratchet/LibsignalSim.lean), [`ACD19/SM/Theorem8And12Statements.lean`](../Computational/Specifications/Session/ACD19/SM/Theorem8And12Statements.lean) |
| **C.10 SHA-512 Random-Oracle Reductions for XEdDSA** | Reference signer `xeddsaSignRef`, curve axioms `XeddsaCurveLaws`, roundtrip `XeddsaSignRoundtrip`, HVZK simulator loss `xeddsaSimLoss` & modular bias `xeddsaModLoss`, Gap-DH reductions `GapDhWithSignRoBound1A` / `GapDhWithSignRoBound1B`, Bellare–Neven forking reductions `GapSigEufCmaRoBoundQuad` / `GapSigEufCmaRoBound`, and $\mathbb{Z}/\ell\mathbb{Z}$ joint non-vacuity | Statements: [`Computational/Proofs/SignalPqxdh/XeddsaRom/Statements.lean`](../Computational/Proofs/SignalPqxdh/XeddsaRom/Statements.lean); proofs (`0` `sorry`): [`Roundtrip.lean`](../Computational/Proofs/SignalPqxdh/XeddsaRom/Roundtrip.lean), [`HvzkSim.lean`](../Computational/Proofs/SignalPqxdh/XeddsaRom/HvzkSim.lean), [`GapDhWithSignReduction.lean`](../Computational/Proofs/SignalPqxdh/XeddsaRom/GapDhWithSignReduction.lean), [`ForkingReduction.lean`](../Computational/Proofs/SignalPqxdh/XeddsaRom/ForkingReduction.lean), [`PrimeL25519.lean`](../Computational/Proofs/SignalPqxdh/XeddsaRom/PrimeL25519.lean); $\mathbb{Z}/\ell\mathbb{Z}$ witness (`xeddsaRom_hypotheses_satisfiable`): [`Computational/Tests/XeddsaRomNonVac.lean`](../Computational/Tests/XeddsaRomNonVac.lean) |

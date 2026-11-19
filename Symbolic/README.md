# Symbolic: DyLean Model, Binary Refinement, and Security of `libsignal-cli`

This folder holds the Dolev-Yao (DyLean) symbolic security development for `libsignal v0.105.4`:
the symbolic protocol models of PQXDH and the Triple Ratchet (Double Ratchet + SPQR V1), their
composition, ten protocol security properties (secrecy, authentication, forward secrecy,
post-compromise security, KCI resistance, session independence, and HNDL resistance), trace
refinement from the SHA-256-pinned AArch64 `libsignal-cli` binary (`cliElfBytes`), security
preservation across refinement, and the bug-injection mutation suite.

For the full trusted computing base, axiom audits, and specification deviations, see
[`Computational/docs/TRUSTED_BASE.md`](../Computational/docs/TRUSTED_BASE.md) and
[`Computational/docs/DEVIATIONS.md`](../Computational/docs/DEVIATIONS.md). For shared binary
specifications and proofs reused by both the symbolic and computational developments, see
[`LibsignalBinary/README.md`](../LibsignalBinary/README.md).

## Directory Map

| Directory | Role |
|---|---|
| [`Specifications/Model/`](Specifications/Model/) | DyLean equational theories (`EquationalTheory/`: X25519 with encoding/torsion variants, KEM, SPQR, symmetric encryption, 8-byte MAC truncation, wire terms) and the symbolic models of PQXDH (`PQXDH.lean`), Triple Ratchet (`TripleRatchet.lean`), hybrid message keys (`MsgKeys.lean`), and their composition (`Composed.lean`, `Instance.lean`). |
| [`Specifications/Concrete/`](Specifications/Concrete/) | Concrete byte-level mirrors (`ByteSpecs.lean`, `MachineEvents.lean`, `SessionRecord.lean`, `SessionRecordDecidable.lean`), wire/symbol constants (`ImageSymbols.lean`), and cryptographic extern laws (`ExternInterpretation.lean`). |
| [`Specifications/Refinement/`](Specifications/Refinement/) | Trace refinement statement linking `libsignal-cli` executions to model traces: `CliSetup.lean`, `Concretization.lean`, `WireFormat.lean`, `ModelTraces.lean`, `TraceExplanation.lean`, `Statement.lean`, `RefinementPreservation.lean`, and the ELF-direct binding `ElfBinding.lean`. |
| [`Specifications/Security/`](Specifications/Security/) | Protocol security queries in the symbolic model (`Model.lean`), hardware-attacker explained-trace security (`AsmSecure.lean`), and the top-level binary security statements (`Binary.lean`). |
| [`Theorems/`](Theorems/) | Top-level audited theorem statements (`ModelSecurity.lean`, `RefinementPreservation.lean`, `Refinement.lean`, `Security.lean`). |
| [`Tests/`](Tests/) | Non-vacuity and specification guard modules (`ExternWitness.lean`, `ModelNonVacuity.lean`, `HwAttackerKnowsNonVacuity.lean`, `CliNonvacuity.lean`, `Nonvacuity.lean`, `Nonvacuity/`, `CliGuards.lean`, `ForwardSecrecyTour.lean`, `RejKeyNonDerivability.lean`, `SetupKyberGuard.lean`, `SpecDuplicateGuards.lean`). |
| [`Proofs/`](Proofs/) | Untrusted Lean proofs supporting model security, trace refinement, refinement preservation, and ELF-direct binary assembly. |
| [`DYBridge/`](DYBridge/) | Untrusted theorem-only bridge lemmas exposing DyLean/Comparse internals to `Symbolic/Proofs/` without leaking `import all` into specifications or proofs. |
| [`BugInjection/`](BugInjection/) | Regression and specification-audit mutation suite against upstream historical bugs and synthetic mutants ([`BugInjection/README.md`](BugInjection/README.md), [`BugInjection/Synthetic/README.md`](BugInjection/Synthetic/README.md)). |
| [`scripts/`](scripts/) | Dependency and machine-freeness checks (`check_symbolic_deps.py`, `machine_free_check.py`, `MachineFreeCheck.lean`). |

## Reading Order

1. **Symbolic protocol & model security** (`lake build`, machine-free):
   - [`Specifications/Model/Composed.lean`](Specifications/Model/Composed.lean) (`PQXDH.lean`, `TripleRatchet.lean`)
   - [`Specifications/Security/Model.lean`](Specifications/Security/Model.lean)
   - [`Theorems/ModelSecurity.lean`](Theorems/ModelSecurity.lean) (the 10 protocol security properties)
2. **Trace refinement & security preservation** (`lake build`, machine-free):
   - [`Specifications/Refinement/ModelTraces.lean`](Specifications/Refinement/ModelTraces.lean), [`TraceExplanation.lean`](Specifications/Refinement/TraceExplanation.lean), and [`Statement.lean`](Specifications/Refinement/Statement.lean)
   - [`Specifications/Security/AsmSecure.lean`](Specifications/Security/AsmSecure.lean) and [`Specifications/Refinement/RefinementPreservation.lean`](Specifications/Refinement/RefinementPreservation.lean)
   - [`Theorems/RefinementPreservation.lean`](Theorems/RefinementPreservation.lean) (`comp_refinement_preservation_cli`)
3. **ELF-direct binary binding & top-level binary security** (`lake build CliElfLib`):
   - [`Specifications/Refinement/ElfBinding.lean`](Specifications/Refinement/ElfBinding.lean) (`elfRel`, `elfRelReal`, `RealPrimsAdmissible`, `CompRefinesCliBinary`, `CompRefinesCliBinaryReal`)
   - [`Specifications/Security/Binary.lean`](Specifications/Security/Binary.lean) (`SignalSessionSecure`, `SignalSessionSecureReal`)
   - [`Theorems/Refinement.lean`](Theorems/Refinement.lean) and [`Theorems/Security.lean`](Theorems/Security.lean)
   - [`Tests/ExternWitness.lean`](Tests/ExternWitness.lean) (`comp_externsSatisfiable_cli`, `realAes256ContractsSatisfiable_cli`)

## Headline Theorems

| Module | Theorems | Target |
|---|---|---|
| [`Theorems/ModelSecurity.lean`](Theorems/ModelSecurity.lean) | `Proven.ForwardSecrecy.forward_secrecy`, `Proven.PostCompromiseSecurity.post_compromise_security`, and 8 `Proven.Handshake.*` properties (`alice_initiator_secrecy`, `bob_responder_secrecy`, `authentication`, `peer_authentication`, `handshake_forward_secrecy`, `kci_resistance`, `session_independence`, `hndl_resistance`) | default `lake build` |
| [`Theorems/RefinementPreservation.lean`](Theorems/RefinementPreservation.lean) | `Proven.RefinementPreservation.comp_refinement_preservation_cli` | default `lake build` |
| [`Tests/ExternWitness.lean`](Tests/ExternWitness.lean) | `Proven.ExternWitness.comp_externsSatisfiable_cli`, `Proven.ExternWitness.realAes256ContractsSatisfiable_cli` | default `lake build` |
| [`Theorems/Refinement.lean`](Theorems/Refinement.lean) | `Proven.Refinement.comp_refines_cli`, `Proven.Refinement.real_prims_admissible`, `Proven.Refinement.comp_refines_cli_real` | `lake build CliElfLib` |
| [`Theorems/Security.lean`](Theorems/Security.lean) | `Proven.Security.signal_session_secure`, `Proven.Security.signal_session_secure_real` | `lake build CliElfLib` |

In the ELF-direct binary theorems, every non-panic instruction executes from plain loaded ELF
memory (`ElfImage.loadState`, zero initial memory patches, pinned `AT_HWCAP = 0x1b`, DEV-CLI10)
with only the 18 `.symtab`-resolved Rust panic entry points intercepted as `SIGABRT` (DEV-E7),
and progress (`CliElfProgress` / `CliElfProgressReal`) excuses `libcrux_ml_kem` `SampleNTT`
divergence on concrete non-terminating SHAKE-128 seeds (DEV-CLI22). `signal_session_secure` and
`comp_refines_cli` quantify over primitive bundles `W : CliHooks` guarded per input by
`RealHooksAgreeOnInput`, whereas `signal_session_secure_real` and `comp_refines_cli_real` (backed
by `real_prims_admissible`) fix the primitives to the real linked ones (`realCliHooks` via
`RealPrimsMatch`) over guarded traces with no `RealHooksAgreeOnInput` filter (`elfRelReal`).

## Building and Checking

```bash
# 1. Build default symbolic model, preservation, tests, and BugInjection spec-half proofs:
lake build

# 2. Build the SHA-256-pinned stock ld.lld CLI ELF and the binary-level headlines:
./scripts/cli-elf-stock --stdbin --build
./scripts/cli-elf-stock --stdbin --verify-pin --lean-mod LibsignalBinary/Specifications/SignalSession/CliElf.lean
lake build CliElfLib

# 3. Audit import isolation, machine-freeness, trusted closures, and comparator replay:
python3 Symbolic/scripts/check_symbolic_deps.py
./scripts/trusted-closure.sh --symbolic --out-dir /tmp/closure-symbolic
./comparator/run.sh symbolic
```

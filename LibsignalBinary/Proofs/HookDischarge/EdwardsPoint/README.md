# `EdwardsPoint`: `curve25519-dalek` ARM64 Machine-Code Proofs

Untrusted (`**Checked by Lean.**`) ARM64 machine-code and algebraic soundness proofs for the
`curve25519-dalek` `5.0.0` operations executed directly by the `libsignal-cli` ELF
(`cliElfBytes`):

- `<MontgomeryPoint>::to_edwards` (`267` insns)
- `<EdwardsPoint>::compress` (`204` insns) and `<CompressedEdwardsY>::decompress` (`176` insns)
- `<EdwardsPoint>::is_torsion_free` (`32` insns)
- `<EdwardsPoint>::vartime_double_scalar_mul_basepoint` (`316` insns)
- `<&EdwardsPoint as Mul<&Scalar>>::mul` (`219` insns), `EdwardsBasepointTable::mul_base` (`167` insns), and `<&Scalar as Mul<&EdwardsBasepointTable>>::mul` (`4` insns)
- `<EdwardsPoint as ConstantTimeEq>::ct_eq` (`408` insns)
- `<Scalar>::from_bytes_mod_order` (`3` insns), `<Scalar>::from_bytes_mod_order_wide` (`277` insns), `<Scalar as Mul>::mul` (`24` insns), and `<Scalar as Add>::add` (`4` insns)
- `subtle::black_box::<u8>` (`5` insns)

All specifications target the Curve25519 reference definitions in
`arm64-semantics/VerifiedLibraries/Common/Spec/Curve25519.lean` (`EdPoint`, `EdExtPoint`,
`edAdd`, `edNeg`, `edSub`, `edSmul`, `encodeEd`, `montLiftEd`, `edOrderL`), and discharge the
corresponding `SignalPqxdh.isCanonicalRef` and `SignalPqxdh.xeddsaVerifyRef` operations directly
against the linked stock ELF via `dalekCliMultiLib.checkInElf`.

## Committed Object Bundle (Provenance & Licenses)

- **`DalekCliPlacedObj.bin`** (`68,068` bytes, loaded by `PlacedObjDefs.lean` via `include_bytes%`):
  extracted from the pinned `rustc 1.98.1` (`aarch64-unknown-linux-musl`) build of
  `third_party/libsignal/libsignal-session`. Contains `36` `.text.*` blocks and `11` `.rodata` /
  `.data.rel.ro` sections from `curve25519-dalek 5.0.0` (`BSD-3-Clause`), plus `1` stock `musl 1.2.5`
  (`MIT`) `memcpy` block (`37` blocks total, `dalekCliMultiLib : Obj.MultiPlacedLib`). Checked
  byte-for-byte against the linked `libsignal-cli` ELF in `LibsignalBinary/Proofs/SignalSession/Cli/`.

## Module Layout

- **Object bundle & placement base**: `PlacedObjDefs.lean`, `PlacedCodeBase.lean`, `CommonBase.lean`,
  `SliceBase.lean`, `RoTables.lean`, `InternalSpecs.lean`, `CurveSpecs.lean`, `MulSpecs.lean`.
- **Pure Curve25519 & Edwards algebra (`Math/`)**: field arithmetic over $\mathbb{F}_{2^{255}-19}$,
  twisted Edwards group laws, birational Montgomery–Edwards equivalence, scalar reduction mod $\ell$,
  point codecs, and double-scalar-multiplication bridges.
- **ARM64 block proofs**: `Layer0.lean`, `Field51Base.lean`, `Field51.lean`, `Field51Pow.lean`,
  `CurveModels2.lean`, `CurveModels3.lean`, `Scalar52.lean`, `Scalar.lean`, `LookupTableProj1.lean`,
  `LookupTableProj.lean`, `VariableBaseMul.lean`, `BasepointTable.lean`, `NafLookupTable1.lean`,
  `NafLookupTable2.lean`, `DoubleScalarMulNaf.lean`, `DoubleScalarMul.lean`, `PointCompress2.lean`,
  `PointCompress3.lean`, `MontToEdwards.lean`, `IsTorsionFree.lean`, assembled in `AllBlocksOk.lean`.
- **CLI & symbolic consumer bridges**: `ConsumerBridges.lean`, `DalekPureFallbacks.lean`,
  `Phase4RefBridge.lean`, `Phase4GhostHooks.lean`, `Phase4ConsumerGlue.lean`,
  `Phase4ActiveLocality.lean`, `Phase4Block202.lean`, `Phase4Block204.lean`, and
  `Phase4SymbolicBridge.lean` (threading the `5×51`-bit limb bounds across `MontgomeryPoint::to_edwards`,
  `is_torsion_free`, `<EdwardsPoint as Neg>::neg`, `vartime_double_scalar_mul_basepoint`, and
  `compress` into `SignalPqxdh` and `Symbolic`).

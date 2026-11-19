/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder -- proof-setup: allow-public-import

/-!
# X25519 Public-Key-From-Secret Edwards Basepoint Bridges (`LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath`)

Pure `0-sorry` mathematical bridge theorems connecting the fixed-base radix-16 Edwards table
pipeline (`edMulBase ed25519BasepointTableBytes (clampScalarBytes s)` followed by projective
birational conversion `edExtToMontgomeryU`) to RFC 7748 `x25519Pubkey s` and `x25519PubFromSecretRef`:
1. Projective-to-affine Montgomery $u$-coordinate equivalence (`edExtToMontgomeryU_eq_edToMontU_of_valid`).
2. Clamped basepoint table validity and affine scalar-multiplication identity
   (`edMulBase_clampScalarBytes_valid`, `edMulBase_clampScalarBytes_toAffine`).
3. End-to-end public-key bridge (`x25519Pubkey_eq_edBasepoint`, `edExtToMontgomeryU_mulBase_clamped`),
   non-low-order guarantees (`x25519Pubkey_not_lowOrder`, `x25519PubFromSecretRef_not_lowOrder`),
   and canonicality (`isCanonicalX25519_x25519Pubkey`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath

open VerifiedLibraries.Common (
  p25519 EdExtPoint edExtToAffine edBasepoint edSmul natToLeBytes clampScalarBytes clampScalar)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  decodeU255 x25519Basepoint x25519Pubkey x25519PubFromSecretRef isCanonicalX25519 lowOrderUs
  low_order_noncanonical_and_twist_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  ed25519BasepointTableBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  edExtToMontgomeryU edMulBase)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Edwards (
  Fp EdExtValid)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.Birational (
  edToMontU edToMontU_edExtToAffine)

/-- Projective `(Z + Y) * (Z - Y)⁻¹ mod p` agrees with affine `edToMontU (edExtToAffine P)`
    for every valid extended twisted Edwards point `P`. -/
theorem edExtToMontgomeryU_eq_edToMontU_of_valid {P : EdExtPoint} (hP : EdExtValid P) :
    edExtToMontgomeryU P = edToMontU (edExtToAffine P) :=
  (edToMontU_edExtToAffine ((Fp.ofNat_ne_zero_iff P.Z).mp hP.z_ne_zero)).symm

/-- `edMulBase` on `ed25519BasepointTableBytes` and any clamped 32-byte scalar produces a valid
    extended point on $E(\mathbb{F}_p)$. -/
theorem edMulBase_clampScalarBytes_valid {s : List (BitVec 8)} (hs : s.length = 32) :
    EdExtValid (edMulBase ed25519BasepointTableBytes (clampScalarBytes s)) :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul2.edMulBase_clampScalarBytes_valid hs

/-- `edMulBase` on `ed25519BasepointTableBytes` and any clamped 32-byte scalar represents
    `edSmul (clampScalar s) edBasepoint`. -/
theorem edMulBase_clampScalarBytes_toAffine {s : List (BitVec 8)} (hs : s.length = 32) :
    edExtToAffine (edMulBase ed25519BasepointTableBytes (clampScalarBytes s)) =
      edSmul (clampScalar s) edBasepoint :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Math.ScalarMul2.edMulBase_clampScalarBytes_toAffine hs

/-- RFC 7748 `x25519Pubkey s` equals the 32-byte little-endian encoding of the birational
    Montgomery $u$-coordinate of `edSmul (clampScalar s) edBasepoint`. -/
theorem x25519Pubkey_eq_edBasepoint (s : List (BitVec 8)) :
    x25519Pubkey s = natToLeBytes 32 (edToMontU (edSmul (clampScalar s) edBasepoint)) :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder.x25519Pubkey_eq_edBasepoint s

/-- End-to-end pure functional equivalence between `curve25519-dalek`'s fixed-base radix-16
    `EdwardsPoint::mul_base` + `EdwardsPoint::to_montgomery` pipeline and RFC 7748 `x25519Pubkey`. -/
theorem edExtToMontgomeryU_mulBase_clamped {s : List (BitVec 8)} (hs : s.length = 32) :
    natToLeBytes 32
        (edExtToMontgomeryU (edMulBase ed25519BasepointTableBytes (clampScalarBytes s))) =
      x25519Pubkey s := by
  rw [edExtToMontgomeryU_eq_edToMontU_of_valid (edMulBase_clampScalarBytes_valid hs),
      edMulBase_clampScalarBytes_toAffine hs,
      ← x25519Pubkey_eq_edBasepoint s]

/-- Derived X25519 public keys never lie in `lowOrderUs`. -/
theorem x25519Pubkey_not_lowOrder (s : List (BitVec 8)) :
    decodeU255 (x25519Pubkey s) % p25519 ∉ lowOrderUs :=
  LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder.x25519Pubkey_not_lowOrder s

/-- `List.Vector` hook public-key derivation `x25519PubFromSecretRef` never lies in `lowOrderUs`. -/
theorem x25519PubFromSecretRef_not_lowOrder (sk : List.Vector (BitVec 8) 32) :
    decodeU255 (x25519PubFromSecretRef sk).toList % p25519 ∉ lowOrderUs :=
  x25519Pubkey_not_lowOrder sk.toList

/-- Every derived X25519 public key `x25519Pubkey s` satisfies `libsignal-core`'s
    `isCanonicalX25519` predicate. -/
theorem isCanonicalX25519_x25519Pubkey (s : List (BitVec 8)) :
    isCanonicalX25519 (x25519Pubkey s) = true := by
  unfold x25519Pubkey
  exact LibsignalBinary.Proofs.HookDischarge.CryptoX25519.MontgomeryLadder.isCanonicalX25519_x25519
    low_order_noncanonical_and_twist_ok.2.2.1

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath

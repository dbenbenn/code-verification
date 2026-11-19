/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.ModelProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy -- proof-setup: allow-public-import

/-!
# `<PublicKey>::is_canonical` Specs and Shared Curve/XEdDSA Helpers

Defines `ecPubKeyIsCanonicalCallSpec`, `StructuralPrims`, Curve25519/SHA-512 stub specs, and shared
bitvector/layout lemmas for `<libsignal_core::curve::PublicKey>::is_canonical` and `VerifySignature`.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open SignalPqxdh
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
  (packEdBytes unpackEdBytes packEdBytes_length unpackEdBytes_packEdBytes
   packEdBytes_unpackEdBytes unpackEdBytes_coords_lt montLiftEd_coords_lt
   edNeg_coords_lt edAdd_coords_lt legacyMontToEd legacyIsTorsionFree legacyDsmb
   legacyCompress legacyEdNeg legacyScalarMod legacyScalarWide
   toEdwardsName torsionFreeName packEd160 unpackEd160 packEdBv8 unpackEdBv8)

abbrev Bytes := SignalPqxdh.Bytes

/-- `P.montToEd` packed into 160 `UInt8` bytes (`80 + 80` little-endian coordinates). -/
@[expose] def _root_.SignalPqxdh.Primitives.montToEdBytes (P : Primitives) (u : Bytes) (s : UInt8) :
    Option Bytes :=
  (P.montToEd u s).map packEdBytes

/-- `P.isTorsionFree` over a 160-byte packed `EdPoint`. -/
@[expose] def _root_.SignalPqxdh.Primitives.isTorsionFreeBytes (P : Primitives) (pt : Bytes) : Bool :=
  P.isTorsionFree (unpackEdBytes pt)

/-- `P.edNeg` over a 160-byte packed `EdPoint`. -/
@[expose] def _root_.SignalPqxdh.Primitives.edNegBytes (P : Primitives) (pt : Bytes) : Bytes :=
  packEdBytes (P.edNeg (unpackEdBytes pt))

/-- `P.doubleScalarMulBasepoint` over a 160-byte packed `EdPoint`. -/
@[expose] def _root_.SignalPqxdh.Primitives.doubleScalarMulBasepointBytes (P : Primitives)
    (h a s : Bytes) : Bytes :=
  packEdBytes (P.doubleScalarMulBasepoint h (unpackEdBytes a) s)

/-- `P.compress` over a 160-byte packed `EdPoint`. -/
@[expose] def _root_.SignalPqxdh.Primitives.compressBytes (P : Primitives) (pt : Bytes) : Bytes :=
  P.compress (unpackEdBytes pt)

theorem _root_.SignalPqxdh.Primitives.montToEdBytes_len (P : Primitives)
    (u : Bytes) (s : UInt8) (pt : Bytes)
    (h : P.montToEdBytes u s = some pt) : pt.length = 160 := by
  rcases Option.map_eq_some_iff.mp h with ⟨_, _, rfl⟩
  exact packEdBytes_length _

@[simp] theorem _root_.SignalPqxdh.Primitives.edNegBytes_len (P : Primitives) (pt : Bytes) :
    (P.edNegBytes pt).length = 160 :=
  packEdBytes_length _

@[simp] theorem _root_.SignalPqxdh.Primitives.doubleScalarMulBasepointBytes_len
    (P : Primitives) (h a s : Bytes) :
    (P.doubleScalarMulBasepointBytes h a s).length = 160 :=
  packEdBytes_length _

@[simp] theorem _root_.SignalPqxdh.Primitives.compressBytes_len {P : Primitives}
    (hcomp : ∀ p, (P.compress p).length = 32) (pt : Bytes) :
    (P.compressBytes pt).length = 32 :=
  hcomp _

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := rfl

theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setMem m).setPC pc).sp = s.sp := rfl

theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := rfl

theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setMem m).setPC pc).readReg64 r = s.readReg64 r := rfl

theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := rfl

theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setMem m).setPC pc).readReg32 r = s.readReg32 r := rfl

theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := rfl

theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setMem m).setPC pc).readReg w r = s.readReg w r := rfl

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

theorem bv_sub_sub_lit (x : BitVec 64) (a b : Nat) (_h : a + b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem bv_add_neg64 (x : BitVec 64) :
    x + -64#64 = x - 64#64 := by bv_omega

attribute [local arm64_norm] bv_sub_sub_lit bv_add_neg64

/-! ## Byte Conversion and Memory Region Helpers -/

@[simp] theorem fitBytes_length (n : Nat) (bs : Bytes) : (fitBytes n bs).length = n := by
  simp [fitBytes]
  omega

theorem fitBytes_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) : fitBytes n bs = bs := by
  subst h
  simp [fitBytes]

@[expose] def bytesToBv8 (bs : Bytes) : List (BitVec 8) :=
  bs.map (fun b => BitVec.ofNat 8 b.toNat)

@[expose] def fitBv8 (n : Nat) (bs : Bytes) : List (BitVec 8) :=
  (bytesToBv8 bs).take n ++ List.replicate (n - (bytesToBv8 bs).length) 0#8

@[simp]
theorem fitBv8_length (n : Nat) (bs : Bytes) : (fitBv8 n bs).length = n := by
  simp [fitBv8]
  omega

theorem fitBv8_eq_bytesToBv8 {n : Nat} {bs : Bytes} (h : bs.length = n) :
    fitBv8 n bs = bytesToBv8 bs := by
  have hb : (bytesToBv8 bs).length = n := by simp [bytesToBv8, h]
  simp [fitBv8, hb]

@[expose] def u64le (w : BitVec 64) : List (BitVec 8) :=
  unpack64 w

abbrev pqxdhHookStack : Nat := 4096
abbrev pqxdhEntryStack : Nat := 16384

theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k :=
  ProofLib.memRegion_cells a k h

theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k :=
  ProofLib.stackAt_split_cells sp n k h

/-! ## Curve25519-Dalek and SHA-512 Hook Contracts -/

abbrev ecPubKeyIsCanonicalSym : String :=
  "<libsignal_core::curve::PublicKey>::is_canonical"
abbrev verifySignatureSym : String :=
  "<libsignal_core::curve::PublicKey>::verify_signature"
abbrev verifySignatureMultipartSym : String :=
  "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message"

abbrev sha512CompressStub : String := "sha2::sha512::compress512"
abbrev dalekScalarWideStub : String :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide"
abbrev dalekScalarModStub : String :=
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order"
abbrev dalekCompressStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::compress"
abbrev dalekMontToEdStub : String :=
  "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"
abbrev dalekTorsionFreeStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"
abbrev dalekEdNegStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg"
abbrev dalekDoubleMulStub : String :=
  "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint"

structure CryptoUnaryGhost where
  inPtr   : BitVec 64
  inBytes : Bytes

@[expose] def cryptoBoolRegStubSpec (pred : Bytes → Bool) (inLen : Nat) (_img : Unit := ()) :
    Spec CryptoUnaryGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 32 = (if pred g.inBytes then 1#32 else 0#32)⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      stackAt s0.sp pqxdhHookStack

structure CryptoLeafCall where
  inPtr   : BitVec 64
  inBytes : Bytes
  outPtr  : BitVec 64

@[expose] def cryptoLeafStubSpec (fn : Bytes → Bytes) (inLen outLen : Nat) : Spec CryptoLeafCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr outLen ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      (g.outPtr ↦ₛ fitBv8 outLen (fn g.inBytes)) ∗
      stackAt s0.sp pqxdhHookStack

@[expose] def revWords64 (bs : Bytes) : Bytes :=
  ((bs.take 8).reverse ++
   ((bs.drop 8).take 8).reverse ++
   ((bs.drop 16).take 8).reverse ++
   ((bs.drop 24).take 8).reverse ++
   ((bs.drop 32).take 8).reverse ++
   ((bs.drop 40).take 8).reverse ++
   ((bs.drop 48).take 8).reverse ++
   ((bs.drop 56).take 8).reverse)

@[expose] def sha512CompressOutBytes (P : Primitives) (stateBytes blockBytes : Bytes) : Bytes :=
  revWords64 (fitBytes 64
    ((chunkBlocks 128 blockBytes).foldl (sha512Step P) (revWords64 stateBytes)))

structure CryptoCompressGhost where
  statePtr   : BitVec 64
  stateBytes : Bytes
  blocksPtr  : BitVec 64
  blockBytes : Bytes
  nBlocks    : Nat

@[expose] def compressInPlaceStubSpec (fn : Bytes → Bytes → Bytes) (stateLen blockLen : Nat)
    (_img : Unit := ()) : Spec CryptoCompressGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.statePtr ∧
      s.readReg64 .x1 = g.blocksPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.nBlocks ∧
      g.nBlocks < 2 ^ 64 ∧
      g.stateBytes.length = stateLen ∧
      g.blockBytes.length = blockLen * g.nBlocks⌝ ∗
      (g.statePtr ↦ₛ bytesToBv8 g.stateBytes) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.statePtr ↦ₛ fitBv8 stateLen (fn g.stateBytes g.blockBytes)) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s0.sp pqxdhHookStack

@[expose] def dalekMontToEdOutAt (P : Primitives) (outPtr : BitVec 64) (inBytes : Bytes)
    (signBit : UInt8) : SepProp :=
  match P.montToEdBytes inBytes signBit with
  | some edPt => outPtr ↦ₛ (u64le 1#64 ++ fitBv8 160 edPt)
  | none      => (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 160

structure DalekMontToEdGhost where
  inBytes : Bytes
  signBit : UInt8
  inPtr   : BitVec 64
  outPtr  : BitVec 64

@[expose] def dalekMontToEdStubSpec (P : Primitives) (_img : Unit := ()) :
    Spec DalekMontToEdGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧
      (s.readReg64 .x1).setWidth 8 = BitVec.ofNat 8 g.signBit.toNat ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      memRegion g.outPtr 168 ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes (g.signBit &&& 1) ∗
      stackAt s0.sp pqxdhHookStack

theorem signBit_shr7_and_one (b : UInt8) :
    (((b &&& 0x80) >>> 7) &&& 1 : UInt8) = ((b &&& 0x80) >>> 7 : UInt8) := by
  have h : ∀ i : Fin 256,
      (((UInt8.ofBitVec (BitVec.ofFin i) &&& 0x80) >>> 7) &&& 1 : UInt8) =
        ((UInt8.ofBitVec (BitVec.ofFin i) &&& 0x80) >>> 7 : UInt8) := by decide
  rcases b with ⟨⟨i⟩⟩
  exact h i

structure DalekDoubleMulGhost where
  hBytes    : Bytes
  negABytes : Bytes
  sBytes    : Bytes
  hPtr      : BitVec 64
  negAPtr   : BitVec 64
  sPtr      : BitVec 64
  outPtr    : BitVec 64

@[expose] def dalekDoubleMulStubSpec (P : Primitives) (_img : Unit := ()) :
    Spec DalekDoubleMulGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.hPtr ∧
      s.readReg64 .x1 = g.negAPtr ∧
      s.readReg64 .x2 = g.sPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.hBytes.length = 32 ∧
      g.negABytes.length = 160 ∧
      g.sBytes.length = 32⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      memRegion g.outPtr 160 ∗
      stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.hPtr ↦ₛ bytesToBv8 g.hBytes) ∗
      (g.negAPtr ↦ₛ bytesToBv8 g.negABytes) ∗
      (g.sPtr ↦ₛ bytesToBv8 g.sBytes) ∗
      (g.outPtr ↦ₛ fitBv8 160 (P.doubleScalarMulBasepointBytes g.hBytes g.negABytes g.sBytes)) ∗
      stackAt s0.sp pqxdhHookStack

theorem zext64_bv32_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    ((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64).setWidth 8 = b0 := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [BitVec.setWidth_append, ↓reduceDIte]
  exact BitVec.setWidth_eq b0

theorem zext64_bv32_shr8_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64) >>> 8#64).setWidth 8 = b1 := by
  bv_bits

theorem zext64_bv32_shr16_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64) >>> 16#64).setWidth 8 = b2 := by
  bv_bits

theorem zext64_bv32_shr24_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ (b2 ++ (b1 ++ b0))).zeroExtend 64) >>> 24#64).setWidth 8 = b3 := by
  bv_bits

theorem zext64_bv16_setWidth_8 (b0 b1 : BitVec 8) :
    ((b1 ++ b0).zeroExtend 64).setWidth 8 = b0 := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [BitVec.setWidth_append, ↓reduceDIte]
  exact BitVec.setWidth_eq b0

theorem zext64_bv16_shr8_setWidth_8 (b0 b1 : BitVec 8) :
    (((b1 ++ b0).zeroExtend 64) >>> 8#64).setWidth 8 = b1 := by
  bv_bits

theorem zext64_bv8_setWidth_8 (b0 : BitVec 8) :
    (b0.zeroExtend 64).setWidth 8 = b0 := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Structural length, coordinate-bound, totality, and reference-equivalence laws on
`SignalPqxdh.Primitives` used by machine-code refinement proofs, satisfied unconditionally by
`modelPrims X W` (`structuralPrims_modelPrims`). -/
structure StructuralPrims (P : Primitives) : Prop where
  sha256Compress_len           : ∀ st blk, (P.sha256Compress st blk).length = 32
  sha512Compress_len           : ∀ st blk, (P.sha512Compress st blk).length = 64
  aesEncBlock_len              : ∀ k blk, (P.aesEncBlock k blk).length = 16
  aesDecBlock_len              : ∀ k blk, (P.aesDecBlock k blk).length = 16
  sha512_eq_ref                : ∀ m, P.sha512 m = sha512Ref P m
  hkdfDerive96_eq_ref          : ∀ secrets, P.hkdfDerive96 secrets = hkdfDerive96Ref P secrets
  rootCreateChain_eq_ref       : ∀ rk dh, P.rootCreateChain rk dh = rootCreateChainRef P rk dh
  chainKdfSeed_eq_ref          : ∀ ck, P.chainKdfSeed ck = chainKdfSeedRef P ck
  chainKdfNext_eq_ref          : ∀ ck, P.chainKdfNext ck = chainKdfNextRef P ck
  deriveMsgKeys_eq_ref         :
    ∀ mkSeed salt?, P.deriveMsgKeys mkSeed salt? = deriveMsgKeysRef P mkSeed salt?
  aeadEnc_eq_ref               : ∀ mk ad pt, P.aeadEnc mk ad pt = aes256CbcHmacEncRef P mk ad pt
  aeadDec_eq_ref               : ∀ mk ad ct, P.aeadDec mk ad ct = aes256CbcHmacDecRef P mk ad ct
  sigVerify_eq_xeddsaVerifyRef : ∀ pk m sig, P.sigVerify pk m sig = xeddsaVerifyRef P pk m sig
  isCanonical_eq_isCanonicalRef : ∀ pk, P.isCanonical pk = isCanonicalRef P pk
  x25519_len                   : ∀ k p, (P.x25519 k p).length = 32
  x25519Base_len               : ∀ k, (P.x25519Base k).length = 32
  sha512_len                   : ∀ m, (P.sha512 m).length = 64
  scalarFromBytesModOrder_len  : ∀ b, (P.scalarFromBytesModOrder b).length = 32
  scalarFromWide_len           : ∀ b, (P.scalarFromWide b).length = 32
  montToEd_lt                  : ∀ u s pt, P.montToEd u s = some pt →
                                   pt.x < 256 ^ 80 ∧ pt.y < 256 ^ 80
  edNeg_lt                     : ∀ pt, (P.edNeg pt).x < 256 ^ 80 ∧ (P.edNeg pt).y < 256 ^ 80
  doubleScalarMulBasepoint_lt  : ∀ h a s,
                                   (P.doubleScalarMulBasepoint h a s).x < 256 ^ 80 ∧
                                     (P.doubleScalarMulBasepoint h a s).y < 256 ^ 80
  compress_len                 : ∀ pt, (P.compress pt).length = 32
  kemEncaps_isSome             : ∀ pk r, pk.length = 1568 → r.length = 32 →
                                   (P.kemEncaps pk r).isSome = true
  kemEncaps_len                : ∀ pk r ss ct,
                                   P.kemEncaps pk r = some (ss, ct) →
                                   ss.length = 32 ∧ ct.length = 1568
  kemDecaps_isSome             : ∀ sk ct, sk.length = 3168 → ct.length = 1568 →
                                   (P.kemDecaps sk ct).isSome = true
  kemDecaps_len                : ∀ sk ct ss,
                                   P.kemDecaps sk ct = some ss →
                                   ss.length = 32
  spqrInitSend_some            : ∀ k r, (P.spqrInitSend k r).isSome = true

private theorem flatMap_toBEBytes_length_shared {w : Nat} (n : Nat) :
    ∀ l : List (BitVec w), (l.flatMap (HMAC.toBEBytes n)).length = n * l.length
  | [] => by simp
  | x :: xs => by
    have hx : (HMAC.toBEBytes n x).length = n := by simp [HMAC.toBEBytes]
    simp only [List.flatMap_cons, List.length_append, hx, flatMap_toBEBytes_length_shared n xs,
      List.length_cons, Nat.mul_succ]; omega

theorem structuralPrims_modelPrims (X : E2E.UnreachedPqxdhPrimitives) (W : E2E.PEParams) :
    StructuralPrims (E2E.modelPrims X W) where
  sha256Compress_len _ _ := by
    change (E2E.toU8 _).length = 32
    rw [E2E.toU8, List.length_map, flatMap_toBEBytes_length_shared 4, List.Vector.toList_length]
  sha512Compress_len _ _ := by
    change (E2E.toU8 _).length = 64
    rw [E2E.toU8, List.length_map, flatMap_toBEBytes_length_shared 8, List.Vector.toList_length]
  aesEncBlock_len _ _ := by
    simp [E2E.modelPrims, E2E.blockLevelPrims, E2E.toU8,
      LibsignalAesCbc.blockToBytes, LibsignalAesCbc.toLEBytes]
  aesDecBlock_len _ _ := by
    simp [E2E.modelPrims, E2E.blockLevelPrims, E2E.toU8,
      LibsignalAesCbc.blockToBytes, LibsignalAesCbc.toLEBytes]
  sha512_eq_ref := E2E.modelPrims_sha512_eq_ref X W
  hkdfDerive96_eq_ref := E2E.modelPrims_hkdfDerive96_eq_ref X W
  rootCreateChain_eq_ref := E2E.modelPrims_rootCreateChain_eq_ref X W
  chainKdfSeed_eq_ref := E2E.modelPrims_chainKdfSeed_eq_ref X W
  chainKdfNext_eq_ref := E2E.modelPrims_chainKdfNext_eq_ref X W
  deriveMsgKeys_eq_ref := E2E.modelPrims_deriveMsgKeys_eq_ref X W
  aeadEnc_eq_ref := E2E.modelPrims_aeadEnc_eq_ref X W
  aeadDec_eq_ref := E2E.modelPrims_aeadDec_eq_ref X W
  sigVerify_eq_xeddsaVerifyRef := E2E.modelPrims_sigVerify_eq_ref X W
  isCanonical_eq_isCanonicalRef := E2E.modelPrims_isCanonical_eq_ref X W
  x25519_len _ _ := by simp [E2E.modelPrims, E2E.blockLevelPrims, E2E.vecU8, E2E.toU8]
  x25519Base_len _ := by simp [E2E.modelPrims, E2E.blockLevelPrims, E2E.vecU8, E2E.toU8]
  sha512_len m := by
    rw [E2E.modelPrims_sha512_eq_ref X W m, sha512Ref]
    exact fitBytesRef_length 64 _
  scalarFromBytesModOrder_len _ := by
    simp [E2E.modelPrims, E2E.blockLevelPrims, E2E.toU8, VerifiedLibraries.Common.natToLeBytes]
  scalarFromWide_len _ := by
    simp [E2E.modelPrims, E2E.blockLevelPrims, E2E.toU8, VerifiedLibraries.Common.natToLeBytes]
  montToEd_lt _ _ _ h := montLiftEd_coords_lt h
  edNeg_lt pt := edNeg_coords_lt pt
  doubleScalarMulBasepoint_lt _ _ _ := edAdd_coords_lt _ _
  compress_len _ := by
    simp [E2E.modelPrims, E2E.blockLevelPrims, E2E.toU8,
      VerifiedLibraries.Common.encodeEd, VerifiedLibraries.Common.natToLeBytes]
  kemEncaps_isSome _ _ hpk _ := by
    simp [E2E.modelPrims, E2E.blockLevelPrims, SignalPqxdh.kyberPkLen, hpk]
  kemEncaps_len _ _ _ _ h := by
    dsimp only [E2E.modelPrims, E2E.blockLevelPrims] at h
    split at h <;> [skip; simp at h]
    injection h with hpair; injection hpair with hss hct; subst hss hct
    simp [E2E.vecU8, E2E.toU8]
  kemDecaps_isSome _ _ _ hct := by
    simp [E2E.modelPrims, E2E.blockLevelPrims, SignalPqxdh.kyberCtLen, hct]
  kemDecaps_len _ _ _ h := by
    dsimp only [E2E.modelPrims, E2E.blockLevelPrims] at h
    split at h <;> [skip; simp at h]
    injection h with hss; subst hss
    simp [E2E.vecU8, E2E.toU8]
  spqrInitSend_some _ _ := rfl

structure KeyCanonicalGhost where
  keyPtr   : BitVec 64
  keyBytes : Bytes

abbrev PqxdhHookContracts : Type := Unit

/-! ## `<libsignal_core::curve::PublicKey>::is_canonical` (`0x3dc60`) -/

@[expose] def ecPubKeyIsCanonicalCallSpec (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s.sp (pqxdhHookStack + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s0.sp (pqxdhHookStack + 400)

theorem stackAt_ecPubKeyIsCanonical_call (sp : BitVec 64) :
    stackAt sp (pqxdhHookStack + 400) =
      stackAt (sp - 400#64) pqxdhHookStack ∗
      cells (sp - 400#64) 4 ∗
      memRegion (sp - 368#64) 8 ∗
      memRegion (sp - 360#64) 168 ∗
      memRegion (sp - 192#64) 160 ∗
      cells (sp - 32#64) 4 := by
  rw [show (pqxdhHookStack + 400 : Nat) = pqxdhHookStack + 8 * 50 by decide,
    stackAt_split_cells sp pqxdhHookStack 50 (by decide),
    ← memRegion_cells (sp - 400#64) 50 (by decide)]
  change stackAt (sp - 400#64) pqxdhHookStack ∗ memRegion (sp - 400#64) 400 = _
  rw [memRegion_split (sp - 400#64) 32 368 (by decide),
    memRegion_cells (sp - 400#64) 4 (by decide),
    memRegion_split (sp - 400#64 + 32#64) 8 360 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64) 168 192 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64 + 168#64) 160 32 (by decide),
    memRegion_cells (sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64) 4 (by decide)]
  have h1 : sp - 400#64 + 32#64 = sp - 368#64 := by bv_arith
  have h2 : sp - 400#64 + 32#64 + 8#64 = sp - 360#64 := by bv_arith
  have h3 : sp - 400#64 + 32#64 + 8#64 + 168#64 = sp - 192#64 := by bv_arith
  have h4 : sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64 = sp - 32#64 := by bv_arith
  rw [h4, h3, h2, h1]

theorem dalekMontToEdOutAt_none (P : Primitives) (keyBytes : Bytes) (signBit : UInt8)
    (hmont : P.montToEdBytes keyBytes signBit = none) (a : BitVec 64) :
    dalekMontToEdOutAt P a keyBytes signBit =
      (a ↦₆₄ 0#64) ∗ memRegion (a + 8#64) 160 := by
  simp only [dalekMontToEdOutAt, hmont]

theorem dalekMontToEdOutAt_some (P : Primitives) (keyBytes edPt : Bytes) (signBit : UInt8)
    (hmont : P.montToEdBytes keyBytes signBit = some edPt) (hlen : edPt.length = 160) (a : BitVec 64) :
    dalekMontToEdOutAt P a keyBytes signBit =
      (a ↦₆₄ 1#64) ∗ ((a + 8#64) ↦ₛ bytesToBv8 edPt) := by
  simp only [dalekMontToEdOutAt, hmont, fitBv8_eq_bytesToBv8 hlen]
  have hu : u64le 1#64 = unpack64 1#64 := rfl
  rw [hu, pointsToBytes_append, show (unpack64 1#64).length = 8 by rfl,
    ← pointsTo64_eq_pointsToBytes]

private theorem memRegion168_of_cell_and_memRegion160 (a : BitVec 64) (v : BitVec 64)
    (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion168_of_cell_and_bytes160 (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  have h2 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (a + 8#64) bs
  refine Entails.trans (sepConj_mono_left h1) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h2)) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]
  exact Entails.refl _

private theorem memRegion160_of_bytes160 (a : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦ₛ bs) ∗ R_tail ⊢ memRegion a 160 ∗ R_tail := by
  have h1 : (a ↦ₛ bs) ⊢ memRegion a 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion a bs
  exact sepConj_mono_left h1

private theorem exists_unpack64_of_length_160 {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a R_tail,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1 ∗ ((a + 16#64) ↦₆₄ w2 ∗ ((a + 24#64) ↦₆₄ w3 ∗
        ((a + 32#64) ↦₆₄ w4 ∗ ((a + 40#64) ↦₆₄ w5 ∗ ((a + 48#64) ↦₆₄ w6 ∗ ((a + 56#64) ↦₆₄ w7 ∗
        ((a + 64#64) ↦₆₄ w8 ∗ ((a + 72#64) ↦₆₄ w9 ∗ ((a + 80#64) ↦₆₄ w10 ∗ ((a + 88#64) ↦₆₄ w11 ∗
        ((a + 96#64) ↦₆₄ w12 ∗ ((a + 104#64) ↦₆₄ w13 ∗ ((a + 112#64) ↦₆₄ w14 ∗
        ((a + 120#64) ↦₆₄ w15 ∗ ((a + 128#64) ↦₆₄ w16 ∗ ((a + 136#64) ↦₆₄ w17 ∗
        ((a + 144#64) ↦₆₄ w18 ∗ ((a + 152#64) ↦₆₄ w19 ∗
         R_tail))))))))))))))))))) =
        (a ↦ₛ bs) ∗ R_tail := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  have h4 : (bs.drop 128).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 h4
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, fun a R_tail => ?_⟩
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++
      ((bs.drop 64).take 32 ++ ((bs.drop 96).take 32 ++ bs.drop 128))) := by
    have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
    have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
    have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
      simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
    have s1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    rw [s4] at s3
    rw [s3] at s2
    rw [s2] at s1
    exact s1
  symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0,
    pointsToBytes_append, h1, hp1,
    pointsToBytes_append, h2, hp2,
    pointsToBytes_append, h3, hp3, hp4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sepWP_memRegion160_head {prog : Program} {ret : BitVec 64} {s : State}
    (a : BitVec 64) {P_pre F_rest : SepProp}
    (heq : P_pre = memRegion a 160 ∗ F_rest) {Q : State → SepProp → Prop}
    (h : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 : BitVec 64,
      SepWP prog ret s
        ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1 ∗ ((a + 16#64) ↦₆₄ u2 ∗ ((a + 24#64) ↦₆₄ u3 ∗
        ((a + 32#64) ↦₆₄ u4 ∗ ((a + 40#64) ↦₆₄ u5 ∗ ((a + 48#64) ↦₆₄ u6 ∗ ((a + 56#64) ↦₆₄ u7 ∗
        ((a + 64#64) ↦₆₄ u8 ∗ ((a + 72#64) ↦₆₄ u9 ∗ ((a + 80#64) ↦₆₄ u10 ∗ ((a + 88#64) ↦₆₄ u11 ∗
        ((a + 96#64) ↦₆₄ u12 ∗ ((a + 104#64) ↦₆₄ u13 ∗ ((a + 112#64) ↦₆₄ u14 ∗
        ((a + 120#64) ↦₆₄ u15 ∗ ((a + 128#64) ↦₆₄ u16 ∗ ((a + 136#64) ↦₆₄ u17 ∗
        ((a + 144#64) ↦₆₄ u18 ∗ ((a + 152#64) ↦₆₄ u19 ∗
         F_rest)))))))))))))))))))) Q) :
    SepWP prog ret s P_pre Q := by
  rw [heq, memRegion_eq_exists_bytes a 160 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hlen => ?_
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15,
    u16, u17, u18, u19, hbs⟩ :=
    exists_unpack64_of_length_160 hlen
  rw [← hbs a F_rest]
  exact h u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19


private theorem bytesToBv8_getD (bs : Bytes) (i : Nat) :
    (bytesToBv8 bs).getD i 0#8 = (bs.getD i 0).toBitVec := by
  induction bs generalizing i with
  | nil => simp [bytesToBv8]
  | cons b rest ih =>
    cases i with
    | zero => rcases b with ⟨⟨val, isLt⟩⟩; simp [bytesToBv8]
    | succ j => exact ih j

private theorem uint8_getLsbD7_eq_true_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = true ↔ ((b &&& 0x80) == 0) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_getLsbD7_eq_false_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = false ↔ ((b &&& 0x80) == 0) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_true_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = true ↔ decide (b ≥ 0xED) = false := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_ult237_eq_false_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = false ↔ decide (b ≥ 0xED) = true := by
  rcases b with ⟨bv⟩
  revert bv; decide

private theorem uint8_b31_7f_eq (b : UInt8) (h7 : ((b &&& 0x80) == 0) = true) :
    (BitVec.truncate 32 (BitVec.signExtend 64 b.toBitVec) == 127#32) = ((b &&& 0x7F) == 0x7F) := by
  rcases b with ⟨bv⟩
  revert bv h7; decide

private theorem uint8_toBitVec_eq_ff_iff (b : UInt8) :
    (b.toBitVec = 0xff#8) ↔ (b = 0xFF) := by
  rcases b with ⟨bv⟩
  constructor
  · intro h; subst h; rfl
  · intro h; exact congrArg UInt8.toBitVec h

private theorem bv64_add1_eq_zero_iff (x : BitVec 64) :
    (x + 1#64 == 0#64) = (x == 0xffffffffffffffff#64) := by
  bv_bits

private theorem bv64_allOnes_getElem (i : Nat) (hi : i < 64) :
    (0xffffffffffffffff#64 : BitVec 64)[i] = true := by
  revert i hi; decide

private theorem bv64_and_eq_allOnes_iff (a b : BitVec 64) :
    (a &&& b = 0xffffffffffffffff#64) ↔
      (a = 0xffffffffffffffff#64 ∧ b = 0xffffffffffffffff#64) := by
  constructor
  · intro h
    constructor
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.1
    · ext i hi
      have hi' := congrArg (fun v : BitVec 64 => v[i]) h
      rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi'
      rw [bv64_allOnes_getElem i hi]
      exact hi'.2
  · rintro ⟨rfl, rfl⟩; rfl

private theorem pack64_eq_allOnes_iff (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7 = 0xffffffffffffffff#64) ↔
      (b0 = 0xff#8 ∧ b1 = 0xff#8 ∧ b2 = 0xff#8 ∧ b3 = 0xff#8 ∧
       b4 = 0xff#8 ∧ b5 = 0xff#8 ∧ b6 = 0xff#8 ∧ b7 = 0xff#8) := by
  unfold pack64
  bv_bits

private theorem list_take_drop_succ (xs : List UInt8) (i n : Nat) (hi : i < xs.length) :
    (xs.drop i).take (n + 1) = xs.getD i 0 :: (xs.drop (i + 1)).take n := by
  have hget : xs.getD i 0 = xs[i] := by simp [List.getD, hi]
  rw [List.drop_eq_getElem_cons hi, ← hget]
  rfl

private theorem list32_drop1_take30_eq (xs : List UInt8) (h : xs.length = 32) :
    (xs.drop 1).take 30 =
      [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] := by
  repeat (rw [list_take_drop_succ _ _ _ (by omega)])
  rfl

private theorem list32_drop1_take30_eq_replicate_iff (xs : List UInt8) (h : xs.length = 32) :
    ((xs.drop 1).take 30 == List.replicate 30 0xFF) = true ↔
      (xs.getD 1 0 = 0xFF ∧ xs.getD 2 0 = 0xFF ∧ xs.getD 3 0 = 0xFF ∧ xs.getD 4 0 = 0xFF ∧
       xs.getD 5 0 = 0xFF ∧ xs.getD 6 0 = 0xFF ∧ xs.getD 7 0 = 0xFF ∧ xs.getD 8 0 = 0xFF ∧
       xs.getD 9 0 = 0xFF ∧ xs.getD 10 0 = 0xFF ∧ xs.getD 11 0 = 0xFF ∧ xs.getD 12 0 = 0xFF ∧
       xs.getD 13 0 = 0xFF ∧ xs.getD 14 0 = 0xFF ∧ xs.getD 15 0 = 0xFF ∧ xs.getD 16 0 = 0xFF ∧
       xs.getD 17 0 = 0xFF ∧ xs.getD 18 0 = 0xFF ∧ xs.getD 19 0 = 0xFF ∧ xs.getD 20 0 = 0xFF ∧
       xs.getD 21 0 = 0xFF ∧ xs.getD 22 0 = 0xFF ∧ xs.getD 23 0 = 0xFF ∧ xs.getD 24 0 = 0xFF ∧
       xs.getD 25 0 = 0xFF ∧ xs.getD 26 0 = 0xFF ∧ xs.getD 27 0 = 0xFF ∧ xs.getD 28 0 = 0xFF ∧
       xs.getD 29 0 = 0xFF ∧ xs.getD 30 0 = 0xFF) := by
  rw [beq_iff_eq, list32_drop1_take30_eq xs h]
  change [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0,
       xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
       xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
       xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
       xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] =
      [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] ↔ _
  simp only [List.cons.injEq, and_true]

private theorem pack64_4_allOnes_eq_drop1_take30 (keyBytes : Bytes) (h : keyBytes.length = 32) :
    ((pack64 ((bytesToBv8 keyBytes).getD 1 0#8) ((bytesToBv8 keyBytes).getD 2 0#8)
              ((bytesToBv8 keyBytes).getD 3 0#8) ((bytesToBv8 keyBytes).getD 4 0#8)
              ((bytesToBv8 keyBytes).getD 5 0#8) ((bytesToBv8 keyBytes).getD 6 0#8)
              ((bytesToBv8 keyBytes).getD 7 0#8) ((bytesToBv8 keyBytes).getD 8 0#8) &&&
            pack64 ((bytesToBv8 keyBytes).getD 9 0#8) ((bytesToBv8 keyBytes).getD 10 0#8)
              ((bytesToBv8 keyBytes).getD 11 0#8) ((bytesToBv8 keyBytes).getD 12 0#8)
              ((bytesToBv8 keyBytes).getD 13 0#8) ((bytesToBv8 keyBytes).getD 14 0#8)
              ((bytesToBv8 keyBytes).getD 15 0#8) ((bytesToBv8 keyBytes).getD 16 0#8) &&&
          (pack64 ((bytesToBv8 keyBytes).getD 17 0#8) ((bytesToBv8 keyBytes).getD 18 0#8)
              ((bytesToBv8 keyBytes).getD 19 0#8) ((bytesToBv8 keyBytes).getD 20 0#8)
              ((bytesToBv8 keyBytes).getD 21 0#8) ((bytesToBv8 keyBytes).getD 22 0#8)
              ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8) &&&
            pack64 ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8)
              ((bytesToBv8 keyBytes).getD 25 0#8) ((bytesToBv8 keyBytes).getD 26 0#8)
              ((bytesToBv8 keyBytes).getD 27 0#8) ((bytesToBv8 keyBytes).getD 28 0#8)
              ((bytesToBv8 keyBytes).getD 29 0#8) ((bytesToBv8 keyBytes).getD 30 0#8))) +
        1#64 == 0#64) =
      ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) := by
  rw [bv64_add1_eq_zero_iff]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff,
    pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff,
    list32_drop1_take30_eq_replicate_iff keyBytes h]
  simp only [bytesToBv8_getD, uint8_toBitVec_eq_ff_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
            ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨_, _, h25, h26, h27, h28, h29, h30⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
           h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
            h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
    exact ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
           ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨h23, h24, h25, h26, h27, h28, h29, h30⟩⟩

private theorem ecPubKeyIsCanonical_tail_eq (P : Primitives) (keyBytes : Bytes)
    (edPt : VerifiedLibraries.Common.EdPoint)
    (h : keyBytes.length = 32)
    (hmont : P.montToEd keyBytes 0 = some edPt)
    (htors : P.isTorsionFree edPt = true)
    (hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true)
    (hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true) :
    (if isCanonicalRef P keyBytes = true then (1#8 : BitVec 8) else 0#8) =
      BitVec.setWidth 8
        (if
          (if (BitVec.truncate 32
              (BitVec.signExtend 64 ((bytesToBv8 keyBytes).getD 31 0#8)) == 127#32) = true then
            (pack64 ((bytesToBv8 keyBytes).getD 1 0#8) ((bytesToBv8 keyBytes).getD 2 0#8)
                      ((bytesToBv8 keyBytes).getD 3 0#8) ((bytesToBv8 keyBytes).getD 4 0#8)
                      ((bytesToBv8 keyBytes).getD 5 0#8) ((bytesToBv8 keyBytes).getD 6 0#8)
                      ((bytesToBv8 keyBytes).getD 7 0#8) ((bytesToBv8 keyBytes).getD 8 0#8) &&&
                    pack64 ((bytesToBv8 keyBytes).getD 9 0#8) ((bytesToBv8 keyBytes).getD 10 0#8)
                      ((bytesToBv8 keyBytes).getD 11 0#8) ((bytesToBv8 keyBytes).getD 12 0#8)
                      ((bytesToBv8 keyBytes).getD 13 0#8) ((bytesToBv8 keyBytes).getD 14 0#8)
                      ((bytesToBv8 keyBytes).getD 15 0#8) ((bytesToBv8 keyBytes).getD 16 0#8) &&&
                  (pack64 ((bytesToBv8 keyBytes).getD 17 0#8) ((bytesToBv8 keyBytes).getD 18 0#8)
                      ((bytesToBv8 keyBytes).getD 19 0#8) ((bytesToBv8 keyBytes).getD 20 0#8)
                      ((bytesToBv8 keyBytes).getD 21 0#8) ((bytesToBv8 keyBytes).getD 22 0#8)
                      ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8) &&&
                    pack64 ((bytesToBv8 keyBytes).getD 23 0#8) ((bytesToBv8 keyBytes).getD 24 0#8)
                      ((bytesToBv8 keyBytes).getD 25 0#8) ((bytesToBv8 keyBytes).getD 26 0#8)
                      ((bytesToBv8 keyBytes).getD 27 0#8) ((bytesToBv8 keyBytes).getD 28 0#8)
                      ((bytesToBv8 keyBytes).getD 29 0#8) ((bytesToBv8 keyBytes).getD 30 0#8))) +
                1#64 ==
              0#64
          else false) =
            true then
          (0#64 : BitVec 64)
        else 1#64) := by
  have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr h
  rw [pack64_4_allOnes_eq_drop1_take30 keyBytes h, bytesToBv8_getD keyBytes 31,
    uint8_b31_7f_eq (keyBytes.getD 31 0) hb31_u8]
  simp only [isCanonicalRef, scalarIsInRange, hlen_beq, hb31_u8, hb0_u8, hmont, htors]
  cases ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) <;>
    cases ((keyBytes.getD 31 0 &&& 0x7F) == 0x7F) <;> rfl

@[simp, wp_norm, arm64_norm]
private theorem State_ite_setPState_setPC (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) :
    @_root_.ite State c inst ((s.setPState ps1).setPC pc) ((s.setPState ps2).setPC pc) =
      (s.setPState (@_root_.ite PState c inst ps1 ps2)).setPC pc := by
  by_cases hc : c <;> simp [hc]

@[simp, wp_norm, arm64_norm]
private theorem State_ite_setPState_setPC_setMem (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) (m : Memory) :
    @_root_.ite State c inst (((s.setPState ps1).setPC pc).setMem m)
      (((s.setPState ps2).setPC pc).setMem m) =
      ((s.setPState (@_root_.ite PState c inst ps1 ps2)).setPC pc).setMem m := by
  by_cases hc : c <;> simp [hc]

@[simp, wp_norm, arm64_norm]
private theorem ConditionHolds_ite (cond : CondCode) (c : Prop) [inst : Decidable c]
    (ps1 ps2 : PState) :
    ConditionHolds cond (@_root_.ite PState c inst ps1 ps2) =
      @_root_.ite Bool c inst (ConditionHolds cond ps1) (ConditionHolds cond ps2) := by
  by_cases hc : c <;> simp [hc]

/-! ## Contract-Backed `extHookStack` Variants -/

abbrev pqxdhHookStackExt : Nat := extHookStack
abbrev pqxdhEntryStackExt : Nat := 32768
abbrev verifySigHookStackExt : Nat := extHookStack + 48
abbrev verifySigStackExt : Nat := extHookStack + 1328

@[expose] def ecPubKeyIsCanonicalCallSpecExt (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s.sp (pqxdhHookStackExt + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
    stackAt s0.sp (pqxdhHookStackExt + 400)

theorem stackAt_ecPubKeyIsCanonical_call_ext (sp : BitVec 64) :
    stackAt sp (pqxdhHookStackExt + 400) =
      stackAt (sp - 400#64) pqxdhHookStackExt ∗
      cells (sp - 400#64) 4 ∗
      memRegion (sp - 368#64) 8 ∗
      memRegion (sp - 360#64) 168 ∗
      memRegion (sp - 192#64) 160 ∗
      cells (sp - 32#64) 4 := by
  rw [show (pqxdhHookStackExt + 400 : Nat) = pqxdhHookStackExt + 8 * 50 by decide,
    stackAt_split_cells sp pqxdhHookStackExt 50 (by decide),
    ← memRegion_cells (sp - 400#64) 50 (by decide)]
  change stackAt (sp - 400#64) pqxdhHookStackExt ∗ memRegion (sp - 400#64) 400 = _
  rw [memRegion_split (sp - 400#64) 32 368 (by decide),
    memRegion_cells (sp - 400#64) 4 (by decide),
    memRegion_split (sp - 400#64 + 32#64) 8 360 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64) 168 192 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64 + 168#64) 160 32 (by decide),
    memRegion_cells (sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64) 4 (by decide)]
  have h1 : sp - 400#64 + 32#64 = sp - 368#64 := by bv_arith
  have h2 : sp - 400#64 + 32#64 + 8#64 = sp - 360#64 := by bv_arith
  have h3 : sp - 400#64 + 32#64 + 8#64 + 168#64 = sp - 192#64 := by bv_arith
  have h4 : sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64 = sp - 32#64 := by bv_arith
  rw [h4, h3, h2, h1]

end CryptoVerification.E2E.Pqxdh.Shared

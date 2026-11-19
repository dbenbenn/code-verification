/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.DecodeHex32 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# `.keepsFs` Contract for `uuid::parser::decode_hex32`

Lifts `decodeHex32_ok` to `decodeHex32Spec.keepsFs` on `libsignalSessionCode` for arbitrary image
base and hook table.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops.UuidFs

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_local (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

structure DecodeLoopInvFs (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) (i : Nat) : Prop where
  inv : DecodeLoopInv entry s0 s out src sp' acc i
  hfs : s.fs = s0.fs

structure DecodeLoopPostFs (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) : Prop where
  post : DecodeLoopPost entry s0 s out src sp' acc
  hfs : s.fs = s0.fs

end CryptoVerification.SignalSession.Cli.MainHops.UuidFs

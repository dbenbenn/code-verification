/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Bridge -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Leaf
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterface -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvOk
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarint
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Compose
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Entry
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Key
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Top-Level CLI Inlined `SessionStructure::decode`

Assembles the verified entry, loop-head, key, varint, bytes, sender-chain (tag 6), and
receiver-chain (tag 7) contracts into the unconditional `OverPrevDecodeStmt` (`+0x1ee8 → +0x2620`)
for `message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)

section HeadExt

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem top_rest_len_ofNat64_ne_zero {rest enc : List (BitVec 8)}
    (hne : rest ≠ []) (hsuf : rest <:+ enc) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 rest.length ≠ 0#64 := by
  have hpos : 0 < rest.length := List.length_pos_iff.mpr hne
  rcases hsuf with ⟨t, ht⟩
  have hle : rest.length ≤ enc.length := by rw [← ht, List.length_append]; omega
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64)] at hnat
  omega

private def top_headFrameRestExt (A : RustAlloc) (g : OverDecG) (v : SSGQ) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool

private theorem top_overDecHeapExt_eq_head_split (A : RustAlloc) (g : OverDecG)
    (rest : List (BitVec 8)) (v : SSGQ) :
    overDecHeapExt A g rest v =
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest) ∗
      top_headFrameRestExt A g v := by
  unfold overDecHeapExt top_headFrameRestExt
  ac_rfl

end HeadExt

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

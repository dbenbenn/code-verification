/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Init.Data.BitVec.Basic

/-!
# Position-Independent 32-Bit Instruction Word Tables for `aes_256_cbc_decrypt` (`900` Instructions)

Pure `List (BitVec 32)` word slices between relocated instructions in
`signal_crypto::aes_cbc::aes_256_cbc_decrypt`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords

/-! ## 1. Prologue, Key-Schedule, SROA & Allocator Dispatch Words -/

@[expose] def cbcPrologueWords : List (BitVec 32) := [
    0xa9ba7bfd#32, 0xa9016ffc#32, 0xa90267fa#32, 0xa9035ff8#32, 0xa90457f6#32, 0xa9054ff4#32, 0x910003fd#32, 0xd13c83ff#32,
    0xf90003ff#32, 0xf9001be0#32, 0xb4000281#32, 0x92400c29#32, 0xb5000249#32, 0xf100807f#32, 0x540030e1#32, 0xf90013e8#32]
@[expose] def cbcPostStorageAdrpWords : List (BitVec 32) := [0xaa0103f9#32]
@[expose] def cbcStorageCheckWords : List (BitVec 32) := [
    0xaa0503f5#32, 0xaa0403f4#32, 0x9112c3f8#32, 0x7100051f#32, 0x54000240#32, 0x7103fd1f#32, 0x54000180#32, 0x912d03e8#32,
    0xaa0203e0#32]
@[expose] def cbcPostSoftKsWords : List (BitVec 32) := [0x14000033#32, 0x52800669#32]
@[expose] def cbcFastRejectWords : List (BitVec 32) := [0xa900a50a#32, 0x92800009#32, 0xf9000109#32, 0x14000173#32, 0xaa0203f6#32]
@[expose] def cbcPostInitWords : List (BitVec 32) := [0xaa1603e2#32, 0x3607fe40#32, 0x912943e0#32, 0xaa0203e1#32]
@[expose] def cbcPreInvExpandWords : List (BitVec 32) := [0x9121c3e8#32, 0x912943e1#32, 0x9103c100#32]
@[expose] def cbcHwCopyEkWords : List (BitVec 32) := [
    0x3dc19700#32, 0x3dc19b01#32, 0x912d03e0#32, 0x3dc19f02#32, 0x3dc17b03#32, 0x9121c3e1#32, 0x3d811f00#32, 0x3dc1a300#32,
    0x52803c02#32, 0x3d812301#32, 0x3dc18701#32, 0x3d812b00#32, 0x3dc18b00#32, 0x3d810f01#32, 0x3dc18f01#32, 0x3d811300#32,
    0x3dc19300#32, 0x3d811701#32, 0x3dc18301#32, 0x3d811b00#32, 0x3dc17f00#32, 0x3d810b01#32, 0x3dc16f01#32, 0x3d810700#32,
    0x3dc16b00#32, 0x3d812702#32, 0x3dc17702#32, 0xad1e0700#32, 0x3dc17300#32, 0xad1f8f02#32, 0x3d80fb00#32]
@[expose] def cbcSroaCopy960Words : List (BitVec 32) := [0x9112c3e0#32, 0x912d03e1#32, 0x52807802#32, 0x9112c3f7#32, 0x912d03f6#32]
@[expose] def cbcSroaCopy952Words : List (BitVec 32) := [0xf10042bf#32, 0x54002501#32, 0xf9425bf5#32, 0x912d03e0#32, 0xb27d02e1#32, 0x52807702#32]
@[expose] def cbcSroaStage968Words : List (BitVec 32) := [0x3dc00280#32, 0x910ee2c8#32, 0x9103a3e0#32, 0x912d03e1#32, 0x52807902#32, 0x3d800100#32]
@[expose] def cbcPreAllocWords : List (BitVec 32) := [0xaa1903e0#32, 0x52800021#32]
@[expose] def cbcPostAllocWords : List (BitVec 32) := [
    0xf90017e0#32, 0xb40062a0#32, 0x912d03f6#32, 0x9103a3e1#32, 0x52807902#32, 0xb27d02c0#32, 0xf905a3f5#32]
@[expose] def cbcLoopDispatchWords : List (BitVec 32) := [0xd344ff29#32, 0x7100051f#32, 0xa90167e9#32, 0x54002561#32]

/-! ## 2. `STORAGE == 1` Hardware Loop Words (`266` Instructions Total with 5 `BL`s) -/

@[expose] def hwSetupWords : List (BitVec 32) := [
    0xb204cfe8#32, 0xf29e1e28#32, 0x9bc87f28#32, 0xd348fd15#32, 0x8b1512a8#32, 0xeb080134#32,
    0xf90073e8#32, 0x540060a3#32, 0xf104433f#32, 0x912d03f3#32, 0x540014a3#32]
@[expose] def hwPar17InitWords : List (BitVec 32) := [
    0x9121c3f7#32, 0xaa1f03fc#32, 0x5280221a#32, 0x91001ef9#32, 0x9112c3fb#32]
@[expose] def hwPar17PreMc1Words : List (BitVec 32) := [
    0xf9401be8#32, 0x9b1a2396#32, 0x9121c3e0#32, 0x52802202#32, 0xaa1603e1#32]
@[expose] def hwPar17PreMc2Words : List (BitVec 32) := [
    0x9112c3e0#32, 0xaa1603e1#32, 0x52802202#32]
@[expose] def hwPar17PreDecWords : List (BitVec 32) := [
    0x9103c260#32, 0x9112c3e1#32, 0x9112c3e2#32]
@[expose] def hwPar17Xor0AWords : List (BitVec 32) := [
    0x397c03e9#32, 0x3952c3ea#32, 0xaa1f03e8#32, 0x397c07eb#32, 0x3952c7ec#32, 0x397c0bed#32, 0x3952cbee#32, 0x4a090149#32,
    0x3952f3ef#32, 0x4a0b018a#32, 0x3912c3e9#32, 0x397c0fe9#32, 0x3912c7ea#32, 0x4a0d01cb#32, 0x3952cfea#32, 0x3912cbeb#32,
    0x3952d3eb#32, 0x397c2fec#32, 0x4a090149#32, 0x397c13ea#32, 0x3952efed#32, 0x3912cfe9#32, 0x397c33ee#32, 0x397c37f0#32,
    0x4a0a0169#32, 0x397c17ea#32, 0x3952d7eb#32, 0x3912d3e9#32, 0x3952f7f1#32, 0x4a0a0169#32, 0x397c1bea#32, 0x3952dbeb#32]
@[expose] def hwPar17Xor0BWords : List (BitVec 32) := [
    0x3912d7e9#32, 0x4a0a0169#32, 0x397c1fea#32, 0x3952dfeb#32, 0x3912dbe9#32, 0x4a0a0169#32, 0x397c23ea#32, 0x3952e3eb#32,
    0x3912dfe9#32, 0x4a0a0169#32, 0x397c27ea#32, 0x3952e7eb#32, 0x3912e3e9#32, 0x4a0a0169#32, 0x397c2bea#32, 0x3952ebeb#32,
    0x3912e7e9#32, 0x4a0e01e9#32, 0x4a0a016a#32, 0x4a0c01ab#32, 0x3912f3e9#32, 0x3912ebea#32, 0x397c3bea#32, 0x397c3fe9#32,
    0x3912efeb#32, 0x3952fbeb#32, 0x3952ffed#32, 0x4a10022c#32, 0x4a0a016a#32, 0x4a0901a9#32, 0x3912f7ec#32, 0x3912fbea#32,
    0x3912ffe9#32]
@[expose] def hwPar17XorLoopAWords : List (BitVec 32) := [
    0x8b080369#32, 0x38686aeb#32, 0x8b08032a#32, 0x3940412c#32, 0x385fa14d#32, 0x3940452e#32, 0x385fb14f#32, 0x39404930#32,
    0x91004108#32, 0x4a0b018b#32, 0x385fc14c#32, 0x4a0d01cd#32, 0x3900412b#32, 0x39404d2b#32, 0x4a0f020e#32, 0x3900452d#32,
    0x3940512d#32, 0x39406d2f#32, 0x4a0c016b#32, 0x385fd14c#32, 0x3900492e#32, 0x39004d2b#32, 0x3940114e#32, 0xf104011f#32,
    0x4a0c01ab#32, 0x385fe14c#32, 0x3940552d#32, 0x3900512b#32, 0x39401550#32, 0x39407131#32, 0x4a0c01ab#32, 0x385ff14c#32,
    0x3940592d#32, 0x3900552b#32]
@[expose] def hwPar17XorLoopBWords : List (BitVec 32) := [
    0x39401952#32, 0x39407520#32, 0x4a0c01ab#32, 0x3940014c#32, 0x39405d2d#32, 0x3900592b#32, 0x4a0c01ab#32, 0x3940054c#32,
    0x3940612d#32, 0x39005d2b#32, 0x4a0c01ab#32, 0x3940094c#32, 0x3940652d#32, 0x3900612b#32, 0x4a0c01ab#32, 0x39400d4c#32,
    0x3940692d#32, 0x3900652b#32, 0x4a10022b#32, 0x4a0c01ac#32, 0x4a0e01ed#32, 0x3900712b#32, 0x3900692c#32, 0x39401d4c#32,
    0x3940214a#32, 0x39006d2d#32, 0x3940792d#32, 0x39407d2b#32, 0x4a12000e#32, 0x4a0c01ac#32, 0x4a0a016a#32, 0x3900752e#32,
    0x3900792c#32, 0x39007d2a#32, 0x54fff781#32]
@[expose] def hwPar17PostMcWords : List (BitVec 32) := [
    0xf94017e8#32, 0x9b1a2380#32, 0x9112c3e1#32, 0x52802202#32, 0x9100079c#32]
@[expose] def hwPar17TailWords : List (BitVec 32) := [
    0x3dc042c0#32, 0xeb1c02bf#32, 0x912d03f3#32, 0x3d80f260#32, 0x54ffec41#32]
@[expose] def hwRemSetupWords : List (BitVec 32) := [
    0xf100429f#32, 0x54004948#32, 0xa9415ffa#32, 0x912d03f9#32, 0xf94073e8#32, 0xeb08035f#32,
    0x540043c0#32, 0xa942abe9#32, 0xd37ced08#32, 0x92800016#32, 0x8b080153#32, 0x8b080135#32]
@[expose] def hwRemPreDecWords : List (BitVec 32) := [
    0xb4004976#32, 0x3dc00260#32, 0x9103c320#32, 0x912943e1#32, 0x912943e2#32, 0x3d816b00#32]
@[expose] def hwRemPostAWords : List (BitVec 32) := [
    0x397c03e8#32, 0x396943e9#32, 0xd1000694#32, 0x397c07ea#32, 0x396947eb#32, 0xd10006d6#32, 0x397c0bec#32, 0x39694bed#32,
    0x4a080128#32, 0x4a0a0169#32, 0x392943e8#32, 0x397c0fe8#32, 0x392947e9#32, 0x39694fe9#32, 0x4a0c01aa#32, 0x39294bea#32,
    0x396953ea#32, 0x397c2feb#32, 0x4a080128#32, 0x397c13e9#32, 0x39696fec#32, 0x39294fe8#32, 0x397c33ed#32, 0x396973ee#32,
    0x4a090148#32, 0x397c17e9#32, 0x396957ea#32, 0x392953e8#32, 0x397c37ef#32, 0x396977f0#32, 0x4a090148#32, 0x397c1be9#32,
    0x39695bea#32, 0x392957e8#32]
@[expose] def hwRemPostBWords : List (BitVec 32) := [
    0x3cc10661#32, 0x4a090148#32, 0x397c1fe9#32, 0x39695fea#32, 0x39295be8#32, 0x4a090148#32, 0x397c23e9#32, 0x396963ea#32,
    0x39295fe8#32, 0x4a090148#32, 0x397c27e9#32, 0x396967ea#32, 0x392963e8#32, 0x4a090148#32, 0x397c2be9#32, 0x39696bea#32,
    0x392967e8#32, 0x4a0d01c8#32, 0x4a090149#32, 0x4a0b018a#32, 0x392973e8#32, 0x39296be9#32, 0x397c3be9#32, 0x397c3fe8#32,
    0x39296fea#32, 0x39697bea#32, 0x39697fec#32, 0x4a0f020b#32, 0x3d80f321#32, 0x4a090149#32, 0x4a080188#32, 0x392977eb#32,
    0x39297be9#32, 0x39297fe8#32, 0x3dc16b00#32, 0x3c8106a0#32, 0xb5fff674#32]
@[expose] def hwRemExitWords : List (BitVec 32) := [0x140001ca#32]

/-! ## 3. `Fixslice64` Quad/Tail Loops, PKCS#7 Unpad, Epilogue & Cold Panic Words -/

@[expose] def cbcBadKeyIvWords : List (BitVec 32) := [
    0x7100051f#32, 0x54000181#32, 0xf94013e8#32, 0xaa1f03ea#32, 0x9112c3e9#32, 0xf905a3e9#32, 0xaa0a03eb#32, 0x9100054a#32,
    0xf107815f#32, 0x382b693f#32, 0x54ffff81#32, 0x912d03e9#32, 0x14000009#32, 0x9112c3eb#32, 0xf94013e8#32, 0x52807809#32,
    0xaa0b03ea#32, 0xf800855f#32, 0xf1002129#32, 0xaa0a03eb#32, 0x54ffffa1#32, 0x92800009#32, 0xa9007d09#32]
@[expose] def cbcRetEpilogueWords : List (BitVec 32) := [
    0x913c83ff#32, 0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa94267fa#32, 0xa9416ffc#32, 0xa8c67bfd#32, 0xd65f03c0#32]
@[expose] def cbcSoftQuadSetupWords : List (BitVec 32) := [0xd346ff3b#32, 0xd3441728#32, 0xf90007e8#32, 0xb40029db#32, 0xa942a3f4#32, 0x9100611a#32]
@[expose] def cbcSoftQuadPre1Words : List (BitVec 32) := [
    0x3cdf8340#32, 0x3cc08341#32, 0x9112c3e8#32, 0x3cc18342#32, 0x385ee349#32, 0x912d03e0#32, 0xad008500#32, 0x39402b4a#32,
    0x9121c3e1#32, 0x3c830102#32, 0x385ef348#32, 0x3cde8340#32, 0xad408b01#32, 0x385e8359#32, 0x2907a7e8#32, 0x385f0349#32,
    0x385f1348#32, 0x3d80f300#32, 0x3dc00f00#32, 0x385e9353#32, 0x2908a3e9#32, 0x385f2349#32, 0x385f3348#32, 0x385ea356#32,
    0x385eb357#32, 0x385ec355#32, 0x2909a7e8#32, 0x385f4349#32, 0x385f5348#32, 0x385ed35c#32, 0xad1e8b01#32, 0x290aa3e9#32,
    0x385f6349#32, 0x385f7348#32, 0x3d80ff00#32, 0x290ba7e8#32, 0x385f8349#32, 0x385f9348#32, 0x290ca3e9#32, 0x385fa349#32,
    0x385fb348#32, 0x290da7e8#32]
@[expose] def cbcSoftQuadPre2Words : List (BitVec 32) := [
    0x385fc349#32, 0x385fd348#32, 0x290ea3e9#32, 0x385fe349#32, 0x385ff348#32, 0x290fa7e8#32, 0x39400349#32, 0x39400748#32,
    0x2910a3e9#32, 0x39400b49#32, 0x39400f48#32, 0x2911a7e8#32, 0x39401349#32, 0x39401748#32, 0x2912a3e9#32, 0x39401b49#32,
    0x39401f48#32, 0x291427e8#32, 0x39402348#32, 0x39402749#32, 0xb9009fe8#32, 0x39402f48#32, 0x291523e9#32, 0x39403348#32,
    0x39403749#32, 0x291623ea#32, 0x39403f48#32, 0x39403b4a#32, 0x291723e9#32, 0x39404348#32, 0x39404749#32, 0x291823ea#32,
    0x39404f48#32, 0x39404b4a#32, 0x291923e9#32, 0x39405348#32, 0x39405749#32, 0x291a23ea#32, 0x39405b48#32, 0xb900e3e8#32,
    0x39405f48#32, 0x291b23e9#32, 0x9112c3e8#32]
@[expose] def cbcSoftQuadPost1aWords : List (BitVec 32) := [
    0xad400700#32, 0xf100077b#32, 0x397c07e8#32, 0x397c0bea#32, 0x397c3fed#32, 0xad1e0700#32, 0xad410b00#32, 0xad1f0b00#32,
    0x3961c7e9#32, 0x3961cbeb#32, 0x3961f3ec#32, 0x3961ffee#32, 0x4a080128#32, 0x4a0a0169#32, 0x3961cfea#32, 0x3921c7e8#32,
    0x397c0fe8#32, 0x3961efeb#32, 0x3921cbe9#32, 0x397c13e9#32, 0x4a080148#32, 0x3961d3ea#32, 0x3921cfe8#32, 0x4a090148#32,
    0x397c17e9#32, 0x3961d7ea#32, 0x3921d3e8#32, 0x4a090148#32, 0x397c1be9#32, 0x3961dbea#32, 0x3921d7e8#32, 0x4a090148#32,
    0x397c1fe9#32, 0x3961dfea#32]
@[expose] def cbcSoftQuadPost1bWords : List (BitVec 32) := [
    0x3921dbe8#32, 0x4a090148#32, 0x397c23e9#32, 0x3961e3ea#32, 0x3921dfe8#32, 0x4a090148#32, 0x397c27e9#32, 0x3961e7ea#32,
    0x3921e3e8#32, 0x4a090148#32, 0x397c2be9#32, 0x3961ebea#32, 0x3921e7e8#32, 0x397c2fe8#32, 0x4a090149#32, 0x397c33ea#32,
    0x4a080168#32, 0x3921ebe9#32, 0x397c37e9#32, 0x3921efe8#32, 0x4a0a0188#32, 0x3961f7ea#32, 0x397c3beb#32, 0x3961fbec#32,
    0x3921f3e8#32, 0x4a090149#32, 0x396203e8#32, 0x4a0b018a#32, 0x4a0d01cb#32, 0x3921f7e9#32, 0x396207e9#32, 0x3921ffeb#32,
    0x39620feb#32, 0x4a190108#32, 0x3921fbea#32]
@[expose] def cbcSoftQuadPost2Words : List (BitVec 32) := [
    0x39620bea#32, 0x4a130129#32, 0x4a17016b#32, 0x392203e8#32, 0x392207e9#32, 0x396217e9#32, 0x396213e8#32, 0x2947b7ec#32,
    0x39220feb#32, 0x39621feb#32, 0x4a1c0129#32, 0x4a150108#32, 0x392217e9#32, 0x4a16014a#32, 0x4a0c016b#32, 0x392213e8#32,
    0x396223e8#32, 0x2948b3e9#32, 0x39220bea#32, 0x39621bea#32, 0x912d03f6#32, 0x39221feb#32, 0x39622feb#32, 0x4a090108#32,
    0x396227e9#32, 0x4a0d014a#32, 0x392223e8#32, 0x396233e8#32, 0x4a0c0129#32, 0x39221bea#32, 0x39622bea#32, 0x2949b7ec#32,
    0x392227e9#32, 0x4a0c016b#32, 0x4a0d014a#32, 0x294ab3e9#32, 0x39222feb#32, 0x39623feb#32, 0x39222bea#32, 0x39623bea#32,
    0x4a090108#32, 0x396237e9#32, 0x392233e8#32, 0x396243e8#32, 0x4a0c0129#32, 0x294bb7ec#32, 0x392237e9#32, 0x4a0c016b#32,
    0x4a0d014a#32, 0x294cb3e9#32, 0x39223feb#32, 0x39624feb#32, 0x39223bea#32]
@[expose] def cbcSoftQuadPost3Words : List (BitVec 32) := [
    0x39624bea#32, 0x4a090108#32, 0x396247e9#32, 0x392243e8#32, 0x396253e8#32, 0x4a0c0129#32, 0x294db7ec#32, 0x392247e9#32,
    0x4a0c016b#32, 0x4a0d014a#32, 0x294eb3e9#32, 0x39224feb#32, 0x39625feb#32, 0x39224bea#32, 0x39625bea#32, 0x4a090108#32,
    0x396257e9#32, 0x392253e8#32, 0x396263e8#32, 0x4a0c0129#32, 0x294fb7ec#32, 0x392257e9#32, 0x4a0c016b#32, 0x4a0d014a#32,
    0x2950b3e9#32, 0x39225feb#32, 0x39626feb#32, 0x39225bea#32, 0x39626bea#32, 0x4a090108#32, 0x396267e9#32, 0x392263e8#32,
    0x396273e8#32, 0x4a0c0129#32, 0x2951b7ec#32, 0x392267e9#32, 0x4a0c016b#32, 0x4a0d014a#32, 0x2952b3e9#32, 0x39226feb#32,
    0x39627feb#32, 0x39226bea#32, 0x39627bea#32, 0x4a090108#32, 0x396277e9#32, 0x392273e8#32, 0x396283e8#32, 0x4a0c0129#32,
    0x295437ec#32, 0x392277e9#32, 0xb9409fe9#32, 0x4a0c016b#32, 0x4a090108#32, 0x396287e9#32, 0xb940abec#32, 0x4a0d014a#32,
    0x39227feb#32, 0x39628feb#32, 0x392283e8#32, 0x396293e8#32, 0x4a0c0129#32, 0x39227bea#32]
@[expose] def cbcSoftQuadPost4Words : List (BitVec 32) := [
    0x39628bea#32, 0x2955b7ec#32, 0x392287e9#32, 0x4a0c016b#32, 0x4a0d014a#32, 0x2956b3e9#32, 0x39228feb#32, 0x39629feb#32,
    0x39228bea#32, 0x39629bea#32, 0x4a090108#32, 0x396297e9#32, 0x392293e8#32, 0x3962a3e8#32, 0x4a0c0129#32, 0x2957b7ec#32,
    0x392297e9#32, 0x4a0c016b#32, 0x4a0d014a#32, 0x2958b3e9#32, 0x39229feb#32, 0x3962afeb#32, 0x39229bea#32, 0x3962abea#32,
    0x4a090108#32, 0x3962a7e9#32, 0x3922a3e8#32, 0x3962b3e8#32, 0x4a0c0129#32, 0x2959b7ec#32, 0x3922a7e9#32, 0x4a0c016b#32,
    0x4a0d014a#32, 0x295ab3e9#32, 0x3922abea#32, 0x3962bbea#32, 0x3922afeb#32, 0x3962bfeb#32, 0x4a090108#32, 0x3962b7e9#32,
    0x3922b3e8#32, 0xb940e3e8#32, 0x4a0c0129#32, 0x4a080148#32, 0xb940dfea#32, 0x3922b7e9#32, 0x397c03e9#32, 0x3922bbe8#32,
    0x3961c3e8#32, 0x4a0a016a#32, 0x3922bfea#32, 0x4a090108#32]
@[expose] def cbcSoftQuadPost5Words : List (BitVec 32) := [
    0xad5f0301#32, 0x3921c3e8#32, 0xad010281#32, 0xad5e0302#32, 0x3cc18341#32, 0x9101035a#32, 0xac820282#32, 0x3d80f2c1#32,
    0x54ffd6c1#32]
@[expose] def cbcSoftTailSetupWords : List (BitVec 32) := [
    0xa9415ffa#32, 0xf94007f9#32, 0xb4000ad9#32, 0xa942abe9#32, 0x927ae6e8#32, 0xb2400908#32, 0x9121c3f3#32, 0x8b080154#32,
    0x8b080135#32]
@[expose] def cbcSoftTailPreWords : List (BitVec 32) := [
    0x6f00e401#32, 0x3cdf9280#32, 0x9112c3e8#32, 0x912d03e0#32, 0x9121c3e1#32, 0x3d80f300#32, 0xad010661#32, 0x3c810261#32]
@[expose] def cbcSoftTailPost1Words : List (BitVec 32) := [
    0x3952c3e8#32, 0x397c03f2#32, 0xf1000739#32, 0x3952c7e9#32, 0x397c07e0#32, 0x3952d3ec#32, 0x4a080248#32, 0x397c13f2#32,
    0x3952cbea#32, 0x3952dbee#32, 0x4a090009#32, 0x397c0be1#32, 0x381f92a8#32, 0x4a0c024c#32, 0x397c1be8#32, 0x3952d7ed#32,
    0x4a0a002a#32, 0x3952dfef#32, 0x3952e3f0#32, 0x4a0e0108#32, 0x397c17e3#32, 0x397c1ff2#32, 0x381fa2a9#32, 0x397c23e9#32,
    0x4a0d006d#32, 0x3952cfeb#32, 0x397c0fe2#32, 0x4a100129#32, 0x381fb2aa#32, 0x4a0f024a#32, 0x381fd2ac#32, 0x4a0b004b#32,
    0x3952ebec#32, 0x3952efee#32, 0x381ff2a8#32]
@[expose] def cbcSoftTailPost2Words : List (BitVec 32) := [
    0x397c2be8#32, 0x397c2ff0#32, 0x3952e7f1#32, 0x397c27e0#32, 0x4a0c0108#32, 0x381fe2ad#32, 0x3952f3ed#32, 0x390002aa#32,
    0x397c33ea#32, 0x3952f7ef#32, 0x390006a9#32, 0x4a0e0209#32, 0x397c3bec#32, 0x4a0d014a#32, 0x381fc2ab#32, 0x4a11000b#32,
    0x397c37f1#32, 0x39000ea8#32, 0x3952fbe8#32, 0x390012a9#32, 0x3952ffe9#32, 0x397c3fed#32, 0x4a080188#32, 0x39000aab#32,
    0x4a0f022b#32, 0x4a0901a9#32, 0x3cdf9280#32, 0x91004294#32, 0x390016aa#32, 0x39001aab#32, 0x39001ea8#32, 0x390022a9#32,
    0x910042b5#32, 0x3d80f2c0#32, 0x54fff641#32]
@[expose] def cbcUnpadWords : List (BitVec 32) := [
    0xf94017e9#32, 0xd1000748#32, 0x8b081129#32, 0x39403d2a#32, 0x5100454b#32, 0x3100417f#32, 0x54000143#32, 0x5280020b#32,
    0xcb0a016b#32, 0xaa0b03ec#32, 0xf1003d9f#32, 0x54000260#32, 0x386c692d#32, 0x9100058c#32, 0x6b0a01bf#32, 0x54ffff60#32,
    0x912d03e0#32]
@[expose] def cbcErrDeallocArgsWords : List (BitVec 32) := [0xf94017e0#32, 0xaa1703e1#32, 0x52800022#32]
@[expose] def cbcErrRetPreWords : List (BitVec 32) := [0xf94013ea#32, 0x52800228#32]
@[expose] def cbcErrRetPostWords : List (BitVec 32) := [0xa900a149#32, 0x92800008#32, 0xf9000148#32, 0x17fffe32#32]
@[expose] def cbcOkPreDropWords : List (BitVec 32) := [0x8b081175#32, 0xeb1702bf#32, 0x540001a8#32, 0x912d03e0#32]
@[expose] def cbcOkRetWords : List (BitVec 32) := [0xa94227e8#32, 0xa9002517#32, 0xf9000915#32, 0x17fffe29#32]
@[expose] def cbcPanic1MidWords : List (BitVec 32) := [0x52800761#32]
@[expose] def cbcSlicePanicMidWords : List (BitVec 32) := [0xaa1f03e0#32, 0xaa1503e1#32, 0xaa1703e2#32]
@[expose] def cbcHandleErrPreWords : List (BitVec 32) := [0x52800020#32, 0xaa1903e1#32]

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords

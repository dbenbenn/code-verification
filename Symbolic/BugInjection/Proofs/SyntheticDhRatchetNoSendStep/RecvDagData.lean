/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagDefs

/-!
# Concrete 181-Node DAG Certificate for `DhRatchetNoSendStepCli` Call 2 (`RecvDagData.lean`)

Stores the depth-8 `BinTree` tables `opTree` and `bytesTree` for all prefix, state-proxy,
trial, and 1..64-byte send-coin subterms at Call 2 (`dhEv2`), and certifies `dagAllNodesOk`
and `dagPairwiseNoCollide` in the Lean kernel (`decide +kernel`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagData

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree btGet)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0 (dhAesPt0)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagDefs
  (DagOp dagShape checkAllDagNodes dagPairwiseOk)

abbrev dagDepth : Nat := 8
abbrev dagSize : Nat := 181
abbrev coinBaseId : Nat := 92

def coinNodeId (cl : Nat) : Nat := coinBaseId + (cl - 1)

abbrev emptyId : Nat := 0
abbrev b00Id : Nat := 1
abbrev b01Id : Nat := 2
abbrev b02Id : Nat := 3
abbrev b03Id : Nat := 4
abbrev b05Id : Nat := 5
abbrev u32_0Id : Nat := 6
abbrev u32_1Id : Nat := 7
abbrev ff32Id : Nat := 8
abbrev zero32Id : Nat := 9
abbrev wrLblId : Nat := 10
abbrev wmkLblId : Nat := 11
abbrev pqxdhLblId : Nat := 12
abbrev wmkInfo1Id : Nat := 13
abbrev wmkInfo2Id : Nat := 14
abbrev wmkInfo3Id : Nat := 15
abbrev wrInfo1Id : Nat := 16
abbrev wrInfo2Id : Nat := 17
abbrev pqxdhInfo1Id : Nat := 18
abbrev pqxdhInfo2Id : Nat := 19
abbrev pqxdhInfo3Id : Nat := 20
abbrev rt1Id : Nat := 21
abbrev rt2Id : Nat := 22
abbrev recvTail0Id : Nat := 23
abbrev ikAId : Nat := 24
abbrev ikBId : Nat := 25
abbrev spkBId : Nat := 26
abbrev pqskBId : Nat := 27
abbrev pk0Id : Nat := 28
abbrev pk1Id : Nat := 29
abbrev pk2Id : Nat := 30
abbrev ik0sId : Nat := 31
abbrev ik1sId : Nat := 32
abbrev aliceLitId : Nat := 33
abbrev bobLitId : Nat := 34
abbrev pqsecAId : Nat := 43
abbrev pqsecB1Id : Nat := 50
abbrev pqsecB2Id : Nat := 57
abbrev pqsecB3Id : Nat := 64
abbrev r22Id : Nat := 65
abbrev r23Id : Nat := 66
abbrev dhsAId : Nat := 67
abbrev ekId : Nat := 68
abbrev pk4Id : Nat := 69
abbrev pqpkId : Nat := 70
abbrev ctKemId : Nat := 71
abbrev ssKemId : Nat := 72
abbrev dh02Id : Nat := 73
abbrev dh13Id : Nat := 74
abbrev dh23Id : Nat := 75
abbrev c3Id : Nat := 76
abbrev c2Id : Nat := 77
abbrev c1Id : Nat := 78
abbrev ikmId : Nat := 79
abbrev prkPqId : Nat := 80
abbrev rkInitId : Nat := 81
abbrev pqi2CId : Nat := 82
abbrev ckInitId : Nat := 83
abbrev pqi3CId : Nat := 84
abbrev pqrInitId : Nat := 85
abbrev sidId : Nat := 86
abbrev dh24Id : Nat := 87
abbrev prkAId : Nat := 88
abbrev stA0RkId : Nat := 89
abbrev wri2CId : Nat := 90
abbrev stA0CksId : Nat := 91
abbrev pqKey0Id : Nat := 156
abbrev pqMsg0Id : Nat := 157
abbrev seed0Id : Nat := 158
abbrev nck0Id : Nat := 159
abbrev prk0Id : Nat := 160
abbrev ckey0Id : Nat := 161
abbrev wmki2_0Id : Nat := 162
abbrev mkey0Id : Nat := 163
abbrev wmki3_0Id : Nat := 164
abbrev iv0Id : Nat := 165
abbrev ct0Id : Nat := 166
abbrev wire0Id : Nat := 167
abbrev miR0Id : Nat := 168
abbrev mi0Id : Nat := 169
abbrev fmac0Id : Nat := 170
abbrev mac0Id : Nat := 171
abbrev wmac0Id : Nat := 172
abbrev zPrkId : Nat := 173
abbrev zCkeyId : Nat := 174
abbrev zWmki2Id : Nat := 175
abbrev zMkeyId : Nat := 176
abbrev zWmki3Id : Nat := 177
abbrev zIvId : Nat := 178
abbrev zFmacId : Nat := 179
abbrev zMacId : Nat := 180

def pqAddrBytes : HwBytes := leBytes 36 0x1f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a00

def opTree : BinTree DagOp :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([]))) (.leaf (.rand 32 37)))
                (.branch (.leaf (.concat 2 63)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 5 29)) (.leaf (.kdf 156 158)))
                (.branch (.leaf (.rand 32 5)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 10 2)) (.leaf (.rand 32 53)))
                (.branch (.leaf (.kdf 9 79)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 47)) (.leaf (.kdf 173 175)))
                (.branch (.leaf (.rand 32 21)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (.lit (leBytes 32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))
                  (.leaf (.rand 32 45)))
                (.branch (.leaf (.kemSS 70 66)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 39)) (.leaf (.concat 32 167)))
                (.branch (.leaf (.rand 32 13)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.rand 0 32)) (.leaf (.rand 32 61)))
                (.branch (.leaf (.kdf 81 87)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 55)) (.empty))
                (.branch (.leaf (.rand 32 29)) (.empty))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([0x03#8]))) (.leaf (.rand 32 41)))
                (.branch (.leaf (.dhPk 65)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 35)) (.leaf (.concat 163 15)))
                (.branch (.leaf (.rand 32 9)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 12 4)) (.leaf (.rand 32 57)))
                (.branch (.leaf (.concat 83 20)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 51)) (.leaf (.trunc8 179)))
                (.branch (.leaf (.rand 32 25)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (.lit (leBytes 46 0x343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857)))
                  (.leaf (.rand 32 49)))
                (.branch (.leaf (.concat 75 72)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 25)) (.leaf (.concat 167 171)))
                (.branch (.leaf (.rand 32 17)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (.dhPk 24))
                  (.leaf (.lit (leBytes 32 0xdca7c61aa7a987e18382419a29f1af5a7776e03585c50f7f88f11132219b39b5))))
                (.branch (.leaf (.rand 32 1)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 34 59)) (.empty))
                (.branch (.leaf (.rand 32 33)) (.empty)))))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([0x01#8]))) (.leaf (.rand 32 39)))
                (.branch (.leaf (.rand 23 32)) (.empty)))
              (.branch
                (.branch (.leaf (.lit ([0x62#8, 0x6f#8, 0x62#8]))) (.leaf (.concat 161 14)))
                (.branch (.leaf (.rand 32 7)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 12 2)) (.leaf (.rand 32 55)))
                (.branch (.leaf (.concat 81 19)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 49)) (.leaf (.kdf 173 177)))
                (.branch (.leaf (.rand 32 23)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit (leBytes 14 0x7465686374615272657073696857))) (.leaf (.rand 32 47)))
                (.branch (.leaf (.dh 68 25)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 41)) (.leaf (.kdf 163 169)))
                (.branch (.leaf (.rand 32 15)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.rand 10 32)) (.leaf (.rand 32 63)))
                (.branch (.leaf (.concat 89 17)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 27)) (.empty))
                (.branch (.leaf (.rand 32 31)) (.empty))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([0x00#8, 0x00#8, 0x00#8, 0x00#8]))) (.leaf (.rand 32 43)))
                (.branch
                  (.leaf (.lit (leBytes 1568 0x89f6a44a4192619751ad2bfbd97786f69f870782bc1437a1c5432910070899f9861bf6442bfc650aa3795797e2ae2460699a71a2d491830adf1bfc435559d0a393bdae80abce052688e0c0a6c59369137d6287b5c4c6a89e40905fcafa29b87755e722bb9454a7b8759136f0ba9ac38fca225ed0ea618a542e67c35e81a5b8776129d5867eaca617f82831c8509b6b48b5d013b90b2d4526ad80faa8b4c32c79c6ab01db989b7706bc215a6e4cc84ed2339dc481a861d83cb1beb82cf21bf7ba1cf422cd8b829089cc54b9a34028b04df24c90fbf6a96506c8d03925e55ab4f99397236f9f13462c5cf26bf8d90f7c6407062aaa082527cc4e2031758b92765d2a57551892968adfa5d113c72955a02c9333955072fcd8bb835e2e814d4161349cb6c92475de6b980874e796a339ff66058e32cbca8f390b76f3be9cb637c8622ac2a8ed8a18f5386c95133c3b9206bd64e5913464220f1410af120141c42907303f1e61287d43ee913ab868c38738a3b08c15ebc9141fba83f78f3a64451626adfc966c7af03b1bddbaa77d4a4cb252a06c8eba6e8734a2c0bcdaa2c2782d959e236a396b93e2ba14769485b3bd1bf623725870fc3f6a886933d0e43105f87478db30f31dce0af1541a764100ce5b292303e74766957a28e4bd4a45140844254387eeaac3402acc1fc2f58325a3f50ff1e173686511712e3db626631bbb1fbb58cb3929287cada9d4773d155344a15c4ed60990e5a9a326ff17952265ba293a88646d922998fb7baf8b868dd24f850118bffca0c889d56de0751538c665fac0688282bd6ae80051e59ed5a1b4da525994561f9632c0b02468db5ab480cf3fabfec860d0b4250316d723bc84b2693183bb53a3ca2ce378b79813c3588b2b74344660a1a6b9c5c3d27f77c03a41615c686c99b2e78070f841650624110b688318c561cc03ac65ba3a1419a60bb58b451997c50ea1b2ab32899d86a80b510632f64191316134c2ac46f8fe4fc61141baf92864942356a358f7002b27a96f92a14e59ffca5cb3bdb02ac9b9292ec6fb24c42922216bca5a8865d77bbc05f09486459929897b3bf3ac17070d697807e7915582289de265787ad287a2828329e21bda629ad15d7922879a68c88ccbb69a9107a5fcdb27119170540e469aae1f64149f08f86c14b666294941578b8a6674bdd5926b996d7410df6bea443c2a4c10ec161ca954009ac0b931626283a69834ae15542267744f4e85ecad5ad695f90f23a0016474f6561892125982c6021f7857c60ae534cb79e2941c80642aeb2fe257a69c6126326a5a58fa58d1157f2cf7a8a5d1cb98cc7e55c1637b33b917d8b7774b367cae5f54a645e260327adb5bc3155a00c555174b68005256b52263bb6a7dc2c5c7e29c3e91f346534f1e3387688520100ab94e333f06c7468707be0bc32d783579018ce60c03346052b86523b19becd6a0cba09f14381d235217045a448b637e501b48872f3c5625c3e644282b430b18198c130e1a22cec8e7a9c6133605649550532b33111e34ec8dbd550c8611b7c9816da026ac53e856772b789b80828a281641e7430986e12969e746159539ca0b68a53ab460952ef9423ad05e77a74e9cf52582d3b07837566be4fc8527e3b2414e41b84857148416e974962c7864db3116a3a52b21e5c7e227ae749f09bb981aca30aa58716c30061d0620904b5618c7991f0c025ec2f31d8b8576c072172295c6d20a4d290e5586cfca61508af37450f5e55c2a4167358f5327d02f1260b27113b0abc5922b1e4718736dcb4845f56e44b2bf58c35198d74819e40785223f0352ed8dc2bb2061224864f9b2833ac09ca25ac09c7b31a7c9b9f28a87c9367bf96e5117bd96d8a748db2ed84c0eda8768c3de01670c1879d215cbb5c710dea5c6efc78a143476465e614597d37e7744622aeb4d743b5f04711171f1e02d666665d7c67985518fe27475a1725cb2194e7856aef7236acb84cb6668960a5dc9a5d7a5ea2118da6c0bc1493522078fb7431206e116f78072d436c174ddcd75acafe7df6a53bf915786a4eb371a13bfba99f505c7ac2a7458303919715aa6432c259a4235c3476c9ed682ad40790646b72afb4a83442745374f7a1a1e69d8238969dc46267f23b7cf184cde0e9a5e6e9b6379399711f1b102ac3fab372a617bc50b981a8d760c988bc0c015864930e73a8)))
                  .empty))
              (.branch
                (.branch (.leaf (.concat 1 37)) (.leaf (.symEncPt 161 165 31 dhAesPt0)))
                (.branch (.leaf (.rand 32 11)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 2 21)) (.leaf (.rand 32 59)))
                (.branch (.leaf (.concat 69 81)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 53)) (.empty))
                (.branch (.leaf (.rand 32 27)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.concat 11 3)) (.leaf (.rand 32 51)))
                (.branch (.leaf (.concat 73 77)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 34 45)) (.leaf (.kdf 173 13)))
                (.branch (.leaf (.rand 32 19)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.dhPk 26)) (.leaf (.kdf 91 2)))
                (.branch (.leaf (.rand 32 3)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 61)) (.empty))
                (.branch (.leaf (.rand 32 35)) (.empty))))))))
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([0x00#8]))) (.leaf (.rand 32 38)))
                (.branch (.leaf (.rand 22 32)) (.empty)))
              (.branch
                (.branch (.leaf (.lit ([0x61#8, 0x6c#8, 0x69#8, 0x63#8, 0x65#8]))) (.leaf (.kdf 160 13)))
                (.branch (.leaf (.rand 32 6)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 10 3)) (.leaf (.rand 32 54)))
                (.branch (.leaf (.kdf 80 18)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 48)) (.leaf (.concat 176 15)))
                (.branch (.leaf (.rand 32 22)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit (leBytes 32 0x0))) (.leaf (.rand 32 46)))
                (.branch (.leaf (.dh 30 24)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 40)) (.leaf (.concat 31 168)))
                (.branch (.leaf (.rand 32 14)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.rand 5 32)) (.leaf (.rand 32 62)))
                (.branch (.leaf (.kdf 88 16)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 56)) (.empty))
                (.branch (.leaf (.rand 32 30)) (.empty))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([0x05#8]))) (.leaf (.rand 32 42)))
                (.branch (.leaf (.dhPk 67)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 33 36)) (.leaf (.kdf 160 164)))
                (.branch (.leaf (.rand 32 10)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 1 0)) (.leaf (.rand 32 58)))
                (.branch (.leaf (.kdf 80 84)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 34 52)) (.empty))
                (.branch (.leaf (.rand 32 26)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.concat 11 2)) (.leaf (.rand 32 50)))
                (.branch (.leaf (.concat 74 76)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 44)) (.leaf (.kdf 9 158)))
                (.branch (.leaf (.rand 32 18)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (.dhPk 25))
                  (.leaf (.lit (leBytes 37 0xb8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a50001010101))))
                (.branch (.leaf (.rand 32 2)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 60)) (.empty))
                (.branch (.leaf (.rand 32 34)) (.empty)))))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([0x02#8]))) (.leaf (.rand 32 40)))
                (.branch (.leaf (.rand 24 32)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 24)) (.leaf (.kdf 160 162)))
                (.branch (.leaf (.rand 32 8)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 12 3)) (.leaf (.rand 32 56)))
                (.branch (.leaf (.kdf 80 82)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 26)) (.leaf (.kdf 176 169)))
                (.branch (.leaf (.rand 32 24)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit (leBytes 18 0x7379654b6567617373654d72657073696857))) (.leaf (.rand 32 48)))
                (.branch (.leaf (.dh 68 26)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 42)) (.leaf (.trunc8 170)))
                (.branch (.leaf (.rand 32 16)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.rand 16 64)) (.leaf (.rand 32 64)))
                (.branch (.leaf (.kdf 88 90)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 58)) (.empty))
                (.branch (.leaf (.rand 32 32)) (.empty))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.lit ([0x01#8, 0x00#8, 0x00#8, 0x00#8]))) (.leaf (.rand 32 44)))
                (.branch (.leaf (.kemEncap 70 66)) (.empty)))
              (.branch
                (.branch
                  (.leaf (.concat 2 38))
                  (.leaf (.trWire 4 69 0 0 166 157 (leBytes 36 0x1f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a00))))
                (.branch (.leaf (.rand 32 12)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 6 22)) (.leaf (.rand 32 60)))
                (.branch (.leaf (.dh 69 26)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 54)) (.empty))
                (.branch (.leaf (.rand 32 28)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch (.leaf (.concat 11 4)) (.leaf (.rand 32 52)))
                (.branch (.leaf (.concat 8 78)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 1 46)) (.leaf (.concat 174 14)))
                (.branch (.leaf (.rand 32 20)) (.empty))))
            (.branch
              (.branch
                (.branch (.leaf (.concat 5 28)) (.leaf (.kdf 91 3)))
                (.branch (.leaf (.rand 32 4)) (.empty)))
              (.branch
                (.branch (.leaf (.concat 2 62)) (.empty))
                (.branch (.leaf (.rand 32 36)) (.empty)))))))))

def bytesTree : BinTree HwBytes :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([]))
                  (.leaf (leBytes 37 0x3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch (.leaf (leBytes 73 0x100001626f6200010101)) (.empty)))
              (.branch
                (.branch
                  (.leaf (leBytes 33 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df705))
                  (.leaf (leBytes 32 0xfd7b2845c14e83b95fb8cc3b4f7b8116cf6f3fd3bdd9462380c6c76996fc28ec)))
                (.branch (.leaf ([0x23#8, 0x25#8, 0x1f#8, 0x46#8, 0xb9#8])) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 15 0x17465686374615272657073696857))
                  (.leaf (leBytes 53 0x65d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0xec19597384b08680a028b22d7cc7f415e6979b2ee95643f6b6e07905d9c622df))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 39 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df000000626f620001))
                  (.leaf (leBytes 32 0xad1eb6e9e387df589b13ca79c6549b8e5309f3071834a3738f36bfe5d7d7d7d7)))
                (.branch (.leaf (leBytes 21 0x13b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                  (.leaf (leBytes 45 0x6390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x86e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace4))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 42 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800006563696c61000101))
                  (.leaf (leBytes 184 0x1f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a0024320b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a50001010101252adbc5fd668244bee2b702b903547bc7e9761bdc96f03ff507deb278ea5657291a2022001800103fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b05210a44627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df705)))
                (.branch (.leaf (leBytes 13 0xd08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b1566240215318))
                  (.leaf (leBytes 61 0x1ebb34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x2429541396799c82dbc778deb105e581ba091898f74195fbdb85a45283c6396a))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 40 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd520800100626f62000101))
                  .empty)
                (.branch (.leaf (leBytes 29 0x525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x03#8]))
                  (.leaf (leBytes 41 0xda16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 34 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b15662402153180000))
                  (.leaf (leBytes 51 0x37379654b6567617373654d72657073696857fa0686eb97c86347027b689913b7ba1e2ea4b2b26943ef9d48d98f7782bc0314)))
                (.branch (.leaf (leBytes 9 0x9c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 47 0x3343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857))
                  (.leaf (leBytes 57 0xfb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 79 0x3343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857e44d7386028958b64ebb5f751324b0e67d621f120eeea63263e77b2c71ece3af))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 34 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd520800100))
                  (.leaf ([0xd7#8, 0xd7#8, 0xd7#8, 0xd7#8, 0x08#8, 0xd9#8, 0xb9#8, 0x11#8])))
                (.branch (.leaf (leBytes 25 0xaa9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 46 0x343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857))
                  (.leaf (leBytes 49 0xf252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 64 0x86e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace46b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e3))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 33 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df0000))
                  (.leaf (leBytes 159 0xb8c86a4b7a46164201f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a0024320b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a50001010101252adbc5fd668244bee2b702b903547bc7e9761bdc96f03ff507deb278ea5657291a2022001800103fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b05210a44)))
                (.branch (.leaf (leBytes 17 0xf356802ad08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a))
                  (.leaf (leBytes 32 0xdca7c61aa7a987e18382419a29f1af5a7776e03585c50f7f88f11132219b39b5)))
                (.branch (.leaf ([0x23#8])) (.empty)))
              (.branch
                (.branch (.leaf (leBytes 69 0x100001626f62)) (.empty))
                (.branch
                  (.leaf (leBytes 33 0xe13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523))
                  .empty))))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x01#8]))
                  (.leaf (leBytes 39 0xb3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x26dbbcc03fd18c061cfc083f071e14d5baf49d84843ffc43a4383b3212e60505))
                  .empty))
              (.branch
                (.branch
                  (.leaf ([0x62#8, 0x6f#8, 0x62#8]))
                  (.leaf (leBytes 51 0x27379654b6567617373654d72657073696857675cd8931fad91165aab9f19384fad036b91292bc99dd88b42fda26566aeaa51)))
                (.branch (.leaf ([0x23#8, 0x25#8, 0x1f#8, 0x46#8, 0xb9#8, 0x73#8, 0xb8#8])) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 47 0x1343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857))
                  (.leaf (leBytes 55 0x88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 79 0x2343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f747865547265707369685761ee114c7c6218231d5dc8989c493e319e457ca30a25aa7f31b40835507e86c9))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 41 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df000000626f6200010101))
                  (.leaf (leBytes 32 0xdd4f0bc7b5536779bc729252a4b596c9c54419ee7375a75dfafc8a54d7d7d7d7)))
                (.branch (.leaf (leBytes 23 0x72c613b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 14 0x7465686374615272657073696857))
                  (.leaf (leBytes 47 0xf6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x54151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf3))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 44 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800006563696c610001010101))
                  (.leaf (leBytes 32 0xf3010689952eb0d5500818cb8f3ba22b71d4713955d5ffe7b8c86a4b7a461642)))
                (.branch (.leaf (leBytes 15 0x802ad08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd52080))
                  (.leaf (leBytes 63 0x9f4b1ebb34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 47 0x27465686374615272657073696857181e9b485bd683950efcead5d67ad9ab817002ab7bf0cda342af9a4ddc2daeca))
                  .empty))
              (.branch
                (.branch (.leaf (leBytes 65 0x1000)) (.empty))
                (.branch (.leaf (leBytes 31 0xedf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x00#8, 0x00#8, 0x00#8, 0x00#8]))
                  (.leaf (leBytes 43 0xab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 1568 0x89f6a44a4192619751ad2bfbd97786f69f870782bc1437a1c5432910070899f9861bf6442bfc650aa3795797e2ae2460699a71a2d491830adf1bfc435559d0a393bdae80abce052688e0c0a6c59369137d6287b5c4c6a89e40905fcafa29b87755e722bb9454a7b8759136f0ba9ac38fca225ed0ea618a542e67c35e81a5b8776129d5867eaca617f82831c8509b6b48b5d013b90b2d4526ad80faa8b4c32c79c6ab01db989b7706bc215a6e4cc84ed2339dc481a861d83cb1beb82cf21bf7ba1cf422cd8b829089cc54b9a34028b04df24c90fbf6a96506c8d03925e55ab4f99397236f9f13462c5cf26bf8d90f7c6407062aaa082527cc4e2031758b92765d2a57551892968adfa5d113c72955a02c9333955072fcd8bb835e2e814d4161349cb6c92475de6b980874e796a339ff66058e32cbca8f390b76f3be9cb637c8622ac2a8ed8a18f5386c95133c3b9206bd64e5913464220f1410af120141c42907303f1e61287d43ee913ab868c38738a3b08c15ebc9141fba83f78f3a64451626adfc966c7af03b1bddbaa77d4a4cb252a06c8eba6e8734a2c0bcdaa2c2782d959e236a396b93e2ba14769485b3bd1bf623725870fc3f6a886933d0e43105f87478db30f31dce0af1541a764100ce5b292303e74766957a28e4bd4a45140844254387eeaac3402acc1fc2f58325a3f50ff1e173686511712e3db626631bbb1fbb58cb3929287cada9d4773d155344a15c4ed60990e5a9a326ff17952265ba293a88646d922998fb7baf8b868dd24f850118bffca0c889d56de0751538c665fac0688282bd6ae80051e59ed5a1b4da525994561f9632c0b02468db5ab480cf3fabfec860d0b4250316d723bc84b2693183bb53a3ca2ce378b79813c3588b2b74344660a1a6b9c5c3d27f77c03a41615c686c99b2e78070f841650624110b688318c561cc03ac65ba3a1419a60bb58b451997c50ea1b2ab32899d86a80b510632f64191316134c2ac46f8fe4fc61141baf92864942356a358f7002b27a96f92a14e59ffca5cb3bdb02ac9b9292ec6fb24c42922216bca5a8865d77bbc05f09486459929897b3bf3ac17070d697807e7915582289de265787ad287a2828329e21bda629ad15d7922879a68c88ccbb69a9107a5fcdb27119170540e469aae1f64149f08f86c14b666294941578b8a6674bdd5926b996d7410df6bea443c2a4c10ec161ca954009ac0b931626283a69834ae15542267744f4e85ecad5ad695f90f23a0016474f6561892125982c6021f7857c60ae534cb79e2941c80642aeb2fe257a69c6126326a5a58fa58d1157f2cf7a8a5d1cb98cc7e55c1637b33b917d8b7774b367cae5f54a645e260327adb5bc3155a00c555174b68005256b52263bb6a7dc2c5c7e29c3e91f346534f1e3387688520100ab94e333f06c7468707be0bc32d783579018ce60c03346052b86523b19becd6a0cba09f14381d235217045a448b637e501b48872f3c5625c3e644282b430b18198c130e1a22cec8e7a9c6133605649550532b33111e34ec8dbd550c8611b7c9816da026ac53e856772b789b80828a281641e7430986e12969e746159539ca0b68a53ab460952ef9423ad05e77a74e9cf52582d3b07837566be4fc8527e3b2414e41b84857148416e974962c7864db3116a3a52b21e5c7e227ae749f09bb981aca30aa58716c30061d0620904b5618c7991f0c025ec2f31d8b8576c072172295c6d20a4d290e5586cfca61508af37450f5e55c2a4167358f5327d02f1260b27113b0abc5922b1e4718736dcb4845f56e44b2bf58c35198d74819e40785223f0352ed8dc2bb2061224864f9b2833ac09ca25ac09c7b31a7c9b9f28a87c9367bf96e5117bd96d8a748db2ed84c0eda8768c3de01670c1879d215cbb5c710dea5c6efc78a143476465e614597d37e7744622aeb4d743b5f04711171f1e02d666665d7c67985518fe27475a1725cb2194e7856aef7236acb84cb6668960a5dc9a5d7a5ea2118da6c0bc1493522078fb7431206e116f78072d436c174ddcd75acafe7df6a53bf915786a4eb371a13bfba99f505c7ac2a7458303919715aa6432c259a4235c3476c9ed682ad40790646b72afb4a83442745374f7a1a1e69d8238969dc46267f23b7cf184cde0e9a5e6e9b6379399711f1b102ac3fab372a617bc50b981a8d760c988bc0c015864930e73a8))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 40 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800006563696c6100))
                  (.leaf (leBytes 32 0xdbc5fd668244bee2b702b903547bc7e9761bdc96f03ff507deb278ea5657291a)))
                (.branch (.leaf (leBytes 11 0x25469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x01#8, 0x00#8]))
                  (.leaf (leBytes 59 0x34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 64 0x61ee114c7c6218231d5dc8989c493e319e457ca30a25aa7f31b40835507e86c93fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 38 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd520800100626f6200))
                  .empty)
                (.branch (.leaf (leBytes 27 0x5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 19 0x27379654b6567617373654d72657073696857))
                  (.leaf (leBytes 51 0xc64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 128 0x86e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace46b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e354151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf32b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373b))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 37 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df000000626f62))
                  (.leaf (leBytes 32 0xc65fb2c7964deae9eb437757908023af7468ab2c7ad5ae34197b550cd7d7d7d7)))
                (.branch (.leaf (leBytes 19 0x758df356802ad08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6))
                  (.leaf (leBytes 32 0x8f064f78ad3e6ac583d25b8fb206870a41be7644b58f31f2328ec8b147ea7c64)))
                (.branch (.leaf ([0x23#8, 0x25#8, 0x1f#8])) (.empty)))
              (.branch
                (.branch (.leaf (leBytes 71 0x100001626f620001)) (.empty))
                (.branch
                  (.leaf (leBytes 35 0xc0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523))
                  .empty)))))))
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x00#8]))
                  (.leaf (leBytes 38 0xdb3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x9ebeb27d522a4e8b1b9ec6ebbda97281992ffac69a7acd4c118e846ea93bc949))
                  .empty))
              (.branch
                (.branch
                  (.leaf ([0x61#8, 0x6c#8, 0x69#8, 0x63#8, 0x65#8]))
                  (.leaf (leBytes 32 0x675cd8931fad91165aab9f19384fad036b91292bc99dd88b42fda26566aeaa51)))
                (.branch (.leaf ([0x23#8, 0x25#8, 0x1f#8, 0x46#8, 0xb9#8, 0x73#8])) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 15 0x27465686374615272657073696857))
                  (.leaf (leBytes 54 0xa065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x61ee114c7c6218231d5dc8989c493e319e457ca30a25aa7f31b40835507e86c9))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 40 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df000000626f62000101))
                  (.leaf (leBytes 51 0x37379654b6567617373654d72657073696857ad1eb6e9e387df589b13ca79c6549b8e5309f3071834a3738f36bfe5d7d7d7d7)))
                (.branch (.leaf (leBytes 22 0xc613b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0x0))
                  (.leaf (leBytes 46 0xb36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x2b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373b))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 43 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800006563696c6100010101))
                  (.leaf (leBytes 217 0x1f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a0024320b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a50001010101252adbc5fd668244bee2b702b903547bc7e9761bdc96f03ff507deb278ea5657291a2022001800103fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b05210a44627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7053c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a05)))
                (.branch (.leaf (leBytes 14 0x2ad08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df00))
                  (.leaf (leBytes 62 0x4b1ebb34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x181e9b485bd683950efcead5d67ad9ab817002ab7bf0cda342af9a4ddc2daeca))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 41 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd520800100626f6200010101))
                  .empty)
                (.branch (.leaf (leBytes 30 0xdf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x05#8]))
                  (.leaf (leBytes 42 0x32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x3fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 39 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800006563696c61))
                  (.leaf (leBytes 32 0x7ab867650dbf293ba64ca99b028a06ccb7ca7a35cbdbee763f0a1a89736fc326)))
                (.branch (.leaf (leBytes 10 0x469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x00#8]))
                  (.leaf (leBytes 58 0xc5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x4db1c7d7cb3f0ef2dd4c4f71b3da39d48a6630179242aaa06c341d1277e3fb11))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 37 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd520800100626f62))
                  .empty)
                (.branch (.leaf (leBytes 26 0x21aa9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 19 0x17379654b6567617373654d72657073696857))
                  (.leaf (leBytes 50 0x4af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 96 0x86e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace46b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e354151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf3))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 34 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df000000))
                  (.leaf (leBytes 32 0xa7ddd59209bc7e55956f373e18a71d96c573e2cce70cd864f56d485ad7d7d7d7)))
                (.branch (.leaf (leBytes 18 0x8df356802ad08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 32 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7))
                  (.leaf (leBytes 37 0xb8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a50001010101)))
                (.branch (.leaf ([0x23#8, 0x25#8])) (.empty)))
              (.branch
                (.branch (.leaf (leBytes 70 0x100001626f6200)) (.empty))
                (.branch
                  (.leaf (leBytes 34 0xf2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523))
                  .empty))))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x02#8]))
                  (.leaf (leBytes 40 0x16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x26964f30e299608354c3ce2401e61e48206f8f36b8468efae8fb77c01904264a))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 33 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800))
                  (.leaf (leBytes 32 0xfa0686eb97c86347027b689913b7ba1e2ea4b2b26943ef9d48d98f7782bc0314)))
                (.branch (.leaf ([0x23#8, 0x25#8, 0x1f#8, 0x46#8, 0xb9#8, 0x73#8, 0xb8#8, 0x98#8])) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 47 0x2343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857))
                  (.leaf (leBytes 56 0x9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0xe44d7386028958b64ebb5f751324b0e67d621f120eeea63263e77b2c71ece3af))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 33 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd5208001))
                  (.leaf (leBytes 32 0x668ec26226d31920e21a2b81bbeb4086ef71d1c6b412e57311b9d908d7d7d7d7)))
                (.branch (.leaf (leBytes 24 0x9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 18 0x7379654b6567617373654d72657073696857))
                  (.leaf (leBytes 48 0x52f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x6b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e3))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 45 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800006563696c61000101010101))
                  (.leaf ([0x42#8, 0x16#8, 0x46#8, 0x7a#8, 0x4b#8, 0x6a#8, 0xc8#8, 0xb8#8])))
                (.branch (.leaf (leBytes 16 0x56802ad08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 64 0x10))
                  (.leaf (leBytes 64 0xd29f4b1ebb34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0xdcb7063ba7528d591eaa850906cb91213281bfa0c4c4420d30bbf4d01eca2095))
                  .empty))
              (.branch
                (.branch (.leaf (leBytes 66 0x100001)) (.empty))
                (.branch
                  (.leaf (leBytes 32 0x3e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523))
                  .empty)))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x01#8, 0x00#8, 0x00#8, 0x00#8]))
                  (.leaf (leBytes 44 0x90ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 1568 0xb42a96dfc7a8a6d25abee582e4b78cea7fadac372a1824a1e626760fe6ff6c9e34b2c6f03cb0501a903a303f516d73b2db2a00072963704437743abdce9db0dc84fd0ba040ec002e7baf168e128381ea90c450e953c86ccb291155d636cbd1b560de601ba52819dc2272f5e82e1fa3962fb32205351bc1ffdc5466b3db95ac329db4a737713a2b490456ae8fada2e9ba4550f9153fa011cc5d9cd2f0a3bf536fedf72c797f8f0582d2a1dd5cec9691a837e7d5f74e8993b8126331de8288bb54d6f29b2bd3ac0fc96ce62e013b07ea8cf6796c7b526ed61f4eadc6d9672a5c71b5b4d1e69d374456f3b914a23a0c58ddc2e0cfdb434ca164fa8928d637d9434e9f4a19a7d57785ee084ca2d9350115ec2a56fdfe5e6e4d36c992a9ff42598279e32cda1c5b345c77f6fcace6d3c05989c16443b0198a4430dd5f2201b6bc024ce4abf131369ed8e983942e19e39930ed26ed7c7461c962453cfa647e37c58b7a72730db8a5d60dd8a2a9afb3beb9bacf4657b7926aac6e524367ebee8716bcb68cace7e857b472fa59325e7df90a65f75ed132b5c410b80565daf1cbd26ef53ef459de28227ec0500ff994facb3e97925f187e902475c8b0b4deac39a887024e09c951dd07b1c8ec6f88b457144b6711f37789a0800cd689d2bbf117ca9302a01824d436c19bf7ca05c27d5ecb8d535098fcb6bcd1ec09d1fa58c0dc810cc9b53238d8d89ad152c4059e12095b07977a07b68006c97255d442475b5491d0497885d69dbcf3b1b4545c8e767e26e87f270d0aed90e54e267d0b4c48ca1090e437135bdaddea439d7d0fa04c446d4d45b5f11cae388f7956e01edc102b0766384ebd775eb816a5a9ac26143ec6c849ef7931ab44c83ea3d47dc0f0f06893f8e344aec2387347f66b1a7a2887f6c608721283f1778bc2bebc1a2347ddb961ec2c4d198f4c9516f05b7b570a4bce3fd8a2ddf5e5fecca255f209c0e5bea962fdceff96dbb7a8e8fad916f9058e4ce958339f95ed69432f6e4a3a9d33bf35b03b59cb896782b88bff16e27c11311ec4c006a58b8c1532bb525a72a3b7dc90e757c1b01647ac36b866bad55fa2f0da38a0139d21f079be85160334fdac98bdfeb68871e35213db43035f7ba38a456b0e29841ac3d4ced36c5f0b184b1fb44c3dd2993bb179ed6108d317bcf62d556c1366f797a44bd7d1b2585dd9fce77b25f32fc4ab1b1fa46b7ff2bc5adb73a0fbef2a60c09d3fdea2b1a5ed88b6da60c3bd3b2be0c331e6ce080835561884cf82745d1265b3d8a0d5726292c1d4191ae51ed8bf94125accd3aaf8fdde3a34218457bc05916295707c07e299a86856ec3fd6d30c73d709e4c5dd70dda07c29998c03f726117b5ec13279b904e3b715faf9761744f292833392fd0950fc7b2e6308e08fcabe7d852440067aa9dc4da1e2c3e5342580fd96a8a9c7b30bac80c5a4902989a7399a01da490bbc70b48f02fc3d11d9416c4e46eb691e2c663138cd576cc79ac8d5adf247b36b6cd9e5e8a04c374ca8cecb14159a294b149a6401eb19a4def3c4a0f66c4ac306b91292c477fabb4e282cdf2edb540ce09c61bf7f134f2ceaf617bc03fe047b4d5fe42bc7486bc2dd43e98e0d4baea36a4cbc16ff724df76ef4adaec83fde1d7001aad07b7ce3ce98a5829dc13f22f44c152cd6cb6245aefc3d7e2764bf795c64a1959fb6445c00293fd380ea76a052840184a2bb786a83f260b3ae9a4a32bda75fa24bdb4130d8c1ddd36f948b548557852eb7890f1194eb5d1e929a57c0d304666e3909429b4d2eb1eb5040febd7e88c7d16695fa45af26587a82e36f7655a39190bdde536d501169a29df89e38ad467374b25201a1057d2dfb2ff41261c1c039138ec8a41b1b80d7dcfd525bb84e94a1f126a5010f04414c22c107f7de161d2e7390cb291c163285dd4d816fb137d8c1887007fb458eee73beecd9289453829e6869b6e4240a18c5334ba3f64144ed7b58ac1cdbf6ddef93aa64ce716c130cb6419e10a0a1b38b07cb4ab66348a7f03624ee33ebcb3cb81b4cbf9204b7f6ac5edb9a2bfd8b27f8d037534f41a994293a1aa2a1fe72c59e9f45af08afcb7f995a36e1ea386abd57873249e8a85374526a9ddd5bf2b94d5813d9792c1fac610337404fe8b49af34604b0c177ad64ea0b19c5cf3f96a292dce6860e598e3a06d184059f6ef89cb80872c8e4))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 41 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b156624021531800006563696c610001))
                  (.leaf (leBytes 151 0x1f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a0024320b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a50001010101252adbc5fd668244bee2b702b903547bc7e9761bdc96f03ff507deb278ea5657291a2022001800103fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b05210a44)))
                (.branch (.leaf (leBytes 12 0x8725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf ([0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x01#8, 0x00#8]))
                  (.leaf (leBytes 60 0xbb34c5fb9a88a065d0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 32 0x863177d59a538caa707d477ef3bc0bcd29ddbc0055aeeedb3b5795a24d424bf))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 39 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd520800100626f620001))
                  .empty)
                (.branch (.leaf (leBytes 28 0x5b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)) (.empty)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 19 0x37379654b6567617373654d72657073696857))
                  (.leaf (leBytes 52 0xd0c64af252f6b36390ab32da16b3db3cf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523)))
                (.branch
                  (.leaf (leBytes 160 0x86e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace46b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e354151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf32b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373bffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
                  .empty))
              (.branch
                (.branch
                  (.leaf (leBytes 38 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df000000626f6200))
                  (.leaf (leBytes 51 0x27379654b6567617373654d72657073696857c65fb2c7964deae9eb437757908023af7468ab2c7ad5ae34197b550cd7d7d7d7)))
                (.branch (.leaf (leBytes 20 0xb3758df356802ad08725469c98b873b9461f2523)) (.empty))))
            (.branch
              (.branch
                (.branch
                  (.leaf (leBytes 33 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a05))
                  (.leaf (leBytes 32 0x2a6e1f242c3d680cda0d09f5bd834db9c1b98f83db8a933cf67408f91325c283)))
                (.branch (.leaf ([0x23#8, 0x25#8, 0x1f#8, 0x46#8])) (.empty)))
              (.branch
                (.branch (.leaf (leBytes 72 0x100001626f62000101)) (.empty))
                (.branch
                  (.leaf (leBytes 36 0xf2c0f2e13e0edf525b5b21aa9072c613b3758df356802ad08725469c98b873b9461f2523))
                  .empty))))))))

def opOf (id : Nat) : DagOp :=
  (btGet dagDepth opTree id).getD (.lit [])

def bytesOf (id : Nat) : HwBytes :=
  (btGet dagDepth bytesTree id).getD []

def shapeOf (id : Nat) : DY.Bytes :=
  dagShape opOf id

def anchorSfx : HwBytes :=
  bytesOf ckInitId ++ bytesOf recvTail0Id

theorem dagAllNodesOk : checkAllDagNodes dagSize opOf bytesOf anchorSfx = true := by
  decide +kernel

theorem dagPairwiseNoCollide : dagPairwiseOk dagSize opOf bytesOf = true := by
  decide +kernel

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagData

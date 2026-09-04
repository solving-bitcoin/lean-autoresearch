import GarblingPrize.Submission.G1LambdaCertShard01

namespace GarblingPrize.Submission.G1LambdaCertShard02

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard01.endpoint

private def doubled0 : Checkpoint := affine
  3332067860048431471901120675549418563229742095390465707195068668992425993262
  4546621221122757574104760471740610930208458978819243651148891685906683632782
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  12382416240261483366134609544070006535458403532768252729382873819872736304179
  9431717032309217064332584200471756010903306756974483285038305478617950921236
  (by decide)

private theorem addCert0 :
    semantic checkpoint0 = semantic doubled0 + semantic generator := by
  unfold checkpoint0
  apply certifyAddAffine
  all_goals decide

private theorem leaf0 :
    pointStep generatorPoint (semantic start) true = semantic checkpoint0 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert0, ← addCert0]

private def doubled1 : Checkpoint := affine
  19615556846814481385012439424681976036007657968151560485523491863997105961534
  11689566346231570584533647402054077991858216082588463701225368111222532306090
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  19615556846814481385012439424681976036007657968151560485523491863997105961534
  11689566346231570584533647402054077991858216082588463701225368111222532306090
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  9870362802559604489080142107600825250675753398121660797313089602382410193021
  16627425205459223563868478436304067528205934674905280393996374926107443570278
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  9870362802559604489080142107600825250675753398121660797313089602382410193021
  16627425205459223563868478436304067528205934674905280393996374926107443570278
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  9379890322449891287711519380928900544315951152304019295919513510177568054549
  2712470122302544550767583611547331082834228253261816913795957039775819076200
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  9379890322449891287711519380928900544315951152304019295919513510177568054549
  2712470122302544550767583611547331082834228253261816913795957039775819076200
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  8899436090528467020824754944019458553452626803372580279559276797673061576901
  16462217587667681816634772857805978681893409036208314643990088981791531797892
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  8899436090528467020824754944019458553452626803372580279559276797673061576901
  16462217587667681816634772857805978681893409036208314643990088981791531797892
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  1458399095058551734572233272031622771185163045960521746557360952628301630288
  13743395561230428162835556849140217964893356061848343663749083411426117048250
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  1458399095058551734572233272031622771185163045960521746557360952628301630288
  13743395561230428162835556849140217964893356061848343663749083411426117048250
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  16555704397524375693458998074542495004684812106034511755681970968398749604216
  8019325778685850783945088889719008859619873186551991266324895236420748736231
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  9653141570334029862192575767970408533389525647398243464724659812444592542382
  11621556915958142307611510862960638668267644527531627577260120214827858798301
  (by decide)

private theorem addCert6 :
    semantic checkpoint6 = semantic doubled6 + semantic generator := by
  unfold checkpoint6
  apply certifyAddAffine
  all_goals decide

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) true = semantic checkpoint6 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert6, ← addCert6]

private def doubled7 : Checkpoint := affine
  17062628611716670760893562920159448753396566719793232114868967879022036186568
  15307584804328513087340754936907721422192408933248534005292159287903969238692
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  5240782997526107719525532388025269200792555374040660833630969018774724457042
  3905093670943401121768099126636813781709908730214859055053928762063311994680
  (by decide)

private theorem addCert7 :
    semantic checkpoint7 = semantic doubled7 + semantic generator := by
  unfold checkpoint7
  apply certifyAddAffine
  all_goals decide

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) true = semantic checkpoint7 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert7, ← addCert7]

private def doubled8 : Checkpoint := affine
  5045762802093774911460668939362551745421819554245529067838532720200365291508
  1097209301309641795142746137264269682163299467579046040031228621442713441482
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  5045762802093774911460668939362551745421819554245529067838532720200365291508
  1097209301309641795142746137264269682163299467579046040031228621442713441482
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  1569583295069100327154460808194434286352848936021996781921401601298729942717
  8925637327765498213602715269945997147827424912667119614627051246723473053324
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  13977842120718582234752294188753935864110817346167204431412605085253831228961
  12866388258612911138752980778894425612838464985311454699435042088544867254988
  (by decide)

private theorem addCert9 :
    semantic checkpoint9 = semantic doubled9 + semantic generator := by
  unfold checkpoint9
  apply certifyAddAffine
  all_goals decide

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) true = semantic checkpoint9 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert9, ← addCert9]

private def doubled10 : Checkpoint := affine
  4720384595298703046707714054287920282944234454287558635497453403749805568916
  9078350823764987140107193435074878520903973510070860042147121034868438319395
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  4720384595298703046707714054287920282944234454287558635497453403749805568916
  9078350823764987140107193435074878520903973510070860042147121034868438319395
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  19883395931399060599343557903440614641858149589512383099424909661695010305671
  7996923187542190712574674662162708270013229348458442827741805584584835557482
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  17821466386348378287481547448105471696167359051887084229007712378849333742407
  17529815885790906721435937474790651136903277165480316940794474916714405151366
  (by decide)

private theorem addCert11 :
    semantic checkpoint11 = semantic doubled11 + semantic generator := by
  unfold checkpoint11
  apply certifyAddAffine
  all_goals decide

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) true = semantic checkpoint11 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert11, ← addCert11]

private def doubled12 : Checkpoint := affine
  14651116721251116598493805822846940966114939734128829321884853914538412986876
  10945158513054411713558917139762213369131259879839592204141988332850782267736
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  14651116721251116598493805822846940966114939734128829321884853914538412986876
  10945158513054411713558917139762213369131259879839592204141988332850782267736
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  15410949752473953024579720228205391354879865780863784816946275839678458451629
  19668588128558314094121411205397262296720424721834704677542954460422013801940
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  15410949752473953024579720228205391354879865780863784816946275839678458451629
  19668588128558314094121411205397262296720424721834704677542954460422013801940
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  16633804386315281602301596109817858862183732570089674605960393122885922695695
  9199234829468124673982531240266196785181573903452045240383079531561836149376
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  15766541273930938157482459339627490370116180404867908859389396163879979195369
  208654293528258088799687350519463752292146000899805070484710943207121402902
  (by decide)

private theorem addCert14 :
    semantic checkpoint14 = semantic doubled14 + semantic generator := by
  unfold checkpoint14
  apply certifyAddAffine
  all_goals decide

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) true = semantic checkpoint14 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert14, ← addCert14]

private def doubled15 : Checkpoint := affine
  13299097924730418539249131622221124796390408430025006746317541900731804463603
  9277926446205554058341207601599013427133574269974200068568447922338844252044
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  13299097924730418539249131622221124796390408430025006746317541900731804463603
  9277926446205554058341207601599013427133574269974200068568447922338844252044
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [true, false, false, false, false, false, true, true, false, true, false, true, false, false, true, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard01.endpoint) =
      semantic endpoint := by
  simp only [bits, List.foldl_cons, List.foldl_nil]
  rw [leaf0]
  rw [leaf1]
  rw [leaf2]
  rw [leaf3]
  rw [leaf4]
  rw [leaf5]
  rw [leaf6]
  rw [leaf7]
  rw [leaf8]
  rw [leaf9]
  rw [leaf10]
  rw [leaf11]
  rw [leaf12]
  rw [leaf13]
  rw [leaf14]
  rw [leaf15]

end

end GarblingPrize.Submission.G1LambdaCertShard02

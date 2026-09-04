import GarblingPrize.Submission.G1LambdaCertShard08

namespace GarblingPrize.Submission.G1LambdaCertShard09

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard08.endpoint

private def doubled0 : Checkpoint := affine
  1956019330119833216535383508368204131611561770897153447361292677439023316862
  4450553414591841680742825243019091395870155955591471117487555740706955053478
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  3105663296462853346111410956804414559653060813317684318427977991695950075843
  691898266432873980070453306764998251619611355439945572459731061005316991352
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
  10915264444468733395725967785104489275342588525986277717988242543700311731923
  6259740770481538882065457831046914612041480445202790297429056142205887433143
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  2399613597238396462301097119530690098649712388920725107513654038575532029316
  21640016051408295967549157665121093602783509517617886921951189749104120453665
  (by decide)

private theorem addCert1 :
    semantic checkpoint1 = semantic doubled1 + semantic generator := by
  unfold checkpoint1
  apply certifyAddAffine
  all_goals decide

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) true = semantic checkpoint1 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert1, ← addCert1]

private def doubled2 : Checkpoint := affine
  7056288591627505788950713230576745367607300307647457601702825243449504118795
  9732526433657241751677868848947120573065210383975924202179599668025413471317
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  7056288591627505788950713230576745367607300307647457601702825243449504118795
  9732526433657241751677868848947120573065210383975924202179599668025413471317
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  3453400164744809954171416846686966700632668942046551161938778041892362823583
  16037387041559050739421249605599408113101227314915559915611784217878448035487
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  11603781403558302638037571302205379469346787811104168562424905189213517044671
  14229841667330172032912068395666246501954202574132399001775666058052692951867
  (by decide)

private theorem addCert3 :
    semantic checkpoint3 = semantic doubled3 + semantic generator := by
  unfold checkpoint3
  apply certifyAddAffine
  all_goals decide

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) true = semantic checkpoint3 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert3, ← addCert3]

private def doubled4 : Checkpoint := affine
  3368653602365564593303042076577662767881317116917059186895582082588732459240
  753212351639998355594235053319630541215225753932043952094670287974185701825
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  3368653602365564593303042076577662767881317116917059186895582082588732459240
  753212351639998355594235053319630541215225753932043952094670287974185701825
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  5146255379071733969414870445761037824980570607929741408775686835041294512711
  11030821234141098827122413076053682316547780020273808541880051910856706459587
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  519857736174161039691766530981961402391492114179952012958369231320142436734
  2734501744737633591413811358237514847445045673893459448664374853538065421894
  (by decide)

private theorem addCert5 :
    semantic checkpoint5 = semantic doubled5 + semantic generator := by
  unfold checkpoint5
  apply certifyAddAffine
  all_goals decide

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) true = semantic checkpoint5 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert5, ← addCert5]

private def doubled6 : Checkpoint := affine
  4295851668748727275129128814332582705530876696738761411734288626771417706094
  5210881944458123809334337916370198530480794581127101520606531393854959047411
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  4295851668748727275129128814332582705530876696738761411734288626771417706094
  5210881944458123809334337916370198530480794581127101520606531393854959047411
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  13564316568658404489267716992640065343281022777420052682631235398196298484108
  1416010653485760633147605312570324697002113647077187408739207144624484439896
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  13564316568658404489267716992640065343281022777420052682631235398196298484108
  1416010653485760633147605312570324697002113647077187408739207144624484439896
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  8479117237395746442412915097697195745580994379308672996925771047682227179619
  13790666072010200376769016790836182162218399316309247786699808805187254808902
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  9104666668968574125198632769951661977893273544285426702664215711322447183734
  18199097612730187705267789775857291526681214935450832763812879264122600770776
  (by decide)

private theorem addCert8 :
    semantic checkpoint8 = semantic doubled8 + semantic generator := by
  unfold checkpoint8
  apply certifyAddAffine
  all_goals decide

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) true = semantic checkpoint8 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert8, ← addCert8]

private def doubled9 : Checkpoint := affine
  18268762965787724268843413819923096647748523221064261635900670985359686011404
  3051529525583092700211604002305842960084767412048811018454993942879246013172
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  11804675586305385982382584920033239174455059106785470828305922739432969302627
  2871866347055907070289625819890014592777231838152632436368194938378428952004
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
  11355247633432854703159634968846010890793001626521575516475699098608346214895
  19304569622838203516138653964587340851575021643118403972818946850628132032176
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  11355247633432854703159634968846010890793001626521575516475699098608346214895
  19304569622838203516138653964587340851575021643118403972818946850628132032176
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  140467921189070503842338633878695758609831116192944135978608827347386807023
  20978493187838938151092873151158996760230728431332253819159619109701888831283
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  140467921189070503842338633878695758609831116192944135978608827347386807023
  20978493187838938151092873151158996760230728431332253819159619109701888831283
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  2666668145225553080826907303526682994581446674553408187462154025365515298245
  14325695869674560693121876656683034871310914295187961344369616813096767211034
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  1796756475213021712959930213184320115912553109313269767831534586985071374850
  12763852621767769752651267334340414536259721554357364923848174459475626370386
  (by decide)

private theorem addCert12 :
    semantic checkpoint12 = semantic doubled12 + semantic generator := by
  unfold checkpoint12
  apply certifyAddAffine
  all_goals decide

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) true = semantic checkpoint12 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert12, ← addCert12]

private def doubled13 : Checkpoint := affine
  2866672766736831353814960393807951307421138171488798309568391457584176950116
  1962345431455525398176615256768215474795493293532893052003494417955470347970
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  1496540991256683789922794611006342571574230457785717392227329458716186848503
  17609728586996922261537417232845363207900725088818347928547782202770972891074
  (by decide)

private theorem addCert13 :
    semantic checkpoint13 = semantic doubled13 + semantic generator := by
  unfold checkpoint13
  apply certifyAddAffine
  all_goals decide

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) true = semantic checkpoint13 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert13, ← addCert13]

private def doubled14 : Checkpoint := affine
  1325146285540684158978535703290257777075641910458385507126692270220229389833
  9134355671089694751243463104947421716464083298899941856195870000486332066293
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  1325146285540684158978535703290257777075641910458385507126692270220229389833
  9134355671089694751243463104947421716464083298899941856195870000486332066293
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  18620622709006740106187826824592671041759315406662987571483032494557428895206
  5570925103502912260716621649682661677659207544273284263821605404625160110947
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  17182407157823338064433269755052173476291222056954113490663579043392834902496
  8409986809730212141458949799974282580936872509209696001048415203469342730658
  (by decide)

private theorem addCert15 :
    semantic endpoint = semantic doubled15 + semantic generator := by
  unfold endpoint
  apply certifyAddAffine
  all_goals decide

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) true = semantic endpoint := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert15, ← addCert15]

def bits : List Bool := [true, true, false, true, false, true, false, false, true, true, false, false, true, true, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard08.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard09

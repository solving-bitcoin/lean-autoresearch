import GarblingPrize.Submission.G1OrderCertShard12

namespace GarblingPrize.Submission.G1OrderCertShard13

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard12.endpoint

private def doubled0 : Checkpoint := affine
  20021534265047989830284924951489082594496439618344953928635875801135440611972
  11340144136901284450463652692844357910049838204645036474403956581580905053435
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  6879587272717695902844134047773277732743197473963223751050700670973168006338
  18013630555963130621600522214999364069144138940350295282749902924606490847392
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
  10603465884445780282610090626095539145683626363563397080097963045240105686301
  4494369676015499930125803874832226025012053361170262712010482854625828649208
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  10603465884445780282610090626095539145683626363563397080097963045240105686301
  4494369676015499930125803874832226025012053361170262712010482854625828649208
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  4400263822691323105548773124088699645994124908943564298160848299241367004978
  9162071736587670750320182106693062653601505626507205529776354745998091257404
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  19926456253954450105636659647574293731627912303108006357667575328406826238619
  19469336403296562341577641564214833581116687857009247811915398612552133452550
  (by decide)

private theorem addCert2 :
    semantic checkpoint2 = semantic doubled2 + semantic generator := by
  unfold checkpoint2
  apply certifyAddAffine
  all_goals decide

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) true = semantic checkpoint2 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert2, ← addCert2]

private def doubled3 : Checkpoint := affine
  12664098077352909444224873621382327709962227508015599540409072533639128792722
  21745389531216344603606825228513085293070810077166928094225633082321221373649
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  12664098077352909444224873621382327709962227508015599540409072533639128792722
  21745389531216344603606825228513085293070810077166928094225633082321221373649
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  11550201721647795047212350194882673768684193188732201206123807349383051955558
  1764606251949638193185878907553304483561199147664550132453428131992533086808
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  17809808800828189204989857441359747966279069689211279437142936385072784326384
  14524232380367492138104003696311069334886097443657852808007676911502653777059
  (by decide)

private theorem addCert4 :
    semantic checkpoint4 = semantic doubled4 + semantic generator := by
  unfold checkpoint4
  apply certifyAddAffine
  all_goals decide

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) true = semantic checkpoint4 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert4, ← addCert4]

private def doubled5 : Checkpoint := affine
  14838018378682843985652221421006540015435510973724319010397359700359180951615
  15313375057795556758962669954278971171331388523357700709254330787896335017611
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  21512579976108710984982107260636479836137672567777949177240998156780044576016
  12756524534595617123575072751134844195958554515382766727870578531285843323239
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
  5277856786320568033665207450676637488928824947555173716681605369390322061101
  7860410807915211956910366159843320678242469024337069592617487914728857684348
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  5277856786320568033665207450676637488928824947555173716681605369390322061101
  7860410807915211956910366159843320678242469024337069592617487914728857684348
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  3387023448792248663169312803022067432712357765215396408176983842546812430512
  4813183790220863957527933855185345053211250838659802484139916065046414964571
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  3387023448792248663169312803022067432712357765215396408176983842546812430512
  4813183790220863957527933855185345053211250838659802484139916065046414964571
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  21554799075947683185039801857708376533407963442710688690806931662179514733006
  11669322461528929388784680867034087026696779138902703320663593973389826607622
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  5398750939419111040155066173148532627328762214990448310302079762857893508677
  1115312267434942596622949857158846812505500741396416953150882638693942315112
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
  10945505906220687596492648420406886385174344348804236339649183285290851008238
  1687748508546546691216549040932832375110266983915207458452092482942899936864
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  10945505906220687596492648420406886385174344348804236339649183285290851008238
  1687748508546546691216549040932832375110266983915207458452092482942899936864
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  21857172676405067121758283918588870320483563074777308944961883188012727934153
  3245667496210653934821060542171832681939271931418672532074650179666032695416
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  21857172676405067121758283918588870320483563074777308944961883188012727934153
  3245667496210653934821060542171832681939271931418672532074650179666032695416
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  5347234361025335044169415399187001726236885410426914643064137402413890318023
  12049830686041387067081974055557521383799458218831754496215632367027237167947
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  1946808861045025617503469028974348077792325321964753948740588070083151705413
  6461727574722275847703776236012258002284914284176519966705978982506069147224
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
  13418001134195887248061559000159853970268387030664272778784650915559930722961
  6510117568776965977689596825902857194973594736959937464858954551799318282358
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  16088861184824031822088878591119798562267037605748281920564904995331226313904
  11660877068632102265673926725541233197023496957959784122414301245095522474304
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
  19630135958874598599156324907434086589874837966713466718638897254585457690933
  1215083759637841539876930297015452182659789754863026424656238157440263596944
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  5316175863453146906996089071930315056832299144633832196659022682337144380775
  3054922473209376917532143532481901500354037593489308950960551737288680593825
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
  463840483850370034700430519912912276230269652022667056483292128180140501094
  10923491354143366310576428197915872894832981068401813917925881631685150543249
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  7496237058229201417747565556403782279983689975103914195952243531786907822738
  5322023083872232148723196039146632746093883042086547558259042902113077159381
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
  7733639504359773843249643184603165392222102958348192323152617282227904299020
  15513199716968808781839773180057275273192009371449636445621195975879618454250
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  20005353362510544789447017663183550895256750763454211535051487172391857870955
  16809366114809725670250412214230350563761866122127480158151841799052037166032
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

def bits : List Bool := [true, false, true, false, true, true, false, false, true, false, false, true, true, true, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard12.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard13

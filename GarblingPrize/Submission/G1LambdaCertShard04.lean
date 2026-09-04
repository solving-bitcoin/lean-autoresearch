import GarblingPrize.Submission.G1LambdaCertShard03

namespace GarblingPrize.Submission.G1LambdaCertShard04

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard03.endpoint

private def doubled0 : Checkpoint := affine
  11301699193669341381694954349179778292265195985229953363713378069080734666902
  17264230729754546429906664117786435674030459570859652336338172977032247498313
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  7304244190055946734141298498723020109916481982465436207752559886299555586774
  19150728303357587359351886375699936879314400935257175168809012141104806240655
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
  607411142255821019409186330783166768339992386276106997200638728952308220839
  17092427812283501300303116927736436067712222462510425551811404840323932450350
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  607411142255821019409186330783166768339992386276106997200638728952308220839
  17092427812283501300303116927736436067712222462510425551811404840323932450350
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  12183619163537517482436654198740242641819505163613812429392126589961399606905
  4621644181417303362681695063231273546986526266658496248335301223625467507292
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  8747968301906611346621637581766420120715999105489225087845195511534382607443
  385765848728536685672414309559692993312820161779094427721541147230674625893
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
  3482911080491131748363360538705913506152228001104912898625290322264912435319
  3940735697619147026419708179868724199269248089861510245716081314382176726453
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  7590330535372996731262255357398833204379177163147440753015194287682286425666
  11697593125180281147507335507951611789104158377241223360812689182015898608162
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
  17596622020393286025810422909771982158542053304881940770299083660926398957241
  10108964854731617381844198760970121075403192604886328743469377090283468650170
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  17596622020393286025810422909771982158542053304881940770299083660926398957241
  10108964854731617381844198760970121075403192604886328743469377090283468650170
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  13984868378223729250315978408379823049000942582197562044466711326911208333454
  18978965611463149451631803809868078921792414868539417737976420491768530739769
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  18561920695872512253182351035445141872899848813917686748502052613367779222729
  7924573168793723625711649837251623339292072204471674906394511610571577043790
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
  7584690645635563577142213738891338884145916196642053698636379506572147603394
  19302851858787626938748780067219801725443008232937242704142811522929970970170
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  10500136933262330039288726613926006782941199497403210677411267130098438828184
  1553438011709094319904511006064630558858586656226374780229244377526875002806
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
  5083872717474882240343233645762779031187161263259971802894300694762436764948
  2330389911985552965327033658293674125942965292642172667649180223478153353094
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  4017001079497971307363889049379679084734020286332856720821740908966755159933
  6531096995839698560564072084287820973446625001299775295684176769299935540252
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
  20331163388131098722427025623152817269710287753963588652529721098780157919364
  20445261362275496415299093513352190842977560578986210470879389748014698918929
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  7736584300932741878389434668604453030078439476985596642423725424469348885924
  10034297220124567966480614071787053928215260013800628115302199834194763133870
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
  14521233218401529178921468952447580723409394398552147456920221064349110523860
  2066298906710804815541438839222770054218176158318742497778962097328938876586
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  13026309864789147764852744560549311327231450225661141739038504810356463072771
  18246446413115066412596260484699199280912666939624406407823628759523636197736
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
  4886799483818277115802740053534456203157174021912742373920500104203242396599
  20721619706912765896251279579700220158691983198436994215468749340283577529080
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  18797500464510945426696071726335106628162069647387569164157324074297127340643
  11055679078877845002549351361666719196317548206244711906420546629765012364641
  (by decide)

private theorem addCert10 :
    semantic checkpoint10 = semantic doubled10 + semantic generator := by
  unfold checkpoint10
  apply certifyAddAffine
  all_goals decide

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) true = semantic checkpoint10 := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert10, ← addCert10]

private def doubled11 : Checkpoint := affine
  4275827503561463499117443127986061484381850113035301862875351757016678881846
  13763686017832937417626124229803889090809716262432648473447990575963761608336
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  7564263622872264774812272397973989845753572124631636514714428203495192059319
  6031358891610917501167972147085889555724705007380537749121095926209084409688
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
  11589522867664806299169550061973691401965642539260875368296609617676071443374
  11107348472622358611945177639236003052943706045990367186397149575178388633947
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  9757592986115275849868742492167924599653345659630703600940535522496956232640
  9115579376601242084531689913457109390274583872088636395884095788969307484853
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
  18367205063562704483454222121752508783113954115611337119477566617916063371630
  10300765377721026737330075805546417112512761416136333491181790964028931066718
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  18367205063562704483454222121752508783113954115611337119477566617916063371630
  10300765377721026737330075805546417112512761416136333491181790964028931066718
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  20141365836160535366606215313095618349333024677982457633369286858574685543801
  20959159609715404384759414678240042683020259145795080400835906495390981766869
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  20141365836160535366606215313095618349333024677982457633369286858574685543801
  20959159609715404384759414678240042683020259145795080400835906495390981766869
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  14888398951564675487699016288426348960704873488789344611595781930863134391356
  8711689909278984366453490366981141090580649672513082187689812894335614580698
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  14888398951564675487699016288426348960704873488789344611595781930863134391356
  8711689909278984366453490366981141090580649672513082187689812894335614580698
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [true, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard03.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard04

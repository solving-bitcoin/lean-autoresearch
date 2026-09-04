import GarblingPrize.Submission.G1OrderCertShard09

namespace GarblingPrize.Submission.G1OrderCertShard10

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard09.endpoint

private def doubled0 : Checkpoint := affine
  20514355591889565761252819251037927847831457999931491915853198660562235503795
  20936384085172164280751576068311812118231155983509595229552853097300039372423
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  1914144769503543572129736174921464811766208766134214249996145895510455568473
  13768116764025300995590890354026709832979152595614028226460973667548303600043
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
  11068819866973019952744790499269689747096222081008404771048274898830593231978
  7084036087376573893691418461864374154272607331365028085046574082435771490985
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  2536526707570551341216376177812685434389764692767133459893048150561128071562
  21379231255317754614726479140200577479396325485433681511118898500998972589028
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
  839440150020227279120642978951186932300806004036993895669714140917640390056
  17155007998460806552693275811072727069032097720359539231321565341450702904525
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  839440150020227279120642978951186932300806004036993895669714140917640390056
  17155007998460806552693275811072727069032097720359539231321565341450702904525
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  1977961040777422355620502976418038760537845756166287374324381314266812120765
  18850312668577545903900588294529546141066047694607108855401296727979893630658
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  1977961040777422355620502976418038760537845756166287374324381314266812120765
  18850312668577545903900588294529546141066047694607108855401296727979893630658
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  11768306114815587263751531851778236500753526756946002902288023211755932376015
  5100903510863745827622385352664402378024398255153037584517552105182733537853
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  250253436018895877216416495513165520362856155146309980033518720331169433449
  21323274317500394595694886159256454910770799081145473484128648493344538522424
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
  4190702285855151748963040728807246035560442139001683237770238528171083112540
  6206087977047339537529998892278724144891670112664280519014407452520654451766
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  11833323160917654537851389409996227677457332257711979738057936162328736328756
  5309155511994672755289956593736076153766889612904278503651522147067764506334
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
  19552371425399913441347315334224598928178112514797153508476176719507969311957
  17453895529575611403336812941491502811203161263595766913144384748235096277691
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  19552371425399913441347315334224598928178112514797153508476176719507969311957
  17453895529575611403336812941491502811203161263595766913144384748235096277691
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  8010465813696286515157347072897360691523412374075489413338342382888826001610
  17796996439402024113326116836939948556847850977379207027053624080895840967203
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  21308438852277368721285575155886645610679460794801945420877662921483792354825
  52359321332734979384533928642339259339662210953775130665557932311310387313
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
  19210367940637193336242834069798870657737988988520266009872431640104071322675
  5365474323739128188389308078510104283636696230968834275847747582977029568316
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  120717803374555582323392277268630872880968583506578133667615386242896569880
  6129475455053413430235219618232968941897809095087059520528462302841920729351
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
  14200940620773578931313401295147717614113033913670987782092584757561734776950
  19600758891805429023521867088817943428320330250957289817272316680756382802879
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  4303947709082951354156697786520769433045986543388910658169042253463205230612
  2420209727216247476975323797573745902406106255636376706557680006441413300690
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
  16112599563338975974979587493020070008320105722357216977313134801600125757557
  7063972103797499904530664673468122134036873169537842250672870222946248192166
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  16112599563338975974979587493020070008320105722357216977313134801600125757557
  7063972103797499904530664673468122134036873169537842250672870222946248192166
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  4180103589007202953640796299655316036340497111723338558629089892272108188391
  9220683401275746195747183477564158738088367123296175953657916603156510245357
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  4180103589007202953640796299655316036340497111723338558629089892272108188391
  9220683401275746195747183477564158738088367123296175953657916603156510245357
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  7026660005597468304081788333972363166936533767195960264126755656252559890304
  17697919050718452242950802189796868208306637825404810564103199177646123286705
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  3696847466707670326280067021280801709494997226063563465207792184872815895357
  11806891827868100878305545813461324845360325804019748357632030684442997262374
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
  2964247171511534790052622364597132328437580643759129078185784086279975195495
  9663145408286629150198875873294030214104662368727854044044143940668025013973
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  2964247171511534790052622364597132328437580643759129078185784086279975195495
  9663145408286629150198875873294030214104662368727854044044143940668025013973
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  5480579204116993745225170735998109652802395368675776370532101605814118309865
  6726970941731664064336372339431343021413209685103869249283174061004250296371
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  19551724446896079405804909061746460736531290903379862419865283769252864111550
  12947521600645944130356291925047997296233963028276308100988568798625897226841
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
  196526119456560696575115651712628607686075727806338814543213968108037629616
  11937498572805340955608637364635615448468883579482070084177407311969352810403
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  4561426780069278263184563528082069963192282618877283470312087892392542844542
  12331345087662307646366417909380622969105811331960737886781897572742199818345
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

def bits : List Bool := [true, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard09.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard10

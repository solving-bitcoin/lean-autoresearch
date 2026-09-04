import GarblingPrize.Submission.G1LambdaCertShard02

namespace GarblingPrize.Submission.G1LambdaCertShard03

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard02.endpoint

private def doubled0 : Checkpoint := affine
  13197639276741041784659026143871327668664313767113315390522297442611908995505
  1012601062026701768285425987593370731903859951411473984309258883075070867811
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  13197639276741041784659026143871327668664313767113315390522297442611908995505
  1012601062026701768285425987593370731903859951411473984309258883075070867811
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  20923962214662849251942649884012263021932071243925809598148340804941645938449
  11697386029297797003441811829895272981777575523193463842201459662676241902968
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  20923962214662849251942649884012263021932071243925809598148340804941645938449
  11697386029297797003441811829895272981777575523193463842201459662676241902968
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  18633674784256435566118852343031191206396411783719741823577519850508308798012
  7973685941147219779135917473173611571998578225630088811398903130305605226214
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  3828043783777153789014265214754454459191195938558538458751093468032378445337
  2467624610383747855438830677196724942098020726095891110105734056434840383349
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
  5544825499335467799714694696838647507367473306118167131797488025253720838061
  13879464873324552026611385327345581499707896206242610264458586282720455667693
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  5544825499335467799714694696838647507367473306118167131797488025253720838061
  13879464873324552026611385327345581499707896206242610264458586282720455667693
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  10782715837026994673509816815179122718561503992384402765650639040117733948080
  6315489690158975555657513494766035531991744812637855074494854515398359680972
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  20341561985429866257237794541316489831441777749901497753943458962752925578068
  21595825031650831224235917389984397428298228850097557880426856170211441513735
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
  17541712633763452092276446767374594574636435248772653583677691905837839048311
  20190242458155579776410565950860700990578966853049195127803283513093102270225
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  2343758205575658143234353305814963828152314722523276080272763889818031103178
  7782843787777101312088262756667955889479417645986214832735197310193879482981
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
  11424243819265214199152507215077706223300108059886326765984523035352201809501
  9416212190094444249800484304188875156675781556984382417727146177327671613423
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  1794495634545290736168861953385678104501092420093343816736146065357594622047
  5757588222050244549862386088872454161779783824472212560165414788435582895023
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
  317933474171678821641183039338246111665032514671922376768119979040555772877
  2541493522404252408905761878396448527152027613483756697182176960940534818355
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  317933474171678821641183039338246111665032514671922376768119979040555772877
  2541493522404252408905761878396448527152027613483756697182176960940534818355
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  12772607693843232142043250469668341575130117175205403029557698962468292935487
  21562038965975825208846041905352672774791359030727804421383992136750674278327
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  2641568794243777045635236123853387302569325384382739733431567588225746527531
  8910265173814679361339609541851698412899472665049244886562751390525513037842
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
  19694267155443694666762113517683025695003142272109233346844535390916236057882
  722149395543047113806071101021531123312868385976357413328244424862338298638
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  19694267155443694666762113517683025695003142272109233346844535390916236057882
  722149395543047113806071101021531123312868385976357413328244424862338298638
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  6257909249061674474856079846600452166213514986515870262689901544309893617708
  184021653357517865696889484773937036306597713764027641505229725551521917398
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  6780103465363849570958777856540219167255516730294472721472734362496761577018
  11650728460517924355689823708424243513647941968094845814622308129159430485363
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
  4486513621620628959446736372288906573549714832516158365031344072478465884866
  9735802333702756883654107233300335164582701218588615872933086491274583259306
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  4397024174066744868962726631270113352338651306231210171111992129637115659749
  9294711195519009324076027423783202130720460480459683345363081669819442112010
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
  17613158346199387765598305642063988809466810910326584394479101380761604379044
  9638354309402463615235682367625073153906688205164627306861021407284040486249
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  17613158346199387765598305642063988809466810910326584394479101380761604379044
  9638354309402463615235682367625073153906688205164627306861021407284040486249
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  8418636207882715512606402751716384639693804112264866027307417987071177493603
  17949182400846249750339383861608711315854771888684967707445617388100750184583
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  8418636207882715512606402751716384639693804112264866027307417987071177493603
  17949182400846249750339383861608711315854771888684967707445617388100750184583
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  5849324091283909899179350743047615749506086610051257436435660356200355124484
  3844868715555386702169145368538322319788644259743026119120087316533377987633
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  5849324091283909899179350743047615749506086610051257436435660356200355124484
  3844868715555386702169145368538322319788644259743026119120087316533377987633
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  5590208359262289326825760097952283199932288027584036737202800878224332227943
  191467402431771870025605108329357921217200706438353640056319394287951150195
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  5590208359262289326825760097952283199932288027584036737202800878224332227943
  191467402431771870025605108329357921217200706438353640056319394287951150195
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [false, false, true, false, true, true, true, false, true, false, true, true, false, false, false, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard02.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard03

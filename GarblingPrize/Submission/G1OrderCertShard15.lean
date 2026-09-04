import GarblingPrize.Submission.G1OrderCertShard14

namespace GarblingPrize.Submission.G1OrderCertShard15

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard14.endpoint

private def doubled0 : Checkpoint := affine
  19160344921963847848039335847568873411425807361016539117861686925774747194844
  9924990947567700331970623917891703578794469542655157609938756118838211800672
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  19160344921963847848039335847568873411425807361016539117861686925774747194844
  9924990947567700331970623917891703578794469542655157609938756118838211800672
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  887359345784696120696147942004148861637654273598610085077096998247507568245
  4982961135386181672778433609998961958343386637718100620802177802072094231981
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  887359345784696120696147942004148861637654273598610085077096998247507568245
  4982961135386181672778433609998961958343386637718100620802177802072094231981
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  3368943841223469567718804779241171469732547828349094858259714784477259929501
  21148621142677723484773977960259048170115158869354706281870950609974870205393
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  3368943841223469567718804779241171469732547828349094858259714784477259929501
  21148621142677723484773977960259048170115158869354706281870950609974870205393
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  14179199379082904039500857934295295760084700649804250484721226212057251512731
  17322329406925871301969897033226294889134111374776494386129672075096367915287
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  14179199379082904039500857934295295760084700649804250484721226212057251512731
  17322329406925871301969897033226294889134111374776494386129672075096367915287
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  12284995474042360818259355402795767071442747720923270694651131246987175329999
  18388369154461897617730482395166516653103623418875430492702004462723800999873
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  12284995474042360818259355402795767071442747720923270694651131246987175329999
  18388369154461897617730482395166516653103623418875430492702004462723800999873
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  124104263348746699820243296627512547767824486891358560730287200164125242831
  4126565122625087160006228206494775150683807037206487578293049918084695563309
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  124104263348746699820243296627512547767824486891358560730287200164125242831
  4126565122625087160006228206494775150683807037206487578293049918084695563309
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  19054000724474322872219795259051237826917566290891001221834571941264729081810
  1393798562231072562770201785890748341953124988996803679336852367787415408679
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  19054000724474322872219795259051237826917566290891001221834571941264729081810
  1393798562231072562770201785890748341953124988996803679336852367787415408679
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  7230769019813642385348760909487096733126150733251427069126437937972133349264
  5303808279579493414713699325408078127648368198856753885812875846249318486861
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  7230769019813642385348760909487096733126150733251427069126437937972133349264
  5303808279579493414713699325408078127648368198856753885812875846249318486861
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  8072560362566127411344462881012674831531540353122947732798740100247880349164
  12595255086231605782521638172011139154504632033114198409595701681607482396644
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  8072560362566127411344462881012674831531540353122947732798740100247880349164
  12595255086231605782521638172011139154504632033114198409595701681607482396644
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  10969632791947051655379456753656371937227631669341412855378493071200512999424
  11581733400981890303337425887520133291189252189216568941146463853861557535927
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  10969632791947051655379456753656371937227631669341412855378493071200512999424
  11581733400981890303337425887520133291189252189216568941146463853861557535927
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  573011686476384881690454609118746307550318485872372750831234481186080953516
  1188230788905976769201396878518386897403528116966001667479997099236322495383
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  573011686476384881690454609118746307550318485872372750831234481186080953516
  1188230788905976769201396878518386897403528116966001667479997099236322495383
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  10296210423881459776936787717049993391325552021605413991699412493845789633013
  5355709597874802838595238292502764122767652289540488992110592095073644011920
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  10296210423881459776936787717049993391325552021605413991699412493845789633013
  5355709597874802838595238292502764122767652289540488992110592095073644011920
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  1
  21888242871839275222246405745257275088696311157297823662689037894645226208581
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := infinity

private theorem addCert12 :
    semantic endpoint = semantic doubled12 + semantic generator := by
  unfold endpoint
  apply certifyAddInfinity
  decide

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) true = semantic endpoint := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert12, ← addCert12]

def bits : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard14.endpoint) =
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

end

end GarblingPrize.Submission.G1OrderCertShard15

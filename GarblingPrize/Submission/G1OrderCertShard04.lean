import GarblingPrize.Submission.G1OrderCertShard03

namespace GarblingPrize.Submission.G1OrderCertShard04

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard03.endpoint

private def doubled0 : Checkpoint := affine
  13609853745788465261114106685736536350443777942850691951010498211486354778715
  8781428246963256225300715065399081687508596998735336782984647399533319559891
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  12267088100391532748365499369236352131669436370930223695668607309821911205880
  6619414379374760784253845190515848343951103900810114994243946947501111031053
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
  18649801222377818276321524678895140172996306511972467186123708329929416788577
  12854278909070433053759621891438970085500147101225229139593213908436131707276
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  17921148677036471914894518328360980104973313398151551115037615152912510220400
  5685387171315336921215881000136798572770126665877283463413259256052791214035
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
  8164563560424455395282834767141870687279711155019247847535758949637485803993
  19538002217229381140878980929199600339279099375530638827531118228978954737258
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  8164563560424455395282834767141870687279711155019247847535758949637485803993
  19538002217229381140878980929199600339279099375530638827531118228978954737258
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  15014216833986610683039131171541333701438049454045330972622302084805633540951
  9111465447071315232627492190215063112340635454082559746533261871723631655144
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  15014216833986610683039131171541333701438049454045330972622302084805633540951
  9111465447071315232627492190215063112340635454082559746533261871723631655144
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  21673005861711667308902399388489375736909212278961375365092133849100460729967
  4455215849530048806006228240499789538093773635540576044845204943944421659898
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  21673005861711667308902399388489375736909212278961375365092133849100460729967
  4455215849530048806006228240499789538093773635540576044845204943944421659898
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  2962515052219118157980391729890663689218794185091186960914729093591234065801
  19734804906444798786528440829267098069792024891343728241763028765457360745745
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  2962515052219118157980391729890663689218794185091186960914729093591234065801
  19734804906444798786528440829267098069792024891343728241763028765457360745745
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  21468380116908915125206946338382608567289796515286800706340223118106067351806
  13075888085325456713067020615388101227955353070579232226383966516399328281685
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  4245250637531130192748609361509858892538627214918641801716651871295382095590
  19646158723196270449595058839120751776501968602018960529872625451499365405764
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
  8187554712918960478336683342712972955424145537799272994018162371459021266978
  3483550431885083700642455236649104810379547307781524128013787382211400242373
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  8187554712918960478336683342712972955424145537799272994018162371459021266978
  3483550431885083700642455236649104810379547307781524128013787382211400242373
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  21708893960559384613431842027340304581904388515436300844355279830618417156373
  17863939529386146897666811414198097083934317141071551213820404031662587363472
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  14931636117504991279840113875419881387040611734703383629772995374637118474328
  15219395098062141773775936838624970711341598353900845867965283749182455803284
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
  10847505557317507561445800082710548525979326612867323401467419954595254086233
  11235830229634585300031194104468928958827795117798228633469899541890854018442
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  10847505557317507561445800082710548525979326612867323401467419954595254086233
  11235830229634585300031194104468928958827795117798228633469899541890854018442
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  21200181465070634668901868873553585698868669547621903726932279226281197838346
  20735716798282009922929711394459324368012052113675314525828862139559127816081
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  21200181465070634668901868873553585698868669547621903726932279226281197838346
  20735716798282009922929711394459324368012052113675314525828862139559127816081
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  1175712074005182969851933371671000318812198306717910431543463914048202587290
  20912887166496847990244845363369429739187759737992306420257543360507846517691
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  1175712074005182969851933371671000318812198306717910431543463914048202587290
  20912887166496847990244845363369429739187759737992306420257543360507846517691
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  1815437910549799610237288107936227451242600248566566131308042324047900670684
  14516134043794900929807530588559053370052504754462199710202844844165170365921
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  1815437910549799610237288107936227451242600248566566131308042324047900670684
  14516134043794900929807530588559053370052504754462199710202844844165170365921
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  21037827931955344747700664646026121676584576964591852573675260845006706513069
  2731109455351658874414535826312900916261495783004319112378608872127461658825
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  21037827931955344747700664646026121676584576964591852573675260845006706513069
  2731109455351658874414535826312900916261495783004319112378608872127461658825
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  11518947123138846150843072602057367618759590262024537105441997856666058904094
  3846774938775249394319848322581375776109515519108974316750604506915749321559
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  2853789530178150142563755136468914056564959260994926381706343505463210577269
  4624971915649830534927270412909856891300782545077725966777132530403616737527
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
  5694784260622112350275208867486142799440269295625181097734280533443605241013
  1588882997021653122954778482669216264398534791968388211599031597601425583888
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  5694784260622112350275208867486142799440269295625181097734280533443605241013
  1588882997021653122954778482669216264398534791968388211599031597601425583888
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard03.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard04

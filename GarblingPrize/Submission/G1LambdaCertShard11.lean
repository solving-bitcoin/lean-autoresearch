import GarblingPrize.Submission.G1LambdaCertShard10

namespace GarblingPrize.Submission.G1LambdaCertShard11

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard10.endpoint

private def doubled0 : Checkpoint := affine
  17550575648348552023488426059866060778309379640396614373588635066092545268751
  13097206971365319176344824334800280549245584187922841926841518356243070362018
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  17550575648348552023488426059866060778309379640396614373588635066092545268751
  13097206971365319176344824334800280549245584187922841926841518356243070362018
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  11873349528467397552575044468918779778013749510506201883439978718922047114536
  20210556557287808115167852382657604557004746474712704873888858677880499725055
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  11873349528467397552575044468918779778013749510506201883439978718922047114536
  20210556557287808115167852382657604557004746474712704873888858677880499725055
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  3321918528016199981616648061558731058762792132689613539934464228465010734477
  8888284898448161914544651578641909944562691259440596786445338449411022900740
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  5718573092743488090561294487983732204630960612568753182665461196692073270863
  9043369457691562592130296502561675492200223843567866741032323744121398290952
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
  2416459354619012952733948568914752847566378685319727298385729831873052561574
  5587361329119684102759265403164584874331959203344727693311314729412009520866
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  2416459354619012952733948568914752847566378685319727298385729831873052561574
  5587361329119684102759265403164584874331959203344727693311314729412009520866
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  21645966595829317468082325691615761553433721615404684166011101687645512190438
  2514522331343673441259133170469370488482112403382078187004057364087272493816
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  21645966595829317468082325691615761553433721615404684166011101687645512190438
  2514522331343673441259133170469370488482112403382078187004057364087272493816
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  9082995871295643248029581997875479939889700686002158876531789592029330919741
  16947169579923763963002785663519444928562164243558860009355014582767580885443
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  9082995871295643248029581997875479939889700686002158876531789592029330919741
  16947169579923763963002785663519444928562164243558860009355014582767580885443
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  20950495331380657611619678321271078816308116892861543327788067888932240490174
  21625878900831836780378921722800549559283426836087093967587584571834095647464
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  20950495331380657611619678321271078816308116892861543327788067888932240490174
  21625878900831836780378921722800549559283426836087093967587584571834095647464
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  878901062865383295198445719475621199963776489059346859094576386869057560174
  6143654474826223167434437721587150062911939351905866249096625479894657095325
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  8504031575233148692279481530821060364959194507046822221394480925085686715554
  9273518917623278002270584929882799122221145694084113211876326231111815298123
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
  68875366405897482734437241647126218987219548195471379432623368715967607926
  4673798297784900767166510070894965563076251861132228449676479439677689136153
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  6179306032194278920470389368358492217500424738393779539582318613369819850180
  12364904126297365251032610810997921864775681069390266312536811844781223409249
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
  11034536036457384226507158182085858945183084252211598232947324935762845034456
  14893689341212014256549342915714362425652841305336519353241846909197603755613
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  11034536036457384226507158182085858945183084252211598232947324935762845034456
  14893689341212014256549342915714362425652841305336519353241846909197603755613
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  21502840506500291691416206548223041554222937671667787202594379759764167995879
  4239235963562511051660203473923975651508722775661372017393140204736984476502
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  11658319678339048737017114908212845809903011076797232292981851366420478074144
  11679555856678219515586383506705836297421637629930685716786753537784591011430
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
  9618042079389852418261080268633377813375784969112755285945180448069757092064
  17632535256709894463797959182945267090292584495109154707893218024897527883293
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  5938119033517326346005256459637826682086721564336245109983605677064764053966
  19406544318253654744907157363057242723738515316711646175246418116559138690222
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
  7689226862336386214494710555669122877302613819928866389806661762491812437768
  20768111794617362452955154239660799816632738673457317518228411158063277765173
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  15421199639979879381207713111757281742961719229594398692604862661917518114331
  2895956841059616317861723146962557261798430448699797651831986591601737708076
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
  2885957510535131587395118180048681186979339791058499116421585959502060289546
  8255992826948674688429575162176629486312447936800673020467551228528569596009
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  2885957510535131587395118180048681186979339791058499116421585959502060289546
  8255992826948674688429575162176629486312447936800673020467551228528569596009
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  7296080957279758416965964017394286689046053271344243311784889420029299894718
  14592161914559516837360311011685651922521045698195227545085324353872253025824
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  2203960485148121921418603742825762020974279258880205651966
  2
  (by decide)

private theorem addCert14 :
    semantic endpoint = semantic doubled14 + semantic generator := by
  unfold endpoint
  apply certifyAddAffine
  all_goals decide

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) true = semantic endpoint := by
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert14, ← addCert14]

def bits : List Bool := [false, false, true, false, false, false, false, true, true, false, true, true, true, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard10.endpoint) =
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

end

end GarblingPrize.Submission.G1LambdaCertShard11

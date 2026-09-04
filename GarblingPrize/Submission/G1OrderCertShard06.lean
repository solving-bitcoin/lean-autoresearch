import GarblingPrize.Submission.G1OrderCertShard05

namespace GarblingPrize.Submission.G1OrderCertShard06

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard05.endpoint

private def doubled0 : Checkpoint := affine
  16715865214850939569917178835956938368446730271339480885797949716316284497270
  19886146467068377022459533841058309844343600081602413207556733814015584178753
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  16715865214850939569917178835956938368446730271339480885797949716316284497270
  19886146467068377022459533841058309844343600081602413207556733814015584178753
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  6000142419921353957423218989209844656901064084909382944240206165566430571395
  7896692869157960685941616234886911003127410856827580502402959505712875618717
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  6000142419921353957423218989209844656901064084909382944240206165566430571395
  7896692869157960685941616234886911003127410856827580502402959505712875618717
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  18497637619334717018270248530313984136320665269533824724329578365335002150421
  17203450320112181681547097964987676688463094113114617545209134904322164221786
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  18497637619334717018270248530313984136320665269533824724329578365335002150421
  17203450320112181681547097964987676688463094113114617545209134904322164221786
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  4574373655097207362943615250369522184296293658601324028460605312298338111609
  12076469179615372150336123423496407387929443862232772412204863606128568638110
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  4574373655097207362943615250369522184296293658601324028460605312298338111609
  12076469179615372150336123423496407387929443862232772412204863606128568638110
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  7769240515025628565234318536587965219087297833461899151255711746031105659540
  20691773397882802856169488034060435696395072926012856694843854847028383900791
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  16794399563592060408807198299571767547963994438871301290325028734636838765028
  2764260279601987530048224165503335592637505351958777659743325922302511097999
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
  18059112821840630957264205138423471398188182055713051397189683632459554713041
  7289356017554583290733909121725423826301256285771941856565091720847956162369
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  4267247532970207687799675758324412152542427034738568668108604477817294851347
  20816845207004569272201291652769393272272404079265302186722239284515029137108
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
  21038766711230555395497035620949310296843337229807869892219825034256632240884
  3511661231116752603623454357192773242307152084073724241735305921817174766690
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  21038766711230555395497035620949310296843337229807869892219825034256632240884
  3511661231116752603623454357192773242307152084073724241735305921817174766690
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  10344367969553456390416188690190150304287076751810094630101700012356696465308
  11906896384500444147301045382321264986130471556857236895574554835012339036520
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  10344367969553456390416188690190150304287076751810094630101700012356696465308
  11906896384500444147301045382321264986130471556857236895574554835012339036520
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  16290884305015216027253985735977128113167431432844487318960935747781679334171
  20488827089214899731253991252534653963255850366962721192803817287220357959727
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  16290884305015216027253985735977128113167431432844487318960935747781679334171
  20488827089214899731253991252534653963255850366962721192803817287220357959727
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  19428776265611853804866350916260546831697354763829922666671949538271795035669
  11626101678136789874890121286472211523915954666921526546337040848336080730179
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  19428776265611853804866350916260546831697354763829922666671949538271795035669
  11626101678136789874890121286472211523915954666921526546337040848336080730179
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  14132538038548644590892882495382537872992883422167565578475930208251434359817
  1787503649609316690403669977829453996224162065167162819825444981054573310181
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  14132538038548644590892882495382537872992883422167565578475930208251434359817
  1787503649609316690403669977829453996224162065167162819825444981054573310181
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  13359331191965508988470024842149735614136069946506021791970371080744324284320
  11587331713964512560129986040582507998085529754248582518236232167435050523101
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  13359331191965508988470024842149735614136069946506021791970371080744324284320
  11587331713964512560129986040582507998085529754248582518236232167435050523101
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  3295730211560957427849800158061486130967863751717680536425721735331358082240
  2340342747468353727883851831132639946529584575730114779689122881724541296875
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  1743358892238446787528410255605158798352457918483299003806164294460772291436
  18436519999506280275149963512466691064152435095302999004089955001151978786865
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
  5663034206170312308125999507075927956997838152965564335746385339304453308471
  3424452776851608129243898561548875626180610419697879402670959939032586516312
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  5663034206170312308125999507075927956997838152965564335746385339304453308471
  3424452776851608129243898561548875626180610419697879402670959939032586516312
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  12674218847944266526227421165562170880897249703119929719949943087180130989491
  8823494984394892019101350380783501343351897702169817294253765309495826470259
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  12053269439053162557791929048256339043797953948105883383317343929131210764317
  14734145423897124010836734084580132488839657112232095148482368670592399668006
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
  16648960279531841921158553278012524172950129512125314034845209682073726488699
  19775715529467074218474266950748476671193340282350883138025340955994742197066
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  16648960279531841921158553278012524172950129512125314034845209682073726488699
  19775715529467074218474266950748476671193340282350883138025340955994742197066
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [false, false, false, false, true, true, false, false, false, false, false, false, true, false, true, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard05.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard06

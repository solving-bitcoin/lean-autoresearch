import GarblingPrize.Submission.G1GeneratorCertificateBase

namespace GarblingPrize.Submission.G1OrderCertShard00

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := generator

private def doubled0 : Checkpoint := affine
  1368015179489954701390400359078579693043519447331113978918064868415326638035
  9918110051302171585080402603319702774565515993150576347155970296011118125764
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  3353031288059533942658390886683067124040920775575537747144343083137631628272
  19321533766552368860946552437480515441416830039777911637913418824951667761761
  (by decide)

private theorem addCert0 :
    semantic checkpoint0 = semantic doubled0 + semantic generator := by
  unfold checkpoint0
  apply certifyAddAffine
  all_goals decide

private theorem leaf0 :
    pointStep generatorPoint (generatorPoint) true = semantic checkpoint0 := by
  change pointStep generatorPoint (semantic start) true = semantic checkpoint0
  simp only [pointStep, if_true]
  unfold generatorPoint
  rw [← doubleCert0, ← addCert0]

private def doubled1 : Checkpoint := affine
  4503322228978077916651710446042370109107355802721800704639343137502100212473
  6132642251294427119375180147349983541569387941788025780665104001559216576968
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  4503322228978077916651710446042370109107355802721800704639343137502100212473
  6132642251294427119375180147349983541569387941788025780665104001559216576968
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  17108685722251241369314020928988529881027530433467445791267465866135602972753
  20666112440056908034039013737427066139426903072479162670940363761207457724060
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  17108685722251241369314020928988529881027530433467445791267465866135602972753
  20666112440056908034039013737427066139426903072479162670940363761207457724060
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  20453939078259811958859768391452073654460321168773748684493785442363495374770
  9582859829925552874957318860636821932456214701004608986274201852321144884827
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  20453939078259811958859768391452073654460321168773748684493785442363495374770
  9582859829925552874957318860636821932456214701004608986274201852321144884827
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  10609540540875827932797320455850052859827897498153948414964160013685734487046
  4813993645475805825314378837641334666424083557311142113454529369033402933209
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  10609540540875827932797320455850052859827897498153948414964160013685734487046
  4813993645475805825314378837641334666424083557311142113454529369033402933209
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  18671841561121186512404299858044607005439720124998758352195376573445009373523
  7809354174443370407285436184170596638054012602210636316839373867916701870951
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  18671841561121186512404299858044607005439720124998758352195376573445009373523
  7809354174443370407285436184170596638054012602210636316839373867916701870951
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  20995044653276697911307939368731579655805262441003207714079406136482465396049
  16084789831238785085254656825936433668733393950486585714819251008157280258921
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  14405412407063018763746635831875882041521743521688399193732505237193568935420
  6272588754200310235302307668289134587180577803105249708612090375729169501999
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
  14137258555763687132939794885051041870447540593633693869823145302990175245096
  4823424260238737826651581520945393565627261403333940726137376386911795887012
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  19629594285088025119699124465014260400978598803815724301163961238657807597874
  18972946422592766935115455664335606655985322343940506011023604971405642956012
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
  21112385514428891796169431039086280501551394190964081602819863409575226989978
  18218309326674345017307792464899257152985027233491987744887543710752419133932
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  21112385514428891796169431039086280501551394190964081602819863409575226989978
  18218309326674345017307792464899257152985027233491987744887543710752419133932
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  9439567917765669029501347063065533137850412880012470412086164080236539870552
  13634162010830210649266763010054033738468916624620186196298620608836343523062
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  9439567917765669029501347063065533137850412880012470412086164080236539870552
  13634162010830210649266763010054033738468916624620186196298620608836343523062
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  21756937165391847415104541733272689674245924447265498991583156437838473228067
  8120752594659579623788816080379380623233699211270727017443313228082184337274
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  13132964765163485444716177043487079492060902885853065696970933946490049319153
  4068653405888627265423540468292930351734471226927779604391831356913822304896
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
  9717817072720801701008715071150022087545160304836358844771695532270710306313
  4556503081702366128702989327562466017401893946567115050526392793271699367285
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  9717817072720801701008715071150022087545160304836358844771695532270710306313
  4556503081702366128702989327562466017401893946567115050526392793271699367285
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  10603037916082927299275152201573294150494341379932786198408700496936307944773
  18277110226847665964981398163300722465868704615894819387876549757384422718655
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  10603037916082927299275152201573294150494341379932786198408700496936307944773
  18277110226847665964981398163300722465868704615894819387876549757384422718655
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  13725458913518042704931395406606511407901531403298781018538023776470588395958
  13194786348850164788345658590082530163710910988194678660627524705489317917545
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  13725458913518042704931395406606511407901531403298781018538023776470588395958
  13194786348850164788345658590082530163710910988194678660627524705489317917545
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  5452235926606136789702305950946911767811544176402908875218248519614463732026
  8758937053656458489751793914453976519905869382206016111985940222851064227378
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  14264813743504709087572277969915465452846101983705707042475804812573347819547
  6665502117700586216085406727733241119255506109988221942866851018801464606740
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
  1615393765029574506146005826685263175389861848804824229233928429018519494518
  9703352315056188456993782499433453727625717945767457763003461334625262349913
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  1615393765029574506146005826685263175389861848804824229233928429018519494518
  9703352315056188456993782499433453727625717945767457763003461334625262349913
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [true, false, false, false, false, false, true, true, false, false, true, false, false, false, true, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (generatorPoint) =
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

end GarblingPrize.Submission.G1OrderCertShard00

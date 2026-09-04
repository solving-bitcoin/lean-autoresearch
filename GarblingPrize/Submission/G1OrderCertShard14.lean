import GarblingPrize.Submission.G1OrderCertShard13

namespace GarblingPrize.Submission.G1OrderCertShard14

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard13.endpoint

private def doubled0 : Checkpoint := affine
  13778417441527115048594690117047949441133928288552043071224120727920925593177
  17760661420648105182837058074020642912537073911139853538184037289600989435605
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  8059491878023404902058315989993562523808148645928349852381795954778728127542
  12836540159297566699190255773857783536567274802078949190530614215182933410705
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
  10944451880040176897265006620724579187411706564980841755901149805617821574865
  4826891080119456979144307001646250993176502956511547635100536556281454324166
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  10944451880040176897265006620724579187411706564980841755901149805617821574865
  4826891080119456979144307001646250993176502956511547635100536556281454324166
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  18547988277170396031024173795111487653533598236823338634926315499848716264632
  9170266845543497579463599697790440187891471876258537554445554197233404922158
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  18547988277170396031024173795111487653533598236823338634926315499848716264632
  9170266845543497579463599697790440187891471876258537554445554197233404922158
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  21514077069704124560307509007962696153046213362991534780509138008300036107536
  14031951318209649202636650052406311322658442650709504326870095797710814859937
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  21514077069704124560307509007962696153046213362991534780509138008300036107536
  14031951318209649202636650052406311322658442650709504326870095797710814859937
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  8375445861957106014727599871455565032530829964871288835416607778173138608030
  18688606973224452984196087228523865031769713604355177322819360559204009340685
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  8375445861957106014727599871455565032530829964871288835416607778173138608030
  18688606973224452984196087228523865031769713604355177322819360559204009340685
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  11070764736042928947241622973607091607029363451541845198814287139512404523300
  1806325991056295949777226636950423049472245802346272598989246073588797121679
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  11070764736042928947241622973607091607029363451541845198814287139512404523300
  1806325991056295949777226636950423049472245802346272598989246073588797121679
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  9505235282324437317279146314673675042869741295389300413888657067410794167518
  15038946189653084154991148895498847832108045961359226259705163148809266115690
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  9505235282324437317279146314673675042869741295389300413888657067410794167518
  15038946189653084154991148895498847832108045961359226259705163148809266115690
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  21253958592813165596446974180996401479102511261944137899667225206581636672002
  7848905193814911667082086241639955221633002568848044822832486665562120426940
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  21253958592813165596446974180996401479102511261944137899667225206581636672002
  7848905193814911667082086241639955221633002568848044822832486665562120426940
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  12489019718118963383648936313982162182753616369170651624702991752110316820732
  5091927323547464877111379297039580257510033945875796405646456730973778519765
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  12489019718118963383648936313982162182753616369170651624702991752110316820732
  5091927323547464877111379297039580257510033945875796405646456730973778519765
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  1673681362873432666819839789066825316021365691897986544978227774694072251351
  1709169751945494500247815938208007664826421477772626121201557891846453899375
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  1673681362873432666819839789066825316021365691897986544978227774694072251351
  1709169751945494500247815938208007664826421477772626121201557891846453899375
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  10744714802106827425888394862888810182779572104286404090525452745988254279537
  18703216195880807354136587774542183424409325491173937221916420714312269392675
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  10744714802106827425888394862888810182779572104286404090525452745988254279537
  18703216195880807354136587774542183424409325491173937221916420714312269392675
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  5942070469394237232698861489109794959468855373384094309241387005948179847646
  20303608384887861411903279435825060279881384748308292392678814336615222519590
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  5942070469394237232698861489109794959468855373384094309241387005948179847646
  20303608384887861411903279435825060279881384748308292392678814336615222519590
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  18819830460927528009327382683593189868620495855914431189999358994593911501872
  11648760058870234429798339537299700022849544508377709038024695150145511893411
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  18819830460927528009327382683593189868620495855914431189999358994593911501872
  11648760058870234429798339537299700022849544508377709038024695150145511893411
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  4724979338438337620187508035341199112686187003435685508000933272962314051517
  9630802697663988217610330104726922477585063056700314970774027875130740836618
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  4724979338438337620187508035341199112686187003435685508000933272962314051517
  9630802697663988217610330104726922477585063056700314970774027875130740836618
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  7429060867049855643771493596675526036604618967602466575106453903252939225548
  13954310940594949201507824515773766930662963361798323733095061125381951185822
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  7429060867049855643771493596675526036604618967602466575106453903252939225548
  13954310940594949201507824515773766930662963361798323733095061125381951185822
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  6599266017836942868473941844122039045588194660968998128822552050186689694185
  11684484235257161703169884468796605764447347748278158343270256378189557886368
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  6599266017836942868473941844122039045588194660968998128822552050186689694185
  11684484235257161703169884468796605764447347748278158343270256378189557886368
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard13.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard14

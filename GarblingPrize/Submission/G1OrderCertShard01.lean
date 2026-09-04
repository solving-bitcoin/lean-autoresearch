import GarblingPrize.Submission.G1OrderCertShard00

namespace GarblingPrize.Submission.G1OrderCertShard01

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard00.endpoint

private def doubled0 : Checkpoint := affine
  15861082628889704756444564386879917216918833959805530526981377052804846220224
  11630935753723338261089488658594380041393025375031794504247827947832817429774
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  15861082628889704756444564386879917216918833959805530526981377052804846220224
  11630935753723338261089488658594380041393025375031794504247827947832817429774
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  4186603601590990643919208521088327877840124845225690373332146556767190479149
  14377362231297443837455987187252793847727821946201263463667231408564742289412
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  15525560615552525143609111677341925582250692797064993952882886548522413062764
  18203431104738891146133628329981869126004574898527373601618254795269486639468
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
  19150204306754218684263545760741935658175041549417226169807092777621130371592
  16258985207117724867813746855760838417916071087460458672772553515130880499904
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  1333142790901505204859366195021021631678530986604707590915719465769006947121
  15399587771363585857262129877948052670843058645632841057776080501980470201769
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
  17888564079587544110050492541643844418825674239006627461629187225757848334752
  3911484354450028142314833463054991280868851728070571432295568474240834863609
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  6059192169760337238726070962541692257756534588172630340878530646839679601522
  1794703652753897511264739577110030369932395193700392294272364284302071684345
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
  901874762298374226630936083236048752882317833897062656715365069255234561528
  5432514478171607624067123677518171087180393473610864097061889158832316902680
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  901874762298374226630936083236048752882317833897062656715365069255234561528
  5432514478171607624067123677518171087180393473610864097061889158832316902680
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  9551959919498178396098483409724133208587126547743397018017757898489405504342
  619821417682071287200331603270138992448707105538346195531633550757915115152
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  9551959919498178396098483409724133208587126547743397018017757898489405504342
  619821417682071287200331603270138992448707105538346195531633550757915115152
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  7405195609621948867316366630994267552785693617424749070323486058676532772508
  12200056067481388410920644015636462696995506026537129245010219638168966109342
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  7350021255767972432724474360250666206372368985668248995172442191612592773757
  20750210546040000665576542131011277281902724930532109080089468728458537310609
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
  2635279829511012420179074635242322402494619603468802170014192486455596669492
  17516920154290207833178761273249335756729999958443999395836659270444885349962
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  18013491984905456525454436605705150670771203435503420165025367234161464051026
  929727432976037161100044150783245605760340084758904740318136472586147589703
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
  5570703561226380040199655113528456906778535966909818484584770141501881303798
  3347688306373900604916562399951819539174771925671450143673658908640586520430
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  11652184718160746077987363053209285973092250854369810057198057583150750382932
  3127481206917539967861628016883118695352425924409552018808041039994966598680
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
  13073160125451149128739079760444239255809468347676735712789124117477395297355
  2870141839114391598482190085516538742149359570455345405198951602542001095302
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  13073160125451149128739079760444239255809468347676735712789124117477395297355
  2870141839114391598482190085516538742149359570455345405198951602542001095302
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  6701305746698986451499028581669017386046895819489961359489581263562514948113
  7213851887611872224997932555022132889476259823882873453480093868852519585779
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  6701305746698986451499028581669017386046895819489961359489581263562514948113
  7213851887611872224997932555022132889476259823882873453480093868852519585779
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  18813742634681700761299240567285776650025466584792786827542663165162024354266
  1332139953773311381623157745740593833676646392706330008637382126017227088221
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  9919287261208055833010897399343846849181364038713417502261430158220552993467
  2255469506695140973286610915439942212784439199578713379309930278620078248244
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
  10228516078344147144541813535266364883729368033150355165505313248182186448993
  5842007323746616955453898260610763803968646969155645454693387793280369343371
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  10228516078344147144541813535266364883729368033150355165505313248182186448993
  5842007323746616955453898260610763803968646969155645454693387793280369343371
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  14958956047665287816414210305435721277827327459416132197798251754160986395370
  5072189445308516756388591589860407298518566377380098877239630305759322254214
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  18476597782837256020961355819158749283572033575025449111122557218345034691241
  1920573919992579196197768188329831531513945653024621048001030298860379015073
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
  3856713538355685901956033574354914683446623898233837322071384732489658486116
  5566407667124021096130495509970472833313031126510401864725933742679325361160
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  15576941252383958971371419745141735506125508437092934368946253824790277622624
  9302957452436071358621757524965656439643450421556167524013064770805002938446
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
  20361154053945982970871261386366932942429602690796416003340869011395495570725
  15181482326769496357850461713499621837027845056054501666190949287220944230069
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  4717871036515536747141762651066629586135471993132961719102106435051301326288
  16967786899600648678010495584789371934971729206337059434314417286232600661235
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

def bits : List Bool := [false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard00.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard01

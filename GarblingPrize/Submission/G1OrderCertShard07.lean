import GarblingPrize.Submission.G1OrderCertShard06

namespace GarblingPrize.Submission.G1OrderCertShard07

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard06.endpoint

private def doubled0 : Checkpoint := affine
  15205411462761954648932020763076712999567027686566369650926451499859832054899
  12587541717284698677070925448058516964705056850000728101325599867971167269267
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  21157814818847603217167214004612177395031769480244576857430073223383139008558
  6586821375488579255792301586377484145186594626466298867626033788168521101891
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
  13012067996646852652470141889484007192963878445174882939051139036811376289723
  20239992146507744330630452917992216124296312902950209008573020372113533943695
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  18754563955773683455658872729632968915963290095541263745291404097030544595831
  6616281298913110931504288910990953347131152331890379619411082897882024856159
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
  7453054499831553501102891277063833463123306800972066274295119658549941318175
  11615890141423662150778903607058649322017684036543414351880152485553892315931
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  7453054499831553501102891277063833463123306800972066274295119658549941318175
  11615890141423662150778903607058649322017684036543414351880152485553892315931
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  14681952093033829541130603319259804852121968634174410812690005514265104631682
  14322269518227312371087115668733546699944969267720122432782036257974969566989
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  14681952093033829541130603319259804852121968634174410812690005514265104631682
  14322269518227312371087115668733546699944969267720122432782036257974969566989
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  14179204379675857627015871038073775265356190828146876005617783114885079093990
  10107256159467558994892306413526868903081113870117096756724968844547847535580
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  14179204379675857627015871038073775265356190828146876005617783114885079093990
  10107256159467558994892306413526868903081113870117096756724968844547847535580
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  13753361556789026882139452199539198183712310689378084650191025692364807413968
  13406663038065741359684521877245158787639508734490779749497249540978049180941
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  13753361556789026882139452199539198183712310689378084650191025692364807413968
  13406663038065741359684521877245158787639508734490779749497249540978049180941
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  14590544886943254237596795071852215509422484836845159186717169483935907769734
  16081145635375888814249743021988028646001114453478283076367430992266887219639
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  20391787686659121011345531274155445182113365418571667643127949793424869552709
  3350207191227239689689901048695493702847051564785470733713501604949532642008
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
  16653661138893830905514367369668657785682542390928768118829285085835525613688
  7829784653676677772817484411427946036602623465817865603835562871586058674625
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  16653661138893830905514367369668657785682542390928768118829285085835525613688
  7829784653676677772817484411427946036602623465817865603835562871586058674625
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  4900894817105709965700254261993087880749194485347325960610755608378489061753
  2955292403320217914847098372560668604733069644464492618684487039447843176355
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  3845032153324284232807242118139816870316017333860068257784795935929581206383
  19785386667520876515117340115484442402372884256620667724297036213600733962592
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
  2537557375977312440627579814647537226735392394517511808870026012672022200088
  13208813711759317157740314271275201984156400836313788462988653180269703216034
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  17924643494163769224862221289000817295051928733228945396031194257539858860742
  21087345225741285204156766307706429932255464274905486220854322627856861782602
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
  10254157560401296032060705818280994877995314907316624662049607888247901133817
  18226854125339978394559560578916850782122255504539700022184007688193850999700
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  3029721583836974724665199422228980798538622305517676568633599080516183343657
  13581767533832268978157026763351869733392862156276224784170828075821080599670
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
  11252501484322363492572404588155419496798824184228279442279286425687651126344
  8741261630864509677348240461287025008738571092067602674765635893114794217935
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  11252501484322363492572404588155419496798824184228279442279286425687651126344
  8741261630864509677348240461287025008738571092067602674765635893114794217935
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  12945467647232099202514519938761797465888825337802708636794297455387541484477
  15620984946569281117188310437921978853947753297872833021680865116989458607611
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  11971932795944629387522825645760587507608130579618617180450125637959294415560
  16789650761186656678508975827078114123916127468978459497703347701691006106089
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
  10508299423663422579066424578978544423346103815511763583038567496404027728148
  5400588978606561186040752411715998993538407074125291812548041806479551120439
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  10508299423663422579066424578978544423346103815511763583038567496404027728148
  5400588978606561186040752411715998993538407074125291812548041806479551120439
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  17567492830276227205403662930404404567753583819639040936874670365329080030901
  6997336790735750927110360857027964079220481443173072435720971996715930649165
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  17567492830276227205403662930404404567753583819639040936874670365329080030901
  6997336790735750927110360857027964079220481443173072435720971996715930649165
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  17591420540863632951529239879994299098436739101271779175822226071387253669917
  16166548373654032735574770133640862795527928318202601405201899289653712122554
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  3603630477889035234427286913294782844565352417701785270256887429948438414133
  1133821267251803015956932692517656756653900876338443788813737445005378527740
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

def bits : List Bool := [true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard06.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard07

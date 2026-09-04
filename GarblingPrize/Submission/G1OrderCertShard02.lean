import GarblingPrize.Submission.G1OrderCertShard01

namespace GarblingPrize.Submission.G1OrderCertShard02

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard01.endpoint

private def doubled0 : Checkpoint := affine
  3934939070796382432193425097365193242318509229884311299874664491542258928763
  16343345859374374804067822266908856874880897146969299254765508607403116559791
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  3934939070796382432193425097365193242318509229884311299874664491542258928763
  16343345859374374804067822266908856874880897146969299254765508607403116559791
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  15446874839726033756427343557133330772668010054409252694599510074773468211934
  4056434794750767376790196866528283661830520930104024741868231705869500338853
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  15446874839726033756427343557133330772668010054409252694599510074773468211934
  4056434794750767376790196866528283661830520930104024741868231705869500338853
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  18498530005613620447805266292518900490392837167128280830122277760936335009346
  2278764658377990638002715555271195845031828550258067716547044244264048552241
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  18498530005613620447805266292518900490392837167128280830122277760936335009346
  2278764658377990638002715555271195845031828550258067716547044244264048552241
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  14485409908134114468611588685609923375190860698636089304974339915798790195449
  11984147568408440413158968508932051378792325707267893854008048825433633646179
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  14485409908134114468611588685609923375190860698636089304974339915798790195449
  11984147568408440413158968508932051378792325707267893854008048825433633646179
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  20974210409631845397137197021869890458660934150421373932920910452349970115799
  7487809312424924236144615835864791370936060318800780046717144727830876567147
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  10612500672922528209356345331907116191732874047196004816619282754926289027894
  4132282271181502384170483473623573846689588663592239436349734488077548021956
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
  10086599256209555440212492305486764848406923551313314138714356144912444505269
  9127364459711433590184928939504442209815676364622526500877629338991084343502
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  10086599256209555440212492305486764848406923551313314138714356144912444505269
  9127364459711433590184928939504442209815676364622526500877629338991084343502
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  995902985336829689367405546423331655250656219021675120260309144786855406077
  11155996231834851675249336575441729573411560745722103405621802504252001952052
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  995902985336829689367405546423331655250656219021675120260309144786855406077
  11155996231834851675249336575441729573411560745722103405621802504252001952052
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  6416256380800533611243537641239537058195845514365564925103711467492685739241
  9163602272124579418480553517711952552090954739355610141102615128507986613291
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  17297172266594459472548354977580339066973231820231853089887216961216959059872
  17173592215776310039956485720783164713492619511238268996662067874897628274892
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
  17614435366972872082653886615142005657806009329100948417836834128496507365772
  8088668111575999571746535140859555569788768989455592181661003183673765571687
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  13878758248644232552143690173677505977542312339944627590716002024008594140305
  21321412416858276014985847679998368253732352344434613518650731558866700532406
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
  20355414071805581417192447119130885206897924333372867041516318746141432200512
  4676644650126396560236804417093242366316695043551582770761126027437155151216
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  20355414071805581417192447119130885206897924333372867041516318746141432200512
  4676644650126396560236804417093242366316695043551582770761126027437155151216
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  2662088660305316746254324658906076193668085945454640836548649438466599447856
  21099496285883050406548501664630227515895362510530387185245746563915295094204
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  2662088660305316746254324658906076193668085945454640836548649438466599447856
  21099496285883050406548501664630227515895362510530387185245746563915295094204
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  2908861348528718977165916813403102906041588222822444287526802165398404476793
  2221871069951193582208366910358106442165674754989716073175409710786316165941
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  2908861348528718977165916813403102906041588222822444287526802165398404476793
  2221871069951193582208366910358106442165674754989716073175409710786316165941
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  19819360609702490454911676965962439528428277510239374415201944624149712773887
  13874360431157902302430157804327735500918478466551297780526264993050291794733
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  7031769875737270683731788576324598243360011952597263068667238521493759072405
  21136510082930209073338494456753878679363483316996363840496530505278327694299
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
  21628205966827488391845413996513678685826272092189943598743734853221872086873
  8094501179591286485086856883254204956259346031841433523414421575935933008804
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  193126289932320754320105442111941419968689807711514333693969052485788348859
  17706509955884089285541685708064138159298183195962137130926119534728671252102
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
  136517285323071407512031904412258997763223053991785466288034835094709831728
  14957223700508142183999718497181285713584014967995395382418956442288375412909
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  136517285323071407512031904412258997763223053991785466288034835094709831728
  14957223700508142183999718497181285713584014967995395382418956442288375412909
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  10628662960967693693880572913608615406016631555108632041600381078119211878126
  6083325847815351556142775753505033992801798885730786294026809677557507516694
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  13605141512385405821840016378846917855432557240099778579158819396630603654389
  15150090738333273451958318054333798002266631928315556501752925134871267599503
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

def bits : List Bool := [false, false, false, false, true, false, false, true, true, false, false, false, true, true, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard01.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard02

import GarblingPrize.Submission.G1OrderCertShard10

namespace GarblingPrize.Submission.G1OrderCertShard11

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard10.endpoint

private def doubled0 : Checkpoint := affine
  9964669762036162055981008113303985189372366177900369132289068207758744796613
  19608396581587263677138267747460590585019300172975409543495036686153222512045
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  6184523783531789651533732318901178582628746474772504188067248407470430531822
  908653456716104556319925737585222017328647365291948025631494649146586508155
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
  19062855406625955686763966384174784131485262282461841878212545730670940245032
  1520919768001208009434119636220844976136739940624176729888248780846122147825
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  19062855406625955686763966384174784131485262282461841878212545730670940245032
  1520919768001208009434119636220844976136739940624176729888248780846122147825
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  21798724413264925101290269419610774353508301314349313025975775274654308062880
  9846500904790401845921676979415929214384284540741922615111877275528639148304
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  21798724413264925101290269419610774353508301314349313025975775274654308062880
  9846500904790401845921676979415929214384284540741922615111877275528639148304
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  2259277425669653183421377471386121937804173436176459414556544961193593748632
  12250747109680885908427225297603447918030587418770217936104520743106474415612
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  2259277425669653183421377471386121937804173436176459414556544961193593748632
  12250747109680885908427225297603447918030587418770217936104520743106474415612
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  20046431388013478091069850391314375635596304689082244343181043459741660090648
  11513630849887357155073474571105738453630700844460869841680123386131750118280
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  20046431388013478091069850391314375635596304689082244343181043459741660090648
  11513630849887357155073474571105738453630700844460869841680123386131750118280
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  7661299725506608657204670166099157014086536583648042594395481304547999444495
  6712186109917463903749980520636529955457159267193027304635799104060007520913
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  19896611939148482443887842405437573079784533538130152775438213625618984545518
  18311491803905568375687562739427270280911293671135944061432029260143384000709
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
  8277996901485017089939745609841775074304875587984428293512084203306296352943
  14061907856935241861637443282485124173193281785210683759926051113241118779621
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  8277996901485017089939745609841775074304875587984428293512084203306296352943
  14061907856935241861637443282485124173193281785210683759926051113241118779621
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  20087775164717552876037126252618580899431919315707435210256271568749436226675
  248979761517119228284022104558593903907297289719007655028908231071723528671
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  20087775164717552876037126252618580899431919315707435210256271568749436226675
  248979761517119228284022104558593903907297289719007655028908231071723528671
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  12271377633771531593369713541036533804128683945460721729717814240124872656980
  16855994528567774340289897425639103870643265890885870073214227314998184354641
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  11462985175087904325128213887149513237242057939934110785636862839402048285251
  17744353368521140466517227416936171262688254872292200877518720044695732500789
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
  16018037855616601634365991648354969731617011153229924852248420667657826931067
  8508401216100137781724431358082477780423153479572889534529112217835165423321
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  16018037855616601634365991648354969731617011153229924852248420667657826931067
  8508401216100137781724431358082477780423153479572889534529112217835165423321
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  16172936256696883437694746844828464443250414407589691532801179718789332450442
  14488462860448084833329189463703741564205653988614223782966904205744190458639
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  16172936256696883437694746844828464443250414407589691532801179718789332450442
  14488462860448084833329189463703741564205653988614223782966904205744190458639
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  15647173246470978628050717208779756933204465868192730192630088231809239425344
  1136562602419987794964951373255419481129069806782476081424137273051919594681
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  15647173246470978628050717208779756933204465868192730192630088231809239425344
  1136562602419987794964951373255419481129069806782476081424137273051919594681
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  9652236257252637555301963647253278904975837845832936593843044608303245521599
  3640613175120727289974835060031883366022475576190208180834494366139429318946
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  11538413422421301521629864178708410217568572401930594360875211781405104178029
  9236565506430904157410859922476365000768830059843784730254448356543101364885
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
  6177722541340385214827203310924961954806534069664983169203456368906317206366
  759435055801091034912388609517175213121263825712407243068456150950529490252
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  6177722541340385214827203310924961954806534069664983169203456368906317206366
  759435055801091034912388609517175213121263825712407243068456150950529490252
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  19108146475461235522919958987597046576385491470450576984839649879234587059305
  2526322960991516515258877296876685024967161986181616642749075187577502163089
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  19515874428522983054554064741733795559279160793276866352736791063801834034632
  20393045440133847668898374466996797835344641540097279880613446972689832250351
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
  6875206319603867640370934454750268477471455106839796313408285506031686136464
  12427656322688635358323745715912915382168314367822478233163923109410236430092
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  6875206319603867640370934454750268477471455106839796313408285506031686136464
  12427656322688635358323745715912915382168314367822478233163923109410236430092
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard10.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard11

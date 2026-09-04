import GarblingPrize.Submission.G1LambdaCertShard07

namespace GarblingPrize.Submission.G1LambdaCertShard08

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard07.endpoint

private def doubled0 : Checkpoint := affine
  3910872560259017168546041053648911373320290850874807337698248957786252137200
  19146158276752022393530228669577693711871909465214021310872759378527513908953
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  3910872560259017168546041053648911373320290850874807337698248957786252137200
  19146158276752022393530228669577693711871909465214021310872759378527513908953
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  19384373253083922805777355252562340281205227560226872952341014853658605175791
  9450911195075392505907251836061871651151382173537389128853300354653398786639
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  19384373253083922805777355252562340281205227560226872952341014853658605175791
  9450911195075392505907251836061871651151382173537389128853300354653398786639
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  16640790471289285568604647946507823197032675111092251000996721032503726247912
  18227828617645276239148886133595125091892351269743040328243540364572894459947
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  16640790471289285568604647946507823197032675111092251000996721032503726247912
  18227828617645276239148886133595125091892351269743040328243540364572894459947
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  2714515088736064308079992177287255903812876675349145362691260225610873067981
  913302764814684497021513929437769541907362563916644163786725232208183048567
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  16055835655785582893453897967768571960441710176228887651098679540177631847370
  10736060771016018096218090388193387991180162541385478240354092853293139053193
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
  1116300683756090378212590991227105136261892411840141873954146403241723337592
  2824167454470514327449847552338297176525435335792951927658453899276287339790
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  1116300683756090378212590991227105136261892411840141873954146403241723337592
  2824167454470514327449847552338297176525435335792951927658453899276287339790
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  16385344907528377792664557841970141117670784556711974670165880444451417320451
  19369324292158740310768096617720961330384391055131798650885652768844886568621
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  11754561900896036756215893848167823888689237378058172700636460981225269898746
  12943514810796658103924565927862448553659445495620832177853389628072838547277
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
  12362194160615505391932701746877599001997362430649106659043550577901823225253
  8002655739738713839887214953595608801301314600935560691160483056023583946369
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  7929618979651887322818105908937172702429605597801543653715489200791540473081
  12823940854110931669180633721811438610930094545177416447999621570913692630910
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
  8608182532318359264691875489144484083282877657714759195140411652441782151469
  20203776881028388440460408126357419661881786550409684529205677298812285562178
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  8608182532318359264691875489144484083282877657714759195140411652441782151469
  20203776881028388440460408126357419661881786550409684529205677298812285562178
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  7970284525352579498663110124606923665312173804563883784520507687108981840781
  3741806530590451217901569301783915809961508333471752051631408240139735674495
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  7970284525352579498663110124606923665312173804563883784520507687108981840781
  3741806530590451217901569301783915809961508333471752051631408240139735674495
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  12340014910502491910860355755074170620500131179951883910858981011365717541799
  12209781106381554784985991293457462980096582551988900281450238945852570431336
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  12340014910502491910860355755074170620500131179951883910858981011365717541799
  12209781106381554784985991293457462980096582551988900281450238945852570431336
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  2726877101346774194214058692648322368123850307905229208012257136202548162491
  21477445944973623094455686020988390121510759935575248880767424964666486293521
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  5054326654614379799724145478627694951679442795986903071622620778315214755753
  18182164181152875849808369495744519454904342886618084505050704539207364251678
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
  773112615083763985906755026852532634040877613512104334394052499675493007681
  15437543924387014711082284380517881315622241871000476320006854633635441147237
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  773112615083763985906755026852532634040877613512104334394052499675493007681
  15437543924387014711082284380517881315622241871000476320006854633635441147237
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  1737757511868069366745740365278423028990512993147294000388524820705880761354
  19609651615480074232620786376355971484797761530658751265793713003916249164021
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  9751477536541646669036457147336692300680811158269791668727238866440313553490
  8792430857088291979913053282715264125657358593229010375320421717914479052940
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
  3028239617123993953026249240340666426259259054727037073465539064606699932901
  13522463316572350715954314976424486763710412723222404874794664551079364587646
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  13367707460510862317112674892224229258156637335139284843083541073078554748194
  9057848037624818610806501105023701696779869729166515275361624895758235218925
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
  17753624344291800063279749801590282375012286864048849514089608964030783673370
  14152913921872427038683226922825482341160700633538873030835004559715777827682
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  9915299436789992444732731955044047256425952273993890345822918854096944405116
  20112550397905145989370264312060912736601736742265408533110072508863723291290
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
  7614351409663298234620226196005552100705606208793544810541855247622625980188
  3505118869224452471882565170367205845656283606199310345072931683876273100345
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  1330614471222332198726259054277284705029364141366964704664372000244811429417
  17811657785119994634087367509270437345005343561181783027767901637194018615610
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

def bits : List Bool := [false, false, false, true, false, true, true, false, false, false, true, false, true, true, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard07.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard08

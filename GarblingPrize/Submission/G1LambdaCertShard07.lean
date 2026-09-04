import GarblingPrize.Submission.G1LambdaCertShard06

namespace GarblingPrize.Submission.G1LambdaCertShard07

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard06.endpoint

private def doubled0 : Checkpoint := affine
  9385772109913402296053336472032975676771885365904531102798179502236768302773
  13866270864444696504997715838612888861804520462901129104986073167799195053914
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  9385772109913402296053336472032975676771885365904531102798179502236768302773
  13866270864444696504997715838612888861804520462901129104986073167799195053914
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  14490161098723797238799219718774447612858278431682805947860874243811416208522
  16154680649968861519057702514728525013975700507285482982604451888738056400428
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  5732696186284150744447044085167421596251565930714986224509136463040363523516
  14271302196868536807858820673246541342152540230859494989417221450416219538421
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
  21012420776515716999465381963305611010135235981025426766450661417836578708308
  11962875558839753718391362524286675140602020910918142755722342475219873784592
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  21012420776515716999465381963305611010135235981025426766450661417836578708308
  11962875558839753718391362524286675140602020910918142755722342475219873784592
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  18179073165347288414560717055214701918781797163320092697694201195889192232468
  15140735356582923914322252801479693734016022010843069067122395885486346719253
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  15036194310843855724023486228829768504227901229089713828991637728921841726696
  19289231452452843492249951828832231218101110614961776833101522818297114300988
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
  16926813976030527008048487660326087930881770043051618170231581962634648656567
  13471988019321205030204711163477421201752624138592721443733843119139270990191
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  16926813976030527008048487660326087930881770043051618170231581962634648656567
  13471988019321205030204711163477421201752624138592721443733843119139270990191
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  9822318254461978477240994149892178751577592530355912433464554463844341352301
  6877970524370160553015166061525151185188138892315679725460029100078953476584
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  18228806504177712588613279278093446880385216690084743427106813266089537498492
  2809518190580575528065742280976841440384947982791637913074377156350511750471
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
  9500407635855602893706578212078994613194274220769798840068869048592880506475
  521080253634829124352896611448335382526523032673796491192205136338647051548
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  9500407635855602893706578212078994613194274220769798840068869048592880506475
  521080253634829124352896611448335382526523032673796491192205136338647051548
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  17656732203748103364525910498882311628355579735097562962604260096088788631418
  4285876928465854982192285150228322260561341821290604783240294012560501232458
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  8479196834510846386964975851008483373044271530422244538289845438934509901068
  5331373642727140041310688229729360560149884874985947584049441353949296588760
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
  1710412567684294529068915843045679889982158233062941508306019949292822531148
  8912727716455914062021389286504574691729962113376424401030691004987932799234
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  1710412567684294529068915843045679889982158233062941508306019949292822531148
  8912727716455914062021389286504574691729962113376424401030691004987932799234
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  12091688230581010476016611466692872012792050065416257024025399905054278080624
  14392414560779708017080630392896036726856331531389120145448058584895037183114
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  17808900151869586520479645735033005684735580898881341256801584381414735871780
  17009922872908470875811562856076608001911232017620054031184728779576116505035
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
  10192252798834492698101341086110984055710345438163777805622629005009189554610
  7621343666803653865606716746138765479578309941370071696896567394460286029457
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  10192252798834492698101341086110984055710345438163777805622629005009189554610
  7621343666803653865606716746138765479578309941370071696896567394460286029457
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  19710246294850010896375953269789381229393266563443859723091682410077176944476
  10018740502710936891860782035279571664025076064780639127393928866011422951990
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  19710246294850010896375953269789381229393266563443859723091682410077176944476
  10018740502710936891860782035279571664025076064780639127393928866011422951990
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  10133077933773316101778283847352875961829455614439588407873211785137768498966
  21565883296885500118600501367183563196175260378827778556631958389198210928608
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  15479289355918097624866138900889100341889811942165354194738711186481406308996
  2422680309989754720464154426140380815563036056984589187555361811566031002438
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
  10402502214788297596971475854564365422996665201740439170426630778273267968462
  2767656303106027372311132232569149587248780991981624891395059659749417661160
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  11637691050585427500647061145626324894192146580608644876487570197677285110718
  4765419563555733795206330630645266422903839810236809075314258172975434703185
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
  15970525593080540498875770185163503898736765735231447023718435401807801129919
  20329063787691054180112238753827949148599830835261788950365450534514010643321
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  18549094774468334611832090890910012867959072697476771706401881452025702749010
  3791915707751358505813269646665326772149035000687021246052871892192602002574
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
  8684335668370451197063505825524224012873942441466458315446603765694693544106
  17935992889585452002468106449655265081541072067143836939883312032098923027322
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  21001209573506477304796637082899817062720484270093654729317503145266794656284
  15814894543123558223818193992339273551990937396384960974449640982498613472276
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

def bits : List Bool := [false, true, false, true, false, true, false, true, false, true, false, false, true, true, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard06.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard07

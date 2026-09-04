import GarblingPrize.Submission.G1LambdaCertShard09

namespace GarblingPrize.Submission.G1LambdaCertShard10

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard09.endpoint

private def doubled0 : Checkpoint := affine
  2642574414918635205270890466452868186325598773823793217722136325339536925076
  1412004610112991239542815978702446389347683399041994876818677185066946337998
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  2642574414918635205270890466452868186325598773823793217722136325339536925076
  1412004610112991239542815978702446389347683399041994876818677185066946337998
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  15872142333448846696445658010404471056994694453357308631025622813944654175617
  2623411046846823418412297937415083940068127078152429691004343874963431319817
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  2485663156182652969949458898053945998042456457871583195310099367904610145013
  18406255890396457997799789286096874182501607012967632092741836917055306184200
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
  5665187896547801153166734120358293116230640002995748224434671762432060958239
  142671862831897922026198163769536194825719752109387486429056736787600707099
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  13764870524324969608154272009006137703917041464825598453054886094048695973621
  9328867241623996320186012823924241321278461606904502016130113644597939053907
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
  10605338418770741383450160150917306501055583635100969127566212836742874144519
  2554531581071369338085356559269148149769631676028590955844417883016466247033
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  3036439267983336786248571761238340530580455322516377002686829668375873147530
  9950832734403457780480612741167368351018299814535511983850820361908773274744
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
  19994730630016011936266850759279525255011850169185408938441084812935850886212
  5215150392877468429641473458636419785970072162205645844349720929351948721671
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  19994730630016011936266850759279525255011850169185408938441084812935850886212
  5215150392877468429641473458636419785970072162205645844349720929351948721671
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  10844650691745995891100172510315024186281677977079054537660909453527605092299
  923602860588661709879254403052725759551744347309949887820464493627447864283
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  10844650691745995891100172510315024186281677977079054537660909453527605092299
  923602860588661709879254403052725759551744347309949887820464493627447864283
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  6830607448660876961974007721981423676923573761378758442227389398186700833894
  3813479323481213380124773926577104691551187548160480561183004204809163037554
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  8607780411225819393597580510071616199912206204833821350515366215443087241025
  5744444906129469461191248240221343226956056569461016613341526255323761346701
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
  20701434024630769491217650928158882984446976809558007844774385812220057607798
  20433030972603978481976691800424990985183137974066944896261449871264875693992
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  10338722089652306325867497722996403448666029369252942897259162293434893102507
  15089178149796493616749835162055198771955164490274219783818488466432316043052
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
  15297955774492434544677732807167597868923701540709900948858844982892613917281
  17101102451328262177789901391562372328140993680364917255975690868486383715873
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  15297955774492434544677732807167597868923701540709900948858844982892613917281
  17101102451328262177789901391562372328140993680364917255975690868486383715873
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  16309187402730512588020499876997653583586050953850501545299362678579726959814
  4402487108051332447841748303554744363855394498019891115125341573917477828265
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  16309187402730512588020499876997653583586050953850501545299362678579726959814
  4402487108051332447841748303554744363855394498019891115125341573917477828265
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  19765141290703080722948247628297171429092712401029655020841538414092305086048
  19942455912952491506662567259936080049569664300901168334038269151772873830015
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  15461041428184286686988090380112459901030368377388994404389372248271069025424
  1907941570925072349012136273434476412743188764526489086798430208238303761189
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
  19404866409286555719657277436755347362210118147573902998505900003275494284923
  21250081189866513836819243885039037767420222900053437062784998290500589982852
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  12143114307912456801739339563329883053815487932632298545581745231598237252184
  20984823577069415560436412071344091412523381747139454110926290506779058319945
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
  18258050509927547541807223147323906820196158055464666391333494492353028733944
  3881946682719523897322887121727521243878948581970960260954459970051632156066
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  20619089397384572578706318730811941636593898738755031469108439991062588431854
  14268788003516488367182176208344608515214368677936713178676065956141888344536
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
  4950572698008780094628374930141789305287222037596799786733198200065988338855
  7751680759801049706623340027192868938410273548047000369055282769990339846972
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  4950572698008780094628374930141789305287222037596799786733198200065988338855
  7751680759801049706623340027192868938410273548047000369055282769990339846972
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  21330570221698413326916586081085048195839562269577245789221329374103662806907
  4614717536668316706776144060227529361440320989155983207407179522357871680097
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  21330570221698413326916586081085048195839562269577245789221329374103662806907
  4614717536668316706776144060227529361440320989155983207407179522357871680097
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  10429042040402306847568986313206601302531096932676587994741782550951430123036
  14430891297093014565746865803467820697209385532465583669551823948447454350339
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  12564650985984166211221450746828095852749880563154193833488123071658161511008
  4998338683750442589689366761620130190434265917341740851709123912006439403460
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

def bits : List Bool := [false, true, true, true, false, false, true, true, false, false, true, true, true, false, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard09.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard10

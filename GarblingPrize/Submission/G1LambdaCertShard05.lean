import GarblingPrize.Submission.G1LambdaCertShard04

namespace GarblingPrize.Submission.G1LambdaCertShard05

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard04.endpoint

private def doubled0 : Checkpoint := affine
  4723046556981589546099482530148795815808245810881060702494557710603252962984
  20257380268003698513187672355461776134352026228070887708274736631365551336896
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  15152329288918179253596840982597908138968603059580968961420823274771559914597
  21873675889500409532010805395936274401399137477813956132192702547833946495568
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
  21380511216711480796180218136944665396987084554933681927795330310065235702110
  3402494515851002057012880017838965194792714828772808690977922501605977237571
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  21380511216711480796180218136944665396987084554933681927795330310065235702110
  3402494515851002057012880017838965194792714828772808690977922501605977237571
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  1141993906729403159096480676066018092970073044910735358913191521122205118158
  3757527491335292031596677421258720169081381004673820748893781438553326318946
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  1141993906729403159096480676066018092970073044910735358913191521122205118158
  3757527491335292031596677421258720169081381004673820748893781438553326318946
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  10417989673451831225491230023561131249527745312980474773644212482191241362421
  19096276491365165896571321610521201167961534333219609907422633724730216169649
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  10417989673451831225491230023561131249527745312980474773644212482191241362421
  19096276491365165896571321610521201167961534333219609907422633724730216169649
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  3600708436149995674957668219906453622573852764180446903481488288728051042167
  17410469421809130251262622310044068554452554991666412627810294583343671423195
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  3600708436149995674957668219906453622573852764180446903481488288728051042167
  17410469421809130251262622310044068554452554991666412627810294583343671423195
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  19717144478763369839323189935380405068931292217104264495067598973481792434057
  16437970423534133473225185583977345046601215687123389876673353438602009396036
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  19717144478763369839323189935380405068931292217104264495067598973481792434057
  16437970423534133473225185583977345046601215687123389876673353438602009396036
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  181067255155508233483224990246238340443235177081181800904079728244171034025
  13820517192351772867063236488032300232389511241198508092432735198164974637473
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  19233159244292252015538258018310990685913210895585197987105492504654611104528
  5351907108429987520053514632216209755573603872013103299467749315959847134274
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
  2208799736273766936171203157848509233592669262449846789261627498626808830174
  12074004876568459113937879496350506950467748210969035720695409095917937453036
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  2208799736273766936171203157848509233592669262449846789261627498626808830174
  12074004876568459113937879496350506950467748210969035720695409095917937453036
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  1382801299481074585098385194095722226589135425442272589194428759385137252654
  15315774237232041516474492813505959401652206538592274930880917221491699128252
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  1382801299481074585098385194095722226589135425442272589194428759385137252654
  15315774237232041516474492813505959401652206538592274930880917221491699128252
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  18983791190306678768531379814158670134345290542355073271942836581941066221234
  2805237974271078791661988553581854581775324011465908930036795480022585130787
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  18983791190306678768531379814158670134345290542355073271942836581941066221234
  2805237974271078791661988553581854581775324011465908930036795480022585130787
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  1778332827117714630619416366624627668014413815547073038190797784644267688567
  13015815700559155988353613830065735034802136884377735321536362013885298122550
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  1778332827117714630619416366624627668014413815547073038190797784644267688567
  13015815700559155988353613830065735034802136884377735321536362013885298122550
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  9040586220791761059434101779763497330055956474910432525361609368465379137267
  11144382949134159984033519927573967581319437697065661982950731120729523229718
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  18718004607159574282746872974291902167571937524360321766995150569874978839663
  19127240576820622598607038437311322852270901338469193877503450746051176837930
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
  18939786575280343646476054954863595954718725855293411167686078279835274336824
  9445616480219672457213262335789372348921610596239959344584072574783112338787
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  18939786575280343646476054954863595954718725855293411167686078279835274336824
  9445616480219672457213262335789372348921610596239959344584072574783112338787
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  898756670413350539448717675747508359050458901186529155477673611860505066686
  14117933079387655355121988596841546135237831206361408032651114361925210271762
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  898756670413350539448717675747508359050458901186529155477673611860505066686
  14117933079387655355121988596841546135237831206361408032651114361925210271762
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  8477058728243289436425908832235702735997496738902032104771054428134330132282
  6712551849010183035696411953949824903155315774318704303177961183884925006649
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  8477058728243289436425908832235702735997496738902032104771054428134330132282
  6712551849010183035696411953949824903155315774318704303177961183884925006649
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  3532671407472738398700338014817175516019491586682461252060398602050943469745
  21416717943713810329315666237603082333154005028082732578802521956770252672684
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  13777714597255927564186656511950746178524632344882949977517943005165958433667
  17821818089823484653471002646802526888709690418949562630743121795711905858730
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

def bits : List Bool := [true, false, false, false, false, false, true, false, false, false, false, true, false, false, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard04.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard05

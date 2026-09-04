import GarblingPrize.Submission.G1LambdaCertShard00

namespace GarblingPrize.Submission.G1LambdaCertShard01

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard00.endpoint

private def doubled0 : Checkpoint := affine
  2324007286796020416933240483849801967916688413570459968004367033925849979611
  5976045068870844304193145452018251034370582950765383129299935657930104010847
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  12454468717366271446631369904263993043396360722475075918719522388945356116721
  13728237804020489550243203215599570826513858441882897487062852219801432395395
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
  16382031135835613577611294774148405106590364630299106303717802284410358845944
  908503492070831877424806423370034096412364342567287148950095267450972262806
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  16382031135835613577611294774148405106590364630299106303717802284410358845944
  908503492070831877424806423370034096412364342567287148950095267450972262806
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  8928777785115589812489276182862006931745846450800144971607237976252105499675
  9159843862932710800551594608833346957892473209481929307274607962477668634840
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  7650473344083135269840749172357922729030066507599486322094754498908182977579
  9262314838644059307074093897517221343182144209564435153314064208161928693742
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
  9198346463671804774268062040547602712729145110024148442134604062264532386525
  5938737600964437687455955086164490284398512828540906654314857097692434798394
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  9198346463671804774268062040547602712729145110024148442134604062264532386525
  5938737600964437687455955086164490284398512828540906654314857097692434798394
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  9796421642389335796283702474058094545847428448985207441651898555900933702435
  16278072335213352945231542085322648843973355890136686948804750930041516746909
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  17735500230815273424633659534818590753432968871074832986916445657168088357454
  14910563709271002675296283661265546399942452416690377062284978174465305987679
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
  7653037215970228932814066909489667192957021726429119285458751689108314214121
  8102275817625561007349907673427471887984706552339172828398352338635311892862
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  2573846401810188668353320106786475330135464810770684148066719655835949066712
  5292918470385668796506736683786115500106426000233602182410390561059131139900
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
  16081312231004622725423599665003420318974869773116476133665421366381101928876
  15277583305294004973313755668989712968862357183316340961459253090486967333540
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  9216958764909028569098629591000485292143887388117447391660442188197223012985
  19287618036020725888953529516157775594986514527540084060870693743651198479413
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
  11500333644186093537030514542444441053463767222107870375569523720402593025634
  7531865812507682344119672821415108230981380113313272517442186163377343987869
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  1705754876580558959513309425595396656205971874614251875151367402030828572845
  7139081808467055326108069346979111919744581133788254235504583866428856639416
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
  3544914289664871957800144327797642155976180180267670857926750669217811705626
  2326952215841988902025403688600195802195965544688875680610287212243855357798
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  3544914289664871957800144327797642155976180180267670857926750669217811705626
  2326952215841988902025403688600195802195965544688875680610287212243855357798
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  16968213048221114074897286320040670606114293146283714042284255626009217570340
  13736973705805870204226002122276254379961276484907681671174024305628315029948
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  16968213048221114074897286320040670606114293146283714042284255626009217570340
  13736973705805870204226002122276254379961276484907681671174024305628315029948
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  11411108199378945108922910041421820706094240375647128578474611978593632837609
  4723300621764593663892667067880142828662789677588166250651532004836130788565
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  2940767255398905249936454558992825535320312899233474424432874379488063580920
  571212351177164277551100311321779907199802749943643591680963698167142330027
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
  12747394560314754881980595775495387501742504226155854327473476133802206805846
  1601358671820132910855614190759070921351203865985889768914536548584274543006
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  6911032083947884977354278094880550083339312043854094298898209500352204890774
  812890033437155205935760195326979395921015029699360624820390601624870349352
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
  6637450874503244905514380292639619777813646872631934960498894322615496356124
  2850097520550395741864573023660770766378059010416947112718505048119608421961
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  11679736883358808011803303725270632974309593018439776919266898175920146106901
  3260201558020492578311000792631863918277944235251532473801698734050323816119
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
  5173810630690309595414307397508816588175800177684215362665798037871078898666
  1059026994254735267681076105612594526683654616704702096631788469710767326728
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  5173810630690309595414307397508816588175800177684215362665798037871078898666
  1059026994254735267681076105612594526683654616704702096631788469710767326728
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  5042766484261856347552645527025622545167068263217648419652441535907213095207
  107737762738442857992255561221623310496761397200432003456929703039460449609
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  16986169712652836173160654998437233791047365908384782673913417648422125674077
  12529134645774039858596248875731787347279971929018842813193639120882585540152
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
  6699200842860566358766929778164965218279868075686908794039930739534765699100
  10889028805246508956838665746470818991068352550243334580732929304990070815084
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  6699200842860566358766929778164965218279868075686908794039930739534765699100
  10889028805246508956838665746470818991068352550243334580732929304990070815084
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [true, false, true, false, true, true, true, true, false, false, true, true, true, false, true, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard00.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard01

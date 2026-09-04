import GarblingPrize.Submission.G1OrderCertShard08

namespace GarblingPrize.Submission.G1OrderCertShard09

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard08.endpoint

private def doubled0 : Checkpoint := affine
  21405290792212997430298005460624182549531014924734606649733456824741988748995
  1767445624164218414518647992301216768692272353015421871681672695583341791239
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  21405290792212997430298005460624182549531014924734606649733456824741988748995
  1767445624164218414518647992301216768692272353015421871681672695583341791239
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  15449110438772617306992713829125841314396774718024396846297361940616651339974
  17415020080181896177295646031104718749113964326846431803787607609017950330979
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  109032770277310434369095527577783572076322424453051686374298408805925155106
  5873136960285028691032000387583362458137215563197250553822343637559095841949
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
  10758883875179080469277172531808454574305192502854336017729047846500037164691
  8514718829498062141286675624813568981439111947873511706894141608736998760500
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  10758883875179080469277172531808454574305192502854336017729047846500037164691
  8514718829498062141286675624813568981439111947873511706894141608736998760500
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  4886944094290702076128195995370121668452493791355185556878102632201039323065
  17208146862601279267270325599377172374569967730093172065273242467267867490292
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  4886944094290702076128195995370121668452493791355185556878102632201039323065
  17208146862601279267270325599377172374569967730093172065273242467267867490292
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  14874840327612071530121265393800973962726705141162595407565968898455139011819
  11520816238341126062565997519224329573024167765187888434427919686943877902541
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  14874840327612071530121265393800973962726705141162595407565968898455139011819
  11520816238341126062565997519224329573024167765187888434427919686943877902541
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  10495608280940898262277026952206660467285746136008063995615318374807630670151
  13193574317299680522173043675638176747702266821175398169486633270317215060377
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  10495608280940898262277026952206660467285746136008063995615318374807630670151
  13193574317299680522173043675638176747702266821175398169486633270317215060377
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  11728056056855246466998297716091205100410371274512723731732624727989653351483
  21850256100410149978424974753774002668013717089539841826017641787455276372410
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  6342520854757945137981658014715920328421760950937750473614922275343332490805
  9731540625530802787274712341376102251627969455745783143774279425622582431030
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
  3004675187084814748319000935272876997241901596213585405821104377638911411226
  4991216968956488627606213595588924863693308850281272032140710231747572212554
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  3004675187084814748319000935272876997241901596213585405821104377638911411226
  4991216968956488627606213595588924863693308850281272032140710231747572212554
  (by decide)

private theorem leaf7 :
    pointStep generatorPoint (semantic checkpoint6) false = semantic checkpoint7 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert7.symm

private def doubled8 : Checkpoint := affine
  12106950689566239596379868812476692429934161758527370799480860763376242252911
  19205393995550589837805234494552331329594248132995471527847434196342930639644
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  12106950689566239596379868812476692429934161758527370799480860763376242252911
  19205393995550589837805234494552331329594248132995471527847434196342930639644
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  7933775948330777530654453008003092064887026866328419247294983121991466732994
  6769906829722237563436638621626221672851992636610976664517462587512542276316
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  2100063285777214620204791448039825851478047297733750910712774447409178959981
  5886114556721865719586736704587101052773153698265480485441546218866259883089
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
  15082446319251765684290358461088486466400943517266885993519013772869448168307
  21325442466994631528884491454972686237900645040408270319748150647172544840578
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  15082446319251765684290358461088486466400943517266885993519013772869448168307
  21325442466994631528884491454972686237900645040408270319748150647172544840578
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  16565360196142809982535769185565527777103056965825779242142840356149865699328
  187207861273631406735223252499021291934754582699124432439437057542859657060
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  16565360196142809982535769185565527777103056965825779242142840356149865699328
  187207861273631406735223252499021291934754582699124432439437057542859657060
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  20642738619147762191504231116527318780100414435563706358150530576542529026194
  18068664814224821973701675035183021270638222482938921090596637644987212270776
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  20642738619147762191504231116527318780100414435563706358150530576542529026194
  18068664814224821973701675035183021270638222482938921090596637644987212270776
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  3309992908739345569172821819568162124294625033687466712740429416401924734023
  17447445508819069347843874317197435562359108729025187418461504750400756454101
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  3309992908739345569172821819568162124294625033687466712740429416401924734023
  17447445508819069347843874317197435562359108729025187418461504750400756454101
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  4549863755234397161862717727455449429860988020801961837224166864870723050635
  15933648606083786139296763984641097802553241303531197887363358252639644328412
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  5591987424000013667003135916019813870053293418994776286278252383218035621906
  13121539462906976249487984727467040142425803549966978652165814058167667647363
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
  11610907442008502568016484795017432321903673452667540378962882738956960521758
  9527559969793914210219513061496606118820172521632890885615769198758455062515
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  8663849983990281072961188122557726857082858490423436962638535445749385685049
  7152904842866851905062563258824873394010339604105463920126516370385015514599
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

def bits : List Bool := [false, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard08.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard09

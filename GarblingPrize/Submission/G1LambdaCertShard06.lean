import GarblingPrize.Submission.G1LambdaCertShard05

namespace GarblingPrize.Submission.G1LambdaCertShard06

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1LambdaCertShard05.endpoint

private def doubled0 : Checkpoint := affine
  13528740268898938125055456726768181910925954866242780852871509897634181242888
  6743658015334627383311079846709169434943389093914934273663766200372313356588
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  13528740268898938125055456726768181910925954866242780852871509897634181242888
  6743658015334627383311079846709169434943389093914934273663766200372313356588
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  6795618881065996515404684476615720630451572253849461793651553110556597372034
  21831624237920310367873310055403410943669038864123097672300659579375577311258
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  6795618881065996515404684476615720630451572253849461793651553110556597372034
  21831624237920310367873310055403410943669038864123097672300659579375577311258
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  18561121785947055675838267008270641027353811265487584732791821387657189776536
  19107498021694969316784690502387059108754912420535999080799241957717929701166
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  18561121785947055675838267008270641027353811265487584732791821387657189776536
  19107498021694969316784690502387059108754912420535999080799241957717929701166
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  6292231246419843215544320562057201502946168205434516352044372495385139730184
  3343088362745413813618499715437259944407921590720084462004486457643418683932
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  4687250954190489083503732328979816986621280169541025407812490386530567558801
  6509359930605288816678567058722576093962973021173582753735065476365466591188
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
  11949853701011136231201844812563062797811634639015856616668347202002058926071
  885417876013402035420341164582591808672173762902046125579818941288619398887
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  20679747156600140389260964560472283208655639934571001546536351605086652675941
  13623178224986575394219411414661700828115615744893786785140164487391153986923
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
  8521982988607524694604895624651757438979946501865123220136433083142590506041
  7740196237795381291535157550350036243814746076227777774031888320376025143112
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  8521982988607524694604895624651757438979946501865123220136433083142590506041
  7740196237795381291535157550350036243814746076227777774031888320376025143112
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  9440826727265710301205676499339273475088612866995269829073147712858226404212
  8854326598006048131994684034033828074984498136421661095735994402105709363376
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  12498609791283497738393885214643023330874823596896921090819680170824033376131
  4091581611006371334539758236396837893217893287476171808778665501977625774182
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
  5549600405406411308157901786962079845210114124120183533592699754985167794853
  513661474757590781385570680895631611558839027085427780029428939960870275552
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  1591121014992633233747515099595504545826207895643781573775974691673369459006
  8651066287251057095853654122380980374537679701210222895264761690231777678607
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
  20859446066243916501538113906684239441150203539928062859559283680086030626432
  21616802521084008846275841691677342052426684466091210819405992706227718094687
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  20859446066243916501538113906684239441150203539928062859559283680086030626432
  21616802521084008846275841691677342052426684466091210819405992706227718094687
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  15106731568644272798668193082619117610092629669587850693908537538078457335999
  20268708583553308917311472493295403587761948118610191252978617986795613626933
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  15106731568644272798668193082619117610092629669587850693908537538078457335999
  20268708583553308917311472493295403587761948118610191252978617986795613626933
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  15207229422044014045141572016312898298616239785453953490845289871333874708878
  15124257202471001069638729394580675172742569970845505708969232130830892232273
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  15207229422044014045141572016312898298616239785453953490845289871333874708878
  15124257202471001069638729394580675172742569970845505708969232130830892232273
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  10360955750576882837772255016918350205890951127834962737467052681308460683624
  6748793558197774425018024050425227458331322745939953711146686096771448315312
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  11925208487377065022198089779920049925843004611183367669475217517851803403471
  4322596036266593875889455521652213479159942067292863455605838678239216819333
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
  18054301444804959733884133255890844760211171975344245242126470262807527805056
  14057743243371651234706813878529613467610556130065954070399991916294180716127
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  9488231359470482533750712473926897259290455722429600072918533825917193921929
  18763269461919787611755942865021651353361055030506638846231922945522212889815
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
  10756220838577558283346947573913973819037439153988549950322071955416257550313
  18575774382048517119256918955987069240709472575220849892072674084292677308564
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  10756220838577558283346947573913973819037439153988549950322071955416257550313
  18575774382048517119256918955987069240709472575220849892072674084292677308564
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  19855827546518557698692420967993318246192335725293353169704000084329301875247
  5054152883304586190919513787748705621914188263395099916360453278194029841429
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  2647240636458181540526476107315571481992500321965195528070099868874024253462
  3199291146417524722497134125289817406901146233851017641522406830393960623715
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
  18130004429642176132462780338051918480233283904149060337009341179095908392439
  18597904930469359724957374406319513080303762900315277202073755327370145692176
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  19058999614576148404205069622264983328539007163748957571357594098142464444317
  4655816317266964614906935596626408191691389553505394016601726422546270705518
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

def bits : List Bool := [false, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1LambdaCertShard05.endpoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard06

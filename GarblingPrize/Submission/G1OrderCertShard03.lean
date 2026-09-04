import GarblingPrize.Submission.G1OrderCertShard02

namespace GarblingPrize.Submission.G1OrderCertShard03

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard02.endpoint

private def doubled0 : Checkpoint := affine
  8560057989756786740008072204404258349477423149178036706037443832879713770486
  2366549464160866045495223399471326929509180175149969006307234524735175224061
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  8560057989756786740008072204404258349477423149178036706037443832879713770486
  2366549464160866045495223399471326929509180175149969006307234524735175224061
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  10293409142513447465991257269904923649917636103056320548955998370617747387275
  15916873144762663633988000278374405662045683958388191567052502855574366021275
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  10293409142513447465991257269904923649917636103056320548955998370617747387275
  15916873144762663633988000278374405662045683958388191567052502855574366021275
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  5241168360551363709918533177711193198838479908416093098130866097475009021870
  4747079055219228743433281041684535784581582335113709576587589290791997981353
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  5241168360551363709918533177711193198838479908416093098130866097475009021870
  4747079055219228743433281041684535784581582335113709576587589290791997981353
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  19362478818188724088229418171329043110077156734640015625382175130474248359041
  4684458110783323986718258061627789362479515367605477556882564891503012922314
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  19362478818188724088229418171329043110077156734640015625382175130474248359041
  4684458110783323986718258061627789362479515367605477556882564891503012922314
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  17884559236615405798622090936999203342667140361146383450381340800745864262470
  19960915343368855065046994977314310616832253749603734112448294046650605636478
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  17884559236615405798622090936999203342667140361146383450381340800745864262470
  19960915343368855065046994977314310616832253749603734112448294046650605636478
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  8778054418058491089808947508935519775588683908284511353971940992707976293545
  16529287506185029124430727043948034786827391777477113399325525637531946604843
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  8778054418058491089808947508935519775588683908284511353971940992707976293545
  16529287506185029124430727043948034786827391777477113399325525637531946604843
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  18956855974700164532360658218753261946341152280938109124175943467300703088116
  20637993613233397049521747246128155213852477051887560274153324288316180643273
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  18956855974700164532360658218753261946341152280938109124175943467300703088116
  20637993613233397049521747246128155213852477051887560274153324288316180643273
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  7046670046167359505886174628031184935877533943450555387507862408795436784696
  1529833479659385250666510326716540734330695175881144589878127386409962298987
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  331297811422939822929681101853770930553685204068002276417947182591883936456
  8639951647303408664247897211508684191734058311446622503160185422293378999038
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
  19145049649995184593203097236786514291321208394674448737409054832277511231655
  14744187429039630105864187663915364473030390007549637031818354435746444036412
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  19145049649995184593203097236786514291321208394674448737409054832277511231655
  14744187429039630105864187663915364473030390007549637031818354435746444036412
  (by decide)

private theorem leaf8 :
    pointStep generatorPoint (semantic checkpoint7) false = semantic checkpoint8 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert8.symm

private def doubled9 : Checkpoint := affine
  10965460073278865867002527184978974145631737410766771548607921489899855535021
  15111813330574796988278204853704837411400986670048270630264796869500463663993
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  17878854673345847465727726195155983562091405189322092924060055551078350650586
  6004722894333629572881026864115495307826536996446080752039571849602381202774
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
  509314473603146770326372068418869153277576992050554285000803539298457619561
  7940164885164731043992526880504955703332967991775375540282157501198672904041
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  509314473603146770326372068418869153277576992050554285000803539298457619561
  7940164885164731043992526880504955703332967991775375540282157501198672904041
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  17240525282326424502339831661406395668678584525593446164610324781952281964353
  11933643784695636961149078866703561822202605214669005315717252486665265710489
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  17240525282326424502339831661406395668678584525593446164610324781952281964353
  11933643784695636961149078866703561822202605214669005315717252486665265710489
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  17563640520773621314171652199362578806198404952176362946783083390726893694102
  18062858003001470974893200353279361772092553945791637047937579170164932105692
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  2232178316091693770795824193625487635437425022850925879029670300389463837942
  18006054056575493741667342094556994412558285186807712924794823503865622282422
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
  3644758067896688531902034862650257799893703539154563289798692930516608191917
  3352369223349487144669147685763412890233886572811269057404549684313362388399
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  3185014452148977754432709679225233470997630757253839668756383029530380820897
  8820781816152274402417021472603542960782809289552856479948720016381875464351
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
  2673927151757028324298031680995680545179815567514678800444256663905989233955
  19774377806469312507759164295526487953847112408526458932594312968424507567377
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  2673927151757028324298031680995680545179815567514678800444256663905989233955
  19774377806469312507759164295526487953847112408526458932594312968424507567377
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  143305081437531267837810118554704713691580244108306932058352425425677333999
  1069729831104410834682234077392058278204897052435680836219965217157233989207
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  2364005032682194565151257719610607387721623920577269205690647072366275715835
  8926491462960084058518014667975690946884669474130641715646426934469004750847
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

def bits : List Bool := [false, false, false, false, false, false, false, true, false, true, false, false, true, true, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard02.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard03

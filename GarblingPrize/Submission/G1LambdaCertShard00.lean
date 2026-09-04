import GarblingPrize.Submission.G1GeneratorCertificateBase

namespace GarblingPrize.Submission.G1LambdaCertShard00

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := generator

private def doubled0 : Checkpoint := affine
  1368015179489954701390400359078579693043519447331113978918064868415326638035
  9918110051302171585080402603319702774565515993150576347155970296011118125764
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  1368015179489954701390400359078579693043519447331113978918064868415326638035
  9918110051302171585080402603319702774565515993150576347155970296011118125764
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (generatorPoint) false = semantic checkpoint0 := by
  change pointStep generatorPoint (semantic start) false = semantic checkpoint0
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  3010198690406615200373504922352659861758983907867017329644089018310584441462
  4027184618003122424972590350825261965929648733675738730716654005365300998076
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  10744596414106452074759370245733544594153395043370666422502510773307029471145
  848677436511517736191562425154572367705380862894644942948681172815252343932
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
  4444740815889402603535294170722302758225367627362056425101568584910268024244
  10537263096529483164618820017164668921386457028564663708352735080900270541420
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  19033251874843656108471242320417533909414939332036131356573128480367742634479
  20792135454608030201903199625673964159744755218442260092768620403349374102584
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
  15727213640762128376977790067421582934261473041285176203873887513123693207669
  19144605879150273414601776380457513460094228635793066771119021730299648624873
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  15727213640762128376977790067421582934261473041285176203873887513123693207669
  19144605879150273414601776380457513460094228635793066771119021730299648624873
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  5876881561172177367761102554364316594534030070605210311973953824975119560761
  18140326442304782788324966183794984189967425964511625408211449718334364063811
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  5876881561172177367761102554364316594534030070605210311973953824975119560761
  18140326442304782788324966183794984189967425964511625408211449718334364063811
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  9185496653949827395542415852257310150255649249011849327295920325446660237101
  12548175832346631452607385519956685961219907043494535339456541319739689218477
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  10652570957973409579623191463251851675899922606368748990663442515835679121713
  5441723394640545945982417439291579383664705007242237338345721073927502597580
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
  13058054820872484446482705680895825229848765878538036634541145702916948409317
  13307865924901068251957911404220415995548975094597054311740487760190290250898
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  14896727548757637941059595865114876291804060360571361264916712750548344935894
  6659885779340888267702207498043808774879479214248197370795979802746687671952
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
  13848607647740021456780998291778238585518832142687461723089933979579038318275
  9038129316682296550715484044855310175027614987208414425491564196031374259247
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  9011061106011612137156415923039997762188944564301687442117632848964921692887
  14721547239894109786944831617464025779934635959174770517994064506818933294280
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
  326908575164722639011694666315300123056332177378591649084372470630615276305
  9560537727983610830746442249080411316244220880860341098456973114592001438274
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  1348501067026339436270112815749514437467210112392125778316784869073475785646
  10505867816134810380799117821540686299058523791552723952628244765578725946327
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
  309154338039473785933038441698559634177030649353518918738548077091945779866
  19774165077395559981561490102573592415857022969955769896612766896728066432461
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  309154338039473785933038441698559634177030649353518918738548077091945779866
  19774165077395559981561490102573592415857022969955769896612766896728066432461
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  10228100521038970481904586984105098227610080284571086263720544150361906480456
  17390088122062924203452196198007353682715463047191946212725654290808358533580
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  10228100521038970481904586984105098227610080284571086263720544150361906480456
  17390088122062924203452196198007353682715463047191946212725654290808358533580
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  6330403237407465760586903981406666457968317785236896477653761860163896539269
  3346414382485296948676880071447990860164731888732836649750094894105349480566
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  6330403237407465760586903981406666457968317785236896477653761860163896539269
  3346414382485296948676880071447990860164731888732836649750094894105349480566
  (by decide)

private theorem leaf11 :
    pointStep generatorPoint (semantic checkpoint10) false = semantic checkpoint11 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert11.symm

private def doubled12 : Checkpoint := affine
  526644729342898920920439369386991783811927169749055736541154806790389969716
  15758972826469939910565042143964999879599202353187871488721090106708179054451
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  21295470749143438464919141896268582265803241545466783822382424119208290814490
  16515149784714707372010326973056894061129642750141053674497960568734490006398
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
  19424960854304149063525180903812466871652167157458364307907327703638207689644
  17623534761659137607457971104358768040388474465222792330835984557844078966359
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  19424960854304149063525180903812466871652167157458364307907327703638207689644
  17623534761659137607457971104358768040388474465222792330835984557844078966359
  (by decide)

private theorem leaf13 :
    pointStep generatorPoint (semantic checkpoint12) false = semantic checkpoint13 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert13.symm

private def doubled14 : Checkpoint := affine
  13314717169673784697793401870131136229363765547789164560657335989753666087420
  21545976270015635042315901983421744127250552075042423408246508865543536804923
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  13314717169673784697793401870131136229363765547789164560657335989753666087420
  21545976270015635042315901983421744127250552075042423408246508865543536804923
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  12784141069574256082645307395433998701561248031036140719803200670681006937807
  16896746038365445099182797923442551589143339201558102733760991362996985665896
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  16391562646529349211364957856371960250527202147260117479147304313335666916128
  4170631601080174032285204482931215116862177160905320049478675961664194382123
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

def bits : List Bool := [false, true, true, false, false, true, true, true, true, false, false, false, true, false, false, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (generatorPoint) =
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

end GarblingPrize.Submission.G1LambdaCertShard00

import GarblingPrize.Submission.G1OrderCertShard07

namespace GarblingPrize.Submission.G1OrderCertShard08

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard07.endpoint

private def doubled0 : Checkpoint := affine
  4549124063693787434095416447863135269666332657263000278173407289362922335978
  6178280474869751674456220415555595484128997316722667582661087898583954994789
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  4549124063693787434095416447863135269666332657263000278173407289362922335978
  6178280474869751674456220415555595484128997316722667582661087898583954994789
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  5564988105374734635013368471384295367483785380725267667245240216445874756994
  6045831907799805328122605723168217901519582285195122571692638506061068911800
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  1295027477021691094180753217960123237694537181234153074806484814350279375216
  2701303531369591672486450921906658559790545270114913222101240556248577298157
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
  15027942402529782568632889353775045515315670046580484147886479901678048703371
  6580070877408906270572961211924813912525200278467800419233516819331665104780
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  15027942402529782568632889353775045515315670046580484147886479901678048703371
  6580070877408906270572961211924813912525200278467800419233516819331665104780
  (by decide)

private theorem leaf2 :
    pointStep generatorPoint (semantic checkpoint1) false = semantic checkpoint2 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert2.symm

private def doubled3 : Checkpoint := affine
  8837119469707728298961766874265054829349092530837316584363734517936190465468
  20069943639304637962277282554429933360054041667388331115259497058323311826101
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  8837119469707728298961766874265054829349092530837316584363734517936190465468
  20069943639304637962277282554429933360054041667388331115259497058323311826101
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  19343034460750076307861627580827215159559349534161662730856858391414579216395
  14609722115324168502202126467665770483870049258089916682315316665196256917511
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  19343034460750076307861627580827215159559349534161662730856858391414579216395
  14609722115324168502202126467665770483870049258089916682315316665196256917511
  (by decide)

private theorem leaf4 :
    pointStep generatorPoint (semantic checkpoint3) false = semantic checkpoint4 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert4.symm

private def doubled5 : Checkpoint := affine
  21475786804735049616566336254104453216805005612333877988037410913027803452688
  14206021143104608142327453259129208728620398937862942876543760401041787428491
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  21475786804735049616566336254104453216805005612333877988037410913027803452688
  14206021143104608142327453259129208728620398937862942876543760401041787428491
  (by decide)

private theorem leaf5 :
    pointStep generatorPoint (semantic checkpoint4) false = semantic checkpoint5 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert5.symm

private def doubled6 : Checkpoint := affine
  2382628486486340066191841409554489281524436764062155021725876074152812978286
  16117006675402933144900260999018270445893456990212432140189482809045417672050
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  2382628486486340066191841409554489281524436764062155021725876074152812978286
  16117006675402933144900260999018270445893456990212432140189482809045417672050
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  4093911248842716061106504638179393563018338899808805926502797126936851784193
  13417968900313135361263936538778852389964832425181642138884139309806218781012
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  14256391995064382580498744972641408421124747322262086995504805599273375046292
  9054914324179645825919208504222925738797890053393118130861733781011555909469
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
  4245164106696156116028344890560413236420207408834634121226437316234190273990
  467148310397989214719840457171283542527196201696573074994307613771914642209
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  6863425965358762294313086122824714165450312807955740770040909403985112766287
  21503328827618788655565892248491580494119568366964087764154526247921019885809
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
  20376696030342732462302356012710162229333202844114732833048087763313737689005
  6596802462940834959655493225165093512531955092363297514792871955364901310617
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  20376696030342732462302356012710162229333202844114732833048087763313737689005
  6596802462940834959655493225165093512531955092363297514792871955364901310617
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  6919562401312476741739313102052221541015107014393702897385664195646309413552
  6543667731494954938996946860145831927133466969661494870560635112889142536450
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  6919562401312476741739313102052221541015107014393702897385664195646309413552
  6543667731494954938996946860145831927133466969661494870560635112889142536450
  (by decide)

private theorem leaf10 :
    pointStep generatorPoint (semantic checkpoint9) false = semantic checkpoint10 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert10.symm

private def doubled11 : Checkpoint := affine
  4141780253915895059128634975989388038379218313761174502189889095426930799579
  12213552687398619224028171387181680232964219079045229151613804902314234903272
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  4241613150483592559695264166824740633357798262261352395233906749172452654666
  14794900129131471670891271836560501426406424131946922839013849543162876712616
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
  20535350727304335372664325349686351302373511276041911773447285420709225156406
  10879869873883070997512062045582703023103073639391395996778018853504298831309
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  15463337706023986323816709328777142214229221395003104918753822271436926276711
  20110929424156263902114738466201982365337265460620761822379823590745040965081
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
  19425291475635231022254292427774991360255475058853907861942984842801239074919
  10159075621912628832936987077431085359349924091553402605020366211790387009688
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  19820177663599500171850442009192266402992238668564531010972922283016785630867
  21141458608584523758344317217949215591274461232187944314334659904085068743494
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
  4648104983461056544931323260802247320556050879306381036551009878377369384705
  7808264911108649442428029780487580150214146932069352089150676301074914396812
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  18178491387047775447722695407947375196469937951883697237495378292318179220646
  14917702462971955969192158689666382483242921248635433496721333126040531420307
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
  12793534927769648419163175226692562494874391244782125477152905083544779696399
  7612924054878804217340025317062877885171935555689477178911341868399634688563
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  6701842225964844393695561116602648939007771380453183314652523879508073076152
  11111167377330791156814500984258499866092125673183311870375799632149494798770
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

def bits : List Bool := [false, true, false, false, false, false, false, true, true, false, false, true, true, true, true, true]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard07.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard08

import GarblingPrize.Submission.G1OrderCertShard04

namespace GarblingPrize.Submission.G1OrderCertShard05

open G1CertificateBase
open G1GeneratorCertificateBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

noncomputable section

private abbrev start : Checkpoint := G1OrderCertShard04.endpoint

private def doubled0 : Checkpoint := affine
  18154201016970196990165133268248530371880021517673851018793913067599369454767
  11089872648052874581106880861001069650386164939833419134639179732371679170151
  (by decide)

private theorem doubleCert0 :
    semantic doubled0 = semantic start + semantic start := by
  unfold doubled0
  apply certifyAddAffine
  all_goals decide

private def checkpoint0 : Checkpoint := affine
  18154201016970196990165133268248530371880021517673851018793913067599369454767
  11089872648052874581106880861001069650386164939833419134639179732371679170151
  (by decide)

private theorem leaf0 :
    pointStep generatorPoint (semantic start) false = semantic checkpoint0 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert0.symm

private def doubled1 : Checkpoint := affine
  6225318413940543388509707598148184625549374950859186798296199530036527797852
  9183773041224670207985825849418956294201413379971876951922817108508033076685
  (by decide)

private theorem doubleCert1 :
    semantic doubled1 = semantic checkpoint0 + semantic checkpoint0 := by
  unfold doubled1
  apply certifyAddAffine
  all_goals decide

private def checkpoint1 : Checkpoint := affine
  6225318413940543388509707598148184625549374950859186798296199530036527797852
  9183773041224670207985825849418956294201413379971876951922817108508033076685
  (by decide)

private theorem leaf1 :
    pointStep generatorPoint (semantic checkpoint0) false = semantic checkpoint1 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert1.symm

private def doubled2 : Checkpoint := affine
  15929805198942522781854847079651094281686759303571327104578838671720088362463
  19293629368670104870368024711773298551896648293555178159123252337999195139680
  (by decide)

private theorem doubleCert2 :
    semantic doubled2 = semantic checkpoint1 + semantic checkpoint1 := by
  unfold doubled2
  apply certifyAddAffine
  all_goals decide

private def checkpoint2 : Checkpoint := affine
  6278037985194996205574317844126115031103802854106103924863287352549367198342
  6303482740698535092654682434154694228388846968391298117744461190308854281274
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
  7640136001220317478483750599501042013892553990556924241463290250475369579940
  10902025582554779153031293939836965350235721833902169211357766309821241393965
  (by decide)

private theorem doubleCert3 :
    semantic doubled3 = semantic checkpoint2 + semantic checkpoint2 := by
  unfold doubled3
  apply certifyAddAffine
  all_goals decide

private def checkpoint3 : Checkpoint := affine
  7640136001220317478483750599501042013892553990556924241463290250475369579940
  10902025582554779153031293939836965350235721833902169211357766309821241393965
  (by decide)

private theorem leaf3 :
    pointStep generatorPoint (semantic checkpoint2) false = semantic checkpoint3 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert3.symm

private def doubled4 : Checkpoint := affine
  5455808482592089698570290059293146196380262509386883622111378368216101581076
  12211218530585429756793055267432159979536994732320531165851941607294088623231
  (by decide)

private theorem doubleCert4 :
    semantic doubled4 = semantic checkpoint3 + semantic checkpoint3 := by
  unfold doubled4
  apply certifyAddAffine
  all_goals decide

private def checkpoint4 : Checkpoint := affine
  2799691475208854777619649555846113004421909428310602018825531570782619612981
  5050047918747518904825056511595305985627558803815465860749552529772425562960
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
  3264257988403743147898633347001193707874134821688103855728479530455505735349
  14648166580416507229481898341536715820105999854954929027359789659143142108306
  (by decide)

private theorem doubleCert5 :
    semantic doubled5 = semantic checkpoint4 + semantic checkpoint4 := by
  unfold doubled5
  apply certifyAddAffine
  all_goals decide

private def checkpoint5 : Checkpoint := affine
  2087667884372961407854923009192551423063470129066499407063205948633255137429
  13363492326566904034786676424001026374992182791446789501884550767494980402005
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
  8151492244731495291807921824941546763200371647143783676155458220643367370169
  13226693498420001207648539896405392655915491475404857406158750876890000811229
  (by decide)

private theorem doubleCert6 :
    semantic doubled6 = semantic checkpoint5 + semantic checkpoint5 := by
  unfold doubled6
  apply certifyAddAffine
  all_goals decide

private def checkpoint6 : Checkpoint := affine
  8151492244731495291807921824941546763200371647143783676155458220643367370169
  13226693498420001207648539896405392655915491475404857406158750876890000811229
  (by decide)

private theorem leaf6 :
    pointStep generatorPoint (semantic checkpoint5) false = semantic checkpoint6 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert6.symm

private def doubled7 : Checkpoint := affine
  5126838032551529383611586414191555174662245611037552429751953972592552385522
  15575471517022980928393619837102566295617929111937769536157506132851913646997
  (by decide)

private theorem doubleCert7 :
    semantic doubled7 = semantic checkpoint6 + semantic checkpoint6 := by
  unfold doubled7
  apply certifyAddAffine
  all_goals decide

private def checkpoint7 : Checkpoint := affine
  1090976545881187748601885533280343331621339772318494385625640447992069295414
  2469522418136217298041861360641115891468389989686843883769894658508966832645
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
  3177208533240422989715876712061049177029749639429779621187898536447701612207
  12156801019929058439153159369693973824491577185204015730805281859812035186019
  (by decide)

private theorem doubleCert8 :
    semantic doubled8 = semantic checkpoint7 + semantic checkpoint7 := by
  unfold doubled8
  apply certifyAddAffine
  all_goals decide

private def checkpoint8 : Checkpoint := affine
  16530704712139109324989678057345307087331674936920701453186731925510043421935
  13058234191291289729679769859418760767455466866792616060775658083337436031099
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
  17794805988885915203923057651140429781919048145364337266585574867871453726614
  8487529189285209044925317565659006939270903074969633926411754778507437783625
  (by decide)

private theorem doubleCert9 :
    semantic doubled9 = semantic checkpoint8 + semantic checkpoint8 := by
  unfold doubled9
  apply certifyAddAffine
  all_goals decide

private def checkpoint9 : Checkpoint := affine
  17794805988885915203923057651140429781919048145364337266585574867871453726614
  8487529189285209044925317565659006939270903074969633926411754778507437783625
  (by decide)

private theorem leaf9 :
    pointStep generatorPoint (semantic checkpoint8) false = semantic checkpoint9 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert9.symm

private def doubled10 : Checkpoint := affine
  11292495220406297685585300252572389880941611119104429412814974931368831829561
  6411934849955116063899182425367773681517889620650767577110604942410032039480
  (by decide)

private theorem doubleCert10 :
    semantic doubled10 = semantic checkpoint9 + semantic checkpoint9 := by
  unfold doubled10
  apply certifyAddAffine
  all_goals decide

private def checkpoint10 : Checkpoint := affine
  15551552634842401356335401044628742245756957869332041594857598559979248221102
  12793318962103675431811282038222374691759665001588069487883080446430592424491
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
  1945676313749557179759033525661438804373028735098930772040740003905294603985
  10360043727215236399822130738588416582558072437735144197779399534524523417113
  (by decide)

private theorem doubleCert11 :
    semantic doubled11 = semantic checkpoint10 + semantic checkpoint10 := by
  unfold doubled11
  apply certifyAddAffine
  all_goals decide

private def checkpoint11 : Checkpoint := affine
  7857972547765742377894721099524004597273900407687308246073173910480728452461
  3281688510903311759081488368788117032401871001598984658520886129003095011452
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
  2325083939044307035164395301858650847676271880787174354416188905244005703997
  9350357594669614054045573140473955368865517100858306734184238954273089498282
  (by decide)

private theorem doubleCert12 :
    semantic doubled12 = semantic checkpoint11 + semantic checkpoint11 := by
  unfold doubled12
  apply certifyAddAffine
  all_goals decide

private def checkpoint12 : Checkpoint := affine
  2325083939044307035164395301858650847676271880787174354416188905244005703997
  9350357594669614054045573140473955368865517100858306734184238954273089498282
  (by decide)

private theorem leaf12 :
    pointStep generatorPoint (semantic checkpoint11) false = semantic checkpoint12 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert12.symm

private def doubled13 : Checkpoint := affine
  21113994601722403315088586837789233211783072962165584888229283361627968102595
  10241846827268630408253697245520960607479611735726138791433086951090445584192
  (by decide)

private theorem doubleCert13 :
    semantic doubled13 = semantic checkpoint12 + semantic checkpoint12 := by
  unfold doubled13
  apply certifyAddAffine
  all_goals decide

private def checkpoint13 : Checkpoint := affine
  6657606209401805053910023940221531589418320510298867725776034698157796123265
  15488461542064826297929593143933386393704404980938237403977638024555675137638
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
  20162178091620398660293863150258737198603350864917045217950721842474653336134
  6797624428335188326418256386812739195273125753903473070939075059096134812461
  (by decide)

private theorem doubleCert14 :
    semantic doubled14 = semantic checkpoint13 + semantic checkpoint13 := by
  unfold doubled14
  apply certifyAddAffine
  all_goals decide

private def checkpoint14 : Checkpoint := affine
  20162178091620398660293863150258737198603350864917045217950721842474653336134
  6797624428335188326418256386812739195273125753903473070939075059096134812461
  (by decide)

private theorem leaf14 :
    pointStep generatorPoint (semantic checkpoint13) false = semantic checkpoint14 := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert14.symm

private def doubled15 : Checkpoint := affine
  4631413540302581572994434551248189597395512394791305102605150733219417979071
  7576422400766764093844050206919373585456554920781991823602854482891348625362
  (by decide)

private theorem doubleCert15 :
    semantic doubled15 = semantic checkpoint14 + semantic checkpoint14 := by
  unfold doubled15
  apply certifyAddAffine
  all_goals decide

def endpoint : Checkpoint := affine
  4631413540302581572994434551248189597395512394791305102605150733219417979071
  7576422400766764093844050206919373585456554920781991823602854482891348625362
  (by decide)

private theorem leaf15 :
    pointStep generatorPoint (semantic checkpoint14) false = semantic endpoint := by
  simp only [pointStep, if_false, add_zero]
  exact doubleCert15.symm

def bits : List Bool := [false, false, true, false, true, true, false, true, true, false, true, true, false, true, false, false]

theorem transition :
    bits.foldl (pointStep generatorPoint) (semantic G1OrderCertShard04.endpoint) =
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

end GarblingPrize.Submission.G1OrderCertShard05

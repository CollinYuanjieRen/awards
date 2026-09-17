import MerLeanExperiment.FixedCorePattern

namespace CochromaticTwenty.CoreWitnesses
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def model_0_2_0_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 3, 14, 11, 1, 0, 15, 9, 6]
theorem model_0_2_0_bijective : Function.Bijective model_0_2_0_map := by decide +kernel
theorem model_0_2_0_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_0_map u) (model_0_2_0_map v) ↔
      (codeGraph 16 1033524294936737235384115735117026507).Adj u v := by decide +kernel
def model_0_2_0_iso : codeGraph 16 1033524294936737235384115735117026507 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_0_map model_0_2_0_bijective
  map_rel_iff' := by intro u v; exact model_0_2_0_adj u v

def model_0_2_1_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 5, 7, 15, 13, 6, 4, 14, 12]
theorem model_0_2_1_bijective : Function.Bijective model_0_2_1_map := by decide +kernel
theorem model_0_2_1_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_1_map u) (model_0_2_1_map v) ↔
      (codeGraph 16 1037337368125511127389810778040554699).Adj u v := by decide +kernel
def model_0_2_1_iso : codeGraph 16 1037337368125511127389810778040554699 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_1_map model_0_2_1_bijective
  map_rel_iff' := by intro u v; exact model_0_2_1_adj u v

def model_0_2_2_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 6, 7, 12, 4, 5, 13, 14, 15]
theorem model_0_2_2_bijective : Function.Bijective model_0_2_2_map := by decide +kernel
theorem model_0_2_2_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_2_map u) (model_0_2_2_map v) ↔
      (codeGraph 16 1034173312217670504124281626490688715).Adj u v := by decide +kernel
def model_0_2_2_iso : codeGraph 16 1034173312217670504124281626490688715 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_2_map model_0_2_2_bijective
  map_rel_iff' := by intro u v; exact model_0_2_2_adj u v

def model_0_2_3_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 3, 11, 14, 1, 15, 0, 6, 9]
theorem model_0_2_3_bijective : Function.Bijective model_0_2_3_map := by decide +kernel
theorem model_0_2_3_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_3_map u) (model_0_2_3_map v) ↔
      (codeGraph 16 1036607032989721505740760291957134539).Adj u v := by decide +kernel
def model_0_2_3_iso : codeGraph 16 1036607032989721505740760291957134539 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_3_map model_0_2_3_bijective
  map_rel_iff' := by intro u v; exact model_0_2_3_adj u v

def model_0_2_4_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 14, 13, 4, 7, 12, 15, 5, 6]
theorem model_0_2_4_bijective : Function.Bijective model_0_2_4_map := by decide +kernel
theorem model_0_2_4_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_4_map u) (model_0_2_4_map v) ↔
      (codeGraph 16 1029873065057004482010659550448178379).Adj u v := by decide +kernel
def model_0_2_4_iso : codeGraph 16 1029873065057004482010659550448178379 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_4_map model_0_2_4_bijective
  map_rel_iff' := by intro u v; exact model_0_2_4_adj u v

def model_0_2_5_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 15, 5, 4, 12, 7, 14, 13, 6]
theorem model_0_2_5_bijective : Function.Bijective model_0_2_5_map := by decide +kernel
theorem model_0_2_5_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_5_map u) (model_0_2_5_map v) ↔
      (codeGraph 16 1029873238384314364969178735834420427).Adj u v := by decide +kernel
def model_0_2_5_iso : codeGraph 16 1029873238384314364969178735834420427 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_5_map model_0_2_5_bijective
  map_rel_iff' := by intro u v; exact model_0_2_5_adj u v

def model_0_2_6_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 12, 13, 6, 15, 14, 7, 5, 4]
theorem model_0_2_6_bijective : Function.Bijective model_0_2_6_map := by decide +kernel
theorem model_0_2_6_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_6_map u) (model_0_2_6_map v) ↔
      (codeGraph 16 1034254065507212810847059763749311691).Adj u v := by decide +kernel
def model_0_2_6_iso : codeGraph 16 1034254065507212810847059763749311691 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_6_map model_0_2_6_bijective
  map_rel_iff' := by intro u v; exact model_0_2_6_adj u v

def model_0_2_7_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 11, 3, 15, 6, 14, 9, 1, 0]
theorem model_0_2_7_bijective : Function.Bijective model_0_2_7_map := by decide +kernel
theorem model_0_2_7_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_7_map u) (model_0_2_7_map v) ↔
      (codeGraph 16 1030197524207665615481363609463149771).Adj u v := by decide +kernel
def model_0_2_7_iso : codeGraph 16 1030197524207665615481363609463149771 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_7_map model_0_2_7_bijective
  map_rel_iff' := by intro u v; exact model_0_2_7_adj u v

def model_0_2_8_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 6, 0, 1, 11, 14, 9, 15, 3]
theorem model_0_2_8_bijective : Function.Bijective model_0_2_8_map := by decide +kernel
theorem model_0_2_8_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_8_map u) (model_0_2_8_map v) ↔
      (codeGraph 16 1032307285995497805902074060054320331).Adj u v := by decide +kernel
def model_0_2_8_iso : codeGraph 16 1032307285995497805902074060054320331 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_8_map model_0_2_8_bijective
  map_rel_iff' := by intro u v; exact model_0_2_8_adj u v

def model_0_2_9_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 4, 14, 15, 6, 13, 5, 7, 12]
theorem model_0_2_9_bijective : Function.Bijective model_0_2_9_map := by decide +kernel
theorem model_0_2_9_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_9_map u) (model_0_2_9_map v) ↔
      (codeGraph 16 1037337041278518752721264093330527435).Adj u v := by decide +kernel
def model_0_2_9_iso : codeGraph 16 1037337041278518752721264093330527435 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_9_map model_0_2_9_bijective
  map_rel_iff' := by intro u v; exact model_0_2_9_adj u v

def model_0_2_10_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 6, 12, 7, 4, 13, 5, 15, 14]
theorem model_0_2_10_bijective : Function.Bijective model_0_2_10_map := by decide +kernel
theorem model_0_2_10_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_10_map u) (model_0_2_10_map v) ↔
      (codeGraph 16 1036282554049535155408359906119898315).Adj u v := by decide +kernel
def model_0_2_10_iso : codeGraph 16 1036282554049535155408359906119898315 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_10_map model_0_2_10_bijective
  map_rel_iff' := by intro u v; exact model_0_2_10_adj u v

def model_0_2_11_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 15, 4, 5, 12, 14, 7, 6, 13]
theorem model_0_2_11_bijective : Function.Bijective model_0_2_11_map := by decide +kernel
theorem model_0_2_11_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_11_map u) (model_0_2_11_map v) ↔
      (codeGraph 16 1032955976437298635325823292674528459).Adj u v := by decide +kernel
def model_0_2_11_iso : codeGraph 16 1032955976437298635325823292674528459 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_11_map model_0_2_11_bijective
  map_rel_iff' := by intro u v; exact model_0_2_11_adj u v

def model_0_2_12_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 11, 15, 3, 6, 9, 14, 0, 1]
theorem model_0_2_12_bijective : Function.Bijective model_0_2_12_map := by decide +kernel
theorem model_0_2_12_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_12_map u) (model_0_2_12_map v) ↔
      (codeGraph 16 1029142903248524743320128249751000267).Adj u v := by decide +kernel
def model_0_2_12_iso : codeGraph 16 1029142903248524743320128249751000267 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_12_map model_0_2_12_bijective
  map_rel_iff' := by intro u v; exact model_0_2_12_adj u v

def model_0_2_13_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 7, 5, 6, 14, 15, 12, 13, 4]
theorem model_0_2_13_bijective : Function.Bijective model_0_2_13_map := by decide +kernel
theorem model_0_2_13_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_13_map u) (model_0_2_13_map v) ↔
      (codeGraph 16 1034254238866567045625801362650813643).Adj u v := by decide +kernel
def model_0_2_13_iso : codeGraph 16 1034254238866567045625801362650813643 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_13_map model_0_2_13_bijective
  map_rel_iff' := by intro u v; exact model_0_2_13_adj u v

def model_0_2_14_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 6, 1, 0, 11, 9, 14, 3, 15]
theorem model_0_2_14_bijective : Function.Bijective model_0_2_14_map := by decide +kernel
theorem model_0_2_14_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_14_map u) (model_0_2_14_map v) ↔
      (codeGraph 16 1035552273429042759373819498177352907).Adj u v := by decide +kernel
def model_0_2_14_iso : codeGraph 16 1035552273429042759373819498177352907 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_14_map model_0_2_14_bijective
  map_rel_iff' := by intro u v; exact model_0_2_14_adj u v

def model_0_2_15_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 1, 6, 9, 3, 0, 15, 11, 14]
theorem model_0_2_15_bijective : Function.Bijective model_0_2_15_map := by decide +kernel
theorem model_0_2_15_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_15_map u) (model_0_2_15_map v) ↔
      (codeGraph 16 1032226205866823059862879264042243275).Adj u v := by decide +kernel
def model_0_2_15_iso : codeGraph 16 1032226205866823059862879264042243275 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_15_map model_0_2_15_bijective
  map_rel_iff' := by intro u v; exact model_0_2_15_adj u v

def model_0_2_16_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 5, 15, 7, 13, 4, 6, 12, 14]
theorem model_0_2_16_bijective : Function.Bijective model_0_2_16_map := by decide +kernel
theorem model_0_2_16_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_16_map u) (model_0_2_16_map v) ↔
      (codeGraph 16 1036282747166370255228575418328405195).Adj u v := by decide +kernel
def model_0_2_16_iso : codeGraph 16 1036282747166370255228575418328405195 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_16_map model_0_2_16_bijective
  map_rel_iff' := by intro u v; exact model_0_2_16_adj u v

def model_0_2_17_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 1, 9, 6, 3, 15, 0, 14, 11]
theorem model_0_2_17_bijective : Function.Bijective model_0_2_17_map := by decide +kernel
theorem model_0_2_17_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_17_map u) (model_0_2_17_map v) ↔
      (codeGraph 16 1036363564846315174242707790162678987).Adj u v := by decide +kernel
def model_0_2_17_iso : codeGraph 16 1036363564846315174242707790162678987 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_17_map model_0_2_17_bijective
  map_rel_iff' := by intro u v; exact model_0_2_17_adj u v

def model_0_2_18_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 9, 1, 15, 14, 6, 11, 3, 0]
theorem model_0_2_18_bijective : Function.Bijective model_0_2_18_map := by decide +kernel
theorem model_0_2_18_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_18_map u) (model_0_2_18_map v) ↔
      (codeGraph 16 1030197717324500715301579121671656651).Adj u v := by decide +kernel
def model_0_2_18_iso : codeGraph 16 1030197717324500715301579121671656651 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_18_map model_0_2_18_bijective
  map_rel_iff' := by intro u v; exact model_0_2_18_adj u v

def model_0_2_19_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 7, 6, 5, 14, 12, 15, 4, 13]
theorem model_0_2_19_bijective : Function.Bijective model_0_2_19_map := by decide +kernel
theorem model_0_2_19_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_19_map u) (model_0_2_19_map v) ↔
      (codeGraph 16 1032956243856527554884882754501465291).Adj u v := by decide +kernel
def model_0_2_19_iso : codeGraph 16 1032956243856527554884882754501465291 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_19_map model_0_2_19_bijective
  map_rel_iff' := by intro u v; exact model_0_2_19_adj u v

def model_0_2_20_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 14, 3, 0, 9, 11, 6, 1, 15]
theorem model_0_2_20_bijective : Function.Bijective model_0_2_20_map := by decide +kernel
theorem model_0_2_20_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_20_map u) (model_0_2_20_map v) ↔
      (codeGraph 16 1035552080320067594905734011925419211).Adj u v := by decide +kernel
def model_0_2_20_iso : codeGraph 16 1035552080320067594905734011925419211 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_20_map model_0_2_20_bijective
  map_rel_iff' := by intro u v; exact model_0_2_20_adj u v

def model_0_2_21_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 9, 15, 1, 14, 11, 6, 0, 3]
theorem model_0_2_21_bijective : Function.Bijective model_0_2_21_map := by decide +kernel
theorem model_0_2_21_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_21_map u) (model_0_2_21_map v) ↔
      (codeGraph 16 1032306959156365366585657401300866251).Adj u v := by decide +kernel
def model_0_2_21_iso : codeGraph 16 1032306959156365366585657401300866251 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_21_map model_0_2_21_bijective
  map_rel_iff' := by intro u v; exact model_0_2_21_adj u v

def model_0_2_22_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 14, 0, 3, 9, 6, 11, 15, 1]
theorem model_0_2_22_bijective : Function.Bijective model_0_2_22_map := by decide +kernel
theorem model_0_2_22_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_22_map u) (model_0_2_22_map v) ↔
      (codeGraph 16 1029143230095517117988674934461027531).Adj u v := by decide +kernel
def model_0_2_22_iso : codeGraph 16 1029143230095517117988674934461027531 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_22_map model_0_2_22_bijective
  map_rel_iff' := by intro u v; exact model_0_2_22_adj u v

def model_0_2_23_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 14, 4, 13, 7, 15, 12, 6, 5]
theorem model_0_2_23_bijective : Function.Bijective model_0_2_23_map := by decide +kernel
theorem model_0_2_23_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_23_map u) (model_0_2_23_map v) ↔
      (codeGraph 16 1030116439140536128728394189317199051).Adj u v := by decide +kernel
def model_0_2_23_iso : codeGraph 16 1030116439140536128728394189317199051 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_23_map model_0_2_23_bijective
  map_rel_iff' := by intro u v; exact model_0_2_23_adj u v

def model_0_2_24_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 4, 15, 14, 6, 5, 13, 12, 7]
theorem model_0_2_24_bijective : Function.Bijective model_0_2_24_map := by decide +kernel
theorem model_0_2_24_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_24_map u) (model_0_2_24_map v) ↔
      (codeGraph 16 1030928191053968275804205015866135755).Adj u v := by decide +kernel
def model_0_2_24_iso : codeGraph 16 1030928191053968275804205015866135755 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_24_map model_0_2_24_bijective
  map_rel_iff' := by intro u v; exact model_0_2_24_adj u v

def model_0_2_25_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 0, 6, 14, 15, 1, 3, 11, 9]
theorem model_0_2_25_bijective : Function.Bijective model_0_2_25_map := by decide +kernel
theorem model_0_2_25_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_25_map u) (model_0_2_25_map v) ↔
      (codeGraph 16 1036607206317031388699279477343376587).Adj u v := by decide +kernel
def model_0_2_25_iso : codeGraph 16 1036607206317031388699279477343376587 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_25_map model_0_2_25_bijective
  map_rel_iff' := by intro u v; exact model_0_2_25_adj u v

def model_0_2_26_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 0, 14, 6, 15, 3, 1, 9, 11]
theorem model_0_2_26_bijective : Function.Bijective model_0_2_26_map := by decide +kernel
theorem model_0_2_26_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_26_map u) (model_0_2_26_map v) ↔
      (codeGraph 16 1036363832233499741981544838474355915).Adj u v := by decide +kernel
def model_0_2_26_iso : codeGraph 16 1036363832233499741981544838474355915 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_26_map model_0_2_26_bijective
  map_rel_iff' := by intro u v; exact model_0_2_26_adj u v

def model_0_2_27_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 13, 12, 14, 5, 6, 4, 15, 7]
theorem model_0_2_27_bijective : Function.Bijective model_0_2_27_map := by decide +kernel
theorem model_0_2_27_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_27_map u) (model_0_2_27_map v) ↔
      (codeGraph 16 1030927997944993111336119529614202059).Adj u v := by decide +kernel
def model_0_2_27_iso : codeGraph 16 1030927997944993111336119529614202059 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_27_map model_0_2_27_bijective
  map_rel_iff' := by intro u v; exact model_0_2_27_adj u v

def model_0_2_28_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 15, 9, 11, 0, 1, 3, 14, 6]
theorem model_0_2_28_bijective : Function.Bijective model_0_2_28_map := by decide +kernel
theorem model_0_2_28_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_28_map u) (model_0_2_28_map v) ↔
      (codeGraph 16 1033524027517508315825056273290089675).Adj u v := by decide +kernel
def model_0_2_28_iso : codeGraph 16 1033524027517508315825056273290089675 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_28_map model_0_2_28_bijective
  map_rel_iff' := by intro u v; exact model_0_2_28_adj u v

def model_0_2_29_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 12, 6, 13, 15, 7, 14, 4, 5]
theorem model_0_2_29_bijective : Function.Bijective model_0_2_29_map := by decide +kernel
theorem model_0_2_29_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_29_map u) (model_0_2_29_map v) ↔
      (codeGraph 16 1030116706527720696467231237628875979).Adj u v := by decide +kernel
def model_0_2_29_iso : codeGraph 16 1030116706527720696467231237628875979 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_29_map model_0_2_29_bijective
  map_rel_iff' := by intro u v; exact model_0_2_29_adj u v

def model_0_2_30_map : Fin 16 → Fin 16 := ![4, 5, 2, 7, 8, 10, 12, 13, 15, 11, 9, 0, 3, 1, 6, 14]
theorem model_0_2_30_bijective : Function.Bijective model_0_2_30_map := by decide +kernel
theorem model_0_2_30_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_30_map u) (model_0_2_30_map v) ↔
      (codeGraph 16 1032226032507468825084137665140741323).Adj u v := by decide +kernel
def model_0_2_30_iso : codeGraph 16 1032226032507468825084137665140741323 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_30_map model_0_2_30_bijective
  map_rel_iff' := by intro u v; exact model_0_2_30_adj u v

def model_0_2_31_map : Fin 16 → Fin 16 := ![0, 1, 3, 2, 8, 9, 11, 10, 13, 14, 12, 5, 4, 6, 7, 15]
theorem model_0_2_31_bijective : Function.Bijective model_0_2_31_map := by decide +kernel
theorem model_0_2_31_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (model_0_2_31_map u) (model_0_2_31_map v) ↔
      (codeGraph 16 1034172985378538064807864967737234635).Adj u v := by decide +kernel
def model_0_2_31_iso : codeGraph 16 1034172985378538064807864967737234635 ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective model_0_2_31_map model_0_2_31_bijective
  map_rel_iff' := by intro u v; exact model_0_2_31_adj u v

def model_8_0_0_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 8, 11, 4, 5, 6, 7, 13, 15, 12, 14]
theorem model_8_0_0_bijective : Function.Bijective model_8_0_0_map := by decide +kernel
theorem model_8_0_0_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_0_map u) (model_8_0_0_map v) ↔
      (codeGraph 16 567700708560257362446748513803736415).Adj u v := by decide +kernel
def model_8_0_0_iso : codeGraph 16 567700708560257362446748513803736415 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_0_map model_8_0_0_bijective
  map_rel_iff' := by intro u v; exact model_8_0_0_adj u v

def model_8_0_1_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 10, 9, 4, 5, 7, 6, 14, 12, 15, 13]
theorem model_8_0_1_bijective : Function.Bijective model_8_0_1_map := by decide +kernel
theorem model_8_0_1_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_1_map u) (model_8_0_1_map v) ↔
      (codeGraph 16 567051671452941689008906212040545631).Adj u v := by decide +kernel
def model_8_0_1_iso : codeGraph 16 567051671452941689008906212040545631 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_1_map model_8_0_1_bijective
  map_rel_iff' := by intro u v; exact model_8_0_1_adj u v

def model_8_0_2_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 10, 9, 5, 4, 6, 7, 12, 14, 13, 15]
theorem model_8_0_2_bijective : Function.Bijective model_8_0_2_map := by decide +kernel
theorem model_8_0_2_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_2_map u) (model_8_0_2_map v) ↔
      (codeGraph 16 568998663947152044449887723164833119).Adj u v := by decide +kernel
def model_8_0_2_iso : codeGraph 16 568998663947152044449887723164833119 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_2_map model_8_0_2_bijective
  map_rel_iff' := by intro u v; exact model_8_0_2_adj u v

def model_8_0_3_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 8, 11, 5, 4, 7, 6, 15, 13, 14, 12]
theorem model_8_0_3_bijective : Function.Bijective model_8_0_3_map := by decide +kernel
theorem model_8_0_3_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_3_map u) (model_8_0_3_map v) ↔
      (codeGraph 16 568998703556397597727701296104641887).Adj u v := by decide +kernel
def model_8_0_3_iso : codeGraph 16 568998703556397597727701296104641887 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_3_map model_8_0_3_bijective
  map_rel_iff' := by intro u v; exact model_8_0_3_adj u v

def model_8_0_4_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 11, 8, 4, 5, 7, 6, 14, 12, 15, 13]
theorem model_8_0_4_bijective : Function.Bijective model_8_0_4_map := by decide +kernel
theorem model_8_0_4_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_4_map u) (model_8_0_4_map v) ↔
      (codeGraph 16 566889045790591397790568697210639711).Adj u v := by decide +kernel
def model_8_0_4_iso : codeGraph 16 566889045790591397790568697210639711 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_4_map model_8_0_4_bijective
  map_rel_iff' := by intro u v; exact model_8_0_4_adj u v

def model_8_0_5_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 5, 15, 2, 7, 13, 10, 11, 3, 0, 12]
theorem model_8_0_5_bijective : Function.Bijective model_8_0_5_map := by decide +kernel
theorem model_8_0_5_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_5_map u) (model_8_0_5_map v) ↔
      (codeGraph 16 566889006157167327688962496695932255).Adj u v := by decide +kernel
def model_8_0_5_iso : codeGraph 16 566889006157167327688962496695932255 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_5_map model_8_0_5_bijective
  map_rel_iff' := by intro u v; exact model_8_0_5_adj u v

def model_8_0_6_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 5, 15, 2, 7, 13, 10, 11, 3, 0, 12]
theorem model_8_0_6_bijective : Function.Bijective model_8_0_6_map := by decide +kernel
theorem model_8_0_6_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_6_map u) (model_8_0_6_map v) ↔
      (codeGraph 16 567538003650401743994638192120468831).Adj u v := by decide +kernel
def model_8_0_6_iso : codeGraph 16 567538003650401743994638192120468831 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_6_map model_8_0_6_bijective
  map_rel_iff' := by intro u v; exact model_8_0_6_adj u v

def model_8_0_7_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 9, 10, 4, 5, 6, 7, 13, 15, 12, 14]
theorem model_8_0_7_bijective : Function.Bijective model_8_0_7_map := by decide +kernel
theorem model_8_0_7_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_7_map u) (model_8_0_7_map v) ↔
      (codeGraph 16 567538082897907071228413189407151455).Adj u v := by decide +kernel
def model_8_0_7_iso : codeGraph 16 567538082897907071228413189407151455 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_7_map model_8_0_7_bijective
  map_rel_iff' := by intro u v; exact model_8_0_7_adj u v

def model_8_0_8_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 5, 15, 7, 2, 13, 10, 0, 12, 11, 3]
theorem model_8_0_8_bijective : Function.Bijective model_8_0_8_map := by decide +kernel
theorem model_8_0_8_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_8_map u) (model_8_0_8_map v) ↔
      (codeGraph 16 566402357080900056485532173204231519).Adj u v := by decide +kernel
def model_8_0_8_iso : codeGraph 16 566402357080900056485532173204231519 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_8_map model_8_0_8_bijective
  map_rel_iff' := by intro u v; exact model_8_0_8_adj u v

def model_8_0_9_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 9, 10, 5, 4, 6, 7, 12, 14, 13, 15]
theorem model_8_0_9_bijective : Function.Bijective model_8_0_9_map := by decide +kernel
theorem model_8_0_9_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_9_map u) (model_8_0_9_map v) ↔
      (codeGraph 16 568998505510169831338642193138881887).Adj u v := by decide +kernel
def model_8_0_9_iso : codeGraph 16 568998505510169831338642193138881887 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_9_map model_8_0_9_bijective
  map_rel_iff' := by intro u v; exact model_8_0_9_adj u v

def model_8_0_10_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 11, 8, 5, 4, 7, 6, 15, 13, 14, 12]
theorem model_8_0_10_bijective : Function.Bijective model_8_0_10_map := by decide +kernel
theorem model_8_0_10_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_10_map u) (model_8_0_10_map v) ↔
      (codeGraph 16 568998545119415384616455766078690655).Adj u v := by decide +kernel
def model_8_0_10_iso : codeGraph 16 568998545119415384616455766078690655 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_10_map model_8_0_10_bijective
  map_rel_iff' := by intro u v; exact model_8_0_10_adj u v

def model_8_0_11_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 11, 8, 4, 5, 6, 7, 13, 15, 12, 14]
theorem model_8_0_11_bijective : Function.Bijective model_8_0_11_map := by decide +kernel
theorem model_8_0_11_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_11_map u) (model_8_0_11_map v) ↔
      (codeGraph 16 565104560130994668695370545017689439).Adj u v := by decide +kernel
def model_8_0_11_iso : codeGraph 16 565104560130994668695370545017689439 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_11_map model_8_0_11_bijective
  map_rel_iff' := by intro u v; exact model_8_0_11_adj u v

def model_8_0_12_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 15, 5, 7, 2, 10, 13, 3, 11, 12, 0]
theorem model_8_0_12_bijective : Function.Bijective model_8_0_12_map := by decide +kernel
theorem model_8_0_12_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_12_map u) (model_8_0_12_map v) ↔
      (codeGraph 16 562345865257862170860079198865495391).Adj u v := by decide +kernel
def model_8_0_12_iso : codeGraph 16 562345865257862170860079198865495391 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_12_map model_8_0_12_bijective
  map_rel_iff' := by intro u v; exact model_8_0_12_adj u v

def model_8_0_13_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 15, 5, 7, 2, 10, 13, 3, 11, 12, 0]
theorem model_8_0_13_bijective : Function.Bijective model_8_0_13_map := by decide +kernel
theorem model_8_0_13_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_13_map u) (model_8_0_13_map v) ↔
      (codeGraph 16 561696867759790870684324269330830687).Adj u v := by decide +kernel
def model_8_0_13_iso : codeGraph 16 561696867759790870684324269330830687 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_13_map model_8_0_13_bijective
  map_rel_iff' := by intro u v; exact model_8_0_13_adj u v

def model_8_0_14_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 10, 9, 5, 4, 7, 6, 15, 13, 14, 12]
theorem model_8_0_14_bijective : Function.Bijective model_8_0_14_map := by decide +kernel
theorem model_8_0_14_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_14_map u) (model_8_0_14_map v) ↔
      (codeGraph 16 562994941974434022036051519063496031).Adj u v := by decide +kernel
def model_8_0_14_iso : codeGraph 16 562994941974434022036051519063496031 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_14_map model_8_0_14_bijective
  map_rel_iff' := by intro u v; exact model_8_0_14_adj u v

def model_8_0_15_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 8, 11, 5, 4, 6, 7, 12, 14, 13, 15]
theorem model_8_0_15_bijective : Function.Bijective model_8_0_15_map := by decide +kernel
theorem model_8_0_15_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_15_map u) (model_8_0_15_map v) ↔
      (codeGraph 16 562994902365188468758240136557008223).Adj u v := by decide +kernel
def model_8_0_15_iso : codeGraph 16 562994902365188468758240136557008223 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_15_map model_8_0_15_bijective
  map_rel_iff' := by intro u v; exact model_8_0_15_adj u v

def model_8_0_16_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 15, 5, 2, 7, 10, 13, 12, 0, 3, 11]
theorem model_8_0_16_bijective : Function.Bijective model_8_0_16_map := by decide +kernel
theorem model_8_0_16_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_16_map u) (model_8_0_16_map v) ↔
      (codeGraph 16 567700391642771602399310736569177439).Adj u v := by decide +kernel
def model_8_0_16_iso : codeGraph 16 567700391642771602399310736569177439 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_16_map model_8_0_16_bijective
  map_rel_iff' := by intro u v; exact model_8_0_16_adj u v

def model_8_0_17_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 15, 5, 2, 7, 10, 13, 12, 0, 3, 11]
theorem model_8_0_17_bijective : Function.Bijective model_8_0_17_map := by decide +kernel
theorem model_8_0_17_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_17_map u) (model_8_0_17_map v) ↔
      (codeGraph 16 567051354530620225683009918107161951).Adj u v := by decide +kernel
def model_8_0_17_iso : codeGraph 16 567051354530620225683009918107161951 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_17_map model_8_0_17_bijective
  map_rel_iff' := by intro u v; exact model_8_0_17_adj u v

def model_8_0_18_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 5, 15, 7, 2, 13, 10, 0, 12, 11, 3]
theorem model_8_0_18_bijective : Function.Bijective model_8_0_18_map := by decide +kernel
theorem model_8_0_18_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_18_map u) (model_8_0_18_map v) ↔
      (codeGraph 16 566402396690146790354966463555343711).Adj u v := by decide +kernel
def model_8_0_18_iso : codeGraph 16 566402396690146790354966463555343711 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_18_map model_8_0_18_bijective
  map_rel_iff' := by intro u v; exact model_8_0_18_adj u v

def model_8_0_19_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 9, 10, 4, 5, 7, 6, 14, 12, 15, 13]
theorem model_8_0_19_bijective : Function.Bijective model_8_0_19_map := by decide +kernel
theorem model_8_0_19_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_19_map u) (model_8_0_19_map v) ↔
      (codeGraph 16 564455523023678995257528243254498655).Adj u v := by decide +kernel
def model_8_0_19_iso : codeGraph 16 564455523023678995257528243254498655 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_19_map model_8_0_19_bijective
  map_rel_iff' := by intro u v; exact model_8_0_19_adj u v

def model_8_0_20_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 5, 15, 2, 7, 10, 13, 12, 0, 3, 11]
theorem model_8_0_20_bijective : Function.Bijective model_8_0_20_map := by decide +kernel
theorem model_8_0_20_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_20_map u) (model_8_0_20_map v) ↔
      (codeGraph 16 565104401669833937176607954871031135).Adj u v := by decide +kernel
def model_8_0_20_iso : codeGraph 16 565104401669833937176607954871031135 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_20_map model_8_0_20_bijective
  map_rel_iff' := by intro u v; exact model_8_0_20_adj u v

def model_8_0_21_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 5, 15, 2, 7, 10, 13, 12, 0, 3, 11]
theorem model_8_0_21_bijective : Function.Bijective model_8_0_21_map := by decide +kernel
theorem model_8_0_21_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_21_map u) (model_8_0_21_map v) ↔
      (codeGraph 16 564455364557682560460307136409015647).Adj u v := by decide +kernel
def model_8_0_21_iso : codeGraph 16 564455364557682560460307136409015647 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_21_map model_8_0_21_bijective
  map_rel_iff' := by intro u v; exact model_8_0_21_adj u v

def model_8_0_22_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 15, 5, 7, 2, 13, 10, 0, 12, 11, 3]
theorem model_8_0_22_bijective : Function.Bijective model_8_0_22_map := by decide +kernel
theorem model_8_0_22_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_22_map u) (model_8_0_22_map v) ↔
      (codeGraph 16 563806367088614855782512455065572703).Adj u v := by decide +kernel
def model_8_0_22_iso : codeGraph 16 563806367088614855782512455065572703 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_22_map model_8_0_22_bijective
  map_rel_iff' := by intro u v; exact model_8_0_22_adj u v

def model_8_0_23_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 15, 5, 7, 2, 13, 10, 0, 12, 11, 3]
theorem model_8_0_23_bijective : Function.Bijective model_8_0_23_map := by decide +kernel
theorem model_8_0_23_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_23_map u) (model_8_0_23_map v) ↔
      (codeGraph 16 563806406697861589651946745416684895).Adj u v := by decide +kernel
def model_8_0_23_iso : codeGraph 16 563806406697861589651946745416684895 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_23_map model_8_0_23_bijective
  map_rel_iff' := by intro u v; exact model_8_0_23_adj u v

def model_8_0_24_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 10, 9, 4, 5, 6, 7, 13, 15, 12, 14]
theorem model_8_0_24_bijective : Function.Bijective model_8_0_24_map := by decide +kernel
theorem model_8_0_24_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_24_map u) (model_8_0_24_map v) ↔
      (codeGraph 16 564941934468644377477043982354388319).Adj u v := by decide +kernel
def model_8_0_24_iso : codeGraph 16 564941934468644377477043982354388319 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_24_map model_8_0_24_bijective
  map_rel_iff' := by intro u v; exact model_8_0_24_adj u v

def model_8_0_25_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 15, 5, 2, 7, 13, 10, 11, 3, 0, 12]
theorem model_8_0_25_bijective : Function.Bijective model_8_0_25_map := by decide +kernel
theorem model_8_0_25_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_25_map u) (model_8_0_25_map v) ↔
      (codeGraph 16 564941855201796237129434918272406879).Adj u v := by decide +kernel
def model_8_0_25_iso : codeGraph 16 564941855201796237129434918272406879 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_25_map model_8_0_25_bijective
  map_rel_iff' := by intro u v; exact model_8_0_25_adj u v

def model_8_0_26_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 8, 11, 4, 5, 7, 6, 14, 12, 15, 13]
theorem model_8_0_26_bijective : Function.Bijective model_8_0_26_map := by decide +kernel
theorem model_8_0_26_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_26_map u) (model_8_0_26_map v) ↔
      (codeGraph 16 564292897361328704039199490157876575).Adj u v := by decide +kernel
def model_8_0_26_iso : codeGraph 16 564292897361328704039199490157876575 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_26_map model_8_0_26_bijective
  map_rel_iff' := by intro u v; exact model_8_0_26_adj u v

def model_8_0_27_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 15, 5, 2, 7, 13, 10, 11, 3, 0, 12]
theorem model_8_0_27_bijective : Function.Bijective model_8_0_27_map := by decide +kernel
theorem model_8_0_27_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_27_map u) (model_8_0_27_map v) ↔
      (codeGraph 16 564292857708561820823759222847870303).Adj u v := by decide +kernel
def model_8_0_27_iso : codeGraph 16 564292857708561820823759222847870303 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_27_map model_8_0_27_bijective
  map_rel_iff' := by intro u v; exact model_8_0_27_adj u v

def model_8_0_28_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 4, 9, 5, 15, 7, 2, 10, 13, 3, 11, 12, 0]
theorem model_8_0_28_bijective : Function.Bijective model_8_0_28_map := by decide +kernel
theorem model_8_0_28_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_28_map u) (model_8_0_28_map v) ↔
      (codeGraph 16 562346023694849106337816360269944159).Adj u v := by decide +kernel
def model_8_0_28_iso : codeGraph 16 562346023694849106337816360269944159 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_28_map model_8_0_28_bijective
  map_rel_iff' := by intro u v; exact model_8_0_28_adj u v

def model_8_0_29_map : Fin 16 → Fin 16 := ![0, 3, 2, 1, 9, 10, 11, 8, 5, 4, 6, 7, 12, 14, 13, 15]
theorem model_8_0_29_bijective : Function.Bijective model_8_0_29_map := by decide +kernel
theorem model_8_0_29_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_29_map u) (model_8_0_29_map v) ↔
      (codeGraph 16 562995060802170681869494428316243295).Adj u v := by decide +kernel
def model_8_0_29_iso : codeGraph 16 562995060802170681869494428316243295 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_29_map model_8_0_29_bijective
  map_rel_iff' := by intro u v; exact model_8_0_29_adj u v

def model_8_0_30_map : Fin 16 → Fin 16 := ![6, 1, 8, 14, 9, 4, 5, 15, 7, 2, 10, 13, 3, 11, 12, 0]
theorem model_8_0_30_bijective : Function.Bijective model_8_0_30_map := by decide +kernel
theorem model_8_0_30_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_30_map u) (model_8_0_30_map v) ↔
      (codeGraph 16 561697026196777806162061430735279455).Adj u v := by decide +kernel
def model_8_0_30_iso : codeGraph 16 561697026196777806162061430735279455 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_30_map model_8_0_30_bijective
  map_rel_iff' := by intro u v; exact model_8_0_30_adj u v

def model_8_0_31_map : Fin 16 → Fin 16 := ![0, 3, 1, 2, 8, 11, 9, 10, 5, 4, 7, 6, 15, 13, 14, 12]
theorem model_8_0_31_bijective : Function.Bijective model_8_0_31_map := by decide +kernel
theorem model_8_0_31_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (model_8_0_31_map u) (model_8_0_31_map v) ↔
      (codeGraph 16 562995100411416235147305810822731103).Adj u v := by decide +kernel
def model_8_0_31_iso : codeGraph 16 562995100411416235147305810822731103 ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective model_8_0_31_map model_8_0_31_bijective
  map_rel_iff' := by intro u v; exact model_8_0_31_adj u v

def complement0_map : Fin 16 → Fin 16 := ![8, 14, 11, 12, 10, 9, 15, 13, 7, 2, 6, 3, 1, 5, 4, 0]
theorem complement0_bijective : Function.Bijective complement0_map := by decide +kernel
theorem complement0_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode0).Adj (complement0_map u) (complement0_map v) ↔
      (codeGraph 16 coreCode0)ᶜ.Adj u v := by decide +kernel
def complement0_iso : (codeGraph 16 coreCode0)ᶜ ≃g codeGraph 16 coreCode0 where
  toEquiv := Equiv.ofBijective complement0_map complement0_bijective
  map_rel_iff' := by intro u v; exact complement0_adj u v

def complement1_map : Fin 16 → Fin 16 := ![9, 10, 14, 12, 15, 11, 13, 8, 1, 4, 7, 3, 5, 2, 6, 0]
theorem complement1_bijective : Function.Bijective complement1_map := by decide +kernel
theorem complement1_adj : ∀ u v : Fin 16,
    (codeGraph 16 coreCode1).Adj (complement1_map u) (complement1_map v) ↔
      (codeGraph 16 coreCode1)ᶜ.Adj u v := by decide +kernel
def complement1_iso : (codeGraph 16 coreCode1)ᶜ ≃g codeGraph 16 coreCode1 where
  toEquiv := Equiv.ofBijective complement1_map complement1_bijective
  map_rel_iff' := by intro u v; exact complement1_adj u v

end
end CochromaticTwenty.CoreWitnesses
#print axioms CochromaticTwenty.CoreWitnesses.complement0_iso
#print axioms CochromaticTwenty.CoreWitnesses.complement1_iso

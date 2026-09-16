import Jsp937.Definitions

/-! Positive affine normalization of the extreme nodes of an ordered family. -/
namespace Jsp937
open Randy1153
open Randy1153.DeBoorPinkus
noncomputable section

/-- The positive affine order isomorphism carrying `a` to `-1` and `b` to `1`. -/
def intervalNormalize (a b : ℝ) (hab : a < b) : ℝ ≃o ℝ where
  toFun t := 2 * (t - a) / (b - a) - 1
  invFun y := a + (b - a) * (y + 1) / 2
  left_inv t := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp [hba]
    ring
  right_inv y := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp [hba]
    ring
  map_rel_iff' := by
    intro x y
    change 2 * (x - a) / (b - a) - 1 ≤ 2 * (y - a) / (b - a) - 1 ↔ x ≤ y
    rw [sub_le_sub_iff_right]
    rw [div_le_div_iff₀ (sub_pos.mpr hab) (sub_pos.mpr hab)]
    constructor <;> intro h <;> nlinarith

@[simp]
lemma intervalNormalize_apply (a b : ℝ) (hab : a < b) (t : ℝ) :
    intervalNormalize a b hab t = 2 * (t - a) / (b - a) - 1 :=
  rfl

@[simp]
lemma intervalNormalize_left (a b : ℝ) (hab : a < b) :
    intervalNormalize a b hab a = -1 := by
  simp [intervalNormalize]

@[simp]
lemma intervalNormalize_right (a b : ℝ) (hab : a < b) :
    intervalNormalize a b hab b = 1 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  rw [intervalNormalize_apply]
  field_simp [hba]
  ring

/-- The positive affine map normalizing the two extreme points of `nodes`. -/
def normalizingMap {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ ≃o ℝ :=
  intervalNormalize
    (nodes.point (endpointLeftIndex d))
    (nodes.point (endpointRightIndex d))
    (nodes.strictMono (by simp [Fin.lt_def]))

@[simp]
lemma normalizingMap_left {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    normalizingMap nodes (nodes.point (endpointLeftIndex d)) = -1 := by
  simp [normalizingMap]

@[simp]
lemma normalizingMap_right {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    normalizingMap nodes (nodes.point (endpointRightIndex d)) = 1 := by
  apply intervalNormalize_right

/-- Normalize an ordered family by sending its extreme points to `-1` and `1`. -/
def normalizedNodes {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    EndpointArray d (-1) 1 where
  point i := normalizingMap nodes (nodes.point i)
  injective := (normalizingMap nodes).injective.comp nodes.injective
  mem_Icc i := by
    constructor
    · rw [← normalizingMap_left nodes]
      exact (normalizingMap nodes).monotone <|
        nodes.strictMono.monotone (Fin.zero_le i)
    · rw [← normalizingMap_right nodes]
      exact (normalizingMap nodes).monotone <|
        nodes.strictMono.monotone (Fin.le_last i)
  strictMono := (normalizingMap nodes).strictMono.comp nodes.strictMono
  left_endpoint := normalizingMap_left nodes
  right_endpoint := normalizingMap_right nodes

@[simp]
lemma normalizedNodes_point {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 2)) :
    (normalizedNodes nodes).point i = normalizingMap nodes (nodes.point i) :=
  rfl

end
end Jsp937

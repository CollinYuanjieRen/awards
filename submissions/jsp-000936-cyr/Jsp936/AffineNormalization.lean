import Jsp936.NormalizedNodes

/-! Preservation of Lagrange and Lebesgue data under positive affine normalization. -/
namespace Jsp936
open Randy1153 Set
open Randy1153.DeBoorPinkus
noncomputable section

/-- The normalizing map scales every difference by the same positive constant. -/
private lemma normalizingMap_sub {d : ℕ} (nodes : OrderedNodes (d + 2)) (x y : ℝ) :
    normalizingMap nodes x - normalizingMap nodes y =
      2 / (nodes.point (endpointRightIndex d) - nodes.point (endpointLeftIndex d)) *
        (x - y) := by
  simp only [normalizingMap, intervalNormalize_apply]
  ring

/-- Normalizing both the nodes and the evaluation point preserves each fundamental function. -/
theorem lagrangeFundamental_normalized {d : ℕ} (nodes : OrderedNodes (d + 2))
    (k : Fin (d + 2)) (t : ℝ) :
    lagrangeFundamental (normalizedNodes nodes).toNodeFamily k (normalizingMap nodes t) =
      lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  simp only [lagrangeFundamental, normalizedNodes_point]
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  have hnodes : nodes.point k - nodes.point i ≠ 0 := by
    exact sub_ne_zero.mpr (nodes.injective.ne hik.symm)
  have hextremes :
      nodes.point (endpointRightIndex d) - nodes.point (endpointLeftIndex d) ≠ 0 := by
    exact sub_ne_zero.mpr (nodes.injective.ne (by simp [endpointLeftIndex,
      endpointRightIndex]))
  rw [normalizingMap_sub nodes t (nodes.point i),
    normalizingMap_sub nodes (nodes.point k) (nodes.point i)]
  field_simp [hnodes, hextremes]

/-- Normalizing the nodes and argument preserves the full Lebesgue function. -/
theorem lebesgueFunction_normalized {d : ℕ} (nodes : OrderedNodes (d + 2)) (t : ℝ) :
    lebesgueFunction (normalizedNodes nodes).toNodeFamily (normalizingMap nodes t) =
      lebesgueFunction nodes.toNodeFamily t := by
  simp only [lebesgueFunction, lagrangeFundamental_normalized]

/-- Positive affine normalization carries every interval Lebesgue maximum to its image interval. -/
theorem lebesgueOn_normalized {d : ℕ} (nodes : OrderedNodes (d + 2)) (a b : ℝ) :
    lebesgueOn (normalizedNodes nodes).toNodeFamily
        (normalizingMap nodes a) (normalizingMap nodes b) =
      lebesgueOn nodes.toNodeFamily a b := by
  unfold lebesgueOn
  rw [← (normalizingMap nodes).image_Icc, image_image]
  congr 1
  apply image_congr
  intro t _
  exact lebesgueFunction_normalized nodes t

/-- Positive affine normalization preserves every actual closed-gap maximum. -/
theorem gapHeight_normalized {d : ℕ} (nodes : OrderedNodes (d + 2))
    (g : Fin (d + 1)) :
    gapHeight (normalizedNodes nodes).toOrderedNodes g = gapHeight nodes g := by
  simpa only [gapHeight, normalizedNodes_point] using
    lebesgueOn_normalized nodes (nodes.point (gapLeftIndex g))
      (nodes.point (gapRightIndex g))

end
end Jsp936

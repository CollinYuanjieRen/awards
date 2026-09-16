import Jsp937.AffineNormalization
import Randy1153.DeBoorPinkus.Simplex
import Mathlib.Analysis.Polynomial.Basic

/-! Contracting a normalized array while preserving its internal gap heights. -/
namespace Jsp937
open Randy1153
open Randy1153.DeBoorPinkus
open Polynomial
noncomputable section

/-- Contract a normalized endpoint array by a factor in `(0, 1]`. -/
def contractedNodes {d : ℕ} (opt : EndpointArray d (-1) 1) (r : ℝ)
    (hr : 0 < r) (hrone : r ≤ 1) : OrderedNodes (d + 2) where
  point i := r * opt.point i
  injective := by
    intro i j hij
    apply opt.injective
    exact mul_left_cancel₀ hr.ne' hij
  mem_Icc i := by
    constructor
    · have hi := (opt.mem_Icc i).1
      nlinarith
    · have hi := (opt.mem_Icc i).2
      nlinarith
  strictMono := fun _ _ hij ↦ mul_lt_mul_of_pos_left (opt.strictMono hij) hr

@[simp]
lemma contractedNodes_point {d : ℕ} (opt : EndpointArray d (-1) 1) (r : ℝ)
    (hr : 0 < r) (hrone : r ≤ 1) (i : Fin (d + 2)) :
    (contractedNodes opt r hr hrone).point i = r * opt.point i :=
  rfl

/-- Normalizing a positive contraction recovers the original endpoint array. -/
theorem normalizedNodes_contractedNodes {d : ℕ} (opt : EndpointArray d (-1) 1) (r : ℝ)
    (hr : 0 < r) (hrone : r ≤ 1) :
    normalizedNodes (contractedNodes opt r hr hrone) = opt := by
  apply EndpointArray.ext
  intro i
  simp only [normalizedNodes_point, normalizingMap, intervalNormalize_apply,
    contractedNodes_point]
  rw [opt.left_endpoint, opt.right_endpoint]
  field_simp [hr.ne']
  ring

/-- The normalizing map of a positive contraction is division by its scale. -/
theorem normalizingMap_contractedNodes {d : ℕ} (opt : EndpointArray d (-1) 1) (r t : ℝ)
    (hr : 0 < r) (hrone : r ≤ 1) :
    normalizingMap (contractedNodes opt r hr hrone) t = t / r := by
  simp only [normalizingMap, intervalNormalize_apply, contractedNodes_point]
  rw [opt.left_endpoint, opt.right_endpoint]
  field_simp [hr.ne']
  ring

/-- Arbitrarily large exterior values can be obtained without changing any normalized internal
gap height. -/
theorem exists_nodes_preserving_heights_with_large_tails {d : ℕ}
    (opt : EndpointArray d (-1) 1) (H : ℝ) :
    ∃ nodes : OrderedNodes (d + 2),
      (∀ g : Fin (d + 1), gapHeight nodes g = opt.height g) ∧
      H ≤ lebesgueFunction nodes.toNodeFamily (-1) ∧
      H ≤ lebesgueFunction nodes.toNodeFamily 1 := by
  let k : Fin (d + 2) := 0
  let p : ℝ[X] := lagrangeBasis opt.toNodeFamily k
  let q : ℝ[X] := p.comp (-X)
  have hpdeg : 0 < p.degree := by
    rw [show p.degree = (d + 2 - 1 : ℕ) by
      exact degree_lagrangeBasis opt.toNodeFamily k]
    exact_mod_cast Nat.succ_pos d
  have hqdeg : 0 < q.degree := by
    rw [← natDegree_pos_iff_degree_pos, show q = p.comp (-X) from rfl, natDegree_comp]
    simp [p, natDegree_lagrangeBasis, natDegree_neg, natDegree_X]
  have hp_large := (abs_tendsto_atTop p hpdeg).eventually_ge_atTop H
  have hq_large := (abs_tendsto_atTop q hqdeg).eventually_ge_atTop H
  obtain ⟨R, hR, hpR, hqR⟩ :=
    ((Filter.eventually_ge_atTop (2 : ℝ)).and (hp_large.and hq_large)).exists
  have hRpos : 0 < R := by linarith
  have hrpos : 0 < R⁻¹ := inv_pos.mpr hRpos
  have hrone : R⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hRpos]
    linarith
  let nodes : OrderedNodes (d + 2) := contractedNodes opt R⁻¹ hrpos hrone
  have hnormalized : normalizedNodes nodes = opt :=
    normalizedNodes_contractedNodes opt R⁻¹ hrpos hrone
  have hsingle : ∀ t : ℝ, |p.eval t| ≤ lebesgueFunction opt.toNodeFamily t := by
    intro t
    rw [lebesgueFunction]
    rw [show p.eval t = lagrangeFundamental opt.toNodeFamily k t by
      exact lagrangeBasis_eval opt.toNodeFamily k t]
    have hmem : k ∈ (Finset.univ : Finset (Fin (d + 2))) := Finset.mem_univ k
    exact Finset.single_le_sum (fun i _ ↦ abs_nonneg
      (lagrangeFundamental opt.toNodeFamily i t)) hmem
  refine ⟨nodes, ?_, ?_, ?_⟩
  · intro g
    rw [← gapHeight_normalized nodes g, hnormalized]
    rfl
  · calc
      H ≤ |p.eval (-R)| := by
        simpa [q, eval_comp] using hqR
      _ ≤ lebesgueFunction opt.toNodeFamily (-R) := hsingle (-R)
      _ = lebesgueFunction nodes.toNodeFamily (-1) := by
        rw [← lebesgueFunction_normalized nodes (-1), hnormalized]
        congr 2
        simp [nodes, normalizingMap_contractedNodes opt R⁻¹ (-1) hrpos hrone]
  · calc
      H ≤ |p.eval R| := hpR
      _ ≤ lebesgueFunction opt.toNodeFamily R := hsingle R
      _ = lebesgueFunction nodes.toNodeFamily 1 := by
        rw [← lebesgueFunction_normalized nodes 1, hnormalized]
        congr 2
        simp [nodes, normalizingMap_contractedNodes opt R⁻¹ 1 hrpos hrone]

end
end Jsp937

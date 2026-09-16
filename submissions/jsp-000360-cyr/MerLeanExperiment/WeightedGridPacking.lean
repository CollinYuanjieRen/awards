import MerLeanExperiment.FiniteOrderTransfer
import MerLeanExperiment.GridForwardPacking
import MerLeanExperiment.GridPrefixAll
import MerLeanExperiment.GridWeightSums
import Mathlib.Tactic

namespace Erdos441

theorem sum_int_interval_subtype (a b : ℤ) (f : ℤ → ℝ) :
    (∑ i : {i : ℤ // i ∈ Finset.Icc a b}, f i.val) =
      ∑ i ∈ Finset.Icc a b, f i := by
  classical
  change (∑ i ∈ (Finset.Icc a b).attach, f i.val) = _
  exact Finset.sum_attach (Finset.Icc a b) f

theorem sum_int_interval_prefix (a b t : ℤ) (hat : a ≤ t) (htb : t ≤ b)
    (f : ℤ → ℝ) :
    (∑ i : {i : ℤ // i ∈ Finset.Icc a b}, if i.val ≤ t then f i.val else 0) =
      ∑ i ∈ Finset.Icc a t, f i := by
  classical
  change (∑ i : {i : ℤ // i ∈ Finset.Icc a b},
    if i.val ≤ t then f i.val else 0) = _
  calc
    _ = ∑ i ∈ Finset.Icc a b, if i ≤ t then f i else 0 :=
      sum_int_interval_subtype a b (fun i => if i ≤ t then f i else 0)
    _ = _ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro i hi
        rfl

theorem eventually_weighted_grid_packing :
    ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T : ℤ, (L : ℤ) - 1 ≤ T →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ,
        LcmBounded N A →
        (∑ i ∈ Finset.Icc (-T) T, gridBeta (gridQ L) L i *
          intervalDensity A (gridQ L ^ i) (gridQ L ^ (i + 1))
            (Real.sqrt (N : ℝ))) ≤
          (1 + epsilon) * ∑ j ∈ Finset.Icc (-T) (L : ℤ),
            gridDelta (gridQ L) L j := by
  classical
  obtain ⟨L0, hL0, hprefix⟩ := grid_prefix_all
  refine ⟨L0, hL0, ?_⟩
  intro L hL T hT epsilon hepsilon
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, _, _, _⟩ := grid_ratio_spec L hLone
  let I := {i : ℤ // i ∈ Finset.Icc (-T) T}
  let J := {j : ℤ // j ∈ Finset.Icc (-T) (L : ℤ)}
  let row : I → ℤ := fun i => i.val
  let col : J → ℤ := fun j => j.val
  have hrow : Function.Injective row := fun _ _ h => Subtype.ext h
  obtain ⟨N0, hpack⟩ := eventually_uniform_grid_forward_packing
    (I := I) (J := J) (gridQ L) hq L col row hrow epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hN A hA
  let alpha : I → ℝ := fun i => intervalDensity A (gridQ L ^ i.val)
    (gridQ L ^ (i.val + 1)) (Real.sqrt (N : ℝ))
  let beta : I → ℝ := fun i => gridBeta (gridQ L) L i.val
  let k : J → I → ℕ := fun j i => gridCount (gridQ L) L i.val j.val
  let delta : J → ℝ := fun j => gridDelta (gridQ L) L j.val
  have halpha : ∀ i, 0 ≤ alpha i := by
    intro i
    unfold alpha intervalDensity
    apply div_nonneg
    · positivity
    · apply mul_nonneg
      · have hp : 0 < gridQ L ^ i.val := zpow_pos (by linarith) _
        have hadd : gridQ L ^ (i.val + 1) = gridQ L ^ i.val * gridQ L := by
          rw [zpow_add₀ (by linarith : gridQ L ≠ 0), zpow_one]
        rw [hadd]
        nlinarith
      · exact Real.sqrt_nonneg _
  obtain ⟨hbeta0, hdelta0⟩ := grid_weights_nonneg (gridQ L) hq L
  have hbeta : ∀ i, 0 ≤ beta i := fun i => hbeta0 i.val
  have hdelta : ∀ j, 0 ≤ delta j := fun j => hdelta0 j.val
  have hpref : ∀ t : I,
      (∑ i : I, if i ≤ t then beta i else 0) ≤
        ∑ i : I, if i ≤ t then ∑ j : J, delta j * k j i else 0 := by
    intro t
    have htlo : -T ≤ t.val := (Finset.mem_Icc.mp t.property).1
    have hthi : t.val ≤ T := (Finset.mem_Icc.mp t.property).2
    have hh := hprefix L hL T hT t.val htlo hthi
    unfold gridBetaPrefix gridCapacityPrefix at hh
    change
      (∑ i : I, if i.val ≤ t.val then gridBeta (gridQ L) L i.val else 0) ≤
        ∑ i : I, if i.val ≤ t.val then
          ∑ j : J, gridDelta (gridQ L) L j.val *
            gridCount (gridQ L) L i.val j.val else 0
    have hinner (i : I) :
        (∑ j : J, gridDelta (gridQ L) L j.val *
          gridCount (gridQ L) L i.val j.val) =
        ∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta (gridQ L) L j *
          gridCount (gridQ L) L i.val j := by
      simpa only [J] using sum_int_interval_subtype (-T) (L : ℤ)
        (fun j => gridDelta (gridQ L) L j *
          gridCount (gridQ L) L i.val j)
    simp_rw [hinner]
    rw [sum_int_interval_prefix (-T) T t.val htlo hthi
      (fun i => gridBeta (gridQ L) L i)]
    rw [sum_int_interval_prefix (-T) T t.val htlo hthi
      (fun i => ∑ j ∈ Finset.Icc (-T) (L : ℤ),
        gridDelta (gridQ L) L j * gridCount (gridQ L) L i j)]
    exact hh
  have hmoves : ∀ j (phi : I → I), (∀ i, i ≤ phi i) →
      (∑ i : I, (k j i : ℝ) * alpha (phi i)) ≤ 1 + epsilon := by
    intro j phi hphi
    exact hpack N hN A hA j phi (fun i => hphi i)
  have hh := weighted_finite_order_transfer alpha beta k delta (1 + epsilon)
    halpha hbeta hdelta hpref hmoves
  change (∑ i : I, gridBeta (gridQ L) L i.val *
      intervalDensity A (gridQ L ^ i.val) (gridQ L ^ (i.val + 1))
        (Real.sqrt (N : ℝ))) ≤
      (1 + epsilon) * ∑ j : J, gridDelta (gridQ L) L j.val at hh
  calc
    (∑ i ∈ Finset.Icc (-T) T, gridBeta (gridQ L) L i *
        intervalDensity A (gridQ L ^ i) (gridQ L ^ (i + 1))
          (Real.sqrt (N : ℝ))) =
      ∑ i : I, gridBeta (gridQ L) L i.val *
        intervalDensity A (gridQ L ^ i.val) (gridQ L ^ (i.val + 1))
          (Real.sqrt (N : ℝ)) := by
        symm
        simpa only [I] using sum_int_interval_subtype (-T) T
          (fun i => gridBeta (gridQ L) L i *
            intervalDensity A (gridQ L ^ i) (gridQ L ^ (i + 1))
              (Real.sqrt (N : ℝ)))
    _ ≤ (1 + epsilon) * ∑ j : J, gridDelta (gridQ L) L j.val := hh
    _ = (1 + epsilon) * ∑ j ∈ Finset.Icc (-T) (L : ℤ),
        gridDelta (gridQ L) L j := by
      rw [sum_int_interval_subtype]

end Erdos441

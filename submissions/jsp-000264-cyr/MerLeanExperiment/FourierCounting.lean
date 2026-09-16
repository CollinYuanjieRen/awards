import MerLeanExperiment.FourierBridge
import MerLeanExperiment.FiniteCounting

namespace ReciprocalSquares

theorem real_sum_centeredProduct
    (D : Finset ℕ) (m k : ℕ) [NeZero m] (r : ℚ) (p : ℝ)
    (hD : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ m)
    (hW : recipSumQ D < 1) (hrW : r < recipSumQ D)
    (hk : (k : ℚ) = (m : ℚ) * r)
    (hp : p * (recipSumQ D : ℝ) = (r : ℝ)) :
    (∑ h : ZMod m, centeredProduct D p h.valMinAbs).re =
      (m : ℝ) *
        ∑ S ∈ D.powerset.filter (fun S => recipSumQ S = r), bernWeight D S p := by
  classical
  have hfilter :
      D.powerset.filter (fun S => (∑ d ∈ S, ((m / d : ℕ) : ZMod m)) =
        (k : ZMod m)) = D.powerset.filter (fun S => recipSumQ S = r) := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hS, hmod⟩
      exact ⟨hS, (modular_subset_sum_iff_exact D S m k r hD hdiv
        (Finset.mem_powerset.mp hS) hW (hrW.trans hW) hk).mp hmod⟩
    · rintro ⟨hS, hexact⟩
      exact ⟨hS, (modular_subset_sum_iff_exact D S m k r hD hdiv
        (Finset.mem_powerset.mp hS) hW (hrW.trans hW) hk).mpr hexact⟩
  have heq : (∑ h : ZMod m, centeredProduct D p h.valMinAbs) =
      ∑ h : ZMod m,
        modularProduct D (fun d => ((m / d : ℕ) : ZMod m)) (k : ZMod m) p h := by
    apply Finset.sum_congr rfl
    intro h _
    exact centeredProduct_eq_modularProduct D m k r p hD hdiv hk hp h
  rw [heq, sum_modularProduct, hfilter]
  simp

/-- The analytic estimates in the last two hypotheses are internal proof
obligations of the square construction, not assumptions of the partition root. -/
theorem exists_two_subsets_of_centered_sum
    (D : Finset ℕ) (m k : ℕ) [NeZero m] (r : ℚ) (p : ℝ)
    (hD : ∀ d ∈ D, 0 < d) (hdiv : ∀ d ∈ D, d ∣ m)
    (hW : recipSumQ D < 1) (hr0 : 0 < r) (hrW : r < recipSumQ D)
    (hk : (k : ℚ) = (m : ℚ) * r)
    (hp : p = (r : ℝ) / (recipSumQ D : ℝ))
    (hFourier : (1 / 2 : ℝ) ≤
      (∑ h : ZMod m, centeredProduct D p h.valMinAbs).re)
    (hAtom : (max p (1 - p)) ^ D.card < 1 / (2 * (m : ℝ))) :
    ∃ S ⊆ D, ∃ T ⊆ D,
      S ≠ T ∧ recipSumQ S = r ∧ recipSumQ T = r := by
  classical
  have hWpos : (0 : ℝ) < (recipSumQ D : ℝ) := by exact_mod_cast hr0.trans hrW
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hrlt : (r : ℝ) < (recipSumQ D : ℝ) := by exact_mod_cast hrW
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]
    exact (div_lt_one hWpos).mpr hrlt |>.le
  have hpmul : p * (recipSumQ D : ℝ) = (r : ℝ) :=
    (eq_div_iff (ne_of_gt hWpos)).mp hp
  have hm : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  let F := D.powerset.filter (fun S => recipSumQ S = r)
  let B := (max p (1 - p)) ^ D.card
  have hmass : 1 / (2 * (m : ℝ)) ≤ ∑ S ∈ F, bernWeight D S p := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).mpr
    have hid := real_sum_centeredProduct D m k r p hD hdiv hW hrW hk hpmul
    change (∑ h : ZMod m, centeredProduct D p h.valMinAbs).re =
      (m : ℝ) * ∑ S ∈ F, bernWeight D S p at hid
    nlinarith
  have hB : 0 ≤ B := pow_nonneg (hp0.trans (le_max_left _ _)) _
  have hweight : ∀ S ∈ F, bernWeight D S p ≤ B := by
    intro S hS
    exact bernWeight_le_max_pow D S p
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) hp0 hp1
  obtain ⟨S, hS, T, hT, hne⟩ := two_elements_of_sum_gt_bound F
    (fun S => bernWeight D S p) B hB hweight (hAtom.trans_le hmass)
  exact ⟨S, Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1,
    T, Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1,
    hne, (Finset.mem_filter.mp hS).2, (Finset.mem_filter.mp hT).2⟩

end ReciprocalSquares

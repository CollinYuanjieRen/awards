import Jsp1010.Defs

/-!
# JSP-001010 / Erdős #1205 — Chernoff bound on the product space

A finite, elementary Chernoff bound: all "probabilities" are counts over the finset
`choices N = Π_{i : Fin N} range (i+1)`.
-/

open Finset Real

namespace Erdos1205

theorem card_choices (N : ℕ) : (choices N).card = ∏ i : Fin N, (i.1 + 1) := by
  rw [choices, Fintype.card_piFinset]
  simp

theorem mem_choices {N : ℕ} {a : Fin N → ℕ} : a ∈ choices N ↔ ∀ i, a i < i.1 + 1 := by
  simp [choices, Fintype.mem_piFinset]

private lemma card_choices_real (N : ℕ) :
    ((choices N).card : ℝ) = ∏ i : Fin N, ((i.1 : ℝ) + 1) := by
  rw [card_choices]
  push_cast
  ring

private lemma exp_smallCount_eq (N m : ℕ) (θ : ℝ) (a : Fin N → ℕ) :
    Real.exp (-θ * (smallCount N a m : ℝ))
      = ∏ i : Fin N, Real.exp (-θ * (if m % (i.1 + 1) = a i then (1 : ℝ) else 0)) := by
  have hs : (smallCount N a m : ℝ)
      = ∑ i : Fin N, (if m % (i.1 + 1) = a i then (1 : ℝ) else 0) := by
    rw [smallCount, Finset.card_filter]
    push_cast
    rfl
  rw [hs, Finset.mul_sum, Real.exp_sum]

/-- The moment generating function factorises: for fixed `m`,
`∑_{a ∈ choices N} exp(−θ · smallCount N a m) = ∏_i (i + exp(−θ))`. -/
theorem sum_exp_smallCount (N : ℕ) (m : ℕ) (θ : ℝ) :
    ∑ a ∈ choices N, Real.exp (-θ * (smallCount N a m : ℝ)) =
      ∏ i : Fin N, ((i.1 : ℝ) + Real.exp (-θ)) := by
  have h1 : ∑ a ∈ choices N, Real.exp (-θ * (smallCount N a m : ℝ))
      = ∑ a ∈ Fintype.piFinset (fun i : Fin N => range (i.1 + 1)),
          ∏ i : Fin N, Real.exp (-θ * (if m % (i.1 + 1) = a i then (1 : ℝ) else 0)) := by
    rw [choices]
    exact Finset.sum_congr rfl fun a _ => exp_smallCount_eq N m θ a
  have h2 := Finset.prod_univ_sum (fun i : Fin N => range (i.1 + 1))
      (fun (i : Fin N) (r : ℕ) => Real.exp (-θ * (if m % (i.1 + 1) = r then (1 : ℝ) else 0)))
  rw [h1, ← h2]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hb : m % (i.1 + 1) ∈ range (i.1 + 1) :=
    mem_range.mpr (Nat.mod_lt _ (Nat.succ_pos _))
  rw [← Finset.add_sum_erase _ _ hb]
  have hrest : ∀ r ∈ (range (i.1 + 1)).erase (m % (i.1 + 1)),
      Real.exp (-θ * (if m % (i.1 + 1) = r then (1 : ℝ) else 0)) = 1 := by
    intro r hr
    have hne : ¬ (m % (i.1 + 1) = r) := fun h => (Finset.mem_erase.mp hr).1 h.symm
    simp [hne]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem hb,
    Finset.card_range]
  simp
  ring

private lemma harmonic_real (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ i : Fin N, ((i.1 : ℝ) + 1)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1)⁻¹) N, harmonic]
  push_cast
  rfl

/-- `∏_i (i + e^{−θ}) ≤ (∏_i (i+1)) · exp(−(1 − e^{−θ}) · harmonic N)`. -/
theorem prod_le (N : ℕ) (θ : ℝ) :
    ∏ i : Fin N, ((i.1 : ℝ) + Real.exp (-θ)) ≤
      (∏ i : Fin N, ((i.1 : ℝ) + 1)) * Real.exp (-(1 - Real.exp (-θ)) * (harmonic N : ℝ)) := by
  have hepos : (0 : ℝ) < Real.exp (-θ) := Real.exp_pos _
  have step : ∀ i : Fin N, ((i.1 : ℝ) + Real.exp (-θ)) ≤
      ((i.1 : ℝ) + 1) * Real.exp ((Real.exp (-θ) - 1) * ((i.1 : ℝ) + 1)⁻¹) := by
    intro i
    have hpos : (0 : ℝ) < (i.1 : ℝ) + 1 := by positivity
    have hle := Real.add_one_le_exp ((Real.exp (-θ) - 1) * ((i.1 : ℝ) + 1)⁻¹)
    have heq : ((i.1 : ℝ) + Real.exp (-θ))
        = ((i.1 : ℝ) + 1) * ((Real.exp (-θ) - 1) * ((i.1 : ℝ) + 1)⁻¹ + 1) := by
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hle hpos.le
  calc ∏ i : Fin N, ((i.1 : ℝ) + Real.exp (-θ))
      ≤ ∏ i : Fin N, (((i.1 : ℝ) + 1) * Real.exp ((Real.exp (-θ) - 1) * ((i.1 : ℝ) + 1)⁻¹)) :=
        Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => step i)
    _ = (∏ i : Fin N, ((i.1 : ℝ) + 1)) *
          Real.exp (∑ i : Fin N, (Real.exp (-θ) - 1) * ((i.1 : ℝ) + 1)⁻¹) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ = (∏ i : Fin N, ((i.1 : ℝ) + 1)) *
          Real.exp (-(1 - Real.exp (-θ)) * (harmonic N : ℝ)) := by
        rw [← Finset.mul_sum, ← harmonic_real N]
        congr 2
        ring

/-- Markov/Chernoff: the number of choices for which `m` is covered fewer than
`harmonic N − t` times. -/
theorem card_bad_le (N : ℕ) (hN : 1 ≤ N) (m : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (ht2 : t ≤ 2 * (harmonic N : ℝ)) :
    (((choices N).filter fun a => (smallCount N a m : ℝ) < (harmonic N : ℝ) - t).card : ℝ) ≤
      (choices N).card * Real.exp (-(t ^ 2) / (4 * (harmonic N : ℝ))) := by
  set μ : ℝ := ((harmonic N : ℚ) : ℝ) with hμdef
  have hμpos : 0 < μ := by
    have h := harmonic_pos (n := N) (by omega)
    rw [hμdef]
    exact_mod_cast h
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = t / (2 * μ) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]
    exact ht2
  have hteq : t = 2 * μ * θ := by rw [hθ]; field_simp
  set B := (choices N).filter fun a => (smallCount N a m : ℝ) < μ - t with hB
  have h1 : (B.card : ℝ) * Real.exp (-θ * (μ - t))
      ≤ ∑ a ∈ B, Real.exp (-θ * (smallCount N a m : ℝ)) := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun a ha => ?_
    have hlt := (Finset.mem_filter.mp ha).2
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h2 : ∑ a ∈ B, Real.exp (-θ * (smallCount N a m : ℝ))
      ≤ ∑ a ∈ choices N, Real.exp (-θ * (smallCount N a m : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => (Real.exp_pos _).le
  have h3 : ∑ a ∈ choices N, Real.exp (-θ * (smallCount N a m : ℝ))
      ≤ ((choices N).card : ℝ) * Real.exp (-(1 - Real.exp (-θ)) * μ) := by
    rw [sum_exp_smallCount, card_choices_real]
    exact prod_le N θ
  have habs := Real.abs_exp_sub_one_sub_id_le (x := -θ)
    (by rw [abs_neg, abs_of_nonneg hθ0]; exact hθ1)
  have he1 : Real.exp (-θ) - 1 ≤ θ ^ 2 - θ := by
    have h := (abs_le.mp habs).2
    nlinarith [h]
  have hexppos : (0 : ℝ) < Real.exp (-θ * (μ - t)) := Real.exp_pos _
  have key : ((choices N).card : ℝ) * Real.exp (-(1 - Real.exp (-θ)) * μ)
      ≤ ((choices N).card : ℝ) * Real.exp (-(t ^ 2) / (4 * μ)) * Real.exp (-θ * (μ - t)) := by
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
    rw [hteq]
    have hrw : -((2 * μ * θ) ^ 2) / (4 * μ) = -(μ * θ ^ 2) := by
      field_simp
      ring
    rw [hrw]
    nlinarith [mul_le_mul_of_nonneg_right he1 hμpos.le]
  have hfinal := (h1.trans (h2.trans h3)).trans key
  exact le_of_mul_le_mul_right hfinal hexppos

/-- Averaging over `m ∈ X`: some choice has few badly covered `m`. -/
theorem exists_choice_few_bad (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t)
    (ht2 : t ≤ 2 * (harmonic N : ℝ)) (X : Finset ℕ) :
    ∃ a ∈ choices N, ((X.filter fun m => (smallCount N a m : ℝ) < (harmonic N : ℝ) - t).card : ℝ) ≤
      X.card * Real.exp (-(t ^ 2) / (4 * (harmonic N : ℝ))) := by
  have hne : (choices N).Nonempty := by
    rw [choices, Fintype.piFinset_nonempty]
    exact fun i => ⟨0, mem_range.mpr (Nat.succ_pos _)⟩
  have key : ∑ a ∈ choices N,
        ((X.filter fun m => (smallCount N a m : ℝ) < (harmonic N : ℝ) - t).card : ℝ)
      ≤ ∑ _a ∈ choices N,
        ((X.card : ℝ) * Real.exp (-(t ^ 2) / (4 * (harmonic N : ℝ)))) := by
    have hswap : ∑ a ∈ choices N,
          ((X.filter fun m => (smallCount N a m : ℝ) < (harmonic N : ℝ) - t).card : ℝ)
        = ∑ m ∈ X,
          (((choices N).filter fun a => (smallCount N a m : ℝ) < (harmonic N : ℝ) - t).card : ℝ) := by
      simp_rw [Finset.card_filter]
      push_cast
      exact Finset.sum_comm
    rw [hswap, Finset.sum_const, nsmul_eq_mul]
    calc ∑ m ∈ X,
          (((choices N).filter fun a => (smallCount N a m : ℝ) < (harmonic N : ℝ) - t).card : ℝ)
        ≤ ∑ _m ∈ X, ((choices N).card : ℝ) * Real.exp (-(t ^ 2) / (4 * (harmonic N : ℝ))) :=
          Finset.sum_le_sum fun m _ => card_bad_le N hN m ht ht2
      _ = ((choices N).card : ℝ) *
            ((X.card : ℝ) * Real.exp (-(t ^ 2) / (4 * (harmonic N : ℝ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  obtain ⟨a, ha, hle⟩ := Finset.exists_le_of_sum_le hne key
  exact ⟨a, ha, hle⟩

end Erdos1205


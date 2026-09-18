import Jsp1010.Upper
import Jsp1010.Chernoff
import Jsp1010.Greedy
import Jsp1010.Asymptotics

/-!
# JSP-001010 / Erdős #1205 — `F(x) ∼ log x`

`F(x)` is the largest `k` such that one class `a_n (mod n)` can be chosen for every `n ≤ x` so that
every `m ≤ x` lies in at least `k` of the classes.  The resolution recorded on erdosproblems.com/1205:

* `F(x) ≤ log x + O(1)` (pigeonhole: the classes cover `[1, x]` at most `x·H_x + x` times in total);
* `F(x) ≥ log x − O(√(log x · log log x))` (random classes for `n ≤ x/2`, a Chernoff bound, and a
  greedy repair of the few badly covered `m` with the moduli `x/2 < n ≤ x`).

Hence `F(x)/log x → 1`.
-/

open Finset Filter Topology Real

namespace Erdos1205

/-- Lower bound with the explicit constant `6`. -/
theorem F_ge_log_sub_six_sqrt : ∀ᶠ x : ℕ in atTop,
    Real.log x - 6 * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ F x := by
  classical
  filter_upwards [eventually_facts] with x hx
  set N := x / 2 with hN
  set μ : ℝ := (harmonic N : ℝ) with hμ
  set t : ℝ := Real.sqrt (8 * μ * Real.log (Real.log x)) with ht
  obtain ⟨hx2, hN1, hμlow, hμup, ht0, ht2, hexp, hcap, hfinal⟩ := hx N μ t rfl rfl rfl
  have hx1 : 1 ≤ x := by omega
  have hNx : N ≤ x := Nat.div_le_self x 2
  -- the random part: a choice with few badly covered `m`
  obtain ⟨a, ha, hbad⟩ := exists_choice_few_bad N hN1 ht0 ht2 (Icc 1 x)
  set B : Finset ℕ := (Icc 1 x).filter fun m => (smallCount N a m : ℝ) < μ - t with hB
  set L : ℕ := ⌊μ - t⌋₊ with hL
  have hL_le : ∀ r : ℕ, μ - t ≤ (r : ℝ) → L ≤ r := by
    intro r hr
    rcases le_or_gt 0 (μ - t) with h | h
    · exact Nat.floor_le_of_le hr |>.trans le_rfl
    · rw [hL, Nat.floor_of_nonpos h.le]; exact Nat.zero_le r
  have hL_ge : μ - t - 1 ≤ L := by
    rcases le_or_gt 0 (μ - t) with h | h
    · exact (Nat.sub_one_lt_floor _).le
    · rw [hL, Nat.floor_of_nonpos h.le]; push_cast; linarith
  have hLμ : (L : ℝ) ≤ μ + 1 := by
    rcases le_or_gt 0 (μ - t) with h | h
    · have := Nat.floor_le h; linarith
    · rw [hL, Nat.floor_of_nonpos h.le]; push_cast; linarith
  -- the repair capacity
  have hcard : B.card * L ≤ (Ioc N x).card := by
    have h1 : (B.card : ℝ) ≤ (x : ℝ) * ((Real.log x) ^ 2)⁻¹ := by
      have := hbad
      simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
      calc (B.card : ℝ) ≤ (x : ℝ) * Real.exp (-(t ^ 2) / (4 * μ)) := this
        _ ≤ (x : ℝ) * ((Real.log x) ^ 2)⁻¹ := by gcongr
    have h2 : ((Ioc N x).card : ℝ) = ((x - N : ℕ) : ℝ) := by simp [Nat.card_Ioc]
    have h3 : (B.card : ℝ) * L ≤ ((Ioc N x).card : ℝ) := by
      rw [h2]
      calc (B.card : ℝ) * L ≤ ((x : ℝ) * ((Real.log x) ^ 2)⁻¹) * (μ + 1) := by
            apply mul_le_mul h1 hLμ (Nat.cast_nonneg _)
            exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (sq_nonneg _))
        _ ≤ ((x - N : ℕ) : ℝ) := hcap
    exact_mod_cast h3
  obtain ⟨g, hg⟩ := exists_repair x N L B hcard
  -- the combined choice of classes
  let a' : ℕ → ℕ := fun n => if h : 1 ≤ n ∧ n ≤ N then a ⟨n - 1, by omega⟩ else g n
  have ha' : ∀ i : Fin N, a' (i.1 + 1) = a i := by
    intro i
    have hc : 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ N := ⟨by omega, by omega⟩
    have h1 : a' (i.1 + 1) = a ⟨i.1 + 1 - 1, by omega⟩ := by
      simp only [a', hc, and_self, dite_true]
    rw [h1]
    congr 1
  have hsmall : ∀ m, ((Icc 1 N).filter fun n => m % n = a' n % n).card = smallCount N a m :=
    fun m => card_filter_Icc_eq_smallCount N a ha a' ha' m
  have hbig : ∀ m ∈ B, L ≤ ((Ioc N x).filter fun n => m % n = a' n % n).card := by
    intro m hm
    have := hg m hm
    refine le_trans this (le_of_eq ?_)
    congr 1
    apply Finset.filter_congr
    intro n hn
    have hn' : ¬ (1 ≤ n ∧ n ≤ N) := by
      rw [Finset.mem_Ioc] at hn; omega
    simp only [a', hn', dite_false]
  -- every `m ∈ [1, x]` is covered at least `L` times
  have hcover : ∀ m ∈ Icc 1 x, L ≤ coverCount a' x m := by
    intro m hm
    rw [coverCount_split x N hNx a' m]
    by_cases hmB : m ∈ B
    · exact le_add_left (hbig m hmB)
    · have hnot : μ - t ≤ (smallCount N a m : ℝ) := by
        by_contra hlt
        exact hmB (Finset.mem_filter.mpr ⟨hm, not_le.mp hlt⟩)
      have hL' : L ≤ smallCount N a m := hL_le _ hnot
      rw [hsmall m]
      exact le_add_right hL'
  have hF : L ≤ F x := le_F_of_forall hx1 a' hcover
  calc Real.log x - 6 * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ μ - t - 1 := hfinal
    _ ≤ L := hL_ge
    _ ≤ F x := by exact_mod_cast hF

theorem F_ge_log_sub_sqrt : ∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
    Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ F x :=
  ⟨6, F_ge_log_sub_six_sqrt⟩

theorem F_div_log_tendsto_one : Tendsto (fun x : ℕ => (F x : ℝ) / Real.log x) atTop (𝓝 1) :=
  tendsto_div_log_of_bounds (fun x => (F x : ℝ)) 6
    (Filter.eventually_atTop.2 ⟨1, fun x hx => F_le_log_add_two x hx⟩) F_ge_log_sub_six_sqrt

theorem F_sub_log_isBigO :
    (fun x : ℕ => (F x : ℝ) - Real.log x) =O[atTop]
      fun x : ℕ => Real.sqrt (Real.log x * Real.log (Real.log x)) :=
  isBigO_sub_log_of_bounds (fun x => (F x : ℝ)) 6
    (Filter.eventually_atTop.2 ⟨1, fun x hx => F_le_log_add_two x hx⟩) F_ge_log_sub_six_sqrt

/-- **Erdős #1205**: `log x − O(√(log x · log log x)) ≤ F(x) ≤ log x + O(1)`, hence `F(x) ∼ log x`. -/
theorem erdos_1205 :
    (∀ x : ℕ, 1 ≤ x → (F x : ℝ) ≤ Real.log x + 2) ∧
    (∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
      Real.log x - C * Real.sqrt (Real.log x * Real.log (Real.log x)) ≤ F x) ∧
    Tendsto (fun x : ℕ => (F x : ℝ) / Real.log x) atTop (𝓝 1) :=
  ⟨F_le_log_add_two, F_ge_log_sub_sqrt, F_div_log_tendsto_one⟩

end Erdos1205

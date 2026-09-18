import Jsp799.Assembly

/-!
# JSP-000799 / Erdős #960 — the threshold is not `o(n²)`

For `r ≥ 3`, `k ≥ 4` and `n ≥ 72` the configuration `config m s` (`n = 6m + s`) has `n` points,
no four collinear, no all-ordinary triple, and at least `3m² − 3ms` ordinary lines; hence every
forcing threshold exceeds `3m² − 3ms`, i.e. `f_{r,k}(n) ≥ 3m² − 3ms + 1 ≥ n²/12 − 10n/3`.
Consequently `f_{r,k}(n)` is neither `o(n²)` nor `O(n)` (APSSV26b, Theorem 2.1).
-/

open Finset Filter Asymptotics

namespace Erdos960

/-- `ordCount A ≤ n²` where `n = |A|`: a crude bound making the forcing set nonempty. -/
theorem ordCount_le_sq (A : Finset Point) : ordCount A ≤ A.card ^ 2 := by
  classical
  unfold ordCount
  calc (A.sym2.filter (IsOrdinaryLine A)).card ≤ A.sym2.card := Finset.card_filter_le _ _
    _ = (A.card + 1).choose 2 := Finset.card_sym2 A
    _ = (A.card + 1) * A.card / 2 := Nat.choose_two_right _
    _ ≤ A.card ^ 2 := by
      have : (A.card + 1) * A.card ≤ 2 * A.card ^ 2 := by nlinarith
      omega

theorem forces_sq_add_one (r k n : ℕ) : Forces r k n (n ^ 2 + 1) := by
  intro A hA _ ht
  have := ordCount_le_sq A
  rw [hA] at this
  omega

theorem forcesSet_nonempty (r k n : ℕ) : {t : ℕ | Forces r k n t}.Nonempty :=
  ⟨n ^ 2 + 1, forces_sq_add_one r k n⟩

/-- A configuration with no all-ordinary `r`-subset pushes the threshold above its ordinary count. -/
theorem le_f_of_counterexample {r k n : ℕ} {A : Finset Point} (hA : A.card = n)
    (hk : NoKCollinear A k) (hr : ¬ HasOrdinaryClique A r) : ordCount A + 1 ≤ f r k n := by
  refine le_csInf (forcesSet_nonempty r k n) ?_
  intro t ht
  by_contra hlt
  exact hr (ht A hA hk (by omega))

/-- Proposition 2.5(3) of APSSV26b plus `f = F + 1`: `f_{r,k}(n) ≥ 3m² − 3ms + 1` where `n = 6m + s`. -/
theorem f_ge_nat {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    3 * m ^ 2 - 3 * m * s + 1 ≤ f r k (6 * m + s) := by
  have h1 := le_f_of_counterexample (card_config hm hs) (noKCollinear_config hm hs hk)
    (not_hasOrdinaryClique_config hm hs hr)
  have h2 := ordCount_config_ge hm hs
  omega

/-- Theorem 2.1 of APSSV26b: `f_{r,k}(n) ≥ n²/12 − 10n/3` for `n ≥ 72`. -/
theorem f_ge {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) (n : ℕ) (hn : 72 ≤ n) :
    (n : ℝ) ^ 2 / 12 - 10 / 3 * n ≤ f r k n := by
  obtain ⟨m, s, hm, hs, rfl⟩ : ∃ m s : ℕ, 12 ≤ m ∧ s ≤ 5 ∧ n = 6 * m + s :=
    ⟨n / 6, n % 6, by omega, by omega, by omega⟩
  have h := f_ge_nat hr hk hm hs
  have hms : 3 * m * s ≤ 3 * m ^ 2 := by nlinarith
  have hcast : ((3 * m ^ 2 - 3 * m * s : ℕ) : ℝ) + 1 ≤ f r k (6 * m + s) := by exact_mod_cast h
  rw [Nat.cast_sub hms] at hcast
  push_cast at hcast ⊢
  have hs' : (s : ℝ) ≤ 5 := by exact_mod_cast hs
  have hm' : (12 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- `f_{r,k}(n) ≥ n²/24` for `n ≥ 80`. -/
theorem f_ge_sq_div (r k : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ 2 / 24 ≤ f r k n := by
  filter_upwards [eventually_ge_atTop 80] with n hn
  have h := f_ge hr hk n (by omega)
  have hn' : (80 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem f_not_isLittleO (r k : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ¬ ((fun n : ℕ => (f r k n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ 2) := by
  intro h
  have hbound := h.def (by norm_num : (0 : ℝ) < 1 / 48)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hbound.and (f_ge_sq_div r k hr hk))
  obtain ⟨h1, h2⟩ := hN (max N 80) (le_max_left _ _)
  set n := max N 80 with hn
  have hle : 80 ≤ n := le_max_right _ _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity)] at h1
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (80 : ℝ) ≤ n := by exact_mod_cast hle
    positivity
  nlinarith

theorem f_not_isBigO_linear (r k : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ¬ ((fun n : ℕ => (f r k n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ)) := by
  intro h
  obtain ⟨C, hC⟩ := h.isBigOWith
  have hev := hC.bound.and (f_ge_sq_div r k hr hk)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  set n := max N (⌈24 * C⌉₊ + 80) with hn
  obtain ⟨h1, h2⟩ := hN n (le_max_left _ _)
  have hn80 : (80 : ℝ) ≤ n := by
    have : 80 ≤ n := le_trans (by omega) (le_max_right N _)
    exact_mod_cast this
  have hnC : 24 * C < n := by
    have h1' : ⌈24 * C⌉₊ + 80 ≤ n := le_max_right _ _
    have h2' : 24 * C ≤ ⌈24 * C⌉₊ := Nat.le_ceil _
    have : ((⌈24 * C⌉₊ + 80 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1'
    push_cast at this
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _)] at h1
  nlinarith

/-- **Erdős #960** (Alexeev–Putterman–Sawhney–Sellke–Valiant, Theorem 2.1): for every fixed
`r ≥ 3`, `k ≥ 4`, the threshold `f_{r,k}(n)` is at least `n²/12 − 10n/3` for `n ≥ 72`; in
particular it is neither `o(n²)` nor `O(n)`. -/
theorem erdos_960 (r k : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) :
    (∀ n : ℕ, 72 ≤ n → (n : ℝ) ^ 2 / 12 - 10 / 3 * n ≤ (f r k n : ℝ)) ∧
    ¬ ((fun n : ℕ => (f r k n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ 2) ∧
    ¬ ((fun n : ℕ => (f r k n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ)) :=
  ⟨fun n hn => f_ge hr hk n hn, f_not_isLittleO r k hr hk, f_not_isBigO_linear r k hr hk⟩

end Erdos960

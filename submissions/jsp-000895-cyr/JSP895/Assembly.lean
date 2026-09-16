import JSP895.External.Erdos207
import JSP895.Bridge

/-!
# Erdős Problem 1076 (JSP-000895): `ex₃(n, 𝓕_{≤k}) ~ n² / 6`

For every `k ≥ 4`, the maximum number `exLe k n` of triples of a three-uniform hypergraph on
`n` vertices in which no `j - 2` triples span at most `j` vertices for all `4 ≤ j ≤ k`
satisfies

* `3 * exLe k n ≤ n.choose 2` for every `n` (elementary: no pair lies in two triples), and
* `(n - 3).choose 2 ≤ 3 * exLe k n` for all sufficiently large `n`, from the high-girth Steiner
  triple systems of Kwan–Sah–Sawhney–Simkin (`Erdos207.erdos_207`, third-party formalization),
  transported from the largest admissible order `m ≤ n`;

hence `exLe k n / n² → 1/6`, i.e. `exLe k n ~ n²/6`.  This is the locally sparse reading of
Problem 1076 (Bohman–Warnke 2019, Glock–Kühn–Lo–Osthus 2020).
-/

open Finset Filter Topology

namespace Erdos1076Sparse

/-- Lower bound: for `n` large, the largest admissible `m ∈ [n-3, n]` carries a Steiner
triple system with no `j - 2` triples on `j` vertices for `4 ≤ j ≤ k`. -/
theorem choose_le_three_mul_exLe (k : ℕ) (hk : 4 ≤ k) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe k n := by
  obtain ⟨N₀, hN₀⟩ := Erdos207.erdos_207 (k - 2) (by omega)
  refine ⟨N₀ + 3, fun n hn => ?_⟩
  obtain ⟨m, hm, hmn, hnm⟩ := exists_admissible_near n (by omega)
  obtain ⟨H, hSt, hLS⟩ := hN₀ m (by omega) hm
  have hcard := three_mul_card_of_isSteiner hSt
  have hFF : FamilyFree k H := familyFree_of_locallySparse hLS
  have hle := card_le_exLe (familyFree_castSystem hmn hFF)
  rw [card_castSystem] at hle
  calc (n - 3).choose 2 ≤ m.choose 2 := Nat.choose_le_choose 2 (by omega)
    _ = 3 * H.card := hcard.symm
    _ ≤ 3 * exLe k n := by omega

/-- Erdős Problem 1076 (locally sparse reading): for every `k ≥ 4`,
`ex₃(n, 𝓕_{≤k}) ~ n² / 6`, with explicit two-sided binomial bounds. -/
theorem erdos_1076_locally_sparse_of_le (k : ℕ) (hk : 4 ≤ k) :
    (∀ n : ℕ, 3 * exLe k n ≤ n.choose 2) ∧
      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe k n) ∧
      Tendsto (fun n : ℕ => (exLe k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) := by
  obtain ⟨N₀, hN₀⟩ := choose_le_three_mul_exLe k hk
  refine ⟨fun n => three_mul_exLe_le_choose k n hk, ⟨N₀, hN₀⟩, ?_⟩
  exact tendsto_div_sq_of_choose_bounds (fun n => three_mul_exLe_le_choose k n hk) hN₀

/-- Erdős Problem 1076 (locally sparse reading), premise-free form: for every `k`, with
`k + 4` ranging over all configuration sizes at least four, `ex₃(n, 𝓕_{≤k+4}) ~ n² / 6`
with explicit two-sided binomial bounds. -/
theorem erdos_1076_locally_sparse (k : ℕ) :
    (∀ n : ℕ, 3 * exLe (k + 4) n ≤ n.choose 2) ∧
      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe (k + 4) n) ∧
      Tendsto (fun n : ℕ => (exLe (k + 4) n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) :=
  erdos_1076_locally_sparse_of_le (k + 4) (by omega)

/-- The same statement in Mathlib's asymptotic-equivalence notation. -/
theorem exLe_isEquivalent (k : ℕ) (hk : 4 ≤ k) :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (exLe k n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 2 / 6) := by
  have h := (erdos_1076_locally_sparse_of_le k hk).2.2
  have hv : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 / 6 ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  rw [Asymptotics.isEquivalent_iff_tendsto_one hv]
  have h6 : Tendsto (fun n : ℕ => 6 * ((exLe k n : ℝ) / (n : ℝ) ^ 2)) atTop (𝓝 1) := by
    have := h.const_mul 6
    norm_num at this
    exact this
  refine h6.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [Pi.div_apply]
  field_simp

end Erdos1076Sparse

import Proof.Defs

/-!
# Erdős Problem 295: the two estimates behind the Erdős–Straus lower bound

* For `N ≥ 1`, a set of `k` distinct natural numbers all `≥ N` has reciprocal sum at most
  `∑_{i < k} 1 / (N + i)` (remove the maximum, which is at least `N + k - 1`, and induct).
* `∑_{i < k} 1 / (N + i) ≤ 1 / N + log (N + k - 1) - log N` for `N ≥ 1`, `k ≥ 1`, since
  `1 / (m + 1) ≤ log (m + 1) - log m` for `m ≥ 1`.
-/

open Finset

namespace Erdos295

/-- A finite set of `k` distinct naturals, all `≥ N`, has an element `≥ N + k - 1`
(indeed its maximum is). -/
theorem exists_ge_add_card_sub_one {N : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, N ≤ d)
    (hne : D.Nonempty) : N + D.card - 1 ≤ D.max' hne := by
  have hsub : D ⊆ Finset.Icc N (D.max' hne) := fun d hd =>
    Finset.mem_Icc.2 ⟨hD d hd, Finset.le_max' D d hd⟩
  have hcard : D.card ≤ (Finset.Icc N (D.max' hne)).card := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hpos : 0 < D.card := Finset.card_pos.2 hne
  omega

/-- Auxiliary form of `sum_inv_le_harmonic`, phrased so that the induction is on the
cardinality of `D`. -/
private theorem sum_inv_le_harmonic_aux (N : ℕ) (hN : 1 ≤ N) :
    ∀ (n : ℕ) (D : Finset ℕ), D.card = n → (∀ d ∈ D, N ≤ d) →
      ∑ d ∈ D, (1 : ℝ) / d ≤ ∑ i ∈ range n, (1 : ℝ) / (N + i) := by
  intro n
  induction n with
  | zero =>
    intro D hcard _
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    simp
  | succ n ih =>
    intro D hcard hD
    have hne : D.Nonempty := Finset.card_pos.1 (by omega)
    have hmem : D.max' hne ∈ D := D.max'_mem hne
    have hcard' : (D.erase (D.max' hne)).card = n := by
      rw [Finset.card_erase_of_mem hmem, hcard]
      omega
    have hD' : ∀ d ∈ D.erase (D.max' hne), N ≤ d := fun d hd =>
      hD d (Finset.mem_of_mem_erase hd)
    have hIH := ih (D.erase (D.max' hne)) hcard' hD'
    have hsplit : ∑ d ∈ D.erase (D.max' hne), (1 : ℝ) / d + (1 : ℝ) / (D.max' hne)
        = ∑ d ∈ D, (1 : ℝ) / d :=
      Finset.sum_erase_add D (fun d => (1 : ℝ) / d) hmem
    have hmax : N + n ≤ D.max' hne := by
      have := exists_ge_add_card_sub_one hD hne
      omega
    have hmaxR : (N : ℝ) + (n : ℝ) ≤ ((D.max' hne : ℕ) : ℝ) := by exact_mod_cast hmax
    have hposR : (0 : ℝ) < (N : ℝ) + (n : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      positivity
    have hinv : (1 : ℝ) / ((D.max' hne : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + (n : ℝ)) :=
      one_div_le_one_div_of_le hposR hmaxR
    rw [Finset.sum_range_succ, ← hsplit]
    linarith

/-- Reciprocal sums of `k` distinct naturals `≥ N` are bounded by the harmonic block
`∑_{i < k} 1 / (N + i)`. -/
theorem sum_inv_le_harmonic (N : ℕ) (hN : 1 ≤ N) (D : Finset ℕ) (hD : ∀ d ∈ D, N ≤ d) :
    ∑ d ∈ D, (1 : ℝ) / d ≤ ∑ i ∈ range D.card, (1 : ℝ) / (N + i) :=
  sum_inv_le_harmonic_aux N hN D.card D rfl hD

/-- `1 / (m + 1) ≤ log (m + 1) - log m` for real `m ≥ 1`. -/
theorem inv_add_one_le_log_sub (m : ℝ) (hm : 1 ≤ m) :
    1 / (m + 1) ≤ Real.log (m + 1) - Real.log m := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hm0 hm1)
  rw [Real.log_div (ne_of_gt hm0) (ne_of_gt hm1)] at h
  have hid : m / (m + 1) - 1 = -(1 / (m + 1)) := by
    field_simp
    ring
  linarith [hid ▸ h]

/-- The harmonic block is bounded by `1 / N + log (N + k - 1) - log N` (`N ≥ 1`, `k ≥ 1`). -/
theorem harmonic_le_log (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    ∑ i ∈ range k, (1 : ℝ) / (N + i) ≤ 1 / N + Real.log (N + k - 1) - Real.log N := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  induction k, hk using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_one]
    norm_num
  | succ k hk ih =>
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hstep := inv_add_one_le_log_sub ((N : ℝ) + (k : ℝ) - 1) (by linarith)
    have he : (N : ℝ) + (k : ℝ) - 1 + 1 = (N : ℝ) + (k : ℝ) := by ring
    rw [he] at hstep
    have hlog : Real.log ((N : ℝ) + ((k + 1 : ℕ) : ℝ) - 1)
        = Real.log ((N : ℝ) + (k : ℝ)) := by
      norm_num
      congr 1
      ring
    rw [Finset.sum_range_succ, hlog]
    linarith

end Erdos295

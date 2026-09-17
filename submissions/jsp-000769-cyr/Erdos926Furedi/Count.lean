import Erdos926Furedi.Rich
import Erdos926Furedi.Turan

/-! Double counting of poor pairs and the final edge bound. -/

namespace Erdos926

open SimpleGraph Finset

/-- `x ^ (3/2)` is the square root of `x ^ 3` for nonnegative `x`. -/
private lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = Real.sqrt (x ^ 3) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
  norm_num

set_option linter.unusedVariables false in
/-- Every ordered poor pair `(u, v)` is counted once for each common neighbour `x`, and has fewer
than `T` of them.  (The hypothesis `1 ≤ T` is part of the frozen statement but is not needed:
`codeg < T` already forces `codeg ≤ T - 1` in `ℕ`.) -/
theorem sum_poorOrd_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : ℕ) (hT : 1 ≤ T) :
    ∑ x, poorOrd G T x ≤ (T - 1) * (Fintype.card V * (Fintype.card V - 1)) := by
  classical
  -- Rewrite each `poorOrd G T x` as a sum over all ordered pairs of distinct vertices.
  have key : ∀ x : V, poorOrd G T x =
      ∑ uv ∈ (Finset.univ : Finset V).offDiag,
        (if uv.1 ∈ G.neighborFinset x ∧ uv.2 ∈ G.neighborFinset x ∧
            codeg G uv.1 uv.2 < T then 1 else 0) := by
    intro x
    have hsub : (G.neighborFinset x).offDiag ⊆ (Finset.univ : Finset V).offDiag := by
      intro uv huv
      rw [Finset.mem_offDiag] at huv ⊢
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, huv.2.2⟩
    have hz : ∀ uv ∈ (Finset.univ : Finset V).offDiag,
        uv ∉ (G.neighborFinset x).offDiag →
        (if uv.1 ∈ G.neighborFinset x ∧ uv.2 ∈ G.neighborFinset x ∧
          codeg G uv.1 uv.2 < T then (1 : ℕ) else 0) = 0 := by
      intro uv huv hnot
      have hne : uv.1 ≠ uv.2 := (Finset.mem_offDiag.1 huv).2.2
      refine ite_eq_right ?_
      rintro ⟨h1, h2, _⟩
      exact hnot (Finset.mem_offDiag.2 ⟨h1, h2, hne⟩)
    rw [poorOrd, Finset.card_filter, ← Finset.sum_subset hsub hz]
    refine Finset.sum_congr rfl ?_
    intro uv huv
    rw [Finset.mem_offDiag] at huv
    simp [huv.1, huv.2.1]
  -- For a fixed pair, the number of common neighbours is the codegree.
  have inner : ∀ uv : V × V, uv ∈ (Finset.univ : Finset V).offDiag →
      (∑ x : V, (if uv.1 ∈ G.neighborFinset x ∧ uv.2 ∈ G.neighborFinset x ∧
        codeg G uv.1 uv.2 < T then 1 else 0)) ≤ T - 1 := by
    intro uv _
    by_cases hc : codeg G uv.1 uv.2 < T
    · have hset : (Finset.univ : Finset V).filter
          (fun x => uv.1 ∈ G.neighborFinset x ∧ uv.2 ∈ G.neighborFinset x ∧
            codeg G uv.1 uv.2 < T)
          = G.neighborFinset uv.1 ∩ G.neighborFinset uv.2 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
          SimpleGraph.mem_neighborFinset, hc, and_true]
        exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
      have := Finset.card_filter
        (fun x : V => uv.1 ∈ G.neighborFinset x ∧ uv.2 ∈ G.neighborFinset x ∧
          codeg G uv.1 uv.2 < T) (Finset.univ : Finset V)
      rw [hset] at this
      rw [← this]
      exact Nat.le_sub_one_of_lt hc
    · simp [hc]
  calc ∑ x, poorOrd G T x
      = ∑ x : V, ∑ uv ∈ (Finset.univ : Finset V).offDiag,
          (if uv.1 ∈ G.neighborFinset x ∧ uv.2 ∈ G.neighborFinset x ∧
            codeg G uv.1 uv.2 < T then 1 else 0) := Finset.sum_congr rfl (fun x _ => key x)
    _ = ∑ uv ∈ (Finset.univ : Finset V).offDiag, ∑ x : V,
          (if uv.1 ∈ G.neighborFinset x ∧ uv.2 ∈ G.neighborFinset x ∧
            codeg G uv.1 uv.2 < T then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ _uv ∈ (Finset.univ : Finset V).offDiag, (T - 1) := Finset.sum_le_sum inner
    _ = ((Finset.univ : Finset V).offDiag.card) * (T - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = (T - 1) * (Fintype.card V * (Fintype.card V - 1)) := by
          rw [Finset.offDiag_card, Finset.card_univ, Nat.mul_comm]
          congr 1
          cases h : Fintype.card V with
          | zero => simp
          | succ m => simp [Nat.succ_mul, Nat.mul_succ]

/-- Cauchy–Schwarz for the degree sequence. -/
theorem sum_degree_sq_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hV : 0 < Fintype.card V) :
    4 * (G.edgeFinset.card : ℝ) ^ 2 / Fintype.card V ≤ ∑ x, (G.degree x : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hcs : (∑ x : V, (G.degree x : ℝ)) ^ 2
      ≤ (Fintype.card V : ℝ) * ∑ x : V, (G.degree x : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V))
      (f := fun x => (G.degree x : ℝ))
    simpa [Finset.card_univ] using this
  have hsum : (∑ x : V, (G.degree x : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    have h := G.sum_degrees_eq_twice_card_edges
    have : ((∑ x : V, G.degree x : ℕ) : ℝ) = ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at this
    simpa using this
  rw [hsum] at hcs
  rw [div_le_iff₀ hn]
  nlinarith [hcs]

/-- The number of pairs `{i, j} ⊆ Fin k` is at most `k²`. -/
theorem card_pairIdx_le (k : ℕ) : Fintype.card (PairIdx k) ≤ k * k := by
  have h := Fintype.card_subtype_le (fun p : Fin k × Fin k => p.1 < p.2)
  simpa [Fintype.card_prod, Fintype.card_fin] using h

/-- Füredi's bound with explicit constants: an `H_k`-free graph on `n` vertices has at most
`k^{3/2} n^{3/2} + k n` edges. -/
theorem card_edgeFinset_le_of_free (k : ℕ) (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : (Hk k).Free G) :
    (G.edgeFinset.card : ℝ) ≤
      (k : ℝ) ^ (3 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) + k * Fintype.card V := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
  · -- No vertices: no edges, and the right-hand side is `0`.
    have : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    have hzero : G.edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.eq_empty_of_forall_notMem ?_
      intro s _
      exact Sym2.ind (fun a _ => (IsEmpty.false a)) s
    rw [hzero, hV]
    norm_num
  -- Notation.
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  set e : ℝ := (G.edgeFinset.card : ℝ) with he_def
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn_def]; exact_mod_cast hV
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have he0 : (0 : ℝ) ≤ e := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hk1' : (0 : ℝ) < (k : ℝ) - 1 := lt_of_lt_of_le zero_lt_one hk1
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set S : ℝ := ∑ x : V, (G.degree x : ℝ) with hS_def
  -- Lower bound on the number of poor pairs (Turán).
  have hpoor : ∀ x : V, (G.degree x : ℝ) ^ 2 / ((k : ℝ) - 1) - G.degree x
      ≤ (poorOrd G (threshold k) x : ℝ) :=
    fun x => poorOrd_ge G k (threshold k) hk x (richGraph_cliqueFree k hk G hfree x)
  have hsum_poor : (∑ x : V, (G.degree x : ℝ) ^ 2) / ((k : ℝ) - 1) - 2 * e
      ≤ ((∑ x : V, poorOrd G (threshold k) x : ℕ) : ℝ) := by
    have h1 : ∑ x : V, ((G.degree x : ℝ) ^ 2 / ((k : ℝ) - 1) - G.degree x)
        ≤ ∑ x : V, (poorOrd G (threshold k) x : ℝ) := Finset.sum_le_sum (fun x _ => hpoor x)
    have hdeg : (∑ x : V, (G.degree x : ℝ)) = 2 * e := by
      have h := G.sum_degrees_eq_twice_card_edges
      have h' : ((∑ x : V, G.degree x : ℕ) : ℝ) = ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
      push_cast at h'
      rw [he_def]
      simpa using h'
    rw [Finset.sum_sub_distrib, hdeg, ← Finset.sum_div] at h1
    rw [Nat.cast_sum]
    exact h1
  -- Upper bound on the number of poor pairs (double counting).
  have hT1 : threshold k - 1 = Fintype.card (PairIdx k) + k := by
    simp [threshold]
  have hcount : (∑ x : V, poorOrd G (threshold k) x)
      ≤ (k * k + k) * (Fintype.card V * Fintype.card V) := by
    refine le_trans (sum_poorOrd_le G (threshold k) (by simp [threshold])) ?_
    refine Nat.mul_le_mul ?_ ?_
    · rw [hT1]
      exact Nat.add_le_add_right (card_pairIdx_le k) k
    · exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hcountR : ((∑ x : V, poorOrd G (threshold k) x : ℕ) : ℝ)
      ≤ ((k : ℝ) * k + k) * (n * n) := by
    have := (Nat.cast_le (α := ℝ)).2 hcount
    rw [hn_def]
    push_cast at this ⊢
    linarith
  -- Cauchy–Schwarz.
  have hCS : 4 * e ^ 2 / n ≤ ∑ x : V, (G.degree x : ℝ) ^ 2 := by
    rw [he_def, hn_def]
    exact sum_degree_sq_ge G hV
  set D : ℝ := ∑ x : V, (G.degree x : ℝ) ^ 2 with hD_def
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun x _ => by positivity)
  -- Combine: `4 e² ≤ (k-1) (k²+k) n³ + 2 (k-1) n e`.
  have hmain : 4 * e ^ 2 ≤ ((k : ℝ) - 1) * ((k : ℝ) * k + k) * n ^ 3 + 2 * ((k : ℝ) - 1) * n * e := by
    have h1 : D / ((k : ℝ) - 1) - 2 * e ≤ ((k : ℝ) * k + k) * (n * n) :=
      le_trans hsum_poor hcountR
    have h2 : D ≤ (((k : ℝ) * k + k) * (n * n) + 2 * e) * ((k : ℝ) - 1) := by
      have h1' : D / ((k : ℝ) - 1) ≤ ((k : ℝ) * k + k) * (n * n) + 2 * e := by linarith
      rwa [div_le_iff₀ hk1'] at h1'
    have h3 : 4 * e ^ 2 ≤ n * D := by
      rw [div_le_iff₀ hn0] at hCS
      linarith
    nlinarith [h3, h2, hn0.le, hk1'.le]
  by_cases hcase : e ≤ ((k : ℝ) - 1) * n
  · -- Few edges: `e ≤ k n`.
    have h1 : (0 : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) * n ^ (3 / 2 : ℝ) := by positivity
    nlinarith [hn0.le, hcase, h1]
  · -- Many edges: `e² ≤ k³ n³`.
    push Not at hcase
    have hepos : (0 : ℝ) < e := lt_trans (by positivity) hcase
    have hlt : ((k : ℝ) - 1) * n * e < e ^ 2 := by nlinarith [hepos, hcase]
    have hsq : e ^ 2 ≤ (k : ℝ) ^ 3 * n ^ 3 := by
      have hc : ((k : ℝ) - 1) * ((k : ℝ) * k + k) ≤ 2 * (k : ℝ) ^ 3 := by nlinarith [hkR]
      have hn3 : (0 : ℝ) < n ^ 3 := by positivity
      nlinarith [hmain, hlt, hn3, hc]
    have hkn : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hfinal : e ≤ Real.sqrt ((k : ℝ) ^ 3 * n ^ 3) := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq he0] at this
    have heq : (k : ℝ) ^ (3 / 2 : ℝ) * n ^ (3 / 2 : ℝ) = Real.sqrt ((k : ℝ) ^ 3 * n ^ 3) := by
      rw [rpow_three_halves hkn, rpow_three_halves hn0.le, ← Real.sqrt_mul (by positivity)]
    rw [heq]
    have : (0 : ℝ) ≤ (k : ℝ) * n := by positivity
    linarith

end Erdos926

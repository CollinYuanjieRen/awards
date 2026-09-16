import JSP518.External.Erdos88.Probability
import Mathlib

/-!
# Turán-type lower bounds on independent sets

This file proves the independent-set bounds used in the JKLY development.  The
route is the standard deletion argument: sample every vertex of a finset `S`
independently with a constant probability `p`, keep a sample whose value of
`|W| - e(G[W])` is at least the expectation `p|S| - p² e(G[S])`, and delete one
endpoint of every surviving edge.  Optimising `p` gives the edge-count form
`|S|² / (|S| + 4 e(G[S]))` of Turán's theorem.

The probability space is the explicit finite Bernoulli product of
`Erdos88.Probability`; no measure theory is involved.
-/

universe u

open scoped BigOperators

namespace JKLY

open Erdos88.Probability

/-- The number of edges of `G` with both endpoints in `S`. -/
def inducedEdges {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card

/-- A finset spans no edge exactly when it is independent. -/
lemma inducedEdges_eq_zero_iff {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    inducedEdges G W = 0 ↔ G.IsIndepSet (W : Set V) := by
  classical
  rw [inducedEdges, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x hx y hy hne hadj
    refine h (x := s(x, y)) (by simpa using hadj) ?_
    intro a ha
    rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp ha) with rfl | rfl
    · exact Finset.mem_coe.mp hx
    · exact Finset.mem_coe.mp hy
  · intro h e
    induction e using Sym2.ind with
    | _ x y =>
      intro he hsub
      have hadj : G.Adj x y := by simpa using he
      exact h (Finset.mem_coe.mpr (hsub (by simp))) (Finset.mem_coe.mpr (hsub (by simp)))
        hadj.ne hadj

/-- A finset spanning at least one edge contains two adjacent vertices. -/
lemma exists_adj_of_inducedEdges_ne_zero {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {W : Finset V} (h : inducedEdges G W ≠ 0) :
    ∃ x ∈ W, ∃ y ∈ W, G.Adj x y := by
  classical
  have hpos : 0 < (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ W).card :=
    Nat.pos_of_ne_zero h
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at he
  obtain ⟨he₁, he₂⟩ := he
  revert he₁ he₂
  induction e using Sym2.ind with
  | _ x y =>
    intro he₁ he₂
    exact ⟨x, he₂ (by simp), y, he₂ (by simp), by simpa using he₁⟩

/-- Deleting an endpoint of a spanned edge strictly decreases the spanned edge count. -/
lemma inducedEdges_erase_lt {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {W : Finset V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (hadj : G.Adj x y) :
    inducedEdges G (W.erase x) < inducedEdges G W := by
  classical
  have hsub : (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ W.erase x) ⊆
      G.edgeFinset.filter fun e ↦ e.toFinset ⊆ W := by
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans (Finset.erase_subset _ _)⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨s(x, y), ?_, ?_⟩)
  · simp only [Finset.mem_filter]
    refine ⟨by simpa using hadj, ?_⟩
    intro a ha
    rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp ha) with rfl | rfl
    · exact hx
    · exact hy
  · simp only [Finset.mem_filter, not_and]
    intro _ hcon
    exact Finset.notMem_erase x W (hcon (by simp))

/-- Delete one endpoint of every induced edge. -/
lemma exists_indepSet_subset_card_ge {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧
      (W.card : ℝ) - (inducedEdges G W : ℝ) ≤ I.card := by
  classical
  suffices h : ∀ n : ℕ, ∀ W : Finset V, inducedEdges G W ≤ n →
      ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧
        (W.card : ℝ) - (inducedEdges G W : ℝ) ≤ I.card by
    exact h (inducedEdges G W) W le_rfl
  intro n
  induction n with
  | zero =>
    intro W hW
    have h0 : inducedEdges G W = 0 := Nat.le_zero.mp hW
    exact ⟨W, Finset.Subset.refl W, (inducedEdges_eq_zero_iff G W).mp h0, by simp [h0]⟩
  | succ n ih =>
    intro W hW
    by_cases h0 : inducedEdges G W = 0
    · exact ⟨W, Finset.Subset.refl W, (inducedEdges_eq_zero_iff G W).mp h0, by simp [h0]⟩
    obtain ⟨x, hx, y, hy, hadj⟩ := exists_adj_of_inducedEdges_ne_zero G h0
    have hlt : inducedEdges G (W.erase x) < inducedEdges G W :=
      inducedEdges_erase_lt G hx hy hadj
    obtain ⟨I, hIsub, hIind, hIcard⟩ := ih (W.erase x) (by omega)
    refine ⟨I, hIsub.trans (Finset.erase_subset _ _), hIind, ?_⟩
    have hcard : (W.erase x).card + 1 = W.card := Finset.card_erase_add_one hx
    have h1 : ((W.erase x).card : ℝ) = (W.card : ℝ) - 1 := by
      rw [← hcard]
      push_cast
      ring
    have h2 : (inducedEdges G (W.erase x) : ℝ) + 1 ≤ (inducedEdges G W : ℝ) := by
      exact_mod_cast hlt
    linarith

/-- Some sample attains at least the expected value. -/
lemma exists_ge_expectation {V : Type u} [Fintype V] [DecidableEq V] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Finset V → ℝ) :
    ∃ W : Finset V, expectation p f ≤ f W := by
  classical
  obtain ⟨W, -, hW⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Finset V)) f ⟨∅, Finset.mem_univ _⟩
  refine ⟨W, ?_⟩
  calc expectation p f = ∑ X : Finset V, bernoulliWeight p X * f X := rfl
    _ ≤ ∑ X : Finset V, bernoulliWeight p X * f W :=
        Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left (hW X (Finset.mem_univ X))
          (bernoulliWeight_nonneg hp0 hp1 X)
    _ = f W := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

/-- Expected size of the sampled part of `S`. -/
lemma expectation_card_inter {V : Type u} [Fintype V] [DecidableEq V] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset V) :
    expectation p (fun W ↦ ((W ∩ S).card : ℝ)) = p * S.card := by
  classical
  have h : (fun W : Finset V ↦ ((W ∩ S).card : ℝ)) = fun W ↦ ∑ v ∈ S, bit v W := by
    funext W
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    push_cast
    simp [bit]
  rw [h, expectation_sum]
  simp [expectation_bit hp0 hp1, mul_comm]

/-- Expected number of edges spanned by the sampled part of `S`. -/
lemma expectation_inducedEdges_inter {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset V) :
    expectation p (fun W ↦ (inducedEdges G (W ∩ S) : ℝ)) =
      p ^ 2 * (inducedEdges G S : ℝ) := by
  classical
  have hfilter : ∀ W : Finset V, (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ W ∩ S) =
      (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).filter fun e ↦ e.toFinset ⊆ W := by
    intro W
    ext e
    simp only [Finset.mem_filter, Finset.subset_inter_iff]
    tauto
  have h : (fun W : Finset V ↦ (inducedEdges G (W ∩ S) : ℝ)) =
      fun W ↦ ∑ e ∈ G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S,
        monomial e.toFinset W := by
    funext W
    rw [inducedEdges, hfilter W, Finset.card_filter]
    push_cast
    simp [monomial]
  have hcard : ∀ e ∈ G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S,
      expectation p (monomial (V := V) e.toFinset) = p ^ 2 := by
    intro e he
    rw [expectation_monomial hp0 hp1,
      SimpleGraph.card_toFinset_mem_edgeFinset (G := G) ⟨e, (Finset.mem_filter.mp he).1⟩]
  calc expectation p (fun W ↦ (inducedEdges G (W ∩ S) : ℝ))
      = ∑ e ∈ G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S,
          expectation p (monomial (V := V) e.toFinset) := by
        rw [h, expectation_sum]
    _ = ∑ _e ∈ G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S, p ^ 2 :=
        Finset.sum_congr rfl hcard
    _ = p ^ 2 * (inducedEdges G S : ℝ) := by simp [inducedEdges, mul_comm]

/-- Sampling `S` at density `p` and deleting one endpoint of each surviving edge. -/
lemma exists_indepSet_subset_card_ge_of_prob {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧
      p * (S.card : ℝ) - p ^ 2 * (inducedEdges G S : ℝ) ≤ I.card := by
  classical
  obtain ⟨W, hW⟩ := exists_ge_expectation (V := V) hp0 hp1
    (fun W ↦ ((W ∩ S).card : ℝ) - (inducedEdges G (W ∩ S) : ℝ))
  rw [expectation_sub, expectation_card_inter hp0 hp1,
    expectation_inducedEdges_inter G hp0 hp1] at hW
  obtain ⟨I, hIsub, hIind, hIcard⟩ := exists_indepSet_subset_card_ge G (W ∩ S)
  exact ⟨I, hIsub.trans Finset.inter_subset_right, hIind, by linarith⟩

/-- The optimal sampling density for the deletion bound. -/
lemma exists_density {n e : ℝ} (hn : 0 ≤ n) (he : 0 ≤ e) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ n ^ 2 / (n + 4 * e) ≤ p * n - p ^ 2 * e := by
  rcases eq_or_lt_of_le hn with hn0 | hn0
  · exact ⟨0, le_rfl, zero_le_one, by simp [← hn0]⟩
  have hden : 0 < n + 4 * e := by linarith
  rcases le_or_gt (2 * e) n with hcase | hcase
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hcase he, mul_nonneg he hn]
  · have he0 : 0 < e := by linarith
    refine ⟨n / (2 * e), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]
      linarith
    · have hval : n / (2 * e) * n - (n / (2 * e)) ^ 2 * e = n ^ 2 / (4 * e) := by
        field_simp
        ring
      rw [hval, div_le_div_iff₀ hden (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg n) hn]

/-- Relative version on a vertex subset `S` with the edge count of `G.induce`/edges inside `S`. -/
theorem exists_indepSet_subset_card_ge_of_edges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧
      (S.card : ℝ) ^ 2 / ((S.card : ℝ) + 4 * (inducedEdges G S : ℝ)) ≤ I.card := by
  classical
  obtain ⟨p, hp0, hp1, hkey⟩ :=
    exists_density (n := (S.card : ℝ)) (e := (inducedEdges G S : ℝ))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨I, hIsub, hIind, hIcard⟩ := exists_indepSet_subset_card_ge_of_prob G S hp0 hp1
  exact ⟨I, hIsub, hIind, hkey.trans hIcard⟩

/-- All edges are spanned by the whole vertex set. -/
lemma inducedEdges_univ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : inducedEdges G Finset.univ = G.edgeFinset.card := by
  simp [inducedEdges]

/-- Turán, edge-count form: an independent set of size ≥ n² / (n + 4 e). -/
theorem exists_indepSet_card_ge {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      (Fintype.card V : ℝ) ^ 2 / ((Fintype.card V : ℝ) + 4 * G.edgeFinset.card) ≤ I.card := by
  classical
  obtain ⟨I, -, hIind, hIcard⟩ := exists_indepSet_subset_card_ge_of_edges G Finset.univ
  exact ⟨I, hIind, by rwa [inducedEdges_univ, Finset.card_univ] at hIcard⟩

/-- Turán, maximum-degree form: an independent set of size ≥ n / (1 + 2 d). -/
theorem exists_indepSet_card_ge_of_maxDegree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ} (hd : ∀ v : V, (G.degree v : ℝ) ≤ d)
    (hd0 : 0 ≤ d) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      (Fintype.card V : ℝ) / (1 + 2 * d) ≤ I.card := by
  classical
  obtain ⟨I, hIind, hIcard⟩ := exists_indepSet_card_ge G
  refine ⟨I, hIind, le_trans ?_ hIcard⟩
  have hsum : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) G.sum_degrees_eq_twice_card_edges
  have hbound : 4 * (G.edgeFinset.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) * d := by
    have hle : (∑ v : V, (G.degree v : ℝ)) ≤ ∑ _v : V, d :=
      Finset.sum_le_sum fun v _ ↦ hd v
    rw [hsum] at hle
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
    linarith
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hcard | hcard
  · simp [hcard]
  · have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hcard
    have he0 : (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) := Nat.cast_nonneg _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hbound hn0.le]

end JKLY

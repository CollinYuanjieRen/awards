import Proof.Defs

/-!
# Erdős Problem 1011: the extremal graph

For `n ≥ 5` let `a = ⌊(n - 1) / 2⌋`.  On `Fin n` take the complete bipartite graph between
`A = {0, …, a - 1}` and `B = {a, …, n - 2}`, delete the edge `{0, a}`, and join the last vertex
`n - 1` to `0` and `a`.  It has `a (n - 1 - a) + 1 = ⌊(n - 1)² / 4⌋ + 1` edges, is triangle-free, and
contains a `5`-cycle `(n-1), 0, y', x', a` with `x' ∈ A \ {0}`, `y' ∈ B \ {a}`, so it is not
`2`-colourable.
-/

open Finset SimpleGraph

namespace Erdos1011

/-- The half size `a = ⌊(n - 1) / 2⌋`. -/
def half (n : ℕ) : ℕ := (n - 1) / 2

/-- The underlying relation of the extremal graph (symmetrised by `SimpleGraph.fromRel`). -/
def extRel (n : ℕ) (i j : Fin n) : Prop :=
  (i.val < half n ∧ half n ≤ j.val ∧ j.val < n - 1 ∧ ¬ (i.val = 0 ∧ j.val = half n)) ∨
    (i.val = n - 1 ∧ (j.val = 0 ∨ j.val = half n))

instance (n : ℕ) : DecidableRel (extRel n) := fun i j => by unfold extRel; infer_instance

/-- The extremal graph. -/
def extremal (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel (extRel n)

instance (n : ℕ) : DecidableRel (extremal n).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (extRel n i j ∨ extRel n j i)))

/-- The defining relation of the extremal graph, read off the vertex values. -/
private def extRelVal (n i j : ℕ) : Prop :=
  (i < half n ∧ half n ≤ j ∧ j < n - 1 ∧ ¬ (i = 0 ∧ j = half n)) ∨
    (i = n - 1 ∧ (j = 0 ∨ j = half n))

/-- Adjacency in the extremal graph, expressed through the vertex values. -/
private theorem adj_iff {n : ℕ} (i j : Fin n) :
    (extremal n).Adj i j ↔
      i.val ≠ j.val ∧ (extRelVal n i.val j.val ∨ extRelVal n j.val i.val) := by
  simp only [extremal, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h ↦ h1 (Fin.val_injective h), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h ↦ h1 (congrArg Fin.val h), h2⟩

/-- The neighbours of `v`, listed by their values. -/
private theorem mem_nbhd_iff {n : ℕ} (v : Fin n) (m : ℕ) :
    (∃ h : m < n, (extremal n).Adj v ⟨m, h⟩) ↔
      m < n ∧ v.val ≠ m ∧ (extRelVal n v.val m ∨ extRelVal n m v.val) :=
  ⟨fun ⟨h, ha⟩ ↦ ⟨h, (adj_iff v ⟨m, h⟩).mp ha⟩, fun ⟨h, ha⟩ ↦ ⟨h, (adj_iff v ⟨m, h⟩).mpr ha⟩⟩

/-- The degree of `v` is the size of any finset listing the values of its neighbours. -/
private theorem degree_eq_card {n : ℕ} (v : Fin n) (s : Finset ℕ)
    (hs : ∀ m : ℕ, m ∈ s ↔ ∃ h : m < n, (extremal n).Adj v ⟨m, h⟩) :
    (extremal n).degree v = #s := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun (j : Fin n) _ ↦ j.val) (fun j hj ↦ ?_) (fun j₁ _ j₂ _ h ↦ ?_)
    (fun m hm ↦ ?_)
  · rw [SimpleGraph.mem_neighborFinset] at hj
    exact (hs j.val).mpr ⟨j.isLt, hj⟩
  · exact Fin.val_injective h
  · obtain ⟨h, hadj⟩ := (hs m).mp hm
    refine ⟨⟨m, h⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj

/-- The degree of the extremal graph at a vertex, as a function of its value. -/
private def degVal (n m : ℕ) : ℕ :=
  if m = n - 1 then 2 else if m < half n then n - 1 - half n else half n

/-- Every vertex of the extremal graph has the degree predicted by `degVal`. -/
private theorem degree_eq {n : ℕ} (hn : 5 ≤ n) (v : Fin n) :
    (extremal n).degree v = degVal n v.val := by
  have hh : half n = (n - 1) / 2 := rfl
  have hv : v.val < n := v.isLt
  simp only [degVal]
  split_ifs with h1 h2
  · have hc : (extremal n).degree v = #({0, half n} : Finset ℕ) := by
      refine degree_eq_card v _ fun m ↦ ?_
      rw [mem_nbhd_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton, extRelVal]
      omega
    rw [hc, Finset.card_pair (by omega)]
  · by_cases h0 : v.val = 0
    · have hc : (extremal n).degree v = #(insert (n - 1) (Ico (half n + 1) (n - 1))) := by
        refine degree_eq_card v _ fun m ↦ ?_
        rw [mem_nbhd_iff]
        simp only [Finset.mem_insert, Finset.mem_Ico, extRelVal]
        omega
      rw [hc, Finset.card_insert_of_notMem (by simp), Nat.card_Ico]
      omega
    · have hc : (extremal n).degree v = #(Ico (half n) (n - 1)) := by
        refine degree_eq_card v _ fun m ↦ ?_
        rw [mem_nbhd_iff]
        simp only [Finset.mem_Ico, extRelVal]
        omega
      rw [hc, Nat.card_Ico]
  · by_cases h0 : v.val = half n
    · have hc : (extremal n).degree v = #(insert (n - 1) (Ico 1 (half n))) := by
        refine degree_eq_card v _ fun m ↦ ?_
        rw [mem_nbhd_iff]
        simp only [Finset.mem_insert, Finset.mem_Ico, extRelVal]
        omega
      rw [hc, Finset.card_insert_of_notMem (by simp only [Finset.mem_Ico, not_and, not_lt]; omega),
        Nat.card_Ico]
      omega
    · have hc : (extremal n).degree v = #(range (half n)) := by
        refine degree_eq_card v _ fun m ↦ ?_
        rw [mem_nbhd_iff]
        simp only [Finset.mem_range, extRelVal]
        omega
      rw [hc, Finset.card_range]

theorem extremal_cliqueFree (n : ℕ) (hn : 5 ≤ n) : (extremal n).CliqueFree 3 := by
  have hh : half n = (n - 1) / 2 ∧ 5 ≤ n := ⟨rfl, hn⟩
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨i, j, k, hij, hik, hjk, -⟩ := hs
  rw [adj_iff] at hij hik hjk
  simp only [extRelVal] at hij hik hjk
  have h1 := i.isLt
  have h2 := j.isLt
  have h3 := k.isLt
  omega

theorem extremal_not_colorable (n : ℕ) (hn : 5 ≤ n) : ¬ (extremal n).Colorable 2 := by
  have hh : half n = (n - 1) / 2 := rfl
  rintro ⟨C⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin n, z.val = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin n, p.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n, q.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin n, u.val = half n := ⟨⟨half n, by omega⟩, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w.val = half n + 1 := ⟨⟨half n + 1, by omega⟩, rfl⟩
  have a1 : (extremal n).Adj z p := by rw [adj_iff, hz, hp]; unfold extRelVal; omega
  have a2 : (extremal n).Adj p w := by rw [adj_iff, hp, hw]; unfold extRelVal; omega
  have a3 : (extremal n).Adj w q := by rw [adj_iff, hw, hq]; unfold extRelVal; omega
  have a4 : (extremal n).Adj q u := by rw [adj_iff, hq, hu]; unfold extRelVal; omega
  have a5 : (extremal n).Adj u z := by rw [adj_iff, hu, hz]; unfold extRelVal; omega
  have v1 : (C z).val ≠ (C p).val := fun h ↦ (C.valid a1) (Fin.val_injective h)
  have v2 : (C p).val ≠ (C w).val := fun h ↦ (C.valid a2) (Fin.val_injective h)
  have v3 : (C w).val ≠ (C q).val := fun h ↦ (C.valid a3) (Fin.val_injective h)
  have v4 : (C q).val ≠ (C u).val := fun h ↦ (C.valid a4) (Fin.val_injective h)
  have v5 : (C u).val ≠ (C z).val := fun h ↦ (C.valid a5) (Fin.val_injective h)
  have b1 := (C z).isLt
  have b2 := (C p).isLt
  have b3 := (C q).isLt
  have b4 := (C u).isLt
  have b5 := (C w).isLt
  omega

theorem extremal_card_edgeFinset (n : ℕ) (hn : 5 ≤ n) :
    #(extremal n).edgeFinset = (n - 1) ^ 2 / 4 + 1 := by
  have hh : half n = (n - 1) / 2 := rfl
  have hsum : ∑ v : Fin n, (extremal n).degree v = ∑ m ∈ range n, degVal n m := by
    rw [← Fin.sum_univ_eq_sum_range (degVal n) n]
    exact Finset.sum_congr rfl fun v _ ↦ degree_eq hn v
  have hsplit : ∑ m ∈ range n, degVal n m
      = (∑ m ∈ Ico 0 (half n), degVal n m) + (∑ m ∈ Ico (half n) (n - 1), degVal n m)
        + ∑ m ∈ Ico (n - 1) n, degVal n m := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (degVal n) (show (0 : ℕ) ≤ n - 1 by omega)
        (show n - 1 ≤ n by omega),
      ← Finset.sum_Ico_consecutive (degVal n) (show (0 : ℕ) ≤ half n by omega)
        (show half n ≤ n - 1 by omega)]
  have e1 : ∑ m ∈ Ico 0 (half n), degVal n m = half n * (n - 1 - half n) := by
    have h : ∀ m ∈ Ico 0 (half n), degVal n m = n - 1 - half n := by
      intro m hm
      simp only [Finset.mem_Ico] at hm
      simp only [degVal]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.sub_zero]
  have e2 : ∑ m ∈ Ico (half n) (n - 1), degVal n m = half n * (n - 1 - half n) := by
    have h : ∀ m ∈ Ico (half n) (n - 1), degVal n m = half n := by
      intro m hm
      simp only [Finset.mem_Ico] at hm
      simp only [degVal]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.mul_comm]
  have e3 : ∑ m ∈ Ico (n - 1) n, degVal n m = 2 := by
    rw [show Ico (n - 1) n = {n - 1} by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega]
    simp [degVal]
  have hkey : half n * (n - 1 - half n) = (n - 1) ^ 2 / 4 := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n - 1)
    · have h2 : n - 1 - half n = k := by omega
      have h1 : half n = k := by omega
      rw [h2, h1, hk, show (2 * k) ^ 2 = k * k * 4 by ring, Nat.mul_div_cancel _ (by norm_num)]
    · have h2 : n - 1 - half n = k + 1 := by omega
      have h1 : half n = k := by omega
      rw [h2, h1, hk, show (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 by ring,
        Nat.mul_add_div (by norm_num : 0 < 4)]
      norm_num
  have hd := SimpleGraph.sum_degrees_eq_twice_card_edges (extremal n)
  rw [hsum, hsplit, e1, e2, e3, hkey] at hd
  obtain ⟨K, hK⟩ : ∃ K, (n - 1) ^ 2 / 4 = K := ⟨_, rfl⟩
  rw [hK] at hd ⊢
  omega

end Erdos1011

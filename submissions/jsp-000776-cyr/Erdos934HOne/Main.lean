import Mathlib

/-!
# Erdős Problem #934: `h_1(d) = d + 1` (for `d ≥ 3`), and the `d = 2` exception

Erdős and Nešetřil define `h_t(d)` as the minimal `m` such that every graph with `m` edges and
maximum degree `≤ d` contains two edges at distance `≥ t`, and ask to estimate `h_t(d)` (OPEN;
NOT addressed here).  The problem page records "It is easy to see that `h_t(d) ≤ 2d^t` always
and `h_1(d) = d + 1`."  This file proves the second clause for every `d ≥ 3`, and records that
it fails for `d = 2`: the triangle has `3` edges, maximum degree `2`, and no two disjoint edges,
so `h_1(2) = 4`.  (The bound `h_t(d) ≤ 2d^t` is not formalized.)

Definitions (ours; there is no formal-conjectures rendering of this problem).  For `t = 1`, two
edges are at distance `≥ 1` exactly when they are disjoint.  `Forces₁ d m` says every finite simple
graph with exactly `m` edges and maximum degree `≤ d` has two disjoint edges; `h₁ d = sInf {m |
Forces₁ d m}`.  Since deleting edges preserves disjointness of the remaining edges, "exactly `m`"
and "at least `m`" define the same `h₁`.

Why it works.  A family of pairwise intersecting edges in a simple graph is a star or a triangle,
so a graph with `m ≥ 4` edges and no two disjoint edges is a star with a vertex of degree `m`;
hence `Forces₁ d m` whenever `4 ≤ m` and `d < m`.  Conversely the star `K_{1,m}` (`m ≤ d`) shows
`¬ Forces₁ d m`, and the triangle shows `¬ Forces₁ 2 3`.
-/

namespace Erdos934

/-- Every graph with exactly `m` edges and maximum degree `≤ d` contains two disjoint edges. -/
def Forces₁ (d m : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.edgeFinset.card = m → G.maxDegree ≤ d →
      ∃ e ∈ G.edgeSet, ∃ f ∈ G.edgeSet, ∀ v : V, ¬ (v ∈ e ∧ v ∈ f)

/-- `h_1(d)`, the least `m` with `Forces₁ d m`. -/
noncomputable def h₁ (d : ℕ) : ℕ := sInf {m | Forces₁ d m}

/-- Two distinct members of a `Sym2` determine it. -/
theorem sym2_eq_of_mem_of_mem {α : Type*} (e : Sym2 α) {a b : α} (hab : a ≠ b)
    (ha : a ∈ e) (hb : b ∈ e) : e = s(a, b) := by
  revert ha hb
  induction e using Sym2.ind with
  | _ p q =>
    intro ha hb
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- Every edge is a pair of two distinct vertices. -/
theorem edge_eq_pair {V : Type*} (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ a b : V, a ≠ b ∧ e = s(a, b) := by
  revert he
  induction e using Sym2.ind with
  | _ p q => intro he; exact ⟨p, q, G.ne_of_adj (G.mem_edgeSet.mp he), rfl⟩

/-- Given a vertex lying on an edge, the edge is that vertex paired with a different vertex. -/
theorem exists_other_vertex {V : Type*} (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet)
    {a : V} (ha : a ∈ e) : ∃ b : V, b ≠ a ∧ e = s(a, b) := by
  revert he ha
  induction e using Sym2.ind with
  | _ p q =>
    intro he ha
    have hpq : p ≠ q := G.ne_of_adj (G.mem_edgeSet.mp he)
    simp only [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨q, Ne.symm hpq, rfl⟩
    · exact ⟨p, hpq, Sym2.eq_swap⟩

/-- A graph with `m ≥ 4` edges and no two disjoint edges is a star: some vertex lies on every
edge. -/
theorem exists_common_vertex {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h4 : 4 ≤ G.edgeFinset.card)
    (hno : ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, ∃ v : V, v ∈ e ∧ v ∈ f) :
    ∃ u : V, ∀ e ∈ G.edgeSet, u ∈ e := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < G.edgeFinset.card by omega)
  rw [SimpleGraph.mem_edgeFinset] at he
  obtain ⟨u, v, huv, rfl⟩ := edge_eq_pair G e he
  obtain ⟨f, hf, hfu⟩ := hcon u
  obtain ⟨g, hg, hgv⟩ := hcon v
  have hvf : v ∈ f := by
    obtain ⟨w, hw1, hw2⟩ := hno _ he _ hf
    rw [Sym2.mem_iff] at hw1
    rcases hw1 with rfl | rfl
    · exact absurd hw2 hfu
    · exact hw2
  have hug : u ∈ g := by
    obtain ⟨w, hw1, hw2⟩ := hno _ he _ hg
    rw [Sym2.mem_iff] at hw1
    rcases hw1 with rfl | rfl
    · exact hw2
    · exact absurd hw2 hgv
  obtain ⟨x, hxv, rfl⟩ := exists_other_vertex G f hf hvf
  obtain ⟨y, hyu, rfl⟩ := exists_other_vertex G g hg hug
  have hxu : x ≠ u := by rintro rfl; exact hfu (by simp)
  have hyv : y ≠ v := by rintro rfl; exact hgv (by simp)
  have hxy : x = y := by
    obtain ⟨w, hw1, hw2⟩ := hno _ hf _ hg
    rw [Sym2.mem_iff] at hw1 hw2
    rcases hw1 with rfl | rfl
    · rcases hw2 with h | h
      · exact absurd h.symm huv
      · exact absurd h.symm hyv
    · rcases hw2 with h | h
      · exact absurd h hxu
      · exact h
  subst hxy
  have hsub : G.edgeFinset ⊆ ({s(u, v), s(v, x), s(u, x)} : Finset (Sym2 V)) := by
    intro h hh
    rw [SimpleGraph.mem_edgeFinset] at hh
    have hA : u ∈ h ∨ v ∈ h := by
      obtain ⟨w, hw1, hw2⟩ := hno _ hh _ he
      rw [Sym2.mem_iff] at hw2
      rcases hw2 with rfl | rfl
      · exact Or.inl hw1
      · exact Or.inr hw1
    have hB : v ∈ h ∨ x ∈ h := by
      obtain ⟨w, hw1, hw2⟩ := hno _ hh _ hf
      rw [Sym2.mem_iff] at hw2
      rcases hw2 with rfl | rfl
      · exact Or.inl hw1
      · exact Or.inr hw1
    have hC : u ∈ h ∨ x ∈ h := by
      obtain ⟨w, hw1, hw2⟩ := hno _ hh _ hg
      rw [Sym2.mem_iff] at hw2
      rcases hw2 with rfl | rfl
      · exact Or.inl hw1
      · exact Or.inr hw1
    rcases hA with hu | hv
    · rcases hB with hv | hx
      · simp [sym2_eq_of_mem_of_mem h huv hu hv]
      · simp [sym2_eq_of_mem_of_mem h (Ne.symm hxu) hu hx]
    · rcases hC with hu | hx
      · simp [sym2_eq_of_mem_of_mem h huv hu hv]
      · simp [sym2_eq_of_mem_of_mem h (Ne.symm hxv) hv hx]
  have : G.edgeFinset.card ≤ 3 := le_trans (Finset.card_le_card hsub) Finset.card_le_three
  omega

/-- If `4 ≤ m` and `d < m`, every graph with `m` edges and maximum degree `≤ d` has two disjoint
edges. -/
theorem forces_of_lt (d m : ℕ) (h4 : 4 ≤ m) (hdm : d < m) : Forces₁ d m := by
  intro V _ _ G _ hcard hmax
  by_contra hno
  push Not at hno
  obtain ⟨u, hu⟩ := exists_common_vertex G (by omega) hno
  have hsub : G.edgeFinset ⊆ (G.neighborFinset u).image (fun w => s(u, w)) := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    obtain ⟨w, _, rfl⟩ := exists_other_vertex G e he (hu e he)
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
    exact ⟨w, G.mem_edgeSet.mp he, rfl⟩
  have h1 : m ≤ G.degree u := by
    calc m = G.edgeFinset.card := hcard.symm
      _ ≤ ((G.neighborFinset u).image (fun w => s(u, w))).card := Finset.card_le_card hsub
      _ ≤ (G.neighborFinset u).card := Finset.card_image_le
      _ = G.degree u := G.card_neighborFinset_eq_degree u
  have h2 := G.degree_le_maxDegree u
  omega

/-- The star `K_{1,m}` with `m ≤ d` edges has maximum degree `≤ d` and no two disjoint edges. -/
theorem not_forces_of_le (d m : ℕ) (hm : m ≤ d) : ¬ Forces₁ d m := by
  intro h
  set G : SimpleGraph (Fin (m + 1)) :=
    SimpleGraph.fromRel (fun a b : Fin (m + 1) => a = 0 ∧ b ≠ 0) with hG
  have hadj : ∀ a b : Fin (m + 1), G.Adj a b ↔ (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0) := by
    intro a b
    rw [hG, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, hab⟩; exact hab
    · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
      · exact ⟨Ne.symm hb, Or.inl ⟨rfl, hb⟩⟩
      · exact ⟨ha, Or.inr ⟨rfl, ha⟩⟩
  have hE : G.edgeFinset = (Finset.univ.erase (0 : Fin (m + 1))).image (fun i => s(0, i)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hadj, Finset.mem_image,
        Finset.mem_erase, Finset.mem_univ, and_true, Sym2.eq_iff]
      constructor
      · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
        · exact ⟨b, hb, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨i, hi, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · exact Or.inl ⟨rfl, hi⟩
        · exact Or.inr ⟨rfl, hi⟩
  have hcard : G.edgeFinset.card = m := by
    rw [hE, Finset.card_image_of_injective _ (by
      intro i j hij
      simp only [Sym2.eq_iff] at hij
      rcases hij with ⟨-, hh⟩ | ⟨h1, h2⟩
      · exact hh
      · exact h2.trans h1), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have hmax : G.maxDegree ≤ d := by
    apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · have hnb : G.neighborFinset (0 : Fin (m + 1)) = Finset.univ.erase (0 : Fin (m + 1)) := by
        ext z
        simp [SimpleGraph.mem_neighborFinset, hadj]
      rw [← G.card_neighborFinset_eq_degree, hnb,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    · have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hp
        · exact absurd (Fin.fin_one_eq_zero w) hw
        · exact hp
      have hnb : G.neighborFinset w = {0} := by
        ext z
        simp [SimpleGraph.mem_neighborFinset, hadj, hw]
      rw [← G.card_neighborFinset_eq_degree, hnb, Finset.card_singleton]
      omega
  have hzero : ∀ e ∈ G.edgeSet, (0 : Fin (m + 1)) ∈ e := by
    intro e he
    rw [← SimpleGraph.mem_edgeFinset, hE] at he
    simp only [Finset.mem_image] at he
    obtain ⟨i, -, rfl⟩ := he
    simp
  obtain ⟨e, he, f, hf, hd⟩ := h (Fin (m + 1)) G hcard hmax
  exact hd 0 ⟨hzero e he, hzero f hf⟩

/-- The triangle: `3` edges, maximum degree `2`, no two disjoint edges. -/
theorem not_forces_two_three : ¬ Forces₁ 2 3 := by
  intro h
  obtain ⟨e, he, f, hf, hd⟩ := h (Fin 3) ⊤ (by decide) (by decide)
  rw [← SimpleGraph.mem_edgeFinset] at he hf
  revert he hf hd
  revert e f
  decide

/-- **Erdős #934, `h_1(d) = d + 1` for `d ≥ 3`.** -/
theorem erdos_934_h_one (d : ℕ) (hd : 3 ≤ d) : IsLeast {m | Forces₁ d m} (d + 1) ∧ h₁ d = d + 1 := by
  have key : IsLeast {m | Forces₁ d m} (d + 1) := by
    constructor
    · exact forces_of_lt d (d + 1) (by omega) (by omega)
    · intro m hm
      by_contra hlt
      push Not at hlt
      exact not_forces_of_le d m (by omega) hm
  exact ⟨key, key.csInf_eq⟩

/-- **The `d = 2` exception**: `h_1(2) = 4`, not `3`. -/
theorem erdos_934_h_one_two : IsLeast {m | Forces₁ 2 m} 4 ∧ h₁ 2 = 4 := by
  have key : IsLeast {m | Forces₁ 2 m} 4 := by
    constructor
    · exact forces_of_lt 2 4 (by norm_num) (by norm_num)
    · intro m hm
      by_contra hlt
      push Not at hlt
      interval_cases m
      · exact not_forces_of_le 2 0 (by norm_num) hm
      · exact not_forces_of_le 2 1 (by norm_num) hm
      · exact not_forces_of_le 2 2 (by norm_num) hm
      · exact not_forces_two_three hm
  exact ⟨key, key.csInf_eq⟩

end Erdos934

open Erdos934 in
/-- **Erdős #934, the page's `h_1(d) = d + 1`, closed form**: it holds for every `d ≥ 3`, while
`h_1(2) = 4`. -/
theorem erdos_934_h_one_closed :
    (¬ ∃ d : ℕ, 3 ≤ d ∧ ¬ (IsLeast {m | Forces₁ d m} (d + 1) ∧ h₁ d = d + 1)) ∧
      (IsLeast {m | Forces₁ 2 m} 4 ∧ h₁ 2 = 4) := by
  refine ⟨?_, erdos_934_h_one_two⟩
  rintro ⟨d, hd, hcon⟩
  exact hcon (erdos_934_h_one d hd)

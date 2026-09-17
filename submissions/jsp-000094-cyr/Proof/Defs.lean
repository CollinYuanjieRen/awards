import Mathlib

/-!
# Erdős problem #812 — basic definitions

A red/blue colouring of the complete graph on a vertex type `V` is encoded as a
`SimpleGraph V`: *red* edges are the edges of the graph, *blue* edges are the
non-edges (equivalently, the edges of the complement `Gᶜ`).

This file sets up the two-colour Ramsey numbers `r(m, n)` and records the basic
monotonicity / symmetry / transport lemmas used in the rest of the development.

Reused from our own JSP-000669 package (Erdős #812).

Reused from our own JSP-000855 package (Erdős #1029).
-/

namespace Erdos77

open SimpleGraph

/-- The colouring `G` (red = edges, blue = non-edges) is `(m, n)`-good when it contains
neither a red `K_m` nor a blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- `RamseyProp N m n` says that every red/blue colouring of the complete graph on `N`
vertices contains a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The two-colour Ramsey number `r(m, n)`: the least `N` such that every red/blue
colouring of `K_N` contains a red `K_m` or a blue `K_n`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- The diagonal Ramsey number `R(n) = r(n, n)`. -/
noncomputable def R (n : ℕ) : ℕ := ramsey n n

section Basic

variable {V W : Type*}

/-- Any clique of a `k`-clique-free graph has fewer than `k` vertices. -/
theorem card_lt_of_cliqueFree {H : SimpleGraph V} {k : ℕ} (h : H.CliqueFree k)
    {t : Finset V} (ht : H.IsClique (t : Set V)) : t.card < k := by
  by_contra hc
  simp only [not_lt] at hc
  obtain ⟨t', ht', hcard⟩ := Finset.exists_subset_card_eq hc
  exact h t' ⟨ht.subset (Finset.coe_subset.mpr ht'), hcard⟩

/-- Cliques of a pulled-back colouring push forward along the embedding. -/
theorem isNClique_map_comap (f : V ↪ W) (H : SimpleGraph W) {k : ℕ} {t : Finset V}
    (ht : (H.comap f).IsNClique k t) : H.IsNClique k (t.map f) := by
  rw [SimpleGraph.isNClique_iff] at ht ⊢
  refine ⟨?_, by rw [Finset.card_map]; exact ht.2⟩
  intro a ha b hb hab
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact ht.1 hx hy (fun h => hab (by rw [h]))

/-- Pulling a colouring back along an embedding preserves clique-freeness. -/
theorem cliqueFree_comap (f : V ↪ W) {H : SimpleGraph W} {k : ℕ} (h : H.CliqueFree k) :
    (H.comap f).CliqueFree k :=
  fun _ ht => h _ (isNClique_map_comap f H ht)

/-- Taking complements commutes with pulling back along an embedding. -/
theorem compl_comap (f : V ↪ W) (H : SimpleGraph W) : (H.comap f)ᶜ = Hᶜ.comap f := by
  ext a b
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj, f.injective.ne_iff]

/-- Pulling a good colouring back along an embedding gives a good colouring. -/
theorem isGood_comap (f : V ↪ W) {H : SimpleGraph W} {m n : ℕ} (h : IsGood H m n) :
    IsGood (H.comap f) m n :=
  ⟨cliqueFree_comap f h.1, by rw [compl_comap]; exact cliqueFree_comap f h.2⟩

/-- Swapping the two colours swaps the two parameters of goodness. -/
theorem isGood_symm {G : SimpleGraph V} {m n : ℕ} : IsGood G m n ↔ IsGood Gᶜ n m := by
  unfold IsGood
  rw [compl_compl]
  exact and_comm

end Basic

/-- `RamseyProp` is monotone in the number of vertices. -/
theorem ramseyProp_mono {N N' m n : ℕ} (h : N ≤ N') (hN : RamseyProp N m n) :
    RamseyProp N' m n := by
  intro G hG
  exact hN (G.comap (Fin.castLEEmb h)) (isGood_comap _ hG)

/-- `RamseyProp` is symmetric in its two colour parameters. -/
theorem ramseyProp_symm {N m n : ℕ} : RamseyProp N m n ↔ RamseyProp N n m := by
  constructor <;> exact fun h G hG => h Gᶜ (isGood_symm.mp hG)

/-- If `RamseyProp N m n` holds then `r(m, n) ≤ N`. -/
theorem ramsey_le_of_ramseyProp {N m n : ℕ} (h : RamseyProp N m n) : ramsey m n ≤ N :=
  Nat.sInf_le h

/-- Below the Ramsey number there is a good colouring. -/
theorem exists_good_of_lt {N m n : ℕ} (h : N < ramsey m n) :
    ∃ G : SimpleGraph (Fin N), IsGood G m n := by
  have h' : ¬ RamseyProp N m n := Nat.notMem_of_lt_sInf h
  simp only [RamseyProp, not_forall, not_not] at h'
  exact h'

/-- The two-colour Ramsey number is symmetric. -/
theorem ramsey_comm (m n : ℕ) : ramsey m n = ramsey n m := by
  unfold ramsey
  congr 1
  ext N
  exact ramseyProp_symm

end Erdos77

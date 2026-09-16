import Mathlib

/-!
# Erdős Problem #23: the blow-up of `C₅` shows that `n²` deleted edges can be necessary

Erdős asked whether every triangle-free graph on `5n` vertices can be made bipartite by deleting
at most `n²` edges (OPEN).  The problem page records that the blow-up of `C₅` shows this would be
best possible.  This file proves that statement: in the balanced blow-up of the `5`-cycle with
parts of size `n`, every bipartite subgraph omits at least `n²` edges, and (the formal-conjectures
instance `Erdos23.erdos_23.variants.n5_tight`, tagged "research solved" with `sorry`) there is a
triangle-free graph on `25` vertices from which at least `25` edges must be removed to make it
bipartite.  The definitions `blowupC5` and the statement shapes are those of the
formal-conjectures file.  The question itself (the upper bound) is not addressed.

Proof.  The blow-up contains `n²` edge-disjoint `5`-cycles `(0,a), (1,b), (2,a+b), (3,a), (4,b)`
for `(a, b) ∈ (ZMod n)²`; a bipartite subgraph contains no odd cycle, so it omits an edge of each,
and these omitted edges are distinct.  The blow-up is triangle-free since three pairwise adjacent
classes of `C₅` do not exist.
-/

open SimpleGraph BigOperators

/-- The blow-up of the 5-cycle `C₅`: replace each vertex of `C₅` with an independent set of `n`
vertices, and connect two vertices iff their corresponding vertices in `C₅` are adjacent
(formal-conjectures definition). -/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

namespace BlowupC5Aux

/-! ### Arithmetic in `ZMod 5` -/

private lemma succ_ne (i : ZMod 5) : i ≠ i + 1 := by revert i; decide

private lemma no_two_step : ∀ i j : ZMod 5, i = j + 1 → i + 1 = j → False := by decide

private lemma no_triangle : ∀ i j k : ZMod 5, (i + 1 = j ∨ j + 1 = i) →
    (j + 1 = k ∨ k + 1 = j) → (i + 1 = k ∨ k + 1 = i) → False := by decide

private lemma cases5 : ∀ i : ZMod 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide

private lemma s01 : (0 : ZMod 5) + 1 = 1 := by decide
private lemma s12 : (1 : ZMod 5) + 1 = 2 := by decide
private lemma s23 : (2 : ZMod 5) + 1 = 3 := by decide
private lemma s34 : (3 : ZMod 5) + 1 = 4 := by decide
private lemma s40 : (4 : ZMod 5) + 1 = 0 := by decide

/-- A `2`-colouring cannot alternate around a `5`-cycle. -/
private lemma fin2_cycle : ∀ y₀ y₁ y₂ y₃ y₄ : Fin 2,
    ¬(y₀ ≠ y₁ ∧ y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₄ ∧ y₄ ≠ y₀) := by decide

/-! ### Adjacency in the blow-up -/

variable {n : ℕ}

private lemma adj_iff (u v : ZMod 5 × Fin n) :
    (blowupC5 n).Adj u v ↔ u ≠ v ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) := by
  obtain ⟨u₁, u₂⟩ := u
  obtain ⟨v₁, v₂⟩ := v
  simp only [blowupC5, SimpleGraph.fromRel_adj]
  tauto

/-! ### The `n²` edge-disjoint `5`-cycles -/

/-- The `Fin n`-coordinate of the `i`-th vertex of the `5`-cycle indexed by `(a, b)`:
the cycle is `(0, a), (1, b), (2, a + b), (3, a), (4, b)`. -/
private def w (a b : Fin n) (i : ZMod 5) : Fin n :=
  if i = 0 then a else if i = 1 then b else if i = 2 then a + b else if i = 3 then a else b

private lemma w_zero (a b : Fin n) : w a b 0 = a := by
  simp +decide [w]

private lemma w_one (a b : Fin n) : w a b 1 = b := by
  simp +decide [w]

private lemma w_two (a b : Fin n) : w a b 2 = a + b := by
  simp +decide [w]

private lemma w_three (a b : Fin n) : w a b 3 = a := by
  simp +decide [w]

private lemma w_four (a b : Fin n) : w a b 4 = b := by
  simp +decide [w]

/-- Consecutive vertices of the cycle indexed by `(a, b)` are adjacent in the blow-up. -/
private lemma adj_w (a b : Fin n) (i : ZMod 5) :
    (blowupC5 n).Adj (i, w a b i) (i + 1, w a b (i + 1)) :=
  (adj_iff _ _).2 ⟨fun h => succ_ne i (congrArg Prod.fst h), Or.inl rfl⟩

/-- Two consecutive coordinates of the cycle determine its index `(a, b)`. -/
private lemma w_det [NeZero n] {a b a' b' : Fin n} (i : ZMod 5)
    (h₁ : w a b i = w a' b' i) (h₂ : w a b (i + 1) = w a' b' (i + 1)) : a = a' ∧ b = b' := by
  rcases cases5 i with rfl | rfl | rfl | rfl | rfl
  · rw [w_zero, w_zero] at h₁
    rw [s01, w_one, w_one] at h₂
    exact ⟨h₁, h₂⟩
  · rw [w_one, w_one] at h₁
    rw [s12, w_two, w_two] at h₂
    subst h₁
    exact ⟨add_right_cancel h₂, rfl⟩
  · rw [w_two, w_two] at h₁
    rw [s23, w_three, w_three] at h₂
    subst h₂
    exact ⟨rfl, add_left_cancel h₁⟩
  · rw [w_three, w_three] at h₁
    rw [s34, w_four, w_four] at h₂
    exact ⟨h₁, h₂⟩
  · rw [w_four, w_four] at h₁
    rw [s40, w_zero, w_zero] at h₂
    exact ⟨h₂, h₁⟩

/-- The cycles indexed by distinct pairs `(a, b)` are edge-disjoint. -/
private lemma cedge_inj [NeZero n] {a b a' b' : Fin n} {i j : ZMod 5}
    (h : s((i, w a b i), ((i + 1 : ZMod 5), w a b (i + 1)))
        = s((j, w a' b' j), ((j + 1 : ZMod 5), w a' b' (j + 1)))) : a = a' ∧ b = b' := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, hw₁⟩ := h₁
    exact w_det i hw₁ h₂.2
  · rw [Prod.mk.injEq] at h₁ h₂
    exact (no_two_step i j h₁.1 h₂.1).elim

/-- A bipartite graph omits an edge of each of the `5`-cycles. -/
private lemma exists_index {V : Type*} (φ : ZMod 5 × Fin n → V) (H : SimpleGraph V)
    (hBip : H.IsBipartite) (a b : Fin n) :
    ∃ i : ZMod 5, ¬ H.Adj (φ (i, w a b i)) (φ (i + 1, w a b (i + 1))) := by
  obtain ⟨c⟩ := hBip
  by_contra hcon
  have key : ∀ i : ZMod 5, c (φ (i, w a b i)) ≠ c (φ (i + 1, w a b (i + 1))) := by
    intro i
    refine c.valid ?_
    by_contra hi
    exact hcon ⟨i, hi⟩
  have h₀ := key 0
  have h₁ := key 1
  have h₂ := key 2
  have h₃ := key 3
  have h₄ := key 4
  rw [s01] at h₀
  rw [s12] at h₁
  rw [s23] at h₂
  rw [s34] at h₃
  rw [s40] at h₄
  exact fin2_cycle _ _ _ _ _ ⟨h₀, h₁, h₂, h₃, h₄⟩

/-- The combinatorial heart: for any embedding `φ` of the blow-up's vertices into `V` that maps
the blow-up's edges into `G`, and any bipartite `H` on `V`, there are `n²` distinct edges of `G`
avoided by `H`. -/
private lemma exists_inj {V : Type*} [NeZero n] (φ : ZMod 5 × Fin n ↪ V) (G H : SimpleGraph V)
    (hφ : ∀ u v : ZMod 5 × Fin n, (blowupC5 n).Adj u v → G.Adj (φ u) (φ v))
    (hBip : H.IsBipartite) :
    ∃ f : Fin n × Fin n → Sym2 V, Function.Injective f ∧
      ∀ p : Fin n × Fin n, f p ∈ G.edgeSet ∧ f p ∉ H.edgeSet := by
  choose k hk using fun p : Fin n × Fin n => exists_index (n := n) φ H hBip p.1 p.2
  refine ⟨fun p => s(φ (k p, w p.1 p.2 (k p)), φ (k p + 1, w p.1 p.2 (k p + 1))), ?_, ?_⟩
  · intro p q hpq
    have hsym : s((k p, w p.1 p.2 (k p)), ((k p + 1 : ZMod 5), w p.1 p.2 (k p + 1)))
        = s((k q, w q.1 q.2 (k q)), ((k q + 1 : ZMod 5), w q.1 q.2 (k q + 1))) := by
      rw [Sym2.eq_iff] at hpq ⊢
      rcases hpq with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact Or.inl ⟨φ.injective hu, φ.injective hv⟩
      · exact Or.inr ⟨φ.injective hu, φ.injective hv⟩
    obtain ⟨h₁, h₂⟩ := cedge_inj hsym
    exact Prod.ext h₁ h₂
  · intro p
    exact ⟨(SimpleGraph.mem_edgeSet _).2 (hφ _ _ (adj_w p.1 p.2 (k p))),
      fun hmem => hk p ((SimpleGraph.mem_edgeSet _).1 hmem)⟩

end BlowupC5Aux

open scoped Classical in
/-- The blow-up of `C₅` shows that the bound `n²` in Erdős Problem 23 is tight: any bipartite
subgraph must omit at least `n²` edges (formal-conjectures `blowupC5_tight`). -/
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  have : NeZero n := ⟨_hn.ne'⟩
  have _ : H ≤ blowupC5 n := hH
  obtain ⟨f, hinj, hf⟩ := BlowupC5Aux.exists_inj (Function.Embedding.refl (ZMod 5 × Fin n))
    (blowupC5 n) H (fun _ _ h => h) hBip
  have hcard : (Finset.univ : Finset (Fin n × Fin n)).card = n ^ 2 := by
    simp [Finset.card_univ, pow_two]
  refine le_trans (le_of_eq hcard.symm)
    (Finset.card_le_card_of_injOn f (fun p _ => ?_) hinj.injOn)
  simp only [Finset.mem_coe, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
  exact hf p

theorem blowupC5_cliqueFree (n : ℕ) : (blowupC5 n).CliqueFree 3 := by
  intro s hs
  obtain ⟨hcl, hcard⟩ := hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  have axy := (BlowupC5Aux.adj_iff x y).1 (hcl (by simp) (by simp) hxy)
  have axz := (BlowupC5Aux.adj_iff x z).1 (hcl (by simp) (by simp) hxz)
  have ayz := (BlowupC5Aux.adj_iff y z).1 (hcl (by simp) (by simp) hyz)
  exact BlowupC5Aux.no_triangle x.1 y.1 z.1 axy.2 ayz.2 axz.2

open scoped Classical in
/-- **Erdős #23, tightness at `n = 5` (formal-conjectures `erdos_23.variants.n5_tight`).**  There
is a triangle-free graph on `25` vertices such that at least `25` edges must be removed to make
it bipartite.  The upper-bound question is open and not claimed. -/
theorem erdos_23_n5_tight :
    ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
        H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  have hc : Fintype.card (ZMod 5 × Fin 5) = 25 := by simp
  obtain ⟨e⟩ : Nonempty ((ZMod 5 × Fin 5) ≃ Fin 25) := ⟨Fintype.equivFinOfCardEq hc⟩
  refine ⟨(blowupC5 5).map e.toEmbedding, ?_, ?_⟩
  · rw [SimpleGraph.cliqueFree_map_iff]
    exact blowupC5_cliqueFree 5
  · intro H _ hBip
    obtain ⟨f, hinj, hf⟩ := BlowupC5Aux.exists_inj e.toEmbedding
      ((blowupC5 5).map e.toEmbedding) H
      (fun u v h => (SimpleGraph.map_adj _ _ _ _).2 ⟨u, v, h, rfl, rfl⟩) hBip
    have hcard : (Finset.univ : Finset (Fin 5 × Fin 5)).card = 25 := by
      simp [Finset.card_univ]
    refine le_trans (le_of_eq hcard.symm)
      (Finset.card_le_card_of_injOn f (fun p _ => ?_) hinj.injOn)
    simp only [Finset.mem_coe, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact hf p

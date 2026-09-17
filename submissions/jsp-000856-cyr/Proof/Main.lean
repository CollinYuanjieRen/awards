import Proof.Ramsey
import Proof.Construction

/-!
# Erdős problem #812 — Theorem 1 of Burr–Erdős–Faudree–Schelp (1989) and its consequences

Putting together the finiteness result of `MerLeanExperiment.Ramsey` and the construction of
`MerLeanExperiment.Construction` we obtain

* `Erdos1030.ramsey_succ_right` : `r(m, n) + (2m - 3) ≤ r(m, n+1)`;
* `Erdos1030.ramsey_succ_succ`  : `r(m, n) + (2m + 2n - 4) ≤ r(m+1, n+1)`;
* `Erdos1030.R_succ_ge`         : `R(n) + (4n - 4) ≤ R(n+1)` for `n ≥ 2`;
* `Erdos1030.R_succ_sub_ge`     : `R(n+1) - R(n) ≥ 4n - 8` for `n ≥ 2`, the form stated on the
  Erdős problem page.

Note on hypotheses. Theorem 1 needs `n ≥ 2` on the *source* index, not just `n ≥ 1`: the
construction starts from an `(m, n)`-good colouring of `K_{r(m,n)-1}` and needs it to contain a
red `K_{m-1}`, which is obtained by adjoining a vertex joined in red to everything — and that
vertex is a blue `K_1`, so the argument breaks when `n = 1`.  The statement is in fact false for
`n = 1`: `r(m, 1) = 1` and `r(m, 2) = m`, so at `m = 3` it would read `1 + 3 ≤ 3`.  This is
recorded formally as `Erdos1030.not_ramsey_succ_right_of_one_le`.

Not claimed here: the question of Erdős problem #1030 itself (whether lim R(k+1,k)/R(k,k) > 1 + c
for some c > 0), which is open.

Reused from our own JSP-000669 package (Erdős #812).
-/

namespace Erdos1030

open SimpleGraph

section Cone

variable {N m n : ℕ}

/-- The red relation of the colouring obtained from `G` by adding one vertex joined in red to
every old vertex. -/
def coneRel (G : SimpleGraph (Fin N)) : (Fin N ⊕ Fin 1) → (Fin N ⊕ Fin 1) → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr _, .inr _ => False

/-- The colouring obtained from `G` by adding one vertex joined in red to every old vertex. -/
def cone (G : SimpleGraph (Fin N)) : SimpleGraph (Fin N ⊕ Fin 1) where
  Adj := coneRel G
  symm := ⟨by
    rintro (a | x) (b | y) h <;>
      first
        | exact h
        | exact G.adj_symm h⟩
  loopless := ⟨by
    rintro (a | x) h
    · exact G.irrefl h
    · exact h⟩

variable (G : SimpleGraph (Fin N))

/-- Two old vertices of the cone are red iff they were red in `G`. -/
@[simp] theorem cone_adj_ll (a b : Fin N) :
    (cone G).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := Iff.rfl

/-- The new vertex of the cone is red to every old vertex. -/
@[simp] theorem cone_adj_lr (a : Fin N) (x : Fin 1) :
    (cone G).Adj (Sum.inl a) (Sum.inr x) := trivial

/-- The new vertex of the cone is red to every old vertex. -/
@[simp] theorem cone_adj_rl (x : Fin 1) (a : Fin N) :
    (cone G).Adj (Sum.inr x) (Sum.inl a) := trivial

/-- If `G` is `(m, n)`-good and has no red `K_{m-1}`, then the cone over `G` is `(m, n)`-good
(this is the step that produces a red `K_{m-1}` in an extremal colouring). -/
theorem cone_isGood (hm : 2 ≤ m) (hn : 2 ≤ n) (hG : IsGood G m n)
    (hfree : G.CliqueFree (m - 1)) : IsGood (cone G) m n := by
  classical
  constructor
  · intro s hs
    have hadj : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (cone G).Adj x y := fun x hx y hy hxy =>
      hs.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
    have hc : s.toLeft.card + s.toRight.card = s.card := Finset.card_toLeft_add_card_toRight
    have hU : s.toRight.card ≤ 1 := by simpa using Finset.card_le_univ s.toRight
    have hOcl : G.IsClique ((s.toLeft : Finset (Fin N)) : Set (Fin N)) := by
      intro a ha b hb hab
      have h3 := hadj _ (Finset.mem_toLeft.mp (Finset.mem_coe.mp ha)) _
        (Finset.mem_toLeft.mp (Finset.mem_coe.mp hb)) (by simpa using hab)
      rwa [cone_adj_ll] at h3
    have hOlt := card_lt_of_cliqueFree hfree hOcl
    have h2 := hs.2
    omega
  · intro s hs
    have hblue : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ (cone G).Adj x y := by
      intro x hx y hy hxy
      have h3 := hs.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
      rw [SimpleGraph.compl_adj] at h3
      exact h3.2
    have hc : s.toLeft.card + s.toRight.card = s.card := Finset.card_toLeft_add_card_toRight
    have hU : s.toRight.card ≤ 1 := by simpa using Finset.card_le_univ s.toRight
    have hOcl : Gᶜ.IsClique ((s.toLeft : Finset (Fin N)) : Set (Fin N)) := by
      intro a ha b hb hab
      have h3 := hblue _ (Finset.mem_toLeft.mp (Finset.mem_coe.mp ha)) _
        (Finset.mem_toLeft.mp (Finset.mem_coe.mp hb)) (by simpa using hab)
      rw [cone_adj_ll] at h3
      exact (SimpleGraph.compl_adj _ _ _).mpr ⟨hab, h3⟩
    have hOlt := card_lt_of_cliqueFree hG.2 hOcl
    have hsep : s.toLeft.card = 0 ∨ s.toRight.card = 0 := by
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcon.1)
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcon.2)
      exact hblue _ (Finset.mem_toLeft.mp ha) _ (Finset.mem_toRight.mp hx) (by simp)
        (cone_adj_lr G a x)
    have h2 := hs.2
    omega

end Cone

/-- For `m, n ≥ 1` the Ramsey number `r(m, n)` is positive (the empty colouring is good). -/
theorem ramsey_pos {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : 0 < ramsey m n := by
  have hgood : IsGood (⊥ : SimpleGraph (Fin 0)) m n :=
    ⟨SimpleGraph.cliqueFree_of_card_lt (by simp only [Fintype.card_fin]; omega),
     SimpleGraph.cliqueFree_of_card_lt (by simp only [Fintype.card_fin]; omega)⟩
  exact lt_ramsey_of_isGood hgood

/-- `r(m, 1) = 1` for `m ≥ 1`: a single vertex is already a blue `K_1`. -/
theorem ramsey_one_right (m : ℕ) (hm : 1 ≤ m) : ramsey m 1 = 1 :=
  le_antisymm (ramsey_le_of_ramseyProp (ramseyProp_one_right m)) (ramsey_pos hm le_rfl)

/-- `r(m, 2) = m` for `m ≥ 1`: a good colouring must be all red, hence have fewer than `m`
vertices. -/
theorem ramsey_two_right (m : ℕ) (hm : 1 ≤ m) : ramsey m 2 = m := by
  have hle : ramsey m 2 ≤ m := by
    refine ramsey_le_of_ramseyProp ?_
    intro G hG
    have hbot : Gᶜ = ⊥ := SimpleGraph.cliqueFree_two.mp hG.2
    have htop : G = ⊤ := by rw [← compl_compl G, hbot, compl_bot]
    refine hG.1 Finset.univ ⟨?_, ?_⟩
    · rw [htop]; exact SimpleGraph.IsClique.top _
    · simp
  have hgt : m - 1 < ramsey m 2 := by
    refine lt_ramsey_of_isGood (G := (⊤ : SimpleGraph (Fin (m - 1)))) ⟨?_, ?_⟩
    · exact SimpleGraph.cliqueFree_of_card_lt (by simp only [Fintype.card_fin]; omega)
    · rw [compl_top]; exact SimpleGraph.cliqueFree_bot le_rfl
  omega

/-- The hypothesis `2 ≤ n` in `ramsey_succ_right` cannot be weakened to `1 ≤ n`:
at `m = 3`, `n = 1` the inequality would read `1 + 3 ≤ 3`. -/
theorem not_ramsey_succ_right_of_one_le :
    ¬ ∀ m n : ℕ, 2 ≤ m → 1 ≤ n → ramsey m n + (2 * m - 3) ≤ ramsey m (n + 1) := by
  intro h
  have h3 := h 3 1 (by omega) (by omega)
  rw [ramsey_one_right 3 (by omega)] at h3
  norm_num at h3
  rw [ramsey_two_right 3 (by omega)] at h3
  omega

/-- **Theorem 1 of Burr–Erdős–Faudree–Schelp (1989)**:
`r(m, n+1) ≥ r(m, n) + 2m - 3` for `m ≥ 2` and `n ≥ 2`. -/
theorem ramsey_succ_right (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ramsey m n + (2 * m - 3) ≤ ramsey m (n + 1) := by
  classical
  have hpos : 0 < ramsey m n := ramsey_pos (by omega) (by omega)
  obtain ⟨N, hNdef⟩ : ∃ N, N = ramsey m n - 1 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ := exists_good_of_lt (show N < ramsey m n by omega)
  have hred : ¬ G.CliqueFree (m - 1) := by
    intro hfree
    have hgood : IsGood (cone G) m n := cone_isGood G hm hn hG hfree
    have E : (Fin N ⊕ Fin 1) ≃ Fin (N + 1) := finSumFinEquiv
    have hlt := lt_ramsey_of_isGood (isGood_comap E.symm.toEmbedding hgood)
    omega
  simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hred
  obtain ⟨c, hc⟩ := hred
  obtain ⟨c', hc'sub, hc'card⟩ :=
    Finset.exists_subset_card_eq (show m - 2 ≤ c.card by rw [hc.2]; omega)
  have hu : Function.Injective (c'.orderEmbOfFin hc'card) := (c'.orderEmbOfFin hc'card).injective
  have hured : ∀ i j, i ≠ j →
      G.Adj (c'.orderEmbOfFin hc'card i) (c'.orderEmbOfFin hc'card j) := by
    intro i j hij
    exact hc.1 (Finset.mem_coe.mpr (hc'sub (Finset.orderEmbOfFin_mem c' hc'card i)))
      (Finset.mem_coe.mpr (hc'sub (Finset.orderEmbOfFin_mem c' hc'card j)))
      (fun h => hij (hu h))
  obtain ⟨G', hG'⟩ := exists_good_succ G (c'.orderEmbOfFin hc'card) hm hG hu hured
  have hlt := lt_ramsey_of_isGood hG'
  omega

/-- The left-hand version of Theorem 1: `r(m+1, n) ≥ r(m, n) + 2n - 3`. -/
theorem ramsey_succ_left (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ramsey m n + (2 * n - 3) ≤ ramsey (m + 1) n := by
  rw [ramsey_comm m n, ramsey_comm (m + 1) n]
  exact ramsey_succ_right n m hn hm

/-- **Corollary of BEFS 1989**: `r(m+1, n+1) ≥ r(m, n) + 2m + 2n - 4`. -/
theorem ramsey_succ_succ (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ramsey m n + (2 * m + 2 * n - 4) ≤ ramsey (m + 1) (n + 1) := by
  have h1 := ramsey_succ_left m n hm hn
  have h2 := ramsey_succ_right (m + 1) n (by omega) hn
  omega

/-- Diagonal form: `R(n+1) ≥ R(n) + 4n − 4` for `n ≥ 2`. -/
theorem R_succ_ge (n : ℕ) (hn : 2 ≤ n) : R n + (4 * n - 4) ≤ R (n + 1) := by
  have h := ramsey_succ_succ n n hn hn
  unfold R
  omega

/-- `R 0 = 0`. -/
theorem R_zero : R 0 = 0 := Nat.le_zero.mp (ramsey_le_of_ramseyProp (ramseyProp_zero_left 0))

/-- `R 1 = 1`. -/
theorem R_one : R 1 = 1 :=
  le_antisymm (ramsey_le_of_ramseyProp (ramseyProp_one_left 1)) (ramsey_pos le_rfl le_rfl)

/-- Diagonal form for every n (with truncated subtraction): R(n) + (4n − 4) ≤ R(n+1). -/
theorem R_succ_ge_all (n : ℕ) : R n + (4 * n - 4) ≤ R (n + 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h0 : n = 0 ∨ n = 1 := by omega
    rcases h0 with rfl | rfl
    · rw [R_zero]; omega
    · have h2 : 0 < R (1 + 1) := ramsey_pos (by omega) (by omega)
      rw [R_one]; omega
  · exact R_succ_ge n h

/-- The form on the problem page: `R(n+1) − R(n) ≥ 4n − 8` for all `n ≥ 2`. -/
theorem R_succ_sub_ge : ∀ n : ℕ, 2 ≤ n → (R (n + 1) : ℤ) - (R n : ℤ) ≥ 4 * (n : ℤ) - 8 := by
  intro n hn
  have h := R_succ_ge n hn
  omega

end Erdos1030

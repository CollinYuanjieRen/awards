import Proof.Defs

/-!
# Erdős problem #85 — `f(4) = 2`

Not claimed here: the monotonicity question `f(n+1) ≥ f(n)` of the problem page, the bounds
`f(n) < √n + 1` and `f(n) = (1 + o(1))√n` quoted there from Erdős #552, and any other value of `f`.
-/

namespace Erdos85

open SimpleGraph

/-! ### Auxiliary material -/

/-- `SimpleGraph.minDegree` does not depend on the chosen decidability instance. -/
private lemma minDegree_instance_irrel {V : Type*} [Fintype V] (G : SimpleGraph V)
    (i j : DecidableRel G.Adj) :
    @SimpleGraph.minDegree V G _ i = @SimpleGraph.minDegree V G _ j := by
  have hij : i = j := Subsingleton.elim i j
  rw [hij]

/-- Four vertices `a, b, c, d` of `G` forming a closed walk with distinct "diagonals" span a
copy of `C₄`. -/
private theorem cycle_of_four (G : SimpleGraph (Fin 4)) {a b c d : Fin 4}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : cycleGraph 4 ⊑ G := by
  have key : ∀ u v : Fin 4, (cycleGraph 4).Adj u v →
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨ (u = 3 ∧ v = 0) ∨ (u = 0 ∧ v = 3) := by decide
  have hne1 : a ≠ b := G.ne_of_adj hab
  have hne2 : b ≠ c := G.ne_of_adj hbc
  have hne3 : c ≠ d := G.ne_of_adj hcd
  have hne4 : d ≠ a := G.ne_of_adj hda
  refine ⟨⟨⟨![a, b, c, d], ?_⟩, ?_⟩⟩
  · intro u v huv
    rcases key u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first
        | exact hab | exact hab.symm | exact hbc | exact hbc.symm
        | exact hcd | exact hcd.symm | exact hda | exact hda.symm
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all

/-- On four vertices, a vertex of degree at least `2` has at most one non-neighbour. -/
private theorem adj_of_not_adj (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (hd : ∀ v : Fin 4, 2 ≤ G.degree v) (v x y : Fin 4)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) (h1 : ¬ G.Adj v x) : G.Adj v y := by
  by_contra h2
  have hsub : G.neighborFinset v ⊆ ({v, x, y} : Finset (Fin 4))ᶜ := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl; exact G.irrefl hw
    · rintro rfl; exact h1 hw
    · rintro rfl; exact h2 hw
  have hcard : ({v, x, y} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hvx, hvy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_compl, hcard, Fintype.card_fin,
    SimpleGraph.card_neighborFinset_eq_degree] at h3
  have h4 := hd v
  omega

/-- If `{a, b}` is a non-edge, then `a c b d` is a `4`-cycle (`c`, `d` the other two vertices). -/
private theorem cycle_of_not_adj (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (hd : ∀ v : Fin 4, 2 ≤ G.degree v) (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hn : ¬ G.Adj a b) : cycleGraph 4 ⊑ G := by
  have hn' : ¬ G.Adj b a := fun hh => hn hh.symm
  have e1 : G.Adj a c := adj_of_not_adj G hd a b c hab hac hbc hn
  have e2 : G.Adj a d := adj_of_not_adj G hd a b d hab had hbd hn
  have e3 : G.Adj b c := adj_of_not_adj G hd b a c hab.symm hbc hac hn'
  have e4 : G.Adj b d := adj_of_not_adj G hd b a d hab.symm hbd had hn'
  exact cycle_of_four G e1 e3.symm e4 e2.symm hab hcd

/-! ### The main results -/

/-- (T3) Minimum degree `2` on four vertices forces a `C₄`: the complement is a matching, and the
four vertices can be ordered so that consecutive ones are not matched in the complement. -/
theorem cycleGraph_four_isContained_of_two_le_minDegree (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] (h : 2 ≤ G.minDegree) : cycleGraph 4 ⊑ G := by
  have hd : ∀ v : Fin 4, 2 ≤ G.degree v := fun v => le_trans h (G.minDegree_le_degree v)
  by_cases h01 : G.Adj 0 1
  case neg =>
    exact cycle_of_not_adj G hd 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h01
  by_cases h23 : G.Adj 2 3
  case neg =>
    exact cycle_of_not_adj G hd 2 3 0 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h23
  by_cases h02 : G.Adj 0 2
  case neg =>
    exact cycle_of_not_adj G hd 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h02
  by_cases h13 : G.Adj 1 3
  case neg =>
    exact cycle_of_not_adj G hd 1 3 0 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h13
  by_cases h03 : G.Adj 0 3
  case neg =>
    exact cycle_of_not_adj G hd 0 3 1 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h03
  by_cases h12 : G.Adj 1 2
  case neg =>
    exact cycle_of_not_adj G hd 1 2 0 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h12
  exact cycle_of_four G h01 h12 h23 h03.symm (by decide) (by decide)

/-- (T4) The perfect matching on four vertices has minimum degree `1` and contains no `C₄`. -/
theorem perfectMatching_witness : 1 ≤ perfectMatching.minDegree ∧ ¬ cycleGraph 4 ⊑ perfectMatching := by
  refine ⟨perfectMatching.le_minDegree_of_forall_le_degree 1 (by decide), ?_⟩
  rintro ⟨f⟩
  have hmatch : ∀ x y z : Fin 4,
      perfectMatching.Adj x y → perfectMatching.Adj x z → y = z := by decide
  have h10 : perfectMatching.Adj (f.toHom 1) (f.toHom 0) :=
    f.toHom.map_adj (by decide : (cycleGraph 4).Adj 1 0)
  have h12 : perfectMatching.Adj (f.toHom 1) (f.toHom 2) :=
    f.toHom.map_adj (by decide : (cycleGraph 4).Adj 1 2)
  have h02 : (0 : Fin 4) = 2 := f.injective (hmatch _ _ _ h10 h12)
  exact absurd h02 (by decide)

/-- (T2) `f(4) ≤ 2`. -/
theorem f_four_le : f 4 ≤ 2 := by
  have h2 : ∀ (G : SimpleGraph (Fin 4)) (inst : DecidableRel G.Adj),
      2 ≤ @SimpleGraph.minDegree _ G _ inst → cycleGraph 4 ⊑ G :=
    fun G inst hG => @cycleGraph_four_isContained_of_two_le_minDegree G inst hG
  unfold f
  exact Nat.sInf_le (fun G hG => h2 G _ hG)

/-- (T5) `2 ≤ f(4)`. -/
theorem two_le_f_four : 2 ≤ f 4 := by
  have h2 : ∀ (G : SimpleGraph (Fin 4)) (inst : DecidableRel G.Adj),
      2 ≤ @SimpleGraph.minDegree _ G _ inst → cycleGraph 4 ⊑ G :=
    fun G inst hG => @cycleGraph_four_isContained_of_two_le_minDegree G inst hG
  have hpm : ∀ inst : DecidableRel perfectMatching.Adj,
      1 ≤ @SimpleGraph.minDegree _ perfectMatching _ inst := by
    intro inst
    have hw := perfectMatching_witness.1
    rwa [minDegree_instance_irrel perfectMatching _ inst] at hw
  unfold f
  refine le_csInf ⟨2, fun G hG => h2 G _ hG⟩ ?_
  intro k hk
  by_contra hcon
  have h1 : k ≤ 1 := by omega
  exact perfectMatching_witness.2 (hk perfectMatching (le_trans h1 (hpm _)))

/-- (T1) Audited root: the page's `f(4) = 2`. -/
theorem f_four : f 4 = 2 := le_antisymm f_four_le two_le_f_four

end Erdos85

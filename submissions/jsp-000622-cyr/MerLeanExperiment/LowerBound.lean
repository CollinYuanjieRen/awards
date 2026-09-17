import MerLeanExperiment.Target
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic

/-!
An explicit twenty-vertex lower-bound graph: the Paley graph on the first
seventeen vertices, followed by three isolated vertices.
-/

namespace CochromaticTwenty

/-- The nonzero quadratic residues modulo `17`. -/
private def isSquareMod17 (r : ℕ) : Bool :=
  r == 1 || r == 2 || r == 4 || r == 8 ||
    r == 9 || r == 13 || r == 15 || r == 16

/-- Boolean Paley adjacency on `Fin 17`. -/
private def paleyAdj17 (a b : Fin 17) : Bool :=
  isSquareMod17 ((a.val + 17 - b.val) % 17)

set_option linter.style.haveILetI false in
private theorem paleyAdj17_symm :
    ∀ a b : Fin 17, paleyAdj17 a b = true → paleyAdj17 b a = true := by
  letI (a : Fin 17) : Decidable (∀ b : Fin 17,
      paleyAdj17 a b = true → paleyAdj17 b a = true) :=
    Fintype.decidableForallFintype
  exact of_decide_eq_true rfl

private theorem paleyAdj17_irrefl :
    ∀ a : Fin 17, ¬ paleyAdj17 a a = true := by
  exact of_decide_eq_true rfl

/-- The Paley graph of order seventeen, given by its ordinary adjacency
relation rather than by a precomputed homogeneous-set certificate. -/
def paley17 : SimpleGraph (Fin 17) where
  Adj a b := paleyAdj17 a b
  symm.symm := paleyAdj17_symm
  loopless.irrefl := paleyAdj17_irrefl

private instance paley17AdjDecidable : DecidableRel paley17.Adj := by
  intro a b
  change Decidable (paleyAdj17 a b = true)
  infer_instance

/-- The natural embedding of the Paley vertices into the first seventeen
vertices of `Fin 20`. -/
def firstSeventeen : Fin 17 ↪ Fin 20 :=
  Fin.castLEEmb (by omega)

/-- The lower-bound graph: `paley17` on the first seventeen vertices, with the
remaining three vertices isolated. -/
def paley17WithIsolatedThree : SimpleGraph (Fin 20) :=
  paley17.map firstSeventeen

@[simp]
theorem paley17WithIsolatedThree_adj_first (a b : Fin 17) :
    paley17WithIsolatedThree.Adj (firstSeventeen a) (firstSeventeen b) ↔
      paley17.Adj a b := by
  simp [paley17WithIsolatedThree]

/-- Vertices `17`, `18`, and `19` have no incident edge. -/
theorem paley17WithIsolatedThree_isolated_of_ge_seventeen
    (v : Fin 20) (hv : 17 ≤ v.val) :
    paley17WithIsolatedThree.IsIsolated v := by
  intro w hadj
  rw [paley17WithIsolatedThree, SimpleGraph.map_adj] at hadj
  obtain ⟨a, b, _, ha, _⟩ := hadj
  have hav : a.val = v.val := by
    simpa [firstSeventeen] using congrArg Fin.val ha
  omega

/-!
The only computation in the proof is this closed, tuple-level statement.
It checks the explicit adjacency formula on `17^4` ordered tuples.  The
subsequent theorems derive the graph and cardinality semantics in Lean.
-/
private def paleyFourPointOK (a b c d : Fin 17) : Prop :=
  a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ ((paley17.Adj a b ∧ paley17.Adj a c ∧ paley17.Adj a d ∧
          paley17.Adj b c ∧ paley17.Adj b d ∧ paley17.Adj c d) ∨
        (¬ paley17.Adj a b ∧ ¬ paley17.Adj a c ∧ ¬ paley17.Adj a d ∧
          ¬ paley17.Adj b c ∧ ¬ paley17.Adj b d ∧ ¬ paley17.Adj c d))

private instance paleyFourPointOKDecidable (a b c d : Fin 17) :
    Decidable (paleyFourPointOK a b c d) := by
  unfold paleyFourPointOK
  infer_instance

set_option maxHeartbeats 2000000 in
set_option linter.style.haveILetI false in
private theorem paley17_four_point_check :
    ∀ a b c d : Fin 17, paleyFourPointOK a b c d := by
  letI (a b c : Fin 17) : Decidable (∀ d : Fin 17, paleyFourPointOK a b c d) :=
    Fintype.decidableForallFintype
  letI (a b : Fin 17) : Decidable (∀ c d : Fin 17, paleyFourPointOK a b c d) :=
    Fintype.decidableForallFintype
  letI (a : Fin 17) : Decidable (∀ b c d : Fin 17, paleyFourPointOK a b c d) :=
    Fintype.decidableForallFintype
  exact of_decide_eq_true rfl

/-- No four vertices of `paley17` form a clique or an independent set. -/
theorem paley17_no_homogeneous_four (s : Finset (Fin 17)) (hs_card : s.card = 4) :
    ¬ Homogeneous paley17 s := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    Finset.card_eq_four.mp hs_card
  intro hhom
  apply paley17_four_point_check a b c d hab hac had hbc hbd hcd
  rcases hhom with hclique | hindependent
  · exact Or.inl ⟨
      hclique (by simp) (by simp) hab,
      hclique (by simp) (by simp) hac,
      hclique (by simp) (by simp) had,
      hclique (by simp) (by simp) hbc,
      hclique (by simp) (by simp) hbd,
      hclique (by simp) (by simp) hcd⟩
  · exact Or.inr ⟨
      hindependent (by simp) (by simp) hab,
      hindependent (by simp) (by simp) hac,
      hindependent (by simp) (by simp) had,
      hindependent (by simp) (by simp) hbc,
      hindependent (by simp) (by simp) hbd,
      hindependent (by simp) (by simp) hcd⟩

/-- Five colors cannot cocolor the explicit twenty-vertex graph. -/
theorem paley17WithIsolatedThree_not_hasCocoloring_five :
    ¬ HasCocoloring paley17WithIsolatedThree 5 := by
  rintro ⟨color, hcolor⟩
  let color17 : Fin 17 → Fin 5 := fun v ↦ color (firstSeventeen v)
  obtain ⟨i, hi⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card color17 (n := 3) (by norm_num)
  let fiber : Finset (Fin 17) := {v | color17 v = i}
  have hfour : 4 ≤ fiber.card := by
    have : 3 < fiber.card := by simpa [fiber] using hi
    omega
  obtain ⟨s, hs, hs_card⟩ := Finset.exists_subset_card_eq hfour
  apply paley17_no_homogeneous_four s hs_card
  rcases hcolor i with hclique | hindependent
  · left
    intro a ha b hb hab
    have ha_color : color (firstSeventeen a) = i := by
      simpa [fiber, color17] using hs ha
    have hb_color : color (firstSeventeen b) = i := by
      simpa [fiber, color17] using hs hb
    exact paley17WithIsolatedThree_adj_first a b |>.mp
      (hclique ha_color hb_color (firstSeventeen.injective.ne hab))
  · right
    intro a ha b hb hab hadj
    have ha_color : color (firstSeventeen a) = i := by
      simpa [fiber, color17] using hs ha
    have hb_color : color (firstSeventeen b) = i := by
      simpa [fiber, color17] using hs hb
    exact hindependent ha_color hb_color (firstSeventeen.injective.ne hab)
      (paley17WithIsolatedThree_adj_first a b |>.mpr hadj)

/-- The explicit Paley-plus-isolates graph proves the frozen lower-bound face. -/
theorem paley17_lowerBound : LowerBound :=
  ⟨paley17WithIsolatedThree, paley17WithIsolatedThree_not_hasCocoloring_five⟩

end CochromaticTwenty

#print axioms CochromaticTwenty.paley17_no_homogeneous_four
#print axioms CochromaticTwenty.paley17_lowerBound

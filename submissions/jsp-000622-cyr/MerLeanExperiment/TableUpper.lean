import MerLeanExperiment.CocoloringAssembly
import MerLeanExperiment.TwelveColoring

/-!
# The new upper anchors of the cochromatic table

Together with the two upper anchors already in the tree
(`fin8_hasCocoloring_three`, `fin12_hasCocoloring_four`) and
`universal_six_upperBound`, the three anchors proved here pin down the upper
half of the published table `z(1..19)`:

* `fin2_hasCocoloring_one`  : `z(2) ≤ 1`;
* `fin4_hasCocoloring_two`  : `z(4) ≤ 2`;
* `fin15_hasCocoloring_five`: `z(15) ≤ 5`.

The first two follow from `homogeneous_pair`: any set of at most two vertices
is homogeneous, because two vertices are either adjacent (a clique) or not
(an independent set).  The third is a two-step corollary of the tree's own
`ramsey_three_three` (`R(3,3) ≤ 6`) and `fin12_hasCocoloring_four`: delete a
homogeneous triple from the fifteen vertices, spend one color on it, and
four-cocolor the twelve vertices that remain.
-/

namespace CochromaticTwenty

variable {V : Type*} {G : SimpleGraph V}

/-- Any two-element set of vertices is homogeneous: if the two vertices are
adjacent it is a clique, and otherwise an independent set. -/
theorem homogeneous_pair (a b : V) : Homogeneous G {a, b} := by
  classical
  by_cases h : G.Adj a b
  · left
    intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp_all [G.adj_symm h]
  · right
    intro x hx y hy hxy
    have h' : ¬ G.Adj b a := fun hh ↦ h (G.adj_symm hh)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

/-- `z(2) ≤ 1`: the two vertices form a single homogeneous class. -/
theorem fin2_hasCocoloring_one (G : SimpleGraph (Fin 2)) : HasCocoloring G 1 := by
  refine ⟨fun _ ↦ 0, fun i ↦ ?_⟩
  have h : {v : Fin 2 | (fun _ ↦ (0 : Fin 1)) v = i} = {0, 1} := by
    ext v; fin_cases v <;> simp [Subsingleton.elim i 0]
  rw [show Homogeneous G {v : Fin 2 | (fun _ ↦ (0 : Fin 1)) v = i} =
      Homogeneous G {0, 1} from by rw [h]]
  exact homogeneous_pair 0 1

/-- `z(4) ≤ 2`: pair the four vertices up as `{0,1}` and `{2,3}`; every pair
is homogeneous. -/
theorem fin4_hasCocoloring_two (G : SimpleGraph (Fin 4)) : HasCocoloring G 2 := by
  refine ⟨fun v ↦ if v.val < 2 then 0 else 1, fun i ↦ ?_⟩
  fin_cases i
  · have h : {v : Fin 4 | (if v.val < 2 then (0 : Fin 2) else 1) = (0 : Fin 2)} = {0, 1} := by
      ext v; fin_cases v <;> simp
    show Homogeneous G {v : Fin 4 | (if v.val < 2 then (0 : Fin 2) else 1) = (0 : Fin 2)}
    rw [h]; exact homogeneous_pair 0 1
  · have h : {v : Fin 4 | (if v.val < 2 then (0 : Fin 2) else 1) = (1 : Fin 2)} = {2, 3} := by
      ext v; fin_cases v <;> simp
    show Homogeneous G {v : Fin 4 | (if v.val < 2 then (0 : Fin 2) else 1) = (1 : Fin 2)}
    rw [h]; exact homogeneous_pair 2 3

/-- `z(15) ≤ 5` on an arbitrary fifteen-element vertex type.  By `R(3,3) ≤ 6`
the graph has a homogeneous triple `S`; one color covers `S`, and the twelve
remaining vertices are four-cocolored by `fin12_hasCocoloring_four`. -/
theorem hasCocoloring_five_of_card_fifteen [Fintype V]
    (hcard : Fintype.card V = 15) (G : SimpleGraph V) : HasCocoloring G 5 := by
  classical
  obtain ⟨s, hscard, hs⟩ : ∃ s : Finset V, s.card = 3 ∧ Homogeneous G (s : Set V) := by
    rcases ramsey_three_three G (by omega) with ⟨s, hc, h⟩ | ⟨s, hc, h⟩
    · exact ⟨s, hc, Or.inl h⟩
    · exact ⟨s, hc, Or.inr h⟩
  let S : Set V := (s : Set V)
  have hScard : Fintype.card S = 3 := by simp [S, hscard]
  have hcomplement : Fintype.card ↥(Sᶜ) = 12 := by
    rw [Fintype.card_compl_set, hScard, hcard]
  have hleft : HasCocoloring (G.induce S) 1 := hasCocoloring_one_of_homogeneous hs
  have hright : HasCocoloring (G.induce (Sᶜ)) 4 :=
    hasCocoloring_of_forall_fin hcomplement fin12_hasCocoloring_four (G.induce (Sᶜ))
  simpa using hleft.induce_add hright

/-- `z(15) ≤ 5`: every fifteen-vertex simple graph admits at most five
homogeneous color classes. -/
theorem fin15_hasCocoloring_five (G : SimpleGraph (Fin 15)) : HasCocoloring G 5 :=
  hasCocoloring_five_of_card_fifteen (by simp) G

end CochromaticTwenty

#print axioms CochromaticTwenty.homogeneous_pair
#print axioms CochromaticTwenty.fin2_hasCocoloring_one
#print axioms CochromaticTwenty.fin4_hasCocoloring_two
#print axioms CochromaticTwenty.hasCocoloring_five_of_card_fifteen
#print axioms CochromaticTwenty.fin15_hasCocoloring_five

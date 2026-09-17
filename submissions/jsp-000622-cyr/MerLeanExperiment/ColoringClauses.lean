import MerLeanExperiment.GraphClauses
import MerLeanExperiment.CocoloringAssembly
import MerLeanExperiment.RamseyReduction

namespace CochromaticTwenty
open Std.Sat

theorem homogeneous_of_card_le_two {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (hs : s.card ≤ 2) : Homogeneous G s := by
  classical
  by_cases hsmall : s.card ≤ 1
  · left
    intro u hu v hv hne
    exact False.elim (hne (Finset.card_le_one.mp hsmall u hu v hv))
  · have htwo : s.card = 2 := by omega
    obtain ⟨u, v, _, rfl⟩ := Finset.card_eq_two.mp htwo
    by_cases hadj : G.Adj u v
    · left
      intro a ha b hb hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp_all [SimpleGraph.adj_comm]
    · right
      intro a ha b hb hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp_all [SimpleGraph.adj_comm]

structure ColoringClauseWitness (n k : ℕ) where
  parts : Fin k → Finset (Fin n)
  colors : Fin k → Bool

/-- If a direct clause is false, these sets cover every vertex with homogeneous
classes. Small classes need no constraint on their sole possible edge. -/
def ColoringClauseWitness.Valid {n k : ℕ} (w : ColoringClauseWitness n k)
    (p : GraphPattern n) (c : CNF.Clause ℕ) : Prop :=
  (∀ v : Fin n, ∃ i : Fin k, v ∈ w.parts i) ∧
  ∀ i : Fin k, (w.parts i).card ≤ 2 ∨
    ClauseForcesHomogeneous p c (w.parts i) (w.colors i)

instance {n k : ℕ} (w : ColoringClauseWitness n k) (p : GraphPattern n)
    (c : CNF.Clause ℕ) : Decidable (w.Valid p c) := by
  unfold ColoringClauseWitness.Valid
  infer_instance

theorem ColoringClauseWitness.coloring_of_false {n k : ℕ}
    (w : ColoringClauseWitness n k) (p : GraphPattern n) (c : CNF.Clause ℕ)
    (hw : w.Valid p c) (a : ℕ → Bool) (hc : c.eval a = false) :
    HasCocoloring (p.graph a) k := by
  apply hasCocoloring_of_homogeneous_cover (fun i => (w.parts i : Set (Fin n))) hw.1
  intro i
  rcases hw.2 i with hsmall | hforce
  · exact homogeneous_of_card_le_two (p.graph a) (w.parts i) hsmall
  · exact homogeneous_of_clause_false p c (w.parts i) (w.colors i) hforce a hc

/-- When every clause is explained by a homogeneous cover, no forbidden-subgraph
assumption is needed. -/
theorem cocoloring_of_cover_clauses_unsat {n k : ℕ} (p : GraphPattern n) (f : CNF ℕ)
    (hunsat : f.Unsat)
    (hexplain : ∀ c ∈ f.clauses, ∃ w : ColoringClauseWitness n k, w.Valid p c)
    (a : ℕ → Bool) : HasCocoloring (p.graph a) k := by
  classical
  by_contra hcolor
  have hs : f.eval a = true := by
    apply Array.all_eq_true'.mpr
    intro c hc
    obtain ⟨w, hw⟩ := hexplain c hc
    cases heval : c.eval a with
    | true => rfl
    | false => exact False.elim (hcolor (w.coloring_of_false p c hw a heval))
  have hf := hunsat a
  rw [hf] at hs
  contradiction

structure ForbiddenFourClauseWitness (n : ℕ) where
  vertices : Finset (Fin n)
  color : Bool

def ForbiddenFourClauseWitness.Valid {n : ℕ} (w : ForbiddenFourClauseWitness n)
    (p : GraphPattern n) (c : CNF.Clause ℕ) : Prop :=
  w.vertices.card = 4 ∧ ClauseForcesHomogeneous p c w.vertices w.color

instance {n : ℕ} (w : ForbiddenFourClauseWitness n) (p : GraphPattern n)
    (c : CNF.Clause ℕ) : Decidable (w.Valid p c) := by
  unfold ForbiddenFourClauseWitness.Valid
  infer_instance

theorem ForbiddenFourClauseWitness.not_noHomogeneousFour {n : ℕ}
    (w : ForbiddenFourClauseWitness n) (p : GraphPattern n) (c : CNF.Clause ℕ)
    (hw : w.Valid p c) (a : ℕ → Bool) (hc : c.eval a = false) :
    ¬ NoHomogeneousFour (p.graph a) := by
  intro hno
  have hh := homogeneous_of_clause_false p c w.vertices w.color hw.2 a hc
  rcases hh with hh | hh
  · exact hno.1 ⟨w.vertices, hw.1, hh⟩
  · exact hno.2 ⟨w.vertices, hw.1, hh⟩

/-- A shared semantic consumer for direct clauses in the small coloring cases. -/
theorem cocoloring_of_unsat {n k : ℕ} (p : GraphPattern n) (f : CNF ℕ)
    (hunsat : f.Unsat)
    (hexplain : ∀ c ∈ f.clauses,
      (∃ w : ColoringClauseWitness n k, w.Valid p c) ∨
      (∃ w : ForbiddenFourClauseWitness n, w.Valid p c))
    (a : ℕ → Bool) (hno : NoHomogeneousFour (p.graph a)) :
    HasCocoloring (p.graph a) k := by
  classical
  by_contra hcolor
  have hs : f.eval a = true := by
    apply Array.all_eq_true'.mpr
    intro c hc
    cases heval : c.eval a with
    | true => rfl
    | false =>
      exfalso
      rcases hexplain c hc with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact hcolor (w.coloring_of_false p c hw a heval)
      · exact w.not_noHomogeneousFour p c hw a heval hno
  have hf := hunsat a
  rw [hf] at hs
  contradiction

end CochromaticTwenty

#print axioms CochromaticTwenty.cocoloring_of_unsat

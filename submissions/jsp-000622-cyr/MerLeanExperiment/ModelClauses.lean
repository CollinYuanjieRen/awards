import MerLeanExperiment.NeighborhoodMeaningWitness

namespace CochromaticTwenty
open Std.Sat

/-- A false clause fixes every off-diagonal edge of the pattern to the stated
ordinary graph code. This covers the exact model-blocking clauses. -/
def ClauseForcesCode {n : ℕ} (p : GraphPattern n) (c : CNF.Clause ℕ)
    (code : ℕ) : Prop :=
  ∀ u v : Fin n, u ≠ v →
    match p.edge u v with
    | .fixed value => value = code.testBit (edgeIndex u.val v.val)
    | .variable index => (index, !(code.testBit (edgeIndex u.val v.val))) ∈ c

instance instDecidableClauseForcesCode {n : ℕ} (p : GraphPattern n)
    (c : CNF.Clause ℕ) (code : ℕ) : Decidable (ClauseForcesCode p c code) := by
  letI (u v : Fin n) : Decidable (match p.edge u v with
      | .fixed value => value = code.testBit (edgeIndex u.val v.val)
      | .variable index => (index, !(code.testBit (edgeIndex u.val v.val))) ∈ c) := by
    cases p.edge u v <;> infer_instance
  unfold ClauseForcesCode
  infer_instance

def ClassificationClauseValid {n : ℕ} (p : GraphPattern n) (c : CNF.Clause ℕ)
    (codes : List ℕ) : ForbiddenFourClauseWitness n ⊕ ℕ → Prop
  | .inl w => w.Valid p c
  | .inr code => code ∈ codes ∧ ClauseForcesCode p c code

instance instDecidableClassificationClauseValid {n : ℕ} (p : GraphPattern n)
    (c : CNF.Clause ℕ) (codes : List ℕ) (w : ForbiddenFourClauseWitness n ⊕ ℕ) :
    Decidable (ClassificationClauseValid p c codes w) := by
  cases w <;> simp only [ClassificationClauseValid] <;> infer_instance

theorem graph_eq_code_of_clause_false {n : ℕ} (p : GraphPattern n)
    (c : CNF.Clause ℕ) (code : ℕ) (hforce : ClauseForcesCode p c code)
    (a : ℕ → Bool) (hc : c.eval a = false) : p.graph a = codeGraph n code := by
  have hedge : ∀ u v : Fin n, u ≠ v →
      (p.edge u v).eval a = code.testBit (edgeIndex u.val v.val) := by
    intro u v hne
    have hf := hforce u v hne
    cases he : p.edge u v with
    | fixed value => simpa [he, EdgeRule.eval] using hf
    | «variable» index =>
      have hm : (index, !(code.testBit (edgeIndex u.val v.val))) ∈ c := by
        simpa [he] using hf
      have hh := (List.any_eq_false.mp hc) _ hm
      change ¬ (a index == !(code.testBit (edgeIndex u.val v.val))) = true at hh
      cases hai : a index <;> cases hb : code.testBit (edgeIndex u.val v.val) <;>
        simp_all [EdgeRule.eval]
  ext u v
  change (u ≠ v ∧ (p.edge u v).eval a = true) ↔
    (u ≠ v ∧ code.testBit (edgeIndex u.val v.val) = true)
  by_cases hne : u = v
  · simp [hne]
  · rw [hedge u v hne]

/-- A semantic consumer shared by the twenty-five impossible neighborhood
patterns and the two patterns with explicitly enumerated models. -/
theorem classification_of_clauses_unsat {n : ℕ} (p : GraphPattern n) (f : CNF ℕ)
    (codes : List ℕ) (hunsat : f.Unsat)
    (hexplain : ∀ c ∈ f.clauses,
      (∃ w : ForbiddenFourClauseWitness n, w.Valid p c) ∨
      (∃ code ∈ codes, ClauseForcesCode p c code))
    (a : ℕ → Bool) (hno : NoHomogeneousFour (p.graph a)) :
    ∃ code ∈ codes, p.graph a = codeGraph n code := by
  classical
  by_contra hmissing
  have hs : f.eval a = true := by
    apply Array.all_eq_true'.mpr
    intro c hc
    cases heval : c.eval a with
    | true => rfl
    | false =>
      exfalso
      rcases hexplain c hc with ⟨w, hw⟩ | ⟨code, hcode, hw⟩
      · exact w.not_noHomogeneousFour p c hw a heval hno
      · exact hmissing ⟨code, hcode, graph_eq_code_of_clause_false p c code hw a heval⟩
  have hf := hunsat a
  rw [hf] at hs
  contradiction

end CochromaticTwenty
#print axioms CochromaticTwenty.classification_of_clauses_unsat

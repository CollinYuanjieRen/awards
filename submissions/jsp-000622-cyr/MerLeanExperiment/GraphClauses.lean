import MerLeanExperiment.Target
import Mathlib.Tactic
import Std.Sat.CNF.Basic

namespace CochromaticTwenty
open Std.Sat

/-- An edge is either fixed by a finite graph pattern or is a free Boolean variable. -/
inductive EdgeRule where
  | fixed (value : Bool)
  | variable (index : ℕ)
  deriving DecidableEq

def EdgeRule.eval (a : ℕ → Bool) : EdgeRule → Bool
  | .fixed value => value
  | .variable index => a index

structure GraphPattern (n : ℕ) where
  edge : Fin n → Fin n → EdgeRule
  symmetric : ∀ u v, edge u v = edge v u

def GraphPattern.graph {n : ℕ} (p : GraphPattern n) (a : ℕ → Bool) :
    SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (p.edge u v).eval a = true
  symm.symm := by
    intro u v h
    exact ⟨Ne.symm h.1, by rw [p.symmetric]; exact h.2⟩
  loopless.irrefl := by intro u h; exact h.1 rfl

instance {n : ℕ} (p : GraphPattern n) (a : ℕ → Bool) :
    DecidableRel (p.graph a).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Falsifying this clause forces every edge on `s` to have the indicated color.
This is a finite structural check, independent of any truth assignment. -/
def ClauseForcesHomogeneous {n : ℕ} (p : GraphPattern n) (c : CNF.Clause ℕ)
    (s : Finset (Fin n)) (color : Bool) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
    match p.edge u v with
    | .fixed value => value = color
    | .variable index => (index, !color) ∈ c

instance {n : ℕ} (p : GraphPattern n) (c : CNF.Clause ℕ)
    (s : Finset (Fin n)) (color : Bool) : Decidable (ClauseForcesHomogeneous p c s color) := by
  letI (u v : Fin n) : Decidable (match p.edge u v with
      | .fixed value => value = color
      | .variable index => (index, !color) ∈ c) := by
    cases p.edge u v <;> infer_instance
  unfold ClauseForcesHomogeneous
  infer_instance

theorem homogeneous_of_clause_false {n : ℕ} (p : GraphPattern n)
    (c : CNF.Clause ℕ) (s : Finset (Fin n)) (color : Bool)
    (hforce : ClauseForcesHomogeneous p c s color)
    (a : ℕ → Bool) (hc : c.eval a = false) : Homogeneous (p.graph a) s := by
  have hedge : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (p.edge u v).eval a = color := by
    intro u hu v hv hne
    have hf := hforce u hu v hv hne
    cases he : p.edge u v with
    | fixed value => simpa [he, EdgeRule.eval] using hf
    | «variable» index =>
      have hm : (index, !color) ∈ c := by simpa [he] using hf
      have hh := (List.any_eq_false.mp hc) (index, !color) hm
      change ¬ (a index == !color) = true at hh
      cases hai : a index <;> cases hcolor : color <;>
        simp_all [EdgeRule.eval]
  cases color with
  | false =>
    right
    intro u hu v hv hne hadj
    have hf := hedge u hu v hv hne
    have ht := hadj.2
    rw [hf] at ht
    contradiction
  | true =>
    left
    intro u hu v hv hne
    exact ⟨hne, hedge u hu v hv hne⟩

def TwoHomogeneousFours {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ s t : Finset V, s.card = 4 ∧ t.card = 4 ∧ Disjoint s t ∧
    Homogeneous G s ∧ Homogeneous G t

structure PairClauseWitness (n : ℕ) where
  left : Finset (Fin n)
  right : Finset (Fin n)
  leftColor : Bool
  rightColor : Bool

def PairClauseWitness.Valid {n : ℕ} (w : PairClauseWitness n)
    (p : GraphPattern n) (c : CNF.Clause ℕ) : Prop :=
  w.left.card = 4 ∧ w.right.card = 4 ∧ Disjoint w.left w.right ∧
    ClauseForcesHomogeneous p c w.left w.leftColor ∧
    ClauseForcesHomogeneous p c w.right w.rightColor

instance {n : ℕ} (w : PairClauseWitness n) (p : GraphPattern n) (c : CNF.Clause ℕ) :
    Decidable (w.Valid p c) := by unfold PairClauseWitness.Valid; infer_instance

theorem PairClauseWitness.clause_true {n : ℕ} (w : PairClauseWitness n)
    (p : GraphPattern n) (c : CNF.Clause ℕ) (hw : w.Valid p c)
    (a : ℕ → Bool) (hno : ¬ TwoHomogeneousFours (p.graph a)) : c.eval a = true := by
  cases hc : c.eval a with
  | true => rfl
  | false =>
    exfalso
    apply hno
    exact ⟨w.left, w.right, hw.1, hw.2.1, hw.2.2.1,
      homogeneous_of_clause_false p c w.left w.leftColor hw.2.2.2.1 a hc,
      homogeneous_of_clause_false p c w.right w.rightColor hw.2.2.2.2 a hc⟩

/-- Unsatisfiability plus checked structural explanations for every input clause
gives an unconditional graph conclusion for every free-edge assignment. -/
theorem twoHomogeneousFours_of_unsat {n : ℕ} (p : GraphPattern n) (f : CNF ℕ)
    (hunsat : f.Unsat)
    (hexplain : ∀ c ∈ f.clauses, ∃ w : PairClauseWitness n, w.Valid p c)
    (a : ℕ → Bool) : TwoHomogeneousFours (p.graph a) := by
  classical
  by_contra hno
  have hs : f.eval a = true := by
    apply Array.all_eq_true'.mpr
    intro c hc
    obtain ⟨w, hw⟩ := hexplain c hc
    exact w.clause_true p c hw a hno
  have hf := hunsat a
  rw [hf] at hs
  contradiction

end CochromaticTwenty

#print axioms CochromaticTwenty.twoHomogeneousFours_of_unsat

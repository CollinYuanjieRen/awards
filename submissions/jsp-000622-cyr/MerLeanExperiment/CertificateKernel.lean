import Std.Tactic.BVDecide.LRAT.Checker

namespace CochromaticTwenty.CertificateKernel
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal

def literalsCompatible {n : Nat} (cs : List (Literal (PosFin n))) : Bool :=
  cs.all fun a => cs.all fun b => decide (a.1 = b.1 → a.2 = b.2)

def directClause {n : Nat} (cs : List (Literal (PosFin n)))
    (hc : literalsCompatible cs = true) (hn : cs.Nodup) : DefaultClause n :=
  ⟨cs, by
    intro l
    by_cases ht : (l, true) ∈ cs
    · right
      intro hf
      simp only [literalsCompatible, List.all_eq_true, decide_eq_true_eq] at hc
      have bad := hc (l, true) ht (l, false) hf rfl
      contradiction
    · exact Or.inl ht,
   hn⟩

/-- The semantic bridge for local RUP replay. The shape equality must be checked
against the actual local formula; it permits no arbitrary additional clauses. -/
theorem localUnsat_implies_clause {n : Nat} (f : DefaultFormula n)
    (hints : List (DefaultClause n)) (candidate : List (Literal (PosFin n)))
    (hu : Unsatisfiable (PosFin n) f)
    (hshape : DefaultFormula.toList f = hints ++
      candidate.map (fun l => DefaultClause.unit (Literal.negate l)))
    (a : PosFin n → Bool)
    (hh : ∀ c ∈ hints, Entails.eval a c) :
    ∃ l ∈ candidate, a l.1 = l.2 := by
  classical
  apply Classical.byContradiction
  intro hn
  apply hu a
  simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  change ∀ c ∈ DefaultFormula.toList f, Entails.eval a c
  rw [hshape]
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hh c hc
  · rcases List.mem_map.mp hc with ⟨l, hl, rfl⟩
    have hne : a l.1 ≠ l.2 := by
      intro he
      exact hn ⟨l, hl, he⟩
    change ([(l.1, !l.2)].any (fun t => decide (a t.1 = t.2))) = true
    simp only [List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]
    cases ha : a l.1 <;> cases hb : l.2 <;> simp_all

theorem localUnsat_implies_entails {n : Nat} (f : DefaultFormula n)
    (hints : List (DefaultClause n)) (candidate : DefaultClause n)
    (hu : Unsatisfiable (PosFin n) f)
    (hshape : DefaultFormula.toList f = hints ++
      candidate.clause.map (fun l => DefaultClause.unit (Literal.negate l)))
    (a : PosFin n → Bool) (hh : ∀ c ∈ hints, Entails.eval a c) :
    Entails.eval a candidate := by
  change (candidate.clause.any (fun l => decide (a l.1 = l.2))) = true
  simp only [List.any_eq_true, decide_eq_true_eq]
  exact localUnsat_implies_clause f hints candidate.clause hu hshape a hh


/-- The concrete initial formula corresponding to an indexed list of clauses. -/
def indexedFormula {n : Nat} (count : Nat) (clauseAt : Nat → DefaultClause n) :
    DefaultFormula n :=
  DefaultFormula.ofArray ((List.range count).map (fun i => some (clauseAt (i + 1)))).toArray

def indexedCNF {n : Nat} (count : Nat) (clauseAt : Nat → DefaultClause n) : CNF Nat :=
  ⟨((List.range count).map (fun i =>
    (clauseAt (i + 1)).clause.map (fun l => (l.1.val - 1, l.2)))).toArray⟩

theorem indexedFormula_sat {n : Nat} (count : Nat) (clauseAt : Nat → DefaultClause n)
    (a : PosFin n → Bool) (h : Entails.eval a (indexedFormula count clauseAt)) :
    ∀ i, i < count → Entails.eval a (clauseAt (i + 1)) := by
  simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq] at h
  change ∀ c ∈ DefaultFormula.toList (indexedFormula count clauseAt), Entails.eval a c at h
  intro i hi
  apply h
  simp [indexedFormula, DefaultFormula.toList, DefaultFormula.ofArray]
  exact ⟨i, hi, rfl⟩

/-- Converts the positive one-based internal variable model to ordinary zero-based CNF. -/
theorem indexedCNF_unsat {n : Nat} (count : Nat) (clauseAt : Nat → DefaultClause n)
    (hu : Unsatisfiable (PosFin n) (indexedFormula count clauseAt)) :
    (indexedCNF count clauseAt).Unsat := by
  intro a
  cases he : (indexedCNF count clauseAt).eval a with
  | false => rfl
  | true =>
    exfalso
    apply hu (fun v : PosFin n => a (v.val - 1))
    simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
    change ∀ c ∈ DefaultFormula.toList (indexedFormula count clauseAt),
      Entails.eval (fun v : PosFin n => a (v.val - 1)) c
    intro c hc
    simp [indexedFormula, DefaultFormula.toList, DefaultFormula.ofArray] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    have hclauses : ∀ j ∈ List.range count,
        CNF.Clause.eval a ((clauseAt (j + 1)).clause.map (fun l => (l.1.val - 1, l.2))) = true := by
      simpa [indexedCNF, CNF.eval] using he
    have hc := hclauses i (by simpa using hi)
    change ((clauseAt (i + 1)).clause.any
      (fun l => decide (a (l.1.val - 1) = l.2))) = true
    simpa [CNF.Clause.eval, List.any_map, beq_iff_eq] using hc

#print axioms localUnsat_implies_entails
#print axioms indexedFormula_sat
#print axioms indexedCNF_unsat
end CochromaticTwenty.CertificateKernel

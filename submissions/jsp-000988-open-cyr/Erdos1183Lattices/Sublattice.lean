import Erdos1183Lattices.Definitions

/-!
# Section C1: nonempty closed families are determined by `(⋂ F, ⋃ F, R F)`

For a nonempty family `F : Finset (Finset (Fin n))` that is `Closed` (under binary unions and
intersections) we show that `F` is closed under arbitrary nonempty sub-infima and sub-suprema,
that membership in `F` is characterised by the triple `(F.inf id, F.sup id, R F)` where
`R F i j` records "every member of `F` containing `j` contains `i`", and deduce the counting bound
`2 ^ (n ^ 2 + 2 * n)` on the number of nonempty closed families.
-/

namespace Erdos1183

variable {n : ℕ}

/-- `Closed` is decidable (it is a bounded quantifier over a `Finset`). -/
instance decidableClosed (F : Finset (Finset (Fin n))) : Decidable (Closed F) :=
  inferInstanceAs (Decidable (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F ∧ A ∩ B ∈ F))

/-! ### Closure under sub-infima and sub-suprema -/

/-- A nonempty subfamily of a closed family has its intersection in the family. -/
theorem inf_mem_of_closed {F : Finset (Finset (Fin n))} (hF : Closed F) :
    ∀ {S : Finset (Finset (Fin n))}, S ⊆ F → S.Nonempty → S.inf id ∈ F := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ h; simp at h
  | @insert A S hA ih =>
    intro hsub _
    have hAF : A ∈ F := hsub (Finset.mem_insert_self A S)
    rw [Finset.inf_insert]
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simpa using hAF
    · have hmem := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx)) hS
      simpa [Finset.inf_eq_inter] using (hF A hAF _ hmem).2

/-- A nonempty subfamily of a closed family has its union in the family. -/
theorem sup_mem_of_closed {F : Finset (Finset (Fin n))} (hF : Closed F) :
    ∀ {S : Finset (Finset (Fin n))}, S ⊆ F → S.Nonempty → S.sup id ∈ F := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ h; simp at h
  | @insert A S hA ih =>
    intro hsub _
    have hAF : A ∈ F := hsub (Finset.mem_insert_self A S)
    rw [Finset.sup_insert]
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simpa using hAF
    · have hmem := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx)) hS
      simpa [Finset.sup_eq_union] using (hF A hAF _ hmem).1

/-- The intersection of a nonempty closed family is a member. -/
theorem inf_mem {F : Finset (Finset (Fin n))} (hne : F.Nonempty) (hF : Closed F) :
    F.inf id ∈ F :=
  inf_mem_of_closed hF Finset.Subset.rfl hne

/-- The union of a nonempty closed family is a member. -/
theorem sup_mem {F : Finset (Finset (Fin n))} (hne : F.Nonempty) (hF : Closed F) :
    F.sup id ∈ F :=
  sup_mem_of_closed hF Finset.Subset.rfl hne

/-! ### The relation `R` and the principal sets -/

/-- `R F i j` says that every member of `F` containing `j` also contains `i`. -/
def R (F : Finset (Finset (Fin n))) : Fin n → Fin n → Bool :=
  fun i j => decide (∀ X ∈ F, j ∈ X → i ∈ X)

/-- The principal set of `j`: the intersection of all members of `F` containing `j`. -/
def P (F : Finset (Finset (Fin n))) (j : Fin n) : Finset (Fin n) :=
  (F.filter (fun X => j ∈ X)).inf id

/-- `P F j` consists exactly of the `i` related to `j` by `R F`. -/
theorem mem_P {F : Finset (Finset (Fin n))} {i j : Fin n} :
    i ∈ P F j ↔ R F i j = true := by
  simp only [P, R, decide_eq_true_eq]
  constructor
  · intro hi X hX hj
    have hmem : X ∈ F.filter (fun X => j ∈ X) := Finset.mem_filter.mpr ⟨hX, hj⟩
    have hle : (F.filter (fun X => j ∈ X)).inf id ⊆ X := Finset.inf_le hmem
    exact hle hi
  · intro h
    have hle : ({i} : Finset (Fin n)) ≤ (F.filter (fun X => j ∈ X)).inf id := by
      refine Finset.le_inf ?_
      intro X hX
      obtain ⟨hXF, hjX⟩ := Finset.mem_filter.mp hX
      simpa using h X hXF hjX
    exact hle (Finset.mem_singleton_self i)

/-- `R` is reflexive, hence `j ∈ P F j`. -/
theorem mem_P_self {F : Finset (Finset (Fin n))} {j : Fin n} : j ∈ P F j := by
  rw [mem_P]
  simp [R]

/-- If `j` lies in the union of `F`, the principal set of `j` is a member of `F`. -/
theorem P_mem {F : Finset (Finset (Fin n))} (hF : Closed F) {j : Fin n}
    (hj : j ∈ F.sup id) : P F j ∈ F := by
  obtain ⟨X, hXF, hjX⟩ := Finset.mem_sup.mp hj
  exact inf_mem_of_closed hF (Finset.filter_subset _ _)
    ⟨X, Finset.mem_filter.mpr ⟨hXF, hjX⟩⟩

/-! ### Reconstruction -/

/-- A nonempty closed family is exactly the set of `X` between `F.inf id` and `F.sup id`
that are closed downwards under `R F`. -/
theorem mem_iff {F : Finset (Finset (Fin n))} (hne : F.Nonempty) (hF : Closed F)
    (X : Finset (Fin n)) :
    X ∈ F ↔ F.inf id ⊆ X ∧ X ⊆ F.sup id ∧ ∀ i j, R F i j = true → j ∈ X → i ∈ X := by
  constructor
  · intro hX
    refine ⟨Finset.inf_le hX, Finset.le_sup (f := id) hX, ?_⟩
    intro i j hij hj
    have : ∀ Y ∈ F, j ∈ Y → i ∈ Y := by simpa [R] using hij
    exact this X hX hj
  · rintro ⟨h1, h2, h3⟩
    have key : ∀ S : Finset (Fin n), S ⊆ X → F.inf id ∪ S.sup (P F) ∈ F := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simpa using inf_mem hne hF
      | @insert a S ha ih =>
        intro hsub
        have haX : a ∈ X := hsub (Finset.mem_insert_self a S)
        have hSX : S ⊆ X := fun b hb => hsub (Finset.mem_insert_of_mem hb)
        have h4 : F.inf id ∪ S.sup (P F) ∈ F := ih hSX
        have h5 : P F a ∈ F := P_mem hF (h2 haX)
        have h6 := (hF _ h4 _ h5).1
        have heq : F.inf id ∪ (insert a S).sup (P F)
            = (F.inf id ∪ S.sup (P F)) ∪ P F a := by
          rw [Finset.sup_insert, Finset.sup_eq_union,
            Finset.union_comm (P F a), ← Finset.union_assoc]
        rw [heq]
        exact h6
    have hmem : F.inf id ∪ X.sup (P F) ∈ F := key X Finset.Subset.rfl
    have heq : F.inf id ∪ X.sup (P F) = X := by
      apply Finset.Subset.antisymm
      · refine Finset.union_subset h1 (Finset.sup_le ?_)
        intro j hj i hi
        exact h3 i j (mem_P.mp hi) hj
      · intro j hj
        refine Finset.mem_union_right _ ?_
        have : P F j ⊆ X.sup (P F) := Finset.le_sup hj
        exact this mem_P_self
    rw [heq] at hmem
    exact hmem

/-! ### Injectivity and the count -/

/-- Nonempty closed families are determined by the triple `(F.inf id, F.sup id, R F)`. -/
theorem key_injOn :
    Set.InjOn (fun F : Finset (Finset (Fin n)) => (F.inf id, F.sup id, R F))
      {F | F.Nonempty ∧ Closed F} := by
  intro F hF G hG h
  obtain ⟨hFne, hFc⟩ := hF
  obtain ⟨hGne, hGc⟩ := hG
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  ext X
  rw [mem_iff hFne hFc, mem_iff hGne hGc, h1, h2, h3]

/-- There are at most `2 ^ (n ^ 2 + 2 * n)` nonempty closed families of subsets of `Fin n`. -/
theorem card_closed_le (n : ℕ) :
    ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
      (fun F => F.Nonempty ∧ Closed F)).card ≤ 2 ^ (n ^ 2 + 2 * n) := by
  have hcard : ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
      (fun F => F.Nonempty ∧ Closed F)).card
      ≤ (Finset.univ :
          Finset (Finset (Fin n) × Finset (Fin n) × (Fin n → Fin n → Bool))).card := by
    refine Finset.card_le_card_of_injOn
      (fun F : Finset (Finset (Fin n)) => (F.inf id, F.sup id, R F))
      (fun F _ => Finset.mem_univ _) ?_
    intro F hF G hG h
    obtain ⟨-, hF⟩ := Finset.mem_filter.mp hF
    obtain ⟨-, hG⟩ := Finset.mem_filter.mp hG
    exact key_injOn hF hG h
  refine hcard.trans ?_
  rw [Finset.card_univ]
  have hc : Fintype.card (Finset (Fin n) × Finset (Fin n) × (Fin n → Fin n → Bool))
      = 2 ^ n * (2 ^ n * (2 ^ n) ^ n) := by
    simp [Fintype.card_prod, Fintype.card_finset]
  rw [hc, ← pow_mul, ← pow_add, ← pow_add]
  apply le_of_eq
  congr 1
  ring

end Erdos1183

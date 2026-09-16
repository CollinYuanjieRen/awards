import Mathlib

/-! Selecting distinct occurrence indices from stagewise finite avoidance. -/

namespace Jsp285

/-- If stage `n` admits a suitable index outside every set of at most `n`
previous indices, the choices can be made simultaneously and injectively. -/
theorem exists_injective_of_finite_avoidance
    (P : ℕ → ℕ → Prop)
    (h : ∀ n (s : Finset ℕ), s.card ≤ n →
      ∃ x, x ∉ s ∧ P n x) :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ n, P n (f n) := by
  classical
  let pick (n : ℕ) (s : Finset ℕ) : ℕ :=
    if hs : s.card ≤ n then Classical.choose (h n s hs) else 0
  have pick_spec (n : ℕ) (s : Finset ℕ) (hs : s.card ≤ n) :
      pick n s ∉ s ∧ P n (pick n s) := by
    simp only [pick, dif_pos hs]
    exact Classical.choose_spec (h n s hs)
  let U : ℕ → Finset ℕ :=
    Nat.rec ∅ (fun n s => insert (pick n s) s)
  have U_zero : U 0 = ∅ := rfl
  have U_succ (n : ℕ) : U (n + 1) = insert (pick n (U n)) (U n) := rfl
  have U_card (n : ℕ) : (U n).card = n := by
    induction n with
    | zero => simp [U_zero]
    | succ n ih =>
        rw [U_succ, Finset.card_insert_of_notMem]
        · omega
        · exact (pick_spec n (U n) (by omega)).1
  let f : ℕ → ℕ := fun n => pick n (U n)
  have f_fresh (n : ℕ) : f n ∉ U n := by
    exact (pick_spec n (U n) (by rw [U_card])).1
  have f_property (n : ℕ) : P n (f n) := by
    exact (pick_spec n (U n) (by rw [U_card])).2
  have earlier_mem (n i : ℕ) (hi : i < n) : f i ∈ U n := by
    induction n with
    | zero => omega
    | succ n ih =>
        rw [U_succ]
        by_cases hin : i = n
        · subst i
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ih (by omega))
  refine ⟨f, ?_, f_property⟩
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · exact f_fresh b (hab ▸ earlier_mem b a hablt)
  · exact f_fresh a (hab.symm ▸ earlier_mem a b hbalt)

end Jsp285

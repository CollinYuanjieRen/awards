import Erdos338Bateman

open Filter

#print axioms erdos_338_bateman_succ
#print axioms erdos_338_bateman

/-- Erdős #338, Bateman's observation for every `h ≥ 3`. -/
example (h : ℕ) (hh : 3 ≤ h) :
    IsBasisOfOrder (batemanSet h) h ∧ ¬ IsBasisOfOrder (batemanSet h) (h - 1) ∧
      ∀ t, ¬ HasRestrictedOrder (batemanSet h) t := erdos_338_bateman h hh

/-- The definitions, unfolded. -/
example (h : ℕ) : batemanSet h = {1} ∪ {x | 0 < x ∧ h ∣ x} := rfl
example (A : Set ℕ) (h : ℕ) : IsBasisOfOrder A h ↔
    ∀ᶠ n in atTop, ∃ l : List ℕ, (∀ x ∈ l, x ∈ A) ∧ l.length ≤ h ∧ l.sum = n := Iff.rfl
example (A : Set ℕ) (t : ℕ) : HasRestrictedOrder A t ↔
    ∀ᶠ n in atTop, ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card ≤ t ∧ ∑ x ∈ S, x = n := Iff.rfl

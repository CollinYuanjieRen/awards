import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
The weighted absent-color counting lemma for finite Boolean band codes.
-/

namespace WeightedBandCode

/-- Boolean choices on the colors not used at one vertex. -/
abbrev FreeBits {k : ℕ} (used : Finset (Fin k)) :=
  {m : Fin k // m ∉ used} → Bool

/-- Fill unused coordinates freely and retain the prescribed code on used coordinates. -/
def extend {V : Type*} {k : ℕ} (code : V → Fin k → Bool)
    (used : V → Finset (Fin k)) (v : V) (free : FreeBits (used v)) : Fin k → Bool :=
  fun m ↦ if hm : m ∈ used v then code v m else free ⟨m, hm⟩

/-- Pairwise separation on a commonly used color makes the family of free subcubes disjoint. -/
theorem extend_sigma_injective {V : Type*} [Fintype V] {k : ℕ}
    (code : V → Fin k → Bool) (used : V → Finset (Fin k))
    (hsep : ∀ i j, i ≠ j → ∃ m, m ∈ used i ∧ m ∈ used j ∧ code i m ≠ code j m) :
    Function.Injective
      (fun x : Σ v, FreeBits (used v) ↦ extend code used x.1 x.2) := by
  classical
  intro x y hxy
  have hv : x.1 = y.1 := by
    by_contra hne
    obtain ⟨m, hmi, hmj, hcode⟩ := hsep x.1 y.1 hne
    have hm := congrFun hxy m
    simp [extend, hmi, hmj] at hm
    exact hcode hm
  cases x with
  | mk vx fx =>
    cases y with
    | mk vy fy =>
      change vx = vy at hv
      subst vy
      congr
      funext m
      have hm := congrFun hxy m.1
      simpa [extend, m.2] using hm

/-- The number of free Boolean assignments is the expected complementary power of two. -/
theorem card_freeBits {k : ℕ} (used : Finset (Fin k)) :
    Fintype.card (FreeBits used) = 2 ^ (k - used.card) := by
  classical
  rw [Fintype.card_fun]
  simp

/-- Weighted absent-color capacity: the free subcube weights fit inside the Boolean cube. -/
theorem weightedBandCode_capacity {V : Type*} [Fintype V] {k : ℕ}
    (code : V → Fin k → Bool) (used : V → Finset (Fin k))
    (hsep : ∀ i j, i ≠ j → ∃ m, m ∈ used i ∧ m ∈ used j ∧ code i m ≠ code j m) :
    ∑ v, 2 ^ (k - (used v).card) ≤ 2 ^ k := by
  classical
  have hinj := extend_sigma_injective code used hsep
  have hcard : Fintype.card (Σ v, FreeBits (used v)) ≤ Fintype.card (Fin k → Bool) :=
    Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_sigma, card_freeBits] using hcard

#print axioms extend_sigma_injective
#print axioms card_freeBits
#print axioms weightedBandCode_capacity

end WeightedBandCode

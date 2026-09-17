import Mathlib
/-! Mathlib-only comparator for JSP-000716 (near-Sidon, at most one repeated sum). NOT imported by the build. -/
namespace NearSidonChallenge

def A : Finset ℕ := {1, 2, 4, 6, 7}

def pairs (A : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 < p.2)

def multiRepSums (A : Finset ℕ) : Finset ℕ :=
  ((pairs A).image (fun p => p.1 + p.2)).filter
    (fun s => 2 ≤ ((pairs A).filter (fun p => p.1 + p.2 = s)).card)

theorem A_card : A.card = 5 := by sorry
theorem A_at_most_one_repeat : (multiRepSums A).card ≤ 1 := by sorry
theorem A_subset : A ⊆ Finset.Icc 1 8 := by sorry

def pairsLoose (A : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 ≤ p.2)

def multiRepSumsLoose (A : Finset ℕ) : Finset ℕ :=
  ((pairsLoose A).image (fun p => p.1 + p.2)).filter
    (fun s => 2 ≤ ((pairsLoose A).filter (fun p => p.1 + p.2 = s)).card)

theorem A_multiRepSums : multiRepSums A = {8} := by sorry
theorem A_multiRepSumsLoose : multiRepSumsLoose A = {8} := by sorry
theorem A_at_most_one_repeat_loose : (multiRepSumsLoose A).card ≤ 1 := by sorry

end NearSidonChallenge

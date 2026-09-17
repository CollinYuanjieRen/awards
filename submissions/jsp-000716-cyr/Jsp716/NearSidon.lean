import Mathlib

/-!
# JSP-000716 — a near-Sidon size-5 certificate

We exhibit `A = {1, 2, 4, 6, 7} ⊆ {1, …, 8}` and verify that among the ten
unordered pairs `{x, y} ⊆ A` with `x < y`, exactly one sum value is attained
more than once, namely `8 = 1 + 7 = 2 + 6`.

Only this finite certificate is claimed; nothing here asserts anything about
the (open) asymptotic maximum size of such a set.
-/

namespace NearSidon

def A : Finset ℕ := {1, 2, 4, 6, 7}

/-- Unordered pairs (x < y) of A. -/
def pairs (A : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 < p.2)

/-- Sum-values represented by two or more distinct unordered pairs. -/
def multiRepSums (A : Finset ℕ) : Finset ℕ :=
  ((pairs A).image (fun p => p.1 + p.2)).filter
    (fun s => 2 ≤ ((pairs A).filter (fun p => p.1 + p.2 = s)).card)

theorem A_card : A.card = 5 := by decide

/-- The unique multiply-represented sum is `8 = 1 + 7 = 2 + 6`. -/
theorem A_multiRepSums : multiRepSums A = {8} := by decide

/-- At most one sum-value has multiple representations. -/
theorem A_at_most_one_repeat : (multiRepSums A).card ≤ 1 := by decide

theorem A_subset : A ⊆ Finset.Icc 1 8 := by decide

/-- Ordered pairs (x ≤ y) of A: the standard Sidon/`B₂` convention, doubles `2x` allowed. -/
def pairsLoose (A : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 ≤ p.2)

/-- Sum-values represented by two or more distinct pairs `x ≤ y` (doubles allowed). -/
def multiRepSumsLoose (A : Finset ℕ) : Finset ℕ :=
  ((pairsLoose A).image (fun p => p.1 + p.2)).filter
    (fun s => 2 ≤ ((pairsLoose A).filter (fun p => p.1 + p.2 = s)).card)

/-- Under the standard convention (doubles allowed) the unique multiply-represented sum is still
`8 = 1 + 7 = 2 + 6 = 4 + 4`; so the certificate holds under both conventions. -/
theorem A_multiRepSumsLoose : multiRepSumsLoose A = {8} := by decide

theorem A_at_most_one_repeat_loose : (multiRepSumsLoose A).card ≤ 1 := by decide

end NearSidon

#print axioms NearSidon.A_card
#print axioms NearSidon.A_at_most_one_repeat
#print axioms NearSidon.A_subset
#print axioms NearSidon.A_multiRepSums
#print axioms NearSidon.A_multiRepSumsLoose
#print axioms NearSidon.A_at_most_one_repeat_loose

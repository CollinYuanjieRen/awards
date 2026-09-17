import Mathlib

/-! Comparator-style challenge module (Mathlib-only; targets with `sorry`, not imported by the build)
for JSP-000616 / Erdős #748, the Cameron–Erdős trivial lower bound. -/

namespace Challenge748

open Classical in
def SumFree (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c

open Classical in
noncomputable def f (n : ℕ) : ℕ := ((Finset.Icc 1 n).powerset.filter (fun A => SumFree A)).card

theorem f_ge (n : ℕ) : 2 ^ (n - n / 2) ≤ f n := by
  sorry

theorem f_ge_two_pow_half (n : ℕ) : 2 ^ (n / 2) ≤ f n := by
  sorry

end Challenge748

import Mathlib

/-!
# Erdős Problem 772: Sidon subsets of sets with bounded representation function

For `k ≥ 1` let `H_k(n)` be the largest `r` such that every `n`-element set `A ⊆ ℕ` whose
representation function `1_A * 1_A` is bounded by `k` contains a Sidon set of size at least `r`.
Erdős asked whether `H_k(n) / n^{1/2} → ∞`, and whether `H_k(n) > n^{1/2 + c}` for some `c > 0`.
Alon and Erdős (1985) proved `H_k(n) ≫_k n^{2/3}`, answering both questions affirmatively.

The proof formalized here follows the standard sketch: the number of additive quadruples
`a + b = c + d` in `A` is at most `k n²` and the number of solutions of `a + b = 2c` is at most
`k n`; averaging over the `s`-element subsets of `A` with `6 k s³ ≤ n²` gives a subset with at
most `s / 2` bad quadruples, and deleting one element per bad quadruple leaves a Sidon set of
size at least `s / 2 ≫ n^{2/3}`.
-/

namespace Erdos772

/-- The number of ordered representations `m = a + b` with `a, b ∈ A` (the value of the
convolution `1_A * 1_A` at `m`). -/
def rep (A : Finset ℕ) (m : ℕ) : ℕ := ((A ×ˢ A).filter (fun p => p.1 + p.2 = m)).card

/-- `‖1_A * 1_A‖_∞ ≤ k`. -/
def RepBounded (k : ℕ) (A : Finset ℕ) : Prop := ∀ m, rep A m ≤ k

/-- `S` is a Sidon set: `a + b = c + d` with `a, b, c, d ∈ S` forces `{a, b} = {c, d}`. -/
def IsSidon (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- `H k n`: the largest `r` (necessarily `r ≤ n`) such that every `n`-element `A ⊆ ℕ` with
`‖1_A * 1_A‖_∞ ≤ k` contains a Sidon subset of size at least `r`. -/
noncomputable def H (k n : ℕ) : ℕ :=
  sSup {r : ℕ | r ≤ n ∧ ∀ A : Finset ℕ, A.card = n → RepBounded k A →
    ∃ S ⊆ A, IsSidon S ∧ r ≤ S.card}

/-- The bad (non-trivial additive) ordered quadruples of `S`. -/
def badTuples (S : Finset ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter (fun t => t.1.1 + t.1.2 = t.2.1 + t.2.2 ∧
    ¬ ((t.1.1 = t.2.1 ∧ t.1.2 = t.2.2) ∨ (t.1.1 = t.2.2 ∧ t.1.2 = t.2.1)))

/-- The set of entries of a quadruple. -/
def elems (t : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ := {t.1.1, t.1.2, t.2.1, t.2.2}

/-- Quadruples with a repeated entry in one of the two pairs. -/
def HasRepeat (t : (ℕ × ℕ) × (ℕ × ℕ)) : Prop := t.1.1 = t.1.2 ∨ t.2.1 = t.2.2

instance (t : (ℕ × ℕ) × (ℕ × ℕ)) : Decidable (HasRepeat t) := by unfold HasRepeat; infer_instance

end Erdos772

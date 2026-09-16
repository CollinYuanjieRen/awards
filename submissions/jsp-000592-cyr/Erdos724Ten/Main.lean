import Mathlib

/-!
# Erdős Problem #724: two orthogonal Latin squares of order 10 (the falsity of Euler's conjecture)

Let `f(n)` be the maximum number of mutually orthogonal Latin squares of order `n`.  Erdős asked
whether `f(n) ≫ n^{1/2}`; this is OPEN and is not addressed here.  Euler conjectured `f(n) = 1`
for `n ≡ 2 (mod 4)`; Parker (1959) exhibited a pair of orthogonal Latin squares of order `10`, and
Bose–Shrikhande–Parker (1960) proved `f(n) ≥ 2` for all `n ≥ 7`.  This file certifies the
order-`10` case: an explicit pair of orthogonal Latin squares of order `10`, verified by `decide`.
Consequently `f(10) ≥ 2`, refuting Euler's conjecture at its smallest open order.

The definitions `IsLatinSquare`, `IsOrthogonal` and `IsMOLS` are stated from scratch (there is no
formal-conjectures statement of #724).
-/

/-- A Latin square of order `n`: every row and every column is a permutation of `Fin n`. -/
def IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Injective (L i)) ∧ (∀ j, Function.Injective fun i ↦ L i j)

/-- Two squares are orthogonal if the pairs `(L i j, M i j)` are pairwise distinct, i.e. every
ordered pair of symbols occurs exactly once when the squares are superimposed. -/
def IsOrthogonal {n : ℕ} (L M : Fin n → Fin n → Fin n) : Prop :=
  Function.Injective fun ij : Fin n × Fin n ↦ (L ij.1 ij.2, M ij.1 ij.2)

/-- `k` mutually orthogonal Latin squares of order `n`. -/
def IsMOLS {n : ℕ} (k : ℕ) (S : Fin k → Fin n → Fin n → Fin n) : Prop :=
  (∀ s, IsLatinSquare (S s)) ∧ ∀ s t, s ≠ t → IsOrthogonal (S s) (S t)

/-- The first square of the certified orthogonal pair (ref/orthogonal-pair-order10.json). -/
def squareA : Fin 10 → Fin 10 → Fin 10 :=
  ![
    ![5, 8, 4, 1, 2, 0, 3, 9, 6, 7],
    ![2, 3, 1, 6, 8, 5, 7, 4, 9, 0],
    ![3, 4, 0, 9, 5, 1, 2, 7, 8, 6],
    ![9, 0, 8, 5, 4, 2, 6, 1, 7, 3],
    ![6, 2, 7, 4, 1, 3, 8, 5, 0, 9],
    ![1, 9, 6, 2, 3, 7, 4, 0, 5, 8],
    ![8, 1, 2, 7, 9, 4, 0, 6, 3, 5],
    ![0, 6, 9, 3, 7, 8, 5, 2, 4, 1],
    ![4, 7, 5, 8, 0, 6, 9, 3, 1, 2],
    ![7, 5, 3, 0, 6, 9, 1, 8, 2, 4]]

/-- The second square of the certified orthogonal pair. -/
def squareB : Fin 10 → Fin 10 → Fin 10 :=
  ![
    ![6, 5, 0, 7, 3, 4, 1, 8, 2, 9],
    ![1, 0, 9, 4, 8, 3, 2, 6, 7, 5],
    ![7, 4, 2, 3, 0, 8, 6, 5, 9, 1],
    ![0, 8, 1, 2, 9, 7, 5, 3, 4, 6],
    ![3, 2, 7, 8, 5, 9, 0, 1, 6, 4],
    ![2, 1, 8, 9, 4, 6, 7, 0, 5, 3],
    ![4, 6, 5, 0, 2, 1, 3, 9, 8, 7],
    ![9, 7, 6, 5, 1, 2, 8, 4, 3, 0],
    ![5, 3, 4, 6, 7, 0, 9, 2, 1, 8],
    ![8, 9, 3, 1, 6, 5, 4, 7, 0, 2]]

theorem squareA_isLatinSquare : IsLatinSquare squareA := by
  unfold IsLatinSquare
  decide

theorem squareB_isLatinSquare : IsLatinSquare squareB := by
  unfold IsLatinSquare
  decide

theorem squareA_squareB_isOrthogonal : IsOrthogonal squareA squareB := by
  unfold IsOrthogonal
  decide

/-- Orthogonality is symmetric. -/
theorem IsOrthogonal.symm {n : ℕ} {L M : Fin n → Fin n → Fin n} (h : IsOrthogonal L M) :
    IsOrthogonal M L := by
  intro x y hxy
  apply h
  simp only [Prod.mk.injEq] at hxy ⊢
  exact ⟨hxy.2, hxy.1⟩

/-- **Erdős Problem #724, the order-10 certificate (Parker; Bose–Shrikhande–Parker).**  There
exist two mutually orthogonal Latin squares of order `10`, i.e. `f(10) ≥ 2`, refuting Euler's
conjecture that `f(n) = 1` for `n ≡ 2 (mod 4)` at `n = 10`.  The asymptotic question
`f(n) ≫ n^{1/2}` is open and not claimed. -/
theorem erdos_724_two_mols_ten : ∃ S : Fin 2 → Fin 10 → Fin 10 → Fin 10, IsMOLS 2 S := by
  refine ⟨![squareA, squareB], ?_, ?_⟩
  · intro s
    fin_cases s
    · exact squareA_isLatinSquare
    · exact squareB_isLatinSquare
  · intro s t hst
    fin_cases s <;> fin_cases t
    · exact absurd rfl hst
    · exact squareA_squareB_isOrthogonal
    · exact squareA_squareB_isOrthogonal.symm
    · exact absurd rfl hst

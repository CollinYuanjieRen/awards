import Mathlib

/-!
# Erdős Problem 806: small bases for square-root-size sets

Erdős and Newman asked: if `A ⊆ {1, …, n}` has `|A| ≤ √n`, must there be `B ⊂ ℤ` with
`|B| = o(√n)` and `A ⊆ B + B`? Alon, Bukh and Sudakov (2009) proved that there is. This
development gives an elementary deterministic proof of the `o(√n)` statement.

Construction. Fix `k ≥ 1` and `q ≥ 1`, `M = q^k`. Cut `[0, n]` into blocks of length `M`, cut the
part of `A` in each block into chunks of at most `k` elements, and for every chunk choose a shift
`h < M`, digit by digit in base `q`, so that the `p`-th element of the chunk plus `h` has base-`q`
digit `p` equal to `0`. Then `B` consists of the "universal set" `U` of numbers below `M` with some
zero digit, its translate `U + M`, and one point `jM − h` per chunk of block `j`.
-/

namespace Erdos806

/-- `B` is a basis for `A`: every element of `A` is a sum of two elements of `B`. -/
def HasBasis (A : Finset ℕ) (B : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∃ b ∈ B, ∃ b' ∈ B, (a : ℤ) = b + b'

/-- Base-`q` digit at position `p` of `x`. -/
def digit (q p x : ℕ) : ℕ := x / q ^ p % q

/-- The universal set: numbers below `q ^ k` with some base-`q` digit at a position `< k` equal
to zero. -/
def univSet (q k : ℕ) : Finset ℕ :=
  (Finset.range (q ^ k)).filter (fun u => ∃ p < k, digit q p u = 0)

end Erdos806

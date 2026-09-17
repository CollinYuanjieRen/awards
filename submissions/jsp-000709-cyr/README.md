# JSP-000709 / Erdős Problem #856 — scoped component: the double-counting bound

**Scope (honest).** Erdős defines `f_k(N)` as the maximum of `∑_{n ∈ A} 1/n` over `A ⊆ {1, …, N}`
containing no `k`-subset whose pairwise least common multiples are all equal, and asks to
estimate `f_k(N)`; the problem is **open** (Tang–Zhang's bounds are *not* formalized here).  This
package proves the elementary part of Erdős's bound recorded on the problem page
(erdosproblems.com/856): *"let A be such a set.  This in particular implies that, for every t,
there are < k solutions to t = ap with a ∈ A and p prime, whence
∑_{n∈A} 1/n · ∑_{p<N} 1/p < k ∑_{t<N²} 1/t."*  The final step `≪ log N / log log N` (Mertens'
estimate) is not claimed.

**Definitions** (`Erdos856DoubleCounting/Main.lean`, namespace `Erdos856`; no formal-conjectures
rendering exists, so these are ours).  `NoEqualLcm k A := ¬ ∃ B ⊆ A, B.card = k ∧ ∃ L, ∀ a ∈ B,
∀ b ∈ B, a ≠ b → Nat.lcm a b = L`; `solutions A t` = the pairs `(a, p)` with `a ∈ A`, `p` prime,
`a * p = t`.  Sums are over `ℚ` with Lean's convention `1/0 = 0`.

**Statements.**  `card_solutions_lt : NoEqualLcm k A → ∀ t, (solutions A t).card < k`;
`erdos_856_double_counting (hk : 1 ≤ k) (hN : 2 ≤ N) (hAN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N)
(hA : NoEqualLcm k A) : (∑ a ∈ A, 1/a) * (∑ p ∈ (range N).filter Nat.Prime, 1/p) < k * ∑ t ∈
range (N ^ 2), 1/t`; graded root `erdos_856_double_counting_closed` (its closed `¬∃` form).

**Proof idea.**  `k` distinct solutions `t = a_i p_i` have distinct `a_i` and distinct primes, and
`lcm(t/p_i, t/p_j) = t`, giving a forbidden `k`-subset.  Reindexing `∑_a ∑_p 1/(ap)` by
`t = ap < N²` gives `∑_t |solutions A t| / t ≤ (k − 1) ∑_t 1/t < k ∑_t 1/t` (`N ≥ 2` makes the
last sum positive).

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos856DoubleCounting/Main.lean`, `Erdos856DoubleCounting.lean` (library root),
`Audit.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`,
`verification.txt`, this README.

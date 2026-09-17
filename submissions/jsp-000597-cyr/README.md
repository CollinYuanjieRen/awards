# JSP-000597 / Erdős Problem #729 — scoped component: `a! b! ∣ n! ⇒ a + b ≤ n + O(log n)`

**Scope (honest).** Erdős asked whether `a + b ≤ n + O(log n)` still follows from `a! b! ∣ n!`
"ignoring what happens on small primes".  That question is **proved** (Barreto and Price (the page writes "Leeham"), with
a Lean proof by Barreto in plby/lean-proofs of the formal-conjectures statement `erdos_729`) and
is *not* claimed here.  This package proves the classical fact recorded on the problem page
(erdosproblems.com/729): *"Erdős proved that if a!b! ∣ n! then a+b ≤ n+O(log n).  The proof is
easy, and can be done with powers of 2 alone: Legendre's formula implies that if 2^k is the
highest power of 2 dividing n! then k = n+O(log n), and hence if a!b! ∣ n! then
a+b ≤ n+O(log n)."*, with explicit constants.

**Statements** (`Erdos729LogBound/Main.lean`, namespace `Erdos729`; our own statements, no local
definitions):

- `padicValNat_two_factorial_bounds (n) : padicValNat 2 n ! ≤ n ∧ n ≤ padicValNat 2 n ! + (Nat.log 2 n + 1)`
  (Legendre for `p = 2`: `k = n − s₂(n)` with `0 ≤ s₂(n) ≤ log₂ n + 1`);
- `add_le_of_factorial_mul_factorial_dvd (a b n) (h : a ! * b ! ∣ n !) : a + b ≤ n + 2 * Nat.log 2 n + 2`;
- `erdos_729_erdos_bound : ∃ C : ℕ, ∀ a b n, a ! * b ! ∣ n ! → a + b ≤ n + C * (Nat.log 2 n + 1)`;
- graded root `erdos_729_erdos_bound_closed : ¬ ∃ a b n : ℕ, a ! * b ! ∣ n ! ∧ n + 2 * Nat.log 2 n + 2 < a + b`.

**Proof idea.**  `v₂(a!) + v₂(b!) ≤ v₂(n!)` with `v₂(m!) = m − s₂(m)` (Mathlib's
`sub_one_mul_padicValNat_factorial`) and `s₂(m) ≤ log₂ m + 1`, plus `a, b ≤ n`.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos729LogBound/Main.lean`, `Erdos729LogBound.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

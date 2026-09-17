# JSP-000319 / Erdős Problem #386 — scoped component: the page's explicit examples

**Scope (honest).** Erdős and Graham asked whether `C(n, k)` (`2 ≤ k ≤ n − 2`) can be a product
of consecutive primes infinitely often; the problem is **open** and is *not* claimed here.  This
package formalizes the settled facts recorded on the problem page (erdosproblems.com/386):
*"Weisenberg has provided four easy examples that show Erdős and Graham were too optimistic
here: C(7,3) = 5·7, C(10,4) = 2·3·5·7, C(14,4) = 7·11·13, C(15,6) = 5·7·11·13.  The known
values of n for which C(n,2) is the product of consecutive primes are 4, 6, 15, 21, 715."*  The
list `4, 6, 15, 21, 715` is claimed only as known examples (membership), not as complete.

**Shape.**  "Product of consecutive primes" is taken from the formal-conjectures statement
`Erdos386.erdos_386`: `∃ p q : ℕ, m = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i`, where
`Nat.nth Nat.Prime i` is the `i`-th prime (`2, 3, 5, …`, indexed from `0`).

**Statements** (`Erdos386Examples/Main.lean`, namespace `Erdos386`):

- `weisenberg_values : C(7,3) = 5·7 ∧ C(10,4) = 2·3·5·7 ∧ C(14,4) = 7·11·13 ∧ C(15,6) = 5·7·11·13`;
- `weisenberg_examples`: each of the four is `IsConsecutivePrimeProduct`;
- `exists_middle_consecutivePrimeProduct : ∃ n k, 3 ≤ k ∧ k ≤ n − 3 ∧ IsConsecutivePrimeProduct (n.choose k)`
  (refuting the "probably this can never happen for `3 ≤ k ≤ n − 3`" expectation);
- `choose_two_examples : ∀ n ∈ ({4, 6, 15, 21, 715} : Finset ℕ), IsConsecutivePrimeProduct (n.choose 2)`;
- graded root `erdos_386_examples_closed`, the conjunction of the four Weisenberg instances and
  the `C(n, 2)` list, each spelled out as `∃ p q, … = ∏ i ∈ Finset.Ico p q, Nat.nth Nat.Prime i`.

**Proof idea.**  Explicit indices (`C(7,3) = p₂p₃`, `C(10,4) = p₀⋯p₃`, `C(14,4) = p₃p₄p₅`,
`C(15,6) = p₂⋯p₅`, `C(715,2) = 255255 = p₁⋯p₆`), the prime values `p₅ = 13`, `p₆ = 17` from
`Nat.nth_count` with kernel-checked `Nat.count`, and kernel `decide`/`norm_num` for the products
and binomials (no `native_decide`).

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos386Examples/Main.lean`, `Erdos386Examples.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

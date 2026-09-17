# JSP-000681 / Erdős Problem #825 — scoped component: the necessary condition `C > 2`

**Scope (honest).** Benkoski and Erdős asked for an absolute constant `C > 0` such that every `n`
with `σ(n) > C n` is a sum of distinct proper divisors of `n`.  The problem is **solved** (Larsen),
and the formal-conjectures statement `erdos_825` has a Lean proof by Alexeev in plby/lean-proofs;
neither the existence of `C` nor Larsen's theorem is claimed here.  This package formalizes the
remark recorded on the problem page (erdosproblems.com/825): *"We must have `C > 2` since
`σ(70) = 144` but `70` is not the distinct sum of integers from `{1, 2, 5, 7, 10, 14, 35}`"*.

**Statements** (`Erdos825NecessaryCond/Main.lean`):

- `Erdos825.erdos_825.variants.necessary_cond (C : ℝ) (hC : 0 < C)
  (h : ∀ (n : ℕ) (_ : σ 1 n > C * n), ∃ s ⊆ n.properDivisors, n = s.sum id) : 2 < C` — the
  formal-conjectures statement, copied verbatim (it is a `sorry` there);
- `Erdos825.seventy_witness : (70 : ℕ).properDivisors = {1, 2, 5, 7, 10, 14, 35} ∧ σ 1 70 = 144 ∧
  ¬ ∃ s ⊆ (70 : ℕ).properDivisors, 70 = s.sum id`;
- graded root `erdos_825_necessary_cond_closed : ¬ ∃ C : ℝ, 0 < C ∧ C ≤ 2 ∧
  ∀ (n : ℕ) (_ : σ 1 n > C * n), ∃ s ⊆ n.properDivisors, n = s.sum id`.

**Disclosure.** That `70` is not a sum of distinct proper divisors is Mathlib's `Nat.weird_seventy`
(`70` is a weird number); this package adds the kernel-checked computations `σ 1 70 = 144` and
`properDivisors 70 = {1, 2, 5, 7, 10, 14, 35}` and the deduction `2 < C`.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]` for all
three theorems; no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See
`verification.txt`.  Before submission the package passed MerLean Heavy's research-grade audit
(target/goal contracts, kernel evidence, definition independence, two independent audits).

**Files.** `Erdos825NecessaryCond/Main.lean`, `Erdos825NecessaryCond.lean` (library root),
`Audit.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`,
`verification.txt`, this README.

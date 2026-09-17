# JSP-000130 / Erdős Problem #123 — scoped component: the "no common factor" counterexample

**Scope (honest).** Erdős asked whether, for pairwise coprime `a, b, c > 1`, every large integer is
a sum of distinct integers of the form `a^k b^l c^m` none of which divides another (a `d`-complete
sequence).  That problem is **proved** (Snyder, with a Lean proof of the formal-conjectures
statement `erdos_123` in plby/lean-proofs) and is *not* claimed here.  This package proves the
counterexample recorded on the problem page (erdosproblems.com/123): *"he also suggests the
weaker assumption that a,b,c have no common factor, but it is false under this assumption: for
example if a=6, b=10, and c=15, then any a^k b^l c^m is 0 (mod 3) unless k=m=0, when it is
1 (mod 3), and so any integer 2 (mod 3) requires at least two summands of the shape 10^l, one of
which must divide the other."*

**Definitions.**  `IsDComplete` and `PairwiseCoprime` are copied verbatim from the
formal-conjectures file for the problem; the set `{6^k 10^l 15^m}` is written, as in that file's
`powers_2_3` variant, as `(↑(powers 6) * ↑(powers 10) * ↑(powers 15) : Set ℕ)`.

**Statements** (`Erdos123Counterexample/Main.lean`, namespace `Erdos123`):
`gcd_six_ten_fifteen : Nat.gcd (Nat.gcd 6 10) 15 = 1 ∧ ¬ PairwiseCoprime 6 10 15`;
`mem_powers_mod_three` (every member is `0 (mod 3)` or a power of `10`, which is `1 (mod 3)`);
`not_isDComplete_six_ten_fifteen : ¬ IsDComplete (↑(powers 6) * ↑(powers 10) * ↑(powers 15))`;
graded root `erdos_123_no_common_factor_counterexample` (`gcd = 1 ∧ ¬ IsDComplete …`).

**Proof idea.**  For any threshold `N`, the integer `3N + 2` is `2 (mod 3)`; a representation by
members of the set would need at least two pure powers of `10` (the only summands not divisible
by `3`), and one of two distinct powers of `10` divides the other, contradicting the antichain
condition.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos123Counterexample/Main.lean`, `Erdos123Counterexample.lean` (library root),
`Audit.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`,
`verification.txt`, this README.

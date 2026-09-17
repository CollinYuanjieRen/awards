# JSP-000334 / Erdős Problem #407 — scoped component: the four-representation identities

**Scope (honest).** Newman's conjecture (Erdős #407) that the number `w(n)` of solutions of
`n = 2^a + 3^b + 2^c 3^d` is bounded is **proved** (Evertse–Győry–Stewart–Tijdeman; effective
bounds by Bajpai–Bennett) and is *not* formalized here.  This package verifies the identities
recorded on the problem page (erdosproblems.com/407): *"There are infinitely many n with
w(n) = 4, given by the identities 2^{a−1}+3^b+2^{a−1}3^0 = 2^{a−2}+3^b+2^{a−2}3^1 =
2^a+3^{b−1}+2·3^{b−1} = 2^a+3^{b−2}+2^3 3^{b−2}"*: for `a ≥ 3`, `b ≥ 2` the four exponent
quadruples are pairwise distinct solutions for `n = 2^{a−1} + 3^b + 2^{a−1}`, hence `w(n) ≥ 4`
for infinitely many `n`.  The matching upper bound `w(n) ≤ 4` (so that `w(n) = 4` exactly) is
Bajpai–Bennett's theorem and is *not* claimed; only `≥ 4` is.

**Definitions** (`Erdos407Identities/Main.lean`, namespace `Erdos407`).  `Rep`, `Rep.value`,
`solutions` and `w` are copied verbatim from the plby/lean-proofs comparator statement of the
problem (`w` counts ordered exponent quadruples, the literal convention of the problem
statement); `N a b = 2^(a−1) + 3^b + 2^(a−1)`.

**Statements.**  `four_identities (a b) (ha : 3 ≤ a) (hb : 2 ≤ b)` (the four quadruples all have
value `N a b`); `four_le_w (a b) (ha) (hb) : 4 ≤ w (N a b)`; `erdos_407_infinite_four :
{n | 4 ≤ w n}.Infinite`; graded root `erdos_407_identities_closed` (their conjunction, with the
infinitude stated as `¬ Set.Finite`).

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos407Identities/Main.lean`, `Erdos407Identities.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

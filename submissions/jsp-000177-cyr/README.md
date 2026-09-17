# JSP-000177 / Erdős Problem #183 — scoped component: the pigeonhole recurrence for `R(3;k)`

**Scope (honest).** Erdős asked to determine `lim R(3;k)^{1/k}`, where `R(3;k)` is the least `n`
such that every `k`-colouring of the edges of `K_n` has a monochromatic triangle.  That question
is **solved** (the limit is infinite; OpenAI, with a Lean proof) and is *not* claimed here.  This
package proves the classical fact recorded on the problem page (erdosproblems.com/183): *"An easy
pigeonhole argument shows that R(3;k) ≤ 2 + k(R(3;k−1) − 1)"* — for every `k ≥ 1` — together with
the finiteness of `R(3;k)` that makes the `sInf` in its definition meaningful.  The corollary
`R(3;k) ≤ ⌈e k!⌉` is not formalized.

**Definitions** (`Erdos183Recurrence/Main.lean`).  `ForcesMonochromaticTriangle` and
`multicolourTriangleRamsey` are copied verbatim from the formal-conjectures file for the problem,
and `TopEdgeLabeling.CliqueFree` from its `FormalConjecturesForMathlib` dependency.  With these
definitions `R(3;0) = 2` and `R(3;1) = 3`.

**Statements.**  `forces_mono` (forcing is monotone in the number of vertices); `forces_succ`
(the pigeonhole step: `K_r` forcing on `k` colours gives `K_{2+(k+1)(r−1)}` forcing on `k + 1`
colours); `exists_forces (k) : ∃ n, ForcesMonochromaticTriangle n k`; `erdos_183_recurrence (k)
(hk : 1 ≤ k) : multicolourTriangleRamsey k ≤ 2 + k * (multicolourTriangleRamsey (k - 1) - 1)`;
graded root `erdos_183_recurrence_closed` (finiteness for every `k`, and no `k ≥ 1` violates the
recurrence).

**Proof idea.**  In a `k`-colouring of `K_n` with `n = 2 + k(r − 1)`, a vertex has `1 + k(r − 1)`
neighbours, so some colour `c` occurs on at least `r` of its edges; either two of those neighbours
are joined in colour `c` (a monochromatic triangle) or they span a `(k − 1)`-colouring of `K_r`,
which forces a monochromatic triangle by the choice of `r = R(3;k−1)`.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos183Recurrence/Main.lean`, `Erdos183Recurrence.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

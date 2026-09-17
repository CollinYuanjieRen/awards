# JSP-000776 / Erdős Problem #934 — scoped component: `h_1(d) = d + 1` for `d ≥ 3` (and `h_1(2) = 4`)

**Scope (honest).** Erdős and Nešetřil define `h_t(d)` as the minimal `m` such that every graph
with `m` edges and maximum degree `≤ d` contains two edges at distance `≥ t`, and ask to
estimate `h_t(d)`; the problem is **open** and is *not* addressed here.  The problem page
(erdosproblems.com/934) records *"It is easy to see that h_t(d) ≤ 2d^t always and h_1(d) = d+1."*
This package proves the second clause for every `d ≥ 3`, and records that **it fails for
`d = 2`**: the triangle has `3` edges, maximum degree `2`, and no two disjoint edges, so
`h_1(2) = 4`.  (The bound `h_t(d) ≤ 2d^t` is not formalized.)

**Definitions** (`Erdos934HOne/Main.lean`, namespace `Erdos934`; no formal-conjectures rendering
exists).  For `t = 1`, two edges are at distance `≥ 1` exactly when they are disjoint.
`Forces₁ d m` says every finite simple graph with exactly `m` edges and maximum degree `≤ d` has
two disjoint edges; `h₁ d = sInf {m | Forces₁ d m}`.  (Deleting edges preserves disjointness of
the remaining ones, so "exactly `m`" and "at least `m`" edges define the same `h₁`.)

**Statements.**  `exists_common_vertex` (a graph with `≥ 4` edges, no two disjoint, is a star);
`forces_of_lt (h4 : 4 ≤ m) (hdm : d < m) : Forces₁ d m`; `not_forces_of_le (hm : m ≤ d)`
(the star `K_{1,m}`); `not_forces_two_three` (the triangle); `erdos_934_h_one (d) (hd : 3 ≤ d) :
IsLeast {m | Forces₁ d m} (d + 1) ∧ h₁ d = d + 1`; `erdos_934_h_one_two : IsLeast {m | Forces₁ 2 m} 4 ∧
h₁ 2 = 4`; graded root `erdos_934_h_one_closed` (their closed conjunction).

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos934HOne/Main.lean`, `Erdos934HOne.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

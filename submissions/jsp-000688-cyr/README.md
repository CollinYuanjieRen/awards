# JSP-000688 / Erdős Problem #832 — scoped component: the Fano-plane witness for `r = k = 3`

**Scope (honest).** Erdős conjectured that, for `r ≥ 3` and `k` large, every `r`-uniform
hypergraph with chromatic number `k` has at least `C((r−1)(k−1)+1, r)` edges.  That conjecture
was **disproved** by Alon (with a Lean formalization of the disproof in plby/lean-proofs) and
is *not* claimed here.  This package verifies the witness recorded on the problem page
(erdosproblems.com/832): *"Erdős asked for k to be large in this conjecture since he knew it to be
false for r=k=3, as witnessed by the Steiner triples with 7 vertices and 7 edges."*

**Definitions** (`Erdos832Fano/Main.lean`, namespace `Erdos832`).  `FiniteHypergraph`,
`IsUniform`, `ProperColoring`, `Colorable` and `HasChromaticNumber` are copied verbatim from the
plby Lean file for the main result (Apache 2.0), so the statement is in the same language as the
existing formalization of Alon's disproof (which does not state the Fano witness).  `fano` is the
Fano plane on `Fin 7` with its seven lines as edges (the Steiner triple system `STS(7)`).

**Statements.**  `fano_uniform_card : fano.IsUniform 3 ∧ fano.edges.card = 7 ∧ Fintype.card fano.V = 7`;
`fano_colorable_three`; `fano_not_colorable_two` (every `2`-colouring has a monochromatic line;
kernel-checked over all `128` colourings); `fano_hasChromaticNumber_three`;
`erdos_832_false_three_three : ∃ H, H.IsUniform 3 ∧ H.HasChromaticNumber 3 ∧ H.edges.card < C((3−1)(3−1)+1, 3)`;
graded root `erdos_832_fano_closed : Fintype.card fano.V = 7 ∧ fano.edges.card = 7 ∧ fano.IsUniform 3 ∧
fano.HasChromaticNumber 3 ∧ fano.edges.card < ((3 - 1) * (3 - 1) + 1).choose 3` (`7 < 10`).

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option` (all finite checks are kernel
`decide`).  See `verification.txt`.  Before submission the package passed MerLean Heavy's
research-grade audit (target/goal contracts, kernel evidence, definition independence, two
independent audits).

**Files.** `Erdos832Fano/Main.lean`, `Erdos832Fano.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

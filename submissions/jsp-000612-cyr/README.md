# JSP-000612 / Erdős Problem #744 — scoped component: odd cycles show `f_3(n) = 1`

**Scope (honest).** Erdős, Hajnal and Szemerédi define `f_k(n)` as the minimal `m` such that
there is a graph `G` on `n` vertices with chromatic number `k`, every proper subgraph of which has
chromatic number `< k`, and which can be made bipartite by deleting `m` edges; they asked whether
`f_k(n) → ∞`.  That was **disproved** by Rödl–Tuza (`f_k(n) = C(k−1, 2)` for large `n`) and is
*not* formalized here.  This package proves the remark on the problem page
(erdosproblems.com/744): *"Odd cycles show that f_3(n) = 1"*, for every odd `n ≥ 3` (the only `n`
for which a `3`-critical graph on `n` vertices exists, the `3`-critical graphs being exactly the
odd cycles; for even `n` the defining set is empty).

**Definitions** (`Erdos744OddCycles/Main.lean`, namespace `Erdos744`; no formal-conjectures
rendering exists, so these are ours).  `IsCritical k G`: `G.chromaticNumber = k` and deleting any
edge or any vertex (`G.induce {v}ᶜ`) lowers the chromatic number below `k` — equivalent to "every
proper subgraph has chromatic number `< k`", since every proper subgraph lies in some `G − e` or
`G − v` and the chromatic number is monotone.  `DeletionSet k n` = the numbers `m` such that some
`k`-critical graph on `Fin n` becomes bipartite (`Colorable 2`) after deleting a set of `m` of its
edges; `f k n = sInf (DeletionSet k n)`.

**Statements.**  `cycleGraph_deleteEdges_colorable`, `cycleGraph_induce_colorable` (deleting an
edge or a vertex of `C_n` leaves a `2`-colourable graph), `cycleGraph_isCritical` (odd cycles are
`3`-critical), `zero_notMem_deletionSet`, `erdos_744_f_three (n) (h3 : 3 ≤ n) (hodd : Odd n) :
IsLeast (DeletionSet 3 n) 1 ∧ f 3 n = 1`, and the graded root
`erdos_744_f_three_closed : ¬ ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ ¬ (IsLeast (DeletionSet 3 n) 1 ∧ f 3 n = 1)`.

**Proof idea.**  `C_n` (odd) has chromatic number `3` (Mathlib); cutting it between two vertices
leaves a path, `2`-coloured by the parity of the position along the path — the same colouring
handles edge deletion and vertex deletion; deleting one edge makes it bipartite, deleting none
does not.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos744OddCycles/Main.lean`, `Erdos744OddCycles.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

# JSP-000640 / Erdős Problem #780 — scoped component: sharpness of the Alon–Frankl–Lovász bound

**Scope (honest).** Erdős asked to prove that if `n ≥ kr + (t − 1)(k − 1)` and the edges of the
complete `r`-uniform hypergraph on `n` vertices are `t`-coloured, some colour class contains `k`
pairwise disjoint edges.  That theorem (Lovász for `k = 2`, Alon–Frankl–Lovász in general; the
chromatic number of Kneser hypergraphs) is **proved** and is *not* formalized here.  This package
formalizes the remark on the problem page (erdosproblems.com/780) that the bound is best
possible: *"if n = kr−1+(t−1)(k−1) then decomposing [n] as one set X_1 of size kr−1 and t−1 sets
X_2,…,X_t of size k−1, a colouring without k pairwise disjoint edges is given colouring all
subsets of X_1 in colour 1 and assigning an edge with colour 2 ≤ i ≤ t if i is minimal such that
X_i intersects the edge."*  (The page writes `X_0` once for `X_1`.)

**Definitions** (`Erdos780Sharpness/Main.lean`, namespace `Erdos780`; no formal-conjectures
rendering exists, so the definitions are ours).  Vertices are `Fin n` with
`n = k * r - 1 + (t - 1) * (k - 1)`; `blockOf k r v` is `0` on `X_1 = [0, kr − 1)` and
`1 + (v − (kr − 1)) / (k − 1)` beyond (the block index `i − 1` of `X_i`); `colourNat k r e` is the
least nonzero block index met by `e` (an `sInf`, equal to `0` exactly when `e ⊆ X_1`);
`colour k r t ht e : Fin t` clips it into `Fin t` (it is always in range).

**Statements.**  `no_k_disjoint`: for `k, r, t ≥ 1`, any family `F` of `r`-edges of one colour
that are pairwise disjoint has `F.card < k`; `erdos_780_sharp (k r t) (hk hr ht) : ∃ c, ∀ i F, …
→ F.card < k`; graded root `erdos_780_sharpness_closed : ¬ ∃ k r t : ℕ, 1 ≤ k ∧ 1 ≤ r ∧ 1 ≤ t ∧
∀ c : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) → Fin t, ∃ i F, (∀ e ∈ F, e.card = r ∧ c e = i)
∧ (∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Disjoint e e') ∧ k ≤ F.card`.

**Proof idea.**  `k` pairwise disjoint `r`-edges of colour `1` would need `kr` vertices of `X_1`,
which has `kr − 1`; pairwise disjoint edges of colour `i ≥ 2` each meet `X_i`, which has only
`k − 1` vertices.  (For `k = 1`, `n = r − 1` and there are no `r`-edges at all.)

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos780Sharpness/Main.lean`, `Erdos780Sharpness.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

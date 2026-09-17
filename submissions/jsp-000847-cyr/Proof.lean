import Proof.Defs
import Proof.Main

/-!
# JSP-000847 — Erdős problem #1017 (scoped component)

The page's sharpness remark for the Erdős–Goodman–Pósa bound: the balanced complete bipartite
graph on `n` vertices is triangle-free with `⌊n²/4⌋` edges, so it needs `⌊n²/4⌋` edge-disjoint
complete graphs and `⌊n²/4⌋ ≤ f(n, ⌊n²/4⌋)`.  `Proof.Defs` holds the frozen
definitions; `Proof.Main` the proofs.
-/

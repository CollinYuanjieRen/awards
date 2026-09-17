import Proof.RamseyDefs
import Proof.Ramsey
import Proof.Bound
import Proof.Defs
import Proof.Main

/-!
# JSP-000103 — Erdős problem #87 (scoped component)

The page's remark "Since `R(k) ≤ 4^k` this is trivial for `ε ≥ 3/4`": for every graph `G` with
chromatic number `k ≥ 2` and every `3/4 ≤ ε ≤ 1`, `R(G) > (1 − ε)^k R(k)`.
`RamseyDefs`, `Ramsey`, `Bound` and `Defs` are our own Ramsey toolbox (reused from our JSP-000669,
JSP-000099 and JSP-000175 packages); `Main` holds the proofs.
-/

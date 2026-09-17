import Proof.RamseyDefs
import Proof.Ramsey
import Proof.Bound
import Proof.Defs
import Proof.Main

/-!
# JSP-000175 — Erdős problem #181 (scoped component)

The page's trivial bound `R(Q_n) ≤ R(K_{2^n}) ≤ C^{2^n}` for the hypercube `Q_n`, with `C = 4`.
`RamseyDefs`, `Ramsey` and `Bound` are our own Ramsey toolbox (reused from our JSP-000669 and
JSP-000099 packages); `Defs` holds the frozen definitions (hypercube, graph Ramsey number);
`Main` holds the proofs.
-/

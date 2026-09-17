import Mathlib

/-!
# Erdős problem #85 — the minimum-degree threshold for a `C₄`: definitions

For `n ≥ 4` the problem page defines `f(n)` as the least `k` such that every graph on `n` vertices
with minimum degree at least `k` contains a `C₄`, and asks whether `f(n+1) ≥ f(n)` for all large `n`.
This module fixes `f`, in the shape used by the formal-conjectures statement of the problem
(a `sInf` over the admissible thresholds; the set is nonempty: for `n ≥ 1` the threshold `k = n`
works vacuously, since no graph on `n ≥ 1` vertices has minimum degree `n`, and for `n = 0` the
threshold `k = 1` does).  Containment `cycleGraph 4 ⊑ G` is Mathlib's
`SimpleGraph.IsContained` (an injective homomorphism, i.e. a not-necessarily-induced `4`-cycle).
-/

namespace Erdos85

open SimpleGraph

/-- `f n`: the least `k` such that every graph on `n` vertices with minimum degree `≥ k`
contains a `C₄`. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  sInf {k : ℕ | ∀ G : SimpleGraph (Fin n), k ≤ G.minDegree → cycleGraph 4 ⊑ G}

/-- The perfect matching `{0,1}, {2,3}` on four vertices: the witness that `f(4) > 1`. -/
def perfectMatching : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun a b => (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3))

instance : DecidableRel perfectMatching.Adj := fun a b => by
  unfold perfectMatching; infer_instance

end Erdos85

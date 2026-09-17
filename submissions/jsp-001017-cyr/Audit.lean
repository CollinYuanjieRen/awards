import Erdos1212Stewart

#print axioms stewart_joined
#print axioms erdos_1212_stewart
#print axioms erdos_1212_stewart_closed

/-- Erdős #1212, Stewart's step: `(p_k, p_{k+1})` is joined to `(p_{k+1}, p_{k+2})` when
`p_{k+2} < 2 p_k`. -/
example (k : ℕ) (h : Nat.nth Nat.Prime (k + 2) < 2 * Nat.nth Nat.Prime k) :
    VisiblyJoined (Nat.nth Nat.Prime k, Nat.nth Nat.Prime (k + 1))
      (Nat.nth Nat.Prime (k + 1), Nat.nth Nat.Prime (k + 2)) := erdos_1212_stewart k h

/-- The adjacency is the formal-conjectures one. -/
example (p q : ℕ × ℕ) : Adj p q ↔ ((p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
    (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))) := Iff.rfl

import Erdos203MOne

#print axioms erdos_203_variant_m_one
#print axioms erdos_203_variant_m_one_closed

/-- Erdős #203: the `q₁ ⋯ q_r m + 1` variant has the trivial answer `m = 1`. -/
example (l : List ℕ) (hl : l ≠ []) (hq : ∀ q ∈ l, q.Prime ∧ q % 4 = 1) :
    ¬ (l.prod * 1 + 1).Prime :=
  erdos_203_variant_m_one l hl hq

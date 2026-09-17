import Erdos780Sharpness

#print axioms erdos_780_sharpness_closed
#print axioms Erdos780.erdos_780_sharp

/-- Erdős #780: the Alon–Frankl–Lovász bound is sharp. -/
example (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    ∃ c : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) → Fin t,
      ∀ (i : Fin t) (F : Finset (Finset (Fin (k * r - 1 + (t - 1) * (k - 1))))),
        (∀ e ∈ F, e.card = r ∧ c e = i) → (∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Disjoint e e') →
          F.card < k :=
  Erdos780.erdos_780_sharp k r t hk hr ht

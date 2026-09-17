import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions; target with `sorry`, not imported by
the build) for JSP-000442 / Erdős #551, the lower half of R(C_k, K_n) = (k−1)(n−1)+1. -/

namespace Challenge551

open SimpleGraph

/-- every red/blue colouring of `K_N` (red = `R`, blue = `Rᶜ`) contains a red `G` or a blue `H` -/
def GraphRamseyProp {α β : Type*} (N : ℕ) (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ H ⊑ Rᶜ

/-- the asymmetric graph Ramsey number `R(G, H)` -/
noncomputable def graphRamsey {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G H}

/-- the lower half of the Erdős–Faudree–Rousseau–Schelp identity: `(k−1)(n−1)+1 ≤ R(C_k, K_n)`
(in the `k·n+1 ≤ R(C_{k+1}, K_{n+1})` shifted form). -/
theorem lower_bound (k n : ℕ) :
    k * n + 1 ≤ graphRamsey (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1))) := by
  sorry

/-- the page's form for `k, n ≥ 3`. -/
theorem lower_bound' (k n : ℕ) (hk : 3 ≤ k) (hn : 3 ≤ n) :
    (k - 1) * (n - 1) + 1 ≤ graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin n)) := by
  sorry

end Challenge551

/-
Comparator-style challenge module for JSP-000099 / Erdős Problem #82 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
the `Proof` library (the definitions below are the ones of `Proof/RamseyDefs.lean` and
`Proof/Regular.lean`, repeated verbatim). Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos82Challenge

/-- The colouring `G` (red = edges) is `(m, n)`-good: no red `K_m` and no blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- Every colouring of `K_N` has a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The Ramsey number `r(m, n)`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- `S` induces a regular subgraph of `G`. -/
noncomputable def IsRegularOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  open Classical in ∃ d : ℕ, ∀ v ∈ S, (S.filter (fun w => G.Adj v w)).card = d

/-- `G` has a regular induced subgraph on at least `n` vertices. -/
def HasRegularInduced {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ S : Finset V, n ≤ S.card ∧ IsRegularOn G S

/-- Every graph on `m` vertices has a regular induced subgraph on at least `n` vertices. -/
def RegProp (m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin m), HasRegularInduced G n

/-- `G(n)`: the least `m` with `RegProp m n`. -/
noncomputable def regThreshold (n : ℕ) : ℕ := sInf {m : ℕ | RegProp m n}

/-- `F(m)`: the largest `n` with `RegProp m n`. -/
noncomputable def regGuarantee (m : ℕ) : ℕ := sSup {n : ℕ | RegProp m n}

theorem log_le_regGuarantee (m : ℕ) : Nat.log 4 m ≤ regGuarantee m := by
  sorry

theorem regThreshold_le_four_pow (n : ℕ) : regThreshold n ≤ 4 ^ n := by
  sorry

theorem regThreshold_le_ramsey (n : ℕ) : regThreshold n ≤ ramsey n n := by
  sorry

theorem ramsey_le_choose (m n : ℕ) : ramsey m n ≤ (m + n).choose m - 1 := by
  sorry

theorem regThreshold_three : regThreshold 3 = 5 := by
  sorry

theorem regGuarantee_five : regGuarantee 5 = 3 := by
  sorry

end Erdos82Challenge

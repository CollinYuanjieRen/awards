import Proof.LowerBound
import Proof.Examples

/-!
# Erdős Problem 902 (Schütte's tournament problem): `f 1 = 3`, `f 2 = 7`, `2^(n+1) - 1 ≤ f n`

The scoped component of Erdős Problem 902 formalized here: the exact values `f(1) = 3` and
`f(2) = 7`, and Erdős's 1963 lower bound `2^(n+1) - 1 ≤ f(n)` for every `n` for which some
tournament has the `n`-domination property.  The order of magnitude of `f(n)` (between `n 2^n`
and `n² 2^n`) is open and is not addressed.
-/

namespace Erdos902

/-- Erdős's lower bound in its universal form: every tournament on `N` vertices with the
`n`-domination property has `N ≥ 2^(n+1) - 1`. -/
theorem two_pow_sub_one_le_of_hasProperty (N n : ℕ) (r : Fin N → Fin N → Prop)
    (hr : IsTournament r) (hn : HasProperty r n) : 2 ^ (n + 1) - 1 ≤ N := by
  classical
  have h : DecidableRel r := Classical.decRel r
  simpa using two_pow_sub_one_le_card r hr hn

/-- Erdős's lower bound for Schütte's function, whenever the defining set is nonempty. -/
theorem two_pow_sub_one_le_schutte (n : ℕ)
    (h : ∃ N : ℕ, ∃ r : Fin N → Fin N → Prop, IsTournament r ∧ HasProperty r n) :
    2 ^ (n + 1) - 1 ≤ schutte n := by
  obtain ⟨N, r, hr, hn⟩ := h
  obtain ⟨r', hr', hn'⟩ := Nat.sInf_mem (s := {N : ℕ | ∃ r : Fin N → Fin N → Prop,
    IsTournament r ∧ HasProperty r n}) ⟨N, r, hr, hn⟩
  exact two_pow_sub_one_le_of_hasProperty _ n r' hr' hn'

theorem schutte_one : schutte 1 = 3 := by
  refine le_antisymm (Nat.sInf_le ⟨cyc3, isTournament_cyc3, hasProperty_cyc3⟩) ?_
  have h := two_pow_sub_one_le_schutte 1 ⟨3, cyc3, isTournament_cyc3, hasProperty_cyc3⟩
  norm_num at h
  exact h

theorem schutte_two : schutte 2 = 7 := by
  refine le_antisymm (Nat.sInf_le ⟨paley7, isTournament_paley7, hasProperty_paley7⟩) ?_
  have h := two_pow_sub_one_le_schutte 2 ⟨7, paley7, isTournament_paley7, hasProperty_paley7⟩
  norm_num at h
  exact h

end Erdos902

import Proof.Upper
import Proof.Lower

/-!
# Erdős Problem 436: `Λ(2,2) = 9` (Lehmer–Lehmer 1962)

The scoped component of Erdős Problem 436 formalized here: `Λ(2,2) = limsup_{p → ∞} r(2,2,p) = 9`,
from the bound `r(2,2,p) ≤ 9` for all primes `p ≥ 11` and the existence of arbitrarily large primes
with `r(2,2,p) = 9`.  The finiteness and growth questions for `Λ(k,2)`, `Λ(k,3)` with larger `k`
are not addressed.
-/

open Filter

namespace Erdos436

/-- `r(2,2,p) ≤ 9` for all sufficiently large primes. -/
theorem eventually_runStart_le_nine :
    ∀ᶠ p in atTop ⊓ 𝓟 {p : ℕ | p.Prime}, runStart p ≤ 9 := by
  rw [eventually_inf_principal]
  filter_upwards [eventually_ge_atTop 11] with p hp hprime
  have : Fact p.Prime := ⟨hprime⟩
  exact runStart_le_nine p hp

/-- `r(2,2,p) = 9` for infinitely many primes. -/
theorem frequently_runStart_eq_nine :
    ∃ᶠ p in atTop ⊓ 𝓟 {p : ℕ | p.Prime}, runStart p = 9 := by
  rw [frequently_inf_principal, frequently_atTop]
  intro N
  obtain ⟨p, hpN, hp, h9⟩ := exists_prime_gt_runStart_eq_nine N
  exact ⟨p, hpN.le, hp, h9⟩

/-- **Lehmer–Lehmer (1962).** `Λ(2,2) = 9`. -/
theorem lambda22_eq_nine : Lambda22 = 9 := by
  have hbdd : (atTop ⊓ 𝓟 {p : ℕ | p.Prime}).IsBoundedUnder (· ≤ ·) runStart :=
    ⟨9, by simpa only [eventually_map] using eventually_runStart_le_nine⟩
  have hfreq : ∃ᶠ p in atTop ⊓ 𝓟 {p : ℕ | p.Prime}, 9 ≤ runStart p :=
    frequently_runStart_eq_nine.mono fun _ h ↦ h.ge
  exact le_antisymm (limsup_le_of_le (h := eventually_runStart_le_nine))
    (le_limsup_of_frequently_le hfreq hbdd)

end Erdos436

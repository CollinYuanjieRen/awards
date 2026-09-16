import Proof.Defs

/-!
# Erdős Problem 436: `r(2,2,p) ≤ 9` for every prime `p ≥ 11`

`1`, `4`, `9` are residues.  If `2` is a residue, `(1, 2)` is a run; otherwise if `5` is a residue,
`(4, 5)` is; otherwise `2` and `5` are both non-residues, so `10 = 2 · 5` is a residue and `(9, 10)`
is a run.
-/

namespace Erdos436

/-- Every prime `p ≥ 11` has a run start in `{1, 4, 9}`. -/
theorem exists_runStart_le_nine (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) :
    ∃ r, IsRunStart p r ∧ r ≤ 9 := by
  have hnd : ∀ k : ℕ, 0 < k → k < p → ¬ p ∣ k := fun k hk hkp hdvd ↦
    absurd (Nat.le_of_dvd hk hdvd) (by omega)
  have h1 : IsQR p 1 := by
    simpa using isQR_sq (p := p) (hnd 1 (by norm_num) (by omega))
  have h4 : IsQR p 4 := by
    simpa using isQR_sq (p := p) (hnd 2 (by norm_num) (by omega))
  have h9 : IsQR p 9 := by
    simpa using isQR_sq (p := p) (hnd 3 (by norm_num) (by omega))
  by_cases h2 : IsSquare (2 : ZMod p)
  · have hq2 : IsQR p 2 :=
      ⟨cast_ne_zero_of_lt (by norm_num) (by omega), by push_cast; exact h2⟩
    exact ⟨1, ⟨by norm_num, h1, hq2⟩, by norm_num⟩
  · by_cases h5 : IsSquare (5 : ZMod p)
    · have hq5 : IsQR p 5 :=
        ⟨cast_ne_zero_of_lt (by norm_num) (by omega), by push_cast; exact h5⟩
      exact ⟨4, ⟨by norm_num, h4, hq5⟩, by norm_num⟩
    · have hc2 : ((2 : ℕ) : ZMod p) ≠ 0 := cast_ne_zero_of_lt (by norm_num) (by omega)
      have hc5 : ((5 : ℕ) : ZMod p) ≠ 0 := cast_ne_zero_of_lt (by norm_num) (by omega)
      have h2' : ¬ IsSquare ((2 : ℕ) : ZMod p) := by push_cast; exact h2
      have h5' : ¬ IsSquare ((5 : ℕ) : ZMod p) := by push_cast; exact h5
      have hq10 : IsQR p 10 := by
        simpa using isQR_mul_of_not (p := p) (a := 2) (b := 5) hc2 hc5 h2' h5'
      exact ⟨9, ⟨by norm_num, h9, hq10⟩, by norm_num⟩

/-- **Lehmer–Lehmer, upper half.** `r(2,2,p) ≤ 9` for every prime `p ≥ 11`. -/
theorem runStart_le_nine (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : runStart p ≤ 9 := by
  obtain ⟨r, hr, hr9⟩ := exists_runStart_le_nine p hp
  exact (Nat.sInf_le hr).trans hr9

end Erdos436

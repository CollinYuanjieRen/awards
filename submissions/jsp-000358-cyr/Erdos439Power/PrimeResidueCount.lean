import Mathlib

open scoped BigOperators

namespace Erdos439Power

noncomputable section

/-- The proportion of residues modulo `q` whose canonical representative is
divisible by a divisor `p` of `q` is exactly `1 / p`. -/
theorem expect_indicator_dvd_val (q p : ℕ) [NeZero q]
    (hq : 0 < q) (hp : 0 < p) (hpq : p ∣ q) :
    (𝔼 h : ZMod q, if p ∣ h.val then (1 : ℝ) else 0) = 1 / (p : ℝ) := by
  let base : Fin q ≃ ZMod q :=
    { toFun := fun i => (i : ZMod q)
      invFun := fun h => (⟨h.val, h.val_lt⟩ : Fin q)
      left_inv := fun i => Fin.ext (by simp [ZMod.val_natCast_of_lt i.isLt])
      right_inv := fun h => ZMod.natCast_zmod_val h }
  let e : Fin q ≃ ZMod q := base.trans (Equiv.addRight 1)
  have hdvdmod (n : ℕ) : p ∣ n % q ↔ p ∣ n := by
    have hqd : p ∣ q * (n / q) := hpq.mul_right _
    constructor
    · intro hr
      simpa [Nat.mod_add_div] using hr.add hqd
    · intro hn
      apply (Nat.dvd_add_iff_right hqd).mpr
      simpa [add_comm, Nat.mod_add_div] using hn
  have he (i : Fin q) :
      (p ∣ (e i).val) ↔ p ∣ (i : ℕ) + 1 := by
    dsimp [e, base]
    rw [ZMod.val_add, ZMod.val_natCast_of_lt i.isLt]
    rw [ZMod.val_one_eq_one_mod]
    have hv : ((i : ℕ) + 1 % q) % q = ((i : ℕ) + 1) % q := by
      conv_lhs =>
        lhs
        rw [← Nat.mod_eq_of_lt i.isLt]
      exact (Nat.add_mod _ _ _).symm
    rw [hv]
    exact hdvdmod ((i : ℕ) + 1)
  rw [← Fintype.expect_equiv e
    (fun i : Fin q => if p ∣ (i : ℕ) + 1 then (1 : ℝ) else 0)
    (fun h : ZMod q => if p ∣ h.val then (1 : ℝ) else 0)
    (fun i => by simp only [he])]
  rw [Fintype.expect_eq_sum_div_card]
  have hsum :
      (∑ i : Fin q, if p ∣ (i : ℕ) + 1 then (1 : ℝ) else 0) = (q / p : ℕ) := by
    have hfinrange :
        (∑ i : Fin q, if p ∣ (i : ℕ) + 1 then (1 : ℝ) else 0) =
          ∑ i ∈ Finset.range q, if p ∣ i + 1 then (1 : ℝ) else 0 := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => if p ∣ i + 1 then (1 : ℝ) else 0) q
    rw [hfinrange]
    calc
      (∑ i ∈ Finset.range q, if p ∣ i + 1 then (1 : ℝ) else 0) =
          ((Finset.filter (fun i => p ∣ i + 1) (Finset.range q)).card : ℝ) := by simp
      _ = (q / p : ℕ) := by norm_cast; exact Nat.card_multiples q p
  rw [hsum]
  simp only [Fintype.card_fin]
  have hqeq : q / p * p = q := Nat.div_mul_cancel hpq
  have hqeqr : ((q / p : ℕ) : ℝ) * (p : ℝ) = (q : ℝ) := by exact_mod_cast hqeq
  have hquot : ((q / p : ℕ) : ℝ) = (q : ℝ) / p := by
    exact (eq_div_iff (by positivity)).2 hqeqr
  rw [hquot]
  field_simp

end

end Erdos439Power

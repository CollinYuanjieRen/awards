import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

namespace Erdos441

/-- The actual union of roots of the integer linear forms modulo a prime. -/
noncomputable def linearBadResidues (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (A B : ι → ℤ) : Finset (ZMod p) := by
  classical
  exact Finset.univ.biUnion fun i =>
    Finset.univ.filter fun z => (A i : ZMod p) * z + B i = 0

theorem linear_bad_residue_spec (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (A B : ι → ℤ)
    (hprim : ∀ i, IsCoprime (A i) (B i)) :
    (linearBadResidues p A B).card ≤ Fintype.card ι ∧
      ∀ k : ℤ, (k : ZMod p) ∈ linearBadResidues p A B ↔
        (p : ℤ) ∣ ∏ i, (A i * k + B i) := by
  classical
  have hsingle (i : ι) :
      (Finset.univ.filter fun z : ZMod p => (A i : ZMod p) * z + B i = 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hcop := (hprim i).map (Int.castRingHom (ZMod p))
    obtain ⟨u, v, huv⟩ := hcop
    by_cases ha : (A i : ZMod p) = 0
    · have hb : (B i : ZMod p) = 0 := by simpa [ha] using hz'
      change u * (A i : ZMod p) + v * (B i : ZMod p) = 1 at huv
      simp only [ha, hb, mul_zero, add_zero] at huv
      exact False.elim (zero_ne_one huv)
    · apply mul_left_cancel₀ ha
      exact add_right_cancel (hz'.trans hw'.symm)
  constructor
  · calc
      (linearBadResidues p A B).card ≤
          ∑ i : ι, (Finset.univ.filter fun z : ZMod p =>
            (A i : ZMod p) * z + B i = 0).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ => hsingle i
      _ = Fintype.card ι := by simp
  · intro k
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [linearBadResidues, Finset.prod_eq_zero_iff]

theorem linear_bad_residues_empty (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (A B : ι → ℤ)
    (hprim : ∀ i, IsCoprime (A i) (B i))
    (hno : ∀ k : ℤ, ¬ (p : ℤ) ∣ ∏ i, (A i * k + B i)) :
    linearBadResidues p A B = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzcast : (((z.val : ℕ) : ℤ) : ZMod p) = z := by simp
  rw [← hzcast] at hz
  exact hno z.val ((linear_bad_residue_spec p A B hprim).2 z.val |>.mp hz)

end Erdos441

#print axioms Erdos441.linear_bad_residue_spec
#print axioms Erdos441.linear_bad_residues_empty

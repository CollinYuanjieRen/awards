import MerLeanExperiment.CRTResidues
import MerLeanExperiment.ResidueSetCount

namespace Erdos441

/-- Uniform intersection-count error, obtained from the actual CRT equivalence. -/
theorem joint_residue_discrepancy {ι : Type*} [Fintype ι]
    (a b : ℤ) (hab : a ≤ b) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) :
    |(({x ∈ Finset.Ioc a b | ∀ i, ((x : ℤ) : ZMod (m i)) ∈ R i}).card : ℚ) -
      ((b - a : ℤ) : ℚ) * ∏ i, ((R i).card : ℚ) / m i| ≤
      ∏ i, ((R i).card : ℚ) := by
  classical
  have hpos : 0 < ∏ i, m i := Finset.prod_pos fun i _ => hm i
  have hspec := joint_residue_spec m hc R
  have hcount := residue_set_discrepancy a b (∏ i, m i) hpos hab
    (jointResidues m hc R)
  simp only [hspec.2, hspec.1, Nat.cast_prod] at hcount
  rw [Finset.prod_div_distrib]
  convert hcount using 2
  ring

end Erdos441

#print axioms Erdos441.joint_residue_discrepancy

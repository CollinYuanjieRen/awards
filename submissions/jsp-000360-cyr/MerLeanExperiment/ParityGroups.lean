import MerLeanExperiment.ParityGroupDefinitions
import Mathlib.Logic.Equiv.Sum

namespace Erdos441

theorem even_sub_parity_rep (n r : ℤ) :
    Even (n - r) ↔ Even (n - parityRep (decide (Even r))) := by
  by_cases hr : Even r <;> simp [Int.even_sub, parityRep, hr]

theorem parity_region_rep (A : Finset ℕ) (a b R : ℝ) (r : ℤ) :
    parityRegion A a b R r =
      parityRegion A a b R (parityRep (decide (Even r))) := by
  classical
  ext n
  simp only [parityRegion, Finset.mem_filter, even_sub_parity_rep (n : ℤ) r]

theorem parity_regions_opposite (A : Finset ℕ) (a b c d R : ℝ)
    (v w : Bool) (hvw : v ≠ w) :
    Disjoint (parityRegion A a b R (parityRep v))
      (parityRegion A c d R (parityRep w)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have h := (Finset.mem_filter.mp hn).2.2.2
  have h' := (Finset.mem_filter.mp hn').2.2.2
  cases v <;> cases w <;> simp_all [parityRep]
  all_goals exact (Nat.not_even_iff_odd.mpr ‹Odd n›) ‹Even n›

theorem density_parity_partition (A : Finset ℕ) (a b R : ℝ) (r : ℤ) :
    parityDensity A a b R r + parityDensity A a b R (r + 1) =
      intervalDensity A a b R := by
  classical
  let F := A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R
  have hfilter (s : ℤ) :
      (A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R ∧
        Even ((n : ℤ) - s)) = F.filter (fun n : ℕ => Even ((n : ℤ) - s)) := by
    ext n
    simp [F, and_assoc]
  have hnext (n : ℕ) : Even ((n : ℤ) - (r + 1)) ↔ ¬Even ((n : ℤ) - r) := by
    rw [sub_add_eq_sub_sub, Int.even_sub_one]
  unfold parityDensity intervalDensity
  rw [hfilter r, hfilter (r + 1), ← add_div]
  congr 1
  simp only [hnext]
  exact_mod_cast (Finset.card_filter_add_card_filter_not (s := F)
    (fun n : ℕ => Even ((n : ℤ) - r)))

theorem sum_owner_parity_fibers {K l : ℕ} (o : Fin K → Fin l)
    (r : Fin K → ℤ) (f : Fin K → ℝ) :
    (∑ g : Fin l × Bool, ∑ i : {i : Fin K // ownerParity o r i = g}, f i.val) =
      ∑ i : Fin K, f i := by
  classical
  have hh := Fintype.sum_sigma
    (fun x : Σ g, {i : Fin K // ownerParity o r i = g} => f x.2.val)
  rw [← hh]
  exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv (ownerParity o r)) _ _ (fun _ => rfl)

end Erdos441

#print axioms Erdos441.even_sub_parity_rep
#print axioms Erdos441.parity_region_rep
#print axioms Erdos441.parity_regions_opposite
#print axioms Erdos441.density_parity_partition
#print axioms Erdos441.sum_owner_parity_fibers

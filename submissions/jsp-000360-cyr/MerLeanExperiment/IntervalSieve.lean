import MerLeanExperiment.JointResidueCount
import MerLeanExperiment.SieveError

namespace Erdos441

/-- Elementary sieve on an actual integer interval, with all CRT estimates discharged. -/
theorem interval_sieve_discrepancy {ι : Type*} [Fintype ι]
    (a b : ℤ) (hab : a ≤ b) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) :
    |(({x ∈ Finset.Ioc a b | ∀ i, ((x : ℤ) : ZMod (m i)) ∉ R i}).card : ℚ) -
      ((b - a : ℤ) : ℚ) * ∏ i, (1 - ((R i).card : ℚ) / m i)| ≤
      ∏ i, (1 + ((R i).card : ℚ)) := by
  classical
  let U := Finset.Ioc a b
  let bad : ι → Finset U := fun i =>
    Finset.univ.filter fun x => ((x.val : ℤ) : ZMod (m i)) ∈ R i
  have hmem (T : Finset ι) (f : ι → Finset U) (x : U) :
      x ∈ T.inf f ↔ ∀ i ∈ T, x ∈ f i := by
    induction T using Finset.induction_on with
    | empty => simp [Finset.inf_empty]
    | @insert i T hi ih => simp [Finset.inf_insert, ih]
  have hcard (p : ℤ → Prop) [DecidablePred p] :
      (Finset.univ.filter fun x : U => p x.val).card = (U.filter p).card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
        by simpa using (Finset.mem_filter.mp hx).2, rfl⟩
  have herr (T : Finset ι) :
      |((T.inf bad).card : ℚ) - ((b - a : ℤ) : ℚ) *
        ∏ i ∈ T, ((R i).card : ℚ) / m i| ≤ ∏ i ∈ T, ((R i).card : ℚ) := by
    have hcT : Pairwise (fun i j : T => (m i.val).Coprime (m j.val)) := by
      intro i j hij
      exact hc (fun h => hij (Subtype.ext h))
    have h := joint_residue_discrepancy a b hab (fun i : T => m i.val)
      (fun i => hm i.val) hcT (fun i => R i.val)
    have heq : T.inf bad = Finset.univ.filter
        (fun x : U => ∀ i ∈ T, ((x.val : ℤ) : ZMod (m i)) ∈ R i) := by
      ext x
      simpa [bad] using hmem T bad x
    rw [heq, hcard (fun x : ℤ =>
      ∀ i ∈ T, ((x : ℤ) : ZMod (m i)) ∈ R i)]
    have hforall :
        {x ∈ Finset.Ioc a b |
            ∀ i : T, ((x : ℤ) : ZMod (m i.val)) ∈ R i.val} =
          U.filter (fun x : ℤ =>
            ∀ i ∈ T, ((x : ℤ) : ZMod (m i)) ∈ R i) := by
      ext x
      simp only [U, Finset.mem_filter, Subtype.forall]
    have hrho :
        (∏ i : T, ((R i.val).card : ℚ) / m i.val) =
          ∏ i ∈ T, ((R i).card : ℚ) / m i :=
      Finset.prod_coe_sort T (fun i : ι => ((R i).card : ℚ) / m i)
    have herrprod :
        (∏ i : T, ((R i.val).card : ℚ)) =
          ∏ i ∈ T, ((R i).card : ℚ) :=
      Finset.prod_coe_sort T (fun i : ι => ((R i).card : ℚ))
    rw [← hforall, ← hrho, ← herrprod]
    exact h
  have h := sieve_discrepancy_bound bad ((b - a : ℤ) : ℚ)
    (fun i => ((R i).card : ℚ) / m i) (fun i => ((R i).card : ℚ)) herr
  have heq : (Finset.univ.inf fun i => (bad i)ᶜ) = Finset.univ.filter
      (fun x : U => ∀ i, ((x.val : ℤ) : ZMod (m i)) ∉ R i) := by
    ext x
    simpa [bad] using hmem (Finset.univ : Finset ι) (fun i => (bad i)ᶜ) x
  rw [heq, hcard (fun x : ℤ =>
    ∀ i, ((x : ℤ) : ZMod (m i)) ∉ R i)] at h
  exact h

end Erdos441

#print axioms Erdos441.interval_sieve_discrepancy

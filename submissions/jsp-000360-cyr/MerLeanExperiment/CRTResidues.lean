import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace Erdos441

/-- Pull a finite product of residue sets back along the actual Chinese remainder equivalence. -/
noncomputable def jointResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) : Finset (ZMod (∏ i, m i)) := by
  classical
  exact (Fintype.piFinset R).map (ZMod.prodEquivPi m hc).symm.toEquiv.toEmbedding

/-- The CRT residue set has its expected cardinality and exactly its intended membership test. -/
theorem joint_residue_spec {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (R : ∀ i, Finset (ZMod (m i))) :
    (jointResidues m hc R).card = ∏ i, (R i).card ∧
      ∀ x : ℤ, (x : ZMod (∏ i, m i)) ∈ jointResidues m hc R ↔
        ∀ i, (x : ZMod (m i)) ∈ R i := by
  classical
  constructor
  · simp [jointResidues]
  · intro x
    have hcoords : ZMod.prodEquivPi m hc (x : ZMod (∏ i, m i)) =
        fun i => (x : ZMod (m i)) := by
      ext i
      simp
    constructor
    · rintro hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_map.mp hx
      have hyx : y = fun i => (x : ZMod (m i)) := by
        rw [← hcoords, ← heq]
        exact ((ZMod.prodEquivPi m hc).apply_symm_apply y).symm
      simpa only [hyx] using Fintype.mem_piFinset.mp hy
    · intro hx
      apply Finset.mem_map.mpr
      refine ⟨ZMod.prodEquivPi m hc (x : ZMod (∏ i, m i)), ?_, ?_⟩
      · rw [hcoords]
        exact Fintype.mem_piFinset.mpr hx
      · exact (ZMod.prodEquivPi m hc).symm_apply_apply _

end Erdos441

#print axioms Erdos441.joint_residue_spec

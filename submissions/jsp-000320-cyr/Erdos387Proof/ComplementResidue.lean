import ErdosProblems.Erdos387.TupleCoordinateCRT

/-! Independence of the complementary CRT data from the removed coordinate. -/

namespace Erdos387Proof

open Erdos387
open scoped BigOperators

theorem otherValue_eq_of_factors_eq_off_index
    {k X Y : ℕ} (C : TupleCertificate k X) (D : TupleCertificate k Y) (i : Fin k)
    (hfactor : ∀ j, j ≠ i → C.factor j = D.factor j) :
    C.otherValue i = D.otherValue i := by
  apply Finset.prod_congr rfl
  intro j hj
  exact hfactor j (Finset.mem_erase.mp hj).1

theorem otherResidue_eq_of_factors_eq_off_index
    {k X Y : ℕ} (C : TupleCertificate k X) (D : TupleCertificate k Y) (i : Fin k)
    (hfactor : ∀ j, j ≠ i → C.factor j = D.factor j) :
    C.otherResidue i = D.otherResidue i := by
  classical
  let s : Finset (Fin k) := Finset.univ.erase i
  have hpair : s.toList.Pairwise (fun a b => Nat.Coprime (C.factor a) (C.factor b)) := by
    apply s.nodup_toList.pairwise_of_forall_ne
    intro a _ b _ hab
    exact C.pairwise a b hab
  have hmod : Nat.ModEq (C.otherValue i) (C.otherResidue i) (D.otherResidue i) := by
    change Nat.ModEq (∏ j ∈ s, C.factor j) (C.otherResidue i) (D.otherResidue i)
    have h : Nat.ModEq (s.toList.map C.factor).prod
        (C.otherResidue i) (D.otherResidue i) := (Nat.modEq_list_map_prod_iff hpair).mpr (by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp (Finset.mem_toList.mp hj)).1
      have hD := D.otherResidue_mod_factor hji
      rw [← hfactor j hji] at hD
      exact (C.otherResidue_mod_factor hji).trans hD.symm)
    simpa using h
  exact hmod.eq_of_lt_of_lt (C.otherResidue_lt_otherValue i) (by
    rw [otherValue_eq_of_factors_eq_off_index C D i hfactor]
    exact D.otherResidue_lt_otherValue i)

end Erdos387Proof

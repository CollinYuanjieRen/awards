import MerLeanExperiment.WeightedTransfer
import Mathlib.Data.Fintype.Sort

namespace Erdos441

theorem sum_prefix_order_iso {I : Type*} [Fintype I] [LinearOrder I] {n : ℕ}
    (e : Fin n ≃o I) (f : I → ℝ) (t : Fin n) :
    (∑ i ∈ Finset.Iic t, f (e i)) = ∑ i : I, if i ≤ e t then f i else 0 := by
  classical
  calc
    _ = ∑ i : Fin n, if i ≤ t then f (e i) else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp
    _ = _ := Fintype.sum_equiv e.toEquiv _ _ (fun i => by simp)

theorem weighted_finite_order_transfer {I J : Type*} [Fintype I] [LinearOrder I]
    [Fintype J] (alpha beta : I → ℝ) (k : J → I → ℕ) (delta : J → ℝ) (B : ℝ)
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i) (hdelta : ∀ j, 0 ≤ delta j)
    (hprefix : ∀ t : I, (∑ i : I, if i ≤ t then beta i else 0) ≤
      ∑ i : I, if i ≤ t then ∑ j : J, delta j * k j i else 0)
    (hmoves : ∀ j (phi : I → I), (∀ i, i ≤ phi i) →
      (∑ i : I, (k j i : ℝ) * alpha (phi i)) ≤ B) :
    (∑ i : I, beta i * alpha i) ≤ B * ∑ j : J, delta j := by
  classical
  let e : Fin (Fintype.card I) ≃o I := monoEquivOfFin I rfl
  let d : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hsumI (f : I → ℝ) : (∑ i, f (e i)) = ∑ i : I, f i :=
    Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
  have hsumJ (f : J → ℝ) : (∑ j, f (d j)) = ∑ j : J, f j :=
    Fintype.sum_equiv d _ _ (fun _ => rfl)
  have hpre (t : Fin (Fintype.card I)) :
      (∑ i ∈ Finset.Iic t, beta (e i)) ≤
        ∑ i ∈ Finset.Iic t, ∑ j : Fin (Fintype.card J), delta (d j) * k (d j) (e i) := by
    have heq : (∑ i ∈ Finset.Iic t,
        ∑ j : Fin (Fintype.card J), delta (d j) * k (d j) (e i)) =
        ∑ i ∈ Finset.Iic t, ∑ j : J, delta j * k j (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsumJ (fun j => delta j * k j (e i))
    rw [heq, sum_prefix_order_iso e beta t,
      sum_prefix_order_iso e (fun i => ∑ j : J, delta j * k j i) t]
    exact hprefix (e t)
  have hmove (j : Fin (Fintype.card J))
      (phi : Fin (Fintype.card I) → Fin (Fintype.card I)) (hphi : ∀ i, i ≤ phi i) :
      (∑ i, (k (d j) (e i) : ℝ) * alpha (e (phi i))) ≤ B := by
    let psi : I → I := fun i => e (phi (e.symm i))
    have hpsi (i : I) : i ≤ psi i := by
      have hh := e.monotone (hphi (e.symm i))
      simpa [psi] using hh
    have hh := hmoves (d j) psi hpsi
    have heq : (∑ i, (k (d j) (e i) : ℝ) * alpha (e (phi i))) =
        ∑ i : I, (k (d j) i : ℝ) * alpha (psi i) := by
      exact Fintype.sum_equiv e.toEquiv _ _ (fun i => by simp [psi])
    rw [heq]
    exact hh
  have hh := weighted_prefix_transfer_of_forward_moves
    (fun i => alpha (e i)) (fun i => beta (e i)) (fun j i => k (d j) (e i))
    (fun j => delta (d j)) B (fun i => halpha (e i)) (fun i => hbeta (e i))
    (fun j => hdelta (d j)) hpre hmove
  rw [hsumI (fun i => beta i * alpha i), hsumJ delta] at hh
  exact hh

end Erdos441

#print axioms Erdos441.sum_prefix_order_iso
#print axioms Erdos441.weighted_finite_order_transfer

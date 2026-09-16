import MerLeanExperiment.FiniteParityDensity
import MerLeanExperiment.PackingParameters
import MerLeanExperiment.UniformCellUnion

namespace Erdos441

theorem eventually_parity_packing {K l : ℕ} (a b : Fin l → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (o : Fin K → Fin l) (r : Fin K → ℤ) (hr : Function.Injective r)
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤
      (shiftParityWeight (r i) (r j) : ℝ) * a (o i) * a (o j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i, parityDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r i)) ≤
        1 / 2 + ε := by
  classical
  obtain ⟨c0, _, hc0, _, hca, _⟩ := exists_finite_positive_bounds a ha
  obtain ⟨_, B, _, hB, _, hBb⟩ := exists_finite_positive_bounds b (fun j => (ha j).trans (hab j))
  obtain ⟨M, hM, hMK, hsize⟩ := exists_packing_residue_budget r
  let S : ℝ := ∑ i : Fin K, 1 / (b (o i) - a (o i))
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro i _
    exact (one_div_pos.mpr (sub_pos.mpr (hab (o i)))).le
  obtain ⟨delta, m, hd, hm, hKm, hlo, hhi, hdS⟩ := exists_packing_mesh K a b hab S ε hS hε
  obtain ⟨NU, hNU, hU⟩ := eventually_packing_cell_union M hM hMK r hr
    (fun i j _ => hsize i j) c0 B delta hc0 hB hd.le (ε * delta / 4) (by positivity)
  let N0 : ℕ := max NU (max 1 ⌈(4 * S / ε) ^ 2⌉₊)
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hNN : NU ≤ N := by dsimp [N0] at hN; omega
  have hN1 : 1 ≤ N := by dsimp [N0] at hN; omega
  let R : ℝ := Real.sqrt (N : ℝ)
  have hR : 0 < R := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
  have hR2 : R ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hNsq : (4 * S / ε) ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (by dsimp [N0] at hN; omega))
  have hSR : S ≤ ε / 4 * R := by
    have hbase : 0 ≤ 4 * S / ε := by positivity
    have hlarge : 4 * S / ε ≤ R := by nlinarith
    have hh := (div_le_iff₀ hε).mp hlarge
    nlinarith
  obtain ⟨c, hcb, hfinite⟩ := exists_finite_parity_density_mesh A a b o r m
    delta R hd hR hm hKm hlo hhi hdisj
  have hc (i : Fin K) : 0 < c i := (ha (o i)).trans_le (hcb i).1
  have hsepc (i j : Fin K) (hij : i < j) :
      ((r j - r i).natAbs : ℝ) ≤
        (shiftParityWeight (r i) (r j) : ℝ) * c i * c j := by
    have hw : (0 : ℝ) ≤ shiftParityWeight (r i) (r j) := Nat.cast_nonneg _
    exact (hsep i j hij).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hcb i).1 hw) (hcb j).1 (ha (o j)).le
      (mul_nonneg hw (hc i).le))
  have hbound := hU N hNN c (fun i => (hca (o i)).trans (hcb i).1)
    (fun i => (hcb i).2.trans (hBb (o i))) hsepc A hA
  have herr : delta * (delta * R + 1) * S ≤ delta * R * (ε / 2) := by
    have hh1 := mul_le_mul_of_nonneg_left hdS (mul_pos hd hR).le
    have hh2 := mul_le_mul_of_nonneg_left hSR hd.le
    nlinarith only [hh1, hh2]
  apply (mul_le_mul_iff_right₀ (mul_pos hd hR)).mp
  change delta * R * (∑ i, parityDensity A (a (o i)) (b (o i)) R (r i)) ≤ _
  change delta * R * (∑ i, parityDensity A (a (o i)) (b (o i)) R (r i)) ≤
    (packingCellUnion A r c delta R).card + delta * (delta * R + 1) * S at hfinite
  change ((packingCellUnion A r c delta R).card : ℝ) ≤ (delta / 2 + ε * delta / 4) * R at hbound
  nlinarith [mul_pos (mul_pos hd hR) hε]

end Erdos441

#print axioms Erdos441.eventually_parity_packing

import Jsp799.Cubic
import Jsp799.Trig
import Jsp799.Indices

/-!
# JSP-000799 / Erdős #960 — the assembly

The construction of `evidence/design.md` ("Assembly"): the point with index `i` is the point of
the nodal cubic with parameter `cot (iπ/M)`, `M = 7m`, and the configuration is the image of the
index set `Idx m s` (`n = 6m + s` points).

Since three distinct curve points `pt a, pt b, pt c` are collinear iff `ab + bc + ca = 1`
(`collinear_pt_iff`) and the cotangents satisfy that relation exactly when `M ∣ i + j + k`
(`cot_criterion`), the geometry of the configuration is *exactly* the index combinatorics of
`Jsp799.Indices`: ordinary pairs are the `ordIdx` pairs, there is no all-ordinary triple, no four
points are collinear, and there are at least `3m² − 3ms` ordinary lines.
-/

open Finset

namespace Erdos960

/-- The point with index `i`: parameter `cot(iπ/M)` on the nodal cubic. -/
noncomputable def P (m i : ℕ) : Point := pt (Real.cot (angle (M m) i))

/-- The configuration `A = P '' Idx m s` (`n = 6m + s` points). -/
noncomputable def config (m s : ℕ) : Finset Point := (Idx m s).image (P m)

theorem P_injOn (m : ℕ) : Set.InjOn (P m) {i : ℕ | 0 < i ∧ i < M m} := by
  intro i hi j hj h
  exact cot_angle_injOn (M m) hi hj (pt_injective h)

/-- Three distinct indices in `(0, M)` give collinear points iff `M ∣ i + j + k`. -/
theorem collinear_P_iff {m i j k : ℕ} (hm : 0 < m) (hi : 0 < i ∧ i < M m) (hj : 0 < j ∧ j < M m)
    (hk : 0 < k ∧ k < M m) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Collinear ℝ ({P m i, P m j, P m k} : Set Point) ↔ (i + j + k) % M m = 0 := by
  have hM : 0 < M m := by unfold M; omega
  have hinj := cot_angle_injOn (M m)
  have hi' : i ∈ {i : ℕ | 0 < i ∧ i < M m} := hi
  have hj' : j ∈ {i : ℕ | 0 < i ∧ i < M m} := hj
  have hk' : k ∈ {i : ℕ | 0 < i ∧ i < M m} := hk
  have hab : Real.cot (angle (M m) i) ≠ Real.cot (angle (M m) j) := fun h => hij (hinj hi' hj' h)
  have hbc : Real.cot (angle (M m) j) ≠ Real.cot (angle (M m) k) := fun h => hjk (hinj hj' hk' h)
  have hca : Real.cot (angle (M m) k) ≠ Real.cot (angle (M m) i) := fun h =>
    hik (hinj hk' hi' h).symm
  show Collinear ℝ ({pt _, pt _, pt _} : Set Point) ↔ _
  rw [collinear_pt_iff hab hbc hca]
  exact cot_criterion hM hi hj hk

private theorem mem_Ioo_of_mem_Idx {m s i : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (hi : i ∈ Idx m s) :
    0 < i ∧ i < M m := Finset.mem_Ioo.1 (Idx_subset hm hs hi)

private theorem P_eq_iff {m s i j : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) (hi : i ∈ Idx m s)
    (hj : j ∈ Idx m s) : P m i = P m j ↔ i = j := by
  refine ⟨fun h => P_injOn m (mem_Ioo_of_mem_Idx hm hs hi) (mem_Ioo_of_mem_Idx hm hs hj) h, ?_⟩
  rintro rfl
  rfl

private theorem mem_config {m s i : ℕ} (hi : i ∈ Idx m s) : P m i ∈ config m s :=
  Finset.mem_image_of_mem _ hi

/-- Ordinary pairs of the configuration are exactly the index-level ordinary pairs. -/
theorem ordinaryPair_config_iff {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) {i j : ℕ} (hi : i ∈ Idx m s)
    (hj : j ∈ Idx m s) : OrdinaryPair (config m s) (P m i) (P m j) ↔ ordIdx m (Idx m s) i j := by
  have hm0 : 0 < m := by omega
  have hbi := mem_Ioo_of_mem_Idx hm hs hi
  have hbj := mem_Ioo_of_mem_Idx hm hs hj
  constructor
  · rintro ⟨-, -, hne, h⟩
    have hij : i ≠ j := fun e => hne (by rw [e])
    refine ⟨hi, hj, hij, fun k hk hki hkj hzero => ?_⟩
    have hbk := mem_Ioo_of_mem_Idx hm hs hk
    have hcol : Collinear ℝ ({P m i, P m j, P m k} : Set Point) :=
      (collinear_P_iff hm0 hbi hbj hbk hij (Ne.symm hkj) (Ne.symm hki)).2 hzero
    rcases h (P m k) (mem_config hk) hcol with e | e
    · exact hki ((P_eq_iff hm hs hk hi).1 e)
    · exact hkj ((P_eq_iff hm hs hk hj).1 e)
  · rintro ⟨-, -, hij, h⟩
    refine ⟨mem_config hi, mem_config hj, fun e => hij ((P_eq_iff hm hs hi hj).1 e), ?_⟩
    intro x hx hcol
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    by_cases hki : k = i
    · exact Or.inl (by rw [hki])
    by_cases hkj : k = j
    · exact Or.inr (by rw [hkj])
    have hbk := mem_Ioo_of_mem_Idx hm hs hk
    exact absurd ((collinear_P_iff hm0 hbi hbj hbk hij (Ne.symm hkj) (Ne.symm hki)).1 hcol)
      (h k hk hki hkj)

theorem card_config {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) : (config m s).card = 6 * m + s := by
  have hsub : (↑(Idx m s) : Set ℕ) ⊆ {i : ℕ | 0 < i ∧ i < M m} := fun x hx =>
    mem_Ioo_of_mem_Idx hm hs (Finset.mem_coe.1 hx)
  rw [config, Finset.card_image_of_injOn ((P_injOn m).mono hsub), card_Idx hm hs]

-- the hypotheses `hm`, `hs` are part of the interface (they are needed for the other
-- statements); `noKCollinear` holds for any set of curve points
theorem noKCollinear_config {m s : ℕ} (_hm : 12 ≤ m) (_hs : s ≤ 5) {k : ℕ} (hk : 4 ≤ k) :
    NoKCollinear (config m s) k := by
  refine noKCollinear_of_curve (fun p hp => ?_) hk
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
  exact ⟨Real.cot (angle (M m) i), rfl⟩

theorem not_hasOrdinaryClique_config {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) {r : ℕ} (hr : 3 ≤ r) :
    ¬ HasOrdinaryClique (config m s) r := by
  classical
  rintro ⟨B, hB, hcard, hpair⟩
  obtain ⟨C, hCB, hC3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ B.card)
  obtain ⟨p, q, t, hpq, hpt, hqt, rfl⟩ := Finset.card_eq_three.mp hC3
  have hmem : ∀ x ∈ ({p, q, t} : Finset Point), x ∈ config m s := fun x hx => hB (hCB hx)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hmem p (by simp))
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (hmem q (by simp))
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (hmem t (by simp))
  have hord : ∀ {a b : ℕ}, a ∈ Idx m s → b ∈ Idx m s →
      P m a ∈ ({P m i, P m j, P m k} : Finset Point) →
      P m b ∈ ({P m i, P m j, P m k} : Finset Point) → P m a ≠ P m b →
      ordIdx m (Idx m s) a b := by
    intro a b ha hb hma hmb hab
    exact (ordinaryPair_config_iff hm hs ha hb).1
      (hpair _ (hCB hma) _ (hCB hmb) hab)
  exact no_ordinary_triangle hm hs (hord hi hj (by simp) (by simp) hpq)
    (hord hj hk (by simp) (by simp) hqt) (hord hi hk (by simp) (by simp) hpt)

theorem ordCount_config_ge {m s : ℕ} (hm : 12 ≤ m) (hs : s ≤ 5) :
    3 * m ^ 2 - 3 * m * s ≤ ordCount (config m s) := by
  classical
  set S := ((Idx m s) ×ˢ (Idx m s)).filter fun p : ℕ × ℕ => ordIdx m (Idx m s) p.1 p.2 with hS
  set φ : ℕ × ℕ → Sym2 Point := fun p => s(P m p.1, P m p.2) with hφ
  have hmemS : ∀ p ∈ S, p.1 ∈ Idx m s ∧ p.2 ∈ Idx m s ∧ ordIdx m (Idx m s) p.1 p.2 := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  -- each fibre of `φ` on `S` has at most two elements
  have hfib : ∀ e ∈ S.image φ, (S.filter fun q => φ q = e).card ≤ 2 := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hp1, hp2, -⟩ := hmemS p hp
    have hsub : (S.filter fun q => φ q = φ p) ⊆ ({p, (p.2, p.1)} : Finset (ℕ × ℕ)) := by
      intro q hq
      obtain ⟨hqS, hqe⟩ := Finset.mem_filter.1 hq
      obtain ⟨hq1, hq2, -⟩ := hmemS q hqS
      have hqe' : s(P m q.1, P m q.2) = s(P m p.1, P m p.2) := hqe
      rcases Sym2.eq_iff.1 hqe' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have hqp : q = p := by
          rw [Prod.ext_iff]
          exact ⟨(P_eq_iff hm hs hq1 hp1).1 e1, (P_eq_iff hm hs hq2 hp2).1 e2⟩
        simp [hqp]
      · have hqp : q = (p.2, p.1) := by
          rw [Prod.ext_iff]
          exact ⟨(P_eq_iff hm hs hq1 hp2).1 e1, (P_eq_iff hm hs hq2 hp1).1 e2⟩
        simp [hqp]
    calc (S.filter fun q => φ q = φ p).card ≤ ({p, (p.2, p.1)} : Finset (ℕ × ℕ)).card :=
          Finset.card_le_card hsub
      _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
  have h1 : S.card ≤ 2 * (S.image φ).card := Finset.card_le_mul_card_image S 2 hfib
  have h2 : (S.image φ).card ≤ ordCount (config m s) := by
    unfold ordCount
    refine Finset.card_le_card ?_
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hp1, hp2, hord⟩ := hmemS p hp
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Finset.mk_mem_sym2_iff.2 ⟨mem_config hp1, mem_config hp2⟩
    · show IsOrdinaryLine (config m s) s(P m p.1, P m p.2)
      rw [IsOrdinaryLine, Sym2.lift_mk]
      exact (ordinaryPair_config_iff hm hs hp1 hp2).2 hord
  have h3 := card_ordIdx_pairs hm hs
  rw [← hS] at h3
  omega

end Erdos960


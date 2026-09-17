import Erdos210Ordinary.Definitions

/-!
# Erdős Problem 210 — bridge to the Mathlib affine vocabulary

This file connects the elementary determinant vocabulary of `Definitions.lean` with Mathlib's
affine-geometry notions:

* `mem_line_iff` : `z ∈ line[ℝ, a, b] ↔ OnLine a b z` for `a ≠ b`;
* `notCollinear_iff` : `NotCollinear P ↔ ¬ Collinear ℝ ↑P`;
* `ncard_ordinaryLines` : `(ordinaryLines P).ncard = (ordinaryPairs P).card`;
* `ordinaryLines_finite` : `(ordinaryLines P).Finite`.

To stay independent of the other modules, the few facts about the parametrisation of a line and
about `ordinaryPairs` that are needed here are re-proved locally as `private` lemmas.
-/

namespace Erdos210

/-! ### Parametrisation of a line -/

/-- Every point of the form `a + s • (b - a)` lies on the line `a b`. -/
private lemma onLine_param' (a b : ℝ × ℝ) (s : ℝ) : OnLine a b (a + s • (b - a)) := by
  simp only [OnLine, D, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

/-- Conversely, every point of the line `a b` (with `a ≠ b`) has that form. -/
private lemma exists_param' {a b z : ℝ × ℝ} (hab : a ≠ b) (hz : OnLine a b z) :
    ∃ s : ℝ, z = a + s • (b - a) := by
  rw [Ne, Prod.ext_iff, not_and_or] at hab
  simp only [OnLine, D] at hz
  rcases hab with h | h
  · refine ⟨(z.1 - a.1) / (b.1 - a.1), ?_⟩
    have hb : b.1 - a.1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> field_simp <;> linarith [hz]
  · refine ⟨(z.2 - a.2) / (b.2 - a.2), ?_⟩
    have hb : b.2 - a.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> field_simp <;> linarith [hz]

/-- The relation `OnLine` is symmetric in its first two arguments. -/
private lemma onLine_comm' {a b z : ℝ × ℝ} : OnLine a b z ↔ OnLine b a z := by
  simp only [OnLine, D]
  constructor <;> intro h <;> linarith

/-! ### The frozen bridge statements -/

theorem mem_line_iff {a b : ℝ × ℝ} (hab : a ≠ b) (z : ℝ × ℝ) :
    z ∈ line[ℝ, a, b] ↔ OnLine a b z := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    exact onLine_param' a b r
  · intro hz
    obtain ⟨s, rfl⟩ := exists_param' hab hz
    exact ⟨s, by rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]⟩

theorem notCollinear_iff (P : Finset (ℝ × ℝ)) :
    NotCollinear P ↔ ¬ Collinear ℝ (P : Set (ℝ × ℝ)) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, habc⟩ hcol
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
    obtain ⟨p₀, v, hv⟩ := hcol
    obtain ⟨ra, rfl⟩ := hv a (Finset.mem_coe.2 ha)
    obtain ⟨rb, rfl⟩ := hv b (Finset.mem_coe.2 hb)
    obtain ⟨rc, rfl⟩ := hv c (Finset.mem_coe.2 hc)
    apply habc
    simp only [OnLine, D, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  · intro h
    by_contra hnc
    apply h
    simp only [NotCollinear, not_exists, not_and, not_not] at hnc
    by_cases hex : ∃ a ∈ P, ∃ b ∈ P, a ≠ b
    · obtain ⟨a, ha, b, hb, hab⟩ := hex
      rw [collinear_iff_of_mem (Finset.mem_coe.2 ha)]
      refine ⟨b - a, fun p hp => ?_⟩
      obtain ⟨s, hs⟩ := exists_param' hab (hnc a ha b hb p (Finset.mem_coe.1 hp))
      exact ⟨s, by rw [hs, vadd_eq_add, add_comm]⟩
    · have hex' : ∀ a ∈ P, ∀ b ∈ P, a = b := by
        intro a ha b hb
        by_contra hab
        exact hex ⟨a, ha, b, hb, hab⟩
      rcases Finset.eq_empty_or_nonempty P with rfl | ⟨a, ha⟩
      · simpa using collinear_empty ℝ (ℝ × ℝ)
      · exact Collinear.subset
          (fun p hp => Set.mem_singleton_iff.2 (hex' p (Finset.mem_coe.1 hp) a ha))
          (collinear_singleton ℝ a)

/-! ### Counting the ordinary lines -/

/-- Membership in `ordinaryPairs`, unfolded. -/
private lemma mem_ordinaryPairs' {P e : Finset (ℝ × ℝ)} :
    e ∈ ordinaryPairs P ↔ (e ⊆ P ∧ e.card = 2) ∧
      ∀ a ∈ e, ∀ b ∈ e, a ≠ b → ∀ c ∈ P, OnLine a b c → c ∈ e := by
  simp only [ordinaryPairs, Finset.mem_filter, Finset.mem_powersetCard]

open scoped Classical in
/-- An ordinary pair is recovered from the line it spans. -/
private lemma filter_span_eq {P e : Finset (ℝ × ℝ)} (he : e ∈ ordinaryPairs P) :
    P.filter (· ∈ affineSpan ℝ (↑e : Set (ℝ × ℝ))) = e := by
  rw [mem_ordinaryPairs'] at he
  obtain ⟨⟨hsub, hcard⟩, hord⟩ := he
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
  have hcoe : ((({a, b} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) = {a, b} := Finset.coe_pair
  apply Finset.Subset.antisymm
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcP, hcL⟩ := hc
    rw [hcoe, mem_line_iff hab] at hcL
    exact hord a (Finset.mem_insert_self _ _) b
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hab c hcP hcL
  · intro x hx
    rw [Finset.mem_filter]
    refine ⟨hsub hx, ?_⟩
    rw [hcoe]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact left_mem_affineSpan_pair ℝ _ _
    · exact right_mem_affineSpan_pair ℝ _ _

open scoped Classical in
/-- The ordinary lines of `P` are exactly the spans of the ordinary pairs of `P`. -/
private lemma ordinaryLines_eq (P : Finset (ℝ × ℝ)) :
    ordinaryLines P =
      ↑((ordinaryPairs P).image fun e : Finset (ℝ × ℝ) =>
        affineSpan ℝ (↑e : Set (ℝ × ℝ))) := by
  ext L
  simp only [Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, hab, rfl, hcard⟩
    have hcoe : ((({a, b} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) = {a, b} := Finset.coe_pair
    have hsub : ({a, b} : Finset (ℝ × ℝ)) ⊆ P.filter (· ∈ line[ℝ, a, b]) := by
      intro x hx
      rw [Finset.mem_filter]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨ha, left_mem_affineSpan_pair ℝ _ _⟩
      · exact ⟨hb, right_mem_affineSpan_pair ℝ _ _⟩
    have hpc : ({a, b} : Finset (ℝ × ℝ)).card = 2 := Finset.card_pair hab
    have heq : ({a, b} : Finset (ℝ × ℝ)) = P.filter (· ∈ line[ℝ, a, b]) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hpc])
    refine ⟨{a, b}, ?_, by rw [hcoe]⟩
    rw [mem_ordinaryPairs']
    refine ⟨⟨fun x hx => (Finset.mem_filter.1 (hsub hx)).1, hpc⟩, ?_⟩
    intro x hx y hy hxy c hcP hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hcL : OnLine a b c := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hc
      · exact onLine_comm'.2 hc
      · exact absurd rfl hxy
    rw [heq, Finset.mem_filter]
    exact ⟨hcP, (mem_line_iff hab c).2 hcL⟩
  · rintro ⟨e, he, rfl⟩
    have hmem := he
    rw [mem_ordinaryPairs'] at hmem
    obtain ⟨⟨hsub, hcard⟩, -⟩ := hmem
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
    have hcoe : ((({a, b} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) = {a, b} := Finset.coe_pair
    refine ⟨a, hsub (Finset.mem_insert_self _ _), b,
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), hab, by rw [hcoe], ?_⟩
    rw [filter_span_eq he]
    exact Finset.card_pair hab

open scoped Classical in
theorem ncard_ordinaryLines (P : Finset (ℝ × ℝ)) :
    (ordinaryLines P).ncard = (ordinaryPairs P).card := by
  have hinj : Set.InjOn (fun e : Finset (ℝ × ℝ) => affineSpan ℝ (↑e : Set (ℝ × ℝ)))
      ↑(ordinaryPairs P) := by
    intro e₁ h₁ e₂ h₂ hspan
    simp only at hspan
    have h := filter_span_eq (Finset.mem_coe.1 h₁)
    rw [hspan, filter_span_eq (Finset.mem_coe.1 h₂)] at h
    exact h.symm
  rw [ordinaryLines_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

open scoped Classical in
theorem ordinaryLines_finite (P : Finset (ℝ × ℝ)) : (ordinaryLines P).Finite := by
  rw [ordinaryLines_eq]
  exact Finset.finite_toSet _

end Erdos210

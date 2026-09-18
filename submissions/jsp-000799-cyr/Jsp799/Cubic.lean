import Jsp799.Defs

/-!
# JSP-000799 / Erdős #960 — the nodal cubic and its collinearity law

The construction of `evidence/design.md` ("Curve and parametrization", "Collinearity ↔ Mathlib")
places all points on the real nodal cubic `y² = x²(x − 1)`, parametrized by
`pt t = (t² + 1, t (t² + 1))`.

The orientation determinant of three curve points factors as
`(b − a)(c − b)(c − a)(ab + bc + ca − 1)`, so three distinct curve points are collinear exactly
when `ab + bc + ca = 1`; no four distinct curve points are collinear.
-/

namespace Erdos960

/-- Orientation determinant of three points of the plane. -/
def det (p q r : Point) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- A point of the plane written as base point plus a multiple of a direction vector. -/
private theorem eq_smul_vadd_of {p q x : Point} {c : ℝ} (h1 : x.1 - p.1 = c * (q.1 - p.1))
    (h2 : x.2 - p.2 = c * (q.2 - p.2)) : x = c • (q - p) +ᵥ p := by
  have e1 : (c • (q - p) +ᵥ p).1 = c * (q.1 - p.1) + p.1 := by
    simp [vadd_eq_add]
  have e2 : (c • (q - p) +ᵥ p).2 = c * (q.2 - p.2) + p.2 := by
    simp [vadd_eq_add]
  rw [Prod.ext_iff]
  exact ⟨by rw [e1]; linarith, by rw [e2]; linarith⟩

/-- For `p ≠ q`, Mathlib collinearity of `{p, q, r}` is the vanishing of the determinant. -/
theorem collinear_iff_det {p q r : Point} (hpq : p ≠ q) :
    Collinear ℝ ({p, q, r} : Set Point) ↔ det p q r = 0 := by
  constructor
  · intro h
    rw [collinear_iff_of_mem (Set.mem_insert p {q, r})] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨s, hs⟩ := hv q (by simp)
    obtain ⟨t, ht⟩ := hv r (by simp)
    subst hs
    subst ht
    show ((s • v +ᵥ p).1 - p.1) * ((t • v +ᵥ p).2 - p.2)
        - ((s • v +ᵥ p).2 - p.2) * ((t • v +ᵥ p).1 - p.1) = 0
    simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · intro hdet
    have hd : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) = 0 := hdet
    rw [collinear_iff_of_mem (Set.mem_insert p {q, r})]
    refine ⟨q - p, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, eq_smul_vadd_of (by ring) (by ring)⟩
    · exact ⟨1, eq_smul_vadd_of (by ring) (by ring)⟩
    · by_cases hx1 : q.1 - p.1 = 0
      · have hx2 : q.2 - p.2 ≠ 0 := by
          intro h0
          exact hpq (by rw [Prod.ext_iff]; constructor <;> linarith)
        have hr1 : x.1 - p.1 = 0 := by
          have hz : (q.2 - p.2) * (x.1 - p.1) = 0 := by rw [hx1] at hd; linarith
          rcases mul_eq_zero.mp hz with h | h
          · exact absurd h hx2
          · exact h
        refine ⟨(x.2 - p.2) / (q.2 - p.2), eq_smul_vadd_of ?_ ?_⟩
        · rw [hx1, hr1]; ring
        · field_simp
      · refine ⟨(x.1 - p.1) / (q.1 - p.1), eq_smul_vadd_of ?_ ?_⟩
        · field_simp
        · field_simp
          linarith

/-- The parametrized real nodal cubic `y² = x²(x − 1)`: `pt t = (t² + 1, t(t² + 1))`. -/
def pt (t : ℝ) : Point := (t ^ 2 + 1, t * (t ^ 2 + 1))

theorem pt_injective : Function.Injective pt := by
  intro a b h
  have h1 : a ^ 2 + 1 = b ^ 2 + 1 := congrArg Prod.fst h
  have h2 : a * (a ^ 2 + 1) = b * (b ^ 2 + 1) := congrArg Prod.snd h
  have hsq : a ^ 2 = b ^ 2 := by linarith
  have key : (a - b) * (a ^ 2 + 1) = 0 := by linear_combination h2 - b * hsq
  rcases mul_eq_zero.mp key with h' | h'
  · linarith
  · nlinarith [sq_nonneg a]

/-- The determinant of three curve points factors. -/
theorem det_pt (a b c : ℝ) :
    det (pt a) (pt b) (pt c) = (b - a) * (c - b) * (c - a) * (a * b + b * c + c * a - 1) := by
  show ((pt b).1 - (pt a).1) * ((pt c).2 - (pt a).2)
      - ((pt b).2 - (pt a).2) * ((pt c).1 - (pt a).1) = _
  simp only [pt]
  ring

/-- Three distinct curve points are collinear iff `ab + bc + ca = 1`. -/
theorem collinear_pt_iff {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Collinear ℝ ({pt a, pt b, pt c} : Set Point) ↔ a * b + b * c + c * a = 1 := by
  rw [collinear_iff_det (pt_injective.ne hab), det_pt]
  have h1 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h2 : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have h3 : c - a ≠ 0 := sub_ne_zero.mpr hca
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h₁ | h₁
        · exact absurd h₁ h1
        · exact absurd h₁ h2
      · exact absurd h'' h3
    · linarith
  · intro h
    have : a * b + b * c + c * a - 1 = 0 := by linarith
    rw [this, mul_zero]

/-- No four distinct curve points are collinear. -/
theorem not_collinear_four {a b c d : ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ¬ Collinear ℝ ({pt a, pt b, pt c, pt d} : Set Point) := by
  intro h
  have hsub1 : ({pt a, pt b, pt c} : Set Point) ⊆ {pt a, pt b, pt c, pt d} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hsub2 : ({pt a, pt b, pt d} : Set Point) ⊆ {pt a, pt b, pt c, pt d} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have h1 : a * b + b * c + c * a = 1 :=
    (collinear_pt_iff hab hbc (Ne.symm hac)).mp (h.subset hsub1)
  have h2 : a * b + b * d + d * a = 1 :=
    (collinear_pt_iff hab hbd (Ne.symm had)).mp (h.subset hsub2)
  have hcd' : c - d ≠ 0 := sub_ne_zero.mpr hcd
  have key : (c - d) * (a + b) = 0 := by linarith [h1, h2]
  have hab0 : a + b = 0 := by
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' hcd'
    · exact h'
  have hb : b = -a := by linarith
  rw [hb] at h1
  nlinarith [sq_nonneg a]

/-- A finite set of curve points has no `k` collinear points for every `k ≥ 4`. -/
theorem noKCollinear_of_curve {A : Finset Point} (hA : ∀ p ∈ A, ∃ t : ℝ, p = pt t) {k : ℕ}
    (hk : 4 ≤ k) : NoKCollinear A k := by
  classical
  intro B hB hcard hcol
  obtain ⟨C, hCB, hC4⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ B.card)
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := Finset.card_eq_four.mp hC4
  have hmemA : ∀ x ∈ ({p, q, r, s} : Finset Point), x ∈ A := fun x hx => hB (hCB hx)
  obtain ⟨a, rfl⟩ := hA p (hmemA p (by simp))
  obtain ⟨b, rfl⟩ := hA q (hmemA q (by simp))
  obtain ⟨c, rfl⟩ := hA r (hmemA r (by simp))
  obtain ⟨d, rfl⟩ := hA s (hmemA s (by simp))
  have hsub : ({pt a, pt b, pt c, pt d} : Set Point) ⊆ (B : Set Point) := by
    simpa using Finset.coe_subset.mpr hCB
  exact not_collinear_four (fun h => hpq (by rw [h])) (fun h => hpr (by rw [h]))
    (fun h => hps (by rw [h])) (fun h => hqr (by rw [h])) (fun h => hqs (by rw [h]))
    (fun h => hrs (by rw [h])) (hcol.subset hsub)

end Erdos960


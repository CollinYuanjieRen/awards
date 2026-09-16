import Mathlib
import JSP573.FF.RankLemmas

/-!
# Frankl–Füredi 1984, Theorem 1.4 (Frankl–Singhi): full row rank of the containment matrix

Let `𝓕` be a family of `h`-subsets of `range n` with `#(A ∩ B) ≠ t` for all distinct
`A, B ∈ 𝓕`, and suppose `h - t` has a prime-power divisor `p ^ s > t`. Then the rows
`inclVec n (h - t - 1) A`, `A ∈ 𝓕`, are linearly independent over `ℚ`.

Proof (appendix of the paper). Suppose `∑_A c_A · inclVec A = 0` with `c ≠ 0`; rescale to integers
`c_A` not all divisible by `p` (`exists_int_rescale_not_all_dvd`) and fix `A₁` with `p ∤ c_{A₁}`.
Summing the relation over the `(h - t - 1)`-sets `T ⊇ S` gives, for every `S` with `#S = s`,
`∑_{A ⊇ S} c_A · C(h - s, h - t - 1 - s) = 0` (11); summing over the `s`-subsets `S` of `A₁` gives
`∑_A c_A · C(#(A ∩ A₁), s) · C(h - s, h - t - 1 - s) = 0` (12) for every `s ≤ h - t - 1`.
Combining (12) with the coefficients of `exists_ffPoly_expansion` yields
`∑_A c_A · ffPoly h t (#(A ∩ A₁)) = 0`. For `A ≠ A₁`, `#(A ∩ A₁) ∈ [0, h - 1] \ {t}`: the value is
`0` for `t < #(A ∩ A₁) < h` (`ffPoly_eq_zero`) and `C(h - 1 - j, h - t - 1)` for `j ≤ t - 1`,
which is divisible by `p` (`ffPoly_eq_choose`, `prime_dvd_choose_of_pow_dvd_succ` with
`k = h - t - 1`, `d = t - j`); for `A = A₁` it is `(-1) ^ (h - t - 1)` (`ffPoly_at_top`). Reducing
the integer identity modulo `p` gives `p ∣ c_{A₁}`, a contradiction.
-/

open Finset

namespace FranklFuredi

/-- The integral value of `ffPoly h t (#(B ∩ C))` on `h`-sets `B` meeting the fixed `h`-set `C`
in a number of points different from `t`: `(-1) ^ (h - t - 1)` at `B = C`, `0` when
`t < #(B ∩ C)`, and `C(h - 1 - #(B ∩ C), h - t - 1)` when `#(B ∩ C) < t`. -/
private def wt (h t : ℕ) (C B : Finset ℕ) : ℤ :=
  if B = C then (-1) ^ (h - t - 1)
  else if t < #(B ∩ C) then 0 else ((h - 1 - #(B ∩ C)).choose (h - t - 1) : ℤ)

/-- `wt` indeed computes `ffPoly h t (#(B ∩ C))` on such a set `B`. -/
private lemma wt_cast (h t : ℕ) (ht : t < h) (C B : Finset ℕ) (hB : #B = h) (hC : #C = h)
    (hne : B ≠ C → #(B ∩ C) ≠ t) : ((wt h t C B : ℤ) : ℚ) = ffPoly h t (#(B ∩ C)) := by
  unfold wt
  by_cases hBC : B = C
  · subst hBC
    rw [ite_eq_left rfl, Finset.inter_self, hB, ffPoly_at_top h t ht]
    push_cast
    ring
  · rw [ite_eq_right hBC]
    have hsub : B ∩ C ⊆ C := Finset.inter_subset_right
    have hle : #(B ∩ C) ≤ h := hC ▸ Finset.card_le_card hsub
    have hlt : #(B ∩ C) < h := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · refine absurd ?_ hBC
        have h1 : B ∩ C = C := Finset.eq_of_subset_of_card_le hsub (by omega)
        exact (Finset.eq_of_subset_of_card_le (h1 ▸ Finset.inter_subset_left) (by omega)).symm
    rcases lt_trichotomy (#(B ∩ C)) t with hj | hj | hj
    · rw [ite_eq_right (by omega), ffPoly_eq_choose h t _ ht hj.le]
      push_cast
      ring
    · exact absurd hj (hne hBC)
    · rw [ite_eq_left hj, ffPoly_eq_zero h t _ hj hlt]
      norm_num

/-- Away from the distinguished set `C`, the prime `p` divides `wt`. -/
private lemma prime_dvd_wt (p s h t : ℕ) (hp : p.Prime) (hs : 0 < s) (hdiv : p ^ s ∣ h - t)
    (hq : t < p ^ s) (ht : t < h) (C B : Finset ℕ) (hBC : B ≠ C) (hnt : #(B ∩ C) ≠ t) :
    (p : ℤ) ∣ wt h t C B := by
  unfold wt
  rw [ite_eq_right hBC]
  by_cases hj : t < #(B ∩ C)
  · rw [ite_eq_left hj]
    exact dvd_zero _
  · rw [ite_eq_right hj]
    have hk : p ^ s ∣ (h - t - 1) + 1 := by
      rwa [show h - t - 1 + 1 = h - t by omega]
    have hidx : h - 1 - #(B ∩ C) = (h - t - 1) + (t - #(B ∩ C)) := by omega
    rw [hidx]
    exact_mod_cast prime_dvd_choose_of_pow_dvd_succ p s (h - t - 1) (t - #(B ∩ C)) hp hs hk
      (by omega) (by omega)

/-- Theorem 1.4 (Frankl–Singhi). -/
theorem frankl_singhi (n h t p s : ℕ) (hp : p.Prime) (hs : 0 < s) (hdiv : p ^ s ∣ h - t)
    (hq : t < p ^ s) (ht : t < h) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕)
    (hav : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → #(A ∩ B) ≠ t) :
    LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A) := by
  rw [Fintype.linearIndependent_iff]
  intro c hrel A₀
  by_contra hA₀
  have hcne : c ≠ 0 := fun hc ↦ hA₀ (by simp [hc])
  obtain ⟨d, L, hL, hdL, A₁, hA₁⟩ := exists_int_rescale_not_all_dvd p hp c hcne
  obtain ⟨h1n, h1h⟩ := hU _ A₁.2
  have key : ∀ T : Finset ℕ, T ⊆ range n → #T = h - t - 1 →
      ∑ A : 𝓕, (d A : ℚ) * (if T ⊆ (A : Finset ℕ) then 1 else 0) = 0 := by
    intro T hT1 hT2
    have hTm : T ∈ (range n).powersetCard (h - t - 1) := Finset.mem_powersetCard.2 ⟨hT1, hT2⟩
    have h0 := congrFun hrel ⟨T, hTm⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, inclVec] at h0
    have hfac : ∑ A : 𝓕, (d A : ℚ) * (if T ⊆ (A : Finset ℕ) then 1 else 0)
        = L * ∑ A : 𝓕, c A * (if T ⊆ (A : Finset ℕ) then 1 else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun A _ ↦ by rw [hdL A]; ring
    rw [hfac, h0, mul_zero]
  have h11 : ∀ S : Finset ℕ, S ⊆ range n → #S ≤ h - t - 1 →
      ∑ A : 𝓕, (d A : ℚ) * (if S ⊆ (A : Finset ℕ) then 1 else 0)
        * (((h - #S).choose (h - t - 1 - #S) : ℕ) : ℚ) = 0 := by
    intro S hS hSg
    have hz : ∑ T ∈ ((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T),
        ∑ A : 𝓕, (d A : ℚ) * (if T ⊆ (A : Finset ℕ) then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun T hT ↦ by
        rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
        exact key T hT.1.1 hT.1.2
    have hcnt : ∀ A : 𝓕, ∑ T ∈ ((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T),
        (if T ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)
        = (if S ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)
          * (((h - #S).choose (h - t - 1 - #S) : ℕ) : ℚ) := by
      intro A
      obtain ⟨hAn, hAh⟩ := hU _ A.2
      rw [Finset.sum_boole]
      by_cases hSA : S ⊆ (A : Finset ℕ)
      · rw [ite_eq_left hSA, one_mul]
        have hset : (((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T)).filter
            (fun T ↦ T ⊆ (A : Finset ℕ))
            = ((A : Finset ℕ).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_powersetCard]
          exact ⟨fun hx ↦ ⟨⟨hx.2, hx.1.1.2⟩, hx.1.2⟩,
            fun hx ↦ ⟨⟨⟨hx.1.1.trans hAn, hx.1.2⟩, hx.2⟩, hx.1.1⟩⟩
        rw [hset, Finset.card_filter_powersetCard_subset S _ _ hSA hSg, hAh]
      · rw [ite_eq_right hSA, zero_mul]
        have hset : (((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T)).filter
            (fun T ↦ T ⊆ (A : Finset ℕ)) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro T hT
          simp only [Finset.mem_filter] at hT
          exact hSA (hT.1.2.trans hT.2)
        rw [hset]
        simp
    rw [Finset.sum_comm] at hz
    refine Eq.trans ?_ hz
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    rw [mul_assoc, ← hcnt A, Finset.mul_sum]
  have h12 : ∀ σ : ℕ, σ ≤ h - t - 1 →
      ∑ A : 𝓕, (d A : ℚ) * (((#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))).choose σ : ℕ) : ℚ)
        * (((h - σ).choose (h - t - 1 - σ) : ℕ) : ℚ) = 0 := by
    intro σ hσ
    have hz : ∑ S ∈ (A₁ : Finset ℕ).powersetCard σ, ∑ A : 𝓕,
        (d A : ℚ) * (if S ⊆ (A : Finset ℕ) then 1 else 0)
          * (((h - #S).choose (h - t - 1 - #S) : ℕ) : ℚ) = 0 :=
      Finset.sum_eq_zero fun S hS ↦ by
        rw [Finset.mem_powersetCard] at hS
        exact h11 S (hS.1.trans h1n) (hS.2 ▸ hσ)
    have hz2 : ∑ S ∈ (A₁ : Finset ℕ).powersetCard σ, ∑ A : 𝓕,
        (d A : ℚ) * (if S ⊆ (A : Finset ℕ) then 1 else 0)
          * (((h - σ).choose (h - t - 1 - σ) : ℕ) : ℚ) = 0 := by
      refine Eq.trans ?_ hz
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      rw [(Finset.mem_powersetCard.1 hS).2]
    rw [Finset.sum_comm] at hz2
    refine Eq.trans ?_ hz2
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    have hcnt2 : ∑ S ∈ (A₁ : Finset ℕ).powersetCard σ,
        (if S ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)
        = (((#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))).choose σ : ℕ) : ℚ) := by
      rw [Finset.sum_boole]
      congr 1
      have hset : ((A₁ : Finset ℕ).powersetCard σ).filter (fun S ↦ S ⊆ (A : Finset ℕ))
          = ((A : Finset ℕ) ∩ (A₁ : Finset ℕ)).powersetCard σ := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
        tauto
      rw [hset, Finset.card_powersetCard]
    rw [← hcnt2, Finset.mul_sum, Finset.sum_mul]
  obtain ⟨α, hα⟩ := exists_ffPoly_expansion h t ht
  have hmain : ∑ A : 𝓕, (d A : ℚ) * ffPoly h t (#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))) = 0 := by
    have hstep : ∀ A : 𝓕, (d A : ℚ) * ffPoly h t (#((A : Finset ℕ) ∩ (A₁ : Finset ℕ)))
        = ∑ σ ∈ Finset.range (h - t), α σ * ((d A : ℚ)
            * (((#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))).choose σ : ℕ) : ℚ)
            * (((h - σ).choose (h - t - 1 - σ) : ℕ) : ℚ)) := by
      intro A
      rw [hα, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ ↦ by ring
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun σ hσ ↦ ?_
    rw [Finset.mem_range] at hσ
    rw [← Finset.mul_sum, h12 σ (by omega), mul_zero]
  have hcast : ∀ A : 𝓕, ((wt h t (A₁ : Finset ℕ) (A : Finset ℕ) : ℤ) : ℚ)
      = ffPoly h t (#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))) := by
    intro A
    obtain ⟨hAn, hAh⟩ := hU _ A.2
    exact wt_cast h t ht _ _ hAh h1h fun hne ↦ hav _ A.2 _ A₁.2 hne
  have hZ : ∑ A : 𝓕, d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) = 0 := by
    have h1 : ((∑ A : 𝓕, d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) : ℤ) : ℚ) = 0 := by
      push_cast [hcast]
      exact hmain
    exact_mod_cast h1
  have hsplit : (p : ℤ) ∣ d A₁ * (-1) ^ (h - t - 1) := by
    have he : d A₁ * (-1) ^ (h - t - 1)
        + ∑ A ∈ Finset.univ.erase A₁, d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) = 0 := by
      have hw1 : wt h t (A₁ : Finset ℕ) (A₁ : Finset ℕ) = (-1) ^ (h - t - 1) := by
        simp [wt]
      rw [← hw1, Finset.add_sum_erase Finset.univ
        (fun A : 𝓕 ↦ d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ)) (Finset.mem_univ A₁)]
      exact hZ
    have hrest : (p : ℤ) ∣ ∑ A ∈ Finset.univ.erase A₁,
        d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) :=
      Finset.dvd_sum fun A hA ↦ by
        have hne : (A : Finset ℕ) ≠ (A₁ : Finset ℕ) := fun hEq ↦
          Finset.ne_of_mem_erase hA (Subtype.ext hEq)
        exact Dvd.dvd.mul_left (prime_dvd_wt p s h t hp hs hdiv hq ht _ _ hne
          (hav _ A.2 _ A₁.2 hne)) _
    rw [eq_neg_of_add_eq_zero_left he]
    exact dvd_neg.2 hrest
  refine hA₁ ?_
  have hsq : ((-1 : ℤ) ^ (h - t - 1)) * ((-1 : ℤ) ^ (h - t - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hfin := hsplit.mul_right ((-1 : ℤ) ^ (h - t - 1))
  rwa [mul_assoc, hsq, mul_one] at hfin

end FranklFuredi

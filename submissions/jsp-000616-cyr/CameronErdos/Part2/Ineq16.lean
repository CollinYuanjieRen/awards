import CameronErdos.Part2.Projection
import CameronErdos.Part2.IntervalBM

/-!
# `Lem_16`: Green's inequalities (15) and (16)

This file formalises the two displayed inequalities on p. 9 of Green, *The Cameron–Erdős
conjecture* (2004), which turn the interval data of `Lem_IntervalBM` together with the
projection `π : ℤ → ℤ/tℤ` (`t = M - m`) into the upper bound

`|D(π(A), 8 √ε N)| ≤ 2 N (1 + 30 ε^{1/8}) − 3 |A|`.

The combinatorial heart is `card_add_card_le_card_popularDiff`, Green's (15):

`|D(A, √ε N)| ≥ |D(π(A), 8 √ε N)| + |B|`.

Indeed, Lemma 11 (iii) (`projection_popularDiff_lift`) supplies, for each residue
`e ∈ D(π(A), 8 √ε N)`, an integer lift `ℓ e ∈ D(A, √ε N)`; and for each `b ∈ B` the two
integers `b − m` and `b − M` are *distinct* elements of `D(A, √ε N)` with the *same*
residue `π(b − m) ∈ D(π(A), 8 √ε N)` (Lemma 11 (ii)), so at least one of them — call it
`φ b` — differs from the chosen lift of that residue.  The map `φ` is injective on `B`
(two elements of `B` differ by less than `t`), and its image misses the image of `ℓ`,
whence (15).

Combining with Lemma 8 (`lem8_card_popularDiff_le`), `|B| ≥ |A| − 50 ε^{1/8} N` and
`|π(A)| ≥ |B|` (Lemma 11 (i)) gives the packaged statement `lem16`, which is exactly what
Proposition 7 consumes.
-/

open Finset

namespace CameronErdos

section Ineq16

variable {N : ℕ} {A : Finset ℤ}

/-! ## Monotonicity of `popularDiff` in the popularity threshold -/

/-- Raising the popularity threshold shrinks the set of popular differences. -/
lemma popularDiff_subset_of_le {G : Type*} [AddGroup G] [DecidableEq G] (A : Finset G)
    {K K' : ℝ} (h : K ≤ K') : popularDiff A K' ⊆ popularDiff A K := by
  intro d hd
  simp only [popularDiff, Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, le_trans h hd.2⟩

/-! ## Green's inequality (15) -/

/-- **Green (15)**.  Let `A ⊆ [1, N]`, let `t > N/4` be a positive modulus, let `m < M` be
integers with `M − m = t`, and let `B` be a set of integers each of which lies strictly
between `m` and `M` and is `32 δ N`-popularly linked to both `m` and `M`.  Then

`|D(π(A), 8 δ N)| + |B| ≤ |D(A, δ N)|`,

where `π : ℤ → ZMod t` is reduction mod `t`. -/
theorem card_add_card_le_card_popularDiff
    (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {t : ℕ} (ht : 0 < t) (htN : (N : ℝ) / 4 < t)
    {δ : ℝ} (hδ : 0 < δ) {m M : ℤ} (hMm : M - m = (t : ℤ)) {B : Finset ℤ}
    (hBmem : ∀ b ∈ B, m < b ∧ b < M ∧
      b - m ∈ popularDiff A (32 * δ * (N : ℝ)) ∧ b - M ∈ popularDiff A (32 * δ * (N : ℝ))) :
    #(popularDiff (projImage t A) (8 * δ * (N : ℝ))) + #B
      ≤ #(popularDiff A (δ * (N : ℝ))) := by
  classical
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsub32 : popularDiff A (32 * δ * (N : ℝ)) ⊆ popularDiff A (δ * (N : ℝ)) :=
    popularDiff_subset_of_le A (by nlinarith)
  -- `b − M` and `b − m` have the same residue mod `t`, since `M − m = t`.
  have hres : ∀ b : ℤ, ((b - M : ℤ) : ZMod t) = ((b - m : ℤ) : ZMod t) := by
    intro b
    have hbm : (b - M : ℤ) = (b - m) - (t : ℤ) := by omega
    rw [hbm]
    push_cast
    simp
  -- Lemma 11 (iii): a lift of every popular residue.
  have key : ∀ e : ZMod t, ∃ d : ℤ,
      e ∈ popularDiff (projImage t A) (8 * δ * (N : ℝ)) →
        ((d : ZMod t) = e ∧ d ∈ popularDiff A (δ * (N : ℝ))) := by
    intro e
    by_cases he : e ∈ popularDiff (projImage t A) (8 * δ * (N : ℝ))
    · obtain ⟨d, h1, -, -, h4⟩ := projection_popularDiff_lift hA ht htN hδ he
      exact ⟨d, fun _ => ⟨h1, h4⟩⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose ℓ hℓ using key
  -- Lemma 11 (ii): the common residue of `b − m` and `b − M` is popular for `π(A)`.
  have hebDpi : ∀ b ∈ B, ((b - m : ℤ) : ZMod t)
      ∈ popularDiff (projImage t A) (8 * δ * (N : ℝ)) := by
    intro b hb
    obtain ⟨-, -, h3, -⟩ := hBmem b hb
    have h8 : (0 : ℝ) < 8 * δ := by linarith
    have hconv : (4 : ℝ) * (8 * δ) * (N : ℝ) = 32 * δ * (N : ℝ) := by ring
    exact projection_popularDiff_mem hA ht htN h8 (d := b - m) (by rw [hconv]; exact h3)
  -- For `b ∈ B` pick the popular difference `φ b ∈ {b − m, b − M}` avoiding the lift.
  have keyB : ∀ b : ℤ, ∃ c : ℤ, b ∈ B →
      (c ∈ popularDiff A (δ * (N : ℝ)) ∧ ((c : ZMod t)) = ((b - m : ℤ) : ZMod t) ∧
        ℓ (((b - m : ℤ) : ZMod t)) ≠ c ∧ (c = b - m ∨ c = b - M)) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨h1, h2, h3, h4⟩ := hBmem b hb
      by_cases hc : ℓ (((b - m : ℤ) : ZMod t)) = b - m
      · refine ⟨b - M, fun _ => ⟨hsub32 h4, hres b, ?_, Or.inr rfl⟩⟩
        rw [hc]
        omega
      · exact ⟨b - m, fun _ => ⟨hsub32 h3, rfl, hc, Or.inl rfl⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose φ hφ using keyB
  -- `ℓ` is injective on the popular residues.
  have hS1card : #((popularDiff (projImage t A) (8 * δ * (N : ℝ))).image ℓ)
      = #(popularDiff (projImage t A) (8 * δ * (N : ℝ))) := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have h1 := (hℓ a (by simpa using ha)).1
    have h2 := (hℓ b (by simpa using hb)).1
    rw [← h1, ← h2, hab]
  -- `φ` is injective on `B`.
  have hS2card : #(B.image φ) = #B := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have hA' : a ∈ B := by simpa using ha
    have hB' : b ∈ B := by simpa using hb
    obtain ⟨ha1, ha2, -, -⟩ := hBmem a hA'
    obtain ⟨hb1, hb2, -, -⟩ := hBmem b hB'
    rcases (hφ a hA').2.2.2 with h | h <;> rcases (hφ b hB').2.2.2 with h' | h' <;>
      rw [h, h'] at hab <;> omega
  -- The two images are disjoint.
  have hdisj : Disjoint ((popularDiff (projImage t A) (8 * δ * (N : ℝ))).image ℓ)
      (B.image φ) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨eE, heE, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.1 hy'
    have h1 := hℓ eE heE
    have h2 := hφ b hb
    have hEq : eE = ((b - m : ℤ) : ZMod t) := by
      rw [← h1.1, ← hbeq]; exact h2.2.1
    rw [hEq] at hbeq
    exact h2.2.2.1 hbeq.symm
  -- Both images consist of `δ N`-popular differences of `A`.
  have hsubD : ((popularDiff (projImage t A) (8 * δ * (N : ℝ))).image ℓ) ∪ (B.image φ)
      ⊆ popularDiff A (δ * (N : ℝ)) := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · obtain ⟨eE, heE, rfl⟩ := Finset.mem_image.1 h
      exact (hℓ eE heE).2
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h
      exact (hφ b hb).1
  calc #(popularDiff (projImage t A) (8 * δ * (N : ℝ))) + #B
      = #((popularDiff (projImage t A) (8 * δ * (N : ℝ))).image ℓ) + #(B.image φ) := by
        rw [hS1card, hS2card]
    _ = #(((popularDiff (projImage t A) (8 * δ * (N : ℝ))).image ℓ) ∪ (B.image φ)) :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ #(popularDiff A (δ * (N : ℝ))) := Finset.card_le_card hsubD

/-! ## Numerical preliminaries -/

/-- If `a ≤ b * b` and `0 ≤ b` then `√a ≤ b`. -/
private lemma sqrt_le_of_le_mul_self' {a b : ℝ} (hb : 0 ≤ b) (hab : a ≤ b * b) :
    Real.sqrt a ≤ b := by
  calc Real.sqrt a ≤ Real.sqrt (b * b) := Real.sqrt_le_sqrt hab
    _ = b := Real.sqrt_mul_self hb

/-- The slack estimate `2 √ε N + 1 ≤ 10 ε^{1/8} N`, in the abstract form used below:
here `x = ε^{1/8}` and `s = x⁴ = √ε`. -/
private lemma slack_bound {x s NN : ℝ} (hx0 : 0 ≤ x) (hxle : x ≤ 1 / 1000)
    (hxN : 1000 ≤ x * NN) (hs : s = x * x * (x * x)) :
    2 * s * NN + 1 ≤ 10 * (x * NN) := by
  have h1 : x * x ≤ (1 / 1000 : ℝ) * (1 / 1000) := mul_le_mul hxle hxle hx0 (by norm_num)
  have h2 : x * x * x ≤ ((1 / 1000 : ℝ) * (1 / 1000)) * (1 / 1000) :=
    mul_le_mul h1 hxle hx0 (by norm_num)
  have hxNpos : (0 : ℝ) < x * NN := by linarith
  have h3 : 2 * s * NN = (2 * (x * x * x)) * (x * NN) := by rw [hs]; ring
  have h4 : (2 * (x * x * x)) * (x * NN) ≤ 9 * (x * NN) :=
    mul_le_mul_of_nonneg_right (by norm_num at h2 ⊢; linarith) hxNpos.le
  linarith

/-! ## Green's inequality (16) -/

/-- **`Lem_16`** (Green (15)–(16), p. 9).  Everything Proposition 7 needs: the anchors
`m < M` in `A` with `M − m > N/4`, the endpoint counts, the lower bound
`|π(A)| ≥ |A| − 50 ε^{1/8} N` and the upper bound
`|D(π(A), 8 √ε N)| ≤ 2 N (1 + 30 ε^{1/8}) − 3 |A|`, where `t = M − m` and
`π : ℤ → ZMod t` is reduction mod `t`. -/
theorem lem16 (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε)
    (hε0 : ε ≤ 1 / 10 ^ 24)
    (hN : (1000 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ))
    (hAcard : (1 / 2 - 1 / 50 : ℝ) * (N : ℝ) ≤ (#A : ℝ))
    (htr : (addTriples A : ℝ) ≤ ε * (N : ℝ) ^ 2) :
    ∃ m M : ℤ, m ∈ A ∧ M ∈ A ∧ m < M ∧
      (N : ℝ) / 4 < (M : ℝ) - (m : ℝ) ∧
      ((#{a ∈ A | a ≤ m} : ℝ) ≤ 9 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)) ∧
      ((#{a ∈ A | M ≤ a} : ℝ) ≤ 9 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)) ∧
      ((#A : ℝ) - 50 * Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)
        ≤ (#(projImage (M - m).toNat A) : ℝ)) ∧
      ((#(popularDiff (projImage (M - m).toNat A) (8 * Real.sqrt ε * (N : ℝ))) : ℝ)
        ≤ 2 * (N : ℝ) * (1 + 30 * Real.sqrt (Real.sqrt (Real.sqrt ε))) - 3 * (#A : ℝ)) := by
  classical
  obtain ⟨m, M, hm, hM, hmM, -, -, hleft, hright, hBcard, hgap⟩ :=
    lem_intervalBM hA hε hε0 hN hAcard
  -- the modulus `t = M − m`
  have htZ : (((M - m).toNat : ℕ) : ℤ) = M - m := Int.toNat_of_nonneg (by omega)
  have ht : 0 < (M - m).toNat := by omega
  have htR : (((M - m).toNat : ℕ) : ℝ) = (M : ℝ) - (m : ℝ) := by exact_mod_cast htZ
  have htN : (N : ℝ) / 4 < (((M - m).toNat : ℕ) : ℝ) := by rw [htR]; exact hgap
  -- the set `B`
  set B : Finset ℤ := {a ∈ A | m < a ∧ a < M ∧
      a - m ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ)) ∧
      a - M ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ))} with hBdef
  have hBmem : ∀ b ∈ B, m < b ∧ b < M ∧
      b - m ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ)) ∧
      b - M ∈ popularDiff A (32 * Real.sqrt ε * (N : ℝ)) := by
    intro b hb
    exact (Finset.mem_filter.1 hb).2
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hBIoo : B ⊆ Finset.Ioo m (m + (((M - m).toNat : ℕ) : ℤ)) := by
    intro b hb
    obtain ⟨h1, h2, -, -⟩ := hBmem b hb
    exact Finset.mem_Ioo.2 ⟨h1, by omega⟩
  -- Lemma 11 (i): `|π(A)| ≥ |B|`
  have hproj : #B ≤ #(projImage ((M - m).toNat) A) :=
    card_le_card_projImage_Ioo ht hBA hBIoo
  have hprojR : (#B : ℝ) ≤ (#(projImage ((M - m).toNat) A) : ℝ) := by exact_mod_cast hproj
  -- numerical facts about `ε`
  have hsqrtpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hx0 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt ε)) := Real.sqrt_nonneg _
  have hn1 : (1 / 10 ^ 12 : ℝ) * (1 / 10 ^ 12) = 1 / 10 ^ 24 := by norm_num
  have hn2 : (1 / 10 ^ 6 : ℝ) * (1 / 10 ^ 6) = 1 / 10 ^ 12 := by norm_num
  have hn3 : (1 / 1000 : ℝ) * (1 / 1000) = 1 / 10 ^ 6 := by norm_num
  have hsq1 : Real.sqrt ε ≤ 1 / 10 ^ 12 :=
    sqrt_le_of_le_mul_self' (by norm_num) (by rw [hn1]; exact hε0)
  have hsq2 : Real.sqrt (Real.sqrt ε) ≤ 1 / 10 ^ 6 :=
    sqrt_le_of_le_mul_self' (by norm_num) (by rw [hn2]; exact hsq1)
  have hxle : Real.sqrt (Real.sqrt (Real.sqrt ε)) ≤ 1 / 1000 :=
    sqrt_le_of_le_mul_self' (by norm_num) (by rw [hn3]; exact hsq2)
  have hpow : Real.sqrt ε
      = Real.sqrt (Real.sqrt (Real.sqrt ε)) * Real.sqrt (Real.sqrt (Real.sqrt ε)) *
        (Real.sqrt (Real.sqrt (Real.sqrt ε)) * Real.sqrt (Real.sqrt (Real.sqrt ε))) := by
    rw [Real.mul_self_sqrt (Real.sqrt_nonneg (Real.sqrt ε)),
      Real.mul_self_sqrt (Real.sqrt_nonneg ε)]
  have hslack : 2 * Real.sqrt ε * (N : ℝ) + 1
      ≤ 10 * (Real.sqrt (Real.sqrt (Real.sqrt ε)) * (N : ℝ)) :=
    slack_bound hx0 hxle hN hpow
  -- Green (15)
  have h15 : #(popularDiff (projImage ((M - m).toNat) A)
        (8 * Real.sqrt ε * (N : ℝ))) + #B
      ≤ #(popularDiff A (Real.sqrt ε * (N : ℝ))) :=
    card_add_card_le_card_popularDiff hA ht htN hsqrtpos htZ.symm hBmem
  have h15R : (#(popularDiff (projImage ((M - m).toNat) A)
        (8 * Real.sqrt ε * (N : ℝ))) : ℝ) + (#B : ℝ)
      ≤ (#(popularDiff A (Real.sqrt ε * (N : ℝ))) : ℝ) := by exact_mod_cast h15
  -- Lemma 8
  have h8 := lem8_card_popularDiff_le hA hε htr
  refine ⟨m, M, hm, hM, hmM, hgap, hleft, hright, by linarith, by linarith⟩

end Ineq16

/-! ## Axiom audit -/

#print axioms CameronErdos.popularDiff_subset_of_le
#print axioms CameronErdos.sqrt_le_of_le_mul_self'
#print axioms CameronErdos.slack_bound
#print axioms CameronErdos.card_add_card_le_card_popularDiff
#print axioms CameronErdos.lem16

end CameronErdos

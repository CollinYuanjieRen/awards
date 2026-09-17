import Erdos193Walk.Chords

/-! No three points of the walk are collinear (over `ℚ`). -/

namespace Erdos193Walk

open Zsqrtd Set

/-- The points of the walk, cast to `ℚ³`. -/
def Pq (n : ℕ) : Fin 3 → ℚ := (↑) ∘ P n

/-! ### `2`-adic helpers -/

/-- `2 ^ (v₂ A + 1)` does not divide a nonzero integer `A`. -/
private theorem two_pow_succ_not_dvd {A : ℤ} (hA : A ≠ 0) :
    ¬ ((2 : ℤ) ^ (padicValInt 2 A + 1) ∣ A) := by
  intro hdvd
  have h2 : ((2 : ℕ) : ℤ) ^ (padicValInt 2 A + 1) ∣ A := by exact_mod_cast hdvd
  rcases (padicValInt_dvd_iff (p := 2) _ A).1 h2 with h | h
  · exact hA h
  · omega

/-- A nonzero integer factors as `2 ^ v₂ A` times an odd integer. -/
private theorem exists_odd_factor {A : ℤ} (hA : A ≠ 0) :
    ∃ a', A = 2 ^ padicValInt 2 A * a' ∧ ¬ ((2 : ℤ) ∣ a') := by
  obtain ⟨a', ha'⟩ : (2 : ℤ) ^ padicValInt 2 A ∣ A := by
    have hd := padicValInt_dvd (p := 2) A
    exact_mod_cast hd
  refine ⟨a', ha', ?_⟩
  rintro ⟨m, rfl⟩
  refine two_pow_succ_not_dvd hA ⟨m, ?_⟩
  conv_lhs => rw [ha']
  ring

/-- If `A`, `B` and `C = A + B` are nonzero and all have the same `2`-adic valuation, we get a
contradiction: `A` and `B` would be `2 ^ t` times odd numbers, so `A + B` is divisible by
`2 ^ (t + 1)`. -/
private theorem padicValInt_two_add_contra {A B C : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsum : C = A + B) (h1 : padicValInt 2 B = padicValInt 2 A)
    (h2 : padicValInt 2 C = padicValInt 2 A) : False := by
  obtain ⟨a', ha', hao⟩ := exists_odd_factor hA
  obtain ⟨b', hb', hbo⟩ := exists_odd_factor hB
  rw [h1] at hb'
  obtain ⟨m, hm⟩ : (2 : ℤ) ∣ a' + b' := by omega
  refine two_pow_succ_not_dvd hC ⟨m, ?_⟩
  rw [h2, hsum]
  calc A + B = 2 ^ padicValInt 2 A * (a' + b') := by rw [mul_add, ← ha', ← hb']
    _ = 2 ^ (padicValInt 2 A + 1) * m := by rw [hm]; ring

/-! ### The main argument -/

/-- Three points of the walk with increasing indices are never collinear. -/
theorem not_collinear (a b d : ℕ) (hab : a < b) (hbd : b < d) :
    ¬ Collinear ℚ ({Pq a, Pq b, Pq d} : Set (Fin 3 → ℚ)) := by
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨r₁, hr₁⟩ := hv (Pq b) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r₂, hr₂⟩ := hv (Pq d) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  -- coordinates of `P`
  have hP0 : ∀ n : ℕ, P n 0 = (w n).re := fun n => rfl
  have hP1 : ∀ n : ℕ, P n 1 = (w n).im := fun n => rfl
  have hP2 : ∀ n : ℕ, P n 2 = h n := fun n => rfl
  have key : ∀ (m : ℕ) (r : ℚ), Pq m = r • v +ᵥ Pq a → ∀ i : Fin 3,
      ((P m i : ℤ) : ℚ) = r * v i + ((P a i : ℤ) : ℚ) := by
    intro m r hm i
    have hci := congrFun hm i
    simpa [Pq, Function.comp_apply] using hci
  have hb2 : ((h b : ℤ) : ℚ) = r₁ * v 2 + ((h a : ℤ) : ℚ) := by
    have hk := key b r₁ hr₁ 2; rwa [hP2, hP2] at hk
  have hd2 : ((h d : ℤ) : ℚ) = r₂ * v 2 + ((h a : ℤ) : ℚ) := by
    have hk := key d r₂ hr₂ 2; rwa [hP2, hP2] at hk
  -- the basic cross-multiplication identity, coordinatewise over ℤ
  have main : ∀ i : Fin 3, (h d - h a) * (P b i - P a i) = (h b - h a) * (P d i - P a i) := by
    intro i
    have hbi := key b r₁ hr₁ i
    have hdi := key d r₂ hr₂ i
    have hq : ((h d - h a : ℤ) : ℚ) * ((P b i - P a i : ℤ) : ℚ)
        = ((h b - h a : ℤ) : ℚ) * ((P d i - P a i : ℤ) : ℚ) := by
      push_cast
      rw [hbi, hdi, hb2, hd2]
      ring
    exact_mod_cast hq
  have e0 : (h d - h a) * ((w b).re - (w a).re) = (h b - h a) * ((w d).re - (w a).re) := by
    have hm := main 0; rwa [hP0, hP0, hP0] at hm
  have e1 : (h d - h a) * ((w b).im - (w a).im) = (h b - h a) * ((w d).im - (w a).im) := by
    have hm := main 1; rwa [hP1, hP1, hP1] at hm
  -- lift to the Gaussian integers
  have g1 : ((h d - h a : ℤ) : G) * (w b - w a) = ((h b - h a : ℤ) : G) * (w d - w a) := by
    ext
    · simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_sub,
        Zsqrtd.im_sub]
      linear_combination e0
    · simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_sub,
        Zsqrtd.im_sub]
      linear_combination e1
  have g2 : ((h d - h b : ℤ) : G) * (w b - w a) = ((h b - h a : ℤ) : G) * (w d - w b) := by
    ext
    · simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_sub,
        Zsqrtd.im_sub]
      linear_combination e0
    · simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_sub,
        Zsqrtd.im_sub]
      linear_combination e1
  -- take norms
  have n1 := congrArg Zsqrtd.norm g1
  have n2 := congrArg Zsqrtd.norm g2
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul, Zsqrtd.norm_intCast, Zsqrtd.norm_intCast] at n1 n2
  -- the 2-adic input from Chords.lean
  obtain ⟨hNX, hvX⟩ := norm_w_sub a b hab
  obtain ⟨hNY, hvY⟩ := norm_w_sub b d hbd
  obtain ⟨hNZ, hvZ⟩ := norm_w_sub a d (hab.trans hbd)
  have hA : h b - h a ≠ 0 := sub_ne_zero.2 (h_strictMono hab).ne'
  have hB : h d - h b ≠ 0 := sub_ne_zero.2 (h_strictMono hbd).ne'
  have hC : h d - h a ≠ 0 := sub_ne_zero.2 (h_strictMono (hab.trans hbd)).ne'
  have v1 := congrArg (padicValInt 2) n1
  rw [padicValInt.mul (mul_ne_zero hC hC) hNX, padicValInt.mul hC hC,
      padicValInt.mul (mul_ne_zero hA hA) hNZ, padicValInt.mul hA hA, hvX, hvZ] at v1
  have v2 := congrArg (padicValInt 2) n2
  rw [padicValInt.mul (mul_ne_zero hB hB) hNX, padicValInt.mul hB hB,
      padicValInt.mul (mul_ne_zero hA hA) hNY, padicValInt.mul hA hA, hvX, hvY] at v2
  exact padicValInt_two_add_contra hA hB hC (by ring) (by omega) (by omega)

/-- No three distinct points of the walk are collinear. -/
theorem no_collinear_triple :
    ¬ ∃ x ∈ range (fun n ↦ (↑) ∘ P n : ℕ → Fin 3 → ℚ),
      ∃ y ∈ range (fun n ↦ (↑) ∘ P n : ℕ → Fin 3 → ℚ),
      ∃ zz ∈ range (fun n ↦ (↑) ∘ P n : ℕ → Fin 3 → ℚ),
      x ≠ y ∧ y ≠ zz ∧ x ≠ zz ∧ Collinear ℚ ({x, y, zz} : Set (Fin 3 → ℚ)) := by
  rintro ⟨-, ⟨i, rfl⟩, -, ⟨j, rfl⟩, -, ⟨k, rfl⟩, hxy, hyz, hxz, hcol⟩
  have hij : i ≠ j := fun hh => hxy (by rw [hh])
  have hjk : j ≠ k := fun hh => hyz (by rw [hh])
  have hik : i ≠ k := fun hh => hxz (by rw [hh])
  have hcol' : Collinear ℚ ({Pq i, Pq j, Pq k} : Set (Fin 3 → ℚ)) := hcol
  have gen : ∀ p q r : ℕ, p < q → q < r →
      ({Pq p, Pq q, Pq r} : Set (Fin 3 → ℚ)) ⊆ {Pq i, Pq j, Pq k} → False :=
    fun p q r h1 h2 hs => not_collinear p q r h1 h2 (hcol'.subset hs)
  rcases lt_trichotomy i j with h1 | h1 | h1
  · rcases lt_trichotomy j k with h2 | h2 | h2
    · exact gen i j k h1 h2
        (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    · exact absurd h2 hjk
    · rcases lt_trichotomy i k with h3 | h3 | h3
      · exact gen i k j h3 h2
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
      · exact absurd h3 hik
      · exact gen k i j h3 h1
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  · exact absurd h1 hij
  · rcases lt_trichotomy i k with h2 | h2 | h2
    · exact gen j i k h1 h2
        (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    · exact absurd h2 hik
    · rcases lt_trichotomy j k with h3 | h3 | h3
      · exact gen j k i h3 h2
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
      · exact absurd h3 hjk
      · exact gen k j i h3 h1
          (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)

end Erdos193Walk

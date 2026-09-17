import Erdos193Walk.Walk

/-! Identity (4) of the paper for the tagged walk `w`, the step bound (5), and injectivity. -/

namespace Erdos193Walk

open Zsqrtd

theorem h_strictMono : StrictMono h := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  have h1 := α_lt_four (n + 1)
  have h2 := α_lt_four n
  simp only [h]
  push_cast
  omega

theorem P_injective : Function.Injective P := by
  intro m n hmn
  have h2 : h m = h n := by simpa [P] using congrFun hmn 2
  exact h_strictMono.injective h2

/-- The displacement `P (n+1) - P n` is one of the sixteen steps. -/
theorem P_succ_sub_mem (n : ℕ) : P (n + 1) - P n ∈ stepSet := by
  refine ⟨(⟨α n, α_lt_four n⟩, ⟨α (n + 1), α_lt_four (n + 1)⟩), ?_⟩
  have hw : (2 * I ^ (α n) + c (α (n + 1)) - c (α n)) = w (n + 1) - w n := by
    simp only [w, z_succ, u]; ring
  simp only [step]
  rw [hw]
  funext i
  fin_cases i <;> simp [P, h, Zsqrtd.re_sub, Zsqrtd.im_sub]
  ring

/-! ### Arithmetic helpers -/

/-- The norm on the Gaussian integers is the sum of the squares of the coordinates. -/
private lemma chords_norm_eq (x : G) : norm x = x.re * x.re + x.im * x.im := by
  rw [Zsqrtd.norm_def]; ring

private lemma chords_odd_two_mul_add_one (k : ℤ) : Odd (2 * k + 1) := by
  rw [Int.odd_iff]; omega

private lemma chords_pv2_pow (t : ℕ) : padicValInt 2 ((2 : ℤ) ^ t) = t := by
  have h : ((2 : ℤ) ^ t) = ((2 ^ t : ℕ) : ℤ) := by push_cast; ring
  rw [h, padicValInt.of_nat, padicValNat.prime_pow]

/-- If `N = 2 ^ t * o` with `o` odd, then `N ≠ 0` and `v₂ N = t`. -/
private lemma chords_pv2 {N : ℤ} {t : ℕ} {o : ℤ} (ho : Odd o) (hN : N = 2 ^ t * o) :
    N ≠ 0 ∧ padicValInt 2 N = t := by
  have ho2 : o % 2 = 1 := Int.odd_iff.mp ho
  have ho0 : o ≠ 0 := by intro hh; rw [hh] at ho2; norm_num at ho2
  have hp : ((2 : ℤ) ^ t) ≠ 0 := by positivity
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ o := by
    intro hd
    rw [Int.dvd_iff_emod_eq_zero] at hd
    norm_num at hd
    omega
  refine ⟨by rw [hN]; exact mul_ne_zero hp ho0, ?_⟩
  rw [hN, padicValInt.mul hp ho0, chords_pv2_pow, padicValInt.eq_zero_of_not_dvd hnd]
  omega

private lemma chords_pv4 (N : ℤ) (hN : N ≠ 0) : padicValInt 2 (4 * N) = 2 + padicValInt 2 N := by
  have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
  rw [h4, padicValInt.mul (by norm_num) hN, chords_pv2_pow]

private lemma chords_pv2_of_odd {N : ℤ} (h : Odd N) : N ≠ 0 ∧ padicValInt 2 N = 0 :=
  chords_pv2 h (by rw [pow_zero, one_mul])

private lemma chords_sq_odd_even {x y : ℤ} (hx : Odd x) (hy : Even y) : Odd (x * x + y * y) := by
  obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by have := Int.odd_iff.mp hx; omega⟩
  obtain ⟨l, hl⟩ : ∃ l, y = 2 * l := ⟨y / 2, by have := Int.even_iff.mp hy; omega⟩
  have hxy : x * x + y * y = 2 * (2 * k * k + 2 * k + 2 * l * l) + 1 := by rw [hk, hl]; ring
  rw [hxy]; exact chords_odd_two_mul_add_one _

private lemma chords_sq_odd_odd {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    ∃ o : ℤ, Odd o ∧ x * x + y * y = 2 ^ 1 * o := by
  obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by have := Int.odd_iff.mp hx; omega⟩
  obtain ⟨l, hl⟩ : ∃ l, y = 2 * l + 1 := ⟨y / 2, by have := Int.odd_iff.mp hy; omega⟩
  exact ⟨2 * (k * k + k + l * l + l) + 1, chords_odd_two_mul_add_one _, by rw [hk, hl]; ring⟩

/-- The parities of the corner differences: for `a ≠ b` in `{0, 1, 2, 3}` either `c b - c a` has
exactly one odd coordinate and `b - a` is odd, or both coordinates are odd and `b - a = ±2`. -/
private lemma chords_c_key (a b : ℕ) (ha : a < 4) (hb : b < 4) (hne : a ≠ b) :
    (Odd ((c b).re - (c a).re) ∧ Even ((c b).im - (c a).im) ∧ Odd ((b : ℤ) - (a : ℤ))) ∨
    (Even ((c b).re - (c a).re) ∧ Odd ((c b).im - (c a).im) ∧ Odd ((b : ℤ) - (a : ℤ))) ∨
    (Odd ((c b).re - (c a).re) ∧ Odd ((c b).im - (c a).im) ∧
      ((b : ℤ) - (a : ℤ) = 2 ∨ (b : ℤ) - (a : ℤ) = -2)) := by
  interval_cases a <;> interval_cases b <;>
    simp_all [c, I, Int.odd_iff, Int.even_iff]

/-! ### Identity (4) -/

/-- Identity (4) of the paper: for `m < n`, `|w n - w m|²` is nonzero and its 2-adic valuation
equals that of `h n - h m > 0`. -/
theorem norm_w_sub (m n : ℕ) (hmn : m < n) :
    norm (w n - w m) ≠ 0 ∧ padicValInt 2 (norm (w n - w m)) = padicValInt 2 (h n - h m) := by
  obtain ⟨D, hD, hD0⟩ : ∃ D : ℕ, (n : ℤ) = (m : ℤ) + (D : ℤ) ∧ 0 < D :=
    ⟨n - m, by omega, by omega⟩
  have hH : h n - h m = 4 * (D : ℤ) + ((α n : ℤ) - (α m : ℤ)) := by
    simp only [h]; rw [hD]; ring
  have hW : w n - w m = 2 * (z n - z m) + (c (α n) - c (α m)) := by
    simp only [w]; ring
  by_cases hab : α m = α n
  · -- equal tags: reduce to identity (2) for `z`
    have hu : u m = u n := by simp only [u, hab]
    obtain ⟨hNz, hvz⟩ := norm_z_sub m n hmn hu
    have hW2 : w n - w m = 2 * (z n - z m) := by rw [hW, hab]; ring
    have h2 : norm (2 : G) = 4 := by decide
    have hnorm : norm (w n - w m) = 4 * norm (z n - z m) := by
      rw [hW2, Zsqrtd.norm_mul, h2]
    have hH2 : h n - h m = 4 * (D : ℤ) := by rw [hH, hab]; ring
    have hDne : ((D : ℤ)) ≠ 0 := by exact_mod_cast hD0.ne'
    have hnm : n - m = D := by omega
    refine ⟨by rw [hnorm]; exact mul_ne_zero (by norm_num) hNz, ?_⟩
    rw [hnorm, hH2, chords_pv4 _ hNz, chords_pv4 _ hDne, hvz, hnm, padicValInt.of_nat]
  · -- different tags: the corner difference decides the parity
    obtain ⟨a, ha⟩ : ∃ a, α m = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, α n = b := ⟨_, rfl⟩
    have ha4 : a < 4 := ha ▸ α_lt_four m
    have hb4 : b < 4 := hb ▸ α_lt_four n
    have hne : a ≠ b := fun hh => hab (by rw [ha, hb, hh])
    rw [ha, hb] at hW hH
    have hre : (w n - w m).re = 2 * (z n - z m).re + ((c b).re - (c a).re) := by
      rw [hW]; simp
    have him : (w n - w m).im = 2 * (z n - z m).im + ((c b).im - (c a).im) := by
      rw [hW]; simp
    rcases chords_c_key a b ha4 hb4 hne with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · -- one odd coordinate: the norm and the height difference are both odd
      have hro : Odd ((w n - w m).re) := by
        rw [hre, Int.odd_iff]; rw [Int.odd_iff] at h1; omega
      have hie : Even ((w n - w m).im) := by
        rw [him, Int.even_iff]; rw [Int.even_iff] at h2; omega
      have hN : Odd (norm (w n - w m)) := by
        rw [chords_norm_eq]; exact chords_sq_odd_even hro hie
      have hHo : Odd (h n - h m) := by
        rw [hH, Int.odd_iff]; rw [Int.odd_iff] at h3; omega
      obtain ⟨hn1, hn2⟩ := chords_pv2_of_odd hN
      obtain ⟨-, hh2⟩ := chords_pv2_of_odd hHo
      exact ⟨hn1, by rw [hn2, hh2]⟩
    · have hre' : Even ((w n - w m).re) := by
        rw [hre, Int.even_iff]; rw [Int.even_iff] at h1; omega
      have hio : Odd ((w n - w m).im) := by
        rw [him, Int.odd_iff]; rw [Int.odd_iff] at h2; omega
      have hN : Odd (norm (w n - w m)) := by
        rw [chords_norm_eq, add_comm]; exact chords_sq_odd_even hio hre'
      have hHo : Odd (h n - h m) := by
        rw [hH, Int.odd_iff]; rw [Int.odd_iff] at h3; omega
      obtain ⟨hn1, hn2⟩ := chords_pv2_of_odd hN
      obtain ⟨-, hh2⟩ := chords_pv2_of_odd hHo
      exact ⟨hn1, by rw [hn2, hh2]⟩
    · -- both coordinates odd: the norm is twice an odd number, and so is the height difference
      have hro : Odd ((w n - w m).re) := by
        rw [hre, Int.odd_iff]; rw [Int.odd_iff] at h1; omega
      have hio : Odd ((w n - w m).im) := by
        rw [him, Int.odd_iff]; rw [Int.odd_iff] at h2; omega
      obtain ⟨o, hoo, ho⟩ := chords_sq_odd_odd hro hio
      have hNfac : norm (w n - w m) = 2 ^ 1 * o := by rw [chords_norm_eq]; exact ho
      obtain ⟨hn1, hn2⟩ := chords_pv2 hoo hNfac
      have hHfac : ∃ o' : ℤ, Odd o' ∧ h n - h m = 2 ^ 1 * o' := by
        rcases h3 with h3 | h3
        · exact ⟨2 * (D : ℤ) + 1, chords_odd_two_mul_add_one _, by rw [hH, h3]; ring⟩
        · exact ⟨2 * (D : ℤ) - 1, by rw [Int.odd_iff]; omega, by rw [hH, h3]; ring⟩
      obtain ⟨o', ho', hfac'⟩ := hHfac
      obtain ⟨-, hh2⟩ := chords_pv2 ho' hfac'
      exact ⟨hn1, by rw [hn2, hh2]⟩

end Erdos193Walk

import Mathlib
import JSP573.FF.Basic

/-!
# Frankl–Füredi 1984: arithmetic and polynomial lemmas for the Frankl–Singhi rank theorem

Three independent leaves used in the proof of Theorem 1.4 (appendix of the paper):

1. a binomial divisibility fact from Kummer's theorem: if `p ^ s ∣ k + 1` and `1 ≤ d < p ^ s`
   then `p ∣ C(k + d, k)`;
2. the Newton-series expansion of the degree-`(h - t - 1)` polynomial
   `ffPoly h t x = ∏_{t < i < h} (i - x) / (h - t - 1)!` in the basis
   `C(x, s) · C(h - s, h - t - 1 - s)`, `0 ≤ s ≤ h - t - 1`, together with its values;
3. clearing denominators and powers of `p` from a nonzero rational coefficient vector.
-/

open Finset

namespace FranklFuredi

/-- Kummer: if `p ^ s ∣ k + 1` and `1 ≤ d < p ^ s` then adding `d` to `k` carries in base `p`,
so `p ∣ C(k + d, k)`. -/
theorem prime_dvd_choose_of_pow_dvd_succ (p s k d : ℕ) (hp : p.Prime) (hs : 0 < s)
    (hk : p ^ s ∣ k + 1) (hd1 : 1 ≤ d) (hd : d < p ^ s) : p ∣ (k + d).choose k := by
  have hp2 : 2 ≤ p := hp.two_le
  have hps : 0 < p ^ s := Nat.pow_pos (by omega)
  have hle : p ^ s ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hk
  have hkd : p ^ s ≤ k + d := by omega
  obtain ⟨m, hm⟩ := hk
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hkeq : k = (p ^ s - 1) + p ^ s * (m - 1) := by
    have h1 : p ^ s * m = p ^ s * (m - 1) + p ^ s := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    omega
  have hkmod : k % p ^ s = p ^ s - 1 := by
    rw [hkeq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdmod : d % p ^ s = d := Nat.mod_eq_of_lt hd
  have hsb : s < Nat.log p (k + d) + 1 := by
    have : s ≤ Nat.log p (k + d) := (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hkd
    omega
  have hmem : s ∈ {i ∈ Finset.Ico 1 (Nat.log p (k + d) + 1) |
      p ^ i ≤ k % p ^ i + (k + d - k) % p ^ i} := by
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.add_sub_cancel_left]
    exact ⟨⟨hs, hsb⟩, by rw [hkmod, hdmod]; omega⟩
  refine dvd_of_emultiplicity_pos ?_
  rw [hp.emultiplicity_choose (Nat.le_add_right k d) (Nat.lt_succ_self _)]
  exact_mod_cast Finset.card_pos.mpr ⟨s, hmem⟩

/-- The paper's polynomial `p(x) = ∏_{t < i < h} (i - x) / (h - t - 1)!`, as a function on `ℕ`
with rational values. -/
noncomputable def ffPoly (h t : ℕ) (x : ℕ) : ℚ :=
  (∏ i ∈ Finset.Ico (t + 1) h, ((i : ℚ) - x)) / ((h - t - 1).factorial : ℚ)

/-- For `t < x < h` the product contains the factor `x - x`. -/
theorem ffPoly_eq_zero (h t x : ℕ) (hx₁ : t < x) (hx₂ : x < h) : ffPoly h t x = 0 := by
  rw [ffPoly, Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨hx₁, hx₂⟩) (sub_self _), zero_div]

/-- For `x ≤ t < h` the defining product is a falling factorial. -/
private lemma prod_Ico_sub_eq_descFactorial (t x : ℕ) (hx : x ≤ t) (h : ℕ) (ht : t < h) :
    ∏ i ∈ Finset.Ico (t + 1) h, ((i : ℚ) - x) = ((h - 1 - x).descFactorial (h - t - 1) : ℚ) := by
  induction h, ht using Nat.le_induction with
  | base => simp
  | succ h ht ih =>
    rw [Finset.prod_Ico_succ_top (by omega), ih]
    have e1 : h + 1 - 1 - x = h - 1 - x + 1 := by omega
    have e2 : h + 1 - t - 1 = h - t - 1 + 1 := by omega
    have e3 : ((h - 1 - x : ℕ) : ℚ) + 1 = (h : ℚ) - x := by
      have h1 : ((h - 1 - x : ℕ) : ℚ) = (h : ℚ) - x - 1 := by
        rw [Nat.cast_sub (by omega : x ≤ h - 1), Nat.cast_sub (by omega : 1 ≤ h)]
        push_cast
        ring
      rw [h1]; ring
    rw [e1, e2, Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, e3]
    ring

/-- For `x ≤ t` the value is the binomial coefficient `C(h - 1 - x, h - t - 1)`. -/
theorem ffPoly_eq_choose (h t x : ℕ) (ht : t < h) (hx : x ≤ t) :
    ffPoly h t x = ((h - 1 - x).choose (h - t - 1) : ℚ) := by
  have hfac : ((h - t - 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (h - t - 1)).ne'
  rw [ffPoly, prod_Ico_sub_eq_descFactorial t x hx h ht, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, mul_comm, mul_div_assoc, div_self hfac, mul_one]

/-- At `x = h` the value is `(-1) ^ (h - t - 1)`. -/
theorem ffPoly_at_top (h t : ℕ) (ht : t < h) : ffPoly h t h = (-1 : ℚ) ^ (h - t - 1) := by
  have hfac : ((h - t - 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (h - t - 1)).ne'
  have hcast : (h : ℚ) = (t : ℚ) + 1 + ((h - t - 1 : ℕ) : ℚ) := by
    have h1 : ((h - t - 1 : ℕ) : ℚ) = (h : ℚ) - t - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ h - t), Nat.cast_sub (by omega : t ≤ h)]
      push_cast
      ring
    rw [h1]; ring
  have key : ∏ i ∈ Finset.Ico (t + 1) h, ((i : ℚ) - h)
      = (-1 : ℚ) ^ (h - t - 1) * ((h - t - 1).factorial : ℚ) := by
    rw [Finset.prod_Ico_eq_prod_range]
    have hn : h - (t + 1) = h - t - 1 := by omega
    rw [hn]
    have step : ∀ j ∈ Finset.range (h - t - 1),
        ((t + 1 + j : ℕ) : ℚ) - (h : ℚ) = -1 * (((h - t - 1 - j : ℕ)) : ℚ) := by
      intro j hj
      have hjN : j < h - t - 1 := Finset.mem_range.mp hj
      rw [Nat.cast_sub hjN.le, hcast]
      push_cast
      ring
    rw [Finset.prod_congr rfl step, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    congr 1
    rw [← Nat.cast_prod]
    congr 1
    have hrefl := Finset.prod_range_reflect (fun j ↦ j + 1) (h - t - 1)
    rw [Finset.prod_range_add_one_eq_factorial] at hrefl
    rw [← hrefl]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have : j < h - t - 1 := Finset.mem_range.mp hj
    omega
  rw [ffPoly, key, mul_div_assoc, div_self hfac, mul_one]

/-- Iterated forward differences commute with restriction of a function on `ℚ` to `ℕ`. -/
private lemma fwdDiff_iter_natCast (k : ℕ) (F : ℚ → ℚ) (n : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (fun m : ℕ ↦ F (m : ℚ)) n = (fwdDiff (1 : ℚ))^[k] F (n : ℚ) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hstep : (fwdDiff (1 : ℕ) fun m : ℕ ↦ F (m : ℚ))
        = fun m : ℕ ↦ (fwdDiff (1 : ℚ) F) (m : ℚ) := by
      funext m
      simp only [fwdDiff]
      push_cast
      ring_nf
    rw [hstep, ih]

/-- Iterated forward differences of the zero function vanish. -/
private lemma fwdDiff_iter_zero_fun (j : ℕ) : (fwdDiff (1 : ℚ))^[j] (0 : ℚ → ℚ) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    simp [fwdDiff]

/-- Newton expansion: `ffPoly h t` is a polynomial of degree `h - t - 1` in `x`, so it is a
combination of `C(x, s) · C(h - s, h - t - 1 - s)`, `s ≤ h - t - 1` (the factors
`C(h - s, h - t - 1 - s)` are positive constants; the expansion coefficients are the forward
differences at `0`, see `shift_eq_sum_fwdDiff_iter` and
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`). -/
theorem exists_ffPoly_expansion (h t : ℕ) (ht : t < h) :
    ∃ α : ℕ → ℚ, ∀ x : ℕ, ffPoly h t x =
      ∑ s ∈ Finset.range (h - t), α s * (x.choose s : ℚ) * ((h - s).choose (h - t - 1 - s) : ℚ) := by
  classical
  set N := h - t - 1 with hN
  have hNt : h - t = N + 1 := by omega
  have hfac : ((N).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos N).ne'
  set P : Polynomial ℚ := Polynomial.C (((N).factorial : ℚ))⁻¹ *
    ∏ i ∈ Finset.Ico (t + 1) h, (Polynomial.C (i : ℚ) - Polynomial.X) with hP
  have hPeval : ∀ m : ℕ, P.eval (m : ℚ) = ffPoly h t m := by
    intro m
    rw [hP, ffPoly]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X]
    rw [div_eq_inv_mul]
  have hdeg : P.natDegree < N + 1 := by
    have h1 : (∏ i ∈ Finset.Ico (t + 1) h,
        (Polynomial.C (i : ℚ) - Polynomial.X)).natDegree ≤
        ∑ _i ∈ Finset.Ico (t + 1) h, 1 := by
      refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    have h2 : P.natDegree ≤ ∑ _i ∈ Finset.Ico (t + 1) h, 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans h1
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at h2
    omega
  have hzero : ∀ k, N + 1 ≤ k → (fwdDiff (1 : ℚ))^[k] (fun x ↦ P.eval x) = 0 := by
    intro k hk
    obtain ⟨j, hj⟩ : ∃ j, k = j + (N + 1) := ⟨k - (N + 1), by omega⟩
    rw [hj, Function.iterate_add_apply, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg,
      fwdDiff_iter_zero_fun]
  set β : ℕ → ℚ := fun k ↦ (fwdDiff (1 : ℕ))^[k] (ffPoly h t) 0 with hβ
  have hβzero : ∀ k, N + 1 ≤ k → β k = 0 := by
    intro k hk
    have hff : (fun m : ℕ ↦ P.eval (m : ℚ)) = ffPoly h t := funext hPeval
    have hval : β k = (fwdDiff (1 : ℚ))^[k] (fun x ↦ P.eval x) ((0 : ℕ) : ℚ) := by
      rw [hβ, ← hff]
      exact fwdDiff_iter_natCast k (fun x ↦ P.eval x) 0
    rw [hval, hzero k hk]
    rfl
  have newton : ∀ x : ℕ, ffPoly h t x = ∑ k ∈ Finset.range (x + 1), (x.choose k : ℚ) * β k := by
    intro x
    have := shift_eq_sum_fwdDiff_iter (1 : ℕ) (ffPoly h t) x 0
    simpa [hβ, nsmul_eq_mul] using this
  refine ⟨fun s ↦ β s / ((h - s).choose (h - t - 1 - s) : ℚ), fun x ↦ ?_⟩
  set M := max (x + 1) (N + 1) with hM
  have hsub1 : Finset.range (x + 1) ⊆ Finset.range M :=
    Finset.range_mono (le_max_left _ _)
  have hsub2 : Finset.range (N + 1) ⊆ Finset.range M :=
    Finset.range_mono (le_max_right _ _)
  have hL : ∑ k ∈ Finset.range (x + 1), (x.choose k : ℚ) * β k
      = ∑ k ∈ Finset.range M, (x.choose k : ℚ) * β k := by
    refine Finset.sum_subset hsub1 fun k _ hk ↦ ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
    simp
  have hterm : ∀ s ∈ Finset.range (h - t),
      (β s / ((h - s).choose (h - t - 1 - s) : ℚ)) * (x.choose s : ℚ) *
        ((h - s).choose (h - t - 1 - s) : ℚ) = (x.choose s : ℚ) * β s := by
    intro s hs
    have hs' : s < h - t := Finset.mem_range.mp hs
    have hpos : 0 < (h - s).choose (h - t - 1 - s) := Nat.choose_pos (by omega)
    have hne : ((h - s).choose (h - t - 1 - s) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hne]
    ring
  have hR : ∑ s ∈ Finset.range (h - t),
      (β s / ((h - s).choose (h - t - 1 - s) : ℚ)) * (x.choose s : ℚ) *
        ((h - s).choose (h - t - 1 - s) : ℚ)
      = ∑ k ∈ Finset.range M, (x.choose k : ℚ) * β k := by
    rw [Finset.sum_congr rfl hterm, show h - t = N + 1 from hNt]
    refine Finset.sum_subset hsub2 fun k _ hk ↦ ?_
    rw [hβzero k (by simpa using hk), mul_zero]
  rw [newton x, hL, ← hR]

/-- Divide a nonzero integer vector by the largest power of the prime `p` dividing all entries. -/
private lemma exists_pow_factor {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime) :
    ∀ (n : ℕ) (e : ι → ℤ), e ≠ 0 → ∑ i, (e i).natAbs ≤ n →
      ∃ (f : ι → ℤ) (k : ℕ), (∀ i, e i = (p : ℤ) ^ k * f i) ∧ ∃ i, ¬ (p : ℤ) ∣ f i := by
  intro n
  induction n with
  | zero =>
    intro e he hsum
    exact absurd (funext fun i ↦ by
      have h1 : (e i).natAbs ≤ ∑ j, (e j).natAbs :=
        Finset.single_le_sum (f := fun j ↦ (e j).natAbs) (fun j _ ↦ Nat.zero_le _)
          (Finset.mem_univ i)
      have h2 : (e i).natAbs = 0 := by omega
      simpa [Int.natAbs_eq_zero] using h2) he
  | succ n ih =>
    intro e he hsum
    by_cases hex : ∀ i, (p : ℤ) ∣ e i
    · have hef : ∀ i, e i = (p : ℤ) * (e i / (p : ℤ)) := fun i ↦ (Int.mul_ediv_cancel' (hex i)).symm
      have hfne : (fun i ↦ e i / (p : ℤ)) ≠ 0 := by
        intro h0
        exact he (funext fun i ↦ by rw [hef i, congrFun h0 i]; simp)
      have hnat : ∀ i, (e i).natAbs = p * (e i / (p : ℤ)).natAbs := by
        intro i
        conv_lhs => rw [hef i]
        simp [Int.natAbs_mul]
      have hsum' : ∑ i, (e i / (p : ℤ)).natAbs ≤ n := by
        have h1 : ∑ i, (e i).natAbs = p * ∑ i, (e i / (p : ℤ)).natAbs := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ hnat i
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hfne
        have h2 : 0 < ∑ j, (e j / (p : ℤ)).natAbs :=
          lt_of_lt_of_le (Int.natAbs_pos.mpr hi)
            (Finset.single_le_sum (f := fun j ↦ (e j / (p : ℤ)).natAbs)
              (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i))
        have h3 : 2 * ∑ j, (e j / (p : ℤ)).natAbs ≤ p * ∑ j, (e j / (p : ℤ)).natAbs :=
          Nat.mul_le_mul_right _ hp.two_le
        omega
      obtain ⟨g, k, hg, hgi⟩ := ih (fun i ↦ e i / (p : ℤ)) hfne hsum'
      exact ⟨g, k + 1, fun i ↦ by rw [hef i, hg i]; ring, hgi⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hex
      exact ⟨e, 0, by simp, ⟨i, hi⟩⟩

/-- A nonzero rational vector can be rescaled to an integer vector, not all of whose entries are
divisible by the prime `p`, by clearing denominators and then dividing out powers of `p`. -/
theorem exists_int_rescale_not_all_dvd {ι : Type*} [Fintype ι] (p : ℕ) (hp : p.Prime)
    (c : ι → ℚ) (hc : c ≠ 0) :
    ∃ (d : ι → ℤ) (L : ℚ), L ≠ 0 ∧ (∀ i, (d i : ℚ) = L * c i) ∧ ∃ i, ¬ (p : ℤ) ∣ d i := by
  classical
  set L₀ : ℕ := ∏ i, (c i).den with hL₀
  have hL₀pos : 0 < L₀ := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    rw [hL₀, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    exact (c i).den_pos.ne' hi
  have hL₀q : ((L₀ : ℚ)) ≠ 0 := by exact_mod_cast hL₀pos.ne'
  have hex : ∀ i, ∃ z : ℤ, (z : ℚ) = (L₀ : ℚ) * c i := by
    intro i
    obtain ⟨m, hm⟩ : ((c i).den : ℤ) ∣ (L₀ : ℤ) := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr
        (Finset.dvd_prod_of_mem (fun j ↦ (c j).den) (Finset.mem_univ i))
    have hmq : (L₀ : ℚ) = ((c i).den : ℚ) * (m : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) hm
    refine ⟨m * (c i).num, ?_⟩
    calc ((m * (c i).num : ℤ) : ℚ) = (m : ℚ) * (c i * ((c i).den : ℚ)) := by
          rw [Rat.mul_den_eq_num]
          push_cast
          ring
      _ = ((c i).den : ℚ) * (m : ℚ) * c i := by ring
      _ = (L₀ : ℚ) * c i := by rw [← hmq]
  choose e he using hex
  have hene : e ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    intro h0
    apply hi
    have h1 : (0 : ℚ) = (L₀ : ℚ) * c i := by
      rw [← he i, show e i = 0 from congrFun h0 i]
      simp
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hL₀q
    · exact h
  obtain ⟨f, k, hf, i₀, hi₀⟩ := exists_pow_factor hp (∑ i, (e i).natAbs) e hene le_rfl
  have hpq : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.pos.ne')
  refine ⟨f, (L₀ : ℚ) / ((p : ℚ)) ^ k, div_ne_zero hL₀q hpq, fun i ↦ ?_, ⟨i₀, hi₀⟩⟩
  have h1 : ((e i : ℤ) : ℚ) = ((p : ℚ)) ^ k * (f i : ℚ) := by
    rw [hf i]
    push_cast
    ring
  rw [div_mul_eq_mul_div, ← he i, h1]
  field_simp

end FranklFuredi

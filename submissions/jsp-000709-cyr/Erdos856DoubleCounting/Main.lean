import Mathlib

/-!
# Erdős Problem #856: the double-counting bound for sets with no `k` equal pairwise lcms

Erdős defines `f_k(N)` as the maximum of `∑_{n ∈ A} 1/n` over `A ⊆ {1, …, N}` containing no
`k`-subset whose pairwise least common multiples are all equal, and asks to estimate `f_k(N)`
(OPEN; the bounds of Tang–Zhang are NOT formalized here).  The problem page records the
elementary part of Erdős's bound: "let `A` be such a set.  This in particular implies that, for
every `t`, there are `< k` solutions to `t = ap` with `a ∈ A` and `p` prime, whence
`∑_{n ∈ A} 1/n · ∑_{p < N} 1/p < k ∑_{t < N²} 1/t`."  This file proves both statements; the final
step `≪ log N / log log N` (Mertens' estimate `∑_{p < N} 1/p ≫ log log N`) is not claimed.

Definitions (ours; there is no formal-conjectures rendering of this problem).  `NoEqualLcm k A`
says no `k`-element subset of `A` has all pairwise lcms equal; `solutions A t` is the set of pairs
`(a, p)` with `a ∈ A`, `p` prime and `a * p = t`.  Sums are over `ℚ`, with the Lean convention
`1 / 0 = 0` (the term `t = 0` of `∑_{t < N²} 1/t` contributes nothing).

Why it works: `k` distinct solutions `t = a_i p_i` have distinct `a_i` and distinct primes `p_i`,
and `lcm(t/p_i, t/p_j) = t` for `i ≠ j`, so `{a_i}` would be a `k`-subset with all pairwise lcms
equal to `t`.  Hence `∑_{a ∈ A} ∑_{p < N} 1/(ap) = ∑_{t < N²} |solutions A t| / t ≤ (k − 1) ∑_{t < N²}
1/t < k ∑_{t < N²} 1/t`, using `a ≤ N`, `p < N` so that `ap < N²`, and `N ≥ 2` for strictness.
-/

namespace Erdos856

open Finset

/-- `A` contains no `k`-element subset all of whose pairwise least common multiples are equal. -/
def NoEqualLcm (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬ ∃ B ⊆ A, B.card = k ∧ ∃ L : ℕ, ∀ a ∈ B, ∀ b ∈ B, a ≠ b → Nat.lcm a b = L

/-- The solutions `(a, p)` of `t = a * p` with `a ∈ A` and `p` prime. -/
def solutions (A : Finset ℕ) (t : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ (Finset.range (t + 1)).filter Nat.Prime).filter (fun ap => ap.1 * ap.2 = t)

/-- Membership in `solutions A t` unfolded: `a ∈ A`, `p ≤ t`, `p` prime and `a * p = t`. -/
theorem mem_solutions_iff {A : Finset ℕ} {t : ℕ} {x : ℕ × ℕ} :
    x ∈ solutions A t ↔ x.1 ∈ A ∧ x.2 ≤ t ∧ Nat.Prime x.2 ∧ x.1 * x.2 = t := by
  simp only [solutions, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff, and_assoc]

/-- In a solution `t = a p` the factor `a` is nonzero (otherwise `t = 0`, forcing `p = 0`). -/
theorem fst_ne_zero_of_mem_solutions {A : Finset ℕ} {t : ℕ} {x : ℕ × ℕ}
    (h : x ∈ solutions A t) : x.1 ≠ 0 := by
  rw [mem_solutions_iff] at h
  obtain ⟨-, hle, hp, hmul⟩ := h
  intro h0
  rw [h0, zero_mul] at hmul
  subst hmul
  exact Nat.not_prime_zero (Nat.le_zero.mp hle ▸ hp)

/-- Two distinct solutions of `t = a p` have distinct first components. -/
theorem fst_injOn_solutions {A : Finset ℕ} (t : ℕ) :
    Set.InjOn Prod.fst (solutions A t : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe] at hx hy
  have hx0 : x.1 ≠ 0 := fst_ne_zero_of_mem_solutions hx
  rw [mem_solutions_iff] at hx hy
  have h2 : x.2 = y.2 := by
    have : x.1 * x.2 = x.1 * y.2 := by rw [hx.2.2.2, hxy, hy.2.2.2]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx0) this
  exact Prod.ext hxy h2

/-- Two solutions of `t = a p` with distinct first components have least common multiple `t`. -/
theorem lcm_eq_of_mem_solutions {A : Finset ℕ} {t : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ solutions A t) (hy : y ∈ solutions A t) (hne : x.1 ≠ y.1) :
    Nat.lcm x.1 y.1 = t := by
  obtain ⟨a, p⟩ := x
  obtain ⟨a', p'⟩ := y
  rw [mem_solutions_iff] at hx hy
  obtain ⟨-, -, hp, hmul⟩ := hx
  obtain ⟨-, -, hp', hmul'⟩ := hy
  simp only at hne hmul hmul' ⊢
  have hpp' : p ≠ p' := by
    rintro rfl
    exact hne (Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans hmul'.symm))
  have hpa' : p ∣ a' := by
    have hdvd : p ∣ a' * p' := by rw [hmul', ← hmul]; exact dvd_mul_left p a
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hp').mp h) hpp'
  obtain ⟨c, rfl⟩ := hpa'
  have ha : a = c * p' := by
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [hmul, ← hmul']; ring
  subst ha
  have hcop : Nat.Coprime p' p := (Nat.coprime_primes hp' hp).mpr (Ne.symm hpp')
  rw [mul_comm p c, Nat.lcm_mul_left, hcop.lcm_eq_mul, ← hmul']
  ring

/-- For every `t` there are fewer than `k` solutions to `t = a p` with `a ∈ A`, `p` prime. -/
theorem card_solutions_lt {k : ℕ} {A : Finset ℕ} (hA : NoEqualLcm k A) (t : ℕ) :
    (solutions A t).card < k := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hcon
  refine hA ⟨S.image Prod.fst, ?_, ?_, t, ?_⟩
  · intro a ha
    simp only [Finset.mem_image] at ha
    obtain ⟨x, hxS, rfl⟩ := ha
    exact (mem_solutions_iff.mp (hS hxS)).1
  · rw [Finset.card_image_of_injOn, hScard]
    exact (fst_injOn_solutions t).mono (by exact_mod_cast hS)
  · intro a ha b hb hab
    simp only [Finset.mem_image] at ha hb
    obtain ⟨x, hxS, rfl⟩ := ha
    obtain ⟨y, hyS, rfl⟩ := hb
    exact lcm_eq_of_mem_solutions (hS hxS) (hS hyS) hab

/-- **Erdős #856, the double-counting inequality**: for `A ⊆ {1, …, N}` with no `k` equal
pairwise lcms (`N ≥ 2`, `k ≥ 1`),
`∑_{n ∈ A} 1/n · ∑_{p < N} 1/p < k ∑_{t < N²} 1/t`. -/
theorem erdos_856_double_counting {k N : ℕ} {A : Finset ℕ} (hk : 1 ≤ k) (hN : 2 ≤ N)
    (hAN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) (hA : NoEqualLcm k A) :
    (∑ a ∈ A, (1 : ℚ) / a) * (∑ p ∈ (Finset.range N).filter Nat.Prime, (1 : ℚ) / p) <
      k * ∑ t ∈ Finset.range (N ^ 2), (1 : ℚ) / t := by
  classical
  have hk' : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  set P : Finset ℕ := (Finset.range N).filter Nat.Prime with hPdef
  set T : Finset ℕ := Finset.range (N ^ 2) with hTdef
  have hmaps : ∀ x ∈ A ×ˢ P, x.1 * x.2 ∈ T := by
    rintro ⟨a, p⟩ hx
    rw [Finset.mem_product] at hx
    obtain ⟨ha, hp⟩ := hx
    simp only [hPdef, Finset.mem_filter, Finset.mem_range] at hp
    simp only [hTdef, Finset.mem_range]
    have haN : a ≤ N := (hAN a ha).2
    calc a * p = p * a := mul_comm a p
      _ < N * N := Nat.mul_lt_mul_of_lt_of_le hp.1 haN (by omega)
      _ = N ^ 2 := (sq N).symm
  have stepA : (∑ a ∈ A, (1 : ℚ) / a) * (∑ p ∈ P, (1 : ℚ) / p)
      = ∑ x ∈ A ×ˢ P, (1 : ℚ) / ((x.1 * x.2 : ℕ) : ℚ) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_mul, div_mul_div_comm, one_mul]
  have stepB : ∑ x ∈ A ×ˢ P, (1 : ℚ) / ((x.1 * x.2 : ℕ) : ℚ)
      = ∑ t ∈ T, (((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card : ℚ) * (1 / (t : ℚ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => (1 : ℚ) / ((x.1 * x.2 : ℕ) : ℚ))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ) / (t : ℚ))
      (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul]
  have hcard : ∀ t : ℕ, ((((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card : ℚ)) ≤ (k : ℚ) - 1 := by
    intro t
    have hsub : (A ×ˢ P).filter (fun x => x.1 * x.2 = t) ⊆ solutions A t := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_product] at hx
      obtain ⟨⟨ha, hp⟩, hmul⟩ := hx
      simp only [hPdef, Finset.mem_filter, Finset.mem_range] at hp
      rw [mem_solutions_iff]
      refine ⟨ha, ?_, hp.2, hmul⟩
      rw [← hmul]
      exact Nat.le_mul_of_pos_left x.2 (by have := (hAN x.1 ha).1; omega)
    have h1 : ((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card + 1 ≤ k :=
      le_trans (Nat.add_le_add_right (Finset.card_le_card hsub) 1) (card_solutions_lt hA t)
    have h2 : ((((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card : ℚ)) + 1 ≤ (k : ℚ) := by
      exact_mod_cast h1
    linarith
  have hSpos : (0 : ℚ) < ∑ t ∈ T, (1 : ℚ) / t := by
    have h1 : (1 : ℕ) ∈ T := by
      simp only [hTdef, Finset.mem_range]
      nlinarith
    have := Finset.single_le_sum (f := fun t : ℕ => (1 : ℚ) / t)
      (fun t _ => by positivity) h1
    simp only [Nat.cast_one, div_one] at this
    linarith
  have hstep : ∑ t ∈ T, (((A ×ˢ P).filter (fun x => x.1 * x.2 = t)).card : ℚ) * (1 / (t : ℚ))
      ≤ ((k : ℚ) - 1) * ∑ t ∈ T, (1 : ℚ) / t := by
    have : (0 : ℚ) ≤ (k : ℚ) - 1 := by linarith [hk']
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    exact mul_le_mul_of_nonneg_right (hcard t) (by positivity)
  rw [stepA, stepB]
  have hklt : ((k : ℚ) - 1) * (∑ t ∈ T, (1 : ℚ) / t) < (k : ℚ) * ∑ t ∈ T, (1 : ℚ) / t := by
    nlinarith
  linarith

end Erdos856

open Erdos856 in
/-- **Erdős #856, closed form**: there are no `k ≥ 1`, `N ≥ 2` and `A ⊆ {1, …, N}` with no `k`
equal pairwise lcms for which `∑_{n ∈ A} 1/n · ∑_{p < N} 1/p ≥ k ∑_{t < N²} 1/t`. -/
theorem erdos_856_double_counting_closed :
    ¬ ∃ (k N : ℕ) (A : Finset ℕ), 1 ≤ k ∧ 2 ≤ N ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ NoEqualLcm k A ∧
      k * ∑ t ∈ Finset.range (N ^ 2), (1 : ℚ) / t ≤
        (∑ a ∈ A, (1 : ℚ) / a) * (∑ p ∈ (Finset.range N).filter Nat.Prime, (1 : ℚ) / p) := by
  rintro ⟨k, N, A, hk, hN, hAN, hA, hle⟩
  exact absurd (Erdos856.erdos_856_double_counting hk hN hAN hA) (not_lt.mpr hle)

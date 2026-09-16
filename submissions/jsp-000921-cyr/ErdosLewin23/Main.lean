import Mathlib

/-!
# Erdős Problem #1110, the base case `{p, q} = {2, 3}` (Erdős–Lewin)

Erdős and Lewin (Math. Comp. 65 (1996), 837–840) call `n` *representable* with respect to
coprime `p > q ≥ 2` if `n` is a sum of distinct integers of the form `p^k q^l` none of which
divides another, and proved that there are only finitely many non-representable numbers if and
only if `{p, q} = {2, 3}`.  The open question on erdosproblems.com/1110 concerns the other pairs.
This file proves the base case: **every** natural number is representable with respect to
`p = 3, q = 2` (Erdős's "silly conjecture", proved by Jansen and others by a short induction).

The predicate `Representable` is the one used by the formal-conjectures statement of the
problem: a finite set `s ⊆ {p^k q^l}` that is an antichain for divisibility, with `s.sum id = n`.
-/

open Finset

/-- The integers of the form `p ^ k * q ^ l`. -/
def Gamma (p q : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k l : ℕ, n = p ^ k * q ^ l}

/-- `n` is representable with respect to `p` and `q` if it is the sum of a finite divisibility
antichain of terms of the form `p ^ k * q ^ l`. -/
def Representable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (s : Set ℕ) ⊆ Gamma p q ∧ IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n

/-- The inductive strengthening: every `n` is representable with respect to `3, 2`, and if `n`
is even then all summands can be taken even. -/
theorem representable_three_two_strong (n : ℕ) :
    Representable 3 2 n ∧ (Even n → ∃ s : Finset ℕ, (s : Set ℕ) ⊆ Gamma 3 2 ∧
      IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n ∧ ∀ x ∈ s, Even x) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.even_or_odd n with hev | hodd
  · have key : ∃ s : Finset ℕ, (s : Set ℕ) ⊆ Gamma 3 2 ∧
        IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n ∧ ∀ x ∈ s, Even x := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · refine ⟨∅, by simp, ?_, by simp, by simp⟩
        intro a ha
        simp at ha
      obtain ⟨m, hm⟩ := hev
      obtain ⟨t, htsub, htanti, htsum⟩ := (ih m (by omega)).1
      have hinj : ∀ x ∈ t, ∀ y ∈ t, 2 * x = 2 * y → x = y := fun x _ y _ h ↦ by omega
      refine ⟨t.image (fun x ↦ 2 * x), ?_, ?_, ?_, ?_⟩
      · intro a ha
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha
        obtain ⟨x, hx, rfl⟩ := ha
        obtain ⟨c, l, rfl⟩ := htsub (Finset.mem_coe.mpr hx)
        exact ⟨c, l + 1, by ring⟩
      · intro a ha b hb hab
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
        obtain ⟨x, hx, rfl⟩ := ha
        obtain ⟨y, hy, rfl⟩ := hb
        have hne : x ≠ y := fun h ↦ hab (by rw [h])
        have hnd := htanti (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hne
        simpa [Nat.mul_dvd_mul_iff_left (show 0 < 2 by norm_num)] using hnd
      · have himg : (t.image (fun x ↦ 2 * x)).sum id = 2 * t.sum id := by
          rw [Finset.sum_image hinj, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ ↦ rfl
        rw [himg, htsum]
        omega
      · intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact even_two_mul y
    obtain ⟨s, h1, h2, h3, h4⟩ := key
    exact ⟨⟨s, h1, h2, h3⟩, fun _ ↦ ⟨s, h1, h2, h3, h4⟩⟩
  set k := Nat.log 3 n with hk
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hle : 3 ^ k ≤ n := Nat.pow_log_le_self 3 (by omega)
  have hlt : n < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hpk2 : 3 ^ k % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr rfl))
  have hpos : 0 < 3 ^ k := Nat.pow_pos (by norm_num)
  have hrlt : n - 3 ^ k < n := by omega
  obtain ⟨t, htsub, htanti, htsum, hteven⟩ := (ih _ hrlt).2 (Nat.even_iff.mpr (by omega))
  have hnotmem : 3 ^ k ∉ t := fun hmem ↦ by
    have := Nat.even_iff.mp (hteven _ hmem)
    omega
  have hxle : ∀ x ∈ t, x ≤ n - 3 ^ k := fun x hx ↦
    htsum ▸ Finset.single_le_sum (f := id) (fun i _ ↦ Nat.zero_le (id i)) hx
  have hkey : ∀ x ∈ t, ¬ (3 ^ k ∣ x) ∧ ¬ (x ∣ 3 ^ k) := by
    intro x hx
    obtain ⟨a, b, hxab⟩ := htsub (Finset.mem_coe.mpr hx)
    have hx2 : x % 2 = 0 := Nat.even_iff.mp (hteven x hx)
    refine ⟨fun hdvd ↦ ?_, fun hdvd ↦ ?_⟩
    · have hb0 : b ≠ 0 := by
        rintro rfl
        have h3a : 3 ^ a % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr rfl))
        rw [pow_zero, mul_one] at hxab
        omega
      have hcop : Nat.Coprime (3 ^ k) (2 ^ b) := Nat.Coprime.pow k b (by decide)
      have h3a : 3 ^ k ∣ 3 ^ a := hcop.dvd_of_dvd_mul_right (hxab ▸ hdvd)
      have hpa : 3 ^ k ≤ 3 ^ a := Nat.le_of_dvd (Nat.pow_pos (by norm_num)) h3a
      have h2b : (2 : ℕ) ≤ 2 ^ b := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hbig : 3 ^ k * 2 ≤ x := hxab ▸ Nat.mul_le_mul hpa h2b
      have := hxle x hx
      omega
    · have h2 : (2 : ℕ) ∣ 3 ^ k := dvd_trans (Nat.dvd_of_mod_eq_zero hx2) hdvd
      omega
  refine ⟨⟨insert (3 ^ k) t, ?_, ?_, ?_⟩, fun hev ↦ absurd (Nat.even_iff.mp hev) (by omega)⟩
  · rw [Finset.coe_insert]
    exact Set.insert_subset ⟨k, 0, by ring⟩ htsub
  · intro c hc d hd hcd hdvd
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hc hd
    rcases hc with rfl | hc
    · rcases hd with rfl | hd
      · exact hcd rfl
      · exact (hkey d hd).1 hdvd
    · rcases hd with rfl | hd
      · exact (hkey c hc).2 hdvd
      · exact htanti (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hd) hcd hdvd
  · rw [Finset.sum_insert hnotmem, htsum]
    simp only [id_eq]
    omega

/-- **Erdős–Lewin, the base case `{2, 3}`.**  Every natural number is the sum of distinct
integers of the form `3 ^ k * 2 ^ l`, none of which divides another. -/
theorem erdos_lewin_two_three (n : ℕ) : Representable 3 2 n :=
  (representable_three_two_strong n).1

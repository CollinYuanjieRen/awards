import Jsp731.Construction
import Jsp731.PowTwo
import Jsp731.OrderTwo

/-!
# JSP-000731 / Erdős #880 — the order of `A = basis h` is not smaller than `h`

For `h ≥ 3` we exhibit, in every block of the construction of `Jsp731/Construction.lean`, an
integer which is *not* a sum of `h − 1` or fewer elements of `A`, namely

`u n = 2^(h−1) · x_n² − 1`.

The proof is the pigeonhole argument of Hegyvári–Hennecart–Plagne (2007).  Since
`2^(h−1) < c`, we have `u n < x_{n+1}`, so every summand of a representation of `u n` lies below
`x_{n+1}` and is therefore (by `mem_basis_classify`) either a *spike* `x_n + 2^j·x_n²` with
`j < h − 1` or a *small* element `< x_n + x_n²`.  Writing `E` for the multiset of spike exponents
used, `Q = ∑_{j ∈ E} 2^j`, `m = card E` and `t` for the number of small summands:

* comparing the `x_n²`-parts from below gives `Q < 2^(h−1)`;
* comparing them from above, together with `x_n² ≥ (h−1)·x_n + 3` (`sq_scale_ge`), gives
  `Q + t ≥ 2^(h−1)`;
* the key lemma `sum_two_pow_le_of_lt` bounds `Q ≤ 2^(h−1) − 2^(h−1−m)`, whence
  `t ≥ 2^(h−1−m) ≥ (h − 1 − m) + 1`, contradicting `m + t ≤ h − 1`.

As `u n ≥ x_n ≥ n + h`, these integers are arbitrarily large, so `A` is not an asymptotic basis
of any order `j < h`.
-/

open Filter

namespace Erdos880

variable {h : ℕ}

/-- The integer `u_n = 2^(h−1)·x_n² − 1`, which is not a sum of `h − 1` or fewer elements of `A`. -/
def missing (h n : ℕ) : ℕ := 2 ^ (h - 1) * (scale h n) ^ 2 - 1

theorem scale_le_missing (hh : 3 ≤ h) (n : ℕ) : scale h n ≤ missing h n := by
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have hsq := sq_scale_ge hh n
  have hone : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
  have h1 : 1 * scale h n ^ 2 ≤ 2 ^ (h - 1) * scale h n ^ 2 := Nat.mul_le_mul hone le_rfl
  have h2 : 2 * scale h n ≤ (h - 1) * scale h n := Nat.mul_le_mul (by omega) le_rfl
  unfold missing
  omega

theorem missing_lt_scale_succ (hh : 3 ≤ h) (n : ℕ) : missing h n < scale h (n + 1) := by
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have hc : 2 ^ (h - 1) ≤ coeff h := (two_pow_lt_coeff hh).le
  have h1 : 2 ^ (h - 1) * scale h n ^ 2 ≤ coeff h * scale h n ^ 2 := Nat.mul_le_mul hc le_rfl
  have h2 : 3 * 3 ≤ h * scale h n := Nat.mul_le_mul hh hx
  show 2 ^ (h - 1) * scale h n ^ 2 - 1 < coeff h * scale h n ^ 2 + h * scale h n
  omega

/-- Splitting a multiset of elements of `A` below `x_{n+1}` into spikes (exponent multiset `E`) and
small elements (`t` of them). -/
theorem exists_split (hh : 3 ≤ h) {n : ℕ} (m : Multiset ℕ) (hA : ∀ a ∈ m, a ∈ basis h)
    (hlt : ∀ a ∈ m, a < scale h (n + 1)) :
    ∃ (E : Multiset ℕ) (t : ℕ), (∀ j ∈ E, j < h - 1) ∧ Multiset.card E + t = Multiset.card m ∧
      (E.map fun j => 2 ^ j).sum * (scale h n) ^ 2 + Multiset.card E * scale h n ≤ m.sum ∧
      m.sum ≤ (E.map fun j => 2 ^ j).sum * (scale h n) ^ 2 + Multiset.card E * scale h n +
        t * (scale h n + (scale h n) ^ 2 - 1) := by
  revert hA hlt
  induction m using Multiset.induction_on with
  | empty => exact fun _ _ => ⟨0, 0, by simp, by simp, by simp, by simp⟩
  | cons a s ih =>
    intro hA hlt
    obtain ⟨E, t, hE, hcard, hlow, hhigh⟩ :=
      ih (fun b hb => hA b (Multiset.mem_cons_of_mem hb))
        (fun b hb => hlt b (Multiset.mem_cons_of_mem hb))
    have hx : 3 ≤ scale h n := three_le_scale hh n
    have ha : a ∈ basis h := hA a (Multiset.mem_cons_self a s)
    have halt : a < scale h (n + 1) := hlt a (Multiset.mem_cons_self a s)
    rcases mem_basis_classify hh ha halt with ⟨i, hi, rfl⟩ | hsmall
    · -- a spike: enlarge the exponent multiset
      refine ⟨i ::ₘ E, t, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Multiset.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hE j hj
      · simp only [Multiset.card_cons]
        omega
      · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        have e : (2 ^ i + (Multiset.map (fun j => 2 ^ j) E).sum) * scale h n ^ 2 +
              (Multiset.card E + 1) * scale h n
            = (scale h n + 2 ^ i * scale h n ^ 2) +
              ((Multiset.map (fun j => 2 ^ j) E).sum * scale h n ^ 2 +
                Multiset.card E * scale h n) := by ring
        omega
      · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        have e : (2 ^ i + (Multiset.map (fun j => 2 ^ j) E).sum) * scale h n ^ 2 +
              (Multiset.card E + 1) * scale h n
            = (scale h n + 2 ^ i * scale h n ^ 2) +
              ((Multiset.map (fun j => 2 ^ j) E).sum * scale h n ^ 2 +
                Multiset.card E * scale h n) := by ring
        omega
    · -- a small element: increase the count of small summands
      refine ⟨E, t + 1, hE, ?_, ?_, ?_⟩
      · simp only [Multiset.card_cons]
        omega
      · simp only [Multiset.sum_cons]
        omega
      · simp only [Multiset.sum_cons]
        have e := add_one_mul t (scale h n + scale h n ^ 2 - 1)
        omega

theorem not_isSumOfAtMost_missing (hh : 3 ≤ h) (n : ℕ) :
    ¬ IsSumOfAtMost (basis h) (h - 1) (missing h n) := by
  rintro ⟨m, hmA, hcard, hsum⟩
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have hsq := sq_scale_ge hh n
  have hPpos : 0 < 2 ^ (h - 1) := Nat.two_pow_pos _
  have hXpos : 0 < scale h n ^ 2 := by positivity
  have hPX : 0 < 2 ^ (h - 1) * scale h n ^ 2 := Nat.mul_pos hPpos hXpos
  unfold missing at hsum
  have hmlt := missing_lt_scale_succ hh n
  unfold missing at hmlt
  have hlt : ∀ a ∈ m, a < scale h (n + 1) := by
    intro a hamem
    have h1 : a ≤ m.sum := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hamem
    omega
  obtain ⟨E, t, _hE, hcardEt, hlow, hhigh⟩ := exists_split hh m hmA hlt
  -- (1) the `x_n²`-part is below `2^(h-1)`
  have hQP : (Multiset.map (fun j => 2 ^ j) E).sum < 2 ^ (h - 1) := by
    by_contra hcon
    have h1 : 2 ^ (h - 1) * scale h n ^ 2
        ≤ (Multiset.map (fun j => 2 ^ j) E).sum * scale h n ^ 2 :=
      Nat.mul_le_mul (by omega) le_rfl
    omega
  -- (2) but the total `x_n²`-part, small summands included, is at least `2^(h-1)`
  have hQt : 2 ^ (h - 1) ≤ (Multiset.map (fun j => 2 ^ j) E).sum + t := by
    by_contra hcon
    have h1 : ((Multiset.map (fun j => 2 ^ j) E).sum + t + 1) * scale h n ^ 2
        ≤ 2 ^ (h - 1) * scale h n ^ 2 := Nat.mul_le_mul (by omega) le_rfl
    have h2 : ((Multiset.map (fun j => 2 ^ j) E).sum + t + 1) * scale h n ^ 2
        = (Multiset.map (fun j => 2 ^ j) E).sum * scale h n ^ 2 + t * scale h n ^ 2
          + scale h n ^ 2 := by ring
    have h3 : (Multiset.card E + t) * scale h n ≤ (h - 1) * scale h n :=
      Nat.mul_le_mul (by omega) le_rfl
    have h4 : (Multiset.card E + t) * scale h n
        = Multiset.card E * scale h n + t * scale h n := by ring
    have h5 : t * (scale h n + scale h n ^ 2 - 1) ≤ t * scale h n + t * scale h n ^ 2 :=
      calc t * (scale h n + scale h n ^ 2 - 1)
          ≤ t * (scale h n + scale h n ^ 2) := Nat.mul_le_mul_left t (Nat.sub_le _ _)
        _ = t * scale h n + t * scale h n ^ 2 := by ring
    omega
  -- (3) pigeonhole on the powers of two
  have hQ : (Multiset.map (fun j => 2 ^ j) E).sum
      ≤ 2 ^ (h - 1) - 2 ^ (h - 1 - Multiset.card E) := sum_two_pow_le_of_lt E (h - 1) hQP
  have hmono : 2 ^ (h - 1 - Multiset.card E) ≤ 2 ^ (h - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsucc : (h - 1 - Multiset.card E) + 1 ≤ 2 ^ (h - 1 - Multiset.card E) :=
    succ_le_two_pow _
  omega

/-- `A = basis h` is not an asymptotic basis of any order `j < h`. -/
theorem not_isAsymptoticBasis_of_lt (hh : 3 ≤ h) {j : ℕ} (hj : j < h) :
    ¬ IsAsymptoticBasis (basis h) j := by
  intro hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have h1 : N + h ≤ scale h N := add_le_scale hh N
  have h2 : scale h N ≤ missing h N := scale_le_missing hh N
  exact not_isSumOfAtMost_missing hh N
    (isSumOfAtMost_mono (by omega) (hN (missing h N) (by omega)))

end Erdos880

#print axioms Erdos880.not_isAsymptoticBasis_of_lt
#print axioms Erdos880.not_isSumOfAtMost_missing

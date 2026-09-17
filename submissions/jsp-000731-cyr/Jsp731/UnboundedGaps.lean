import Jsp731.Construction
import Jsp731.PowTwo
import Jsp731.OrderTwo

/-!
# JSP-000731 / Erdős #880 — the restricted sumset of `basis h` has unbounded gaps

Fix `h ≥ 3` and write `x_n = scale h n` for the scales of the construction.  The block structure
of `A = basis h` forces a gap in the set of sums of at most `h` *distinct* elements of `A`:
put
```
M_n = 2^(h−1)·x_n² + h·x_n   (`cap h n`).
```
Then no integer of the open interval `(M_n, x_{n+1})` is such a sum (`not_mem_distinctSums_of_lt`),
while `x_{n+1} ≥ M_n + x_n²` (`cap_add_sq_le`), so the gap has length at least `x_n² − 1 → ∞`.

The heart of the matter is `sum_le_cap`: if `s ⊆ A` has at most `h` elements, all of them below
`x_{n+1}`, then `∑ s ≤ M_n`.  Indeed, by `mem_basis_classify` each element of `s` is either a
spike `x_n + 2^j·x_n²` of block `n` (`j < h − 1`) or is `< x_n + x_n²`.  If the `m` spikes of `s`
use the exponent set `J ⊆ range (h−1)` and `t` elements are small, then
```
∑ s ≤ (∑_{j ∈ J} 2^j)·x_n² + m·x_n + t·(x_n + x_n²) = (Q + t)·x_n² + (m + t)·x_n,
```
and `m + t = |s| ≤ h` while `Q + t ≤ 2^(h−1)`: the subset bound
`Q + 2^(h−1−m) ≤ 2^(h−1)` (`sum_two_pow_add_two_pow_le`) combines with
`t ≤ h − m = (h − 1 − m) + 1 ≤ 2^(h−1−m)` (`succ_le_two_pow`).
-/

open Filter

namespace Erdos880

variable {h : ℕ}

/-- `M_n = 2^(h−1)·x_n² + h·x_n`: every sum of ≤ h distinct elements of `A` below `x_{n+1}` is ≤ M_n. -/
def cap (h n : ℕ) : ℕ := 2 ^ (h - 1) * (scale h n) ^ 2 + h * scale h n

theorem cap_add_sq_le (hh : 3 ≤ h) (n : ℕ) : cap h n + (scale h n) ^ 2 ≤ scale h (n + 1) := by
  have hc : 2 ^ (h - 1) + 1 ≤ coeff h := by have := two_pow_lt_coeff hh; omega
  have h1 : (2 ^ (h - 1) + 1) * (scale h n) ^ 2 ≤ coeff h * (scale h n) ^ 2 :=
    Nat.mul_le_mul hc le_rfl
  calc cap h n + (scale h n) ^ 2
      = (2 ^ (h - 1) + 1) * (scale h n) ^ 2 + h * scale h n := by unfold cap; ring
    _ ≤ coeff h * (scale h n) ^ 2 + h * scale h n := Nat.add_le_add_right h1 _
    _ = scale h (n + 1) := rfl

theorem sum_le_cap (hh : 3 ≤ h) {n : ℕ} {s : Finset ℕ} (hsA : (↑s : Set ℕ) ⊆ basis h)
    (hcard : s.card ≤ h) (hlt : ∀ a ∈ s, a < scale h (n + 1)) : ∑ a ∈ s, a ≤ cap h n := by
  classical
  have hspike : Function.Injective (fun j : ℕ => scale h n + 2 ^ j * (scale h n) ^ 2) :=
    spike_injective hh n
  -- the exponents of the spikes of block `n` that belong to `s`, and the spikes themselves
  set J : Finset ℕ :=
    (Finset.range (h - 1)).filter (fun j => scale h n + 2 ^ j * (scale h n) ^ 2 ∈ s) with hJdef
  set S : Finset ℕ := J.image (fun j : ℕ => scale h n + 2 ^ j * (scale h n) ^ 2) with hSdef
  have hJsub : J ⊆ Finset.range (h - 1) := by rw [hJdef]; exact Finset.filter_subset _ _
  have hSs : S ⊆ s := by
    intro a ha
    rw [hSdef, Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [hJdef, Finset.mem_filter] at hj
    exact hj.2
  have hcardS : S.card = J.card := by
    rw [hSdef]; exact Finset.card_image_of_injective _ hspike
  -- the spike part of the sum
  have hsumS : ∑ a ∈ S, a = J.card * scale h n + (∑ j ∈ J, 2 ^ j) * (scale h n) ^ 2 := by
    rw [hSdef, Finset.sum_image (fun a _ b _ hab => hspike hab), Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul, ← Finset.sum_mul]
  -- every remaining element of `s` is small
  have hsmall : ∀ a ∈ s \ S, a ≤ scale h n + (scale h n) ^ 2 := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    rcases mem_basis_classify hh (hsA (Finset.mem_coe.mpr ha.1)) (hlt a ha.1) with
      ⟨j, hj, rfl⟩ | hsm
    · exact absurd (by
        rw [hSdef, Finset.mem_image]
        exact ⟨j, by rw [hJdef, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hj, ha.1⟩, rfl⟩)
        ha.2
    · omega
  have hsumT : ∑ a ∈ s \ S, a ≤ (s \ S).card * (scale h n + (scale h n) ^ 2) := by
    have := Finset.sum_le_card_nsmul (s \ S) (fun a : ℕ => a) _ hsmall
    simpa using this
  -- counting
  have hcardsum : (s \ S).card + S.card = s.card := Finset.card_sdiff_add_card_eq_card hSs
  have hJcard : J.card ≤ h - 1 := by
    have := Finset.card_le_card hJsub; simpa using this
  have hQ : (∑ j ∈ J, 2 ^ j) + 2 ^ (h - 1 - J.card) ≤ 2 ^ (h - 1) :=
    sum_two_pow_add_two_pow_le hJsub
  have hpow := succ_le_two_pow (h - 1 - J.card)
  have hQt : (∑ j ∈ J, 2 ^ j) + (s \ S).card ≤ 2 ^ (h - 1) := by omega
  have hmt : J.card + (s \ S).card ≤ h := by omega
  have hmul1 : ((∑ j ∈ J, 2 ^ j) + (s \ S).card) * (scale h n) ^ 2
      ≤ 2 ^ (h - 1) * (scale h n) ^ 2 := Nat.mul_le_mul hQt le_rfl
  have hmul2 : (J.card + (s \ S).card) * scale h n ≤ h * scale h n := Nat.mul_le_mul hmt le_rfl
  calc ∑ a ∈ s, a = ∑ a ∈ s \ S, a + ∑ a ∈ S, a := (Finset.sum_sdiff hSs).symm
    _ ≤ (s \ S).card * (scale h n + (scale h n) ^ 2)
          + (J.card * scale h n + (∑ j ∈ J, 2 ^ j) * (scale h n) ^ 2) := by
        rw [hsumS]; exact Nat.add_le_add_right hsumT _
    _ = ((∑ j ∈ J, 2 ^ j) + (s \ S).card) * (scale h n) ^ 2
          + (J.card + (s \ S).card) * scale h n := by ring
    _ ≤ 2 ^ (h - 1) * (scale h n) ^ 2 + h * scale h n := Nat.add_le_add hmul1 hmul2
    _ = cap h n := rfl

theorem not_mem_distinctSums_of_lt (hh : 3 ≤ h) {n m : ℕ} (h1 : cap h n < m)
    (h2 : m < scale h (n + 1)) : m ∉ distinctSums (basis h) h := by
  rintro ⟨s, hsA, hcard, hsum⟩
  have hlt : ∀ a ∈ s, a < scale h (n + 1) := by
    intro a ha
    have := Finset.single_le_sum (f := fun a : ℕ => a) (fun _ _ => Nat.zero_le _) ha
    omega
  have := sum_le_cap hh hsA hcard hlt
  omega

theorem distinctSums_basis_infinite (hh : 3 ≤ h) : (distinctSums (basis h) h).Infinite :=
  distinctSums_infinite_of_infinite (by omega) (basis_infinite hh)

/-- The restricted sumset of `A = basis h` has unbounded gaps. -/
theorem basis_not_hasBoundedGaps (hh : 3 ≤ h) : ¬ HasBoundedGaps (distinctSums (basis h) h) := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hC
  have hxge : (N + C + 2) + h ≤ scale h (N + C + 2) := add_le_scale hh (N + C + 2)
  have hx3 : 3 ≤ scale h (N + C + 2) := three_le_scale hh (N + C + 2)
  have hsq : scale h (N + C + 2) ≤ (scale h (N + C + 2)) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hcapge : scale h (N + C + 2) ≤ cap h (N + C + 2) := by
    have h1 : 1 * scale h (N + C + 2) ≤ h * scale h (N + C + 2) := Nat.mul_le_mul (by omega) le_rfl
    have h2 : h * scale h (N + C + 2) ≤ cap h (N + C + 2) := Nat.le_add_left _ _
    omega
  obtain ⟨b, hbmem, hb1, hb2⟩ := hN (cap h (N + C + 2) + 1) (by omega)
  exact not_mem_distinctSums_of_lt hh (n := N + C + 2) (by omega)
    (lt_of_lt_of_le (show b < cap h (N + C + 2) + (scale h (N + C + 2)) ^ 2 by omega)
      (cap_add_sq_le hh (N + C + 2))) hbmem

end Erdos880

#print axioms Erdos880.basis_not_hasBoundedGaps
#print axioms Erdos880.sum_le_cap

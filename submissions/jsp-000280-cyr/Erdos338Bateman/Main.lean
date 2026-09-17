import Mathlib

/-!
# Erdős Problem #338: Bateman's basis of order `h` with no restricted order

The *order* of an additive basis `A ⊆ ℕ` is the least `h` such that every sufficiently large
integer is a sum of at most `h` elements of `A` (repetitions allowed); its *restricted order* is
the least `t` (if it exists) such that every sufficiently large integer is a sum of at most `t`
*distinct* elements of `A`.  Erdős asked for necessary and sufficient conditions for the
restricted order to exist, and whether it can be bounded in terms of the order (OPEN; not
addressed here).  The problem page records: "Bateman has observed that for `h ≥ 3` there is a
basis of order `h` with no restricted order, taking `A = {1} ∪ {x > 0 : h ∣ x}`."

This file proves Bateman's observation.  There is no formal-conjectures file for #338, so the
definitions below are ours, written to match the page's wording: `IsBasisOfOrder A h` says every
sufficiently large integer is a sum of at most `h` elements of `A` (as a list, so repetitions are
allowed), and `HasRestrictedOrder A t` says every sufficiently large integer is a sum of at most
`t` distinct elements of `A` (a finset).  For `h ≥ 3` the set `A = {1} ∪ {x > 0 : h ∣ x}` is a
basis of order exactly `h` (of order `h` but not of order `h − 1`) and has no restricted order.
Kelly's, Hennecart's and the Hegyvári–Hennecart–Plagne results are not claimed.

Proof.  Write `n = q·h + r` with `r < h`; for `n ≥ h` we have `q ≥ 1`, and `n` is `r` ones plus
the multiple `q·h`, at most `r + 1 ≤ h` summands.  Integers `n ≡ h − 1 (mod h)` need `h − 1` ones
(a sum of `k` elements of `A` is congruent to its number of ones modulo `h`, and the ones are the
only elements not divisible by `h`), hence `h` summands, so the order is not `h − 1`.  A sum of
*distinct* elements of `A` contains at most one `1`, so it is `≡ 0` or `1 (mod h)`; since `h ≥ 3`,
the integers `≡ 2 (mod h)` are never represented, so no restricted order exists.
-/

open Filter

/-- Bateman's set `{1} ∪ {x > 0 : h ∣ x}`. -/
def batemanSet (h : ℕ) : Set ℕ := {1} ∪ {x | 0 < x ∧ h ∣ x}

/-- `A` is an additive basis of order (at most) `h`: every sufficiently large integer is the sum
of at most `h` elements of `A`, repetitions allowed. -/
def IsBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ l : List ℕ, (∀ x ∈ l, x ∈ A) ∧ l.length ≤ h ∧ l.sum = n

/-- `A` has restricted order (at most) `t`: every sufficiently large integer is the sum of at
most `t` distinct elements of `A`. -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ S : Finset ℕ, ↑S ⊆ A ∧ S.card ≤ t ∧ ∑ x ∈ S, x = n

private lemma mem_batemanSet {H x : ℕ} : x ∈ batemanSet H ↔ x = 1 ∨ (0 < x ∧ H ∣ x) := by
  simp [batemanSet]

/-- A sum of elements of `batemanSet H` is congruent modulo `H` to the number of `1`s it uses:
every other element of the set is divisible by `H`. -/
lemma batemanSet_sum_mod_count {H : ℕ} (hH : 3 ≤ H) :
    ∀ l : List ℕ, (∀ x ∈ l, x ∈ batemanSet H) → l.sum % H = l.count 1 % H := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro hmem
    have ha : a ∈ batemanSet H := hmem a (List.mem_cons_self ..)
    have IH : t.sum % H = t.count 1 % H := ih fun x hx => hmem x (List.mem_cons_of_mem _ hx)
    rcases mem_batemanSet.mp ha with rfl | ⟨-, hdvd⟩
    · have key : (1 + t.sum) % H = (1 + t.count 1) % H := by
        conv_lhs => rw [Nat.add_mod, IH, ← Nat.add_mod]
      have hcount : (1 :: t).count 1 = t.count 1 + 1 := by simp
      rw [List.sum_cons, hcount, key, Nat.add_comm]
    · have hne : ¬ (1 = a) := by
        rintro rfl
        have := Nat.le_of_dvd Nat.one_pos hdvd
        omega
      obtain ⟨c, rfl⟩ := hdvd
      have hne' : H * c ≠ 1 := fun h => hne h.symm
      have hcount : (H * c :: t).count 1 = t.count 1 := by simp [hne']
      rw [List.sum_cons, hcount, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
        Nat.mod_mod_of_dvd _ dvd_rfl, IH]

private lemma bateman_isBasis {H : ℕ} (hH : 3 ≤ H) : IsBasisOfOrder (batemanSet H) H := by
  refine Filter.eventually_atTop.mpr ⟨H, fun n hn => ?_⟩
  have hH0 : 0 < H := by omega
  have hq : 0 < n / H := Nat.div_pos hn hH0
  have hr : n % H < H := Nat.mod_lt _ hH0
  refine ⟨List.replicate (n % H) 1 ++ [n / H * H], ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
      exact mem_batemanSet.mpr (Or.inl rfl)
    · rw [List.mem_singleton.mp hx]
      exact mem_batemanSet.mpr (Or.inr ⟨Nat.mul_pos hq hH0, dvd_mul_left H (n / H)⟩)
  · simp only [List.length_append, List.length_replicate, List.length_singleton]
    omega
  · simp only [List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil, smul_eq_mul,
      Nat.mul_one, Nat.add_zero]
    exact Nat.mod_add_div' n H

private lemma bateman_not_isBasis {H : ℕ} (hH : 3 ≤ H) :
    ¬ IsBasisOfOrder (batemanSet H) (H - 1) := by
  intro hb
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  have hHle : H ≤ (N + 1) * H := Nat.le_mul_of_pos_left H (by omega)
  have hNle : N ≤ (N + 1) * H := le_trans (by omega) (Nat.le_mul_of_pos_right (N + 1) (by omega))
  obtain ⟨l, hmem, hlen, hsum⟩ := hN ((N + 1) * H + (H - 1)) (by omega)
  have hnmod : ((N + 1) * H + (H - 1)) % H = H - 1 := by
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod_of_dvd _ dvd_rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hcl : l.count 1 ≤ l.length := List.count_le_length
  have hkey : l.count 1 % H = H - 1 := by
    rw [← batemanSet_sum_mod_count hH l hmem, hsum, hnmod]
  have hcount : l.count 1 = H - 1 := by
    rw [Nat.mod_eq_of_lt (by omega)] at hkey
    exact hkey
  have heq : l.count 1 = l.length := by omega
  have hrep : l = List.replicate l.length 1 :=
    List.eq_replicate_length.mpr fun b hb => (List.count_eq_length.mp heq b hb).symm
  have hs : l.sum = l.length := by
    conv_lhs => rw [hrep]
    simp
  omega

private lemma bateman_no_restricted {H : ℕ} (hH : 3 ≤ H) (t : ℕ) :
    ¬ HasRestrictedOrder (batemanSet H) t := by
  intro hr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hr
  have hNle : N ≤ (N + 1) * H := le_trans (by omega) (Nat.le_mul_of_pos_right (N + 1) (by omega))
  obtain ⟨S, hS, -, hsum⟩ := hN ((N + 1) * H + 2) (by omega)
  have hnmod : ((N + 1) * H + 2) % H = 2 := by
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod_of_dvd _ dvd_rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hdvd : H ∣ ∑ x ∈ S.erase 1, x := by
    refine Finset.dvd_sum fun i hi => ?_
    obtain ⟨hi1, hiS⟩ := Finset.mem_erase.mp hi
    rcases mem_batemanSet.mp (hS (Finset.mem_coe.mpr hiS)) with h | h
    · exact absurd h hi1
    · exact h.2
  obtain ⟨c, hc⟩ := hdvd
  by_cases h1 : (1 : ℕ) ∈ S
  · have hsplit : (∑ x ∈ S.erase 1, x) + 1 = ∑ x ∈ S, x := Finset.sum_erase_add S _ h1
    rw [hc] at hsplit
    rw [← hsplit] at hsum
    rw [← hsum, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod_of_dvd _ dvd_rfl,
      Nat.mod_eq_of_lt (by omega : (1 : ℕ) < H)] at hnmod
    omega
  · rw [Finset.erase_eq_of_notMem h1] at hc
    rw [hc] at hsum
    rw [← hsum, Nat.mul_mod_right] at hnmod
    omega

/-- **Bateman's observation (Erdős #338)**, in the offset form `h + 3` (so `h + 3 ≥ 3` without a
hypothesis): `{1} ∪ {x > 0 : (h + 3) ∣ x}` is a basis of order `h + 3`, not of order `h + 2`,
and has no restricted order. -/
theorem erdos_338_bateman_succ (h : ℕ) :
    IsBasisOfOrder (batemanSet (h + 3)) (h + 3) ∧ ¬ IsBasisOfOrder (batemanSet (h + 3)) (h + 2) ∧
      ∀ t, ¬ HasRestrictedOrder (batemanSet (h + 3)) t := by
  refine ⟨bateman_isBasis (by omega), ?_, fun t => bateman_no_restricted (by omega) t⟩
  simpa using bateman_not_isBasis (H := h + 3) (by omega)

/-- The same statement for every `h ≥ 3`, as on the problem page. -/
theorem erdos_338_bateman (h : ℕ) (hh : 3 ≤ h) :
    IsBasisOfOrder (batemanSet h) h ∧ ¬ IsBasisOfOrder (batemanSet h) (h - 1) ∧
      ∀ t, ¬ HasRestrictedOrder (batemanSet h) t := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 3 := ⟨h - 3, by omega⟩
  simpa using erdos_338_bateman_succ k

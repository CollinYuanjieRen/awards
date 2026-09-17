import Mathlib

/-!
# Erdős Problem #1204: `B(k) < A(k)` for admissible sequences

A sequence of integers `0 ≤ a₁ < ⋯ < a_k` is *admissible* if it misses at least one congruence
class modulo every prime `p`.  Let `A(k) = min a_k` and `B(k) = min (a₁ + ⋯ + a_k)/k` over
admissible sequences of length `k`.  Erdős (attributing the problem to Elliott) asked to estimate
`A(k)` — in particular whether `A(k) ∼ k log k` — and `B(k)` (OPEN; not addressed here, nor the
Elliott / Davenport / Hensley–Richards bounds).  The problem page records: "It is trivial that
`B(k) < A(k)`."  This file proves that remark for every `k ≥ 2`: an admissible sequence
attaining `A(k)` has average strictly below its last term, since `a₁ < a_k`.  (For `k = 1` the
sequence `(0)` is admissible and `A(1) = B(1) = 0`, so `k ≥ 2` is needed.)

There is no formal-conjectures statement for #1204, so the definitions are ours: a sequence of
length `k` is a strictly increasing `a : Fin k → ℕ`, admissible when for every prime `p` some
residue `r < p` is avoided by all `a i % p` (the bound `r < p` is essential: without it `r = p`
would trivially witness the condition); `A k` is the least last term (the least
`Finset.univ.sup a`) and `kB k` the least total `∑ i, a i` over admissible sequences, so that
`B(k) = kB k / k` (the minimum of the averages is the minimum of the totals divided by `k`).
-/

open Finset

/-- `a : Fin k → ℕ` is *admissible* if it is strictly increasing and misses at least one
congruence class `r ∈ {0, …, p − 1}` modulo every prime `p`. -/
def IsAdmissible {k : ℕ} (a : Fin k → ℕ) : Prop :=
  StrictMono a ∧ ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ i, a i % p ≠ r

/-- The admissible sequences of length `k`. -/
def admissibleSeqs (k : ℕ) : Set (Fin k → ℕ) := {a | IsAdmissible a}

/-- `A(k) = min a_k`: the least last term (= largest term) of an admissible sequence of
length `k`. -/
noncomputable def A (k : ℕ) : ℕ :=
  sInf ((fun a : Fin k → ℕ => Finset.univ.sup a) '' admissibleSeqs k)

/-- `k · B(k) = min (a₁ + ⋯ + a_k)`: the least total of an admissible sequence of length `k`. -/
noncomputable def kB (k : ℕ) : ℕ :=
  sInf ((fun a : Fin k → ℕ => ∑ i, a i) '' admissibleSeqs k)

/-- Admissible sequences of every length exist, e.g. `a_i = 1 + i · k!`: for `p ≤ k` every term
is `1 (mod p)`, and for `p > k` the `k` residues cannot cover all `p` classes. -/
theorem admissibleSeqs_nonempty (k : ℕ) : (admissibleSeqs k).Nonempty := by
  refine ⟨fun i => 1 + (i : ℕ) * Nat.factorial k, ?_⟩
  show IsAdmissible _
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij' (Nat.factorial_pos k)) 1
  · intro p hp
    by_cases hpk : p ≤ k
    · obtain ⟨c, hc⟩ : p ∣ Nat.factorial k := Nat.dvd_factorial hp.pos hpk
      refine ⟨0, hp.pos, fun i => ?_⟩
      show (1 + (i : ℕ) * Nat.factorial k) % p ≠ 0
      have hrw : (i : ℕ) * Nat.factorial k = p * ((i : ℕ) * c) := by rw [hc]; ring
      rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.one_lt]
      exact one_ne_zero
    · have hkp : k < p := by omega
      have hcard :
          ((Finset.univ : Finset (Fin k)).image
            (fun i : Fin k => (1 + (i : ℕ) * Nat.factorial k) % p)).card
            < (Finset.range p).card := by
        calc ((Finset.univ : Finset (Fin k)).image
              (fun i : Fin k => (1 + (i : ℕ) * Nat.factorial k) % p)).card
            ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
          _ = k := by simp
          _ < p := hkp
          _ = (Finset.range p).card := (Finset.card_range p).symm
      obtain ⟨r, hrp, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      exact ⟨r, Finset.mem_range.mp hrp,
        fun i hi => hr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)⟩

/-- A strictly increasing sequence of length `k ≥ 2` has total strictly less than `k` times its
largest term. -/
theorem sum_lt_card_mul_sup {k : ℕ} (hk : 2 ≤ k) (a : Fin k → ℕ) (ha : StrictMono a) :
    ∑ i, a i < k * Finset.univ.sup a := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin (m + 2))), a i ≤ Finset.univ.sup a :=
    fun i _ => Finset.le_sup (Finset.mem_univ i)
  have hlt : a 0 < Finset.univ.sup a :=
    lt_of_lt_of_le (ha (show (0 : Fin (m + 2)) < Fin.last (m + 1) from Fin.lt_def.mpr (by simp)))
      (Finset.le_sup (Finset.mem_univ (Fin.last (m + 1))))
  simpa using Finset.sum_lt_sum hle ⟨0, Finset.mem_univ 0, hlt⟩

/-- The integer form of `B(k) < A(k)`: `k · B(k) < k · A(k)` for `k ≥ 2`. -/
theorem kB_lt_mul_A (k : ℕ) (hk : 2 ≤ k) : kB k < k * A k := by
  obtain ⟨a, ha, hA⟩ :=
    Nat.sInf_mem ((admissibleSeqs_nonempty k).image (fun a : Fin k → ℕ => Finset.univ.sup a))
  have hmem : IsAdmissible a := ha
  have h1 : kB k ≤ ∑ i, a i := Nat.sInf_le ⟨a, ha, rfl⟩
  have h2 : ∑ i, a i < k * Finset.univ.sup a := sum_lt_card_mul_sup hk a hmem.1
  have hA' : Finset.univ.sup a = A k := hA
  rw [hA'] at h2
  exact lt_of_le_of_lt h1 h2

/-- **Erdős #1204, the page's remark**: `B(k) < A(k)` for every `k ≥ 2`. -/
theorem erdos_1204_B_lt_A (k : ℕ) (hk : 2 ≤ k) : (kB k : ℚ) / k < A k := by
  have hk0 : (0 : ℚ) < (k : ℚ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  rw [div_lt_iff₀ hk0, mul_comm]
  exact_mod_cast kB_lt_mul_A k hk

/-- Closed form of `erdos_1204_B_lt_A`. -/
theorem erdos_1204_B_lt_A_closed : ¬ ∃ k : ℕ, 2 ≤ k ∧ (A k : ℚ) ≤ (kB k : ℚ) / k := by
  rintro ⟨k, hk, h⟩
  exact absurd (erdos_1204_B_lt_A k hk) (not_lt.mpr h)

import Mathlib

/-!
# Erdős Problem #1187, second question: no, by colouring modulo `4`

Erdős asked (for `k ≥ 3`) whether every finite colouring of the integers contains (i) a
monochromatic `k`-term arithmetic progression of primes — yes, by Green–Tao, NOT formalized
here — and (ii) a monochromatic `k`-term arithmetic progression whose common difference is a
prime.  The problem page records that "the answer to the second question is trivially no:
colouring the integers by their residue modulo `4` creates a colouring in which there is not
even any monochromatic pair of integers whose difference is a prime.  Alternatively, one can
just use `2` colours and avoid any `3`-term progressions whose difference is a prime by
colouring `0, 1 (mod 4)` red and `2, 3 (mod 4)` blue."  This file proves both colourings work:

* `colourMod4 n = (n : ZMod 4)` (four colours): `colourMod4 a ≠ colourMod4 (a + p)` for every
  integer `a` and prime `p`, hence no monochromatic progression of length `≥ 2` with prime
  common difference (`no_mono_ap_colourMod4`);
* `colourTwo n = decide (n % 4 < 2)` (two colours): no monochromatic `3`-term progression with
  prime common difference (`colourTwo_no_three_ap`).

There is no formal-conjectures rendering of this problem; the definitions are ours.  Colourings
are of `ℤ` (the page's "the integers"); restricting to positive integers gives the same
conclusion.  Nothing about the first question is claimed.
-/

namespace Erdos1187

/-- The colouring of the integers by residue modulo `4`. -/
def colourMod4 (n : ℤ) : ZMod 4 := (n : ZMod 4)

/-- The two-colouring: `0, 1 (mod 4)` red (`true`), `2, 3 (mod 4)` blue (`false`). -/
def colourTwo (n : ℤ) : Bool := decide (n % 4 < 2)

/-- Under `colourMod4`, no two integers at prime distance share a colour. -/
theorem colourMod4_ne_add_prime (a : ℤ) (p : ℕ) (hp : p.Prime) :
    colourMod4 a ≠ colourMod4 (a + p) := by
  unfold colourMod4
  intro h
  have h4 : ((4 : ℕ) : ℤ) ∣ (a + (p : ℤ)) - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  rw [add_sub_cancel_left] at h4
  have h4' : (4 : ℕ) ∣ p := Int.natCast_dvd_natCast.mp h4
  rcases hp.eq_one_or_self_of_dvd 4 h4' with h1 | h1
  · omega
  · subst h1
    exact absurd hp (by norm_num)

/-- Under `colourMod4`, there is no monochromatic arithmetic progression of length `k ≥ 2` with
prime common difference. -/
theorem no_mono_ap_colourMod4 (k : ℕ) (hk : 2 ≤ k) (a : ℤ) (p : ℕ) (hp : p.Prime) :
    ¬ ∀ i < k, colourMod4 (a + i * p) = colourMod4 a := by
  intro h
  have h1 := h 1 (by omega)
  simp only [Nat.cast_one, one_mul] at h1
  exact colourMod4_ne_add_prime a p hp h1.symm

/-- Under `colourTwo`, there is no monochromatic `3`-term arithmetic progression with prime
common difference. -/
theorem colourTwo_no_three_ap (a : ℤ) (p : ℕ) (hp : p.Prime) :
    ¬ (colourTwo a = colourTwo (a + p) ∧ colourTwo (a + p) = colourTwo (a + 2 * p)) := by
  unfold colourTwo
  simp only [decide_eq_decide]
  rintro ⟨h1, h2⟩
  rcases hp.eq_two_or_odd' with rfl | hodd
  · push_cast at h1 h2
    omega
  · obtain ⟨m, rfl⟩ := hodd
    push_cast at h1 h2
    omega

end Erdos1187

/-- **Erdős #1187, second question (answer: no), closed form**: there is a `4`-colouring of the
integers with no monochromatic pair at prime distance, and a `2`-colouring with no monochromatic
`3`-term progression of prime common difference. -/
theorem erdos_1187_second_question_closed :
    (∃ c : ℤ → Fin 4, ∀ (a : ℤ) (p : ℕ), p.Prime → c a ≠ c (a + p)) ∧
      (∃ c : ℤ → Bool, ∀ (a : ℤ) (p : ℕ), p.Prime →
        ¬ (c a = c (a + p) ∧ c (a + p) = c (a + 2 * p))) := by
  exact ⟨⟨Erdos1187.colourMod4, Erdos1187.colourMod4_ne_add_prime⟩,
    ⟨Erdos1187.colourTwo, Erdos1187.colourTwo_no_three_ap⟩⟩

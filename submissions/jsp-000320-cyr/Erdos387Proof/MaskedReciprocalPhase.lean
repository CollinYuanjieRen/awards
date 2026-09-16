import ErdosProblems.Erdos387.BezoutAdditiveCharacter
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic

/-!
# Masked reciprocal phases with arbitrary paired integer shifts

The mask retains every original denominator, even when poles cancel after
subtraction. CRT is applied to inverses only on the unit locus.
The elementary CRT inverse proof below is adapted from plby/lean-proofs,
commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
Erdos387/KloostermanMultiplicativity.lean; no analytic estimate is imported.
-/

namespace Erdos387Proof.MaskedReciprocalPhase

open scoped ComplexConjugate

/-- An iterated difference of a reciprocal phase. All shifts are integers. -/
noncomputable def phase (q : ℕ) (c a : ℤ) : List (ℤ × ℤ) → ℤ → ZMod q
  | [], n => (c : ZMod q) * ((a + n : ℤ) : ZMod q)⁻¹
  | (u,v) :: hs, n => phase q c a hs (n + u) - phase q c a hs (n + v)

/-- All original denominators are units, including ones whose poles cancel. -/
def good (q : ℕ) (a : ℤ) : List (ℤ × ℤ) → ℤ → Prop
  | [], n => IsUnit ((a + n : ℤ) : ZMod q)
  | (u,v) :: hs, n => good q a hs (n + u) ∧ good q a hs (n + v)

noncomputable def seq (q : ℕ) [NeZero q] (c a : ℤ) (hs : List (ℤ × ℤ)) (n : ℤ) : ℂ := by
  classical
  exact if good q a hs n then ZMod.stdAddChar (phase q c a hs n) else 0

theorem norm_seq_le (q : ℕ) [NeZero q] (c a : ℤ)
    (hs : List (ℤ × ℤ)) (n : ℤ) : ‖seq q c a hs n‖ ≤ 1 := by
  classical
  unfold seq
  split_ifs <;> simp [AddChar.norm_apply]

theorem phase_periodic (q : ℕ) (c a : ℤ) (hs : List (ℤ × ℤ)) :
    Function.Periodic (phase q c a hs) (q : ℤ) := by
  induction hs with
  | nil => intro n; simp [phase, Int.cast_add]
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    intro n
    simp only [phase]
    rw [show n + q + u = (n + u) + q by omega,
      show n + q + v = (n + v) + q by omega, ih (n+u), ih (n+v)]

theorem good_periodic (q : ℕ) (a : ℤ) (hs : List (ℤ × ℤ)) :
    Function.Periodic (good q a hs) (q : ℤ) := by
  induction hs with
  | nil => intro n; simp [good, Int.cast_add]
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    intro n
    simp only [good]
    rw [show n + q + u = (n + u) + q by omega,
      show n + q + v = (n + v) + q by omega, ih (n+u), ih (n+v)]

theorem seq_periodic (q : ℕ) [NeZero q] (c a : ℤ) (hs : List (ℤ × ℤ)) :
    Function.Periodic (seq q c a hs) (q : ℤ) := by
  intro n
  unfold seq
  rw [good_periodic q a hs n, phase_periodic q c a hs n]

/-- Correlation introduces precisely the conjunction of the two shifted masks. -/
theorem seq_cons (q : ℕ) [NeZero q] (c a : ℤ) (hs : List (ℤ × ℤ)) (u v n : ℤ) :
    seq q c a ((u,v)::hs) n =
      seq q c a hs (n+u) * conj (seq q c a hs (n+v)) := by
  classical
  unfold seq
  simp only [good, phase]
  by_cases hu : good q a hs (n+u) <;>
    by_cases hv : good q a hs (n+v) <;>
    simp [hu, hv, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]

/-- Unit-locus inverse compatibility; no inverse map is claimed off this locus. -/
theorem crt_inv_of_isUnit {s t : ℕ} (hcop : Nat.Coprime s t)
    (x : ZMod (s*t)) (hx : IsUnit x) :
    ZMod.chineseRemainder hcop x⁻¹ =
      ((ZMod.chineseRemainder hcop x).1⁻¹,
        (ZMod.chineseRemainder hcop x).2⁻¹) := by
  let e := ZMod.chineseRemainder hcop
  have hmul : e x * e x⁻¹ = 1 := by
    rw [← e.map_mul]
    simpa using congrArg e (ZMod.mul_inv_of_unit x hx)
  apply Prod.ext
  · have hf : (e x).1 * (e x⁻¹).1 = 1 := congrArg Prod.fst hmul
    exact (ZMod.inv_eq_of_mul_eq_one s (e x).1 (e x⁻¹).1 hf).symm
  · have ht : (e x).2 * (e x⁻¹).2 = 1 := congrArg Prod.snd hmul
    exact (ZMod.inv_eq_of_mul_eq_one t (e x).2 (e x⁻¹).2 ht).symm

theorem isUnit_intCast_mul_iff (s t : ℕ) (hcop : Nat.Coprime s t) (x : ℤ) :
    IsUnit (x : ZMod (s*t)) ↔ IsUnit (x : ZMod s) ∧ IsUnit (x : ZMod t) := by
  let e := ZMod.chineseRemainder hcop
  have he : e (x : ZMod (s*t)) = ((x : ZMod s), (x : ZMod t)) := by
    apply Prod.ext <;> simp [e]
  constructor
  · intro hx
    have h := hx.map e.toRingHom
    change IsUnit (e (x : ZMod (s*t))) at h
    rw [he, Prod.isUnit_iff] at h
    exact h
  · intro hx
    have h : IsUnit (e (x : ZMod (s*t))) := by
      rw [he, Prod.isUnit_iff]
      exact hx
    exact (MulEquiv.isUnit_map e).mp h

/-- CRT splits the full original-denominator mask, not merely surviving poles. -/
theorem good_mul_iff (s t : ℕ) (hcop : Nat.Coprime s t)
    (a : ℤ) (hs : List (ℤ × ℤ)) (n : ℤ) :
    good (s*t) a hs n ↔ good s a hs n ∧ good t a hs n := by
  induction hs generalizing n with
  | nil => exact isUnit_intCast_mul_iff s t hcop (a+n)
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    simp only [good, ih]
    tauto

private theorem seq_nil_mul (s t : ℕ) [NeZero s] [NeZero t]
    (hcop : Nat.Coprime s t) (c a n : ℤ) :
    seq (s*t) c a [] n =
      seq s (c * Nat.gcdB s t) a [] n * seq t (c * Nat.gcdA s t) a [] n := by
  classical
  let e := ZMod.chineseRemainder hcop
  have hu := isUnit_intCast_mul_iff s t hcop (a+n)
  change good (s*t) a [] n ↔ good s a [] n ∧ good t a [] n at hu
  unfold seq
  by_cases hx : good (s*t) a [] n
  · obtain ⟨hs,ht⟩ := hu.mp hx
    rw [if_pos hx, if_pos hs, if_pos ht]
    simp only [phase]
    rw [Erdos387.BezoutAdditiveCharacter.stdAddChar_product_crt s t hcop]
    have hi := crt_inv_of_isUnit hcop ((a+n : ℤ) : ZMod (s*t)) hx
    have hc : e (c : ZMod (s*t)) = ((c : ZMod s), (c : ZMod t)) := by apply Prod.ext <;> simp [e]
    have hd : e ((a+n : ℤ) : ZMod (s*t)) =
        (((a+n : ℤ) : ZMod s), ((a+n : ℤ) : ZMod t)) := by apply Prod.ext <;> simp [e]
    change ZMod.stdAddChar ((e ((c : ZMod (s*t)) * _)).2 * _) *
      ZMod.stdAddChar ((e ((c : ZMod (s*t)) * _)).1 * _) = _
    rw [e.map_mul, hi, hc, hd]
    simp only [Prod.fst_mul, Prod.snd_mul, Int.cast_mul]
    rw [mul_comm]
    congr 1 <;> congr 1 <;> ring
  · rw [if_neg hx]
    by_cases hs : good s a [] n
    · have ht : ¬good t a [] n := fun ht => hx (hu.mpr ⟨hs,ht⟩)
      rw [if_neg ht, mul_zero]
    · rw [if_neg hs, zero_mul]

/-- Exact factorization of masked paired reciprocal phases over coprime moduli.
The `s` coordinate carries `gcdB`; the `t` coordinate carries `gcdA`. -/
theorem seq_mul (s t : ℕ) [NeZero s] [NeZero t]
    (hcop : Nat.Coprime s t) (c a : ℤ) (hs : List (ℤ × ℤ)) (n : ℤ) :
    seq (s*t) c a hs n =
      seq s (c * Nat.gcdB s t) a hs n * seq t (c * Nat.gcdA s t) a hs n := by
  induction hs generalizing n with
  | nil => exact seq_nil_mul s t hcop c a n
  | cons h hs ih =>
    rcases h with ⟨u,v⟩
    rw [seq_cons, seq_cons, seq_cons, ih (n+u), ih (n+v), map_mul]
    ring

end Erdos387Proof.MaskedReciprocalPhase

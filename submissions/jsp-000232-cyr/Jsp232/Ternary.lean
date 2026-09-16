/-
JSP-000232 / Erdős #271 — base-3 combinatorics used for the Stanley sequence `A(1)`.

This file is independent of `Jsp232.Defs`: it only develops the arithmetic of natural numbers
whose base-3 expansion avoids the digit `2`, the "binary expansion read in base 3" map
`binToTer`, and the two digit-repair maps `dropTwo` (`2 ↦ 0`) and `lowerTwo` (`2 ↦ 1`).
-/
import Mathlib

namespace Erdos271

/-! ### Numbers without the digit `2` in base 3 -/

/-- `NoTwo m`: the base-3 expansion of `m` contains no digit `2`. -/
def NoTwo (m : ℕ) : Prop := 2 ∉ Nat.digits 3 m

theorem noTwo_zero : NoTwo 0 := by
  simp [NoTwo]

theorem noTwo_iff (m : ℕ) : NoTwo m ↔ m % 3 ≠ 2 ∧ NoTwo (m / 3) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [NoTwo]
  · rw [NoTwo, Nat.digits_def' (by norm_num : (1 : ℕ) < 3) hm]
    constructor
    · intro h
      refine ⟨fun h' => h (List.mem_cons.2 (Or.inl h'.symm)), fun h' =>
        h (List.mem_cons.2 (Or.inr h'))⟩
    · rintro ⟨h1, h2⟩ h
      rcases List.mem_cons.1 h with h | h
      · exact h1 h.symm
      · exact h2 h

theorem noTwo_iff_forall (m : ℕ) : NoTwo m ↔ ∀ d ∈ Nat.digits 3 m, d ≠ 2 := by
  constructor
  · intro h d hd hd2
    exact h (hd2 ▸ hd)
  · intro h hm
    exact h 2 hm rfl

private theorem noTwo_eq_aux :
    ∀ b a c : ℕ, NoTwo a → NoTwo b → NoTwo c → a + c = 2 * b → a = c := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a c ha hb hc h
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · omega
    · obtain ⟨ha1, ha2⟩ := (noTwo_iff a).1 ha
      obtain ⟨hb1, hb2⟩ := (noTwo_iff b).1 hb
      obtain ⟨hc1, hc2⟩ := (noTwo_iff c).1 hc
      have key : a / 3 + c / 3 = 2 * (b / 3) := by omega
      have key2 : a % 3 = c % 3 := by omega
      have := ih (b / 3) (Nat.div_lt_self hb0 (by norm_num)) (a / 3) (c / 3) ha2 hb2 hc2 key
      omega

/-- three numbers with no digit 2 in base 3 never form an AP unless trivial -/
theorem NoTwo.eq_of_add_eq_two_mul {a b c : ℕ} (ha : NoTwo a) (hb : NoTwo b) (hc : NoTwo c)
    (h : a + c = 2 * b) : a = c :=
  noTwo_eq_aux b a c ha hb hc h

/-! ### The binary expansion of `k` read in base 3 -/

/-- the binary expansion of `k`, read in base 3 -/
def binToTer : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * binToTer ((k + 1) / 2) + (k + 1) % 2
decreasing_by omega

theorem binToTer_zero : binToTer 0 = 0 := by
  simp [binToTer]

theorem binToTer_eq (k : ℕ) : binToTer k = 3 * binToTer (k / 2) + k % 2 := by
  cases k with
  | zero => simp [binToTer]
  | succ n => rw [binToTer]

theorem binToTer_one : binToTer 1 = 1 := by
  rw [binToTer_eq]
  simp [binToTer_zero]

theorem binToTer_eq_ofDigits (k : ℕ) : binToTer k = Nat.ofDigits 3 (Nat.digits 2 k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [binToTer_zero]
    · rw [binToTer_eq, Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hk, Nat.ofDigits_cons,
        ih (k / 2) (Nat.div_lt_self hk (by norm_num))]
      ring

private theorem binToTer_lt_aux : ∀ k j : ℕ, j < k → binToTer j < binToTer k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hj
    have hk : 0 < k := by omega
    have ej := binToTer_eq j
    have ek := binToTer_eq k
    rcases lt_or_eq_of_le (Nat.div_le_div_right (Nat.le_of_lt hj) : j / 2 ≤ k / 2) with h | h
    · have := ih (k / 2) (Nat.div_lt_self hk (by norm_num)) (j / 2) h
      omega
    · rw [h] at ej
      omega

theorem binToTer_strictMono : StrictMono binToTer := fun _ _ h => binToTer_lt_aux _ _ h

private theorem noTwo_binToTer_aux : ∀ k : ℕ, NoTwo (binToTer k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [binToTer_zero]
      exact noTwo_zero
    · have e := binToTer_eq k
      rw [noTwo_iff]
      have hmod : binToTer k % 3 = k % 2 := by omega
      have hdiv : binToTer k / 3 = binToTer (k / 2) := by omega
      rw [hmod, hdiv]
      exact ⟨by omega, ih (k / 2) (Nat.div_lt_self hk (by norm_num))⟩

theorem noTwo_binToTer (k : ℕ) : NoTwo (binToTer k) := noTwo_binToTer_aux k

private theorem exists_binToTer_aux : ∀ m : ℕ, NoTwo m → ∃ k, binToTer k = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact ⟨0, binToTer_zero⟩
    · obtain ⟨h1, h2⟩ := (noTwo_iff m).1 hm
      obtain ⟨k', hk'⟩ := ih (m / 3) (Nat.div_lt_self hm0 (by norm_num)) h2
      refine ⟨2 * k' + m % 3, ?_⟩
      have e := binToTer_eq (2 * k' + m % 3)
      have hd : (2 * k' + m % 3) / 2 = k' := by omega
      have hr : (2 * k' + m % 3) % 2 = m % 3 := by omega
      rw [hd, hr] at e
      omega

theorem exists_binToTer_eq {m : ℕ} (hm : NoTwo m) : ∃ k, binToTer k = m :=
  exists_binToTer_aux m hm

private theorem binToTer_bounds_aux : ∀ k : ℕ, 0 < k →
    3 ^ Nat.log 2 k ≤ binToTer k ∧ binToTer k < 3 ^ (Nat.log 2 k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have hk1 : k = 1 := by omega
      subst hk1
      norm_num [binToTer_one, Nat.log_one_right]
    · have hj : 0 < k / 2 := by omega
      obtain ⟨h3, h4⟩ := ih (k / 2) (Nat.div_lt_self hk (by norm_num)) hj
      have hlog : Nat.log 2 k = Nat.log 2 (k / 2) + 1 := by
        have hd := Nat.log_div_base 2 k
        have hp := Nat.log_pos (b := 2) (n := k) (by norm_num) h2
        omega
      have e := binToTer_eq k
      have hsucc : (3 : ℕ) ^ (Nat.log 2 (k / 2) + 1) = 3 * 3 ^ Nat.log 2 (k / 2) := by ring
      have hsucc2 : (3 : ℕ) ^ (Nat.log 2 (k / 2) + 1 + 1) = 3 * 3 ^ (Nat.log 2 (k / 2) + 1) := by
        ring
      rw [hlog, hsucc, hsucc2]
      omega

/-- growth: for `k ≥ 1`, `3 ^ log₂ k ≤ binToTer k < 3 ^ (log₂ k + 1)` -/
theorem binToTer_bounds {k : ℕ} (hk : 0 < k) :
    3 ^ Nat.log 2 k ≤ binToTer k ∧ binToTer k < 3 ^ (Nat.log 2 k + 1) :=
  binToTer_bounds_aux k hk

/-! ### The digit repair maps -/

/-- digit map 2 ↦ 0 -/
def dropTwo : ℕ → ℕ
  | 0 => 0
  | m + 1 => 3 * dropTwo ((m + 1) / 3) + (if (m + 1) % 3 = 2 then 0 else (m + 1) % 3)
decreasing_by omega

/-- digit map 2 ↦ 1 -/
def lowerTwo : ℕ → ℕ
  | 0 => 0
  | m + 1 => 3 * lowerTwo ((m + 1) / 3) + (if (m + 1) % 3 = 2 then 1 else (m + 1) % 3)
decreasing_by omega

theorem dropTwo_zero : dropTwo 0 = 0 := by
  simp [dropTwo]

theorem lowerTwo_zero : lowerTwo 0 = 0 := by
  simp [lowerTwo]

theorem dropTwo_eq (m : ℕ) :
    dropTwo m = 3 * dropTwo (m / 3) + (if m % 3 = 2 then 0 else m % 3) := by
  cases m with
  | zero => simp [dropTwo]
  | succ n => rw [dropTwo]

theorem lowerTwo_eq (m : ℕ) :
    lowerTwo m = 3 * lowerTwo (m / 3) + (if m % 3 = 2 then 1 else m % 3) := by
  cases m with
  | zero => simp [lowerTwo]
  | succ n => rw [lowerTwo]

private theorem dropTwo_eq' (m : ℕ) : ∃ r < 2, dropTwo m = 3 * dropTwo (m / 3) + r := by
  refine ⟨if m % 3 = 2 then 0 else m % 3, ?_, dropTwo_eq m⟩
  split_ifs <;> omega

private theorem lowerTwo_eq' (m : ℕ) : ∃ r < 2, lowerTwo m = 3 * lowerTwo (m / 3) + r := by
  refine ⟨if m % 3 = 2 then 1 else m % 3, ?_, lowerTwo_eq m⟩
  split_ifs <;> omega

private theorem noTwo_dropTwo_aux : ∀ m : ℕ, NoTwo (dropTwo m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [dropTwo_zero]
      exact noTwo_zero
    · obtain ⟨r, hr, e⟩ := dropTwo_eq' m
      rw [noTwo_iff]
      have hmod : dropTwo m % 3 = r := by omega
      have hdiv : dropTwo m / 3 = dropTwo (m / 3) := by omega
      rw [hmod, hdiv]
      exact ⟨by omega, ih (m / 3) (Nat.div_lt_self hm (by norm_num))⟩

theorem noTwo_dropTwo (m : ℕ) : NoTwo (dropTwo m) := noTwo_dropTwo_aux m

private theorem noTwo_lowerTwo_aux : ∀ m : ℕ, NoTwo (lowerTwo m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [lowerTwo_zero]
      exact noTwo_zero
    · obtain ⟨r, hr, e⟩ := lowerTwo_eq' m
      rw [noTwo_iff]
      have hmod : lowerTwo m % 3 = r := by omega
      have hdiv : lowerTwo m / 3 = lowerTwo (m / 3) := by omega
      rw [hmod, hdiv]
      exact ⟨by omega, ih (m / 3) (Nat.div_lt_self hm (by norm_num))⟩

theorem noTwo_lowerTwo (m : ℕ) : NoTwo (lowerTwo m) := noTwo_lowerTwo_aux m

private theorem dropTwo_add_self_aux : ∀ m : ℕ, dropTwo m + m = 2 * lowerTwo m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [dropTwo_zero, lowerTwo_zero]
    · have ihm := ih (m / 3) (Nat.div_lt_self hm (by norm_num))
      have e1 := dropTwo_eq m
      have e2 := lowerTwo_eq m
      split_ifs at e1 e2 <;> omega

theorem dropTwo_add_self (m : ℕ) : dropTwo m + m = 2 * lowerTwo m := dropTwo_add_self_aux m

private theorem lowerTwo_le_aux : ∀ m : ℕ, lowerTwo m ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [lowerTwo_zero]
    · have e := lowerTwo_eq m
      have := ih (m / 3) (Nat.div_lt_self hm (by norm_num))
      split_ifs at e <;> omega

theorem lowerTwo_le (m : ℕ) : lowerTwo m ≤ m := lowerTwo_le_aux m

private theorem lowerTwo_lt_aux : ∀ m : ℕ, ¬ NoTwo m → lowerTwo m < m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact absurd noTwo_zero hm
    · have hnot := (noTwo_iff m).not.1 hm
      have hle := lowerTwo_le (m / 3)
      have e := lowerTwo_eq m
      split_ifs at e with h
      · omega
      · have h2 : ¬ NoTwo (m / 3) := by tauto
        have := ih (m / 3) (Nat.div_lt_self hm0 (by norm_num)) h2
        omega

theorem lowerTwo_lt {m : ℕ} (hm : ¬ NoTwo m) : lowerTwo m < m := lowerTwo_lt_aux m hm

theorem dropTwo_le_lowerTwo (m : ℕ) : dropTwo m ≤ lowerTwo m := by
  have h1 := dropTwo_add_self m
  have h2 := lowerTwo_le m
  omega

theorem dropTwo_lt_lowerTwo {m : ℕ} (hm : ¬ NoTwo m) : dropTwo m < lowerTwo m := by
  have h1 := dropTwo_add_self m
  have h2 := lowerTwo_lt hm
  omega

end Erdos271

/-! ### Axiom audit -/

#print axioms Erdos271.noTwo_zero
#print axioms Erdos271.noTwo_iff
#print axioms Erdos271.noTwo_iff_forall
#print axioms Erdos271.NoTwo.eq_of_add_eq_two_mul
#print axioms Erdos271.binToTer_zero
#print axioms Erdos271.binToTer_eq
#print axioms Erdos271.binToTer_eq_ofDigits
#print axioms Erdos271.binToTer_strictMono
#print axioms Erdos271.noTwo_binToTer
#print axioms Erdos271.exists_binToTer_eq
#print axioms Erdos271.binToTer_bounds
#print axioms Erdos271.noTwo_dropTwo
#print axioms Erdos271.noTwo_lowerTwo
#print axioms Erdos271.dropTwo_add_self
#print axioms Erdos271.lowerTwo_lt
#print axioms Erdos271.dropTwo_lt_lowerTwo
#print axioms Erdos271.lowerTwo_le
#print axioms Erdos271.dropTwo_le_lowerTwo

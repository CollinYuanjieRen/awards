import Proof.Lcm

/-!
# Erdős problem #317: the non-strict lower bound for non-zero signed harmonic sums

The problem page asks, as its second question, whether for sufficiently large `n` every choice
of signs `δ_k ∈ {−1, 0, 1}` with `Σ_{1 ≤ k ≤ n} δ_k/k ≠ 0` satisfies
`|Σ_{1 ≤ k ≤ n} δ_k/k| > 1/[1, …, n]`, and it calls the non-strict inequality obvious, the
difficulty being the strict inequality.

This package proves that non-strict inequality, and proves it for *every* `n` rather than only
for sufficiently large `n`: writing `L = [1, …, n]`, each `k ≤ n` divides `L`, so
`L · Σ_{k ≤ n} δ_k/k = Σ_{k ≤ n} δ_k · (L/k)` is an integer; if the sum is non-zero this integer
is non-zero, hence has absolute value at least `1`, and `|Σ δ_k/k| ≥ 1/L` follows. The page's own
equality instance `1/2 − 1/3 − 1/4 = −1/12 = −1/[1, …, 4]` is included as well, witnessing that
the strict inequality genuinely fails for small `n`.

Not claimed here: the first question of Erdős problem #317 (a signed harmonic sum below
`c/2^n`), the strict inequality `|Σ δ_k/k| > 1/[1, …, n]` for sufficiently large `n`, and the
Kovač–van Doorn bounds.
-/

namespace Erdos317

/-- `IsSign δ` says that every coefficient `δ k` lies in `{−1, 0, 1}`. -/
def IsSign (δ : ℕ → ℚ) : Prop := ∀ k, δ k = -1 ∨ δ k = 0 ∨ δ k = 1

/-- `signedSum n δ` is the signed harmonic sum `Σ_{1 ≤ k ≤ n} δ_k / k`, computed in `ℚ`. -/
def signedSum (n : ℕ) (δ : ℕ → ℚ) : ℚ := ∑ k ∈ Finset.Icc 1 n, δ k / k

/-- Integrality: `[1, …, n] · Σ_{k ≤ n} δ_k/k` is an integer, because every `k ≤ n` divides
`[1, …, n]` and every `δ k` is one of `−1`, `0`, `1`. -/
theorem exists_int_mul (n : ℕ) (δ : ℕ → ℚ) (hδ : IsSign δ) :
    ∃ z : ℤ, (lcmUpTo n : ℚ) * signedSum n δ = z := by
  classical
  have hint : ∀ k : ℕ, ∃ e : ℤ, δ k = (e : ℚ) := by
    intro k
    rcases hδ k with h | h | h
    · exact ⟨-1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, ∀ k, δ k = ((e k : ℤ) : ℚ) :=
    ⟨fun k => Classical.choose (hint k), fun k => Classical.choose_spec (hint k)⟩
  refine ⟨∑ k ∈ Finset.Icc 1 n, e k * ((lcmUpTo n / k : ℕ) : ℤ), ?_⟩
  rw [signedSum, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have h1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdvd : k ∣ lcmUpTo n := dvd_lcmUpTo hk
  rw [he k, Nat.cast_div hdvd hk0]
  ring

/-- (T2) If a signed harmonic sum of length `n` is non-zero, its absolute value is at least
`1/[1, …, n]`. -/
theorem one_div_lcm_le_abs_signedSum (n : ℕ) (δ : ℕ → ℚ) (hδ : IsSign δ) (h : signedSum n δ ≠ 0) :
    1 / (lcmUpTo n : ℚ) ≤ |signedSum n δ| := by
  obtain ⟨z, hz⟩ := exists_int_mul n δ hδ
  have hL : (0 : ℚ) < (lcmUpTo n : ℚ) := Nat.cast_pos.2 (lcmUpTo_pos n)
  have hprod : (lcmUpTo n : ℚ) * signedSum n δ ≠ 0 := mul_ne_zero (ne_of_gt hL) h
  have hzne : z ≠ 0 := by
    rintro rfl
    exact hprod (by simpa using hz)
  have h1 : (1 : ℚ) ≤ |(z : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hzne
  have habs : |(lcmUpTo n : ℚ) * signedSum n δ| = (lcmUpTo n : ℚ) * |signedSum n δ| := by
    rw [abs_mul, abs_of_pos hL]
  have h2 : (1 : ℚ) ≤ (lcmUpTo n : ℚ) * |signedSum n δ| := by
    rw [← habs, hz]
    exact h1
  rw [div_le_iff₀ hL, mul_comm]
  exact h2

/-- (T1) No signed harmonic sum of length `n` is non-zero and yet smaller than `1/[1, …, n]`
in absolute value. -/
theorem not_exists_small_signedSum (n : ℕ) :
    ¬ ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum n δ ≠ 0 ∧ |signedSum n δ| < 1 / (lcmUpTo n : ℚ) := by
  rintro ⟨δ, hδ, h, hlt⟩
  exact absurd (one_div_lcm_le_abs_signedSum n δ hδ h) (not_le.2 hlt)

/-- (T3) The same bound in the `Fin`-indexed encoding used by `formal-conjectures`: for
`δ : Fin n → ℚ` with values in `{−1, 0, 1}`, a non-zero `Σ_k δ_k/(k+1)` has absolute value at
least `1/[1, …, n]`. -/
theorem one_div_lcm_le_abs_fin (n : ℕ) (δ : Fin n → ℚ) (hδ : ∀ k, δ k ∈ ({-1, 0, 1} : Set ℚ))
    (h : ∑ k, δ k / (((k : ℕ) : ℚ) + 1) ≠ 0) :
    1 / (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) ≤ |∑ k, δ k / (((k : ℕ) : ℚ) + 1)| := by
  classical
  set δ' : ℕ → ℚ := fun m => if hm : m - 1 < n then δ ⟨m - 1, hm⟩ else 0 with hδ'def
  have hsign : IsSign δ' := by
    intro m
    simp only [hδ'def]
    by_cases hm : m - 1 < n
    · simp only [hm, ↓reduceDIte]
      have := hδ ⟨m - 1, hm⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      exact this
    · simp [hm]
  have hre : signedSum n δ' = ∑ k, δ k / (((k : ℕ) : ℚ) + 1) := by
    rw [signedSum]
    refine (Finset.sum_bij' (fun (k : Fin n) _ => (k : ℕ) + 1)
      (fun (m : ℕ) (hm : m ∈ Finset.Icc 1 n) => (⟨m - 1, by
        have := Finset.mem_Icc.1 hm; omega⟩ : Fin n))
      (fun k _ => Finset.mem_Icc.2 ⟨by omega, k.isLt⟩)
      (fun m _ => Finset.mem_univ _)
      (fun k _ => by simp)
      (fun m hm => by
        have h := Finset.mem_Icc.1 hm
        show m - 1 + 1 = m
        omega)
      (fun k _ => ?_)).symm
    simp only [hδ'def, Nat.add_sub_cancel, k.isLt, ↓reduceDIte, Fin.eta, Nat.cast_add,
      Nat.cast_one]
  rw [← hre]
  rw [← hre] at h
  exact one_div_lcm_le_abs_signedSum n δ' hsign h

/-- (T4) The page's equality instance at `n = 4`: with `δ = (0, 1, −1, −1)` the signed harmonic
sum is `1/2 − 1/3 − 1/4 = −1/12`, whose absolute value is exactly `1/[1, …, 4] = 1/12`, so the
strict inequality fails for small `n`. -/
theorem exists_signedSum_eq_one_div_lcm :
    ∃ δ : ℕ → ℚ, IsSign δ ∧ signedSum 4 δ ≠ 0 ∧ |signedSum 4 δ| = 1 / (lcmUpTo 4 : ℚ) := by
  classical
  have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  have hsum : signedSum 4 (fun k => if k = 2 then (1 : ℚ) else if k = 3 ∨ k = 4 then -1 else 0)
      = -1 / 12 := by
    rw [signedSum, hIcc]
    norm_num
  have hlcm : (lcmUpTo 4 : ℚ) = 12 := by
    have h : lcmUpTo 4 = 12 := by decide
    rw [h]
    norm_num
  refine ⟨fun k => if k = 2 then (1 : ℚ) else if k = 3 ∨ k = 4 then -1 else 0, ?_, ?_, ?_⟩
  · intro k
    dsimp only
    split_ifs <;> simp
  · rw [hsum]
    norm_num
  · rw [hsum, hlcm]
    norm_num

end Erdos317

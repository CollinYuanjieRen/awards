import Mathlib
import JSP573.FF.Counting
import JSP573.FF.Asymptotics

/-!
# Frankl–Füredi 1984, Theorem 1.3: `T(n, t) = #𝓕*(n, t)` for `n ≥ n₀(t)`

With the level inequalities in place, the proof of the upper bound `#𝓕 ≤ ffBound n t` for a
`t`-avoiding family `𝓕` on `range n` with `n` large runs as follows.

* If `𝓕` has no member of size in `(t, qBound t)`, `card_le_ffBound_add_middle` gives the bound.
* Otherwise pick `A₀ ∈ 𝓕` with `t < a := #A₀ < qBound t`, let `m = (n + t) / 2`, `b = m + 1`
  and `i₀ = n + t - b` (the partner level of `b`; `qBound t ≤ i₀ ≤ m` for `n` large). The level
  `b` omits `M ≥ C(a, t) · C(n - a, b - t) ≥ C(n - a, b - t)` sets (`level_card_le_choose_sub`),
  and the level inequality at `i₀` (note `i₀ - t = n - b`) gives
  `f_{i₀} · i₀ ≤ (C(n, b) - f_b) · (i₀ - t)`, hence
  `f_{i₀} + f_b ≤ C(n, b) - M · t / i₀`. Redoing the summation of `card_le_ffBound_add_middle`
  with this improved pair bound yields
  `#𝓕 ≤ ffBound n t + ∑_{t < i < qBound t} C(n, i) - M · t / i₀`, and for `n ≥ n₀(t)` the
  exponential term `M · t / i₀ ≥ 2^{⌊(n - 2 qBound t)/2⌋ - 1} · t / n` dominates the polynomial
  `∑_{t < i < qBound t} C(n, i) ≤ qBound t · n ^ qBound t`.

The exact value then follows from plby's lower bounds (`franklFurediOdd_card_le_T`,
`franklFurediEven_card_le_T`) and the closed forms `card_franklFurediOdd/Even`.
-/

open Finset

namespace FranklFuredi

/-- The linear combination closing the endgame: with `i = d + t`, the level inequality
`fi * i + fb * d ≤ C * d`, the deficiency `fb + L ≤ C`, the summation bound
`F + C ≤ E + S + fi + fb` and the domination `i * S ≤ t * L`, one gets `F ≤ E`. -/
private lemma le_of_level_bounds {F E C fb fi S L t d i : ℕ} (hi : i = d + t)
    (h1 : fi * i + fb * d ≤ C * d) (h2 : fb + L ≤ C) (h3 : F + C ≤ E + S + fi + fb)
    (h4 : i * S ≤ t * L) (hpos : 1 ≤ i) : F ≤ E := by
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  have m3 : i * (F + C) ≤ i * (E + S + fi + fb) := Nat.mul_le_mul (le_refl i) h3
  have m2 : t * (fb + L) ≤ t * C := Nat.mul_le_mul (le_refl t) h2
  subst hi
  nlinarith [m3, m2, h1, h4]

/-- Exponential beats polynomial: for `n` large the binomial coefficient
`C(n - q, (n + t) / 2 + 1 - t)` dwarfs `n · q · n ^ q`. -/
private lemma mul_pow_le_choose (n t q : ℕ) (ht : 1 ≤ t) (htq : t < q) (hn : 4 * q + 12 ≤ n)
    (hlt : 2 ^ (2 * q + 6) * q * n ^ (q + 2) < 2 ^ n) :
    n * (q * n ^ q) ≤ t * (n - q).choose ((n + t) / 2 + 1 - t) := by
  set k : ℕ := (n + t) / 2 + 1 - t with hkdef
  set N : ℕ := n - q with hNdef
  set j : ℕ := min k (N - k) with hjdef
  have hkN : k ≤ N := by omega
  have hcb : (2 * j).choose j ≤ N.choose k := by
    rw [hjdef]
    exact centralBinom_min_le_choose N k hkN
  have h4j : 4 ^ j ≤ (2 * j + 1) * N.choose k :=
    (four_pow_le_choose_mul j).trans (Nat.mul_le_mul (le_refl (2 * j + 1)) hcb)
  have hpow : 2 ^ (n - 2 * q - 5) ≤ 4 ^ j := by
    have h1 : n - 2 * q - 5 ≤ 2 * j := by omega
    calc 2 ^ (n - 2 * q - 5) ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) h1
      _ = 4 ^ j := by rw [pow_mul]; norm_num
  have hkey : 2 * (q * n ^ (q + 2)) < 2 ^ (n - 2 * q - 5) := by
    have hsplit : (2 : ℕ) ^ n = 2 ^ (2 * q + 5) * 2 ^ (n - 2 * q - 5) := by
      rw [← pow_add]
      congr 1
      omega
    have heq : 2 ^ (2 * q + 6) * q * n ^ (q + 2)
        = 2 ^ (2 * q + 5) * (2 * (q * n ^ (q + 2))) := by
      have h26 : (2 : ℕ) ^ (2 * q + 6) = 2 ^ (2 * q + 5) * 2 := by ring
      rw [h26]
      ring
    rw [hsplit, heq] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hLbound : 2 * n * (n * (q * n ^ q)) < 2 * n * N.choose k := by
    calc 2 * n * (n * (q * n ^ q)) = 2 * (q * n ^ (q + 2)) := by ring
      _ < 2 ^ (n - 2 * q - 5) := hkey
      _ ≤ 4 ^ j := hpow
      _ ≤ (2 * j + 1) * N.choose k := h4j
      _ ≤ 2 * n * N.choose k := Nat.mul_le_mul (by omega) (le_refl (N.choose k))
  have hfinal : n * (q * n ^ q) < N.choose k := Nat.lt_of_mul_lt_mul_left hLbound
  calc n * (q * n ^ q) ≤ N.choose k := le_of_lt hfinal
    _ ≤ t * N.choose k := Nat.le_mul_of_pos_left _ ht

/-- The upper bound `#𝓕 ≤ ffBound n t` under the three numeric side conditions on `n`. -/
private lemma card_le_ffBound_of_numeric (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ n + t - (n + t) / 2 - 1) (hn : (n + t) / 2 + 1 ≤ n)
    (hbig : n * (qBound t * n ^ qBound t) ≤ t * (n - qBound t).choose ((n + t) / 2 + 1 - t)) :
    #𝓕 ≤ ffBound n t := by
  classical
  have htq : t < qBound t := by
    have h : qBound t = t + 1 + lcmUpTo t := rfl
    omega
  by_cases hemp : ∀ i ∈ Finset.Ioo t (qBound t), level 𝓕 i = ∅
  · have hzero : ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by rw [hemp i hi, Finset.card_empty]
    have h := card_le_ffBound_add_middle n t h𝓕 hav ht (by omega)
    rw [hzero] at h
    omega
  · push Not at hemp
    obtain ⟨a, ha, hane⟩ := hemp
    rw [Finset.mem_Ioo] at ha
    obtain ⟨A₀, hA₀⟩ := hane
    rw [mem_level] at hA₀
    obtain ⟨hA₀mem, hA₀card⟩ := hA₀
    have hn1 : 1 ≤ n := by omega
    have hS : ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) ≤ qBound t * n ^ qBound t := by
      calc ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i)
          ≤ ∑ i ∈ Finset.Ioo t (qBound t), n.choose i :=
            Finset.sum_le_sum fun i _ ↦ level_card_le_choose n i h𝓕
        _ ≤ qBound t * n ^ qBound t := sum_choose_Ioo_le n t (qBound t) hn1
    have hbne : #A₀ ≠ (n + t) / 2 + 1 := by omega
    have htb : t ≤ (n + t) / 2 + 1 := by omega
    have htA : t ≤ #A₀ := by omega
    have hsub := level_card_le_choose_sub n t ((n + t) / 2 + 1) h𝓕 hav hA₀mem hbne htb htA
    have hL : (n - qBound t).choose ((n + t) / 2 + 1 - t)
        ≤ (#A₀).choose t * (n - #A₀).choose ((n + t) / 2 + 1 - t) := by
      have h1 : 1 ≤ (#A₀).choose t := Nat.choose_pos (by omega)
      have h2 : (n - qBound t).choose ((n + t) / 2 + 1 - t)
          ≤ (n - #A₀).choose ((n + t) / 2 + 1 - t) := Nat.choose_le_choose _ (by omega)
      calc (n - qBound t).choose ((n + t) / 2 + 1 - t)
          = 1 * (n - qBound t).choose ((n + t) / 2 + 1 - t) := (one_mul _).symm
        _ ≤ (#A₀).choose t * (n - #A₀).choose ((n + t) / 2 + 1 - t) := Nat.mul_le_mul h1 h2
    have h2 : #(level 𝓕 ((n + t) / 2 + 1)) + (n - qBound t).choose ((n + t) / 2 + 1 - t)
        ≤ n.choose ((n + t) / 2 + 1) := by omega
    have hlev := level_inequality n t (n + t - ((n + t) / 2 + 1)) h𝓕 hav ht (by omega) (by omega)
    have he1 : n + t - (n + t - ((n + t) / 2 + 1)) = (n + t) / 2 + 1 := by omega
    have he2 : n + t - ((n + t) / 2 + 1) - t = n - ((n + t) / 2 + 1) := by omega
    rw [he1, he2, Nat.choose_symm hn] at hlev
    have hmain := card_le_ffBound_add_middle_sub n t h𝓕 hav ht hq hn
    have h4 : (n + t - ((n + t) / 2 + 1)) * (∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i))
        ≤ t * (n - qBound t).choose ((n + t) / 2 + 1 - t) :=
      le_trans (Nat.mul_le_mul (by omega) hS) hbig
    have hid : n + t - ((n + t) / 2 + 1) = n - ((n + t) / 2 + 1) + t := by omega
    have h3 : #𝓕 + n.choose ((n + t) / 2 + 1)
        ≤ ffBound n t + (∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i))
          + #(level 𝓕 (n + t - ((n + t) / 2 + 1))) + #(level 𝓕 ((n + t) / 2 + 1)) := by omega
    have hposi : 1 ≤ n + t - ((n + t) / 2 + 1) := by omega
    exact le_of_level_bounds hid hlev h2 h3 h4 hposi

/-- The upper bound of Theorem 1.3, for all sufficiently large `n`. -/
theorem exists_upper_bound (t : ℕ) (ht : 1 ≤ t) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ 𝓕 : Finset (Finset ℕ), 𝓕 ⊆ (range n).powerset → Erdos703.AvoidsRIntersection t 𝓕 →
      #𝓕 ≤ ffBound n t := by
  have htq : t < qBound t := by
    have h : qBound t = t + 1 + lcmUpTo t := rfl
    omega
  obtain ⟨n₁, hn₁⟩ :=
    eventually_mul_pow_lt_two_pow (2 ^ (2 * qBound t + 6) * qBound t) (qBound t + 2)
  refine ⟨max n₁ (4 * qBound t + 12), fun n hn 𝓕 hsub hav ↦ ?_⟩
  have hnb : 4 * qBound t + 12 ≤ n := le_trans (le_max_right _ _) hn
  have h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n := fun A hA ↦ Finset.mem_powerset.mp (hsub hA)
  have hbig : n * (qBound t * n ^ qBound t)
      ≤ t * (n - qBound t).choose ((n + t) / 2 + 1 - t) :=
    mul_pow_le_choose n t (qBound t) ht htq hnb (hn₁ n (le_trans (le_max_left _ _) hn))
  exact card_le_ffBound_of_numeric n t h𝓕 hav ht (by omega) (by omega) hbig

/-- Theorem 1.3 (Frankl–Füredi 1984): for every `t ≥ 1` and all sufficiently large `n`,
`T(n, t) = #𝓕*(n, t) = ffBound n t`. -/
theorem frankl_furedi (t : ℕ) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Erdos703.T n t = ffBound n t := by
  obtain ⟨n₀, hn₀⟩ := exists_upper_bound t ht
  refine ⟨max n₀ 1, fun n hn ↦ le_antisymm ?_ ?_⟩
  · exact Erdos703.T_le_of_forall (hn₀ n (le_trans (le_max_left _ _) hn))
  · have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    by_cases hpar : (n + t) % 2 = 0
    · rw [← card_franklFurediEven n t hn1 hpar]
      exact Erdos703.franklFurediEven_card_le_T n t hn1 hpar
    · rw [← card_franklFurediOdd n t (by omega)]
      exact Erdos703.franklFurediOdd_card_le_T n t

/-- Together with `T(n, 0) = 2 ^ (n - 1)` (Erdős's trivial case, plby), the exact value is known
for every `r` and all large `n`. -/
theorem erdos_703_exact (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Erdos703.T n r = if r = 0 then 2 ^ (n - 1) else ffBound n r := by
  by_cases hr : r = 0
  · subst hr
    refine ⟨1, fun n hn ↦ ?_⟩
    rw [Erdos703.T_zero n hn]
    simp
  · obtain ⟨n₀, hn₀⟩ := frankl_furedi r (Nat.one_le_iff_ne_zero.mpr hr)
    refine ⟨n₀, fun n hn ↦ ?_⟩
    rw [hn₀ n hn]
    simp [hr]

end FranklFuredi

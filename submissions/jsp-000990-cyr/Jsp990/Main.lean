import Jsp990.Defs
import Jsp990.Sequence
import Jsp990.Density
import Jsp990.NoAP

/-!
# JSP-000990 / Erdős #1185 — the two roots

Assembling the three ingredients:

* `Erdos1185.card_A_ge` (density): the set `A = {n ∈ [1,N] : (n² T) % L < L/16}` has at least
  `N / 64` elements, for `L = 8 bm²` with `bm` a large power of two and `T` odd;
* `Erdos1185.phase`: for `j < i < m` the phase `2 (b i - b j)² T m` lies, mod `L m`, in the middle
  band `[L/8, 7L/8]`;
* `Erdos1185.no_ap`: these two facts are incompatible with a `3`-term arithmetic progression in
  `A` whose common difference is a difference of two elements of `B = {b 0, …, b (m-1)}`.

This yields an explicit counterexample for every `k ≥ 3` and every `δ ≤ 1/64`, hence the negative
answer to Erdős Problem #1185.
-/

open Finset

namespace Erdos1185

/-- Explicit counterexamples for every `k ≥ 3` and every `δ ≤ 1/64`. -/
theorem counterexample (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : δ ≤ 1 / 64) (m N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ A B : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
      δ * (N : ℝ) ≤ (#A : ℝ) ∧ m ≤ #B ∧ ¬ HasAPWithStepInDiff k A B := by
  classical
  -- enlarge `m` so that `m' ≥ 2`, i.e. `1 ≤ m' - 1`
  obtain ⟨m', hmm', hm'2⟩ : ∃ m', m ≤ m' ∧ 2 ≤ m' :=
    ⟨max m 2, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨e, hbm⟩ := two_pow_b (m' - 1)
  have hbpos : 0 < b (m' - 1) := b_pos _
  have hL : L m' = 8 * b (m' - 1) * b (m' - 1) := L_eq m'
  -- `b (m' - 1) ≥ b 1 = 2 ^ 8`, so the exponent `e` is at least `8`
  have he : 8 ≤ e := by
    have hb1 : b 1 = 2 ^ 8 := by rw [b_succ_eq, b_zero]; norm_num
    have h1 : (2 : ℕ) ^ 8 ≤ 2 ^ e := by
      rw [← hb1, ← hbm]; exact b_le_b (by omega)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hTodd : T m' % 2 = 1 := T_odd m' (by omega)
  -- `16 ∣ L m'`, since `b (m' - 1)` is even
  obtain ⟨c, hc⟩ : 2 ∣ b (m' - 1) := by rw [hbm]; exact dvd_pow_self 2 (by omega)
  have h16 : (16 : ℕ) ∣ L m' := ⟨2 * (c * c), by rw [hL, hc]; ring⟩
  -- the window
  have hNle : 2 * L m' ≤ max N₀ (2 * L m') := le_max_right _ _
  refine ⟨max N₀ (2 * L m'), le_max_left _ _,
    Erdos1185.A (L m') (T m') (max N₀ (2 * L m')), (range m').image b, ?_, ?_, ?_, ?_, ?_⟩
  · -- `A ⊆ [1, N]`
    intro x hx
    simp only [Erdos1185.A, Finset.mem_filter] at hx
    exact hx.1
  · -- `B ⊆ [1, N]`
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_range] at hl
    rw [Finset.mem_Icc]
    refine ⟨one_le_b l, ?_⟩
    have h1 : b l ≤ b (m' - 1) := b_le_b (by omega)
    have h2 : b (m' - 1) ≤ 2 * L m' := by rw [hL]; nlinarith only [hbpos]
    omega
  · -- density
    have hcard := card_A_ge (b (m' - 1)) (T m') e he hbm hTodd (max N₀ (2 * L m'))
      (by rw [← hL]; exact hNle)
    rw [← hL] at hcard
    have hN0 : (0 : ℝ) ≤ ((max N₀ (2 * L m') : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmul : δ * ((max N₀ (2 * L m') : ℕ) : ℝ) ≤ (1 / 64) * ((max N₀ (2 * L m') : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hδ hN0
    linarith only [hmul, hcard]
  · -- `m ≤ #B`
    rw [Finset.card_image_of_injective _ b_strictMono.injective, Finset.card_range]
    exact hmm'
  · -- no arithmetic progression
    refine no_ap (L m') (T m') k hk h16 _ ?_ _ ?_
    · intro n hn
      simp only [Erdos1185.A, Finset.mem_filter] at hn
      exact hn.2
    · intro b₁ hb₁ b₂ hb₂ d hd hdiff
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb₁
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb₂
      rw [Finset.mem_range] at hi hj
      have hji : j < i := b_strictMono.lt_iff_lt.mp (by omega)
      have hsq : 2 * d * d * T m' = 2 * (b i - b j) ^ 2 * T m' := by
        have hd' : d = b i - b j := by omega
        rw [hd']; ring
      rw [hsq]
      exact phase m' i j hji hi

/-- The negative resolution of Erdős Problem #1185: the statement fails, already for `k = 3`. -/
theorem not_erdos_1185 : ¬ Erdos1185Statement := by
  intro h
  obtain ⟨m, hm, N₀, hN⟩ := h (1 / 64) (by norm_num) 3 le_rfl
  obtain ⟨N, hN₀, A, B, hA, hB, hdens, hmB, hno⟩ :=
    counterexample 3 le_rfl (1 / 64) le_rfl m N₀
  exact hno (hN N hN₀ A B hA hB hdens hmB)

end Erdos1185

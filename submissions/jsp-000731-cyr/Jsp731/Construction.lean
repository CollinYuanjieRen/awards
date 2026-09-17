import Jsp731.Defs

/-!
# JSP-000731 / Erdős #880 — the counterexample set for order `h ≥ 3`

Following Hegyvári–Hennecart–Plagne (2007), we build, for each `h ≥ 3`, a set of positive
integers `A = basis h` which will later be shown to be an asymptotic basis of order exactly `h`
whose restricted sumset has unbounded gaps.

With `c = 3·2^{h−2} − 1` and the rapidly growing scales `x₀ = h`, `x_{n+1} = c·x_n² + h·x_n`,
the `n`-th block of `A` consists of the interval `[x_n, x_n + x_n²)` together with the `h − 1`
"spikes" `x_n + 2^j·x_n²` for `j < h − 1`.

This file contains only the elementary bookkeeping: growth of the scales, the location of the
blocks (each block sits strictly below the next scale, so the blocks are ordered), and the
resulting classification of the elements of `A` lying below a given scale.
-/

namespace Erdos880

/-- `c = 3·2^(h−2) − 1`. -/
def coeff (h : ℕ) : ℕ := 3 * 2 ^ (h - 2) - 1

/-- The scales `x₀ = h`, `x_{n+1} = c·x_n² + h·x_n`. -/
def scale (h : ℕ) : ℕ → ℕ
  | 0 => h
  | n + 1 => coeff h * (scale h n) ^ 2 + h * scale h n

/-- Block `n`: the interval `[x_n, x_n + x_n²)` together with the spikes `x_n + 2^j·x_n²`,
`j < h − 1`. -/
def block (h n : ℕ) : Set ℕ :=
  {a | ∃ r, r < (scale h n) ^ 2 ∧ a = scale h n + r} ∪
    {a | ∃ j, j < h - 1 ∧ a = scale h n + 2 ^ j * (scale h n) ^ 2}

/-- The counterexample set `A = ⋃ₙ block n`. -/
def basis (h : ℕ) : Set ℕ := ⋃ n, block h n

variable {h : ℕ}

/-! ### Defining equations -/

private lemma scale_zero : scale h 0 = h := rfl

private lemma scale_succ (n : ℕ) :
    scale h (n + 1) = coeff h * (scale h n) ^ 2 + h * scale h n := rfl

private lemma mem_block_iff {n a : ℕ} :
    a ∈ block h n ↔
      (∃ r, r < (scale h n) ^ 2 ∧ a = scale h n + r) ∨
        (∃ j, j < h - 1 ∧ a = scale h n + 2 ^ j * (scale h n) ^ 2) := Iff.rfl

private lemma mem_basis_iff {a : ℕ} : a ∈ basis h ↔ ∃ n, a ∈ block h n := by
  simp only [basis, Set.mem_iUnion]

/-! ### The coefficient `c` -/

private lemma two_le_two_pow (hh : 3 ≤ h) : 2 ≤ 2 ^ (h - 2) := by
  have e : h - 2 = (h - 3) + 1 := by omega
  have h1 : 1 ≤ 2 ^ (h - 3) := Nat.one_le_two_pow
  rw [e, pow_succ]
  omega

private lemma coeff_add_one (hh : 3 ≤ h) : coeff h + 1 = 3 * 2 ^ (h - 2) := by
  have h2 := two_le_two_pow hh
  unfold coeff
  omega

private lemma two_pow_pred (hh : 3 ≤ h) : 2 ^ (h - 1) = 2 * 2 ^ (h - 2) := by
  have e : h - 1 = (h - 2) + 1 := by omega
  rw [e, pow_succ]
  ring

theorem two_pow_lt_coeff (hh : 3 ≤ h) : 2 ^ (h - 1) < coeff h := by
  have h1 := coeff_add_one hh
  have h2 := two_le_two_pow hh
  rw [two_pow_pred hh]
  omega

theorem two_pow_sub_two_le_coeff (hh : 3 ≤ h) : 2 ^ (h - 2) + 1 ≤ coeff h := by
  have h1 := coeff_add_one hh
  have h2 := two_le_two_pow hh
  omega

/-- A spike exponent is at most `h − 2`, so its power of two is at most `2^(h−2)`. -/
private lemma two_pow_le_of_lt {j : ℕ} (hj : j < h - 1) : 2 ^ j ≤ 2 ^ (h - 2) :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### Growth of the scales -/

theorem h_le_scale (hh : 3 ≤ h) (n : ℕ) : h ≤ scale h n := by
  induction n with
  | zero => exact le_of_eq scale_zero.symm
  | succ n ih =>
    rw [scale_succ]
    have h1 : h * 1 ≤ h * scale h n := Nat.mul_le_mul le_rfl (by omega)
    omega

theorem three_le_scale (hh : 3 ≤ h) (n : ℕ) : 3 ≤ scale h n :=
  hh.trans (h_le_scale hh n)

theorem scale_lt_succ (hh : 3 ≤ h) (n : ℕ) : scale h n < scale h (n + 1) := by
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have h1 : 3 * scale h n ≤ h * scale h n := Nat.mul_le_mul hh le_rfl
  rw [scale_succ]
  omega

theorem scale_strictMono (hh : 3 ≤ h) : StrictMono (scale h) :=
  strictMono_nat_of_lt_succ (scale_lt_succ hh)

theorem add_le_scale (hh : 3 ≤ h) (n : ℕ) : n + h ≤ scale h n := by
  induction n with
  | zero => rw [scale_zero]; omega
  | succ n ih =>
    have := scale_lt_succ hh n
    omega

theorem exists_scale_interval (hh : 3 ≤ h) {m : ℕ} (hm : h ≤ m) :
    ∃ n, scale h n ≤ m ∧ m < scale h (n + 1) := by
  classical
  have hex : ∃ n, m < scale h n := ⟨m + 1, by have := add_le_scale hh (m + 1); omega⟩
  have hspec : m < scale h (Nat.find hex) := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0, scale_zero] at hspec; omega
    · exact h0
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    omega
  · rwa [Nat.sub_add_cancel hpos]

theorem sq_scale_ge (hh : 3 ≤ h) (n : ℕ) : (h - 1) * scale h n + 3 ≤ (scale h n) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 3 := ⟨h - 3, by omega⟩
  have hx : k + 3 ≤ scale (k + 3) n := h_le_scale hh n
  have h1 : (k + 3) * scale (k + 3) n ≤ scale (k + 3) n * scale (k + 3) n :=
    Nat.mul_le_mul hx le_rfl
  have h2 : scale (k + 3) n ^ 2 = scale (k + 3) n * scale (k + 3) n := sq _
  have e : k + 3 - 1 = k + 2 := by omega
  rw [e, h2]
  nlinarith [h1, hx]

theorem mul_scale_le (hh : 3 ≤ h) (n : ℕ) : h * scale h n ≤ scale h n + (scale h n) ^ 2 := by
  have hx : h ≤ scale h n := h_le_scale hh n
  have h1 : h * scale h n ≤ scale h n * scale h n := Nat.mul_le_mul hx le_rfl
  have h2 : scale h n ^ 2 = scale h n * scale h n := sq _
  omega

/-! ### Location of the blocks -/

theorem block_max_lt (hh : 3 ≤ h) (n : ℕ) :
    scale h n + 2 ^ (h - 2) * (scale h n) ^ 2 < scale h (n + 1) := by
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have hc : 2 ^ (h - 2) + 1 ≤ coeff h := two_pow_sub_two_le_coeff hh
  have h1 : (2 ^ (h - 2) + 1) * scale h n ^ 2 ≤ coeff h * scale h n ^ 2 :=
    Nat.mul_le_mul hc le_rfl
  have h2 : 3 * scale h n ≤ h * scale h n := Nat.mul_le_mul hh le_rfl
  have h3 : scale h n * scale h n = scale h n ^ 2 := (sq _).symm
  have h4 : 3 * scale h n ≤ scale h n * scale h n := Nat.mul_le_mul hx le_rfl
  rw [scale_succ]
  nlinarith [h1, h2, h3, h4]

theorem mem_block_bounds (hh : 3 ≤ h) {n a : ℕ} (ha : a ∈ block h n) :
    scale h n ≤ a ∧ a ≤ scale h n + 2 ^ (h - 2) * (scale h n) ^ 2 := by
  have hone : 1 ≤ 2 ^ (h - 2) := Nat.one_le_two_pow
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have h1 : 1 * scale h n ^ 2 ≤ 2 ^ (h - 2) * scale h n ^ 2 := Nat.mul_le_mul hone le_rfl
  rcases mem_block_iff.mp ha with ⟨r, hr, rfl⟩ | ⟨j, hj, rfl⟩
  · omega
  · have h2 : 2 ^ j * scale h n ^ 2 ≤ 2 ^ (h - 2) * scale h n ^ 2 :=
      Nat.mul_le_mul (two_pow_le_of_lt hj) le_rfl
    omega

theorem scale_mem_block (hh : 3 ≤ h) (n : ℕ) : scale h n ∈ block h n := by
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have : 0 < scale h n ^ 2 := by positivity
  exact mem_block_iff.mpr (Or.inl ⟨0, this, rfl⟩)

theorem scale_mem_basis (hh : 3 ≤ h) (n : ℕ) : scale h n ∈ basis h :=
  mem_basis_iff.mpr ⟨n, scale_mem_block hh n⟩

theorem basis_pos (hh : 3 ≤ h) : ∀ a ∈ basis h, 0 < a := by
  intro a ha
  obtain ⟨n, hn⟩ := mem_basis_iff.mp ha
  have h1 := (mem_block_bounds hh hn).1
  have h2 := three_le_scale hh n
  omega

theorem basis_infinite (hh : 3 ≤ h) : (basis h).Infinite :=
  Set.infinite_of_injective_forall_mem (scale_strictMono hh).injective (scale_mem_basis hh)

theorem lt_scale_of_mem_block (hh : 3 ≤ h) {i n a : ℕ} (hi : i < n) (ha : a ∈ block h i) :
    a < scale h n := by
  have h1 := (mem_block_bounds hh ha).2
  have h2 := block_max_lt hh i
  have h3 : scale h (i + 1) ≤ scale h n := (scale_strictMono hh).monotone (by omega)
  omega

theorem scale_le_of_mem_block (hh : 3 ≤ h) {i n a : ℕ} (hi : n ≤ i) (ha : a ∈ block h i) :
    scale h n ≤ a := by
  have h1 := (mem_block_bounds hh ha).1
  have h2 : scale h n ≤ scale h i := (scale_strictMono hh).monotone hi
  omega

/-- Classification: an element of `A` below `x_{n+1}` is a spike of block `n` or is `< x_n + x_n²`. -/
theorem mem_basis_classify (hh : 3 ≤ h) {n a : ℕ} (ha : a ∈ basis h) (hlt : a < scale h (n + 1)) :
    (∃ j, j < h - 1 ∧ a = scale h n + 2 ^ j * (scale h n) ^ 2) ∨ a < scale h n + (scale h n) ^ 2 := by
  obtain ⟨i, hi⟩ := mem_basis_iff.mp ha
  rcases lt_trichotomy i n with hin | rfl | hin
  · have := lt_scale_of_mem_block hh hin hi
    omega
  · rcases mem_block_iff.mp hi with ⟨r, hr, rfl⟩ | ⟨j, hj, hj2⟩
    · omega
    · exact Or.inl ⟨j, hj, hj2⟩
  · have := scale_le_of_mem_block hh (show n + 1 ≤ i by omega) hi
    omega

theorem spike_injective (hh : 3 ≤ h) (n : ℕ) :
    Function.Injective (fun j : ℕ => scale h n + 2 ^ j * (scale h n) ^ 2) := by
  intro a b hab
  have hx : 3 ≤ scale h n := three_le_scale hh n
  have hpos : 0 < scale h n ^ 2 := by positivity
  simp only at hab
  have h1 : 2 ^ a * scale h n ^ 2 = 2 ^ b * scale h n ^ 2 := by omega
  have h2 : (2 : ℕ) ^ a = 2 ^ b := Nat.eq_of_mul_eq_mul_right hpos h1
  exact Nat.pow_right_injective le_rfl h2

theorem spike_ge (n j : ℕ) : scale h n + (scale h n) ^ 2 ≤ scale h n + 2 ^ j * (scale h n) ^ 2 := by
  have hone : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h1 : 1 * scale h n ^ 2 ≤ 2 ^ j * scale h n ^ 2 := Nat.mul_le_mul hone le_rfl
  omega

theorem spike_lt_of_lt (hh : 3 ≤ h) {n j : ℕ} (hj : j < h - 1) :
    scale h n + 2 ^ j * (scale h n) ^ 2 < scale h (n + 1) := by
  have h1 : 2 ^ j * scale h n ^ 2 ≤ 2 ^ (h - 2) * scale h n ^ 2 :=
    Nat.mul_le_mul (two_pow_le_of_lt hj) le_rfl
  have h2 := block_max_lt hh n
  omega

end Erdos880

#print axioms Erdos880.mem_basis_classify
#print axioms Erdos880.exists_scale_interval
#print axioms Erdos880.basis_infinite

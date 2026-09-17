import Erdos894Colouring.Definitions

/-! The colouring: given rotations `θ j` (one per residue class `j < r`) whose multiples along the
`j`-th subsequence have fractional part in `[1/4, 3/4]`, colour an integer `a` by the cells
`⌊8 · fract (θ j * a)⌋` for `j < r`. Two integers of the same colour cannot differ by a term. -/

namespace Erdos894

/-- The cell of `x ∈ [0,1)` among eight equal subintervals of the circle. -/
noncomputable def cell (x : ℝ) : Fin 8 :=
  ⟨min (⌊8 * Int.fract x⌋₊) 7, by omega⟩

/-- Since `8 * fract x < 8`, the truncation in `cell` is inactive. -/
private theorem floor_eight_fract_lt (x : ℝ) : ⌊8 * Int.fract x⌋₊ < 8 := by
  have h0 : (0 : ℝ) ≤ 8 * Int.fract x := by
    have := Int.fract_nonneg x; linarith
  have h1 : 8 * Int.fract x < (8 : ℕ) := by
    have := Int.fract_lt_one x; push_cast; linarith
  exact (Nat.floor_lt h0).2 h1

/-- Same cell forces fractional parts within `1/8`. -/
theorem abs_fract_sub_lt_of_cell_eq (x y : ℝ) (h : cell x = cell y) :
    |Int.fract x - Int.fract y| < 1 / 8 := by
  have hx0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have hy0 : (0 : ℝ) ≤ Int.fract y := Int.fract_nonneg y
  have hxn : (0 : ℝ) ≤ 8 * Int.fract x := by linarith
  have hyn : (0 : ℝ) ≤ 8 * Int.fract y := by linarith
  have hxlt := floor_eight_fract_lt x
  have hylt := floor_eight_fract_lt y
  have key : ⌊8 * Int.fract x⌋₊ = ⌊8 * Int.fract y⌋₊ := by
    have hval : min (⌊8 * Int.fract x⌋₊) 7 = min (⌊8 * Int.fract y⌋₊) 7 := congrArg Fin.val h
    omega
  have hxle : ((⌊8 * Int.fract x⌋₊ : ℕ) : ℝ) ≤ 8 * Int.fract x := Nat.floor_le hxn
  have hyle : ((⌊8 * Int.fract y⌋₊ : ℕ) : ℝ) ≤ 8 * Int.fract y := Nat.floor_le hyn
  have hxup : 8 * Int.fract x < (⌊8 * Int.fract x⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  have hyup : 8 * Int.fract y < (⌊8 * Int.fract y⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  rw [key] at hxle hxup
  rw [abs_lt]
  constructor <;> linarith

/-- If `fract (θ * d) ∈ [1/4, 3/4]` then `θ * (b + d)` and `θ * b` have fractional parts at
distance at least `1/4`. -/
theorem one_div_four_le_abs_fract_sub (θ : ℝ) (b d : ℤ)
    (hd : 1 / 4 ≤ Int.fract (θ * d) ∧ Int.fract (θ * d) ≤ 3 / 4) :
    1 / 4 ≤ |Int.fract (θ * (b + d)) - Int.fract (θ * b)| := by
  obtain ⟨hd1, hd2⟩ := hd
  have hsplit : Int.fract (θ * (b + d)) = Int.fract (θ * b + θ * d) := by
    congr 1
    ring
  rw [hsplit]
  obtain ⟨z, hz⟩ := Int.fract_add (θ * b) (θ * d)
  have hb0 : (0 : ℝ) ≤ Int.fract (θ * b) := Int.fract_nonneg _
  have hb1 : Int.fract (θ * b) < 1 := Int.fract_lt_one _
  have hs0 : (0 : ℝ) ≤ Int.fract (θ * b + θ * d) := Int.fract_nonneg _
  have hs1 : Int.fract (θ * b + θ * d) < 1 := Int.fract_lt_one _
  have hzlt : ((z : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
  have hzgt : ((-2 : ℤ) : ℝ) < ((z : ℤ) : ℝ) := by push_cast; linarith
  have hzlt' : z < 1 := by exact_mod_cast hzlt
  have hzgt' : (-2 : ℤ) < z := by exact_mod_cast hzgt
  have hzcases : z = 0 ∨ z = -1 := by omega
  rcases hzcases with hzv | hzv <;> subst hzv <;> push_cast at hz
  · exact le_abs.2 (Or.inl (by linarith))
  · exact le_abs.2 (Or.inr (by linarith))

/-- The avoiding colouring from a family of rotations. -/
theorem hasAvoidingColouring_of_rotations (n : ℕ → ℕ) (r : ℕ) (hr : 0 < r) (θ : ℕ → ℝ)
    (hθ : ∀ j i : ℕ, j < r → 1 / 4 ≤ Int.fract (θ j * n (j + r * i)) ∧
      Int.fract (θ j * n (j + r * i)) ≤ 3 / 4) :
    HasAvoidingColouring n := by
  classical
  refine ⟨Fintype.card (Fin r → Fin 8),
    fun a => Fintype.equivFin (Fin r → Fin 8) (fun j : Fin r => cell (θ (j : ℕ) * (a : ℝ))), ?_⟩
  intro a b hab k hk
  have hfun : (fun j : Fin r => cell (θ (j : ℕ) * (a : ℝ)))
      = (fun j : Fin r => cell (θ (j : ℕ) * (b : ℝ))) :=
    (Fintype.equivFin (Fin r → Fin 8)).injective hab
  have hjr : k % r < r := Nat.mod_lt _ hr
  have hcell : cell (θ (k % r) * (a : ℝ)) = cell (θ (k % r) * (b : ℝ)) :=
    congrFun hfun ⟨k % r, hjr⟩
  have h1 := abs_fract_sub_lt_of_cell_eq _ _ hcell
  obtain ⟨hlo, hhi⟩ := hθ (k % r) (k / r) hjr
  rw [Nat.mod_add_div] at hlo hhi
  have hcastn : (((n k : ℕ) : ℤ) : ℝ) = ((n k : ℕ) : ℝ) := by push_cast; ring
  rw [← hcastn] at hlo hhi
  have h2 := one_div_four_le_abs_fract_sub (θ (k % r)) b ((n k : ℕ) : ℤ) ⟨hlo, hhi⟩
  have hcast : ((b : ℝ) + (((n k : ℕ) : ℤ) : ℝ)) = (a : ℝ) := by
    have ha : a = b + ((n k : ℕ) : ℤ) := by omega
    rw [ha]; push_cast; ring
  rw [hcast] at h2
  linarith

end Erdos894

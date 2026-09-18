import Jsp751.Defs

/-!
# JSP-000751 / Erdős #903 — the algebraic core

For a linear space `block : Fin b → Finset (Fin v)` in which every point has degree at least `2`
we build the incidence matrix `N`, the inverse `K` of `N Nᵀ = diagonal d + J` (with `d x = r_x - 1`),
the idempotent `P = Nᵀ K N` and `Q = 1 - P`, and we prove the rank bound
`rank (Q restricted to a set F of blocks) + v ≤ b`.
-/

open Finset Matrix

namespace Erdos903

variable {v b : ℕ} (block : Fin b → Finset (Fin v))

/-- The incidence matrix of the design: rows are points, columns are blocks. -/
noncomputable def N : Matrix (Fin v) (Fin b) ℝ :=
  Matrix.of fun x i => if x ∈ block i then 1 else 0

/-- `d x = r_x - 1`, one less than the degree of the point `x`. -/
noncomputable def d (x : Fin v) : ℝ := (degree block x : ℝ) - 1

/-- `σ = ∑_x 1 / d x`. -/
noncomputable def σ : ℝ := ∑ x, 1 / d block x

/-- `α = 1 / (1 + σ)`. -/
noncomputable def α : ℝ := 1 / (1 + σ block)

/-- `K = D⁻¹ - α D⁻¹ J D⁻¹`, the inverse of `N Nᵀ = D + J`. -/
noncomputable def K : Matrix (Fin v) (Fin v) ℝ :=
  Matrix.of fun x y =>
    (if x = y then 1 / d block x else 0) - α block * (1 / d block x) * (1 / d block y)

/-- `P = Nᵀ K N`. -/
noncomputable def P : Matrix (Fin b) (Fin b) ℝ := (N block)ᵀ * K block * N block

/-- `Q = 1 - P`. -/
noncomputable def Q : Matrix (Fin b) (Fin b) ℝ := 1 - P block

/-- `a i = ∑_{x ∈ block i} 1 / d x`. -/
noncomputable def a (i : Fin b) : ℝ := ∑ x ∈ block i, 1 / d block x

/-! ### Entries of `K` -/

theorem K_apply (x y : Fin v) :
    K block x y =
      (if x = y then 1 / d block x else 0) - α block * (1 / d block x) * (1 / d block y) :=
  rfl

theorem K_apply_self (x : Fin v) :
    K block x x = 1 / d block x - α block * (1 / d block x) * (1 / d block x) := by
  simp [K_apply]

theorem K_apply_ne {x y : Fin v} (hxy : x ≠ y) :
    K block x y = -(α block * (1 / d block x) * (1 / d block y)) := by
  simp [K_apply, hxy]

theorem K_transpose : (K block)ᵀ = K block := by
  ext x y
  rw [Matrix.transpose_apply, K_apply, K_apply]
  rcases eq_or_ne x y with rfl | hxy
  · ring
  · rw [ite_eq_right hxy, ite_eq_right (Ne.symm hxy)]
    ring

/-! ### `N Nᵀ = diagonal d + J` -/

theorem NNT_apply (h : IsLinearSpace block) (x y : Fin v) :
    (N block * (N block)ᵀ) x y = if x = y then (degree block x : ℝ) else 1 := by
  have hsum : (N block * (N block)ᵀ) x y
      = ∑ i, (if x ∈ block i ∧ y ∈ block i then (1 : ℝ) else 0) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [N, Matrix.of_apply, Matrix.transpose_apply]
    by_cases h1 : x ∈ block i <;> by_cases h2 : y ∈ block i <;> simp [h1, h2]
  rw [hsum]
  rcases eq_or_ne x y with rfl | hxy
  · have hone : (if x = x then ((degree block x : ℝ)) else 1) = (degree block x : ℝ) := ite_eq_left rfl
    rw [hone, degree, through]
    simp
  · obtain ⟨i₀, hi₀, huniq⟩ := h.2 x y hxy
    have key : ∑ i, (if x ∈ block i ∧ y ∈ block i then (1 : ℝ) else 0) = 1 := by
      refine (Finset.sum_eq_single_of_mem i₀ (mem_univ i₀) ?_).trans (ite_eq_left hi₀)
      intro i _ hne
      exact ite_eq_right fun hh => hne (huniq i hh)
    rw [key, ite_eq_right hxy]

theorem NNT_eq (h : IsLinearSpace block) :
    N block * (N block)ᵀ = Matrix.diagonal (d block) + Matrix.of fun _ _ => (1 : ℝ) := by
  ext x y
  rw [NNT_apply block h, Matrix.add_apply, Matrix.diagonal_apply]
  simp only [Matrix.of_apply]
  rcases eq_or_ne x y with rfl | hxy
  · have h1 : (if x = x then ((degree block x : ℝ)) else 1) = (degree block x : ℝ) := ite_eq_left rfl
    have h2 : (if x = x then d block x else (0 : ℝ)) = d block x := ite_eq_left rfl
    rw [h1, h2, d]
    ring
  · rw [ite_eq_right hxy, ite_eq_right hxy, zero_add]

/-! ### Positivity -/

theorem one_le_d (hdeg : ∀ x, 2 ≤ degree block x) (x : Fin v) : 1 ≤ d block x := by
  have h2 : (2 : ℝ) ≤ (degree block x : ℝ) := by exact_mod_cast hdeg x
  rw [d]
  linarith

theorem d_pos (hdeg : ∀ x, 2 ≤ degree block x) (x : Fin v) : 0 < d block x :=
  lt_of_lt_of_le zero_lt_one (one_le_d block hdeg x)

theorem d_ne_zero (hdeg : ∀ x, 2 ≤ degree block x) (x : Fin v) : d block x ≠ 0 :=
  ne_of_gt (d_pos block hdeg x)

theorem sigma_nonneg (hdeg : ∀ x, 2 ≤ degree block x) : 0 ≤ σ block := by
  rw [σ]
  exact Finset.sum_nonneg fun x _ => le_of_lt (one_div_pos.mpr (d_pos block hdeg x))

theorem one_add_sigma_pos (hdeg : ∀ x, 2 ≤ degree block x) : 0 < 1 + σ block := by
  have := sigma_nonneg block hdeg
  linarith

theorem alpha_pos (hdeg : ∀ x, 2 ≤ degree block x) : 0 < α block := by
  rw [α]
  exact one_div_pos.mpr (one_add_sigma_pos block hdeg)

theorem alpha_nonneg (hdeg : ∀ x, 2 ≤ degree block x) : 0 ≤ α block :=
  le_of_lt (alpha_pos block hdeg)

theorem alpha_mul_one_add_sigma (hdeg : ∀ x, 2 ≤ degree block x) :
    α block * (1 + σ block) = 1 := by
  have h0 : (1 : ℝ) + σ block ≠ 0 := (one_add_sigma_pos block hdeg).ne'
  rw [α]
  field_simp

/-! ### `K` is the inverse of `N Nᵀ` -/

theorem M_mul_K (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) :
    N block * (N block)ᵀ * K block = 1 := by
  have hdu : ∀ y, d block y * (1 / d block y) = 1 := fun y => by
    have := d_ne_zero block hdeg y
    field_simp
  have hα : α block * (1 + σ block) = 1 := alpha_mul_one_add_sigma block hdeg
  have e3 : ∀ z, ∑ y, K block y z = 1 / d block z - α block * σ block * (1 / d block z) := by
    intro z
    have s1 : ∑ y, (if y = z then 1 / d block y else (0 : ℝ)) = 1 / d block z := by
      refine (Finset.sum_eq_single_of_mem z (mem_univ z) ?_).trans (ite_eq_left rfl)
      intro y _ hy
      exact ite_eq_right hy
    have s2 : ∑ y, α block * (1 / d block y) * (1 / d block z)
        = α block * σ block * (1 / d block z) := by
      rw [σ, ← Finset.sum_mul, ← Finset.mul_sum]
    have step : ∑ y, K block y z
        = ∑ y, ((if y = z then 1 / d block y else 0)
            - α block * (1 / d block y) * (1 / d block z)) :=
      Finset.sum_congr rfl fun y _ => K_apply block y z
    rw [step, Finset.sum_sub_distrib, s1, s2]
  ext x z
  rw [NNT_eq block h, Matrix.add_mul, Matrix.add_apply, Matrix.diagonal_mul]
  have e2 : ((Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin v) (Fin v) ℝ) * K block) x z
      = ∑ y, K block y z := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun y _ => by simp
  rw [e2, e3]
  rcases eq_or_ne x z with rfl | hxz
  · rw [K_apply_self, Matrix.one_apply_eq]
    linear_combination (1 - α block * (1 / d block x)) * hdu x - (1 / d block x) * hα
  · rw [K_apply_ne block hxz, Matrix.one_apply_ne hxz]
    linear_combination (-(α block * (1 / d block z))) * hdu x - (1 / d block z) * hα

theorem K_mul_M (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) :
    K block * (N block * (N block)ᵀ) = 1 := by
  have h1 := M_mul_K block h hdeg
  have hu : IsUnit (N block * (N block)ᵀ).det := Matrix.isUnit_det_of_right_inverse h1
  rw [← Matrix.inv_eq_right_inv h1]
  exact Matrix.nonsing_inv_mul _ hu

theorem isUnit_NNT (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) :
    IsUnit (N block * (N block)ᵀ) :=
  ⟨⟨N block * (N block)ᵀ, K block, M_mul_K block h hdeg, K_mul_M block h hdeg⟩, rfl⟩

/-! ### `Q` is a symmetric idempotent killed by `N` -/

theorem N_mul_Q (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) :
    N block * Q block = 0 := by
  have hM := M_mul_K block h hdeg
  have key : N block * ((N block)ᵀ * K block * N block)
      = N block * (N block)ᵀ * K block * N block := by
    simp [Matrix.mul_assoc]
  rw [Q, P, Matrix.mul_sub, Matrix.mul_one, key, hM, Matrix.one_mul, sub_self]

theorem P_transpose : (P block)ᵀ = P block := by
  rw [P, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    K_transpose block, Matrix.mul_assoc]

theorem Q_transpose : (Q block)ᵀ = Q block := by
  rw [Q, Matrix.transpose_sub, Matrix.transpose_one, P_transpose block]

theorem P_mul_P (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) :
    P block * P block = P block := by
  have hKM := K_mul_M block h hdeg
  rw [P]
  calc (N block)ᵀ * K block * N block * ((N block)ᵀ * K block * N block)
      = (N block)ᵀ * (K block * (N block * (N block)ᵀ)) * (K block * N block) := by
        simp [Matrix.mul_assoc]
    _ = (N block)ᵀ * K block * N block := by
        rw [hKM, Matrix.mul_one, Matrix.mul_assoc]

theorem Q_mul_Q (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) :
    Q block * Q block = Q block := by
  have hP := P_mul_P block h hdeg
  have expand : Q block * Q block = 1 - P block - P block + P block * P block := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [expand, hP, Q]
  abel

/-! ### Entries of `P` and `Q` -/

theorem sum_indicator (g : Fin v → ℝ) (i : Fin b) :
    ∑ x, (if x ∈ block i then (1 : ℝ) else 0) * g x = ∑ x ∈ block i, g x := by
  have hstep : ∀ x : Fin v, (if x ∈ block i then (1 : ℝ) else 0) * g x
      = if x ∈ block i then g x else 0 := by
    intro x
    by_cases hx : x ∈ block i <;> simp [hx]
  have h1 : ∑ x, (if x ∈ block i then (1 : ℝ) else 0) * g x
      = ∑ x, (if x ∈ block i then g x else 0) :=
    Finset.sum_congr rfl fun x _ => hstep x
  rw [h1, ← Finset.sum_filter, Finset.filter_univ_mem]

theorem P_apply (i j : Fin b) : P block i j = ∑ x ∈ block i, ∑ y ∈ block j, K block x y := by
  have inner : ∀ y : Fin v, ((N block)ᵀ * K block) i y = ∑ x ∈ block i, K block x y := by
    intro y
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, N, Matrix.of_apply]
    exact sum_indicator block (fun x => K block x y) i
  calc P block i j
      = ∑ y, (if y ∈ block j then (1 : ℝ) else 0) * ((N block)ᵀ * K block) i y := by
        rw [P, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [N, Matrix.of_apply]
        ring
    _ = ∑ y ∈ block j, ((N block)ᵀ * K block) i y :=
        sum_indicator block (fun y => ((N block)ᵀ * K block) i y) j
    _ = ∑ y ∈ block j, ∑ x ∈ block i, K block x y :=
        Finset.sum_congr rfl fun y _ => inner y
    _ = ∑ x ∈ block i, ∑ y ∈ block j, K block x y := Finset.sum_comm

theorem Q_apply (_h : IsLinearSpace block) (_hdeg : ∀ x, 2 ≤ degree block x) (i j : Fin b) :
    Q block i j = (if i = j then 1 else 0) - ∑ x ∈ block i ∩ block j, 1 / d block x
      + α block * a block i * a block j := by
  have inner : ∀ x : Fin v, ∑ y ∈ block j, K block x y
      = (if x ∈ block j then 1 / d block x else 0)
        - α block * (1 / d block x) * a block j := by
    intro x
    have step : ∑ y ∈ block j, K block x y
        = ∑ y ∈ block j, ((if x = y then 1 / d block x else 0)
            - α block * (1 / d block x) * (1 / d block y)) :=
      Finset.sum_congr rfl fun y _ => K_apply block x y
    rw [step, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_ite_eq (block j) x fun _ => 1 / d block x
    · simp only [a]
      rw [Finset.mul_sum]
  have hP : P block i j
      = (∑ x ∈ block i, (if x ∈ block j then 1 / d block x else (0 : ℝ)))
        - α block * a block i * a block j := by
    have step : ∑ x ∈ block i, ∑ y ∈ block j, K block x y
        = ∑ x ∈ block i, ((if x ∈ block j then 1 / d block x else 0)
            - α block * (1 / d block x) * a block j) :=
      Finset.sum_congr rfl fun x _ => inner x
    rw [P_apply, step, Finset.sum_sub_distrib]
    congr 1
    simp only [a]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hinter : (∑ x ∈ block i, (if x ∈ block j then 1 / d block x else (0 : ℝ)))
      = ∑ x ∈ block i ∩ block j, 1 / d block x := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  rw [Q, Matrix.sub_apply, hP, hinter]
  rcases eq_or_ne i j with rfl | hij
  · have h1 : (if i = i then (1 : ℝ) else 0) = 1 := ite_eq_left rfl
    rw [Matrix.one_apply_eq, h1]
    ring
  · rw [Matrix.one_apply_ne hij, ite_eq_right hij]
    ring

/-! ### Ranks -/

theorem rank_N (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x) :
    (N block).rank = v := by
  have h1 : (N block * (N block)ᵀ).rank = v := by
    rw [Matrix.rank_of_isUnit _ (isUnit_NNT block h hdeg), Fintype.card_fin]
  have h2 : (N block * (N block)ᵀ).rank ≤ (N block).rank := Matrix.rank_mul_le_left _ _
  have h3 : (N block).rank ≤ v := by
    simpa using Matrix.rank_le_card_height (N block)
  omega

theorem rank_Q_submatrix_le (h : IsLinearSpace block) (hdeg : ∀ x, 2 ≤ degree block x)
    (F : Finset (Fin b)) :
    ((Q block).submatrix (Subtype.val : F → Fin b) (Subtype.val : F → Fin b)).rank + v ≤ b := by
  classical
  set S : Matrix (Fin b) { x // x ∈ F } ℝ := (Q block).submatrix id Subtype.val with hS
  have hSS : Sᵀ * S
      = (Q block).submatrix (Subtype.val : F → Fin b) (Subtype.val : F → Fin b) := by
    ext i j
    have h1 : ((Q block)ᵀ * Q block) (i : Fin b) (j : Fin b) = Q block (i : Fin b) (j : Fin b) := by
      rw [Q_transpose, Q_mul_Q block h hdeg]
    rw [Matrix.mul_apply] at h1
    rw [Matrix.submatrix_apply, Matrix.mul_apply]
    simpa [hS, Matrix.transpose_apply] using h1
  have hNS : N block * S = 0 := by
    ext x j
    have h1 := congrFun (congrFun (N_mul_Q block h hdeg) x) (j : Fin b)
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply, Matrix.zero_apply]
    simpa [hS] using h1
  have hker : LinearMap.range S.mulVecLin ≤ LinearMap.ker (N block).mulVecLin := by
    rintro y ⟨w, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hNS, Matrix.zero_mulVec]
  have h1 : S.rank ≤ Module.finrank ℝ (LinearMap.ker (N block).mulVecLin) :=
    Submodule.finrank_mono hker
  have h2 : Module.finrank ℝ (LinearMap.range (N block).mulVecLin)
      + Module.finrank ℝ (LinearMap.ker (N block).mulVecLin) = b := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have h3 : Module.finrank ℝ (LinearMap.range (N block).mulVecLin) = v := rank_N block h hdeg
  have h4 : ((Q block).submatrix (Subtype.val : F → Fin b)
      (Subtype.val : F → Fin b)).rank ≤ S.rank := by
    rw [← hSS]
    exact Matrix.rank_mul_le_right _ _
  omega

end Erdos903

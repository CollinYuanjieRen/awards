import Erdos210Ordinary.Config
import Erdos210Ordinary.Algebra

/-!
# Erdős Problem 210 — the core lemma (Lemma A)

If `p` is a point of order zero, `x ∉ P` is a point distinct from `p` such that the open segment
`(p, x)` meets no connecting line of `P` missing `p`, then every connecting line through `x`
missing `p` is ordinary.

The proof is the affine rendering of Motzkin's argument (route memo §3.5): if the line `a b`
carried a third point `c`, the three points would be `x + αᵢ • u` for distinct nonzero `αᵢ`
(`u = b - a`); the sign lemma `exists_pivot` selects a pivot, the point of order zero supplies a
third point `p₄` on the line through `p` and the pivot, and the crossing identity
(`oppSide_of_pivot`) makes one of the two remaining connecting lines separate `p` from `x`, hence
cross the open segment `(p, x)` — contradicting visibility.
-/

namespace Erdos210

/-- A connecting line `q r` that strictly separates `p` from `x` contradicts visibility. -/
private theorem contra_of_oppSide {P : Finset (ℝ × ℝ)} {p x q r : ℝ × ℝ}
    (hvis : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → ¬ OnLine c d p →
      ∀ t : ℝ, 0 < t → t < 1 → ¬ OnLine c d (p + t • (x - p)))
    (hq : q ∈ P) (hr : r ∈ P) (hopp : OppSide q r p x) : False := by
  have hD : ¬ OnLine q r p := by
    intro h
    simp only [OppSide] at hopp
    simp only [OnLine] at h
    rw [h, zero_mul] at hopp
    exact lt_irrefl 0 hopp
  have hqr : q ≠ r := by
    rintro rfl
    exact hD (D_self_left q p)
  obtain ⟨t, ht0, ht1, hon⟩ := exists_cross_of_oppSide hopp
  exact hvis q hq r hr hqr hD t ht0 ht1 hon

/-- Three-real form of the sign lemma `exists_pivot`: from three distinct nonzero reals all
satisfying a predicate `M` we extract a pivot `α₁` and the two others, with their ratios to the
pivot separated by the interval `(0, 1)`. -/
private theorem exists_pivot3 {M : ℝ → Prop} {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (Ma : M a) (Mb : M b) (Mc : M c) :
    ∃ α₁ αⱼ αₖ : ℝ, M α₁ ∧ M αⱼ ∧ M αₖ ∧ α₁ ≠ 0 ∧ αⱼ ≠ 0 ∧ αₖ ≠ 0 ∧ αⱼ ≠ α₁ ∧ αₖ ≠ α₁ ∧
      (0 < αⱼ / α₁ ∧ αⱼ / α₁ < 1) ∧ ¬ (0 < αₖ / α₁ ∧ αₖ / α₁ < 1) := by
  have hM : ∀ i : Fin 3, M (![a, b, c] i) := by
    intro i
    fin_cases i
    · exact Ma
    · exact Mb
    · exact Mc
  have h0 : ∀ i : Fin 3, ![a, b, c] i ≠ 0 := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have hinj : Function.Injective ![a, b, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨i, j, k, hij, hik, -, hj, hk⟩ := exists_pivot _ h0 hinj
  exact ⟨_, _, _, hM i, hM j, hM k, h0 i, h0 j, h0 k,
    fun h => hij (hinj h).symm, fun h => hik (hinj h).symm, hj, hk⟩

/-- The geometric core: a pivot `x + α₁ • u` in `P` together with two further points
`x + αⱼ • u`, `x + αₖ • u` of `P` whose ratios to the pivot straddle `(0, 1)` contradicts
visibility. -/
private theorem core_step {P : Finset (ℝ × ℝ)} {p x u : ℝ × ℝ} {α₁ αⱼ αₖ : ℝ}
    (hp : p ∈ orderZero P)
    (hvis : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → ¬ OnLine c d p →
      ∀ t : ℝ, 0 < t → t < 1 → ¬ OnLine c d (p + t • (x - p)))
    (hΔ : D x (x + u) p ≠ 0)
    (h1 : α₁ ≠ 0) (hj0 : αⱼ ≠ 0) (hk0 : αₖ ≠ 0) (hjne : αⱼ ≠ α₁) (hkne : αₖ ≠ α₁)
    (M1 : x + α₁ • u ∈ P) (Mj : x + αⱼ • u ∈ P) (Mk : x + αₖ • u ∈ P)
    (hrj : 0 < αⱼ / α₁ ∧ αⱼ / α₁ < 1) (hrk : ¬ (0 < αₖ / α₁ ∧ αₖ / α₁ < 1)) : False := by
  -- the pivot is not `p`, since `p` is off the line
  have hpp1 : p ≠ x + α₁ • u := by
    rintro rfl
    refine hΔ ?_
    simp only [D, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  -- `p` lies on no ordinary line, so the line through `p` and the pivot carries a third point
  obtain ⟨p₄, hp₄P, hp₄line, hp₄p, hp₄1⟩ := exists_third_of_orderZero hp M1 hpp1
  obtain ⟨γ, rfl⟩ := exists_param_of_onLine hpp1 hp₄line
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact hp₄p (by module)
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    exact hp₄1 (by module)
  by_cases hγ : 0 < γ ∧ γ < 1
  · exact contra_of_oppSide hvis hp₄P Mk
      (oppSide_of_pivot x p u α₁ αₖ γ hΔ h1 hk0 hkne hγ0 hγ1 (Or.inl ⟨hγ.1, hγ.2, hrk⟩))
  · refine contra_of_oppSide hvis hp₄P Mj
      (oppSide_of_pivot x p u α₁ αⱼ γ hΔ h1 hj0 hjne hγ0 hγ1 (Or.inr ⟨?_, hrj⟩))
    rintro ⟨hg0, hg1⟩
    exact hγ ⟨lt_of_le_of_ne hg0 (Ne.symm hγ0), lt_of_le_of_ne hg1 hγ1⟩

/-- Lemma A. -/
theorem ordinary_of_visible {P : Finset (ℝ × ℝ)} {p x : ℝ × ℝ} (hp : p ∈ orderZero P) (hx : x ∉ P)
    (hxp : x ≠ p)
    (hvis : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → ¬ OnLine c d p →
      ∀ t : ℝ, 0 < t → t < 1 → ¬ OnLine c d (p + t • (x - p)))
    {a b : ℝ × ℝ} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) (hpab : ¬ OnLine a b p)
    (hxab : OnLine a b x) : ({a, b} : Finset (ℝ × ℝ)) ∈ ordinaryPairs P := by
  -- `hxp` is part of the frozen interface; the proof below does not need it.
  have _hxp : x ≠ p := hxp
  refine pair_mem_ordinaryPairs ha hb hab ?_
  intro c hc hcab
  by_contra hne
  obtain ⟨hca, hcb⟩ := not_or.mp hne
  -- parametrize the three points of `P` on the line `a b` relative to `x`
  obtain ⟨s, hs⟩ := exists_param_of_onLine hab hxab
  obtain ⟨sc, hsc⟩ := exists_param_of_onLine hab hcab
  have hxa : x + (-s) • (b - a) = a := by rw [hs]; module
  have hxb : x + (1 - s) • (b - a) = b := by rw [hs]; module
  have hxc : x + (sc - s) • (b - a) = c := by rw [hs, hsc]; module
  -- the three parameters are nonzero, else `x ∈ P`
  have hA0 : (-s) ≠ 0 := by
    intro h
    have hxa' : x = a := by rw [← hxa, h, zero_smul, add_zero]
    exact hx (by rw [hxa']; exact ha)
  have hB0 : (1 - s) ≠ 0 := by
    intro h
    have hxb' : x = b := by rw [← hxb, h, zero_smul, add_zero]
    exact hx (by rw [hxb']; exact hb)
  have hC0 : (sc - s) ≠ 0 := by
    intro h
    have hxc' : x = c := by rw [← hxc, h, zero_smul, add_zero]
    exact hx (by rw [hxc']; exact hc)
  -- and pairwise distinct, since the three points are
  have hsc0 : sc ≠ 0 := by
    rintro rfl
    exact hca (by rw [hsc]; module)
  have hsc1 : sc ≠ 1 := by
    rintro rfl
    exact hcb (by rw [hsc]; module)
  have hAB : (-s) ≠ 1 - s := by intro h; linarith
  have hAC : (-s) ≠ sc - s := fun h => hsc0 (by linarith)
  have hBC : (1 - s) ≠ sc - s := fun h => hsc1 (by linarith)
  -- the direction `u = b - a` is independent of `p - x`
  have hΔ : D x (x + (b - a)) p ≠ 0 := by
    have key : D x (x + (b - a)) p = D a b p := by
      rw [hs]
      simp only [D, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      ring
    rw [key]
    exact hpab
  obtain ⟨α₁, αⱼ, αₖ, M1, Mj, Mk, h1, hj0, hk0, hjne, hkne, hrj, hrk⟩ :=
    exists_pivot3 (M := fun t : ℝ => x + t • (b - a) ∈ P) hA0 hB0 hC0 hAB hAC hBC
      (by rw [hxa]; exact ha) (by rw [hxb]; exact hb) (by rw [hxc]; exact hc)
  exact core_step hp hvis hΔ h1 hj0 hk0 hjne hkne M1 Mj Mk hrj hrk

end Erdos210

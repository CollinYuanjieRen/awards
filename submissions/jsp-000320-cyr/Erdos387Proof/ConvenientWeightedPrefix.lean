import Erdos387Proof.ConvenientWeightedMoment
import Erdos387Proof.FamilyMixedAbel

/-! Exact translated-prefix interfaces for the actual weighted moment.
All roughness and unit masks are independent row and column masks. -/
set_option autoImplicit false
namespace Erdos387Proof.ConvenientWeightedPrefix
open Erdos387 Erdos387.CoverBPZ
open ConvenientMomentBoxes ConvenientMomentBound ConvenientWeightedMoment
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def maskedArray {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g r s : ℕ) (c : Index S X z y medium i)
    (F : ℕ → ℕ → ℂ) (u v : ℕ) : ℂ :=
  if boxAllowed g c (2^r+u) then
    if boxAllowed g c (2^s+v) then F (2^r+u) (2^s+v) else 0
  else 0

theorem sum_prefix_maskedArray {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g r s n m : ℕ) (c : Index S X z y medium i)
    (hn : n ≤ 2^r) (hm : m ≤ 2^s) (F : ℕ → ℕ → ℂ) :
    (∑ u ∈ Finset.range n, ∑ v ∈ Finset.range m, maskedArray g r s c F u v) =
      ∑ u ∈ variableBox g r (2^r+n-1) c,
      ∑ v ∈ variableBox g s (2^s+m-1) c, F u v := by
  classical
  rw [← sum_range_mask_eq_variableBox g r n c hn]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : boxAllowed g c (2^r+u)
  · simp only [maskedArray,if_pos hu]
    exact sum_range_mask_eq_variableBox g s m c hm (F (2^r+u))
  · simp only [maskedArray,if_neg hu,Finset.sum_const_zero]

theorem variableBox_full_cut {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g b : ℕ) (c : Index S X z y medium i) :
    variableBox g b medium c = variableBox g b (2^b+2^b-1) c := by
  classical
  ext n
  simp only [variableBox,Finset.mem_filter,Finset.mem_Ico,pow_succ]
  have hp : 0 < 2^b := by positivity
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hy,hm,_,hr,hcop⟩
    exact ⟨⟨hlo,hhi⟩,hy,hm,by omega,hr,hcop⟩
  · rintro ⟨⟨hlo,hhi⟩,hy,hm,_,hr,hcop⟩
    exact ⟨⟨hlo,hhi⟩,hy,hm,hm,hr,hcop⟩

theorem sum_full_maskedArray {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g r s : ℕ) (c : Index S X z y medium i)
    (F : ℕ → ℕ → ℂ) :
    (∑ u ∈ Finset.range (2^r), ∑ v ∈ Finset.range (2^s), maskedArray g r s c F u v) =
      ∑ u ∈ variableBox g r medium c, ∑ v ∈ variableBox g s medium c, F u v := by
  rw [sum_prefix_maskedArray g r s (2^r) (2^s) c le_rfl le_rfl,
    ← variableBox_full_cut,← variableBox_full_cut]

theorem variableBox_subset_full {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g b cut : ℕ) (c : Index S X z y medium i) :
    variableBox g b cut c ⊆ variableBox g b medium c := by
  classical
  intro n hn
  obtain ⟨hn,hy,hm,_,hr,hcop⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hn,hy,hm,hm,hr,hcop⟩

theorem mul_maskedArray {B K X z y medium : ℕ} {S : BPZSection6Input B K}
    {i : Fin S.k} (g r s : ℕ) (c : Index S X z y medium i)
    (w F : ℕ → ℕ → ℂ) (u v : ℕ) :
    w (2^r+u) (2^s+v)*maskedArray g r s c F u v =
      maskedArray g r s c (fun x y => w x y*F x y) u v := by
  classical
  unfold maskedArray
  split_ifs <;> simp

/-- The mixed weight is removed using one maximizing rectangular prefix
per complementary index, and the result is the actual inherited first moment. -/
theorem exists_weighted_prefix_bound {B K N g : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) (e r s a : ℕ) (h : ℤ) [NeZero g]
    (hg : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors,
      max (2*S.k) 3 ≤ p ∧ p < SubpowerScale.z N S.k)
    (hindex : i.val ≤ SubpowerScale.X N S.k)
    (H : ℕ) (hh : h.natAbs ≤ H)
    (row column : ActualIndex S N i → ℕ → ℂ)
    (hrow : ∀ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
      ∀ u ∈ variableBox g r (SubpowerScale.medium N S.k) c, ‖row c u‖ ≤ 1) :
    ∃ rCut sCut : ActualIndex S N i → ℕ,
      (∑ c ∈ activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s,
        ‖∑ u ∈ variableBox g r (SubpowerScale.medium N S.k) c,
          ∑ v ∈ variableBox g s (SubpowerScale.medium N S.k) c,
          FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
            ((modulus S g (product c) : ℝ)*u*v)⁻¹ *
            (row c u*column c v*momentKernel S i a h hg hsupport c u v)‖) ≤
      (128*(B : ℝ)+40960*H*B^2+2097152*(H : ℝ)^2*B^3)*
        firstMoment S N i e r s a h hg hsupport rCut sCut column := by
  classical
  let I := activeIndices S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
    (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k) i e r s
  let w := fun (c : ActualIndex S N i) (u v : ℕ) =>
    FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
      ((modulus S g (product c) : ℝ)*u*v)⁻¹
  let f := fun (c : ActualIndex S N i) (u v : ℕ) =>
    row c u*column c v*momentKernel S i a h hg hsupport c u v
  -- The translated weight is written with the casts already pushed inside, so
  -- that it matches `active_tent_mixedVariation_le` syntactically.
  let w' := fun (c : ActualIndex S N i) (u v : ℕ) =>
    FourierVariation.tentWeight (SubpowerScale.X N S.k) h (-(i.val : ℤ))
      ((modulus S g (product c) : ℝ)*(2^r+u)*(2^s+v))⁻¹
  have hww : ∀ (c : ActualIndex S N i) (u v : ℕ), w' c u v = w c (2^r+u) (2^s+v) := by
    intro c u v
    simp only [w, w', Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  let V : ℝ := 128*B+40960*H*B^2+2097152*(H : ℝ)^2*B^3
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨rn,sn,hcuts,hmass⟩ := FamilyMixedAbel.exists_prefix_maximizers I
    w' (fun c => maskedArray g r s c (f c)) (2^r) (2^s) hV
    (fun c hc => active_tent_mixedVariation_le hc (SubpowerScale.X_pos N S.k) hindex h H hh)
  let rCut := fun c => 2^r+rn c-1
  let sCut := fun c => 2^s+sn c-1
  refine ⟨rCut,sCut,?_⟩
  have hleft (c : ActualIndex S N i) :
      (∑ u ∈ Finset.range (2^r), ∑ v ∈ Finset.range (2^s),
        w' c u v*maskedArray g r s c (f c) u v) =
      ∑ u ∈ variableBox g r (SubpowerScale.medium N S.k) c,
        ∑ v ∈ variableBox g s (SubpowerScale.medium N S.k) c, w c u v*f c u v := by
    simp_rw [hww, mul_maskedArray]
    exact sum_full_maskedArray g r s c (fun u v => w c u v*f c u v)
  simp_rw [hleft] at hmass
  apply hmass.trans
  apply mul_le_mul_of_nonneg_left ?_ hV
  have hprefix : (∑ c ∈ I,
      FamilyMixedAbel.prefixNorm (fun c => maskedArray g r s c (f c)) c (rn c) (sn c)) =
      ∑ c ∈ I, ‖∑ u ∈ variableBox g r (rCut c) c,
        ∑ v ∈ variableBox g s (sCut c) c, f c u v‖ := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [FamilyMixedAbel.prefixNorm]
    rw [sum_prefix_maskedArray g r s (rn c) (sn c) c (hcuts c hc).1 (hcuts c hc).2]
  rw [hprefix]
  exact twisted_prefix_mass_le_firstMoment S i e r s a h hg hsupport rCut sCut row column
    (fun c hc u hu => hrow c hc u ((variableBox_subset_full g r (rCut c) c) hu))

end Erdos387Proof.ConvenientWeightedPrefix

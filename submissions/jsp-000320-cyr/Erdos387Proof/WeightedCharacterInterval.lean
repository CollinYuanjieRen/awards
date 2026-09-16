import Erdos387Proof.WeightedFourierVariation

/-! Whole-interval character bounds applied to the actual reciprocal tent
weight. Fourier twists are additive characters on exactly the original domain. -/

set_option autoImplicit false
namespace Erdos387Proof.WeightedCharacterInterval
open FiniteAbel FourierVariation WeightedFourierVariation
open scoped BigOperators

noncomputable def intCharacter (q : ℕ) [NeZero q] (h : ZMod q) : AddChar ℤ ℂ where
  toFun n := ZMod.stdAddChar (h*(n : ZMod q))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    simp only [Int.cast_add,mul_add,AddChar.map_add_eq_mul]

@[simp] theorem intCharacter_apply (q : ℕ) [NeZero q] (h : ZMod q) (n : ℤ) :
    intCharacter q h n=ZMod.stdAddChar (h*(n : ZMod q)) := rfl

@[simp] theorem norm_intCharacter (q : ℕ) [NeZero q] (h : ZMod q) (n : ℤ) :
    ‖intCharacter q h n‖=1 := by simp

theorem sum_nat_Ioc_eq_sum_range (A N : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc A (A+N), f n)=∑ j ∈ Finset.range N, f (A+1+j) := by
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => A+1+j)
  · intro j hj
    have := Finset.mem_range.mp hj
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro a ha b hb he
    omega
  · intro n hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hn
    refine ⟨n-A-1,Finset.mem_range.mpr (by omega),?_⟩
    omega
  · intro j hj
    rfl

/-- Every hypothesis concerns a character twist of the entire interval. -/
theorem norm_weighted_Ioc_le (A N : ℕ) (w f : ℕ → ℂ) {B : ℝ}
    (htwist : ∀ χ : AddChar ℤ ℂ, (∀ n, ‖χ n‖=1) →
      ‖∑ n ∈ Finset.Ioc A (A+N), χ (n : ℤ)*f n‖≤B) :
    ‖∑ n ∈ Finset.Ioc A (A+N), w n*f n‖ ≤
      variationMass (fun j => w (A+1+j)) N*(Real.log (N+1 : ℕ)+1)*B := by
  let : NeZero (N+1) := ⟨by omega⟩
  rw [sum_nat_Ioc_eq_sum_range]
  apply norm_weighted_sum_le_of_twists (N+1) (A : ℤ) N
    (fun j => w (A+1+j)) (fun j => f (A+1+j)) (by omega)
  intro h
  have ht := htwist (intCharacter (N+1) (-h)) (norm_intCharacter _ _)
  rw [sum_nat_Ioc_eq_sum_range] at ht
  simpa only [intCharacter_apply,Nat.cast_add,Nat.cast_one,
    Int.cast_add,Int.cast_one,Int.cast_natCast] using ht

/-- No analytic restriction on prefixes is introduced when removing the
actual tent coefficient from a full interval. -/
theorem norm_tent_weighted_Ioc_le (X M A N : ℕ) (h i : ℤ) (f : ℕ → ℂ)
    {R H B : ℝ} (hX : 0<X) (hM : 0<M) (hR : 0≤R) (hH : 0≤H)
    (hh : |(h : ℝ)|≤H) (hi : |i|≤(X : ℤ))
    (hbound : (X : ℝ)/(M*(A+1) : ℕ)≤R)
    (htwist : ∀ χ : AddChar ℤ ℂ, (∀ n, ‖χ n‖=1) →
      ‖∑ n ∈ Finset.Ioc A (A+N), χ (n : ℤ)*f n‖≤B) :
    ‖∑ n ∈ Finset.Ioc A (A+N), tentWeight X h i (M*n : ℕ)⁻¹*f n‖ ≤
      (8*R+128*H*R^2)*(Real.log (N+1 : ℕ)+1)*B := by
  have hB : 0≤B := (norm_nonneg _).trans (htwist 1 (by simp))
  have hlog : 0≤Real.log (N+1 : ℕ)+1 := by
    have : (1 : ℝ)≤(N+1 : ℕ) := by exact_mod_cast (show 1≤N+1 by omega)
    linarith [Real.log_nonneg this]
  apply (norm_weighted_Ioc_le A N _ f htwist).trans
  apply mul_le_mul_of_nonneg_right _ hB
  apply mul_le_mul_of_nonneg_right _ hlog
  apply variationMass_tentWeight_reciprocal_le X h i (fun j => M*(A+1+j)) N
    hX hR hH hh hi
  · intro j
    exact Nat.mul_pos hM (by omega)
  · intro a b hab
    exact Nat.mul_le_mul_left M (by omega)
  · simpa only [Nat.add_zero] using hbound

end Erdos387Proof.WeightedCharacterInterval

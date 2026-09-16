import MerLeanExperiment.SquareConstruction

namespace ReciprocalSquares

theorem high_primeFactors_rootProduct (N a : ℕ) (S : Finset ℕ)
    (ha : a ∈ Nat.smoothNumbers (N + 1)) (hS : S ⊆ largePrimes N) :
    ((a * S.prod id).primeFactors.filter (fun p => N < p)) = S := by
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => largePrimes_prime (hS hp)
  have hprod0 : S.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p hp => (hprime p hp).ne_zero)
  simp only [id_eq] at hprod0 ⊢
  rw [Nat.primeFactors_mul (Nat.ne_zero_of_mem_smoothNumbers ha) hprod0,
    Nat.primeFactors_prod hprime]
  ext p
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hp | hp, hNp⟩
    · have hfact := Nat.mem_primeFactors.mp hp
      have hsmall := Nat.mem_smoothNumbers'.mp ha p hfact.1 hfact.2.1
      omega
    · exact hp
  · intro hp
    exact ⟨Or.inr hp, (Finset.mem_filter.mp (hS hp)).2⟩

/-- The explicit large-prime support recovers the subset and hence the
smooth root, so different construction pairs never collapse. -/
theorem rootProduct_injOn (N : ℕ) :
    Set.InjOn rootProduct
      (↑((smoothRoots N).product (largePrimes N).powerset) :
        Set (ℕ × Finset ℕ)) := by
  intro ⟨a, S⟩ haS ⟨b, T⟩ hbT heq
  obtain ⟨ha, hS⟩ := Finset.mem_product.mp haS
  obtain ⟨hb, hT⟩ := Finset.mem_product.mp hbT
  have haSmooth := (Finset.mem_filter.mp ha).2
  have hbSmooth := (Finset.mem_filter.mp hb).2
  have hSsub := Finset.mem_powerset.mp hS
  have hTsub := Finset.mem_powerset.mp hT
  change a * S.prod id = b * T.prod id at heq
  have hST : S = T := by
    calc
      S = (a * S.prod id).primeFactors.filter (fun p => N < p) :=
        (high_primeFactors_rootProduct N a S haSmooth hSsub).symm
      _ = (b * T.prod id).primeFactors.filter (fun p => N < p) := by rw [heq]
      _ = T := high_primeFactors_rootProduct N b T hbSmooth hTsub
  subst T
  have hprod0 : S.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p hp => (largePrimes_prime (hSsub hp)).ne_zero)
  have hab : a = b := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hprod0) heq
  subst b
  rfl

end ReciprocalSquares

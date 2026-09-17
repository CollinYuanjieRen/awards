import Mathlib

namespace Erdos30

/-- `A` is a Sidon set: equal pairwise sums force a matching summand. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → a = c ∨ a = d

theorem choose_two_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card.choose 2 ≤ N - 1 := by
  -- rewrite `choose 2` as the cardinality of the 2-element subsets
  rw [← Finset.card_powersetCard 2 A]
  have hcardIcc : (Finset.Icc 1 (N - 1)).card = N - 1 := by
    rw [Nat.card_Icc]; omega
  rw [← hcardIcc]
  refine Finset.card_le_card_of_injOn
    (f := fun s => if h : s.Nonempty then s.max' h - s.min' h else 0) ?_ ?_
  · -- the difference of a 2-subset lands in `Icc 1 (N-1)`
    intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    obtain ⟨hsub, hcard⟩ := hs
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    simp only [dite_eq_left hne]
    have hlt : s.min' hne < s.max' hne := Finset.min'_lt_max'_of_card (s := s) (by omega)
    have hminA : s.min' hne ∈ A := hsub (Finset.min'_mem s hne)
    have hmaxA : s.max' hne ∈ A := hsub (Finset.max'_mem s hne)
    have h1 := Finset.mem_Icc.mp (hA hminA)
    have h2 := Finset.mem_Icc.mp (hA hmaxA)
    rw [Finset.mem_coe, Finset.mem_Icc]
    omega
  · -- injectivity via the Sidon property
    intro s hs t ht heq
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs ht
    obtain ⟨hsub_s, hcard_s⟩ := hs
    obtain ⟨hsub_t, hcard_t⟩ := ht
    have hne_s : s.Nonempty := Finset.card_pos.mp (by omega)
    have hne_t : t.Nonempty := Finset.card_pos.mp (by omega)
    simp only [dite_eq_left hne_s, dite_eq_left hne_t] at heq
    have hab : s.min' hne_s < s.max' hne_s := Finset.min'_lt_max'_of_card (s := s) (by omega)
    have hce : t.min' hne_t < t.max' hne_t := Finset.min'_lt_max'_of_card (s := t) (by omega)
    have hsum : s.min' hne_s + t.max' hne_t = s.max' hne_s + t.min' hne_t := by omega
    have hminsA : s.min' hne_s ∈ A := hsub_s (Finset.min'_mem s hne_s)
    have hmaxsA : s.max' hne_s ∈ A := hsub_s (Finset.max'_mem s hne_s)
    have hmintA : t.min' hne_t ∈ A := hsub_t (Finset.min'_mem t hne_t)
    have hmaxtA : t.max' hne_t ∈ A := hsub_t (Finset.max'_mem t hne_t)
    have hsidon := hS (s.min' hne_s) hminsA (t.max' hne_t) hmaxtA
      (s.max' hne_s) hmaxsA (t.min' hne_t) hmintA hsum
    have hmineq : s.min' hne_s = t.min' hne_t := by
      rcases hsidon with h | h
      · omega
      · exact h
    have hmaxeq : s.max' hne_s = t.max' hne_t := by omega
    have hpair_card_s : ({s.min' hne_s, s.max' hne_s} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; omega),
        Finset.card_singleton]
    have hpair_card_t : ({t.min' hne_t, t.max' hne_t} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; omega),
        Finset.card_singleton]
    have hs_eq : s = {s.min' hne_s, s.max' hne_s} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]; exact Finset.min'_mem s hne_s
        · rw [Finset.mem_singleton] at h; rw [h]; exact Finset.max'_mem s hne_s
      · omega
    have ht_eq : t = {t.min' hne_t, t.max' hne_t} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]; exact Finset.min'_mem t hne_t
        · rw [Finset.mem_singleton] at h; rw [h]; exact Finset.max'_mem t hne_t
      · omega
    rw [hs_eq, ht_eq, hmineq, hmaxeq]

theorem card_mul_pred_le {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card * (A.card - 1) ≤ 2 * (N - 1) := by
  have hbound := choose_two_le hA hS
  have hdvd : 2 ∣ A.card * (A.card - 1) := by
    rcases A.card with _ | m
    · simp
    · rw [Nat.succ_sub_one, Nat.mul_comm]
      exact (Nat.even_mul_succ_self m).two_dvd
  have key : 2 * A.card.choose 2 = A.card * (A.card - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' hdvd]
  omega

end Erdos30

#print axioms Erdos30.choose_two_le
#print axioms Erdos30.card_mul_pred_le

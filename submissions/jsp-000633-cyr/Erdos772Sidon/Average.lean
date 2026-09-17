import Erdos772Sidon.Count
import Erdos772Sidon.Binom

/-! Averaging over `s`-element subsets: some subset has few bad quadruples. -/

namespace Erdos772

theorem sum_card_badTuples_eq (A : Finset ℕ) (s : ℕ) :
    ∑ S ∈ A.powersetCard s, (badTuples S).card
      = ∑ t ∈ badTuples A, ((A.powersetCard s).filter (fun S => elems t ⊆ S)).card := by
  have h1 : ∀ S ∈ A.powersetCard s,
      (badTuples S).card = ∑ t ∈ badTuples A, if elems t ⊆ S then 1 else 0 := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [badTuples_eq_filter A S hS.1]
    exact (Finset.sum_boole _ _).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact Finset.sum_boole _ _

/-- Every entry of a bad tuple of `A` lies in `A`. -/
private theorem elems_subset {t : (ℕ × ℕ) × (ℕ × ℕ)} {A : Finset ℕ} (ht : t ∈ badTuples A) :
    elems t ⊆ A := by
  have h := (Finset.mem_filter.1 ht).1
  simp only [Finset.mem_product] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  simp only [elems, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact ⟨h1, h2, h3, h4⟩

/-- The number of `s`-subsets of `A` containing a fixed `j`-element subset `T`, weighted by
`A.card ^ j`, is at most `A.card.choose s * s ^ j`.  (When `s < j` no such subset exists.) -/
private theorem card_filter_subset_mul_le (A T : Finset ℕ) (hT : T ⊆ A) (s j : ℕ)
    (hj : T.card = j) (hs : s ≤ A.card) :
    ((A.powersetCard s).filter (fun S => T ⊆ S)).card * A.card ^ j
      ≤ A.card.choose s * s ^ j := by
  rcases Nat.lt_or_ge s j with h | h
  · have he : ((A.powersetCard s).filter (fun S => T ⊆ S)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro S hS hsub
      rw [Finset.mem_powersetCard] at hS
      have h2 := Finset.card_le_card hsub
      rw [hj, hS.2] at h2
      omega
    rw [he]
    simp
  · have h1 := card_powersetCard_filter_subset_le A T hT s
    rw [hj] at h1
    calc ((A.powersetCard s).filter (fun S => T ⊆ S)).card * A.card ^ j
        ≤ (A.card - j).choose (s - j) * A.card ^ j := Nat.mul_le_mul h1 le_rfl
      _ ≤ A.card.choose s * s ^ j := choose_sub_mul_pow_le A.card s j h hs

/-- Pure arithmetic core of the averaging argument. -/
private theorem average_arith (C k n s P Q : ℕ) (hs1 : 1 ≤ s) (hn1 : 1 ≤ n)
    (h6 : 6 * k * s ^ 3 ≤ n ^ 2)
    (hP : P * n ^ 3 ≤ 2 * (k * n) * (C * s ^ 3))
    (hQ : Q * n ^ 4 ≤ k * n ^ 2 * (C * s ^ 4)) :
    2 * (P + Q) ≤ C * s := by
  have hn4 : 0 < n ^ 4 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hn4
  calc 2 * (P + Q) * n ^ 4 = 2 * (P * n ^ 3 * n) + 2 * (Q * n ^ 4) := by ring
    _ ≤ 2 * (2 * (k * n) * (C * s ^ 3) * n) + 2 * (k * n ^ 2 * (C * s ^ 4)) :=
        Nat.add_le_add (Nat.mul_le_mul le_rfl (Nat.mul_le_mul hP le_rfl))
          (Nat.mul_le_mul le_rfl hQ)
    _ = C * (k * n ^ 2) * s ^ 3 * (4 + 2 * s) := by ring
    _ ≤ C * (k * n ^ 2) * s ^ 3 * (6 * s) := Nat.mul_le_mul le_rfl (by omega)
    _ = C * s * (6 * k * s ^ 3) * n ^ 2 := by ring
    _ ≤ C * s * n ^ 2 * n ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul le_rfl h6) le_rfl
    _ = C * s * n ^ 4 := by ring

theorem exists_subset_few_bad (k : ℕ) (A : Finset ℕ) (hA : RepBounded k A) (s : ℕ)
    (hs : s ≤ A.card) (h6 : 6 * k * s ^ 3 ≤ A.card ^ 2) :
    ∃ S ∈ A.powersetCard s, 2 * (badTuples S).card ≤ s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · refine ⟨∅, Finset.mem_powersetCard.2 ⟨Finset.empty_subset _, Finset.card_empty⟩, ?_⟩
    simp [badTuples]
  have hn1 : 1 ≤ A.card := le_trans hs1 hs
  have hne : (A.powersetCard s).Nonempty := Finset.powersetCard_nonempty.2 hs
  refine Finset.exists_le_of_sum_le (f := fun S => 2 * (badTuples S).card) (g := fun _ => s)
    hne ?_
  have hsum : ∑ _S ∈ A.powersetCard s, s = A.card.choose s * s := by
    rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
  rw [hsum, ← Finset.mul_sum, sum_card_badTuples_eq]
  set f : (ℕ × ℕ) × (ℕ × ℕ) → ℕ :=
    fun t => ((A.powersetCard s).filter (fun S => elems t ⊆ S)).card with hf
  have hsplit : ∑ t ∈ badTuples A, f t
      = (∑ t ∈ (badTuples A).filter HasRepeat, f t)
        + ∑ t ∈ (badTuples A).filter (fun t => ¬ HasRepeat t), f t :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hP : (∑ t ∈ (badTuples A).filter HasRepeat, f t) * A.card ^ 3
      ≤ 2 * (k * A.card) * (A.card.choose s * s ^ 3) := by
    have h1 : ∀ t ∈ (badTuples A).filter HasRepeat,
        f t * A.card ^ 3 ≤ A.card.choose s * s ^ 3 := by
      intro t ht
      rw [Finset.mem_filter] at ht
      exact card_filter_subset_mul_le A (elems t) (elems_subset ht.1) s 3
        (card_elems_of_repeat t A ht.1 ht.2) hs
    calc (∑ t ∈ (badTuples A).filter HasRepeat, f t) * A.card ^ 3
        = ∑ t ∈ (badTuples A).filter HasRepeat, f t * A.card ^ 3 := Finset.sum_mul ..
      _ ≤ ∑ _t ∈ (badTuples A).filter HasRepeat, A.card.choose s * s ^ 3 :=
          Finset.sum_le_sum h1
      _ = ((badTuples A).filter HasRepeat).card * (A.card.choose s * s ^ 3) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 * (k * A.card) * (A.card.choose s * s ^ 3) :=
          Nat.mul_le_mul (card_badTuples_repeat_le k A hA) le_rfl
  have hQ : (∑ t ∈ (badTuples A).filter (fun t => ¬ HasRepeat t), f t) * A.card ^ 4
      ≤ k * A.card ^ 2 * (A.card.choose s * s ^ 4) := by
    have h1 : ∀ t ∈ (badTuples A).filter (fun t => ¬ HasRepeat t),
        f t * A.card ^ 4 ≤ A.card.choose s * s ^ 4 := by
      intro t ht
      rw [Finset.mem_filter] at ht
      exact card_filter_subset_mul_le A (elems t) (elems_subset ht.1) s 4
        (card_elems_of_not_repeat t A ht.1 ht.2) hs
    calc (∑ t ∈ (badTuples A).filter (fun t => ¬ HasRepeat t), f t) * A.card ^ 4
        = ∑ t ∈ (badTuples A).filter (fun t => ¬ HasRepeat t), f t * A.card ^ 4 :=
          Finset.sum_mul ..
      _ ≤ ∑ _t ∈ (badTuples A).filter (fun t => ¬ HasRepeat t),
            A.card.choose s * s ^ 4 := Finset.sum_le_sum h1
      _ = ((badTuples A).filter (fun t => ¬ HasRepeat t)).card
            * (A.card.choose s * s ^ 4) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ k * A.card ^ 2 * (A.card.choose s * s ^ 4) :=
          Nat.mul_le_mul (le_trans (Finset.card_filter_le _ _) (card_badTuples_le k A hA)) le_rfl
  exact average_arith _ k A.card s _ _ hs1 hn1 h6 hP hQ

end Erdos772

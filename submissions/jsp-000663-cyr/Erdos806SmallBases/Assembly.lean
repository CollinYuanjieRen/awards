import Erdos806SmallBases.Digits
import Erdos806SmallBases.Chunks

/-! The basis built from blocks, chunks and shifts, with its cardinality bound. -/

namespace Erdos806

/-- Summing floor divisions is at most the floor division of the sum. -/
private theorem sum_div_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (k : ℕ) :
    ∑ i ∈ s, f i / k ≤ (∑ i ∈ s, f i) / k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (Nat.add_le_add_left ih _) Nat.div_add_div_le_add_div

theorem exists_basis_bound (q k n : ℕ) (hq : 0 < q) (hk : 0 < k) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) :
    ∃ B : Finset ℤ, HasBasis A B ∧ B.card ≤ 2 * k * q ^ (k - 1) + A.card / k + n / q ^ k + 1 := by
  have hM0 : 0 < q ^ k := pow_pos hq k
  -- Cut the part of `A` in block `j` into at most `(A ∩ block j).card / k + 1` chunks.
  choose m T hm hT hcov using fun j : ℕ =>
    exists_chunks k hk ((A.filter (fun a => a / q ^ k = j)).image (fun a => a % q ^ k))
  -- For every chunk pick a shift landing all its elements in the universal set.
  choose g hg1 hg2 using fun j t : ℕ => exists_shift q k hq (T j t) (hT j t)
  refine ⟨((univSet q k) ∪ (univSet q k).image (fun u => u + q ^ k)).image (fun u : ℕ => (u : ℤ)) ∪
      (Finset.range (n / q ^ k + 1)).biUnion (fun j =>
        (Finset.range (m j)).image (fun t => (j : ℤ) * ((q ^ k : ℕ) : ℤ) - (g j t : ℤ))), ?_, ?_⟩
  · -- `B` is a basis for `A`.
    intro a ha
    have han : a ≤ n := (Finset.mem_Icc.1 (hA ha)).2
    obtain ⟨j, s, hsM, rfl⟩ : ∃ j s, s < q ^ k ∧ a = q ^ k * j + s :=
      ⟨a / q ^ k, a % q ^ k, Nat.mod_lt _ hM0, (Nat.div_add_mod a (q ^ k)).symm⟩
    have hdiv : (q ^ k * j + s) / q ^ k = j := by
      rw [Nat.mul_add_div hM0, Nat.div_eq_of_lt hsM, Nat.add_zero]
    have hmod : (q ^ k * j + s) % q ^ k = s := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hsM]
    have hjJ : j < n / q ^ k + 1 := by
      have h1 : (q ^ k * j + s) / q ^ k ≤ n / q ^ k := Nat.div_le_div_right han
      rw [hdiv] at h1
      omega
    have hsS : s ∈ (A.filter (fun a => a / q ^ k = j)).image (fun a => a % q ^ k) :=
      Finset.mem_image.2 ⟨q ^ k * j + s, Finset.mem_filter.2 ⟨ha, hdiv⟩, hmod⟩
    obtain ⟨t, htm, hst⟩ := Finset.mem_biUnion.1 (hcov j hsS)
    -- The shifted residue lies in the universal set, and the carry `e` is `0` or `1`.
    obtain ⟨u, e, humem, hele, hsplit⟩ :
        ∃ u e, u ∈ univSet q k ∧ e ≤ 1 ∧ q ^ k * e + u = s + g j t := by
      refine ⟨(s + g j t) % q ^ k, (s + g j t) / q ^ k, hg2 j t s hst, ?_, Nat.div_add_mod _ _⟩
      have h2 : g j t < q ^ k := hg1 j t
      have h3 : (s + g j t) / q ^ k < 2 := (Nat.div_lt_iff_lt_mul hM0).2 (by omega)
      omega
    refine ⟨(j : ℤ) * ((q ^ k : ℕ) : ℤ) - (g j t : ℤ), ?_, ((u + e * q ^ k : ℕ) : ℤ), ?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨j, Finset.mem_range.2 hjJ, Finset.mem_image.2 ⟨t, htm, rfl⟩⟩)
    · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨u + e * q ^ k, ?_, rfl⟩)
      rcases (by omega : e = 0 ∨ e = 1) with he0 | he1
      · rw [he0, Nat.zero_mul, Nat.add_zero]
        exact Finset.mem_union_left _ humem
      · rw [he1, Nat.one_mul]
        exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, humem, rfl⟩)
    · have h1 : (q : ℤ) ^ k * (e : ℤ) + (u : ℤ) = (s : ℤ) + (g j t : ℤ) := by
        exact_mod_cast hsplit
      push_cast
      linarith
  · -- The cardinality bound.
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : (((univSet q k) ∪ (univSet q k).image (fun u => u + q ^ k)).image
        (fun u : ℕ => (u : ℤ))).card ≤ 2 * (k * q ^ (k - 1)) := by
      refine le_trans Finset.card_image_le (le_trans (Finset.card_union_le _ _) ?_)
      have hc1 : (univSet q k).card ≤ k * q ^ (k - 1) := card_univSet q k
      have hc2 : ((univSet q k).image (fun u => u + q ^ k)).card ≤ k * q ^ (k - 1) :=
        le_trans Finset.card_image_le hc1
      omega
    have h2 : ((Finset.range (n / q ^ k + 1)).biUnion (fun j =>
        (Finset.range (m j)).image
          (fun t => (j : ℤ) * ((q ^ k : ℕ) : ℤ) - (g j t : ℤ)))).card
        ≤ A.card / k + n / q ^ k + 1 := by
      refine le_trans Finset.card_biUnion_le ?_
      have step : ∀ j ∈ Finset.range (n / q ^ k + 1),
          ((Finset.range (m j)).image
            (fun t => (j : ℤ) * ((q ^ k : ℕ) : ℤ) - (g j t : ℤ))).card
            ≤ (A.filter (fun a => a / q ^ k = j)).card / k + 1 := by
        intro j _
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_range]
        exact le_trans (hm j)
          (Nat.add_le_add_right (Nat.div_le_div_right Finset.card_image_le) 1)
      refine le_trans (Finset.sum_le_sum step) ?_
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have hsum2 := sum_div_le (Finset.range (n / q ^ k + 1))
        (fun j => (A.filter (fun a => a / q ^ k = j)).card) k
      have hcard : ∑ j ∈ Finset.range (n / q ^ k + 1),
          (A.filter (fun a => a / q ^ k = j)).card = A.card := by
        refine (Finset.card_eq_sum_card_fiberwise ?_).symm
        intro a ha
        have han : a ≤ n := (Finset.mem_Icc.1 (hA ha)).2
        exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right han))
      rw [hcard] at hsum2
      omega
    refine le_trans (Nat.add_le_add h1 h2) (le_of_eq ?_)
    ring

end Erdos806

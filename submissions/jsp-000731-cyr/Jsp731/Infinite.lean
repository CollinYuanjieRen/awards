import Jsp731.Construction
import Jsp731.OrderTwo
import Jsp731.Coverage

/-!
# JSP-000731 / Erdős #880 — infinitude of the exact restricted sumset

For `h ≥ 3` the set of sums of exactly `h` distinct elements of `insert 0 (basis h)` is infinite:
the finset consisting of `0` together with the `h − 1` spikes of block `n` has exactly `h`
elements, all of them in `insert 0 (basis h)`, and its sum grows strictly with `n`.
-/

namespace Erdos880

variable {h : ℕ}

/-- A strictly monotone sequence of elements witnesses that `exactDistinctSums A k` is infinite. -/
theorem exactDistinctSums_infinite_of_forall_exists {A : Set ℕ} {k : ℕ}
    (f : ℕ → ℕ) (hf : StrictMono f) (hmem : ∀ n, f n ∈ exactDistinctSums A k) :
    (exactDistinctSums A k).Infinite :=
  Set.infinite_of_injective_forall_mem hf.injective hmem

/-- The spikes of block `n`, as a finset. -/
private def spikes (h n : ℕ) : Finset ℕ :=
  (Finset.range (h - 1)).image fun j => scale h n + 2 ^ j * (scale h n) ^ 2

private lemma card_spikes (hh : 3 ≤ h) (n : ℕ) : (spikes h n).card = h - 1 := by
  rw [spikes, Finset.card_image_of_injective _ (spike_injective hh n), Finset.card_range]

private lemma zero_notMem_spikes (hh : 3 ≤ h) (n : ℕ) : (0 : ℕ) ∉ spikes h n := by
  simp only [spikes, Finset.mem_image, Finset.mem_range, not_exists]
  rintro j ⟨-, hj⟩
  have := three_le_scale hh n
  omega

private lemma spikes_subset (n : ℕ) : (↑(spikes h n) : Set ℕ) ⊆ basis h := by
  intro a ha
  simp only [spikes, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  exact block_subset_basis h n (Or.inr ⟨j, hj, rfl⟩)

/-- The witness: the sum of the `h − 1` spikes of block `n`. -/
private def spikeSum (h n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (h - 1), (scale h n + 2 ^ j * (scale h n) ^ 2)

private lemma sum_spikes_eq (hh : 3 ≤ h) (n : ℕ) :
    ∑ a ∈ insert 0 (spikes h n), a = spikeSum h n := by
  rw [Finset.sum_insert (zero_notMem_spikes hh n), zero_add, spikes,
    Finset.sum_image fun a _ b _ hab => spike_injective hh n hab, spikeSum]

private lemma spikeSum_strictMono (hh : 3 ≤ h) : StrictMono (spikeSum h) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hlt : scale h n < scale h (n + 1) := scale_lt_succ hh n
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · exact Finset.nonempty_range_iff.mpr (by omega)
  · intro j _
    have h1 : (scale h n) ^ 2 < (scale h (n + 1)) ^ 2 := Nat.pow_lt_pow_left hlt (by omega)
    have h2 : 2 ^ j * (scale h n) ^ 2 < 2 ^ j * (scale h (n + 1)) ^ 2 :=
      Nat.mul_lt_mul_of_pos_left h1 (Nat.two_pow_pos j)
    omega

/-- The set of sums of exactly `h` distinct elements of `insert 0 (basis h)` is infinite. -/
theorem exactDistinctSums_insert_zero_basis_infinite (hh : 3 ≤ h) :
    (exactDistinctSums (insert 0 (basis h)) h).Infinite := by
  refine exactDistinctSums_infinite_of_forall_exists (spikeSum h) (spikeSum_strictMono hh)
    fun n => ⟨insert 0 (spikes h n), ?_, ?_, sum_spikes_eq hh n⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (spikes_subset n ha)
  · rw [Finset.card_insert_of_notMem (zero_notMem_spikes hh n), card_spikes hh n]
    omega

end Erdos880

#print axioms Erdos880.exactDistinctSums_insert_zero_basis_infinite

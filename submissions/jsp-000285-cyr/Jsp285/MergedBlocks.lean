import Jsp285.InfiniteSums
import ErdosProblems.Erdos344

/-! Merge disjoint occurrence blocks while their positive AP steps divide one fixed integer. -/

namespace Jsp285

open scoped Pointwise

/-- The exponentially increasing target length of block `i`. -/
def blockLength (L i : ℕ) : ℕ := 2 ^ i * L

/-- The occurrence indices used through block `i`. -/
def usedBlocks (B : ℕ → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range (i + 1)).biUnion B

/-- The next disjoint block can be merged using the gcd of the progression steps. -/
theorem exists_merged_occurrence_blocks (v : ℕ → ℕ) (B : ℕ → Finset ℕ)
    (L : ℕ) (_hL : 2 ≤ L) (hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (hAP : ∀ i, ∃ a d : ℕ, 0 < d ∧ 16 * d ≤ blockLength L i ∧
      ∀ j < blockLength L i, a + j * d ∈ occurrenceSums v (B i)) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ a d : ℕ, 0 < d ∧ d ∣ D ∧
      ∀ j < blockLength L i / 2, a + j * d ∈ occurrenceSums v (usedBlocks B i) := by
  obtain ⟨a₀, D, hD, hDsmall, hAP₀⟩ := hAP 0
  have hDL : 16 * D ≤ L := by simpa [blockLength] using hDsmall
  refine ⟨D, hD, ?_⟩
  intro i
  induction i with
  | zero =>
    refine ⟨a₀, D, hD, dvd_rfl, ?_⟩
    intro j hj
    simpa [usedBlocks] using hAP₀ j (hj.trans_le (Nat.div_le_self _ _))
  | succ i ih =>
    obtain ⟨aOld, dOld, hdOld, hdOldD, hOld⟩ := ih
    obtain ⟨aNew, dNew, hdNew, hdNewBound, hNew⟩ := hAP (i + 1)
    let q := Nat.gcd dNew dOld
    let M := dNew / q
    let r := dOld / q
    have hq : 0 < q := Nat.gcd_pos_of_pos_left dOld hdNew
    have hqdNew : q ∣ dNew := Nat.gcd_dvd_left _ _
    have hqdOld : q ∣ dOld := Nat.gcd_dvd_right _ _
    have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hdNew hqdNew) hq
    have hr : 0 < r := Nat.div_pos (Nat.le_of_dvd hdOld hqdOld) hq
    have hdNewEq : q * M = dNew := Nat.mul_div_cancel' hqdNew
    have hdOldEq : q * r = dOld := Nat.mul_div_cancel' hqdOld
    have hcop : M.Coprime r := Nat.coprime_div_gcd_div_gcd hq
    have hnext : blockLength L (i + 1) = 2 * blockLength L i := by
      simp [blockLength, pow_succ]
      ring
    have hLnext : L ≤ blockLength L (i + 1) :=
      Nat.le_mul_of_pos_left L (pow_pos (by omega) _)
    have hMle : M ≤ dNew := Nat.div_le_self _ _
    have hMU : M ≤ blockLength L i / 2 := by omega
    have hrOld : r ≤ dOld := Nat.div_le_self _ _
    have hOldD : dOld ≤ D := Nat.le_of_dvd hD hdOldD
    have hrHalf : r ≤ blockLength L (i + 1) / 2 := by omega
    have hlen : blockLength L (i + 1) / 2 ≤ M * (blockLength L (i + 1) - r) := by
      have hsub : blockLength L (i + 1) / 2 ≤ blockLength L (i + 1) - r := by omega
      exact hsub.trans (Nat.le_mul_of_pos_left _ hM)
    have hmerge := Erdos344.merge_AP_by_gcd hq hM hr hcop hMU
      (S := (occurrenceSums v (B (i + 1)) : Set ℕ))
      (U := (occurrenceSums v (usedBlocks B i) : Set ℕ))
      (by simpa [hdNewEq] using hNew) (by simpa [hdOldEq] using hOld)
    have hBU : Disjoint (B (i + 1)) (usedBlocks B i) := by
      apply Finset.disjoint_left.mpr
      intro x hxB hxU
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hxU
      have hjlt : j < i + 1 := Finset.mem_range.mp hj
      exact Finset.disjoint_left.mp (hdisj (by omega : i + 1 ≠ j)) hxB hxj
    have hUsed : B (i + 1) ∪ usedBlocks B i = usedBlocks B (i + 1) := by
      simp [usedBlocks, Finset.range_add_one, Finset.biUnion_insert]
    refine ⟨aNew + aOld + (q * M) * r, q, hq, hqdOld.trans hdOldD, ?_⟩
    intro j hj
    obtain ⟨x, hx, y, hy, hxy⟩ := hmerge j (hj.trans_le hlen)
    change x + y = aNew + aOld + (q * M) * r + j * q at hxy
    have hsum := add_mem_occurrenceSums hBU hx hy
    rwa [hUsed, hxy] at hsum

end Jsp285

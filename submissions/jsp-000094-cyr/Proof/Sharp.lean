import Proof.Ramsey

/-!
# Erdős problem #1029 — the sharp Erdős–Szekeres recursion and upper bound

The finiteness proof of `MerLeanExperiment.Ramsey` uses the lossy recursion
`RamseyProp (A + B + 1) m n`.  Here we prove the sharp form
`RamseyProp (A + B) m n` (the extra vertex is not needed: the red and blue
neighbourhoods of a single vertex already partition the remaining `A + B - 1`
vertices, so one of them has `A` or `B` elements), and deduce the classical
Erdős–Szekeres bound

* `Erdos77.ramsey_le_choose_sharp` : `r(m, n) ≤ C(m + n - 2, m - 1)`;
* `Erdos77.R_le_choose`           : `R(k) ≤ C(2k - 2, k - 1)`;
* `Erdos77.R_le_choose_page`      : `R(k) ≤ C(2k - 1, k - 1)`, the form printed on the
  Erdős problem page.

Reused from our own JSP-000855 package (Erdős #1029).
-/

namespace Erdos77

open SimpleGraph

/-- The classical recursion without loss: if `A` works for `(m-1, n)` and `B` for `(m, n-1)`
and `A + B ≥ 1`, then `A + B` works for `(m, n)`. -/
theorem ramseyProp_step_sharp {A B m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hAB : 1 ≤ A + B)
    (hA : RamseyProp A (m - 1) n) (hB : RamseyProp B m (n - 1)) :
    RamseyProp (A + B) m n := by
  classical
  intro G hG
  let v : Fin (A + B) := ⟨0, hAB⟩
  have hdisj : Disjoint (G.neighborFinset v) (Gᶜ.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj] at hw'
    exact hw'.2 hw
  have hunion : G.neighborFinset v ∪ Gᶜ.neighborFinset v = Finset.univ.erase v := by
    ext w
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact (G.ne_of_adj h).symm
      · exact fun hc => h hc.symm
    · intro h
      by_cases hadj : G.Adj v w
      · exact Or.inl hadj
      · exact Or.inr ⟨fun hc => h hc.symm, hadj⟩
  have hcard : (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card = A + B - 1 := by
    have h1 := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v)] at h1
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hsplit : A ≤ (G.neighborFinset v).card ∨ B ≤ (Gᶜ.neighborFinset v).card := by omega
  rcases hsplit with h | h
  · rcases exists_clique_of_subset G _ h hA with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · have hv : ∀ b ∈ t, G.Adj v b := by
        intro b hb
        have hb' := hts hb
        rw [SimpleGraph.mem_neighborFinset] at hb'
        exact hb'
      have hcl := ht.insert hv
      rw [show m - 1 + 1 = m by omega] at hcl
      exact hG.1 _ hcl
    · exact hG.2 _ ht
  · rcases exists_clique_of_subset G _ h hB with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · exact hG.1 _ ht
    · have hv : ∀ b ∈ t, Gᶜ.Adj v b := by
        intro b hb
        have hb' := hts hb
        rw [SimpleGraph.mem_neighborFinset] at hb'
        exact hb'
      have hcl := ht.insert hv
      rw [show n - 1 + 1 = n by omega] at hcl
      exact hG.2 _ hcl

/-- Auxiliary induction for `Erdos77.ramsey_le_choose_sharp`: `C(m + n - 2, m - 1)` vertices
already force a red `K_m` or a blue `K_n`, for all `m, n ≥ 1`. -/
theorem ramseyProp_choose : ∀ k m n : ℕ, m + n ≤ k → 1 ≤ m → 1 ≤ n →
    RamseyProp ((m + n - 2).choose (m - 1)) m n := by
  intro k
  induction k with
  | zero => intro m n h hm _; omega
  | succ k ih =>
    intro m n h hm hn
    by_cases hm1 : m = 1
    · subst hm1
      rw [show (1 + n - 2).choose (1 - 1) = 1 by simp]
      exact ramseyProp_one_left n
    by_cases hn1 : n = 1
    · subst hn1
      rw [show (m + 1 - 2).choose (m - 1) = 1 by
        rw [show m + 1 - 2 = m - 1 by omega]; exact Nat.choose_self _]
      exact ramseyProp_one_right m
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 2 := ⟨n - 2, by omega⟩
    have key : RamseyProp ((a + b + 1).choose a + (a + b + 1).choose (a + 1)) (a + 2) (b + 2) := by
      refine ramseyProp_step_sharp (by omega) (by omega) ?_ ?_ ?_
      · have := Nat.choose_pos (show a ≤ a + b + 1 by omega)
        omega
      · rw [show a + 2 - 1 = a + 1 by omega]
        have hA := ih (a + 1) (b + 2) (by omega) (by omega) (by omega)
        rwa [show a + 1 + (b + 2) - 2 = a + b + 1 by omega, show a + 1 - 1 = a by omega] at hA
      · rw [show b + 2 - 1 = b + 1 by omega]
        have hB := ih (a + 2) (b + 1) (by omega) (by omega) (by omega)
        rwa [show a + 2 + (b + 1) - 2 = a + b + 1 by omega, show a + 2 - 1 = a + 1 by omega] at hB
    rw [show a + 2 + (b + 2) - 2 = a + b + 1 + 1 by omega, show a + 2 - 1 = a + 1 by omega,
      Nat.choose_succ_succ]
    exact key

/-- Erdős–Szekeres: `r(m, n) ≤ C(m + n − 2, m − 1)` for `m, n ≥ 1`. -/
theorem ramsey_le_choose_sharp (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ramsey m n ≤ (m + n - 2).choose (m - 1) :=
  ramsey_le_of_ramseyProp (ramseyProp_choose (m + n) m n le_rfl hm hn)

/-- The diagonal Erdős–Szekeres bound `R(k) ≤ C(2k − 2, k − 1)`. -/
theorem R_le_choose (k : ℕ) (hk : 1 ≤ k) : R k ≤ (2 * k - 2).choose (k - 1) := by
  have := ramsey_le_choose_sharp k k hk hk
  rwa [show k + k - 2 = 2 * k - 2 by omega] at this

/-- The form printed on the problem page. -/
theorem R_le_choose_page (k : ℕ) (hk : 1 ≤ k) : R k ≤ (2 * k - 1).choose (k - 1) :=
  le_trans (R_le_choose k hk) (Nat.choose_le_choose (k - 1) (by omega))

end Erdos77

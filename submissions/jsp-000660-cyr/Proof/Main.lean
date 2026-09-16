import Mathlib
import Proof.Defs
import Proof.Model
import Proof.Counting
import Proof.Estimates
import Proof.Existence
import Proof.Deterministic
import Proof.Transfer

/-!
# Erdős Problem 803: Alon's construction and the negative answer

**Alon (2008), Proposition 2.1.** For every `D ≥ 1` and every sufficiently large `N` there is a
graph on `N` vertices with at least `N log₂ N` edges in which every `D`-balanced subgraph on `m`
vertices has at most `18 m (4 √(log₂ m) + log₂(64 D) + 26)` edges.  (Alon states the average
degree bound `36 (4 √log₂ m + log₂(64 D) + 18)`; our integer threshold `rpar` costs a slightly
larger additive constant.)

Consequently the Erdős–Simonovits question has a negative answer: there are no absolute constants
`ε > 0`, `D` such that all large graphs with `n log₂ n` edges contain a `D`-balanced subgraph on
`m` (or at least `m₀`) vertices with `ε m log₂ m` edges.
-/

open SimpleGraph

namespace Erdos803

/-- The construction on `Vtx n` has enough edges: `N log₂ N ≤ n · 8 (top n + 1 - 4)` whenever
`2 ^ 40 ≤ n` and `N ≤ 2 n + 1`. -/
private theorem le_edge_count (n N : ℕ) (hn : 2 ^ 40 ≤ n) (hN1 : 1 ≤ N) (hN : N ≤ 2 * n + 1) :
    (N : ℝ) * Real.logb 2 N ≤ ((n * (8 * (top n + 1 - 4)) : ℕ) : ℝ) := by
  have hn' : (1099511627776 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hn0 : n ≠ 0 := by omega
  have hnR : (1099511627776 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
  have hL40 : 40 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by norm_num) hn0).2 hn
  have htop : top n = Nat.log 2 n / 2 := rfl
  obtain ⟨t, ht⟩ : ∃ t : ℕ, top n = t + 4 := ⟨top n - 4, by rw [htop] at *; omega⟩
  have hLt : Nat.log 2 n ≤ 2 * t + 9 := by rw [htop] at ht; omega
  have hLtR : (Nat.log 2 n : ℝ) ≤ 2 * (t : ℝ) + 9 := by exact_mod_cast hLt
  have hLnR : (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.log_le_self 2 n
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hx_lt : Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ) + 1 := by
    have hfl : ⌊Real.logb ((2 : ℕ) : ℝ) ((n : ℕ) : ℝ)⌋₊ = Nat.log 2 n :=
      Real.natFloor_logb_natCast 2 n
    have hlt := Nat.lt_floor_add_one (Real.logb ((2 : ℕ) : ℝ) ((n : ℕ) : ℝ))
    rw [hfl] at hlt
    simpa using hlt
  have hx40 : (40 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos,
      show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hn
  have hlog4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.logb_mul two_ne_zero two_ne_zero,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hNR : (N : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlogN : Real.logb 2 (N : ℝ) ≤ Real.logb 2 (n : ℝ) + 2 := by
    calc Real.logb 2 (N : ℝ) ≤ Real.logb 2 (4 * (n : ℝ)) :=
          Real.logb_le_logb_of_le (by norm_num) hNpos (by linarith)
      _ = Real.logb 2 4 + Real.logb 2 (n : ℝ) :=
          Real.logb_mul (by norm_num) (ne_of_gt hnpos)
      _ = Real.logb 2 (n : ℝ) + 2 := by rw [hlog4]; ring
  have hlogNnn : (0 : ℝ) ≤ Real.logb 2 (N : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hN1)
  have hstep : (N : ℝ) * Real.logb 2 (N : ℝ) ≤ (2 * (n : ℝ) + 1) * (Real.logb 2 (n : ℝ) + 2) :=
    mul_le_mul hNR hlogN hlogNnn (by linarith)
  have hgoal : (2 * (n : ℝ) + 1) * (Real.logb 2 (n : ℝ) + 2) ≤ (n : ℝ) * (8 * ((t : ℝ) + 1)) := by
    nlinarith [mul_nonneg hnpos.le (by linarith : (0 : ℝ) ≤ 2 * (t : ℝ) + 10 - Real.logb 2 (n : ℝ)),
      mul_nonneg hnpos.le (by linarith : (0 : ℝ) ≤ Real.logb 2 (n : ℝ) - 40)]
  have hcast : ((n * (8 * (top n + 1 - 4)) : ℕ) : ℝ) = (n : ℝ) * (8 * ((t : ℝ) + 1)) := by
    rw [show n * (8 * (top n + 1 - 4)) = n * (8 * (t + 1)) by
      rw [ht, show t + 4 + 1 - 4 = t + 1 from by omega]]
    push_cast
    ring
  rw [hcast]
  linarith

/-- For a fixed constant `C ≥ 0` the bound `72 √T + 18 C + 468` is eventually beaten by `ε T`. -/
private theorem exists_threshold (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → 72 * Real.sqrt T + 18 * C + 468 < ε * T := by
  refine ⟨((540 + 18 * C) / ε + 1) ^ 2 + 1, fun T hT ↦ ?_⟩
  have hq : 0 ≤ (540 + 18 * C) / ε := by positivity
  have hb : (0 : ℝ) ≤ (540 + 18 * C) / ε + 1 := by linarith
  have hTpos : (0 : ℝ) < T := by nlinarith [sq_nonneg ((540 + 18 * C) / ε + 1)]
  have hs : (540 + 18 * C) / ε + 1 ≤ Real.sqrt T := by
    calc (540 + 18 * C) / ε + 1 = Real.sqrt (((540 + 18 * C) / ε + 1) ^ 2) :=
          (Real.sqrt_sq hb).symm
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  have hs1 : (1 : ℝ) ≤ Real.sqrt T := by linarith
  have hKs : 540 + 18 * C + ε ≤ ε * Real.sqrt T := by
    have h := mul_le_mul_of_nonneg_left hs hε.le
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hε)] at h
    linarith
  have hTT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
  nlinarith [mul_le_mul_of_nonneg_right hKs (by linarith : (0 : ℝ) ≤ Real.sqrt T),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 468 + 18 * C) (by linarith : (0 : ℝ) ≤ Real.sqrt T - 1),
    mul_pos hε (lt_of_lt_of_le zero_lt_one hs1)]

/-- **Alon's construction** (Erdős Problem 803, negative direction). -/
theorem alon_construction (D : ℝ) (hD : 1 ≤ D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ G : SimpleGraph (Fin N),
      (N : ℝ) * Real.logb 2 N ≤ G.edgeSet.ncard ∧
        ∀ H : G.Subgraph, Balanced D H →
          (H.edgeSet.ncard : ℝ) ≤ 18 * H.verts.ncard *
            (4 * Real.sqrt (Real.logb 2 H.verts.ncard) + Real.logb 2 (64 * D) + 26) := by
  have hlogD : (0 : ℝ) ≤ Real.logb 2 (64 * D) := Real.logb_nonneg (by norm_num) (by linarith)
  refine ⟨2 ^ 41, fun N hN ↦ ?_⟩
  have hN' : (2199023255552 : ℕ) ≤ N := le_trans (by norm_num) hN
  have hn : 2 ^ 40 ≤ N / 2 := le_trans (by norm_num) (by omega : (1099511627776 : ℕ) ≤ N / 2)
  obtain ⟨f, hf⟩ := exists_good (N / 2) hn
  have hcard : Fintype.card (Vtx (N / 2)) ≤ N := le_trans (card_vtx_le (N / 2)) (by omega)
  obtain ⟨G, hG, hsub⟩ := exists_graph_fin (N / 2) N hcard f
  refine ⟨G, ?_, fun H hH ↦ ?_⟩
  · rw [hG, edgeSet_ncard_graphOf, card_blockIdx]
    exact le_edge_count (N / 2) N hn (by omega) (by omega)
  · rcases hsub H D hH with hemp | ⟨H', he, hv, hH'⟩
    · rw [hemp, Set.ncard_empty]
      have h2 : (0 : ℝ) ≤ Real.sqrt (Real.logb 2 H.verts.ncard) := Real.sqrt_nonneg _
      have h3 : (0 : ℝ) ≤ (H.verts.ncard : ℝ) := Nat.cast_nonneg _
      simp only [Nat.cast_zero]
      nlinarith
    · rw [← he, ← hv]
      have hmain := edges_le_of_good hf hn hD H' hH'
      rcases Nat.eq_zero_or_pos H'.verts.ncard with h0 | h0
      · rw [h0] at hmain ⊢
        simp only [Nat.cast_zero, mul_zero, zero_mul] at hmain ⊢
        exact hmain
      · have hr := rpar_le H'.verts.ncard h0
        have hmR : (0 : ℝ) ≤ (H'.verts.ncard : ℝ) := Nat.cast_nonneg _
        nlinarith

/-- The uniform Erdős–Simonovits statement is false for every choice of constants. -/
theorem not_erdosSimonovitsUniform :
    ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsUniform ε D := by
  rintro ⟨ε, D, hε, hD, h⟩
  have hD'1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have hDD' : D ≤ max D 1 := le_max_left _ _
  have hC : (0 : ℝ) ≤ Real.logb 2 (64 * max D 1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  obtain ⟨T₀, hT₀⟩ := exists_threshold ε (Real.logb 2 (64 * max D 1)) hε hC
  obtain ⟨N₀, hN₀⟩ := alon_construction (max D 1) hD'1
  obtain ⟨n₀, hn₀⟩ := h (⌈(2 : ℝ) ^ T₀⌉₊ + 2)
  obtain ⟨G, hGedge, hGsub⟩ := hN₀ (max N₀ n₀) (le_max_left _ _)
  obtain ⟨H, hHcard, hHbal, hHedge⟩ := hn₀ (max N₀ n₀) (le_max_right _ _) G hGedge
  have hmpos : (0 : ℝ) < (H.verts.ncard : ℝ) := by
    have : 0 < H.verts.ncard := by omega
    exact_mod_cast this
  have hTm : T₀ ≤ Real.logb 2 H.verts.ncard := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hmpos]
    calc (2 : ℝ) ^ T₀ ≤ (⌈(2 : ℝ) ^ T₀⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (H.verts.ncard : ℝ) := by exact_mod_cast (by omega : ⌈(2 : ℝ) ^ T₀⌉₊ ≤ H.verts.ncard)
  have hthr := hT₀ (Real.logb 2 H.verts.ncard) hTm
  have hbnd := hGsub H (Balanced.mono hDD' hHbal)
  nlinarith [mul_lt_mul_of_pos_left hthr hmpos]

/-- The literal Erdős–Simonovits statement is false for every choice of constants. -/
theorem not_erdosSimonovitsLiteral :
    ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsLiteral ε D := by
  rintro ⟨ε, D, hε, hD, h⟩
  exact not_erdosSimonovitsUniform ⟨ε, D, hε, hD, h.uniform⟩

end Erdos803

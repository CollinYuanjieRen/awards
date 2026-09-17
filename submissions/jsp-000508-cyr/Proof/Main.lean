import Proof.Lower
import Mathlib.Data.Complex.Basic

/-!
# Erdős Problem 627: Tutte–Zykov via the shift graph

Erdős' problem page for #627 records that "Tutte and Zykov independently proved that for every `k`
there is a graph with `ω(G) = 2` and `χ(G) = k`".  Combining the upper bound of
`Proof.Shift` with the lower bound of `Proof.Lower`, the shift graph on
`2 ^ k` points is a finite triangle-free graph whose chromatic number is exactly `k`; for `k ≥ 2`
it also has an edge, so its clique number is exactly `2`.

Not claimed here: the question of Erdős problem #627 itself (the limit of `f(n)/(n/(log₂ n)²)`),
Erdős's constructions with `χ ≫ n^{1/2}/log n` and the asymptotics `f(n) ≍ n/(log₂ n)²`.
-/

namespace Erdos627

/-- The shift graph on `2 ^ k` points has chromatic number exactly `k`. -/
theorem shiftGraph_chromaticNumber (k : ℕ) : (shiftGraph (2 ^ k)).chromaticNumber = (k : ℕ∞) := by
  refine le_antisymm (shiftGraph_colorable k).chromaticNumber_le ?_
  simp only [SimpleGraph.chromaticNumber]
  refine le_iInf₂ fun n hn => ?_
  simp only [Set.mem_ofPred] at hn
  exact_mod_cast le_of_colorable k n hn

/-- **Tutte–Zykov**: for every `k` there is a finite triangle-free graph with chromatic
number exactly `k`. -/
theorem exists_cliqueFree_chromatic (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞) :=
  ⟨ShiftVertex (2 ^ k), inferInstance, shiftGraph (2 ^ k), shiftGraph_cliqueFree (2 ^ k),
    shiftGraph_chromaticNumber k⟩

/-- For `2 ≤ k` the shift graph on `2 ^ k` points has an edge, namely `(0, 1) ~ (1, 2)`. -/
theorem shiftGraph_exists_adj {k : ℕ} (hk : 2 ≤ k) :
    ∃ u v : ShiftVertex (2 ^ k), (shiftGraph (2 ^ k)).Adj u v := by
  have h4 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by omega
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  refine ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩, ⟨(⟨1, by omega⟩, ⟨2, by omega⟩), ?_⟩, ?_⟩
  · exact Fin.mk_lt_mk.mpr (by omega)
  · exact Fin.mk_lt_mk.mpr (by omega)
  · refine shiftGraph_adj.mpr ⟨?_, Or.inl rfl⟩
    intro hcon
    have : (0 : ℕ) = 1 := congrArg (fun p : ShiftVertex (2 ^ k) => p.1.1.val) hcon
    omega

/-- **Tutte–Zykov** with clique number exactly `2`: for every `k ≥ 2` there is a finite
triangle-free graph with an edge whose chromatic number is exactly `k`. -/
theorem exists_cliqueNum_two_chromatic (k : ℕ) (hk : 2 ≤ k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ (∃ u v, G.Adj u v) ∧ G.chromaticNumber = (k : ℕ∞) :=
  ⟨ShiftVertex (2 ^ k), inferInstance, shiftGraph (2 ^ k), shiftGraph_cliqueFree (2 ^ k),
    shiftGraph_exists_adj hk, shiftGraph_chromaticNumber k⟩

/-- For `2 ≤ k` the shift graph on `2 ^ k` points has clique number exactly `2`, i.e. `ω(G) = 2`
in the notation of the problem page. -/
theorem shiftGraph_cliqueNum (k : ℕ) (hk : 2 ≤ k) : (shiftGraph (2 ^ k)).cliqueNum = 2 := by
  obtain ⟨u, v, huv⟩ := shiftGraph_exists_adj hk
  refine le_antisymm ?_ ?_
  · by_contra hcon
    obtain ⟨s, hs⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := shiftGraph (2 ^ k))
    exact (shiftGraph_cliqueFree (2 ^ k)).mono (by omega) s hs
  · have hclique : (shiftGraph (2 ^ k)).IsClique (({u, v} : Finset (ShiftVertex (2 ^ k))) : Set _) :=
      by simpa using (SimpleGraph.isClique_pair).mpr (fun _ => huv)
    have hcard : ({u, v} : Finset (ShiftVertex (2 ^ k))).card = 2 := Finset.card_pair huv.ne
    have hle : ({u, v} : Finset (ShiftVertex (2 ^ k))).card ≤ (shiftGraph (2 ^ k)).cliqueNum :=
      SimpleGraph.IsClique.card_le_cliqueNum (tc := hclique)
    rw [hcard] at hle
    exact hle

end Erdos627

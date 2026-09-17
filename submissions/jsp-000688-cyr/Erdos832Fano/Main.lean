import Mathlib

/-!
# Erdős Problem #832: the Fano plane witnesses failure for `r = k = 3`

Erdős conjectured (for `r ≥ 3` and `k` large) that every `r`-uniform hypergraph with chromatic
number `k` has at least `C((r−1)(k−1)+1, r)` edges (DISPROVED by Alon; NOT formalized here).  The
problem page records: "Erdős asked for `k` to be large in this conjecture since he knew it to be
false for `r = k = 3`, as witnessed by the Steiner triples with `7` vertices and `7` edges."  This
file verifies that witness: the Fano plane (the Steiner triple system on `7` points, with its `7`
lines as edges) is `3`-uniform, has chromatic number exactly `3`, and has `7 < C(5, 3) = 10` edges.

The hypergraph notions `FiniteHypergraph`, `IsUniform`, `ProperColoring`, `Colorable` and
`HasChromaticNumber` are copied verbatim from the Lean formalization of Alon's disproof in
plby/lean-proofs (`ErdosProblems/Erdos832.lean`, Apache 2.0), so that this statement is in the same
language as the existing formalization of the main result; that file does not state the Fano
witness.
-/

namespace Erdos832

open Finset

/-- A finite simple hypergraph.  Isolated vertices are retained in `V`, which
is important for stating the equality clause of Problem 832 exactly. -/
structure FiniteHypergraph where
  V : Type
  fintypeV : Fintype V
  decidableEqV : DecidableEq V
  edges : Finset (Finset V)

attribute [instance] FiniteHypergraph.fintypeV FiniteHypergraph.decidableEqV

namespace FiniteHypergraph

/-- Every edge has cardinality `r`. -/
def IsUniform (H : FiniteHypergraph) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- A coloring is proper when every edge contains two differently colored
vertices. -/
def ProperColoring (H : FiniteHypergraph) {κ : Type} (c : H.V → κ) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- `H` admits a proper coloring with colors `Fin k`. -/
def Colorable (H : FiniteHypergraph) (k : ℕ) : Prop :=
  ∃ c : H.V → Fin k, H.ProperColoring c

/-- The exact, minimum-color meaning of `χ(H) = k`, stated without making a
partial `Nat.find` definition for hypergraphs containing singleton edges. -/
def HasChromaticNumber (H : FiniteHypergraph) (k : ℕ) : Prop :=
  H.Colorable k ∧ ∀ j < k, ¬H.Colorable j

end FiniteHypergraph

/-- The Fano plane: the Steiner triple system on `7` points, with its `7` lines as edges. -/
def fano : FiniteHypergraph where
  V := Fin 7
  fintypeV := inferInstance
  decidableEqV := inferInstance
  edges := {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- Unfolding lemma: a proper colouring of the Fano plane is exactly a colouring of `Fin 7`
making every one of the seven concrete lines non-monochromatic. -/
theorem fano_properColoring_iff {κ : Type} [DecidableEq κ] (c : Fin 7 → κ) :
    fano.ProperColoring c ↔
      ∀ e ∈ ({{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}} :
          Finset (Finset (Fin 7))), ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y :=
  Iff.rfl

/-- Every `2`-colouring of `Fin 7` leaves one of the seven Fano lines monochromatic. -/
theorem fano_lines_monochromatic_of_two_colors (c : Fin 7 → Fin 2) :
    ¬ ∀ e ∈ ({{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}} :
        Finset (Finset (Fin 7))), ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  revert c
  decide +kernel

/-- The Fano plane is `3`-uniform with `7` edges on `7` vertices. -/
theorem fano_uniform_card : fano.IsUniform 3 ∧ fano.edges.card = 7 ∧ Fintype.card fano.V = 7 := by
  refine ⟨?_, ?_, ?_⟩
  · show ∀ e ∈ fano.edges, e.card = 3
    decide +kernel
  · decide
  · rfl

/-- The Fano plane is properly `3`-colourable. -/
theorem fano_colorable_three : fano.Colorable 3 := by
  exact ⟨![0, 0, 1, 1, 2, 2, 0], (fano_properColoring_iff _).mpr (by decide +kernel)⟩

/-- Every `2`-colouring of the Fano plane has a monochromatic line. -/
theorem fano_not_colorable_two : ¬ fano.Colorable 2 := by
  rintro ⟨c, hc⟩
  exact fano_lines_monochromatic_of_two_colors (fun x : Fin 7 => c x)
    ((fano_properColoring_iff (fun x : Fin 7 => c x)).mp hc)

/-- The Fano plane has chromatic number exactly `3`. -/
theorem fano_hasChromaticNumber_three : fano.HasChromaticNumber 3 := by
  refine ⟨fano_colorable_three, fun j hj => ?_⟩
  interval_cases j
  · rintro ⟨c, hc⟩
    obtain ⟨x, -, y, -, hxy⟩ :=
      (fano_properColoring_iff (fun x : Fin 7 => c x)).mp hc {0, 1, 2} (by decide)
    exact (c x).elim0
  · rintro ⟨c, hc⟩
    obtain ⟨x, -, y, -, hxy⟩ :=
      (fano_properColoring_iff (fun x : Fin 7 => c x)).mp hc {0, 1, 2} (by decide)
    exact hxy (Subsingleton.elim _ _)
  · exact fano_not_colorable_two

/-- **The conjectured bound fails for `r = k = 3`**: a `3`-uniform hypergraph of chromatic number
`3` with fewer than `C((3−1)(3−1)+1, 3) = 10` edges. -/
theorem erdos_832_false_three_three :
    ∃ H : FiniteHypergraph, H.IsUniform 3 ∧ H.HasChromaticNumber 3 ∧
      H.edges.card < ((3 - 1) * (3 - 1) + 1).choose 3 := by
  exact ⟨fano, fano_uniform_card.1, fano_hasChromaticNumber_three, by
    rw [fano_uniform_card.2.1]; decide⟩

end Erdos832

open Erdos832 in
/-- **Erdős #832, the page's witness, closed form**: the Fano plane (`7` vertices, `7` edges) is
`3`-uniform, has chromatic number `3`, and has fewer than `C((3−1)(3−1)+1, 3)` edges. -/
theorem erdos_832_fano_closed :
    Fintype.card fano.V = 7 ∧ fano.edges.card = 7 ∧ fano.IsUniform 3 ∧
      fano.HasChromaticNumber 3 ∧ fano.edges.card < ((3 - 1) * (3 - 1) + 1).choose 3 := by
  exact ⟨fano_uniform_card.2.2, fano_uniform_card.2.1, fano_uniform_card.1,
    fano_hasChromaticNumber_three, by rw [fano_uniform_card.2.1]; decide⟩

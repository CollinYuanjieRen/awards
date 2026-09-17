import Jsp490.Defs
import Jsp490.Family
import Jsp490.ErdosRado

/-!
# JSP-000490 / Erdős #603 — no cardinal suffices

Komjáth's question: for families `(A_i)` of countably infinite sets with `|A_i ∩ A_j| ≠ 2`
(`i ≠ j`), what is the smallest cardinal `C` such that `⋃ A_i` can always be coloured with at most
`C` colours with no `A_i` monochromatic?

Answer (GPT-5.4 Pro, prompted by Chojecki; recorded on erdosproblems.com/603): **no cardinal `C`
suffices.**  For every `C`, take `V` of cardinality `(2^λ)⁺`, `λ = C + ℵ₀`, and the family of edge
sets of countably infinite cliques of the complete graph on `V`.  Two such edge sets meet in the
edge set of a clique, never in exactly two edges; and by Erdős–Rado every colouring of the edges
with at most `C` colours has a monochromatic countably infinite clique.
-/

universe u

open Cardinal

namespace Erdos603

/-- The family of edge sets of countably infinite cliques of the complete graph on `V`. -/
def cliqueFamily (V : Type u) : Set (Set {e : Sym2 V // ¬ e.IsDiag}) :=
  {A | ∃ S : Set V, S.Countable ∧ S.Infinite ∧ A = cliqueEdges S}

/-- **Erdős #603.** For every cardinal `C` there is a family of countably infinite sets, pairwise
never meeting in exactly two elements and covering its ground set, such that every colouring of
the ground set with at most `C` colours makes some member monochromatic. -/
theorem erdos_603 (C : Cardinal.{u}) : ∃ (X : Type u) (𝒜 : Set (Set X)),
    (∀ A ∈ 𝒜, A.Countable ∧ A.Infinite) ∧
    (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → (A ∩ B).encard ≠ 2) ∧
    (∀ x : X, ∃ A ∈ 𝒜, x ∈ A) ∧
    ∀ (Y : Type u) (col : X → Y), #Y ≤ C → ∃ A ∈ 𝒜, ∀ x ∈ A, ∀ y ∈ A, col x = col y := by
  classical
  set lam : Cardinal.{u} := C + ℵ₀ with hlam_def
  have hlam : ℵ₀ ≤ lam := le_add_self
  have hC : C ≤ lam := le_self_add
  set κ : Cardinal.{u} := Order.succ ((2 : Cardinal.{u}) ^ lam) with hκ
  let V : Type u := Quotient.out κ
  have hV : κ ≤ #V := (Cardinal.mk_out κ).ge
  have : Infinite V := infinite_of_succ_le hlam hV
  refine ⟨{e : Sym2 V // ¬ e.IsDiag}, cliqueFamily V, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨S, hSc, hSi, rfl⟩
    exact ⟨cliqueEdges_countable hSc, cliqueEdges_infinite hSi⟩
  · rintro A ⟨S, -, -, rfl⟩ B ⟨T, -, -, rfl⟩ -
    rw [cliqueEdges_inter]
    exact cliqueEdges_encard_ne_two _
  · intro x
    obtain ⟨S, hSc, hSi, hx⟩ := exists_cliqueEdges_mem x
    exact ⟨cliqueEdges S, ⟨S, hSc, hSi, rfl⟩, hx⟩
  · intro Y col hY
    -- `Y` is nonempty because there is at least one edge
    obtain ⟨a, b, hab⟩ := exists_pair_ne V
    obtain ⟨x₀⟩ := nonempty_edges ⟨a, b, hab⟩
    obtain ⟨S, hSc, hSi, y₁, hS⟩ :=
      erdos_rado_countable hlam hV (hY.trans hC) (pairColour col (col x₀))
        (pairColour_symm col (col x₀))
    refine ⟨cliqueEdges S, ⟨S, hSc, hSi, rfl⟩, fun x hx y hy => ?_⟩
    rw [cliqueEdges_monochromatic col (col x₀) y₁ hS x hx,
      cliqueEdges_monochromatic col (col x₀) y₁ hS y hy]

/-- No cardinal `C` suffices. -/
theorem not_alwaysColourable (C : Cardinal.{u}) : ¬ AlwaysColourable C := by
  intro hC
  obtain ⟨X, 𝒜, h1, h2, h3, h4⟩ := erdos_603 C
  obtain ⟨Y, col, hY, hcol⟩ := hC X 𝒜 h1 h2
  have hcover : ∀ x : X, x ∈ ⋃₀ 𝒜 := fun x => by
    obtain ⟨A, hA, hx⟩ := h3 x
    exact Set.mem_sUnion.mpr ⟨A, hA, hx⟩
  obtain ⟨A, hA, hmono⟩ := h4 Y (fun x => col ⟨x, hcover x⟩) hY
  obtain ⟨x, y, hx, hy, hne⟩ := hcol A hA
  apply hne
  have h := hmono x hx y hy
  simpa only [Subtype.coe_eta] using h

/-- Hence there is no smallest sufficient cardinal: the set of sufficient cardinals is empty. -/
theorem no_least_cardinal : ¬ ∃ C : Cardinal.{u}, IsLeast {C | AlwaysColourable C} C := by
  rintro ⟨C, hC, -⟩
  exact not_alwaysColourable C hC

end Erdos603

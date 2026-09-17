import MerLeanExperiment.FixedCorePattern
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Logic.Equiv.Set

/-!
Split an ordinary graph along a vertex subset, retaining the two induced
graphs and an explicit Boolean table of cross edges.
-/

namespace CochromaticTwenty

variable {L R V : Type*}

/-- A graph on a sum type with prescribed left and right induced graphs and
an arbitrary Boolean table of cross edges. -/
def sumExtensionGraph (GLeft : SimpleGraph L) (GRight : SimpleGraph R)
    (cross : L → R → Bool) : SimpleGraph (L ⊕ R) where
  Adj
    | .inl u, .inl v => GLeft.Adj u v
    | .inr u, .inr v => GRight.Adj u v
    | .inl u, .inr v => cross u v = true
    | .inr v, .inl u => cross u v = true
  symm := by
    constructor
    intro u v h
    cases u <;> cases v
    · exact (GLeft.adj_comm _ _).mp h
    · exact h
    · exact h
    · exact (GRight.adj_comm _ _).mp h
  loopless := by
    constructor
    intro u h
    cases u with
    | inl u => exact GLeft.irrefl h
    | inr u => exact GRight.irrefl h

@[simp]
theorem sumExtensionGraph_left (GLeft : SimpleGraph L) (GRight : SimpleGraph R)
    (cross : L → R → Bool) (u v : L) :
    (sumExtensionGraph GLeft GRight cross).Adj (.inl u) (.inl v) ↔
      GLeft.Adj u v :=
  Iff.rfl

@[simp]
theorem sumExtensionGraph_right (GLeft : SimpleGraph L) (GRight : SimpleGraph R)
    (cross : L → R → Bool) (u v : R) :
    (sumExtensionGraph GLeft GRight cross).Adj (.inr u) (.inr v) ↔
      GRight.Adj u v :=
  Iff.rfl

@[simp]
theorem sumExtensionGraph_cross (GLeft : SimpleGraph L) (GRight : SimpleGraph R)
    (cross : L → R → Bool) (u : L) (v : R) :
    (sumExtensionGraph GLeft GRight cross).Adj (.inl u) (.inr v) ↔
      cross u v = true :=
  Iff.rfl

@[simp]
theorem sumExtensionGraph_cross' (GLeft : SimpleGraph L) (GRight : SimpleGraph R)
    (cross : L → R → Bool) (u : L) (v : R) :
    (sumExtensionGraph GLeft GRight cross).Adj (.inr v) (.inl u) ↔
      cross u v = true :=
  Iff.rfl

/-- Any graph is a sum extension of its two induced graphs after concrete
isomorphisms are chosen for the two sides of the split. -/
theorem exists_sumExtensionGraph_iso (G : SimpleGraph V) (S : Set V)
    (GLeft : SimpleGraph L) (GRight : SimpleGraph R)
    (eLeft : G.induce S ≃g GLeft)
    (eRight : G.induce (Sᶜ) ≃g GRight) :
    ∃ cross : L → R → Bool,
      Nonempty (G ≃g sumExtensionGraph GLeft GRight cross) := by
  classical
  let splitInv : L ⊕ R ≃ V :=
    (Equiv.sumCongr eLeft.symm.toEquiv eRight.symm.toEquiv).trans
      (Equiv.Set.sumCompl S)
  let cross : L → R → Bool := fun u v ↦
    decide (G.Adj (splitInv (.inl u)) (splitInv (.inr v)))
  refine ⟨cross, ⟨{ toEquiv := splitInv.symm, map_rel_iff' := ?_ }⟩⟩
  intro u v
  obtain ⟨u, rfl⟩ := splitInv.surjective u
  obtain ⟨v, rfl⟩ := splitInv.surjective v
  rw [splitInv.symm_apply_apply, splitInv.symm_apply_apply]
  cases u with
  | inl u =>
      cases v with
      | inl v =>
          change GLeft.Adj u v ↔
            G.Adj (eLeft.symm u).val (eLeft.symm v).val
          exact eLeft.symm.map_rel_iff.symm
      | inr v => simp [cross]
  | inr u =>
      cases v with
      | inl v => simp [cross, SimpleGraph.adj_comm]
      | inr v =>
          change GRight.Adj u v ↔
            G.Adj (eRight.symm u).val (eRight.symm v).val
          exact eRight.symm.map_rel_iff.symm

/-- A four-vertex clique is isomorphic to the complete graph on `Fin 4`. -/
noncomputable def cliqueFourIso {G : SimpleGraph V} {s : Finset V}
    (hcard : s.card = 4) (hclique : G.IsClique (s : Set V)) :
    G.induce (s : Set V) ≃g (⊤ : SimpleGraph (Fin 4)) where
  toEquiv := Fintype.equivFinOfCardEq (by simp [hcard])
  map_rel_iff' := by
    intro u v
    change
      Fintype.equivFinOfCardEq (by simp [hcard]) u ≠
          Fintype.equivFinOfCardEq (by simp [hcard]) v ↔
        G.Adj u v
    constructor
    · intro huv
      exact hclique u.property v.property
        (fun h ↦ huv (congrArg
          (Fintype.equivFinOfCardEq (by simpa using hcard)) (Subtype.ext h)))
    · intro huv hEq
      have huvEq : u = v :=
        (Fintype.equivFinOfCardEq (by simpa using hcard)).injective hEq
      subst v
      exact G.irrefl huv

/-- The cross table used by `fixedCorePattern`, extended by `false` outside
its sixty-four meaningful entries. -/
def fixedCoreAssignment (cross : Fin 4 → Fin 16 → Bool) : ℕ → Bool :=
  fun i ↦ if hi : i < 64 then
    let uv := (finProdFinEquiv : Fin 4 × Fin 16 ≃ Fin 64).symm ⟨i, hi⟩
    cross uv.1 uv.2
  else false

@[simp]
theorem fixedCoreAssignment_apply (cross : Fin 4 → Fin 16 → Bool)
    (u : Fin 4) (v : Fin 16) :
    fixedCoreAssignment cross (u.val * 16 + v.val) = cross u v := by
  have hlt : u.val * 16 + v.val < 64 := by omega
  unfold fixedCoreAssignment
  rw [dite_eq_left hlt]
  have heq : (⟨u.val * 16 + v.val, hlt⟩ : Fin 64) =
      (finProdFinEquiv : Fin 4 × Fin 16 ≃ Fin 64) (u, v) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  rw [heq, Equiv.symm_apply_apply]

/-- The sum extension with a complete left four-set and a coded right
sixteen-vertex core is exactly the existing fixed-core graph pattern. -/
def sumExtensionFixedCoreIso (core : ℕ) (cross : Fin 4 → Fin 16 → Bool) :
    sumExtensionGraph (⊤ : SimpleGraph (Fin 4)) (codeGraph 16 core) cross ≃g
      (fixedCorePattern core).graph (fixedCoreAssignment cross) where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by
    intro u v
    cases u with
    | inl u =>
        cases v with
        | inl v =>
            rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
            have hu : Fin.castAdd 16 u = u.castLE (by decide) := Fin.ext rfl
            have hv : Fin.castAdd 16 v = v.castLE (by decide) := Fin.ext rfl
            rw [hu, hv]
            simpa using (fixedCorePattern_left core (fixedCoreAssignment cross) u v)
        | inr v =>
            rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
            have hu : Fin.castAdd 16 u = u.castLE (by decide) := Fin.ext rfl
            rw [hu]
            simpa using (fixedCorePattern_cross core (fixedCoreAssignment cross) u v)
    | inr u =>
        cases v with
        | inl v =>
            rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left]
            have hv : Fin.castAdd 16 v = v.castLE (by decide) := Fin.ext rfl
            rw [hv]
            rw [SimpleGraph.adj_comm]
            simpa using (fixedCorePattern_cross core (fixedCoreAssignment cross) v u)
        | inr v =>
            rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right]
            simpa using (fixedCorePattern_right core (fixedCoreAssignment cross) u v)

/-- A twenty-vertex graph split into an actual four-clique and a coded
sixteen-vertex complement is one of the existing fixed-core pattern graphs. -/
theorem exists_fixedCorePattern_iso (G : SimpleGraph (Fin 20))
    (core : ℕ) {s : Finset (Fin 20)}
    (hcard : s.card = 4) (hclique : G.IsClique (s : Set (Fin 20)))
    (eRight : G.induce ((s : Set (Fin 20))ᶜ) ≃g codeGraph 16 core) :
    ∃ a : ℕ → Bool,
      Nonempty (G ≃g (fixedCorePattern core).graph a) := by
  let eLeft := cliqueFourIso hcard hclique
  obtain ⟨cross, ⟨e⟩⟩ := exists_sumExtensionGraph_iso
    G (s : Set (Fin 20)) (⊤ : SimpleGraph (Fin 4)) (codeGraph 16 core) eLeft eRight
  exact ⟨fixedCoreAssignment cross,
    ⟨e.trans (sumExtensionFixedCoreIso core cross)⟩⟩

end CochromaticTwenty

#print axioms CochromaticTwenty.exists_sumExtensionGraph_iso
#print axioms CochromaticTwenty.exists_fixedCorePattern_iso

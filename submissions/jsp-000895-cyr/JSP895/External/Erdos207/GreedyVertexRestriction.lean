/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import JSP895.External.Erdos207.MappedStoppedProcess
import JSP895.External.Erdos207.FiniteSpanCounting

/-! # Exact recovery from the current vertex subtype under explicit support -/

namespace Erdos207

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem map_restrictSupportedTriple (D : Finset V) (T : triplesSupportedOn D) :
    mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D)) (restrictSupportedTriple D T) = T.1 := by
  apply Subtype.ext
  exact subtype_map_of_mem (mem_triplesSupportedOn_iff.mp T.2)

omit [Fintype V] in
theorem exists_mapTriple_subtype [Finite V] (D : Finset V) (T : TripleOn V) (hT : T.1 ⊆ D) :
    ∃ U : TripleOn D, mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D)) U = T := by
  let := Fintype.ofFinite V
  exact ⟨restrictSupportedTriple D ⟨T, mem_triplesSupportedOn_iff.mpr hT⟩,
    map_restrictSupportedTriple D ⟨T, mem_triplesSupportedOn_iff.mpr hT⟩⟩

def restrictTripleSystemTo (D : Finset V) (C : TripleSystemOn V) : TripleSystemOn D :=
  univ.filter fun T ↦ mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D)) T ∈ C

omit [Fintype V] in
@[simp]
theorem mem_restrictTripleSystemTo (D : Finset V) (C : TripleSystemOn V) (T : TripleOn D) :
    T ∈ restrictTripleSystemTo D C ↔
      mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D)) T ∈ C :=
  by
    simp [restrictTripleSystemTo]

omit [Fintype V] in
theorem map_restrictTripleSystemTo [Finite V] (D : Finset V) (C : TripleSystemOn V)
    (hsupport : ∀ T ∈ C, T.1 ⊆ D) :
    mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ D))
        (restrictTripleSystemTo D C) =
      C :=
  by
    let := Fintype.ofFinite V
    ext T
    constructor
    · intro hT
      obtain ⟨U, hU, rfl⟩ := mem_map.mp hT
      exact (mem_restrictTripleSystemTo D C U).1 hU
    · intro hT
      obtain ⟨U, rfl⟩ := exists_mapTriple_subtype D T (hsupport T hT)
      exact (mem_mapTripleSystem_iff _ _ U).2 ((mem_restrictTripleSystemTo D C U).2 hT)

omit [Fintype V] in
@[simp]
theorem restrictTripleSystemTo_map [Finite V] (D : Finset V) (C : TripleSystemOn D) :
    restrictTripleSystemTo D
        (mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ D)) C) =
      C :=
  by
    let := Fintype.ofFinite V
    ext T
    simp only [mem_restrictTripleSystemTo, mem_mapTripleSystem_iff]

omit [Fintype V] in
theorem card_restrictTripleSystemTo [Finite V] (D : Finset V) (C : TripleSystemOn V)
    (hsupport : ∀ T ∈ C, T.1 ⊆ D) : (restrictTripleSystemTo D C).card = C.card := by
  let := Fintype.ofFinite V
  rw [← card_mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ D)),
    map_restrictTripleSystemTo D C hsupport]

def restrictForbiddenFamilyTo (D : Finset V) (F : ForbiddenFamilyOn V) : ForbiddenFamilyOn D :=
  univ.filter fun C ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ D)) C ∈ F

omit [Fintype V] in
@[simp]
theorem mem_restrictForbiddenFamilyTo (D : Finset V) (F : ForbiddenFamilyOn V)
    (C : TripleSystemOn D) :
    C ∈ restrictForbiddenFamilyTo D F ↔
      mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ D)) C ∈ F :=
  by
    simp [restrictForbiddenFamilyTo]

omit [Fintype V] in
theorem map_restrictForbiddenFamilyTo [Finite V] (D : Finset V) (F : ForbiddenFamilyOn V)
    (hsupport : ∀ C ∈ F, ∀ T ∈ C, T.1 ⊆ D) :
    mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ D))
        (restrictForbiddenFamilyTo D F) =
      F :=
  by
    let := Fintype.ofFinite V
    ext C
    constructor
    · intro hC
      obtain ⟨B, hB, rfl⟩ := mem_map.mp hC
      exact (mem_restrictForbiddenFamilyTo D F B).1 hB
    · intro hC
      have hdecode := map_restrictTripleSystemTo D C (hsupport C hC)
      rw [← hdecode]
      apply (mem_mapForbiddenFamily_iff _ _ _).2
      rw [mem_restrictForbiddenFamilyTo, hdecode]
      exact hC

omit [Fintype V] in
@[simp]
theorem restrictForbiddenFamilyTo_map [Finite V] (D : Finset V) (F : ForbiddenFamilyOn D) :
    restrictForbiddenFamilyTo D
        (mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ D)) F) =
      F :=
  by
    let := Fintype.ofFinite V
    ext C
    simp only [mem_restrictForbiddenFamilyTo, mem_mapForbiddenFamily_iff]

def restrictGreedyStateTo (D : Finset V) (S : GreedyStateOn V) : GreedyStateOn D where
  chosen := restrictTripleSystemTo D S.chosen
  available := restrictTripleSystemTo D S.available

omit [Fintype V] in
theorem map_restrictGreedyStateTo [Finite V] (D : Finset V) (S : GreedyStateOn V)
    (hchosen : ∀ T ∈ S.chosen, T.1 ⊆ D) (havailable : ∀ T ∈ S.available, T.1 ⊆ D) :
    mapGreedyState (Function.Embedding.subtype (fun v ↦ v ∈ D)) (restrictGreedyStateTo D S) =
      S :=
  by
    let := Fintype.ofFinite V
    cases S
    apply congrArg₂ GreedyStateOn.mk
    · exact map_restrictTripleSystemTo D _ hchosen
    · exact map_restrictTripleSystemTo D _ havailable

omit [Fintype V] in
@[simp]
theorem restrictGreedyStateTo_map [Finite V] (D : Finset V) (S : GreedyStateOn D) :
    restrictGreedyStateTo D (mapGreedyState (Function.Embedding.subtype (fun v ↦ v ∈ D)) S) =
      S :=
  by
    let := Fintype.ofFinite V
    cases S
    apply congrArg₂ GreedyStateOn.mk
    · exact restrictTripleSystemTo_map D _
    · exact restrictTripleSystemTo_map D _

omit [Fintype V] in
theorem mapTriple_subtype_supported (D : Finset V) (T : TripleOn D) :
    (mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D)) T).1 ⊆ D := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := mem_map.mp hv
  exact u.2

omit [Fintype V] in
theorem greedyInvariant_restrict_iff [Finite V] (D : Finset V) (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (hF : ∀ C ∈ F, ∀ T ∈ C, T.1 ⊆ D) (hchosen : ∀ T ∈ S.chosen, T.1 ⊆ D)
    (havailable : ∀ T ∈ S.available, T.1 ⊆ D) :
    GreedyInvariant (restrictForbiddenFamilyTo D F) (restrictGreedyStateTo D S) ↔
      GreedyInvariant F S :=
  by
    let := Fintype.ofFinite V
    rw [← greedyInvariant_map_iff (Function.Embedding.subtype (fun v ↦ v ∈ D)),
      map_restrictForbiddenFamilyTo D F hF, map_restrictGreedyStateTo D S hchosen havailable]

theorem timedStoppedGreedyProcessLaw_restrict
    (D : Finset V) (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (hF : ∀ C ∈ F, ∀ T ∈ C, T.1 ⊆ D)
    (hchosen : ∀ T ∈ S₀.chosen, T.1 ⊆ D) (havailable : ∀ T ∈ S₀.available, T.1 ⊆ D) :
    FiniteLaw.map (fun u : FiniteLaw.TimedState (GreedyStateOn D) n ↦
      (u.1, mapGreedyState (Function.Embedding.subtype (fun v ↦ v ∈ D)) u.2))
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel (restrictForbiddenFamilyTo D F))
        (fun i S ↦ active i (mapGreedyState (Function.Embedding.subtype (fun v ↦ v ∈ D)) S))
          (restrictGreedyStateTo D S₀)) =
        FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀ := by
  have h := timedStoppedGreedyProcessLaw_map (Function.Embedding.subtype (fun v ↦ v ∈ D)) n
    (restrictForbiddenFamilyTo D F)
    (fun i S ↦ active i (mapGreedyState (Function.Embedding.subtype (fun v ↦ v ∈ D)) S)) active
    (fun _ _ ↦ Iff.rfl) (restrictGreedyStateTo D S₀)
  simpa only [map_restrictForbiddenFamilyTo D F hF,
    map_restrictGreedyStateTo D S₀ hchosen havailable] using h

end

end Erdos207

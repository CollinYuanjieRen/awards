/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Original formal authors: Codex, GPT-5.6 Sol.
This file retains only the ordinary drawing definition, without face certificates.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Topology.UnitInterval


import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Subgraph

open scoped unitInterval

namespace PlanarListColoring

universe u

variable {V : Type u}

/-- A crossing-free topological drawing of a finite simple graph in the
Euclidean plane.  Edge interiors are simple, avoid all vertex images, and are
pairwise disjoint. -/
structure PlaneDrawing (G : SimpleGraph V) where
  vertexPoint : V → (Fin 2 → ℝ)
  vertexPoint_injective : Function.Injective vertexPoint
  edgePoint : G.edgeSet → I → (Fin 2 → ℝ)
  edge_continuous (e : G.edgeSet) : Continuous (edgePoint e)
  edge_zero (e : G.edgeSet) : edgePoint e 0 = vertexPoint e.1.out.1
  edge_one (e : G.edgeSet) : edgePoint e 1 = vertexPoint e.1.out.2
  edge_interior_injective (e : G.edgeSet) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s = edgePoint e t → s = t
  edge_interior_avoids_vertex (e : G.edgeSet) (v : V) {t : I} :
    t ≠ 0 → t ≠ 1 → edgePoint e t ≠ vertexPoint v
  edge_interiors_disjoint {e f : G.edgeSet} (hef : e ≠ f) {s t : I} :
    s ≠ 0 → s ≠ 1 → t ≠ 0 → t ≠ 1 → edgePoint e s ≠ edgePoint f t

end PlanarListColoring

namespace Erdos1018Topological

def expectedStatement : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε),
    ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) ^ ((1 : ℝ) + ε) ≤ (G.edgeSet.ncard : ℝ) →
          ∃ S : G.Subgraph,
            S.verts.ncard ≤ C ∧ ¬ Nonempty (PlanarListColoring.PlaneDrawing S.coe)

end Erdos1018Topological

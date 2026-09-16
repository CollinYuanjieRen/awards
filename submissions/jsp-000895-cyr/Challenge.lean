/- leanprover/lean4:v4.34.0-rc1  mathlib 1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d -/
/-
Comparator challenge for the JSP-000895 submission (Erdős Problem 1076, locally sparse
reading).  This module contains only statements proved by `sorry` and imports only Mathlib,
in the format of leanprover/comparator challenge modules.  The definitions `Erdos207.TripleOn`,
`Erdos207.TripleSystemOn`, `Erdos207.verticesOn` are copied verbatim from
plby/lean-proofs `src/latest/ErdosProblems/Erdos207/Basic.lean` (commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e); `FkFree`, `FamilyFree` and `exLe` are copied
verbatim from `JSP895/Bridge.lean`.  The solution module is `JSP895.Statement`.
-/

import Mathlib

namespace Erdos207

open Finset

abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

abbrev Triple (n : ℕ) := TripleOn (Fin n)

abbrev TripleSystem (n : ℕ) := TripleSystemOn (Fin n)

def verticesOn {V : Type*} [DecidableEq V] (C : TripleSystemOn V) : Finset V :=
  C.biUnion fun T ↦ T.1

end Erdos207

namespace Erdos1076Sparse

open Finset Filter Topology
open Erdos207 (verticesOn TripleOn TripleSystemOn TripleSystem)

def FkFree {V : Type*} [DecidableEq V] (k : ℕ) (G : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ G → C.card = k - 2 → k < (verticesOn C).card

def FamilyFree {V : Type*} [DecidableEq V] (k : ℕ) (G : TripleSystemOn V) : Prop :=
  ∀ j : ℕ, 4 ≤ j → j ≤ k → FkFree j G

noncomputable def exLe (k n : ℕ) : ℕ := by
  classical
  exact (Finset.univ : Finset (TripleSystem n)).sup fun G ↦
    if FamilyFree k G then G.card else 0

theorem erdos_1076_locally_sparse_of_le (k : ℕ) (hk : 4 ≤ k) :
    (∀ n : ℕ, 3 * exLe k n ≤ n.choose 2) ∧
      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe k n) ∧
      Tendsto (fun n : ℕ => (exLe k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) := by
  sorry

theorem erdos_1076_locally_sparse (k : ℕ) :
    (∀ n : ℕ, 3 * exLe (k + 4) n ≤ n.choose 2) ∧
      (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n - 3).choose 2 ≤ 3 * exLe (k + 4) n) ∧
      Tendsto (fun n : ℕ => (exLe (k + 4) n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6)) := by
  sorry

theorem exLe_isEquivalent (k : ℕ) (hk : 4 ≤ k) :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (exLe k n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 2 / 6) := by
  sorry

end Erdos1076Sparse

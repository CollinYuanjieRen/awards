/-
Comparator-style challenge module for JSP-000495 / Erdős Problem #609 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs609.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos609Challenge

/-- The colour class `i` of an edge colouring `c` of the complete graph on `V`. -/
def colourClass {V : Type*} {n : ℕ} (c : Sym2 V → Fin n) (i : Fin n) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => c s(u, v) = i)

/-- `G` contains an odd cycle. -/
def HasOddCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ Odd p.length

/-- `G` contains an odd cycle of length at most `m`. -/
def HasOddCycleLe {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ Odd p.length ∧ p.length ≤ m

/-- `f(n)`: the least `m` such that every `n`-colouring of `K_{2^n+1}` has a monochromatic odd
cycle of length at most `m`. -/
noncomputable def oddCycleThreshold (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n, ∃ i, HasOddCycleLe (colourClass c i) m}

theorem exists_colouring_no_oddCycle (n : ℕ) :
    ∃ c : Sym2 (Fin (2 ^ (n + 1))) → Fin (n + 1), ∀ i, ¬ HasOddCycle (colourClass c i) := by
  sorry

theorem exists_mono_oddCycle (n : ℕ) (c : Sym2 (Fin (2 ^ n + 1)) → Fin n) :
    ∃ i, HasOddCycle (colourClass c i) := by
  sorry

theorem oddCycleThreshold_le (n : ℕ) : oddCycleThreshold n ≤ 2 ^ n + 1 := by
  sorry

theorem oddCycleThreshold_mem (n : ℕ) :
    ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n, ∃ i, HasOddCycleLe (colourClass c i) (oddCycleThreshold n) := by
  sorry

end Erdos609Challenge

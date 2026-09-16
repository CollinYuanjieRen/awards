import Proof.Defs

/-!
# Erdős Problem 902: the tournaments attaining `f 1 = 3` and `f 2 = 7`

The cyclic tournament on `ℤ/3` (`i` beats `i + 1`) has the `1`-domination property, and the Paley
tournament on `ℤ/7` (`i` beats `j` iff `j - i` is a nonzero square mod `7`, i.e. `∈ {1, 2, 4}`) has
the `2`-domination property.  Both facts are finite and are checked by `decide`.
-/

namespace Erdos902

/-- The cyclic tournament on three vertices: `i` beats `i + 1`. -/
def cyc3 (i j : Fin 3) : Prop := j = i + 1

instance : DecidableRel cyc3 := fun i j => inferInstanceAs (Decidable (j = i + 1))

theorem isTournament_cyc3 : IsTournament cyc3 := by
  unfold IsTournament cyc3
  decide

theorem hasProperty_cyc3 : HasProperty cyc3 1 := by
  unfold HasProperty Dominates cyc3
  decide

/-- The Paley tournament on seven vertices: `i` beats `j` iff `j - i ∈ {1, 2, 4}`. -/
def paley7 (i j : Fin 7) : Prop := j - i = 1 ∨ j - i = 2 ∨ j - i = 4

instance : DecidableRel paley7 := fun i j =>
  inferInstanceAs (Decidable (j - i = 1 ∨ j - i = 2 ∨ j - i = 4))

theorem isTournament_paley7 : IsTournament paley7 := by
  unfold IsTournament paley7
  decide

theorem hasProperty_paley7 : HasProperty paley7 2 := by
  unfold HasProperty Dominates paley7
  decide +kernel

end Erdos902

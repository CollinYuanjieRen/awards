import MerLeanExperiment.GraphCode
import MerLeanExperiment.GraphClauses

namespace CochromaticTwenty

/-- Four initial clique vertices, a fixed sixteen-vertex core, and all sixty-four
free cross edges, numbered in lexicographic order from zero. -/
def fixedCoreEdge (core : ℕ) (u v : Fin 20) : EdgeRule :=
  let lo := min u.val v.val
  let hi := max u.val v.val
  if hi < 4 then .fixed true
  else if 4 ≤ lo then .fixed (core.testBit (edgeIndex (lo - 4) (hi - 4)))
  else .variable (lo * 16 + (hi - 4))

def fixedCorePattern (core : ℕ) : GraphPattern 20 where
  edge := fixedCoreEdge core
  symmetric := by intro u v; simp only [fixedCoreEdge, min_comm, max_comm]

def coreCode0 : ℕ := 1057056059467516563339269255695059211
def coreCode1 : ℕ := 896835175313774645522454073373704251

theorem fixedCorePattern_left (core : ℕ) (a : ℕ → Bool) (u v : Fin 4) :
    ((fixedCorePattern core).graph a).Adj
      (u.castLE (by decide)) (v.castLE (by decide)) ↔ u ≠ v := by
  simp [GraphPattern.graph, fixedCorePattern, fixedCoreEdge, EdgeRule.eval]

theorem fixedCorePattern_right (core : ℕ) (a : ℕ → Bool) (u v : Fin 16) :
    ((fixedCorePattern core).graph a).Adj (u.natAdd 4) (v.natAdd 4) ↔
      (codeGraph 16 core).Adj u v := by
  have hn : u.natAdd 4 = v.natAdd 4 ↔ u = v := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
    · rintro rfl; rfl
  have hi : edgeIndex (min u.val v.val) (max u.val v.val) = edgeIndex u.val v.val := by
    simp [edgeIndex]
  simp [GraphPattern.graph, fixedCorePattern, fixedCoreEdge, EdgeRule.eval,
    codeGraph, hi, hn]

theorem fixedCorePattern_cross (core : ℕ) (a : ℕ → Bool) (u : Fin 4) (v : Fin 16) :
    ((fixedCorePattern core).graph a).Adj (u.castLE (by decide)) (v.natAdd 4) ↔
      a (u.val * 16 + v.val) = true := by
  have hlt : u.val < 4 + v.val := by omega
  have hne : u.castLE (by decide : 4 ≤ 20) ≠ v.natAdd 4 := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_castLE, Fin.val_natAdd] at this; omega
  simp [GraphPattern.graph, fixedCorePattern, fixedCoreEdge, EdgeRule.eval,
    min_eq_left (Nat.le_of_lt hlt), max_eq_right (Nat.le_of_lt hlt), hne,
    show ¬ 4 + v.val < 4 by omega, show ¬ 4 ≤ u.val by omega]

end CochromaticTwenty

#print axioms CochromaticTwenty.fixedCorePattern_cross
#print axioms CochromaticTwenty.fixedCorePattern_right

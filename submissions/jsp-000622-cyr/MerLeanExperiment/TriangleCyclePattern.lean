import MerLeanExperiment.GraphClauses
import MerLeanExperiment.FiveVertexClassification

namespace CochromaticTwenty

def triangleCycleEdge (u v : Fin 8) : EdgeRule :=
  let lo := min u.val v.val
  let hi := max u.val v.val
  if hi < 3 then .fixed true
  else if 3 ≤ lo then .fixed (Nat.testBit 613 (edgeIndex (lo - 3) (hi - 3)))
  else .variable (lo * 5 + (hi - 3))

def triangleCyclePattern : GraphPattern 8 where
  edge := triangleCycleEdge
  symmetric := by intro u v; simp only [triangleCycleEdge, min_comm, max_comm]

theorem triangleCyclePattern_left (a : ℕ → Bool) (u v : Fin 3) :
    (triangleCyclePattern.graph a).Adj
      (u.castLE (by decide)) (v.castLE (by decide)) ↔ u ≠ v := by
  simp [GraphPattern.graph, triangleCyclePattern, triangleCycleEdge, EdgeRule.eval]

theorem triangleCyclePattern_right (a : ℕ → Bool) (u v : Fin 5) :
    (triangleCyclePattern.graph a).Adj (u.natAdd 3) (v.natAdd 3) ↔
      cycleFive.Adj u v := by
  have hn : u.natAdd 3 = v.natAdd 3 ↔ u = v := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
    · rintro rfl; rfl
  have hi : edgeIndex (min u.val v.val) (max u.val v.val) = edgeIndex u.val v.val := by
    simp [edgeIndex]
  simp [GraphPattern.graph, triangleCyclePattern, triangleCycleEdge, EdgeRule.eval,
    cycleFive, codeGraph, hi, hn]

theorem triangleCyclePattern_cross (a : ℕ → Bool) (u : Fin 3) (v : Fin 5) :
    (triangleCyclePattern.graph a).Adj (u.castLE (by decide)) (v.natAdd 3) ↔
      a (u.val * 5 + v.val) = true := by
  have hlt : u.val < 3 + v.val := by omega
  have hne : u.castLE (by decide : 3 ≤ 8) ≠ v.natAdd 3 := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_castLE, Fin.val_natAdd] at this; omega
  simp [GraphPattern.graph, triangleCyclePattern, triangleCycleEdge, EdgeRule.eval,
    min_eq_left (Nat.le_of_lt hlt), max_eq_right (Nat.le_of_lt hlt), hne,
    show ¬ 3 + v.val < 3 by omega, show ¬ 3 ≤ u.val by omega]

end CochromaticTwenty

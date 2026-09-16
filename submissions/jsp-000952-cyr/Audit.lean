import Proof

open Erdos1147 Filter

#print axioms Erdos1147.sqrtTwo_recSet_not_basis
#print axioms Erdos1147.not_erdos_1147
#print axioms Erdos1147.not_erdos_1147_le

example : ∀ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) →
    ¬ IsAsymptoticBasis2 (recSet (Real.sqrt 2) ε) :=
  Erdos1147.sqrtTwo_recSet_not_basis

example : ¬ ∀ α : ℝ, 0 < α → Irrational α → IsAsymptoticBasis2 (erdosSet α) :=
  Erdos1147.not_erdos_1147

example : ¬ ∀ α : ℝ, 0 < α → Irrational α →
    IsAsymptoticBasis2 (recSet α (fun n => 1 / Real.log n)) :=
  Erdos1147.not_erdos_1147_le

#print Erdos1147.nd
#print Erdos1147.IsAsymptoticBasis2
#print Erdos1147.recSet
#print Erdos1147.erdosSet

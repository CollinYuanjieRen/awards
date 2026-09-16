import Jsp936

open Randy1153

example (d : ℕ) (nodes : NodeFamily (d + 2)) :
    (∀ other : NodeFamily (d + 2),
      lebesgueOn nodes (-1) 1 ≤ lebesgueOn other (-1) 1) ↔
    ((∀ i j : Fin (d + 1), gapHeight nodes.sorted i = gapHeight nodes.sorted j) ∧
      lebesgueFunction nodes (-1) ≤ gapHeight nodes.sorted (0 : Fin (d + 1)) ∧
      lebesgueFunction nodes 1 ≤ gapHeight nodes.sorted (0 : Fin (d + 1))) :=
  Jsp936.minimizer_iff_equioscillating_and_controlled_tails d nodes

example (nodes : NodeFamily 1) :
    (∀ other : NodeFamily 1,
      lebesgueOn nodes (-1) 1 ≤ lebesgueOn other (-1) 1) ∧
    lebesgueOn nodes (-1) 1 = 1 :=
  Jsp936.singleton_nodes_optimal nodes

example (n : ℕ) : NodeFamily n ≃
    {x : Fin n → ℝ // Function.Injective x ∧ ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1} :=
  Jsp936.nodeFamilyEquivCoordinates n

#print axioms Jsp936.minimizer_iff_equioscillating_and_controlled_tails
#print axioms Jsp936.singleton_nodes_optimal
#print axioms Jsp936.nodeFamilyEquivCoordinates

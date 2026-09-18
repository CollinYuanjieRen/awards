import MerLeanExperiment.Target
import Mathlib.Tactic

/-!
# `z(9) ≥ 4`: an explicit nine-vertex graph with no three-cocoloring

Nine vertices and three color classes leave no slack: three homogeneous
classes of three vertices each would have to partition the whole graph, so the
counting arguments used for the other lower anchors do not apply and an
explicit witness is needed.

`G9` below is a four-regular graph on nine vertices with eighteen edges,
specified by its neighbour bitmasks `[30, 101, 99, 401, 393, 390, 390, 120,
120]`.  Its edge list is

```
0-1  0-2  0-3  0-4  1-2  1-5  1-6  2-5  2-6
3-4  3-7  3-8  4-7  4-8  5-7  5-8  6-7  6-8
```

equivalently the neighbourhoods

```
0 : 1 2 3 4     3 : 0 4 7 8     6 : 1 2 7 8
1 : 0 2 5 6     4 : 0 3 7 8     7 : 3 4 5 6
2 : 0 1 5 6     5 : 1 2 7 8     8 : 3 4 5 6
```

It has no homogeneous four-set and only twelve homogeneous triples, namely
`012 034 056 078 125 126 178 278 347 348 356 456`, and these twelve triples
leave no partition of the nine vertices.  `nine_check` verifies the stronger
statement that each of the `3^9 = 19683` colorings `Fin 9 → Fin 3` has a
monochromatic triple that is neither a clique nor an independent set; it is
checked by the Lean kernel with `decide +kernel` (about 100–120 s, and
`maxRecDepth` must be raised or the kernel reports a deep recursion).
-/

namespace CochromaticTwenty

/-- Neighbour bitmasks of the nine-vertex witness: bit `j` of `mask9 i` is set
exactly when `i` and `j` are adjacent. -/
def mask9 : Fin 9 → Nat := ![30, 101, 99, 401, 393, 390, 390, 120, 120]

/-- Boolean adjacency of the nine-vertex witness. -/
def adj9 (u v : Fin 9) : Bool := (mask9 u).testBit v.val

/-- The four-regular nine-vertex graph with edges
`0-1 0-2 0-3 0-4 1-2 1-5 1-6 2-5 2-6 3-4 3-7 3-8 4-7 4-8 5-7 5-8 6-7 6-8`,
the witness for `z(9) ≥ 4`. -/
def G9 : SimpleGraph (Fin 9) where
  Adj u v := adj9 u v
  symm.symm := by decide
  loopless.irrefl := by decide

/-- Adjacency in `G9` is decidable. -/
instance : DecidableRel G9.Adj := fun a b ↦ by
  change Decidable (adj9 a b = true); infer_instance

/-- `witnessed c` says that the coloring `c` has a monochromatic triple
`u < v < w` that is neither a clique nor an independent set of `G9`. -/
def witnessed (c : Fin 9 → Fin 3) : Bool :=
  (List.finRange 9).any fun u ↦ (List.finRange 9).any fun v ↦
    (List.finRange 9).any fun w ↦
      u.val < v.val && v.val < w.val && c u == c v && c v == c w &&
        (adj9 u v != adj9 u w || adj9 u v != adj9 v w)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- The kernel check: every one of the `3^9` colorings of the nine vertices by
three colors has a monochromatic non-homogeneous triple. -/
theorem nine_check : ∀ c : Fin 9 → Fin 3, witnessed c = true := by
  decide +kernel

/-- `z(9) ≥ 4`: the nine-vertex graph `G9` admits no cocoloring with three
homogeneous classes. -/
theorem fin9_not_hasCocoloring_three : ¬ HasCocoloring G9 3 := by
  rintro ⟨c, hc⟩
  have h := nine_check c
  simp only [witnessed, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨u, v, w, ⟨⟨⟨huv, hvw⟩, hcuv⟩, hcvw⟩, hmis⟩ := h
  have hne_uv : u ≠ v := fun hh ↦ by simp [hh] at huv
  have hne_vw : v ≠ w := fun hh ↦ by simp [hh] at hvw
  have hne_uw : u ≠ w := fun hh ↦ by omega
  have hu : u ∈ {z : Fin 9 | c z = c u} := rfl
  have hv : v ∈ {z : Fin 9 | c z = c u} := hcuv.symm
  have hw : w ∈ {z : Fin 9 | c z = c u} := by
    show c w = c u; rw [← hcvw, hcuv]
  rcases hc (c u) with hcl | hin
  · have a1 : adj9 u v = true := hcl hu hv hne_uv
    have a2 : adj9 u w = true := hcl hu hw hne_uw
    have a3 : adj9 v w = true := hcl hv hw hne_vw
    simp [a1, a2, a3] at hmis
  · have a1 : adj9 u v = false := (Bool.not_eq_true (adj9 u v)).mp (hin hu hv hne_uv)
    have a2 : adj9 u w = false := (Bool.not_eq_true (adj9 u w)).mp (hin hu hw hne_uw)
    have a3 : adj9 v w = false := (Bool.not_eq_true (adj9 v w)).mp (hin hv hw hne_vw)
    simp [a1, a2, a3] at hmis

end CochromaticTwenty

#print axioms CochromaticTwenty.nine_check
#print axioms CochromaticTwenty.fin9_not_hasCocoloring_three

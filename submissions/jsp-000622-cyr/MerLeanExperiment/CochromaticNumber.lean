import MerLeanExperiment.ModelAdapters
import Mathlib.Tactic

/-!
# The cochromatic number and the quantity `z(n)` of the table

The problem speaks of the *cochromatic number* of a graph — the least number
of classes in a partition of its vertices into cliques and independent sets —
and of `z(n)`, the maximum of that number over all graphs on `n` vertices.
This file defines both, so that the table statements read exactly like the
problem statement:

* `cochromaticNumber G` is the least `k` with `HasCocoloring G k`;
* `zmax n` is the maximum of `cochromaticNumber` over all graphs on `Fin n`;
* `CochromaticValue n k` is the two-sided statement "`z(n) = k`" spelled out
  as an upper bound for `k` and a witness against `k - 1`.

`cochromaticNumber_le_iff` and `zmax_eq_iff` connect these definitions with
the `HasCocoloring` vocabulary in which the bounds are proved.
-/

namespace CochromaticTwenty

open Classical

variable {V : Type*}

/-- Every finite graph has a cocoloring: give each vertex its own color, and
singletons are (vacuously) independent sets. -/
theorem exists_hasCocoloring [Fintype V] (G : SimpleGraph V) :
    ∃ k, HasCocoloring G k := by
  refine ⟨Fintype.card V, Fintype.equivFin V, fun i ↦ Or.inr ?_⟩
  have hsub : {v : V | Fintype.equivFin V v = i}.Subsingleton := by
    intro a ha b hb
    exact (Fintype.equivFin V).injective (ha.trans hb.symm)
  exact hsub.pairwise _

/-- The cochromatic number of a finite graph: the least number of homogeneous
classes — cliques or independent sets — needed to color its vertices. -/
noncomputable def cochromaticNumber [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (exists_hasCocoloring G)

/-- The cochromatic number is attained. -/
theorem hasCocoloring_cochromaticNumber [Fintype V] (G : SimpleGraph V) :
    HasCocoloring G (cochromaticNumber G) :=
  Nat.find_spec (exists_hasCocoloring G)

/-- The cochromatic number is the least cocoloring size. -/
theorem cochromaticNumber_le [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : HasCocoloring G k) : cochromaticNumber G ≤ k :=
  Nat.find_min' (exists_hasCocoloring G) h

/-- `cochromaticNumber G ≤ k` is exactly the statement that `G` has a
cocoloring with `k` classes. -/
theorem cochromaticNumber_le_iff [Fintype V] {G : SimpleGraph V} {k : ℕ} :
    cochromaticNumber G ≤ k ↔ HasCocoloring G k :=
  ⟨fun h ↦ (hasCocoloring_cochromaticNumber G).mono h, cochromaticNumber_le⟩

/-- `z(n)`: the maximum cochromatic number of a simple graph on `n` labelled
vertices. -/
noncomputable def zmax (n : ℕ) : ℕ :=
  Finset.univ.sup fun G : SimpleGraph (Fin n) ↦ cochromaticNumber G

/-- `z(n) ≤ k` is exactly the universal upper bound on `Fin n`. -/
theorem zmax_le_iff (n k : ℕ) :
    zmax n ≤ k ↔ ∀ G : SimpleGraph (Fin n), HasCocoloring G k := by
  simp [zmax, Finset.sup_le_iff, cochromaticNumber_le_iff]

/-- The statement "`z(n) = k`", spelled out as a universal upper bound
together with a graph that defeats `k - 1` classes. -/
def CochromaticValue (n k : ℕ) : Prop :=
  (∀ G : SimpleGraph (Fin n), HasCocoloring G k) ∧
    (∃ G : SimpleGraph (Fin n), ¬ HasCocoloring G (k - 1))

/-- For `k ≥ 1`, `z(n) = k` holds exactly when every graph on `n` vertices has
a `k`-cocoloring and some graph on `n` vertices has no `(k-1)`-cocoloring. -/
theorem zmax_eq_iff (n k : ℕ) (hk : 1 ≤ k) :
    zmax n = k ↔
      (∀ G : SimpleGraph (Fin n), HasCocoloring G k) ∧
        (∃ G : SimpleGraph (Fin n), ¬ HasCocoloring G (k - 1)) := by
  constructor
  · rintro rfl
    refine ⟨(zmax_le_iff n (zmax n)).mp le_rfl, ?_⟩
    by_contra hc
    have h : zmax n ≤ zmax n - 1 :=
      (zmax_le_iff n (zmax n - 1)).mpr fun G ↦ not_not.mp fun hG ↦ hc ⟨G, hG⟩
    omega
  · rintro ⟨hupper, G, hG⟩
    have h1 : zmax n ≤ k := (zmax_le_iff n k).mpr hupper
    have h2 : ¬ zmax n ≤ k - 1 := fun h ↦ hG ((zmax_le_iff n (k - 1)).mp h G)
    omega

/-- `zmax_eq_iff` phrased with `CochromaticValue`. -/
theorem zmax_eq_iff_cochromaticValue (n k : ℕ) (hk : 1 ≤ k) :
    zmax n = k ↔ CochromaticValue n k :=
  zmax_eq_iff n k hk

end CochromaticTwenty

#print axioms CochromaticTwenty.exists_hasCocoloring
#print axioms CochromaticTwenty.cochromaticNumber_le_iff
#print axioms CochromaticTwenty.zmax_le_iff
#print axioms CochromaticTwenty.zmax_eq_iff
#print axioms CochromaticTwenty.zmax_eq_iff_cochromaticValue

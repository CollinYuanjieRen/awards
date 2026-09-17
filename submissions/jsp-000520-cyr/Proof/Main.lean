import Proof.Defs

/-!
# Erdős problem #640, the case `k = 3`: `f(3) = 3`

Erdős and Hajnal ask, for `k ≥ 3`, whether there is some `f(k)` such that every graph of chromatic
number at least `f(k)` contains an odd cycle whose vertices span a subgraph of chromatic number at
least `k`.  The problem page calls the case `k = 3` trivial "since any non-bipartite graph contains
an odd cycle, and all odd cycles have chromatic number 3".  This package makes that precise, in the
language of `Erdos640.SpansOddCycle` and `Erdos640.spanThreshold`, as `f(3) = 3`:

* `Erdos640.three_le_chromaticNumber_induce_of_odd`: the subgraph spanned by the vertices of an odd
  closed walk has chromatic number at least `3` — the page's "all odd cycles have chromatic
  number 3", in the direction that is needed here;
* `Erdos640.exists_oddCycle_induce_three_le`: a graph of chromatic number at least `3` is not
  bipartite, hence contains an odd cycle, and that cycle spans a subgraph of chromatic number at
  least `3`;
* `Erdos640.spansOddCycle_three_three`: therefore `3` is a valid value of `f(3)`;
* `Erdos640.not_spansOddCycle_three_of_le_two`: no `f ≤ 2` is valid, since a single edge has
  chromatic number `2` and contains no odd closed walk at all;
* `Erdos640.spanThreshold_three`: consequently `spanThreshold 3 = 3`.

Not claimed here: the existence of `f(k)` for any `k ≥ 4` (the open question of Erdős problem #640)
and Steiner's reformulation with paths in place of odd cycles.
-/

open SimpleGraph

namespace Erdos640

/-- A graph on an arbitrary vertex type that is not `2`-colourable contains an odd cycle.

This is `Erdos640.exists_odd_cycle` of `Proof.OddCycle` with the finiteness hypotheses
of that module dropped: the argument uses `colorable_two_of_forall_even`, which needs no hypotheses
on the vertex type, and `isCycle_of_minimal_odd`, for which a classical decidable equality on the
vertex type suffices. -/
theorem exists_odd_cycle_of_not_colorable_two {V : Type*} (G : SimpleGraph V)
    (h : ¬ G.Colorable 2) : ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
  classical
  by_cases hall : ∀ (v : V) (p : G.Walk v v), Even p.length
  · exact absurd (colorable_two_of_forall_even G hall) h
  simp only [not_forall, Nat.not_even_iff_odd] at hall
  obtain ⟨v, p, hodd⟩ := hall
  have hne : Set.Nonempty {m : ℕ | ∃ (u : V) (r : G.Walk u u), Odd r.length ∧ r.length = m} :=
    ⟨p.length, v, p, hodd, rfl⟩
  obtain ⟨w, q, hqodd, hqlen⟩ := Nat.sInf_mem hne
  refine ⟨w, q, isCycle_of_minimal_odd G q hqodd ?_, hqodd⟩
  intro u r hr
  rw [hqlen]
  exact Nat.sInf_le ⟨u, r, hr, rfl⟩

/-- (T5) The subgraph spanned by the vertices of an odd closed walk has chromatic number at least
`3`.  Indeed the walk lifts to a closed walk of the same (odd) length in that induced subgraph, and
a graph carrying an odd closed walk is not bipartite. -/
theorem three_le_chromaticNumber_induce_of_odd {V : Type*} (G : SimpleGraph V) {v : V} (c : G.Walk v v) (hc : Odd c.length) : 3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber := by
  have hw : ∀ x ∈ c.support, x ∈ {x | x ∈ c.support} := fun _ hx => hx
  have hlen : (c.induce {x | x ∈ c.support} hw).length = c.length := by
    have hsupp := congrArg List.length (Walk.support_induce (s := {x | x ∈ c.support}) c hw)
    rw [List.length_attachWith, Walk.length_support, Walk.length_support] at hsupp
    omega
  exact Walk.three_le_chromaticNumber_of_odd_loop (c.induce {x | x ∈ c.support} hw)
    (by rw [hlen]; exact hc)

/-- (T3) Every graph of chromatic number at least `3` contains an odd cycle whose vertex set spans
a subgraph of chromatic number at least `3`.  A graph of chromatic number at least `3` is not
`2`-colourable, so it has an odd cycle, and `three_le_chromaticNumber_induce_of_odd` bounds the
chromatic number of the subgraph that cycle spans. -/
theorem exists_oddCycle_induce_three_le {V : Type*} (G : SimpleGraph V) (h : 3 ≤ G.chromaticNumber) : ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧ 3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber := by
  have hnc : ¬ G.Colorable 2 := by
    intro hcol
    have h32 : (3 : ℕ∞) ≤ 2 := le_trans h (chromaticNumber_le_iff_colorable.2 hcol)
    norm_num at h32
  obtain ⟨v, c, hcyc, hodd⟩ := exists_odd_cycle_of_not_colorable_two G hnc
  exact ⟨v, c, hcyc, hodd, three_le_chromaticNumber_induce_of_odd G c hodd⟩

/-- (T2) `3` is a valid value of `f(3)`: this is `exists_oddCycle_induce_three_le` phrased through
`SpansOddCycle`. -/
theorem spansOddCycle_three_three : SpansOddCycle 3 3 := by
  intro V G hG
  simpa using exists_oddCycle_induce_three_le G (by simpa using hG)

/-- (T4) No `f ≤ 2` is a valid value of `f(3)`: the complete graph on two vertices has chromatic
number `2`, so it satisfies the hypothesis, yet it has no odd closed walk — a graph with one would
have chromatic number at least `3`. -/
theorem not_spansOddCycle_three_of_le_two (f : ℕ) (hf : f ≤ 2) : ¬ SpansOddCycle 3 f := by
  intro hspan
  have hchrom : (⊤ : SimpleGraph (Fin 2)).chromaticNumber = 2 := by
    simp [chromaticNumber_top]
  have hle : (f : ℕ∞) ≤ (⊤ : SimpleGraph (Fin 2)).chromaticNumber := by
    rw [hchrom]
    exact_mod_cast hf
  obtain ⟨v, c, -, hodd, -⟩ := hspan (Fin 2) ⊤ hle
  have h3 := Walk.three_le_chromaticNumber_of_odd_loop c hodd
  rw [hchrom] at h3
  norm_num at h3

/-- (T1) `f(3) = 3`: the least valid value of `f(3)` is `3`.  `3` is valid by
`spansOddCycle_three_three`, and no smaller value is, by `not_spansOddCycle_three_of_le_two`. -/
theorem spanThreshold_three : spanThreshold 3 = 3 := by
  refine le_antisymm (Nat.sInf_le spansOddCycle_three_three) ?_
  refine le_csInf ⟨3, spansOddCycle_three_three⟩ ?_
  intro f hf
  by_contra hlt
  exact not_spansOddCycle_three_of_le_two f (by omega) hf

end Erdos640

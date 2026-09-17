import Proof.Construction

/-!
# Erdős Problem 609: the pigeonhole converse, and `f(n)` is attained

If the edges of `K_{2^n+1}` are `n`-coloured and no colour class contains an odd cycle, then every
colour class is `2`-colourable, and sending a vertex to the vector of its sides in the `n` classes
is injective into `Fin n → Fin 2`, a set of size `2 ^ n`; but there are `2 ^ n + 1` vertices.  So
some colour class does contain an odd cycle, the set defining `f(n)` is nonempty (an odd cycle of a
graph on `2 ^ n + 1` vertices has length at most `2 ^ n + 1`), and hence `f(n)` is attained and is
at most `2 ^ n + 1`.  Since cycles have length at least `3`, also `3 ≤ f(n)` for `n ≥ 1`.

Together with `exists_colouring_no_oddCycle` (the Erdős–Graham colouring of `K_{2^{n+1}}`), this
formalizes the two facts recorded on the problem page.

Not claimed here: the growth of `f(n)` — the question of Erdős problem #609 itself, Chung's question
whether `f(n) → ∞`, the Day–Johnson lower bound and the Girão–Hunter and Janzer–Yip upper bounds.
-/

open SimpleGraph

namespace Erdos609

/-- Every `n`-colouring of the edges of `K_{2^n+1}` has a monochromatic odd cycle. -/
theorem exists_mono_oddCycle (n : ℕ) (c : Sym2 (Fin (2 ^ n + 1)) → Fin n) :
    ∃ i, HasOddCycle (colourClass c i) := by
  by_contra hcon
  have hcol : ∀ i, (colourClass c i).Colorable 2 := by
    intro i
    by_contra hnc
    exact hcon ⟨i, hasOddCycle_of_not_colorable hnc⟩
  have hinj : Function.Injective
      (fun (v : Fin (2 ^ n + 1)) (i : Fin n) => (hcol i).some v) := by
    intro u v huv
    by_contra hne
    have hadj : (colourClass c (c s(u, v))).Adj u v := colourClass_adj.mpr ⟨hne, rfl⟩
    exact (hcol (c s(u, v))).some.valid hadj (congrFun huv (c s(u, v)))
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_fun] at hcard
  omega

/-- `2 ^ n + 1` belongs to the set defining `f(n)`: every `n`-colouring of `K_{2^n+1}` has a
monochromatic odd cycle, and a cycle in a graph on `2 ^ n + 1` vertices has length at most
`2 ^ n + 1`. -/
theorem two_pow_add_one_mem_threshold_set (n : ℕ) :
    (2 ^ n + 1) ∈ {m : ℕ | ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n,
      ∃ i, HasOddCycleLe (colourClass c i) m} := by
  intro c
  obtain ⟨i, v, p, hcyc, hodd⟩ := exists_mono_oddCycle n c
  refine ⟨i, v, p, hcyc, hodd, ?_⟩
  have hle := cycle_length_le_card hcyc
  simpa using hle

/-- The trivial bound: `f(n) ≤ 2 ^ n + 1`. -/
theorem oddCycleThreshold_le (n : ℕ) : oddCycleThreshold n ≤ 2 ^ n + 1 :=
  Nat.sInf_le (two_pow_add_one_mem_threshold_set n)

/-- `f(n)` is attained: every `n`-colouring of `K_{2^n+1}` has a monochromatic odd cycle of length
at most `f(n)`. -/
theorem oddCycleThreshold_mem (n : ℕ) : ∀ c : Sym2 (Fin (2 ^ n + 1)) → Fin n,
    ∃ i, HasOddCycleLe (colourClass c i) (oddCycleThreshold n) :=
  Nat.sInf_mem ⟨2 ^ n + 1, two_pow_add_one_mem_threshold_set n⟩

/-- Odd cycles have length at least `3`, so `3 ≤ f(n)` as soon as there is at least one colour. -/
theorem three_le_oddCycleThreshold (n : ℕ) (hn : 1 ≤ n) : 3 ≤ oddCycleThreshold n := by
  obtain ⟨i, v, p, hcyc, -, hlen⟩ := oddCycleThreshold_mem n (fun _ => ⟨0, hn⟩)
  exact le_trans hcyc.three_le_length hlen

end Erdos609

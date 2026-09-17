import Proof.OddCycle

/-!
# Erdős problem #640: valid thresholds `f(k)` and the threshold function

Erdős and Hajnal ask, for `k ≥ 3`, whether there is some `f(k)` such that every graph of chromatic
number at least `f(k)` contains an odd cycle whose vertices span a subgraph of chromatic number at
least `k`.  This module fixes the two notions used to state that question formally:

* `Erdos640.SpansOddCycle k f` says that `f` is a *valid value* of `f(k)`;
* `Erdos640.spanThreshold k` is the least valid value of `f(k)`.

The existence question itself is what is open for `k ≥ 4`; the companion module
`Proof.Main` settles the case `k = 3`, where the answer is `f(3) = 3`.
-/

namespace Erdos640

/-- `SpansOddCycle k f` says that `f` is a valid value of `f(k)` in the sense of Erdős problem
#640: for every graph `G`, on any vertex type, whose chromatic number is at least `f`, there is an
odd cycle of `G` whose vertex set spans an induced subgraph of chromatic number at least `k`. -/
def SpansOddCycle (k f : ℕ) : Prop := ∀ (V : Type) (G : SimpleGraph V), (f : ℕ∞) ≤ G.chromaticNumber → ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧ (k : ℕ∞) ≤ (G.induce {x | x ∈ c.support}).chromaticNumber

/-- `spanThreshold k` is the least valid value of `f(k)`, i.e. the infimum in `ℕ` of the set of
valid values.  As always for `sInf` on `ℕ`, this is `0` when no value is valid, so a statement
`spanThreshold k = f` with `f ≠ 0` carries the existence claim as well. -/
noncomputable def spanThreshold (k : ℕ) : ℕ := sInf {f : ℕ | SpansOddCycle k f}

/-- Validity is upward closed: a larger threshold constrains fewer graphs, so if `f` is a valid
value of `f(k)` then so is every `f' ≥ f`. -/
theorem spansOddCycle_of_le (k : ℕ) {f f' : ℕ} (h : f ≤ f') (hf : SpansOddCycle k f) :
    SpansOddCycle k f' := by
  intro V G hG
  exact hf V G (le_trans (Nat.cast_le.2 h) hG)

end Erdos640

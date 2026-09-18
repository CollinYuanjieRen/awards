import CameronErdos.Part2.Cor13
import CameronErdos.Assembly

/-!
# The Cameron–Erdős conjecture (JSP-000616 / Erdős #748)

This file is the top of Green's proof of the Cameron–Erdős conjecture: the three-way split
`CameronErdos.cameronErdos_of_exceptional_bound` (`Thm_Assembly`, `CameronErdos/Assembly.lean`)
applied to the exceptional-class bound `CameronErdos.eventually_exceptional_le`
(`Thm_Cor13`, `CameronErdos/Part2/Cor13.lean`) yields the frozen root statement
`CameronErdos.CameronErdosStatement` of `CameronErdos/Statement.lean`:

`∃ C > 0, ∀ n, f(n)^2 ≤ C · 2^n`, i.e. `f(n) = O(2^{n/2})`,

where `f(n) = CameronErdos.sumFreeCount n` is the number of sum-free subsets of `[1, n]`.
-/

namespace CameronErdos

/-- **The Cameron–Erdős conjecture** (Cameron–Erdős 1990; Green 2004, Sapozhenko 2003):
the number of sum-free subsets of `{1, …, n}` is `O(2^{n/2})`. -/
theorem cameronErdos : CameronErdosStatement :=
  cameronErdos_of_exceptional_bound eventually_exceptional_le

end CameronErdos

/-! ## Axiom audit -/

#print axioms CameronErdos.cameronErdos

# JSP-001010 (Erdős #1205): the minimum coverage multiplicity of one residue class per modulus — `F(x) ∼ log x`

Catalog entry: [JSP-001010](../../problems/catalog-1001-1022.md#JSP-001010). Problem page:
<https://www.erdosproblems.com/1205>.

## The question and its complete answer

Erdős [Er80, p. 108]: let `F(x)` be maximal such that there exists, for all `n ≤ x`, a congruence class
`a_n (mod n)` such that every `m ≤ x` satisfies at least `F(x)` of these congruences. Estimate `F(x)`.

Resolution recorded on the problem page: `F(x) ∼ log x`; precisely
`log x − O(√(log x · log log x)) ≤ F(x) ≤ log x + O(1)`. Everything below is proved in Lean 4 / Mathlib with only
the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | `F(x) ≤ log x + 2` for every `x ≥ 1` (indeed `F(x) ≤ H_x + 1`) | `Erdos1205.F_le_log_add_two`, `F_le_harmonic_add_one` |
| (ii) | `log x − 6 √(log x · log log x) ≤ F(x)` for all large `x` | `Erdos1205.F_ge_log_sub_six_sqrt`, `F_ge_log_sub_sqrt` |
| (iii) | `F(x) / log x → 1` | `Erdos1205.F_div_log_tendsto_one` |
| (iv) | `F(x) − log x = O(√(log x · log log x))` | `Erdos1205.F_sub_log_isBigO` |

Faces (i)–(iii) are bundled in `Erdos1205.erdos_1205` in [Jsp1010/Main.lean](Jsp1010/Main.lean). The definitions
([Jsp1010/Defs.lean](Jsp1010/Defs.lean)) are the literal ones: a choice of classes is any `a : ℕ → ℕ` (only `a n mod n`
matters), `coverCount a x m = #{n ∈ [1, x] : m ≡ a n (mod n)}`, and `F x` is the supremum (a maximum) of the `k` such
that some choice makes every `m ∈ [1, x]` satisfy at least `k` congruences. The frozen statement is restated once
more, with `sorry`, in [Target.lean](Target.lean), which nothing imports (its definitions and statement are
byte-identical to the proved ones).

## Proof structure

* [Upper.lean](Jsp1010/Upper.lean): `F x` is a maximum; double counting
  `Σ_m coverCount a x m = Σ_n #{m ∈ [1,x] : m ≡ a_n (mod n)} ≤ Σ_n (x/n + 1)`, so `x·F(x) ≤ x·H_x + x` and
  `F(x) ≤ H_x + 1 ≤ log x + 2` (Mathlib's `harmonic_le_one_add_log`).
* [Chernoff.lean](Jsp1010/Chernoff.lean): the finite probability space of all choices for the moduli `1, …, N`
  (`N = ⌊x/2⌋`). The moment generating function of the number of congruences satisfied by a fixed `m` factorises
  (`Finset.prod_univ_sum`) as `Π_n (1 − (1 − e^{−θ})/n) ≤ exp(−(1 − e^{−θ}) H_N)`; Markov's inequality at
  `θ = t/(2H_N)` gives: the number of choices for which `m` is covered fewer than `H_N − t` times is at most
  `N! · exp(−t²/(4H_N))` (for `0 ≤ t ≤ 2H_N`); averaging over `m` yields a choice with at most
  `x · exp(−t²/(4H_N))` badly covered `m`.
* [Greedy.lean](Jsp1010/Greedy.lean): if `|B| · L ≤ |(N, x]|`, an injection `B × [L] ↪ (N, x]` assigns `L` private
  large moduli to every badly covered `m`, whose classes are then set to contain `m`; the split of `[1, x]` into
  `[1, N] ∪ (N, x]` and the transfer between the `Fin N`-indexed choice and the function on moduli.
* [Asymptotics.lean](Jsp1010/Asymptotics.lean): with `t = √(8 H_N log log x)`: `exp(−t²/(4H_N)) = (log x)⁻²`,
  `t ≤ 2H_N`, the repair capacity `x (log x)⁻² (H_N + 1) ≤ x − N`, and
  `log x − 6√(log x log log x) ≤ H_N − t − 1`, all for large `x`; the derivations of `F/log x → 1` and the `O(·)` form.
* [Main.lean](Jsp1010/Main.lean): assembly — the combined choice (random classes below `N`, repaired classes above)
  covers every `m ∈ [1, x]` at least `⌊H_N − t⌋` times.

The page's argument is followed exactly; the only quantitative choices made here are the constants (`t = √(8H_N log log x)`,
so that the failure probability is `(log x)⁻²`, and the final constant `6`), and the elementary Chernoff bound is
proved from scratch on the finite space (it uses `|e^u − 1 − u| ≤ u²` for `|u| ≤ 1` instead of the sharper `u²/2`, at the
cost only of the constant).

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside the challenge file `Target.lean`.

## Reproduce

```bash
cd submissions/jsp-001010-cyr
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
`Audit.lean` prints the axioms of the eight audited theorems (expected output in `verification.txt`).

## Attribution and submission status

The problem is due to Erdős [Er80]; the resolution is the argument recorded on erdosproblems.com/1205 (T. F. Bloom,
crediting the comments on Problem #689; the catalog lists [Er80] as the source). The Lean formalization was written
from scratch by Collin Yuanjie Ren (@CollinYuanjieRen) with Claude Code assistance (design and review by Claude Fable 5.1,
Lean implementation by Claude Opus subagents); no Lean code from any other project was consulted or reused. An earlier,
independent Lean proof of the same resolution exists publicly (plby/lean-proofs, module `Erdos1205`); no
first-formalization priority or entitlement to an award is claimed. An independent adversarial audit (statement
alignment against the problem text, axiom census, numerical checks of the constants) was performed before submission;
no organizer-supplied or third-party authoritative Lean statement of this problem exists (erdosproblems.com:
"Formalised statement: No"; formal-conjectures has no `ErdosProblems/1205.lean`), so no official comparator run is
claimed. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the
repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).

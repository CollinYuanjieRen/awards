# Erdős problem 973 — exterior power sums

This project proves the negative answer to [Erdős problem 973](https://www.erdosproblems.com/973), catalog entry JSP-000807. There is no real constant C > 1 such that, for every n ≥ 2, one can choose complex numbers z₁,…,zₙ with z₁ = 1 and |zᵢ| ≥ 1 while every power sum with 2 ≤ k ≤ n+1 has absolute value strictly less than C^(−n).

The proof establishes the stronger uniform statement: for each λ > 0, every sufficiently large n and every n-tuple outside the open unit disk have some power sum in that exponent interval with absolute value strictly greater than exp(−λn). The result covers arbitrary n and the full exponent interval; it has no added unproved mathematical assumptions.

## Theorems

All final roots are in [MerLeanExperiment/Main.lean](MerLeanExperiment/Main.lean):

- `Erdos973.uniformExteriorLowerBound`: the full eventual lower bound.
- `Erdos973.erdos973`: the negative answer to the original question.
- `Erdos973.formalConjectures973Expanded`: the complete proof in the source-exact expanded Formal Conjectures statement shape.

The original and stronger target definitions are in [Statement.lean](MerLeanExperiment/Statement.lean). [FormalConjectures973Frozen.lean](MerLeanExperiment/FormalConjectures973Frozen.lean) imports only Mathlib and fixes the external original statement independently of the candidate proof. The statement is taken from [Formal Conjectures at d5ba143cc2fafd48cc6d5b6320a3aab287c38df7](https://github.com/google-deepmind/formal-conjectures/blob/d5ba143cc2fafd48cc6d5b6320a3aab287c38df7/FormalConjectures/ErdosProblems/973.lean). Its explicit `answer(False)` is expanded to `False` using the elaborator at that same commit; all mathematical quantifiers and inequalities are preserved.

This is a source-exact external-statement bridge compiled with this project's pinned toolchain. The reference repository itself uses Lean 4.33.1; this package does not claim a native build of that repository or a run of an organizer-supplied comparator program.

## Build

The project pins Lean `leanprover/lean4:v4.34.0-rc1` and Mathlib commit `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. From this directory, with elan installed:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

See [verification.txt](verification.txt) for the release checks. The proof sources passed a forced rebuild, six root axiom checks, independent scope and dependency reviews by two separate GPT-5.6-Sol agents, and the live typed Lean runtime audit. Both reviewers were separate from every implementation agent.

No MerLean Gold grade is claimed. Its unmodified metadata checker requires an Astra original-scope reviewer; the project instruction required Sol. The full checker reported only that model-name conflict, while all other schema, source, scope and live kernel checks passed. Reviewer provenance was not changed to bypass the restriction.

## Mathematical proof and attribution

The mathematical argument is due to Yanping Luo, Ruiyi Yang and Keheng Zhu, [*Exterior power sums*, arXiv:2607.22017v1](https://arxiv.org/abs/2607.22017v1), Theorem 1.1. The formalization proves the truncated exponential coefficient identities and bounds, normalized first-sum scale, uniform exterior-disk estimates, and Cauchy-transform contradiction. The compactness step uses probability measures on the closed unit disk, followed by local uniform convergence, the analytic identity theorem, and decay at infinity.

The Lean implementation was produced for GitHub account [CollinYuanjieRen](https://github.com/CollinYuanjieRen) with GPT-5.6-Sol assistance. Independent AI review is distinct from mathematical authorship and does not claim human verification.

The paper's [prior partial Lean companion](https://github.com/miracleqihe/Erdos-973_solution_check-by-Lean/tree/f0f27f85cb9865c706a77692cdae260e77d7aa14) is acknowledged. At the pinned commit its README expressly disclaims a proof of the full theorem. No code from that companion was copied into this development.

The external statement and Mathlib retain their original attribution. See [NOTICE](NOTICE) and the Apache-2.0 [LICENSE](LICENSE). This project makes no claim of organizer acceptance, priority or award eligibility.

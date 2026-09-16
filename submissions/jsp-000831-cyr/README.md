# Kesten's interval characterization — JSP-000831 / Erdős 998

This project formalizes the full interval-length characterization. The root theorem is
`Kesten.bounded_remainder_iff` in `MerLeanExperiment/Kesten.lean`.

For an irrational real number `α` and `0 ≤ u < v ≤ 1`, let `D n` count the integers
`m = 1, …, n` with `u ≤ Int.fract (m * α) < v`, minus `n * (v - u)`. The proved statement is

```text
D n is eventually uniformly bounded in absolute value
  ↔ ∃ k l : ℤ, v - u = k * α + l.
```

The counting definition uses a half-open interval and permits `u = 0`, `v = 1`,
negative irrational `α`, and either sign of the integer coefficients. The
classification concerns the interval length. It does not require each endpoint
separately to be an integer multiple of `α` modulo one.

The proof route follows Grepstad and Lev, *Sets of bounded discrepancy for
multi-dimensional irrational rotation*, [arXiv:1404.0165](https://arxiv.org/abs/1404.0165),
§2: extend a bound along a dense orbit to almost every starting point; construct a
measurable transfer by a liminf; exponentiate and use a nonzero Fourier coefficient
to prove necessity. For sufficiency, an exact fractional-part identity reduces the
counting discrepancy to the difference of two shifted finite sums.

The historical theorem is due to Hecke, Ostrowski, and Kesten. The visit-count
conventions and the fractional-part normalization helper were adapted from
[plby/lean-proofs, Erdos998.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos998.lean)
(Apache-2.0; formal-author notices credit Codex and GPT-5.6 Sol). That source proves
a counterexample to the stronger separate-endpoint formulation; it does not prove
the full length characterization targeted here. This work makes no claim of an
original mathematical discovery or official prize acceptance.

The development is pinned to Lean `v4.34.0-rc1` and Mathlib
`1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.

To reproduce from this directory with Lean's `elan`/`lake` installed:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env leanchecker --fresh --verbose MerLeanExperiment.Kesten
```

`Audit.lean` checks the frozen theorem type and a second version with the original
visit-count expression fully expanded. The root axiom closure is exactly
`propext`, `Classical.choice`, and `Quot.sound`. There are no project axioms,
`sorry`, `admit`, or extra hypotheses. The root has three real data parameters and
exactly the four original hypotheses: irrationality, `0 ≤ u`, `u < v`, and `v ≤ 1`.
The fresh-environment replay checks all constants imported by the root. Bundled
`leanchecker` uses the same Lean kernel implementation; it is not a separate
implementation such as nanoda. Actual check outcomes and source hashes are recorded
in `verification.json` and the accompanying logs.

No authoritative supplied Lean challenge for this full criterion was located in
the bounded source search: the cached Erdős problem page says “Formalised statement?
No”, and the complete formal-conjectures tree at
`40e7c98697de6f66b8cbdbf641749ab39ed9c152` has no problem-998 file. The independent
plby counterexample is a different statement. The official-target comparator gate
is therefore recorded as `NOT-AVAILABLE`, followed by independently reviewed
source alignment, exact typed audits, and kernel/axiom checks. This is not an
official-comparator PASS or official prize acceptance.

The published prize rules snapshot requires axiom audits but gives no explicit
allowlist for the three foundational axioms above. Their acceptance by the prize
is not asserted. Historical mathematical credit and adapted source notices are
preserved in `NOTICE`; adapted Apache-2.0 material is covered by `LICENSE-APACHE`.

The MerLean executable grade audit did not award GOLD. Its current recorder rejects
the standard `Real` data parameters as unaudited structures and cannot encode a
settled theorem with the original proposition hypotheses under its scope policy.
These independently diagnosed recorder failures are retained in
`checks/merlean-grade-audit.log`; no runtime policy or theorem was changed to bypass
them. The successful Lean checks above and the failed grade audit are separate
results.

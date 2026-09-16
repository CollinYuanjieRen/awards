# Free-node maximin characterization — JSP-000937

This project proves the complete characterization asked in the
[JSP-000937 catalog entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#jsp-000937).
For any positive number of distinct ordered nodes in `[-1,1]`, form the Lagrange
fundamental polynomials and their Lebesgue function `L`. Include both exterior
gaps, from `-1` to the first node and from the last node to `1`. The objective is
the minimum, over these closed gaps and all internal gaps, of the maximum of `L`
on that gap.

For at least two nodes, a configuration maximizes this objective if and only if
all its **internal** gap maxima have one common value `H`, and both `L(-1)` and
`L(1)` are at least `H`. A maximizing configuration exists for every positive
number of nodes. Every singleton and every two-node configuration has objective
value `1` and is maximizing. The two exterior maxima need not equal `H`.


Publication overlap: during final publication checks, [issue #129](https://github.com/TheJustinSunPrize/awards/issues/129) disclosed an independently checked all-gap classification in [randyxian08/jsp000936-lean at 0016bb8](https://github.com/randyxian08/jsp000936-lean/tree/0016bb877b3fca8ef7a36a02a6f088e6f807e58a). Its `JSPFreeNodes.jsp_000937_classification` overlaps this package's characterization scope. Although that issue nominates JSP-000936 and excludes the separate logarithmic bound, those boundaries do not remove the classification overlap. This package preserves our completed proof and verification; no duplicate official nomination or priority claim is made. The external proof's source and published check logs were inspected; we have not independently replayed its full dependency cone.

The four public roots are:

- `Jsp937.maximizer_iff_equioscillating_and_large_tails`
- `Jsp937.exists_upsilon_maximizer`
- `Jsp937.singleton_upsilon_and_maximal`
- `Jsp937.pair_upsilon_and_maximal`

`OrderedNodes` contains only real coordinates, their distinctness, membership in
`[-1,1]`, and increasing order. There is no assumed canonical comparison theorem,
existence theorem, or optimality premise. `IntendedModel.lean` proves an equivalence
with raw coordinate functions and identifies the objective with the explicit
finite-product Lagrange formula, endpoint augmentation, closed-gap suprema, and
finite minimum. `Audit.lean` checks the fixed root types and expands both sides of
the characterization into these formulas.

The polynomial comparison and equioscillation theorem follows de Boor and Pinkus,
*Proof of the conjectures of Bernstein and Erdős concerning the optimal nodes for
polynomial interpolation*, J. Approx. Theory 24 (1978), 289–303,
[primary paper](https://pinkus.net.technion.ac.il/files/2021/02/conj.pdf), §§1–3.
The 23 `Randy1153` modules are byte-identical to the MIT-licensed development of
[randyxian08/jsp000958-lean](https://github.com/randyxian08/jsp000958-lean/tree/e1df51e950876056d8951f4a93fa7fef6863b422).
Their source hashes are in `vendor-manifest.json`. This submission adds the
free-node maximin bridge, actual exterior-gap analysis, affine normalization,
attainment construction, small cases, and original-formula audits. Four general
affine/tail helpers are credited to the concurrent JSP-000936 campaign in `NOTICE`.

The exterior-gap convention follows Erdős, *Some remarks on polynomials*,
Bull. Amer. Math. Soc. 53 (1947), 1169–1176,
[primary paper](https://www.renyi.hu/~p_erdos/1947-08.pdf), pp.1171–1172.
The separate logarithmic upper-bound question on the
[Erdős problem 1130 page](https://www.erdosproblems.com/1130) is outside the
catalog characterization proved here. This is not a claim to solve every question
on that page or to discover a new mathematical theorem.

The project is pinned to Lean `v4.27.0`, commit
`db93fe1608548721853390a10cd40580fe7d22ae`, and Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`.
From this directory, with `elan` and `lake` installed:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

All four roots depend exactly on `propext`, `Classical.choice`, and `Quot.sound`.
The completed mathematical proof cone contains no project axioms, `sorry`,
`admit`, native decision certificates, or additional hypotheses.

Lean 4.27 does not bundle the later `leanchecker` executable. The included
`checks/ReplayCheck.lean` adapts the Apache-2.0 stock Lean replay scheduler to a
fresh kernel environment at trust level zero. Every safe non-partial declaration
is submitted to the checked kernel entry point; generated constructors,
recursors, and quotient primitives are compared against the imported records.
Unsafe and partial tooling declarations are skipped, and every eligible
declaration and each requested root must be present after replay. It uses the
same Lean kernel implementation, not a separate implementation such as nanoda.
The harness is a standalone verifier and is not imported by the mathematical proof.
To compile and run it:

```sh
lake env lean -c /tmp/jsp937-replay.c checks/ReplayCheck.lean
lake env leanc -O3 -o /tmp/jsp937-replay /tmp/jsp937-replay.c
lake env /tmp/jsp937-replay Jsp937 \
  Jsp937.maximizer_iff_equioscillating_and_large_tails \
  Jsp937.exists_upsilon_maximizer \
  Jsp937.singleton_upsilon_and_maximal \
  Jsp937.pair_upsilon_and_maximal \
  Jsp937.orderedNodesEquivCoordinates Jsp937.upsilon_eq_raw
```

Actual verification results and source hashes are recorded in `verification.json`.
No authoritative supplied Lean challenge for this full catalog statement was
located in the bounded prize-repository and Formal Conjectures search. The
official comparator gate is `NOT-AVAILABLE`; no official comparator PASS is
claimed. Independent source review and fixed/raw typed audits provide the
statement-fidelity checks here.

The published prize rules require axiom audits but do not explicitly allowlist
the three standard foundations above. Their prize acceptance remains unconfirmed.
Neither these local checks nor a submission assert official verification,
first priority, a prize award, or payment.

The MerLean executable grade audit awards no GOLD for this submission. Its live
generated Lean audit passes, but its coverage rule requires the one frozen main
root to cover all four theorem faces. Here the characterization, existence,
singleton, and pair statements are proved by four separately checked roots.
The retained audit reports `ROOT_FACE_MISMATCH`; no theorem, coverage label, or
runtime policy was changed to force a grade. This recorder outcome is separate
from the successful Lean builds, typed audits, and full fresh kernel replay.

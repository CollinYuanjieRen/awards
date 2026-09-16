# JSP-000936 / Erdős 1129: all optimal free interpolation nodes

This proves a necessary and sufficient condition for every family of distinct real
Lagrange interpolation nodes in `[-1,1]` to minimize the maximum amplification of
input errors. The extreme nodes are free to move. All positive node counts are covered.

For a node family `X`, its Lebesgue function is the literal sum of the absolute
Lagrange fundamental functions, and its Lebesgue constant is the supremum of that
function on the entire closed interval `[-1,1]`. For at least two nodes, the theorem is:

- `X` minimizes this constant among **all** distinct node families of the same size
  if and only if all internal consecutive-gap maxima are equal and the **original**
  Lebesgue function at each of `-1` and `1` is no larger than that common maximum.
- Every singleton family is optimal, with Lebesgue constant exactly one.

The roots are `Jsp936.minimizer_iff_equioscillating_and_controlled_tails` and
`Jsp936.singleton_nodes_optimal`. The data structure stores only node coordinates,
injectivity, and membership in `[-1,1]`; it contains no optimality assumption.
`Jsp936.nodeFamilyEquivCoordinates` identifies it with ordinary injective real coordinate
vectors in that interval. Sorting preserves the Lebesgue function and all interval suprema.

## Proof and scope

The credited de Boor–Pinkus core supplies the unique canonical equioscillating
endpoint-fixed array and coordinatewise peak rigidity. The new bridge sends arbitrary
extreme nodes to `-1,1` by a positive affine order isomorphism and proves preservation
of each actual Lagrange function, Lebesgue function, and internal gap supremum.
Monotonicity of absolute Lagrange products on the two exterior intervals reduces their
bounds to the two original endpoint values. A gap-cover argument and canonical rigidity
then prove both directions of the full characterization.

Canonical uniqueness is used internally. **No uniqueness of free-node minimizers is
asserted.** The original endpoint tail conditions are essential; testing only the
normalized function at its own endpoints would lose them. The two-node case is included
by `d = 0`, and the singleton case is proved separately. Empty families and repeated
nodes are outside this interpolation problem.

## Reproduce

Lean is pinned to `4.27.0`; Mathlib is pinned to
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. From this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The default target imports both roots and the coordinate adapter. `Audit.lean` checks
their expanded statements and prints their actual axiom dependencies. Both theorem
roots use exactly `propext`, `Classical.choice`, and `Quot.sound`. No additional axiom,
proof hole, `native_decide`, or assumed comparison theorem is used in the proof cone.

Independent reviews checked statement fidelity and proof composition, with typed root
checks and pinned Lean compilation. These are native Lean checks, not a claim of an
independent external kernel or sandbox isolation. No matching authoritative full
Erdős 1129 Lean target was located at the inspected Formal Conjectures snapshot
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`; no official-comparator pass is claimed.
The existing third-party three-node nonuniqueness challenge has narrower scope.
Verification and contribution evidence do not establish award eligibility or payment.

## Attribution and licenses

- Mathematical theory: T. A. Kilgore, *Optimization of the norm of the Lagrange
  interpolation operator* (1977), and C. de Boor and A. Pinkus, *Proof of the conjectures
  of Bernstein and Erdős concerning the optimal nodes for polynomial interpolation*,
  J. Approximation Theory 24 (1978), 289–303.
  [Author-hosted primary paper](https://pinkus.net.technion.ac.il/files/2021/02/conj.pdf).
- Existing formalization: [randyxian08/jsp000958-lean](https://github.com/randyxian08/jsp000958-lean/tree/e1df51e950876056d8951f4a93fa7fef6863b422),
  commit `e1df51e950876056d8951f4a93fa7fef6863b422`, MIT. The 23 files under
  `Randy1153/` are copied byte for byte; `vendor-manifest.json` records their hashes.
  `UPSTREAM-LICENSE` retains the copyright and permission notice. The first two
  comparison consequences in `Jsp936/CanonicalBounds.lean` also follow that repository's
  canonical JSP000936 adapter. Its canonical theory is credited to randyxian08.
- The new formalization contribution is the free-node affine/tail bridge, full
  minimizer equivalence, singleton case, and explicit coordinate adapter in `Jsp936/`.
  Its MIT license is provided explicitly in the local `LICENSE`. No claim of
  new mathematical discovery or authorship of the upstream core is made.

The related upstream [recipient issue #96](https://github.com/TheJustinSunPrize/awards/issues/96)
concerns JSP-000958 and explicitly limits its JSP-000936 material to the canonical case.
Any attribution or eligibility review should keep these contributions distinct.

# Original real-subdivision counterexample (JSP-000398 / Erdős 492)

This submission formalizes Schmidt's negative answer to the original question
about **real subdivision endpoints**. It also proposes a source correction to
the catalog's integer-only wording. The existing positive theorem for integer
endpoints, including plby's formalization, remains valid and is credited below.

The unconditional root is `Erdos492Real.schmidt_counterexample` in
[`MerLeanExperiment/Goal.lean`](MerLeanExperiment/Goal.lean). It constructs one
sequence `a : ℕ → ℝ`, fixed before the scale parameter, such that:

- `a 0 = 0`, `a` is strictly increasing and tends to infinity;
- `a (n + 1) / a n` tends to one;
- for Lebesgue-almost every positive real `α`, the sequence of positive multiples
  `n * α` is not uniformly distributed relative to the actual subdivision.

[`Subdivision.lean`](MerLeanExperiment/Subdivision.lean) defines the half-open
prefix of each actual gap and the normalized visit counts. The proof uses
arbitrarily late absolute signed averages near one to contradict the required
half-gap frequency limit. It does not claim that the signed limsup is always
positive one, or state a separate exact absolute-limsup theorem.

The finite construction is proved in
[`DilationLemma.lean`](MerLeanExperiment/DilationLemma.lean): simultaneous
logarithmic approximations produce fine exponential subdivisions whose actual
half-gap signs are invariant under finitely many dilations outside a small
explicit interval union. The global proof rescales and joins these subdivisions,
enumerates the actual endpoint set, applies Borel--Cantelli to the scaled
exceptional sets, and proves the signed-count obstruction. The public root
instantiates the finite lemma; it has no unproved intermediate premise.

## Sources and attribution

- P. Erdős, *Problems and results on diophantine approximations*, Compositio
  Mathematica **16** (1964), 52–65, especially printed page 62:
  [primary text](https://www.numdam.org/item/CM_1964__16__52_0.pdf).
- W. M. Schmidt, *Disproof of some conjectures on Diophantine approximations*,
  Studia Scientiarum Mathematicarum Hungarica **4** (1969), 137–144. Theorem 1
  and its proof occupy printed pages 137–141:
  [primary volume](https://real-j.mtak.hu/5455/1/StudScientMath_04.pdf).
- The one-page 1970 remark, printed page 479, concerns the priority of Theorem 2;
  it does not withdraw the real-subdivision counterexample:
  [primary volume](https://real-j.mtak.hu/5456/1/StudScientMath_05.pdf).
- plby's [positive integer-endpoint theorem](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos492.lean)
  addresses the distinct integer version. The finite simultaneous Dirichlet
  proof used here is also due to plby, at the same pinned revision, in
  [Erdos485/Dirichlet.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos485/Dirichlet.lean).

The external Dirichlet file is not redistributed because no explicit license
grant was located. The fetcher verifies its pinned source hash and a
provenance-comment-only adaptation. Its full proof is included in the verified
root dependency closure. The primary PDFs are linked, not redistributed.

## Reproduce

Lean is pinned to `4.34.0-rc1`; Mathlib is pinned to
`1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.

```sh
python3 fetch_sources.py
lake exe cache get
lake build
lake env lean verification/IndependentAudit.lean
```

The full proof build passed 8,767 jobs. The independent audit checks the
expanded unconditional target and traverses actual declaration bodies without
using the axiom cache. It inspected 33,276 declarations and found exactly
`propext`, `Classical.choice`, and `Quot.sound`. There are no custom mathematical
axioms, proof holes, or native-decision shortcuts.

See [`verification/README.md`](verification/README.md) for the strict
frozen-reference comparison, Lean kernel replay, negative controls and exact
receipts. No authoritative original-real Erdős 492 Lean target was located at
the recorded official-source snapshots. The comparison therefore uses an
independently reviewed, frozen original-real proposition; it is **not official
comparator approval**. The public prize rules do not explicitly name an
allowlist for these three foundational axioms. Acceptance remains subject to
the designated verification process. This submission does not assert an award,
payment, eligibility decision, or recognized first-formalization priority.

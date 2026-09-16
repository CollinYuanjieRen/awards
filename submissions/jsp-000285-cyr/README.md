# JSP-000285: eventual-density subcompleteness of multisets

This package proves the eventual-density form of Folkman's conjecture, associated with Erdős problem 343 and the Szemerédi–Vu theorem. There is an absolute positive integer C such that, for every sequence A of positive integers, if for all sufficiently large N at least C*N indexed occurrences have value at most N, the finite subset sums of A contain an infinite arithmetic progression with positive difference.

Distinct indices remain distinct occurrences, including when their values coincide. No monotonicity or finite-multiplicity restriction is imposed. The closed all-N monotone formulation is also derived.

The mathematical result is due to Endre Szemerédi and Van H. Vu, *Long arithmetic progressions in sumsets: thresholds and bounds*, J. Amer. Math. Soc. 19 (2006), §6; [author manuscript](https://arxiv.org/abs/math/0507539v2). This submission formalizes established mathematics.

## Statements

The principal declaration is `Erdos343.erdos_343_eventual` in `Jsp285/Statement.lean`:

```lean
∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
  (∀ i, 0 < A i) →
  HasEventualLinearCountingLowerBound C A →
  IsSubcomplete A
```

The density premise is literally an eventual finite-index witness with cardinality at least C*N. The conclusion supplies a,d with d>0 and a finite index set summing to a+k*d for every natural k. `Audit.lean` checks the fully expanded statement, the closed all-N corollary, equality with the auxiliary indexed-sum model, and actual examples allowing infinite repetition.

The auxiliary finite multiset theorem `Jsp285.finite_multiset_AP` is proved internally. For values between 1 and n and at least F*n indexed occurrences, it constructs an AP of length n in their subset sums, with F=200000*200^49. The infinite theorem uses the explicit coefficient C=512*F^2. These constants are sufficient bounds, not optimality claims.

## Proof and attribution

The finite proof preserves occurrence indices through divisor extraction, whole dyadic-bin pruning, simultaneous partition, modular subset-sum coverage, and repeated-pivot growth. It instantiates an existing checked sum-tree progression theorem. The infinite proof constructs disjoint index streams from eventual counting, builds and merges finite blocks, stabilizes a positive progression step, and combines residue coverage with an additive net. Every intermediate hypothesis is discharged before the closed root.

The reproduction script downloads credited components into `ErdosProblems/` from [plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest), at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Original headers and formal/mathematical authorship are retained. Six downloaded files are unchanged; `Erdos360/Core.lean` retains the exact documented contiguous source section. `vendor-manifest.json` records every source URL, hash, and transformation. No authorship of these reused proofs is claimed. Upstream source files are not redistributed in this submission: the upstream notice does not establish a blanket license for all seven files. The manifest distinguishes four explicitly Apache-licensed files from three whose redistribution license was not established.

## Reproduction

Lean is pinned to **4.33.0** and mathlib to **db584cd6d46c92f209a44c0f1c829460d327499d**. From this directory:

```sh
python3 fetch_sources.py
lake exe cache get
lake build
lake env lean Audit.lean
```

To replay all eligible imported declarations into a fresh trust-level-zero environment:

```sh
mkdir -p .lake/replay
lake env lean -c .lake/replay/ReplayCheck.c checks/ReplayCheck.lean
lake env leanc -O3 -o .lake/replay/replay-check .lake/replay/ReplayCheck.c
lake env .lake/replay/replay-check Jsp285 Erdos343.erdos_343_eventual Erdos343.erdos_343_all_N Jsp285.finite_multiset_AP Jsp285.indexedSubsetSums_univ_eq
```

The standalone harness rechecks all non-unsafe, non-partial imported declarations using checked `Kernel.Environment.addDeclCore`, compares generated constructors, recursors and quotient primitives, and checks root presence. This is fresh replay using the same pinned Lean kernel implementation, not an independently implemented kernel. Neither check harness is imported by the mathematical proof. `checks/NegativeControl.lean` exercises rejection of an intentionally malformed theorem.

## Verification scope

The full default build completed successfully (8745 jobs). Fresh checked kernel replay passed for all 768,544 eligible imported declarations and all four requested roots in 1140.40 seconds. Both closed problem roots, the finite multiset theorem, and the intended-model equality report exactly `propext`, `Classical.choice`, and `Quot.sound`. Independent source/goal and finite/infinite proof reviews found no additional original-problem condition or unresolved helper premise. Exact results and file hashes are recorded in `verification.json` and `checks/`.

No canonical problem 343 challenge was found in the nontruncated `google-deepmind/formal-conjectures` tree at commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. The independently hosted plby problem 343 theorem addresses the monotone all-N formulation, not the full eventual target proved here. No official comparator success is claimed.

The [published prize rules](https://www.hejustinsun.com/prize/rules) effective September 16, 2026 require verifier axiom/checker review and contain no explicit allowlist for the three foundational axioms. Their explicit acceptance by the prize remains unconfirmed. Local verification and this submission do not establish official acceptance, priority, an award, or payment.

## Licensing

New proof files and the dependency-fetch script are contributed under Apache-2.0; see `LICENSE-APACHE`. The standalone replay harness retains Kim Morrison's Apache-2.0 header. External sources are retrieved directly from their pinned original public repository and are not included in this submission. Their original attribution and license notices are preserved after retrieval; no blanket redistribution grant is asserted. See `NOTICE` and `vendor-manifest.json`.

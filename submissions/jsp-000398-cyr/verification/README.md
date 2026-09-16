# Verification of the original real-subdivision theorem

The reference is an independently reviewed, frozen original-real proposition,
not an official prize challenge. No authoritative original-real Erdős 492 Lean
target was found in awards revision `f4e7173d89dfe91022a185427d63452c8ffbf6ae`
or Formal Conjectures revision `40e7c98697de6f66b8cbdbf641749ab39ed9c152`.
plby's integer challenge has a different endpoint domain.

[`reference/MerLeanExperiment/FrozenStatement.lean`](reference/MerLeanExperiment/FrozenStatement.lean)
contains the unchanged frozen definitions and a closed proposition definition,
with no proof import, assumed theorem or custom axiom. Its SHA-256 is
`284422849e95c0c5db2a04a5727aef900e48926b5ec70d34493f7a90a4d5b8b6`.

The reused driver pins upstream comparator
`011e9d35a10a054ed4b66d8379115ad870f2b0ce` and exporter
`b18d673bd29b476466a51a3be1012df2ed322b10`. It requires exact equality between
the candidate theorem type and the reference proposition's value, compares
the target's definition/dependency closure with empty exception sets, checks
actual root axioms against the three standard foundations, and replays both
exported environments through Lean's kernel. No definition-body exception is
used. Its historical executable name, `jsp511-comparator-driver`, is retained;
the theorem names are command-line arguments.

After the parent README's fetch/build steps, the following commands reproduce
the comparison. Run this block in `sh` or `bash` from the submission directory.

```sh
JSP398_BASE="$(pwd)"
JSP398_DRIVER="$JSP398_BASE/verification/comparator-driver"
JSP398_REF="$JSP398_BASE/verification/reference"
JSP398_OUT="$(mktemp -d)"

(cd "$JSP398_DRIVER" && lake build lean4export jsp511-comparator-driver \
  TestFixtures.Reference TestFixtures.Candidate)
(cd "$JSP398_REF" && lake exe cache get && lake build)

JSP398_EXPORTER="$JSP398_DRIVER/.lake/packages/lean4export/.lake/build/bin/lean4export"
JSP398_CHECKER="$JSP398_DRIVER/.lake/build/bin/jsp511-comparator-driver"
JSP398_PRIMITIVES="propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce"

(cd "$JSP398_REF" && lake env "$JSP398_EXPORTER" MerLeanExperiment.FrozenStatement -- \
  Erdos492Real.expectedStatement $JSP398_PRIMITIVES) > "$JSP398_OUT/reference.ndjson"
(cd "$JSP398_BASE" && lake env "$JSP398_EXPORTER" MerLeanExperiment.Goal -- \
  Erdos492Real.schmidt_counterexample $JSP398_PRIMITIVES) > "$JSP398_OUT/candidate.ndjson"
(cd "$JSP398_DRIVER" && lake env "$JSP398_CHECKER" \
  "$JSP398_OUT/reference.ndjson" "$JSP398_OUT/candidate.ndjson" \
  Erdos492Real.expectedStatement Erdos492Real.schmidt_counterexample)

(cd "$JSP398_DRIVER" && lake env "$JSP398_EXPORTER" TestFixtures.Reference -- \
  ComparatorFixture.expectedStatement $JSP398_PRIMITIVES) > "$JSP398_OUT/test-reference.ndjson"
(cd "$JSP398_DRIVER" && lake env "$JSP398_EXPORTER" TestFixtures.Candidate -- \
  ComparatorFixture.root $JSP398_PRIMITIVES) > "$JSP398_OUT/test-candidate.ndjson"
(cd "$JSP398_DRIVER" && lake env "$JSP398_CHECKER" --self-test \
  "$JSP398_OUT/test-reference.ndjson" "$JSP398_OUT/test-candidate.ndjson" \
  ComparatorFixture.expectedStatement ComparatorFixture.root)

lake env lean verification/IndependentAudit.lean
```

The negative controls accept an honest fixture and reject a changed theorem
type, a changed definition used by the target, and an injected custom-axiom
dependency. A separate control confirms that unexpected acceptance fails the
test harness. Mutations occur only in exported data in memory; no custom
axiom is declared in the proof or reference fixtures.

[`IndependentAudit.lean`](IndependentAudit.lean) checks the expanded
unconditional real-subdivision target and traverses actual kernel declaration
bodies without the axiom cache. It also requires the actual finite
construction, sign bridge and global almost-everywhere argument to occur in
the root closure. Independent source and proof reviews found no undischarged
root premise or substantive mismatch; see [`review-summary.md`](review-summary.md).

Exact commands' outcomes and hashes are in [`receipt.json`](receipt.json),
[`proof-sources.json`](proof-sources.json), [`axioms.log`](axioms.log),
[`comparator.log`](comparator.log), and [`negative-tests.log`](negative-tests.log).
The recorded comparator execution is native macOS execution, without a
process sandbox, and uses Lean's kernel replay. It is not a separately
implemented kernel check or an official designated-verifier decision.

The [public prize rules](https://www.hejustinsun.com/prize/rules) require a
statement, proof and supporting evidence in an official source PR, followed
by designated verification. They do not explicitly approve the three named
foundational axioms. The records therefore report their actual use and leave
official acceptance to that process; no award or payment is claimed.

# Exact frozen-target verification

Observed results and hashes are recorded in [receipt.json](receipt.json), with [build](build.log), [axiom](axioms.log), [comparator](comparator.log), and [negative-test](negative-tests.log) logs. A separate [supporting review summary](review-summary.md) describes the source and proof audits.

The reference package contains a byte-identical copy of the ordinary drawing definition and a closed proposition definition, `PlanarListColoring.expectedStatement`. It contains no unproved theorem, proof hole, or custom axiom. Its source SHA-256 is `a52d0905ca61f69b852f10267775654024c8006089c31a608bc74b7a58e0b238`.

The driver uses upstream comparator commit `011e9d35a10a054ed4b66d8379115ad870f2b0ce` and exporter commit `b18d673bd29b476466a51a3be1012df2ed322b10`, both compatible with Lean 4.34.0-rc1. The stock `definition_names` mechanism intentionally permits definition bodies to differ, so this driver does not use it. It instead:

1. Requires a safe, closed reference definition of type `Prop` with no universe parameters.
2. Requires a closed candidate theorem whose type is exactly the reference definition's value.
3. Compares every target dependency, kernel primitive, and standard axiom with **empty exception sets**.
4. Traverses the actual candidate proof and permits only `propext`, `Classical.choice`, and `Quot.sound`.
5. Replays both exported environments through Lean's kernel.

The source is in [Driver/Core.lean](comparator-driver/Driver/Core.lean); [Main.lean](comparator-driver/Main.lean) supplies the CLI and negative tests. Those tests mutate exported data in memory to verify rejection of a changed theorem type, a changed supporting definition, and a custom-axiom dependency. They do not add an axiom to any Lean proof or reference fixture. An additional control checks that the negative-test harness fails when its action unexpectedly succeeds.

## Commands

Run the following from the submission directory after its ordinary build. These are native checks in a trusted local environment; sandbox controls and independent external-kernel replay are separate operations.

```sh
JSP511_BASE="$(pwd)"
JSP511_DRIVER="$JSP511_BASE/verification/comparator-driver"
JSP511_REF="$JSP511_BASE/verification/reference"
JSP511_OUT="$(mktemp -d)"

(cd "$JSP511_DRIVER" && lake build lean4export jsp511-comparator-driver \
  TestFixtures.Reference TestFixtures.Candidate)
(cd "$JSP511_REF" && lake exe cache get && lake build)

JSP511_EXPORTER="$JSP511_DRIVER/.lake/packages/lean4export/.lake/build/bin/lean4export"
JSP511_CHECKER="$JSP511_DRIVER/.lake/build/bin/jsp511-comparator-driver"
JSP511_PRIMITIVES="propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce"

(cd "$JSP511_REF" && lake env "$JSP511_EXPORTER" MerLeanExperiment -- \
  PlanarListColoring.expectedStatement $JSP511_PRIMITIVES) > "$JSP511_OUT/reference.ndjson"
(cd "$JSP511_BASE" && lake env "$JSP511_EXPORTER" MerLeanExperiment.Goal -- \
  PlanarListColoring.planar_bipartite_three_list_colorable $JSP511_PRIMITIVES) \
  > "$JSP511_OUT/candidate.ndjson"
(cd "$JSP511_DRIVER" && lake env "$JSP511_CHECKER" \
  "$JSP511_OUT/reference.ndjson" "$JSP511_OUT/candidate.ndjson" \
  PlanarListColoring.expectedStatement \
  PlanarListColoring.planar_bipartite_three_list_colorable)

(cd "$JSP511_DRIVER" && lake env "$JSP511_EXPORTER" TestFixtures.Reference -- \
  ComparatorFixture.expectedStatement $JSP511_PRIMITIVES) > "$JSP511_OUT/test-reference.ndjson"
(cd "$JSP511_DRIVER" && lake env "$JSP511_EXPORTER" TestFixtures.Candidate -- \
  ComparatorFixture.root $JSP511_PRIMITIVES) > "$JSP511_OUT/test-candidate.ndjson"
(cd "$JSP511_DRIVER" && lake env "$JSP511_CHECKER" --self-test \
  "$JSP511_OUT/test-reference.ndjson" "$JSP511_OUT/test-candidate.ndjson" \
  ComparatorFixture.expectedStatement ComparatorFixture.root)
```

The reference's implication binders have intentionally preserved names matching the frozen theorem; Lean's unused-variable linter may warn about them in the proposition definition. This is not a proof placeholder.

## Scope of the receipt

The target was frozen and independently checked against the finite-graph Alon–Tarsi statement. No official Erdős 630 Lean challenge was available in the checked Formal Conjectures snapshot. A pass here certifies equality with this supplied frozen target and its definitions, together with the reported axiom and Lean-kernel checks. It does not establish English–Lean equivalence without source review, prize-specific approval of axioms, sandbox isolation, external-kernel agreement, or an award decision.

# Frozen-target comparison and proof checks

[receipt.json](receipt.json) records successful results, source/tool pins and SHA-256 hashes. Logs cover the [complete build](build.log), [root axioms](axioms.log), [comparison](comparator.log), [negative tests](negative-tests.log) and [independent kernel traversal](independent-kernel.log). [proof-sources.json](proof-sources.json) hashes all 92 Lean source files, including the five externally fetched dependencies. [review-summary.md](review-summary.md) explains the separate supporting reviews and their limits.

The frozen reference contains the unchanged ordinary drawing definition and the complete closed proposition `Erdos1018Topological.expectedStatement`, without an unproved theorem, axiom or proof import. Its source SHA-256 is `e3ec3557eeed5ddfccbc6d8490640671d340e5ab053106c7bcba76f0a4fcc3a6`.

The comparator-based driver is reused unchanged from the reviewed JSP511 package; its executable retains the name `jsp511-comparator-driver` and accepts the target names as arguments. It uses upstream comparator `011e9d35a10a054ed4b66d8379115ad870f2b0ce` and exporter `b18d673bd29b476466a51a3be1012df2ed322b10`. The driver requires exact equality between the candidate theorem type and the reference proposition's value, compares the full definition/dependency closure with empty exception sets, checks the actual root axioms against the three standard foundations, and replays both exported environments through Lean's kernel. No definition-body exemption is used.

## Reproduce

First follow the source-fetch and Lean build commands in the parent README. The following native checks assume the shell's ordinary whitespace splitting; use a POSIX shell such as `sh` or `bash` for this block.

```sh
JSP848_BASE="$(pwd)"
JSP848_DRIVER="$JSP848_BASE/verification/comparator-driver"
JSP848_REF="$JSP848_BASE/verification/reference"
JSP848_OUT="$(mktemp -d)"

(cd "$JSP848_DRIVER" && lake build lean4export jsp511-comparator-driver \
  TestFixtures.Reference TestFixtures.Candidate)
(cd "$JSP848_REF" && lake exe cache get && lake build)

JSP848_EXPORTER="$JSP848_DRIVER/.lake/packages/lean4export/.lake/build/bin/lean4export"
JSP848_CHECKER="$JSP848_DRIVER/.lake/build/bin/jsp511-comparator-driver"
JSP848_PRIMITIVES="propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce"

(cd "$JSP848_REF" && lake env "$JSP848_EXPORTER" MerLeanExperiment -- \
  Erdos1018Topological.expectedStatement $JSP848_PRIMITIVES) > "$JSP848_OUT/reference.ndjson"
(cd "$JSP848_BASE" && lake env "$JSP848_EXPORTER" MerLeanExperiment.Goal -- \
  Erdos1018Topological.erdos_1018_ordinary_nonplanarity $JSP848_PRIMITIVES) \
  > "$JSP848_OUT/candidate.ndjson"
(cd "$JSP848_DRIVER" && lake env "$JSP848_CHECKER" \
  "$JSP848_OUT/reference.ndjson" "$JSP848_OUT/candidate.ndjson" \
  Erdos1018Topological.expectedStatement \
  Erdos1018Topological.erdos_1018_ordinary_nonplanarity)

(cd "$JSP848_DRIVER" && lake env "$JSP848_EXPORTER" TestFixtures.Reference -- \
  ComparatorFixture.expectedStatement $JSP848_PRIMITIVES) > "$JSP848_OUT/test-reference.ndjson"
(cd "$JSP848_DRIVER" && lake env "$JSP848_EXPORTER" TestFixtures.Candidate -- \
  ComparatorFixture.root $JSP848_PRIMITIVES) > "$JSP848_OUT/test-candidate.ndjson"
(cd "$JSP848_DRIVER" && lake env "$JSP848_CHECKER" --self-test \
  "$JSP848_OUT/test-reference.ndjson" "$JSP848_OUT/test-candidate.ndjson" \
  ComparatorFixture.expectedStatement ComparatorFixture.root)

lake env lean verification/IndependentAudit.lean
```

The negative tests mutate exported data in memory. They reject a changed theorem type, a changed supporting definition and a custom-axiom dependency; a control tests that unexpected acceptance actually fails the harness. No custom axiom is declared in the proof or reference fixtures.

`IndependentAudit.lean` checks the complete target type, prints axioms, and traverses actual kernel declaration bodies without using the axiom cache. It rejects any nonstandard axiom and any dependency on the old certificate-only nonplanarity predicate. The proposition reference's deliberately retained implication binder name can produce an unused-variable linter warning; it is not a proof placeholder.

## Reported scope

The actual submitted proof export is 148,208,791 bytes, SHA-256 `d04d7705385abb1bd8b62e5ac83b3a0e64533399306c02f1b15c78f4f19cd76a`. Large generated exports are reproducible from the pinned sources and are not separately archived here.

No authoritative Erdős1018 Lean challenge was available in the checked organizer/original-source repositories. This successful check is against the independently frozen and reviewed ordinary-drawing statement. It does not replace source-to-formal semantic review or establish official prize acceptance. The recorded macOS run is unsandboxed; no independent external kernel was run. The prize's public instructions do not explicitly whitelist `propext`, `Classical.choice`, and `Quot.sound`.

# Canonical AP and positive-density comparison: PASS

This evidence concerns two canonical Erdős 318 endpoints:

- `Erdos318.erdos_318.variants.infinite_AP`: every infinite arithmetic progression has property `P₁`.
- `Erdos318.erdos_318.parts.i`: some set of positive natural density does not have property `P₁`.

Both targets passed the official declaration/dependency comparison, permitted-axiom checks and native Lean kernel replay; exit **0**. The log ends with `Lean default kernel accepts the solution` and `Your solution is okay!`. Exact results and hashes are recorded in `result.json`. The square component is covered by a separate comparison on Lean 4.34.

**Verification class: unsandboxed macOS development comparison.** Production Linux/Landrun sandbox: **NOT RUN**. Nanoda: **NOT RUN**. This is not an organizer acceptance or a check in the original reference's Lean 4.33.1 environment.

## Fixed versions and attribution

- Official `leanprover/comparator` tag `v4.33.0`, commit `3927ad383f208ae977c340a91c48ac9b497d2097`.
- Its committed `leanprover/lean4export` pin: `15f6055e299ad5b89345e533cc2192f4cc00f659`.
- Tool and comparison toolchain: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`, retaining the reused proof environment's full dependency manifest.
- Reused proof source: `plby/lean-proofs`, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. The proofs are credited reuse; the namespace adapter supplies the canonical AP endpoint.
- Canonical reference: `google-deepmind/formal-conjectures`, commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`, originally Lean 4.33.1.

The official comparator and exporter were built unchanged in an independent checkout, exit 0, 21 jobs. Their source identities and native binary hashes are recorded in `tool-manifest.json`; the build log is `native-build.log`.

## Reference extraction and version port

All reference declarations were freshly fetched from the fixed official source, independently of the solution. Full originals with Apache headers are retained under `original-source/`. The exact extracted declaration spans and hashes appear in `reference/extraction-manifest.json`:

- P₁ and both target statements from `FormalConjectures/ErdosProblems/318.lean`.
- `Set.partialDensity`, `Set.HasDensity`, `Set.HasPosDensity` from `FormalConjecturesForMathlib/Data/Set/Density.lean`.
- `Set.IsAPOfLengthWith`, `Set.IsAPOfLength` from `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`.

Each extracted declaration is byte-identical to its source span; the partial-density declaration retains its inline attribute. Required namespace, variable and notation context is preserved. The three reference modules retain the original license headers. Unrelated declarations, source-only category attributes and broad utility imports are omitted, and the retained definitions import Mathlib directly. Independent review confirmed the actual natural-density limit predicate, the AP cardinality/affine-image definition and exact P₁ quantifiers.

The reference's original unresolved theorem bodies are isolated specifications, never imports of the solution. There are no `definition_names` holes, and the permitted axiom list is exactly `propext`, `Quot.sound`, `Classical.choice`.

This is a reviewed source port from FC's Lean 4.33.1 environment to the proof's fixed Lean/Mathlib 4.33.0 environment. The comparator compares the full exported statement dependency closure in those two 4.33.0 environments. It does not itself establish that all dependency definitions are unchanged across toolchain versions; the extraction/import port is explicit provenance, not a concealed claim of original-environment identity.

## Canonical solution adapter

The reused source's AP predicate is an alias under `Erdos318.Set`; the canonical reference uses root `Set.IsAPOfLength`. Their definition bodies agree. The original AP endpoint and its local uses were mechanically renamed `_reused`, as recorded in `reused-endpoint-rename.diff`. The canonical adapter imports the exact root AP definitions and proves the original endpoint by unfolding the aliases. The printed proof reduces to applying the reused theorem to `id hA`; no premise was added. The positive-density endpoint retains the reused theorem unchanged.

`solution-source-hashes.json` records the exact 14-file canonical solution import closure copied into a separate checker. No original proof source was edited during comparison. Trusted local prebuilt artifacts were copied alongside the source snapshot; the official comparator then invoked Lake's build checks, exported both environments and independently replayed the exported proof closure into the Lean kernel. Accordingly, this is not described as a cache-free rebuild. The solution's import closure excludes the reference modules.

The native comparison uses the unmodified official executable and unmodified upstream `scripts/fake-landrun.sh`. That script deliberately does not isolate execution; this was explicitly a development run. No comparison, export, proof or axiom check was replaced. The official `compareAt`, `checkAxioms` and kernel replay execute before the final success output. The canonical solution module's diagnostics additionally print both standard-three-axiom audits.

## Reproduction commands

Paths below are portable placeholders. Prepare an independently managed checker with the frozen proof sources and dependency configuration; put the three reference files under `ErdosProblems/` and the comparison config at its root. Build the exact official tool checkout:

```sh
git init <COMPARATOR_ROOT>
git -C <COMPARATOR_ROOT> remote add origin https://github.com/leanprover/comparator.git
git -C <COMPARATOR_ROOT> fetch --depth=1 origin 3927ad383f208ae977c340a91c48ac9b497d2097
git -C <COMPARATOR_ROOT> checkout --detach FETCH_HEAD
cd <COMPARATOR_ROOT>
lake build lean4export comparator
```

Keep the committed manifest unchanged and verify the exporter revision. The actual development comparison command was equivalent to:

```sh
cd <CHECK_ROOT>
COMPARATOR_LANDRUN=<COMPARATOR_ROOT>/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=<COMPARATOR_ROOT>/.lake/packages/lean4export/.lake/build/bin/lean4export \
elan run leanprover/lean4:v4.33.0 lake env \
  <COMPARATOR_ROOT>/.lake/build/bin/comparator comparator-config.json
```

The official config lists both canonical target names, the isolated reference module, `ErdosProblems.Erdos318Canonical` as solution, exactly the standard three permitted axioms, and `enable_nanoda: false`.

Production verification requires a fresh trusted nonprivileged Linux environment with real pinned Landrun and the upstream `systemd-run --property=RestrictAddressFamilies=~AF_UNIX` restriction. The native development result does not provide those security guarantees.

## Evidence handling

`comparator-development.log` preserves all official comparison output and diagnostics. Only absolute machine paths are replaced with `<COMPARATOR_ROOT>` or `<CHECK_ROOT>`. `result.json` records the private unredacted log's SHA-256 and the published redacted log's SHA-256. No warning or result line is removed. `artifact-hashes.json` covers the publication evidence files.

Primary sources:

- https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097
- https://github.com/leanprover/lean4export/tree/15f6055e299ad5b89345e533cc2192f4cc00f659
- https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/318.lean
- https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e

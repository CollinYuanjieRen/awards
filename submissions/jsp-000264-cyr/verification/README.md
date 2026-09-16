# Canonical square-component comparison: PASS

The official Lean comparator accepted `Erdos318.erdos_318.parts.ii` against an independently extracted, source-pinned Formal Conjectures reference port. Its declaration/dependency comparison, permitted-axiom traversal and Lean default kernel replay completed successfully, process exit **0**. The final log contains `Lean default kernel accepts the solution` and `Your solution is okay!`.

**Classification: unsandboxed macOS development verification.** Production Linux/Landrun sandbox: **NOT RUN**. Nanoda: **NOT RUN**. This is not an organizer acceptance or a verification in the original Lean 4.33.1 environment. Scope is only the canonical square component, not all statements in Erdős 318.

## Versions and executable provenance

- `leanprover/comparator`: `011e9d35a10a054ed4b66d8379115ad870f2b0ce`, tag `v4.34.0-rc1`.
- Its pinned `leanprover/lean4export`: `b18d673bd29b476466a51a3be1012df2ed322b10`.
- Both unchanged Git checkouts built successfully with `lake build lean4export comparator`; exit 0, 21 jobs. Native executable hashes are in `tool-build-manifest.json`.
- Comparison toolchain: `leanprover/lean4:v4.34.0-rc1`; Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` and the submission's full pinned transitive manifest.
- Host: macOS 26.6.2, arm64. The official upstream `scripts/fake-landrun.sh` was used explicitly in development mode. It provides no sandbox.

## Independent reference and faithful source port

Original source: `google-deepmind/formal-conjectures` commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`, originally Lean `v4.33.1`. The exact fetched originals are retained in `original-source/` with their licenses.

`reference/Challenge.lean` extracts the complete original `P₁` declaration from 318.lean lines 40–44 and original theorem from lines 134–135 **byte-for-byte**, including `answer(True)` and the original unresolved reference body. It retains the Apache header. The original namespace and `open Set Real` are preserved. Unrelated declarations, nonsemantic category attributes and the broad utility umbrella import are omitted; Mathlib and the reference-only answer elaborator are imported directly. The extraction was independently reviewed before execution.

`reference/AnswerSyntax.lean` is byte-identical to pinned FC `FormalConjecturesUtil/Answer/Syntax.lean`. `reference/Answer.lean` is the complete pinned elaborator with exactly one import relocation, shown in `answer-import-port.diff`. Its logic is unchanged. Thus the actual reference still elaborates `answer(True)` using the original elaborator. The official exporter removes expression metadata by default, making the solution's explicit `True` match without any proposition-definition hole.

These sources are rebuilt on Lean/Mathlib 4.34, so this is a documented source port. Comparator compares the complete exported statement dependency closure in the two 4.34 environments. It does not itself prove that every dependency is unchanged from the earlier 4.33.1 environment; that provenance obligation is addressed by explicit source extraction/import review rather than concealed.

The inherited unresolved proof occurs only in the isolated external reference specification. It is never imported by the solution. The checker holds Challenge and Solution in separate export environments with the same target theorem name. No `definition_names` holes are configured; permitted axioms are exactly `propext`, `Quot.sound`, `Classical.choice`.

## Exact submission snapshot and build discipline

The checker copied the final submission's 57 module source files, aggregate and Audit.lean byte-for-byte; hashes are in `solution-source-hashes.json`. None mentions `ComparatorReference`. No compiled proof artifacts were copied. The isolated checker rebuilt the solution (8801 jobs), and separately built the aggregate successfully (8803 jobs), exit 0. The fresh snapshot also passed its Audit.lean check (exit 0); both the frozen root and canonical endpoint report exactly the three standard axioms, as recorded in `axiom-audit.log`. Reference source files are verification artifacts outside the submitted proof's import closure.

The checker was initialized with the immutable shared workspace profile. The unmodified official comparator invoked the unmodified upstream fake-landrun script. A PATH `lake` launcher accepted only `lake build MODULE` and forwarded it to `merlean-workspace build --project <CHECK_ROOT> MODULE`, preserving locks, exact toolchain selection and before/after provider identity checks. It retried only explicit busy-provider failures. Export used the unmodified official exporter; no statements, exports or comparison results were substituted. The tool's actual `compareAt`, `checkAxioms` and kernel replay ran.

## Commands and reproducibility

Paths below are portable placeholders; substitute the actual tool/checker/helper locations. Tool checkout/build:

```sh
git init <COMPARATOR_ROOT>
git -C <COMPARATOR_ROOT> remote add origin https://github.com/leanprover/comparator.git
git -C <COMPARATOR_ROOT> fetch --depth=1 origin 011e9d35a10a054ed4b66d8379115ad870f2b0ce
git -C <COMPARATOR_ROOT> checkout --detach FETCH_HEAD
cd <COMPARATOR_ROOT>
lake build lean4export comparator
```

The committed manifest must remain unchanged; verify the actual exporter checkout equals the pinned revision above. Prepare a separate checker with the submission's exact pinned configuration and sources; place the three reference files under `MerLeanExperiment/ComparatorReference/`. For a managed checker, route comparator's `lake build` operations through the shared helper as described above. The executed outer command was:

```sh
cd <CHECK_ROOT>
lake env python3 <AUDIT_ROOT>/run-development-comparator.py > <AUDIT_ROOT>/development-comparator.log 2>&1
```

The runner prepended the build launcher to PATH, set `COMPARATOR_LANDRUN=<COMPARATOR_ROOT>/scripts/fake-landrun.sh` and `COMPARATOR_LEAN4EXPORT=<COMPARATOR_ROOT>/.lake/packages/lean4export/.lake/build/bin/lean4export`, then executed `<COMPARATOR_ROOT>/.lake/build/bin/comparator <CHECK_ROOT>/comparator-config.json`. The launcher's actual build command was:

```sh
<MERLEAN_WORKSPACE> build --project <CHECK_ROOT> <MODULE>
```

For a fresh independently managed checker, the equivalent upstream development invocation is:

```sh
COMPARATOR_LANDRUN=<COMPARATOR_ROOT>/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=<COMPARATOR_ROOT>/.lake/packages/lean4export/.lake/build/bin/lean4export \
lake env <COMPARATOR_ROOT>/.lake/build/bin/comparator comparator-config.json
```

This equivalent command is not a production sandbox invocation. A production check requires a fresh trusted nonprivileged Linux environment with real pinned Landrun, the upstream `systemd-run --property=RestrictAddressFamilies=~AF_UNIX` restriction, and trusted reference/configuration setup before compiling potentially adversarial solution files. Native macOS sandbox-exec is not a replacement.

## Evidence redaction

`comparator-development.log` is the raw official run log with only absolute machine paths replaced: the checker directory becomes `<CHECK_ROOT>` and tool checkout becomes `<COMPARATOR_ROOT>`. No messages, diagnostics, warnings or result lines were removed. `result.json` retains both the private unredacted log SHA-256 and the published redacted log SHA-256. Source and native executable fingerprints are not affected by this log redaction. `artifact-hashes.json` fingerprints this evidence bundle.

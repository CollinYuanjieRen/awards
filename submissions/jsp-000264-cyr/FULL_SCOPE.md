# Verification of all three catalog questions

JSP-000264 / Erdős 318 contains three questions. All three now have checked exact canonical endpoints. Only the square component is new formalization work in this submission; the other two are verified, credited reuse.

| Question | Answer and exact theorem | Proof provenance | Verification environment |
| --- | --- | --- | --- |
| Infinite arithmetic progressions | Yes: `Erdos318.erdos_318.variants.infinite_AP` | plby commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, with a proved canonical predicate adapter | Lean 4.33.0 / Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` |
| All sets of positive density | No: `Erdos318.erdos_318.parts.i` | Same credited plby source; odds together with 2 have actual density 1/2 and fail P₁ | Same 4.33.0 environment |
| Squares greater than one | Yes: `Erdos318.erdos_318.parts.ii` | This package, formalizing Daniel Larsen's square construction | Lean 4.34.0-rc1 / Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` |

For every endpoint, the recursive axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`. No solution uses custom axioms, admitted proofs or target-bearing assumptions. AP infinitude and the signing's two nonconstancy conditions are the original hypotheses. The density face proves existence of an actual positive natural-density counterexample, not a weaker positive-upper-density statement.

The [square comparison](verification/README.md) and [AP/density comparison](verification/reused-faces-comparator/README.md) are actual successful runs of the pinned official Lean comparator, including full statement/dependency matching, permitted-axiom checks and native Lean kernel replay. Both compare against independently sourced extracts of Formal Conjectures commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`, with no definition holes. The reference ports retain the original propositions and definitions; the original repository used Lean 4.33.1. The separate environments are deliberate: no foreign-version oleans are imported into another toolchain.

Both runs are explicitly unsandboxed macOS development verification. Production Linux isolation and nanoda were not run. Formal Conjectures supplies the reference collection; no prize-organizer adoption of this checker, acceptance of an axiom allowlist, award decision or independent permanent archive is asserted.

The [reuse bundle](reuse/README.md) fetches only 12 pinned source files and verifies every source hash, preserves attribution and licenses, then applies the four recorded endpoint-name replacements and the definitional AP adapter. Its preparation script was run successfully against a new directory. The exact original source and canonical-adapter builds both passed before the native comparison. The 21,208-line prior proof closure is referenced reproducibly, rather than presented as new work.

# JSP-000360 / Erdős 441: sets with bounded pairwise lcm

This package submits a complete Lean formalization of the two questions in [Erdős problem 441](https://www.erdosproblems.com/441), referenced by [JSP-000360](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000360), for intake and eligibility review.

## Exact statement

[Target.lean](MerLeanExperiment/Target.lean) proves `Erdos441.erdos_441_complete`:

```lean
theorem erdos_441_complete :
    Filter.Tendsto (fun N : ℕ => (g N : ℝ) / Real.sqrt ((9 / 8 : ℝ) * N))
      Filter.atTop (nhds 1) ∧
    ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ (erdosConstruction N).card < g N
```

The definitions in [External/Erdos441.lean](MerLeanExperiment/External/Erdos441.lean) use ordinary natural numbers and finite sets. `LcmBounded N A` says that `A ⊆ Finset.Icc 1 N` and `Nat.lcm a b ≤ N` for every pair of members. `g N` is the maximum cardinality over all such admissible sets, defined by the supremum of a finite family. `erdosConstruction N` is the proposed union of the positive integers up to √(N/2) and the even positive integers up to √(2N), expressed using exact square inequalities.

The first conjunct proves the sharp asymptotic `g(N) ∼ √(9N/8)`. The second says that at arbitrarily large natural N the proposed construction has strictly smaller size than the optimum. The theorem has no public hypotheses. Its asymptotic statement does not require a value for the normalized ratio at N=0. The result does not claim the stronger quantitative error term or growing nonoptimality gap from later papers.

## Proof and attribution

The new asymptotic formalization follows Yong-Gao Chen, “Sequences with bounded l.c.m. of each pair of terms”, *Acta Arithmetica* 84 (1998), 71–95, [DOI](https://doi.org/10.4064/aa-84-1-71-95), [primary article](https://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8416.pdf). The primary PDF used for statement and argument review has SHA-256 `1612db24526724506ca180102cfe0e9f7d68a7fe42b26a9c41b2818eed5253a4` (270087 bytes). It is linked, not included in this package.

The implementation proves the finite sieve and coprimality estimates, parity-sensitive interval packing, order-preserving weighted allocation, all geometric-grid prefix cases and exact weight sum. The resulting uniform upper bound combines with a proved lower bound to obtain the limit in [Asymptotic.lean](MerLeanExperiment/Asymptotic.lean). All mathematical support used here is proved in Lean or supplied by pinned Mathlib; the paper is not introduced as an axiom or theorem assumption.

The ordinary extremal definitions, proposed construction and nonoptimality theorem are reused from [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos441.lean). That source credits Yong-Gao Chen and Li-Xia Dai for the informal proof, and Codex and GPT-5.6 Sol for formalization. Its Apache-2.0 license and exact provenance are preserved in [External/PROVENANCE.md](MerLeanExperiment/External/PROVENANCE.md) and [External/plby-LICENSE](MerLeanExperiment/External/plby-LICENSE). Only import compatibility changes were made to the reused Lean source. We do not claim authorship of that earlier contribution.

The contribution sought is the new formalization of Chen's sharp asymptotic and its integration with the credited construction result, prepared with OpenAI Codex assistance. No new mathematical discovery is claimed.

## Reproduce and audit

Install the pinned Lean toolchain through elan, then run from this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The cache command is optional. [lean-toolchain](lean-toolchain) pins Lean `v4.34.0-rc1`; [lakefile.toml](lakefile.toml) pins Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`; [lake-manifest.json](lake-manifest.json) pins transitive dependencies. The package contains source files, not compiled caches or machine-specific dependency paths.

[Audit.lean](Audit.lean) type-checks the exact two-conjunct statement and prints the root and final supporting theorem axiom sets. The complete root depends exactly on `propext`, `Classical.choice`, and `Quot.sound`. The proof has no `sorry`, custom axioms, assumed target, added original conditions or native-evaluation proof shortcuts. [verification.txt](verification.txt) records the exported package's build and audit; [SHA256SUMS](SHA256SUMS) binds its source and configuration files.

Local checks used pinned cached upstream dependencies on arm64 macOS. They are not an offline independent-checker verdict. As of 2026-09-16, the Erdős 441 page says “Formalised statement? No”, and no organizer-provided full Lean challenge was found in the checked official repositories. **Official comparator: NOT RUN.** The exact theorem and definitions are provided for an authoritative statement comparison when that target is available.

The [prize rules](https://www.hejustinsun.com/prize/rules), version 1.0 effective 2026-09-16, require designated verification including isolated axiom audits and independent checker review. They do not explicitly name the three standard axioms above as accepted. Their use is disclosed for that review; no official acceptance, safe-version designation, archival attestation or comparator pass is asserted.

## Submission status and licensing

The catalog currently marks JSP-000360 “Eligible to claim: No”. Please assess intake and eligibility under the applicable rules; this submission does not change that status or claim award entitlement. The official issue/PR scan performed on 2026-09-16 found no prior submission matching this exact problem; this is a search observation, not an assertion of priority.

This is a self-submission with a direct interest in the review outcome. Formalizer identity confirmation is pending; recipient placeholder: `RECIPIENT-jsp-000360-cyr-A`. No solver nomination, payment status or award tier is asserted. The `submissions/` path is proposed intake packaging and does not introduce an official record schema.

New Lean source is offered under the [MIT license](LICENSE). This README and new provenance documentation are offered under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Third-party source retains its original license and attribution.

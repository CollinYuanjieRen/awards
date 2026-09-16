# Reused Erdős 441 formalization

- Repository: https://github.com/plby/lean-proofs
- Pinned commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`
- Original path: `src/latest/ErdosProblems/Erdos441.lean`
- Original SHA-256: `54e41a155fcac23de29bacf70425428fce33bdbb8a898da3c4ae9d44b19e4d7c`
- Exported SHA-256: `cc597b6cb3cd455aac46bd276524741fcb1eccca6db8a8e2252a9a6effccaaeb`
- License: Apache-2.0. The upstream notice is preserved verbatim in [plby-LICENSE](plby-LICENSE); the full license text is included in [Apache-2.0.txt](Apache-2.0.txt).

The upstream file credits Yong-Gao Chen and Li-Xia Dai for the informal proof, and Codex and GPT-5.6 Sol for formalization. The definitions and proved nonoptimality result are reused with that attribution. This earlier source does not prove the sharp asymptotic supplied by the new files in this package.

The compatibility patch replaces its single `import Mathlib` with explicit Mathlib imports supported by the pinned 4.34.0-rc1 environment. The original top-of-file toolchain comment is retained as historical upstream metadata; the actual package toolchain is fixed by `../../lean-toolchain`. No theorem body or mathematical definition in this file was changed.

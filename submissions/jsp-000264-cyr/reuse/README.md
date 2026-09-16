# Verified reused faces of Erdős Problem 318

This bundle records kernel verification of the two previously formalized faces of
Erdős Problem 318:

```lean
Erdos318.erdos_318.parts.i :
  ∃ A : Set ℕ, A.HasPosDensity ∧ ¬ Erdos318.P₁ A

Erdos318.erdos_318.variants.infinite_AP :
  ∀ {A : Set ℕ}, _root_.Set.IsAPOfLength A ⊤ → Erdos318.P₁ A
```

It does not contain or claim the squares-excluding-one proof. That third face is
formalized separately.

## Attribution and source pins

The informal problem is due to Paul Erdős. The statement and canonical utility
definitions are from the Formal Conjectures authors under the Apache License 2.0.
The reused formal proofs are credited by their source to Codex and GPT-5.6 Sol.

- plby source: <https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e>
- Formal Conjectures statement: <https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/318.lean>
- Lean: `leanprover/lean4:v4.33.0`
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`

The original 12-file proof closure is not republished here. `sources.sha256`
identifies every source byte-for-byte, and `scripts/prepare.sh` fetches only those
files from the pinned plby commit and verifies each hash before creating the adapter.
The complete resolved Lake manifest is included.

## Canonical interface adapter

The plby AP theorem used `Erdos318.Set.IsAPOfLength`, an abbreviation of
`Erdos253.Set.IsAPOfLength`. The official statement uses root
`Set.IsAPOfLength`. Their definition bodies are identical after unfolding.

The adapter performs only these source changes:

1. It changes the four occurrences of
   `erdos_318.variants.infinite_AP` to
   `erdos_318.variants.infinite_AP_reused` in a generated copy of the pinned
   source. These are the declaration, the two internal uses, and its audit command.
2. It adds the two official AP definition bodies under their canonical root names.
3. It restores the original theorem name with the official argument type.

The exact rename is recorded in `patches/Erdos318-infinite-AP-rename.diff`.
The compiled adapter term is:

```lean
fun {A} hA =>
  Erdos318.erdos_318.variants.infinite_AP_reused (id hA)
```

Thus the conversion is definitional and adds no premise.
[`definition-comparison.txt`](evidence/definition-comparison.txt) records normalized
equality with the pinned official source for `P₁`,
`partialDensity`, `HasDensity`, `HasPosDensity`, `IsAPOfLengthWith`, and
`IsAPOfLength`. The density theorem keeps the proof's concrete odd-numbers-plus-2
witness and its density `1 / 2`; no density notion was weakened.

## Reproduction

Prepare a new source directory:

```text
./scripts/prepare.sh /path/to/new/erdos318-verification
```

With Lean 4.33.0 and the resolved dependencies from `lake-manifest.json`
available, run:

```text
cd /path/to/new/erdos318-verification
lake --no-cache build ErdosProblems.Erdos318
lake --no-cache build ErdosProblems.Erdos318Canonical
```

`prepare.sh` never invokes Lake, changes dependency pins, or downloads more than
the 12 listed proof sources. Dependency provisioning is intentionally separate.

## Recorded evidence

- `evidence/exact-build.log`: exact pinned source build and embedded axiom audit.
- `evidence/canonical-build.log`: canonical adapter build, printed theorem types,
  definitions, proof term, and axiom audit.
- `evidence/definition-comparison.txt`: official/reused definition comparison.
- `evidence/source-scope-audit.log`: forbidden-token and closure audit.

Both public face declarations depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, or `native_decide`
occurs in the 12-file source closure. The logs contain no machine-specific paths.
`evidence/SHA256SUMS` binds the evidence bytes, while `SHA256SUMS` binds the
publication bundle.

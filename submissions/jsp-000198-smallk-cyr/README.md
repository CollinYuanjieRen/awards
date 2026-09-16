# JSP-000198: the empty-polygon thresholds h(3) = 3, h(4) = 5 and h(5) = 10

This package submits a Lean formalization for intake and eligibility review. It addresses the finite-threshold part of [JSP-000198](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000198), "How many points in general position force an empty convex polygon of a prescribed size?". Writing h(k) for the least n such that every n points in general position contain an empty convex k-gon, the classical answers are h(3) = 3, h(4) = 5 and h(5) = 10 (Harborth 1978, catalog reference [Ha78]). This package proves all three exact values. It does not treat the empty hexagon (h(6) ≤ 30, [Ni07], [Ge08], [HeSc24]) and it does not treat Horton's construction for k ≥ 7 ([Ho83]), which is the subject of the separate pull request #73 on the Horton component.

## Statement and proof

[EmptyPentagon/SmallHoles.lean](EmptyPentagon/SmallHoles.lean) proves the three roots

```lean
theorem forces_empty_triangle_iff (n : ℕ) : ForcesEmptyKGon 3 n ↔ 3 ≤ n
theorem forces_empty_quadrilateral_iff (n : ℕ) : ForcesEmptyKGon 4 n ↔ 5 ≤ n
theorem forces_empty_pentagon_iff (n : ℕ) : ForcesEmptyKGon 5 n ↔ 10 ≤ n
```

where ([EmptyPentagon/Definitions.lean](EmptyPentagon/Definitions.lean), [EmptyPentagon/Forces.lean](EmptyPentagon/Forces.lean))

```lean
abbrev Point := ℝ × ℝ
def orient (a b c : Point) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)
def GeneralPosition (S : Finset Point) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → orient a b c ≠ 0
def EmptyConvexPolygon (S V : Finset Point) : Prop :=
  V ⊆ S ∧ ConvexIndependent ℝ (fun v : (V : Set Point) => (v : Point)) ∧
    ∀ p ∈ S, p ∉ V → p ∉ interior (convexHull ℝ (V : Set Point))
def ForcesEmptyKGon (k n : ℕ) : Prop :=
  ∀ S : Finset Point, S.card = n → GeneralPosition S →
    ∃ V : Finset Point, V.card = k ∧ EmptyConvexPolygon S V
```

`orient a b c` is twice the signed area of the triangle `a b c`, so `GeneralPosition S` says that no three distinct points of `S` are collinear. `EmptyConvexPolygon S V` says that `V` is a subset of `S` whose points are in convex position (Mathlib's `ConvexIndependent`: no point of `V` lies in the convex hull of the others) and that no other point of `S` lies in the topological interior of the convex hull of `V`; for points in general position this is the usual notion of an empty convex `k`-gon. `ForcesEmptyKGon k n` says that every set of exactly `n` points in general position contains an empty convex `k`-gon, so each root theorem is the exact value of the threshold: it holds for every `n` at or above the value and fails for every smaller `n`. No hypothesis beyond "n points in general position in the plane" is used, and each `↔` is proved in both directions. [Audit.lean](Audit.lean) restates the pentagon threshold with every auxiliary predicate unfolded.

The proof is organised as follows (all files in [EmptyPentagon/](EmptyPentagon/)).

1. **Monotonicity and small witnesses.** `Parabola.lean` provides sets of any size in general position (points on a parabola), which shows that the empty `k`-gon condition is monotone in `n` (`Monotone.lean`) and that `h(k) ≥ k`. `Triangle.lean` proves h(3) = 3. `FourWitness.lean` gives four points with no empty convex quadrilateral, `NineWitness.lean` gives nine integer points with no empty convex pentagon (Harborth's lower-bound configuration, checked by kernel evaluation over all five-element subsets), and `Quadrilateral.lean` proves that five points always contain an empty convex quadrilateral.
2. **Orientation tools.** `Certificate.lean`, `Interp.lean`, `TriangleInterior.lean`, `ExtremeHull.lean`, `Hull.lean` and `Comparators.lean` connect the sign of `orient` with membership in convex hulls, interiors and half-planes. `Identities.lean` proves the four- and five-point orientation identities (cofactor and Grassmann–Plücker relations), and `Enumeration.lean` and `Signs.lean` turn them into a kernel-checked decision procedure for sign implications among five points: a claimed implication between orientation signs is verified by `decide` over all sign vectors consistent with those identities and then transported to real points.
3. **Five points in convex position among nine.** `ES5.lean` (with `CyclicLabel.lean`, `Label4.lean`, `Chord.lean`, `Beam.lean`, `Cover332.lean`, `Cover342.lean`, `Case332.lean`, `Case342.lean`, `FourOuter.lean`, `Quad.lean`) proves that every nine points in general position contain five points in convex position (the Erdős–Szekeres number N(5) = 9, first proved by Kalbfleisch, Kalbfleisch and Stanton in 1970), following Bonnice's 1974 proof by convex-hull layers.
4. **Harborth's argument.** `Descent.lean` shows that a convex pentagon of `S` can be replaced by one with at most one point of `S` inside it. `Core.lean` splits on the number of interior points: with none, the pentagon itself is empty (`Pentagon.lean`), and with exactly one, `Wedge.lean`, `Ear.lean`, `Front.lean`, `Front2.lean`, `Second.lean`, `Third.lean`, `Two.lean` and `Final.lean` supply Harborth's case analysis on how the four remaining points are distributed among the regions around the pentagon; `Harborth.lean` derives `forcesEmptyKGon_five_ten`. Several places where the 1978 text is terse or where its stated choices had to be adjusted are recorded in the campaign notes; every case as formalized was first checked numerically and is then proved in Lean from the orientation signs alone.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) restates the three root statements as typed `example`s closed by the theorems and prints the axioms of the roots and of the main components. Every printed declaration depends exactly on `propext`, `Classical.choice` and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide` or custom trust extension occurs anywhere in the dependency cone (the finite checks in `NineWitness.lean` and `Signs.lean` use `decide +kernel`, which is kernel evaluation, not compiled code). [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated verifiers and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The mathematical results are classical: h(3) = 3 and h(4) = 5 are elementary (the latter refines Esther Klein's observation that five points in general position contain a convex quadrilateral), the convex-pentagon bound N(5) = 9 is due to Kalbfleisch, Kalbfleisch and Stanton (1970) with the proof used here following Bonnice (Amer. Math. Monthly 81 (1974)), and h(5) = 10 with the nine-point lower-bound configuration is due to Harborth (Elem. Math. 33 (1978), 116–118). The Lean formalization, including the orientation-sign decision procedure and the reconstruction and correction of the case analysis, was prepared with Claude Code (Claude Fable 5.1 planning, Claude Opus implementation) assistance. The contribution sought is a formalization of these exact finite thresholds; no new mathematical discovery, first-formalization priority or entitlement to an award is claimed, and this package does not claim the empty-hexagon or Horton parts of the catalog entry.

Proposed formalizer: `RECIPIENT-jsp-000198-smallk-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).

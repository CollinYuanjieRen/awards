# Disk discrepancy bounds — JSP-000822 / Erdős 989

This is a Lean formalization of the absolute, running-radius disk discrepancy bounds proved by J. Beck, together with their qualitative unboundedness consequence. The mathematical result is attributed to Beck; the Lean proof in this directory is written for this submission and imports only the pinned Mathlib dependency.

The unconditional root is:

```lean
theorem disk_discrepancy : DiskDiscrepancy.CompleteTarget
```

`CompleteTarget` is defined in [Target.lean](MerLeanExperiment/Target.lean). The objects and counting conventions are in [DiskModel.lean](MerLeanExperiment/DiskModel.lean).

## Exact statement

The plane is `EuclideanSpace ℝ (Fin 2)`. For a point set `S`, center `x` and radius `r`, discrepancy is the absolute difference between the number of points of `S` in the **closed** Euclidean disk and its area `πr²`. An admissible set is infinite and locally finite; equivalence with finiteness on every compact set is proved.

The root proves all three statements:

1. There are universal `c > 0` and `R₀ ≥ 2` such that, for every `R ≥ R₀` and every admissible `S`, some center and some radius `0 < r ≤ R` have discrepancy at least `c√R`.
2. There are universal `C > 0` and `R₀ ≥ 2` such that, for every `R ≥ R₀`, there is one admissible `S` for which every center and every `0 < r ≤ R` have discrepancy at most `C√(R log R)`. The proof supplies `C = 1000` and `R₀ = 4`. The set may depend on `R`.
3. For every set `S`, there is no finite bound on the discrepancy of all closed disks while all their intersections with `S` are finite. This covers finite sets separately and does not hide infinite cardinalities behind total `ncard`.

The lower statement chooses a radius up to `R`; it does not prescribe that radius to equal `R`. The upper statement chooses one set for each outer scale, not one set simultaneously for all scales. The logarithmic gap is retained.

## Sources and wording

- J. Beck, *Irregularities of distribution. I*, Acta Mathematica 159 (1987), 1–49: Theorem 2A and its upper-bound counterpart, applied to disks. [Primary paper](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6400-11511_2006_Article_BF02392553.pdf).
- P. Erdős, *On some problems in number theory and combinatorics*, 1964, printed page 54. [Primary paper](https://www.renyi.hu/~p_erdos/1964-24.pdf).
- [Official catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000822).

The 1964 displayed discrepancy formula omits absolute-value bars and discusses disk interiors and the running maximum. The theorem here explicitly uses Beck's absolute, closed-disk interpretation. It does not assert an unproved open/closed-disk equivalence or the stronger fixed-radius/global-set quantifiers appearing in some summaries.

## Proof organization

The lower bound derives the actual circular Fourier integral, its differential equation and a radial energy estimate. A compact positive Fourier weight gives a finite-point spectral lower bound. The proof identifies the Fourier transform of the actual disk-count-minus-area cutoff, proves its L1/L2 and Plancherel requirements, and compares the averaged spectral bound with the interior and boundary-strip spatial estimates. Finite disk packing supplies the necessary point count; the contradiction has no density or separation assumption on `S`.

The upper bound constructs an actual infinite periodic jitter of the integer lattice. It proves injectivity, local finiteness and periodicity, bounds the number of boundary cells by their disjoint areas, and proves the midpoint quadrature estimate through scaled-cell geometry. The expected count is identified with that quadrature by a finite bijection. Product-coordinate independence and the boundary-centered count identity yield a Hoeffding tail. One finite union bound chooses a single sample controlling a common center/radius grid; proved interpolation and periodicity extend its bound to every center and every positive radius up to `R`.

## Reproduction and trust

Pinned versions:

- Lean `v4.34.0-rc1`.
- Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.
- Transitive dependency commits are recorded in `lake-manifest.json`.

From this directory, with the pinned toolchain installed:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The cache command fetches compiled pinned dependencies; all submission sources are built by `lake build`. `source-hashes.json` records the submitted Lean source hashes. The root and each of its three faces report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard mathematical foundations. No custom mathematical axiom, `sorry`, `admit`, native-evaluation proof, or conclusion-as-hypothesis is used in the imported proof. The full root has no hypothesis or instance binder. See [verification.txt](verification.txt) for the checked artifact and limits of local verification.

## Official review status

This contribution supplies a proof for review, not an announced award or a completed official verification record. At the checked official repository revision above, no issued JSP-000822 Lean statement or comparator was found; comparator execution is **NOT-RUN**. No explicit prize allowlist for the three standard foundational axioms was found. The catalog's current “Eligible to claim: No” flag is preserved.

Organizer-issued statements, authorized signatories, two independent current checker records and the specified isolated archival verification remain organizer review requirements. Local compilation and independent proof review do not assert those administrative attestations or prize acceptance. No candidate or award record is created by this proof contribution.

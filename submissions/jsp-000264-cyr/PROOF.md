# Proof structure and statement alignment

The primary mathematical source is Daniel Larsen's square-specific construction, pinned in the README. This note explains the checked implementation; it is not a substitute for the Lean proof.

## Endpoint

`ReciprocalSquares.square_partition` takes only a set `X : Set ℕ` and one square denominator greater than one in each color. It returns nonempty finite subsets of the respective colors whose rational reciprocal sums are equal. Elements of `X` outside this domain do not matter.

`Erdos318.erdos_318.parts.ii` retains the canonical `P₁` definition: a function on all natural numbers has range in `{1,-1}` and is nonconstant on the square domain with zero and one removed. The two witnesses follow from those nonconstancy conditions. The partition theorem gives two disjoint finite sets; exact casting of the rational identity into the reals makes their union a nonempty signed zero sum. No integer, prime or limiting statement is used as an added endpoint assumption.

## Construction and estimates

1. Choose fixed color witnesses. They determine a positive residual margin and uniform Bernoulli parameters before any large scale is selected.
2. Put `N=M^10`. Construct square denominators from an `N`-smooth root times a subset product of distinct primes between `N` and `N^3`. Every denominator is an actual square. Remove exactly the small smooth-square prefix; erase one from the initial mass.
3. A finite greedy argument chooses part of that prefix. Its remaining target `r` lies strictly between zero and the retained reciprocal mass `W`, with uniform bounds `c*r<W≤A*r`. All denominators, including the prefix, divide the least common multiple of the retained set, so `m*r` is a positive integer.
4. Use Bernoulli probability `p=r/W`. Centered Fourier inversion counts representations of this target. Explicit small-frequency positivity and residue-energy lower bounds handle the entire centered frequency range. The bottom, middle and high bounds are respectively `M/64`, `M^9/1024` and `C*M^51`, where `C=1/(4*20!*16^40)>0`.
5. The high-frequency argument splits prime subsets into those with no nearby multiple and a dense coherent family. In the latter case, a missing construction factor gives separated residues. The proof checks every smooth and large-prime factor needed for the modulus; it does not silently replace the modulus by just the large-prime part.
6. The bound `log m≤120*M^31`, a retained-cardinality estimate and polynomial-versus-exponential decay allow one integer `M` meeting all inequalities. The real Fourier sum is at least one half, whereas each subset atom has weight strictly less than `1/(2*m)`. Thus two distinct subsets represent `r`.
7. Add the same disjoint greedy prefix to both representations. At least one differs from the original color subset. Cancel their intersection using strictly positive reciprocal weights, yielding the required nonempty sets in opposite colors.

These are proved lemmas with their hypotheses discharged in `SquarePartition.lean`. The final theorem does not assume a Fourier estimate, representation principle, prime-count theorem, or literature result.

## Trust and review

The final endpoint's recursively reported axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. There are no solution declarations using `sorry`, `admit`, custom axioms or `native_decide`. Standard Mathlib results remain within that same transitive axiom audit.

Independent source reviews checked the frozen original statement, finite greedy construction, denominator coverage, all frequency boundaries, uniform parameter choice, exact final cancellation and canonical signed adapter. Build and axiom output is in `verification.txt`. Native comparator evidence, including its platform and reference-port qualifications, is recorded separately when complete. A comparator checks agreement with its trusted Lean reference; the natural-language scope review remains a separate obligation.

# JSP-000992 / Erdős Problem #1187 — scoped component: the second question has answer "no"

**Scope (honest).** Erdős asked (for `k ≥ 3`) whether every finite colouring of the integers
contains (i) a monochromatic `k`-term arithmetic progression of primes and (ii) a monochromatic
`k`-term arithmetic progression whose common difference is a prime.  Question (i) is answered
affirmatively by the Green–Tao theorem and is **not** formalized here.  This package formalizes
the remark recorded on the problem page (erdosproblems.com/1187) answering question (ii): *"The
answer to the second question is trivially no: colouring the integers by their residue modulo 4
creates a colouring in which there is not even any monochromatic pair of integers whose
difference is a prime.  Alternatively, one can just use 2 colours and avoid any 3-term
progressions whose difference is a prime by colouring 0,1 (mod 4) red and 2,3 (mod 4) blue."*

**Definitions** (`Erdos1187ModFour/Main.lean`, namespace `Erdos1187`; there is no
formal-conjectures rendering of this problem, so the definitions are ours; colourings are of `ℤ`,
the page's "the integers"):

- `colourMod4 (n : ℤ) : ZMod 4 := (n : ZMod 4)`;
- `colourTwo (n : ℤ) : Bool := decide (n % 4 < 2)`.

**Statements.**  `colourMod4_ne_add_prime (a : ℤ) (p : ℕ) (hp : p.Prime) : colourMod4 a ≠
colourMod4 (a + p)`; `no_mono_ap_colourMod4 (k) (hk : 2 ≤ k) (a) (p) (hp) : ¬ ∀ i < k,
colourMod4 (a + i * p) = colourMod4 a`; `colourTwo_no_three_ap (a) (p) (hp) : ¬ (colourTwo a =
colourTwo (a + p) ∧ colourTwo (a + p) = colourTwo (a + 2 * p))`; graded root
`erdos_1187_second_question_closed : (∃ c : ℤ → Fin 4, ∀ (a : ℤ) (p : ℕ), p.Prime → c a ≠ c (a + p))
∧ (∃ c : ℤ → Bool, ∀ (a : ℤ) (p : ℕ), p.Prime → ¬ (c a = c (a + p) ∧ c (a + p) = c (a + 2 * p)))`.

**Proof idea.**  `4 ∤ p` for every prime `p`, so `a` and `a + p` differ modulo `4`.  For the
two-colouring, `p = 2` gives residues `r, r + 2, r` and `p` odd gives residues `r, r + odd, r + 2`;
in both cases the first and third (or first and second) terms lie in different halves of `ℤ/4`.

**Verification.** Lean `4.34.0-rc1`, Mathlib `1fe0a51a`; `lake build` completes with zero
warnings; `Audit.lean` reports axioms exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe` or `set_option`.  See `verification.txt`.
Before submission the package passed MerLean Heavy's research-grade audit (target/goal contracts,
kernel evidence, definition independence, two independent audits).

**Files.** `Erdos1187ModFour/Main.lean`, `Erdos1187ModFour.lean` (library root), `Audit.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `verification.txt`, this README.

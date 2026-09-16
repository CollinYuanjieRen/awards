import Mathlib

/-!
# Real subdivisions and uniform distribution

These definitions follow Schmidt, *Disproof of some conjectures on
Diophantine approximations*, printed page 137, equations (1)--(5).
The subdivision points are real numbers. The positive integer subdivision
theorem in plby's Erdos492 is a different, valid result.
-/

open Classical Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos492Real

noncomputable section

/-- Consecutive members of an ordered set of real endpoints. -/
def Consecutive (S : Set ℝ) (a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ c ∈ S, a < c → b ≤ c

/-- The initial proportion `lam` of every interval between consecutive endpoints. -/
def lowerRegion (S : Set ℝ) (lam : ℝ) : Set ℝ :=
  {x | ∃ a b, Consecutive S a b ∧ a ≤ x ∧ x < a + lam * (b - a)}

def divisionSign (S : Set ℝ) (x : ℝ) : ℝ :=
  if x ∈ lowerRegion S (1 / 2) then 1 else -1

/-- A finite subdivision of the unit interval, with its actual endpoints. -/
structure FiniteDivision where
  points : Finset ℝ
  zero_mem : 0 ∈ points
  one_mem : 1 ∈ points
  mem_unit : ∀ x ∈ points, x ∈ Icc (0 : ℝ) 1

def FiniteDivision.Fine (P : FiniteDivision) (ε : ℝ) : Prop :=
  ∀ a b, Consecutive (P.points : Set ℝ) a b → b - a < ε

/-- The finite, quantitative lemma used in Schmidt's construction.
This is an interface to be proved, not an assumption in the final theorem. -/
def FiniteDivision.DilationInvariant (P : FiniteDivision) (N : ℕ) (ε : ℝ) : Prop :=
  ∃ E : Set ℝ, MeasurableSet E ∧ volume E < ENNReal.ofReal ε ∧
    ∀ x : ℝ, 0 ≤ x → x < 1 → x ∉ E →
      ∀ m : ℕ, 1 ≤ m → m ≤ N → (m : ℝ) * x < 1 →
        divisionSign (P.points : Set ℝ) ((m : ℝ) * x) =
          divisionSign (P.points : Set ℝ) x

def FiniteSubdivisionLemma : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ P : FiniteDivision, P.Fine ε ∧ P.DilationInvariant N ε

/-- Schmidt's `M(lam)`, using the sequence of real endpoints directly. -/
def sequenceRegion (a : ℕ → ℝ) (lam : ℝ) : Set ℝ :=
  {x | ∃ n : ℕ, a n ≤ x ∧ x < a n + lam * (a (n + 1) - a n)}

def visitFrequency (a : ℕ → ℝ) (α lam : ℝ) (N : ℕ) : ℝ :=
  (((Finset.Icc 1 N).filter (fun n : ℕ => (n : ℝ) * α ∈ sequenceRegion a lam)).card : ℝ) / N

def UniformlyDistributed (a : ℕ → ℝ) (α : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
    Tendsto (visitFrequency a α lam) atTop (𝓝 lam)

def signedMean (a : ℕ → ℝ) (α : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N,
    if (n : ℝ) * α ∈ sequenceRegion a (1 / 2) then (1 : ℝ) else -1) / N

/-- The complete original real-subdivision counterexample; no extra premise. -/
def SchmidtStatement : Prop :=
  ∃ a : ℕ → ℝ, a 0 = 0 ∧ StrictMono a ∧ Tendsto a atTop atTop ∧
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) ∧
    ∀ᵐ α : ℝ, 0 < α → ¬ UniformlyDistributed a α

end

end Erdos492Real

namespace Erdos492Real

/-- Independently reviewed reference proposition; no proof is assumed. -/
def expectedStatement : Prop := SchmidtStatement

end Erdos492Real

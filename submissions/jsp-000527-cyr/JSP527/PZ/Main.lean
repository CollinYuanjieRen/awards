import JSP527.PZ.Extraction

/-!
# Erdős Problem 651: `f₃(n) ≤ 2^{o(n)}` (Pohoata–Zakharov 2022, Theorem 1.1)

The extraction theorem `Erdos651.pohoataZakharov_forces_eventually` supplies the envelope
certificate of the assembly (scale `pzSourceScale`, constant `77`); the bridge lemmas of plby's
`Erdos651` module turn it into the point-set statement, the well-definedness of the
Erdős–Szekeres numbers, the subexponential upper bound and the refutation of Erdős's
conjectured exponential lower bound.
-/

open Filter

namespace PohoataZakharov

/-- The envelope certificate of the assembly, discharged by the extraction theorem. -/
noncomputable def certificate : Erdos651.PohoataZakharovEnvelopeCertificate where
  scale := Erdos651.pzSourceScale
  constant := 77
  scale_tendsto := Erdos651.pzSourceScale_tendsto_atTop
  forces_eventually := Erdos651.pohoataZakharov_forces_eventually

/-- Pohoata–Zakharov, Theorem 1.1 (point-set form). -/
theorem theorem_one_one : Erdos651.PohoataZakharovTheoremOneOne :=
  certificate.theoremOneOne

/-- The Erdős–Szekeres number in dimension three exists for every `n`. -/
theorem hasErdosSzekeresNumber_three (n : ℕ) : Erdos651.HasErdosSzekeresNumber 3 n :=
  Erdos651.hasErdosSzekeresNumber_three_of_theoremOneOne theorem_one_one n

/-- `f₃(n) ≤ 2 ^ (o(n))`: the negative answer to Erdős Problem 651. -/
theorem erdos_651_subexponential :
    Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber 3) :=
  Erdos651.pohoataZakharovTheoremOneOne_imp_subexponential theorem_one_one

/-- Erdős's conjectured exponential lower bound `f₃(n) > (1 + c)^n` fails. -/
theorem erdos_651_disproved : ¬ Erdos651.Erdos651Claim :=
  Erdos651.erdos_651_of_pohoata_zakharov erdos_651_subexponential

/-- Premise-free form of the subexponential bound, indexed by `k` with `ε = 1 / (k + 1)`:
for every `k`, eventually `f₃(n) ≤ 2 ^ (n / (k + 1))`. -/
theorem erdos_651_subexponential_inv (k : ℕ) : ∀ᶠ n : ℕ in atTop,
    (Erdos651.erdosSzekeresNumber 3 n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  filter_upwards [erdos_651_subexponential (1 / ((k : ℝ) + 1)) hk] with n hn
  have h : (1 / ((k : ℝ) + 1)) * (n : ℝ) = (n : ℝ) / ((k : ℝ) + 1) := by ring
  rw [h] at hn
  exact hn

end PohoataZakharov

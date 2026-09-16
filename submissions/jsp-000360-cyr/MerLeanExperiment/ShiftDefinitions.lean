import MerLeanExperiment.FactorialLinear

namespace Erdos441

def shiftedPoint {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) (i : Fin K) : ℤ :=
  (M.factorial : ℤ) * ell i + r i

def shiftFactor {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) (i j : Fin K) : ℤ :=
  ((M.factorial : ℤ) / (r j - r i)) * (ell j - ell i) + 1

def shiftPairs (K : ℕ) : Finset (Fin K × Fin K) :=
  Finset.univ.filter fun ij => ij.1 < ij.2

def shiftProduct {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) : ℤ :=
  ∏ ij ∈ shiftPairs K, shiftFactor M r ell ij.1 ij.2

def shiftProductNat {K : ℕ} (M : ℕ) (r ell : Fin K → ℤ) : ℕ :=
  (shiftProduct M r ell).natAbs

end Erdos441

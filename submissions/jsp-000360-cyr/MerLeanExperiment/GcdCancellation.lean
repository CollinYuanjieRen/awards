import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Erdos441

theorem gcd_dvd_difference_factor (U V d F : ℤ) (D : ℕ)
    (hdiff : V - U = d * F) (hFD : F.natAbs ∣ D)
    (hcop : Nat.Coprime U.natAbs D) :
    Nat.gcd U.natAbs V.natAbs ∣ d.natAbs := by
  let g := Nat.gcd U.natAbs V.natAbs
  have hgU : g ∣ U.natAbs := Nat.gcd_dvd_left _ _
  have hgV : g ∣ V.natAbs := Nat.gcd_dvd_right _ _
  have hU : (g : ℤ) ∣ U := Int.natCast_dvd.mpr hgU
  have hV : (g : ℤ) ∣ V := Int.natCast_dvd.mpr hgV
  have hprod : (g : ℤ) ∣ d * F := hdiff ▸ dvd_sub hV hU
  have hprodNat : g ∣ d.natAbs * F.natAbs := by
    simpa only [Int.natAbs_mul] using Int.natCast_dvd.mp hprod
  have hcopg : Nat.Coprime g F.natAbs := hcop.of_dvd hgU hFD
  exact hcopg.dvd_mul_right.mp hprodNat

theorem two_mul_le_of_odd_dvd_even (g d : ℕ) (hd : 0 < d)
    (hgodd : Odd g) (hdeven : Even d) (hgd : g ∣ d) : 2 * g ≤ d := by
  exact Nat.le_of_dvd hd
    (hgodd.coprime_two_left.mul_dvd_of_dvd_of_dvd hdeven.two_dvd hgd)

end Erdos441

#print axioms Erdos441.gcd_dvd_difference_factor
#print axioms Erdos441.two_mul_le_of_odd_dvd_even

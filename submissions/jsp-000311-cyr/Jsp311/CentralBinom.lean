import Mathlib

namespace CentralBinom105

theorem centralBinom_ten_eq : Nat.centralBinom 10 = 184756 := by
  rfl

theorem centralBinom_ten_coprime_105 : Nat.Coprime (Nat.centralBinom 10) 105 := by
  rw [Nat.Coprime, centralBinom_ten_eq]
  decide

theorem exists_centralBinom_coprime_105 : ∃ n, 0 < n ∧ Nat.Coprime (Nat.centralBinom n) 105 :=
  ⟨10, by decide, centralBinom_ten_coprime_105⟩

#print axioms CentralBinom105.centralBinom_ten_coprime_105
#print axioms CentralBinom105.exists_centralBinom_coprime_105

end CentralBinom105

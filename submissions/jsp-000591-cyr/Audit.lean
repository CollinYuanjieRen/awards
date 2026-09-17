import Erdos723BruckRyser

open Configuration

#print axioms erdos_723_six_fourteen_closed
#print axioms erdos_723_bruck_ryser_rules_out_six_fourteen

/-- Erdős #723: `6` and `14` are `≡ 2 (mod 4)` and not sums of two squares. -/
example : (6 ≡ 2 [MOD 4] ∧ ¬ ∃ a b : ℕ, 6 = a ^ 2 + b ^ 2) ∧
    (14 ≡ 2 [MOD 4] ∧ ¬ ∃ a b : ℕ, 14 = a ^ 2 + b ^ 2) := erdos_723_six_fourteen_closed

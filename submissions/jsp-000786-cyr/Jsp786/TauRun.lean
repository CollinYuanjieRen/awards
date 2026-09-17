import Mathlib

namespace TauRun

/-- Number of divisors. -/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/-- The six consecutive integers 76..81 have pairwise distinct divisor counts. -/
theorem tau_run_76 : ((List.range 6).map (fun i => tau (76 + i))).Nodup := by
  show ([tau 76, tau 77, tau 78, tau 79, tau 80, tau 81] : List ℕ).Nodup
  decide

/-- There is a run of 6 consecutive integers with pairwise distinct divisor counts. -/
theorem exists_distinct_tau_run_6 :
    ∃ m, ((List.range 6).map (fun i => tau (m + i))).Nodup :=
  ⟨76, tau_run_76⟩

#print axioms TauRun.tau_run_76
#print axioms TauRun.exists_distinct_tau_run_6

end TauRun

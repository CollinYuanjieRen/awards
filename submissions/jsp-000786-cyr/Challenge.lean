import Mathlib
/-! Mathlib-only comparator for JSP-000786 (distinct-tau run). NOT imported by the build. -/
namespace TauRunChallenge

def tau (n : ℕ) : ℕ := (Nat.divisors n).card

theorem tau_run_76 : ((List.range 6).map (fun i => tau (76 + i))).Nodup := by sorry

theorem exists_distinct_tau_run_6 :
    ∃ m, ((List.range 6).map (fun i => tau (m + i))).Nodup := by sorry

end TauRunChallenge

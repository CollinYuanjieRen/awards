import Erdos387Proof.TentFourier

/-! A common integer Fourier window for varying moduli. The explicit
`2*H<q` condition guarantees no repeated or missing canonical frequency. -/

namespace Erdos387Proof.IntegerFourierWindow

open TentFourier
open scoped BigOperators

noncomputable def window (H : ℕ) : Finset ℤ := Finset.Icc (-(H : ℤ)) H

theorem valMinAbs_intCast_of_mem {H q : ℕ} [NeZero q]
    (hHq : 2 * H < q) {h : ℤ} (hh : h ∈ window H) :
    (h : ZMod q).valMinAbs = h := by
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_⟩
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hh
  have hbound : (2 : ℤ) * H < q := by exact_mod_cast hHq
  constructor <;> omega

/-- Exact reindexing to a single integer interval. -/
theorem sum_modular_window_eq_integer {H q : ℕ} [NeZero q]
    (hHq : 2 * H < q) (F : ZMod q → ℂ) :
    (∑ h : ZMod q with h.valMinAbs.natAbs ≤ H, F h) =
      ∑ h ∈ window H, F (h : ZMod q) := by
  classical
  symm
  apply Finset.sum_bij (fun (h : ℤ) _ => (h : ZMod q))
  · intro h hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [valMinAbs_intCast_of_mem hHq hh]
    have habs : |h| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hh)
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  · intro a ha b hb hab
    have hv := congrArg ZMod.valMinAbs hab
    simpa only [valMinAbs_intCast_of_mem hHq ha,
      valMinAbs_intCast_of_mem hHq hb] using hv
  · intro h hh
    have hb := (Finset.mem_filter.mp hh).2
    refine ⟨h.valMinAbs, ?_, ZMod.coe_valMinAbs h⟩
    apply Finset.mem_Icc.mpr
    have habs : |h.valMinAbs| ≤ (H : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hb
    exact abs_le.mp habs
  · intro h hh
    rfl

/-- Uniform truncation with the same signed integer frequencies for every
modulus satisfying the displayed size condition. -/
theorem norm_progressionMass_sub_integerSum_le {X H q : ℕ} [NeZero q]
    (hX : 0 < X) (hH : 0 < H) (hHq : 2 * H < q) (a : ZMod q) :
    ‖(progressionMass X q a : ℂ) -
      ∑ h ∈ window H, ZMod.stdAddChar (-(h : ZMod q) * a) *
        coefficient X q (h : ZMod q)‖ ≤ (q : ℝ) / (2 * X * H) := by
  rw [← sum_modular_window_eq_integer hHq
    (fun h => ZMod.stdAddChar (-h * a) * coefficient X q h)]
  exact norm_progressionMass_sub_partialSum_le hX hH a

end Erdos387Proof.IntegerFourierWindow

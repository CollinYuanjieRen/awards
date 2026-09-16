import Erdos387Proof.SeparatedCertificatePhase
import Erdos387Proof.MediumFourierTailDecay

/-! The actual subpower Fourier window contains no nonzero terminal-prime
exceptional frequency. The finite statement retains the integer frequency
and its absolute value, with no choice of positive representative. -/

namespace Erdos387Proof.SeparatedFrequencyWindow

open Erdos387 Erdos387.CoverBPZ SeparatedCertificatePhase MediumFourierTailDecay
open Filter

theorem intCast_ne_zero_of_natAbs_lt (p : ℕ) (h : ℤ) (hh : h ≠ 0)
    (hab : h.natAbs < p) : (h : ZMod p) ≠ 0 := by
  intro hz
  have hd : (p : ℤ) ∣ h := (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hz
  have hd' : p ∣ h.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hp := Nat.le_of_dvd (Int.natAbs_pos.mpr hh) hd'
  omega

theorem height_two_le (N k : ℕ) (hN : 0 < N) (hk : 0 < k) : 2 ≤ height N k := by
  have hz := SubpowerScale.two_le_z hN hk
  have hp : 1 ≤ 8*N := by omega
  exact hz.trans (by simpa only [height, pow_one] using
    Nat.pow_le_pow_right (by omega : 1 ≤ SubpowerScale.z N k) hp)

theorem base_le_secondMin (t k : ℕ) (ht : 1 ≤ t) (hk : 0 < k) :
    t ≤ BPZScale.secondMin t k := by
  have he : 1 ≤ BPZScale.secondExp k := by
    unfold BPZScale.secondExp
    have : 0 < 300*3^k*k^99 := by positivity
    omega
  simpa only [BPZScale.secondMin, pow_one] using Nat.pow_le_pow_right ht he

/-- Purely finite exclusion of exceptional frequencies for actual
certificate data; the height-square and height lower bounds are checked
internally at the subpower scale by the following theorem. -/
theorem certificate_frequency_ne_zero
    {B K n t medium g H : ℕ} {S : BPZSection6Input B K}
    (C : CertificatePhaseData S n (BPZScale.y t S.k) medium
      (BPZScale.secondMin t S.k) (BPZScale.gap t S.k) g)
    (hH : 2 ≤ H) (hHt : H^2 ≤ t) (h : ℤ) (hh : h ≠ 0) (hab : h.natAbs ≤ H) :
    (h : ZMod (C.q C.j)) ≠ 0 := by
  have hHt' : H < t := by nlinarith
  have ht : 1 ≤ t := by omega
  have hk : 0 < S.k := by have := S.hk3; omega
  apply intCast_ne_zero_of_natAbs_lt _ _ hh
  exact hab.trans_lt (hHt'.trans_le
    ((base_le_secondMin t S.k ht hk).trans C.terminal_large.le))

/-- A single eventual bound works for every actual separated certificate,
all its integer frequency representatives, and every nonzero frequency
in the common H=z^(8N) smoothing window. -/
theorem eventually_certificate_frequency_ne_zero
    {B K : ℕ} (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop, ∀ (n medium g : ℕ)
      (C : CertificatePhaseData S n (BPZScale.y (SubpowerScale.base N S.k) S.k)
        medium (BPZScale.secondMin (SubpowerScale.base N S.k) S.k)
        (BPZScale.gap (SubpowerScale.base N S.k) S.k) g)
      (h : ℤ), h ≠ 0 → h.natAbs ≤ height N S.k → (h : ZMod (C.q C.j)) ≠ 0 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_height_pow_mul_support_le_base S.k 2 0] with N hN hbound
  intro n medium g C h hh hab
  apply certificate_frequency_ne_zero C (height_two_le N S.k (by omega)
    (by have := S.hk3; omega)) _ h hh hab
  simpa only [zero_mul, pow_zero, mul_one] using hbound

end Erdos387Proof.SeparatedFrequencyWindow

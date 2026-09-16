import Erdos387Proof.SeparatedCertificateEnlargement
import Erdos387Proof.SplitCertificateMass

/-! Reciprocal mass on the actual separated-error enlarged certificate
domain, recombined across all dyadic blocks before taking the zero mode. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedMainMass
open Erdos387 Erdos387.CoverBPZ SeparatedCertificateEnlargement
open scoped BigOperators

theorem sum_certificates_reciprocal_le {B K X z y medium second gap : ℕ}
    (S : BPZSection6Input B K) (i : Fin S.k) {C : ℝ} {N : ℕ}
    (hC : 0<C)
    (hcheb : ∀ t : ℕ, N≤t → (Nat.primeCounting t : ℝ)≤C*t/Real.log t)
    (hzN : N≤z) (hz : 2≤z) (hB : 0<B) :
    (∑ t∈certificates S X z y medium second gap i, (1 : ℝ)/t.1.val.value)≤
      (6*B*C/Real.log z)*roughReciprocalMass z X^(S.k+1) := by
  apply SplitCertificateMass.sum_reciprocal_le i _ hC hcheb hzN hz hB
  intro t ht
  have ha := admissible ht
  have hb := split_bounds ht
  exact ⟨ha.factor,fun j => (ha.factors j).2.1,hb.1,hb.2.2.1,ha.near,ha.upper⟩

end Erdos387Proof.SeparatedMainMass

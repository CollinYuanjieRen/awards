import Erdos806SmallBases.Definitions

/-! Base-`q` digits, the universal set, and the digit-by-digit shift. -/

namespace Erdos806

theorem digit_lt (q p x : ℕ) (hq : 0 < q) : digit q p x < q :=
  Nat.mod_lt _ hq

theorem digit_add_mul_pow_succ (q p x c : ℕ) :
    digit q p (x + c * q ^ (p + 1)) = digit q p x := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [digit]
  · unfold digit
    have hpow : c * q ^ (p + 1) = c * q * q ^ p := by ring
    rw [hpow, Nat.add_mul_div_right _ _ (pow_pos hq p), Nat.add_mul_mod_self_right]

theorem digit_add_mul_pow (q p x h : ℕ) (hq : 0 < q) :
    digit q p (x + h * q ^ p) = (digit q p x + h) % q := by
  unfold digit
  rw [Nat.add_mul_div_right _ _ (pow_pos hq p), Nat.mod_add_mod]

theorem digit_mod_pow (q p k x : ℕ) (hp : p < k) : digit q p (x % q ^ k) = digit q p x := by
  unfold digit
  have hk : q ^ k = q ^ p * q ^ (k - p) := by
    rw [← pow_add]; congr 1; omega
  rw [hk, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self q (by omega : k - p ≠ 0))]

/-- Reconstruction of `u` from its high part and low part when its `p`-th digit vanishes. -/
private theorem reconstruct (q p u : ℕ) (h : digit q p u = 0) :
    u = q ^ (p + 1) * (u / q ^ (p + 1)) + u % q ^ p := by
  have h1 : q ^ p * (u / q ^ p) + u % q ^ p = u := Nat.div_add_mod u (q ^ p)
  have h2 : q * (u / q ^ p / q) + u / q ^ p % q = u / q ^ p := Nat.div_add_mod (u / q ^ p) q
  have h3 : u / q ^ p / q = u / q ^ (p + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [h3] at h2
  have h : u / q ^ p % q = 0 := h
  have h4 : u / q ^ p = q * (u / q ^ (p + 1)) := by omega
  calc u = q ^ p * (u / q ^ p) + u % q ^ p := h1.symm
    _ = q ^ (p + 1) * (u / q ^ (p + 1)) + u % q ^ p := by
        rw [h4, ← mul_assoc, ← pow_succ]

private theorem card_fiber (q k p : ℕ) (hq : 0 < q) (hp : p < k) :
    (((Finset.range (q ^ k)).filter (fun u => digit q p u = 0)).card) ≤ q ^ (k - 1) := by
  classical
  have hcard : (Finset.range (q ^ (k - 1 - p)) ×ˢ Finset.range (q ^ p)).card = q ^ (k - 1) := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range, ← pow_add]
    congr 1
    omega
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun u => (u / q ^ (p + 1), u % q ^ p))
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    refine ⟨?_, Nat.mod_lt _ (pow_pos hq p)⟩
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq _), ← pow_add]
    have he : k - 1 - p + (p + 1) = k := by omega
    rw [he]
    exact hu.1
  · intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu hv
    simp only [Prod.mk.injEq] at huv
    have e1 := reconstruct q p u hu.2
    have e2 := reconstruct q p v hv.2
    rw [huv.1, huv.2] at e1
    exact e1.trans e2.symm

theorem card_univSet (q k : ℕ) : (univSet q k).card ≤ k * q ^ (k - 1) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [univSet]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hz : (0 : ℕ) ^ k = 0 := zero_pow (by omega)
    simp [univSet, hz]
  have hsub : univSet q k ⊆ (Finset.range k).biUnion
      (fun p => (Finset.range (q ^ k)).filter (fun u => digit q p u = 0)) := by
    intro u hu
    simp only [univSet, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨hu1, p, hp, hd⟩ := hu
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    exact ⟨p, hp, hu1, hd⟩
  calc (univSet q k).card
      ≤ ((Finset.range k).biUnion
          (fun p => (Finset.range (q ^ k)).filter (fun u => digit q p u = 0))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Finset.range k, ((Finset.range (q ^ k)).filter (fun u => digit q p u = 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Finset.range k, q ^ (k - 1) :=
        Finset.sum_le_sum (fun p hp => card_fiber q k p hq (Finset.mem_range.mp hp))
    _ = k * q ^ (k - 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The digit-by-digit shift: `shiftAux q sel p` fixes the digits below `p`. -/
private def shiftAux (q : ℕ) (sel : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => shiftAux q sel p + ((q - digit q p (sel p + shiftAux q sel p)) % q) * q ^ p

private theorem shiftAux_lt (q : ℕ) (sel : ℕ → ℕ) (hq : 0 < q) (p : ℕ) :
    shiftAux q sel p < q ^ p := by
  induction p with
  | zero => simp [shiftAux]
  | succ p ih =>
    have hdlt : (q - digit q p (sel p + shiftAux q sel p)) % q < q := Nat.mod_lt _ hq
    have key : ((q - digit q p (sel p + shiftAux q sel p)) % q + 1) * q ^ p ≤ q * q ^ p :=
      Nat.mul_le_mul_right _ hdlt
    rw [add_mul, one_mul] at key
    have hqp : q ^ (p + 1) = q * q ^ p := by ring
    show shiftAux q sel p + ((q - digit q p (sel p + shiftAux q sel p)) % q) * q ^ p < q ^ (p + 1)
    rw [hqp]
    omega

private theorem shiftAux_eq_add (q : ℕ) (sel : ℕ → ℕ) (m p' : ℕ) (hp' : m ≤ p') :
    ∃ c, shiftAux q sel p' = shiftAux q sel m + c * q ^ m := by
  induction p', hp' using Nat.le_induction with
  | base => exact ⟨0, by simp⟩
  | succ p' hp' ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + ((q - digit q p' (sel p' + shiftAux q sel p')) % q) * q ^ (p' - m), ?_⟩
    have hpow : q ^ (p' - m) * q ^ m = q ^ p' := by
      rw [← pow_add]; congr 1; omega
    show shiftAux q sel p' + ((q - digit q p' (sel p' + shiftAux q sel p')) % q) * q ^ p' = _
    rw [hc, add_mul, mul_assoc, hpow]
    ring

private theorem digit_shiftAux_succ (q : ℕ) (sel : ℕ → ℕ) (hq : 0 < q) (p : ℕ) :
    digit q p (sel p + shiftAux q sel (p + 1)) = 0 := by
  have hd : digit q p (sel p + shiftAux q sel p) < q := digit_lt q p _ hq
  have he : sel p + shiftAux q sel (p + 1)
      = (sel p + shiftAux q sel p)
        + ((q - digit q p (sel p + shiftAux q sel p)) % q) * q ^ p := by
    show sel p + (shiftAux q sel p + _) = _
    ring
  rw [he, digit_add_mul_pow q p _ _ hq]
  set d := digit q p (sel p + shiftAux q sel p) with hdd
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · rw [hd0, Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.zero_mod]
  · rw [Nat.mod_eq_of_lt (by omega : q - d < q)]
    have hsum : d + (q - d) = q := by omega
    rw [hsum, Nat.mod_self]

private theorem digit_shiftAux (q : ℕ) (sel : ℕ → ℕ) (hq : 0 < q) (p k : ℕ) (hp : p < k) :
    digit q p (sel p + shiftAux q sel k) = 0 := by
  obtain ⟨c, hc⟩ := shiftAux_eq_add q sel (p + 1) k hp
  have hre : sel p + shiftAux q sel k
      = (sel p + shiftAux q sel (p + 1)) + c * q ^ (p + 1) := by rw [hc]; ring
  rw [hre, digit_add_mul_pow_succ]
  exact digit_shiftAux_succ q sel hq p

theorem exists_shift (q k : ℕ) (hq : 0 < q) (T : Finset ℕ) (hT : T.card ≤ k) :
    ∃ h, h < q ^ k ∧ ∀ s ∈ T, (s + h) % q ^ k ∈ univSet q k := by
  classical
  obtain ⟨pos, sel, hposlt, hsel⟩ :
      ∃ pos sel : ℕ → ℕ, (∀ s ∈ T, pos s < k) ∧ (∀ s ∈ T, sel (pos s) = s) := by
    refine ⟨fun s => if hs : s ∈ T then (T.equivFin ⟨s, hs⟩).val else 0,
            fun p => if hp : p < T.card then (T.equivFin.symm ⟨p, hp⟩).val else 0, ?_, ?_⟩
    · intro s hs
      simp only [dite_eq_left hs]
      exact lt_of_lt_of_le (T.equivFin ⟨s, hs⟩).isLt hT
    · intro s hs
      simp only [dite_eq_left hs]
      rw [dite_eq_left (T.equivFin ⟨s, hs⟩).isLt]
      simp
  refine ⟨shiftAux q sel k, shiftAux_lt q sel hq k, ?_⟩
  intro s hs
  simp only [univSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt _ (pow_pos hq k), pos s, hposlt s hs, ?_⟩
  rw [digit_mod_pow q (pos s) k _ (hposlt s hs)]
  have hz := digit_shiftAux q sel hq (pos s) k (hposlt s hs)
  rwa [hsel s hs] at hz

end Erdos806

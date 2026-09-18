import Erdos1183Lattices.Basic
import Erdos1183Lattices.Sublattice

/-!
# Sections C2 and C3: counting monochromatic colourings and the upper bound `f n ≤ (n + 1) ^ 2`

`card_mono_le` bounds the number of colourings that are monochromatic on a fixed nonempty family
`F` by `2 * 2 ^ (2 ^ n - F.card)`.  Combined with the bound `2 ^ (n ^ 2 + 2 * n)` on the number of
nonempty closed families (`card_closed_le`), a double count of the pairs `(c, F)` with `F` a large
nonempty closed family monochromatic for `c` gives `¬ Good n ((n + 1) ^ 2 + 1)`, hence
`f n ≤ (n + 1) ^ 2`.
-/

namespace Erdos1183

variable {n : ℕ}

/-- `Mono` is decidable (an existential over `Bool` of a bounded quantifier over a `Finset`). -/
instance decidableMono (c : Finset (Fin n) → Bool) (F : Finset (Finset (Fin n))) :
    Decidable (Mono c F) :=
  inferInstanceAs (Decidable (∃ b : Bool, ∀ A ∈ F, c A = b))

/-! ### C2: colourings monochromatic on a fixed family -/

/-- At most `2 * 2 ^ (2 ^ n - F.card)` colourings are monochromatic on a fixed nonempty `F`. -/
theorem card_mono_le {n : ℕ} {F : Finset (Finset (Fin n))} (hF : F.Nonempty) :
    (Finset.univ.filter (fun c : Finset (Fin n) → Bool => Mono c F)).card
      ≤ 2 * 2 ^ (2 ^ n - F.card) := by
  obtain ⟨A₀, hA₀⟩ := hF
  set T : Finset (Finset (Fin n) → Bool) :=
    Fintype.piFinset
      (fun X : Finset (Fin n) => if X ∈ F then ({false} : Finset Bool) else Finset.univ) with hT
  have hcompl : (Finset.univ.filter (fun X : Finset (Fin n) => ¬ (X ∈ F))).card
      = 2 ^ n - F.card := by
    have hset : (Finset.univ.filter (fun X : Finset (Fin n) => ¬ (X ∈ F))) = Fᶜ := by
      ext X; simp
    rw [hset, Finset.card_compl, Fintype.card_finset, Fintype.card_fin]
  have hcardT : T.card = 2 ^ (2 ^ n - F.card) := by
    rw [hT, Fintype.card_piFinset]
    have hstep : ∀ X : Finset (Fin n),
        ((if X ∈ F then ({false} : Finset Bool) else Finset.univ)).card
          = if X ∈ F then 1 else 2 := by
      intro X; by_cases hX : X ∈ F <;> simp [hX]
    rw [Finset.prod_congr rfl (fun X _ => hstep X), Finset.prod_ite]
    simp [Finset.prod_const, hcompl]
  have hmain : (Finset.univ.filter (fun c : Finset (Fin n) → Bool => Mono c F)).card
      ≤ ((Finset.univ : Finset Bool) ×ˢ T).card := by
    refine Finset.card_le_card_of_injOn
      (fun c => (c A₀, fun X => if X ∈ F then false else c X)) ?_ ?_
    · intro c _
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and]
      rw [hT, Fintype.mem_piFinset]
      intro X
      by_cases hX : X ∈ F <;> simp [hX]
    · intro c hc c' hc' h
      simp only [Finset.mem_coe, Finset.mem_filter] at hc hc'
      obtain ⟨b, hb⟩ := hc.2
      obtain ⟨b', hb'⟩ := hc'.2
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      funext X
      by_cases hX : X ∈ F
      · rw [hb X hX, hb' X hX, ← hb A₀ hA₀, ← hb' A₀ hA₀, h1]
      · have hx := congrFun h2 X
        simpa [hX] using hx
  refine hmain.trans ?_
  rw [Finset.card_product, hcardT]
  simp

/-! ### C3: the double count -/

/-- The key upper bound: no colouring-free guarantee beyond `(n + 1) ^ 2` sets. -/
theorem not_good_upper (n : ℕ) : ¬ Good n ((n + 1) ^ 2 + 1) := by
  intro hgood
  set m := (n + 1) ^ 2 + 1 with hm
  have hm' : m = n ^ 2 + 2 * n + 2 := by rw [hm]; ring
  rcases Nat.lt_or_ge (2 ^ n) m with hcase | hcase
  · exact absurd (Good.le_two_pow hgood) (by omega)
  choose W hW1 hW2 hW3 hW4 using hgood
  set S : Finset ((Finset (Fin n) → Bool) × Finset (Finset (Fin n))) :=
    Finset.univ.filter
      (fun p => p.2.Nonempty ∧ Closed p.2 ∧ Mono p.1 p.2 ∧ m ≤ p.2.card) with hS
  set closedBig : Finset (Finset (Finset (Fin n))) :=
    Finset.univ.filter (fun F => F.Nonempty ∧ Closed F ∧ m ≤ F.card) with hCB
  -- lower bound
  have hcardfun : Fintype.card (Finset (Fin n) → Bool) = 2 ^ 2 ^ n := by
    simp [Fintype.card_finset]
  have hlow : 2 ^ 2 ^ n ≤ S.card := by
    have hinj : (Finset.univ : Finset (Finset (Fin n) → Bool)).card ≤ S.card := by
      refine Finset.card_le_card_of_injOn (fun c => (c, W c)) ?_ ?_
      · intro c _
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        exact ⟨hW1 c, hW2 c, hW3 c, hW4 c⟩
      · intro c _ c' _ h
        exact congrArg Prod.fst h
    refine le_trans ?_ hinj
    rw [Finset.card_univ, hcardfun]
  -- fibrewise upper bound
  have hfib : ∀ p ∈ S, p.2 ∈ closedBig := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    rw [hCB, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hp.2.1, hp.2.2.1, hp.2.2.2.2⟩
  have hfibre : ∀ F ∈ closedBig, (S.filter fun p => p.2 = F).card ≤ 2 * 2 ^ (2 ^ n - m) := by
    intro F hF
    rw [hCB, Finset.mem_filter] at hF
    obtain ⟨-, hFne, hFcl, hFcard⟩ := hF
    have h1 : (S.filter fun p => p.2 = F).card
        ≤ (Finset.univ.filter (fun c : Finset (Fin n) → Bool => Mono c F)).card := by
      refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        obtain ⟨hpS, hp2⟩ := hp
        rw [Finset.mem_filter] at hpS
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        exact hp2 ▸ hpS.2.2.2.1
      · intro p hp q hq h
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext h (hp.2.trans hq.2.symm)
    refine h1.trans ((card_mono_le hFne).trans ?_)
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hupper : S.card ≤ closedBig.card * (2 * 2 ^ (2 ^ n - m)) := by
    rw [Finset.card_eq_sum_card_fiberwise hfib]
    calc ∑ F ∈ closedBig, (S.filter fun p => p.2 = F).card
        ≤ ∑ _F ∈ closedBig, (2 * 2 ^ (2 ^ n - m)) := Finset.sum_le_sum hfibre
      _ = closedBig.card * (2 * 2 ^ (2 ^ n - m)) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hCBcard : closedBig.card ≤ 2 ^ (n ^ 2 + 2 * n) := by
    refine le_trans (Finset.card_le_card ?_) (card_closed_le n)
    intro F hF
    rw [hCB, Finset.mem_filter] at hF
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hF.2.1, hF.2.2.1⟩
  -- arithmetic
  have hexp : n ^ 2 + 2 * n + 1 + (2 ^ n - m) = 2 ^ n - 1 := by omega
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hfinal : closedBig.card * (2 * 2 ^ (2 ^ n - m)) < 2 ^ 2 ^ n := by
    calc closedBig.card * (2 * 2 ^ (2 ^ n - m))
        ≤ 2 ^ (n ^ 2 + 2 * n) * (2 * 2 ^ (2 ^ n - m)) :=
          Nat.mul_le_mul_right _ hCBcard
      _ = 2 ^ (n ^ 2 + 2 * n + 1 + (2 ^ n - m)) := by
          rw [pow_add (2 : ℕ) (n ^ 2 + 2 * n + 1) (2 ^ n - m), pow_succ]; ring
      _ = 2 ^ (2 ^ n - 1) := by rw [hexp]
      _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- The upper bound `f n ≤ (n + 1) ^ 2`. -/
theorem f_le (n : ℕ) : f n ≤ (n + 1) ^ 2 := by
  have h := f_lt_of_not_good (not_good_upper n)
  omega

end Erdos1183

import Mathlib

/-!
# The greedy (Stanley) sequence `A(n)` — definitions and the greedy specification

This file sets up the greedy construction behind Erdős problem #271 (the Odlyzko–Stanley
sequence).  Starting from `a 0 = 0` and `a 1 = n`, each further term is the least integer
strictly larger than the previous one that keeps the set of terms free of three-term
arithmetic progressions.

The main results are `not_hasThreeAP_prefix` (every prefix is AP-free) and
`isLeast_stanley_succ_succ` (the greedy characterisation of the terms), which together
justify that the recursion never runs into an empty `sInf`.
-/

namespace Erdos271

/-- `HasThreeAP S`: `S` contains a (nontrivial) three-term arithmetic progression
`a < b < c`, `a + c = 2 b`. -/
def HasThreeAP (S : Set ℕ) : Prop :=
  ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c ∧ a + c = 2 * b

/-- The greedy step: the least `m > t` such that `insert m S` has no three-term AP
(`sInf` of the empty set is `0`; the set is nonempty whenever `S` itself is AP-free, see below). -/
noncomputable def greedyNext (S : Finset ℕ) (t : ℕ) : ℕ :=
  sInf {m : ℕ | t < m ∧ ¬ HasThreeAP (insert m (S : Set ℕ))}

/-- State of the greedy construction: (set of terms so far, last term). -/
noncomputable def stanleyState (n : ℕ) : ℕ → Finset ℕ × ℕ
  | 0 => ({0}, 0)
  | 1 => ({0, n}, n)
  | k + 2 =>
    let s := stanleyState n (k + 1)
    let m := greedyNext s.1 s.2
    (insert m s.1, m)

/-- The Stanley sequence `A(n)`: `a 0 = 0`, `a 1 = n`, `a (k+2)` = least integer `> a (k+1)`
such that `{a 0, …, a (k+2)}` has no three-term arithmetic progression. -/
noncomputable def stanley (n : ℕ) (k : ℕ) : ℕ := (stanleyState n k).2

@[simp] theorem stanley_zero (n : ℕ) : stanley n 0 = 0 := rfl

@[simp] theorem stanley_one (n : ℕ) : stanley n 1 = n := rfl

private theorem stanleyState_zero_fst (n : ℕ) : (stanleyState n 0).1 = {0} := rfl

private theorem stanleyState_one_fst (n : ℕ) : (stanleyState n 1).1 = {0, n} := rfl

private theorem stanleyState_succ_succ_fst (n k : ℕ) :
    (stanleyState n (k + 1 + 1)).1 =
      insert (stanley n (k + 1 + 1)) (stanleyState n (k + 1)).1 := rfl

/-- the set component is exactly the image of the terms so far -/
theorem stanleyState_fst (n k : ℕ) :
    (stanleyState n k).1 = (Finset.range (k + 1)).image (stanley n) := by
  induction k with
  | zero => simp [stanleyState_zero_fst]
  | succ k ih =>
    cases k with
    | zero =>
      show (stanleyState n 1).1 = (Finset.range (1 + 1)).image (stanley n)
      rw [stanleyState_one_fst, Finset.range_add_one, Finset.range_one, Finset.image_insert,
        Finset.image_singleton, stanley_zero, stanley_one]
      exact Finset.pair_comm 0 n
    | succ j =>
      rw [Finset.range_add_one (n := j + 1 + 1), Finset.image_insert, stanleyState_succ_succ_fst,
        ih]

theorem coe_stanleyState_fst (n k : ℕ) :
    ((stanleyState n k).1 : Set ℕ) = stanley n '' Set.Iic k := by
  rw [stanleyState_fst, Finset.coe_image, Finset.coe_range]
  congr 1
  ext x
  simp

theorem stanley_succ_succ (n k : ℕ) :
    stanley n (k + 2) = sInf {m : ℕ | stanley n (k + 1) < m ∧
      ¬ HasThreeAP (insert m (stanley n '' Set.Iic (k + 1)))} := by
  rw [← coe_stanleyState_fst]
  rfl

/-- key existence lemma: an AP-free finite set can always be extended above any threshold -/
theorem exists_gt_not_hasThreeAP (S : Finset ℕ) (hS : ¬ HasThreeAP (S : Set ℕ)) (t : ℕ) :
    ∃ m, t < m ∧ ¬ HasThreeAP (insert m (S : Set ℕ)) := by
  refine ⟨2 * S.sup id + t + 1, by omega, ?_⟩
  rintro ⟨a, b, c, ha, hb, hc, hab, hbc, habc⟩
  simp only [Set.mem_insert_iff, Finset.mem_coe] at ha hb hc
  have key : ∀ x : ℕ, (x = 2 * S.sup id + t + 1 ∨ x ∈ S) → x ≤ 2 * S.sup id + t + 1 := by
    rintro x (rfl | hx)
    · exact le_rfl
    · have hx' : id x ≤ S.sup id := Finset.le_sup hx
      simp only [id] at hx'
      omega
  have hbM := key b hb
  have hcM := key c hc
  rcases ha with rfl | haS
  · omega
  rcases hb with rfl | hbS
  · omega
  rcases hc with rfl | hcS
  · have hb' : id b ≤ S.sup id := Finset.le_sup hbS
    simp only [id] at hb'
    omega
  · exact hS ⟨a, b, c, Finset.mem_coe.mpr haS, Finset.mem_coe.mpr hbS,
      Finset.mem_coe.mpr hcS, hab, hbc, habc⟩

private theorem not_hasThreeAP_stanleyState (n k : ℕ) :
    ¬ HasThreeAP ((stanleyState n k).1 : Set ℕ) := by
  induction k with
  | zero =>
    rintro ⟨a, b, c, ha, hb, hc, hab, hbc, -⟩
    rw [stanleyState_zero_fst] at ha hb hc
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb hc
    omega
  | succ k ih =>
    cases k with
    | zero =>
      rintro ⟨a, b, c, ha, hb, hc, hab, hbc, -⟩
      rw [stanleyState_one_fst] at ha hb hc
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb hc
      omega
    | succ j =>
      obtain ⟨m₀, hm₀⟩ :=
        exists_gt_not_hasThreeAP (stanleyState n (j + 1)).1 ih (stanley n (j + 1))
      have hne : Set.Nonempty {m : ℕ | stanley n (j + 1) < m ∧
          ¬ HasThreeAP (insert m ((stanleyState n (j + 1)).1 : Set ℕ))} := ⟨m₀, hm₀⟩
      have hmem := Nat.sInf_mem hne
      rw [stanleyState_succ_succ_fst, Finset.coe_insert]
      exact hmem.2

/-- the prefixes are AP-free (any `n`) -/
theorem not_hasThreeAP_prefix (n k : ℕ) : ¬ HasThreeAP (stanley n '' Set.Iic k) := by
  rw [← coe_stanleyState_fst]
  exact not_hasThreeAP_stanleyState n k

/-- the greedy specification, in `IsLeast` form -/
theorem isLeast_stanley_succ_succ (n k : ℕ) :
    IsLeast {m : ℕ | stanley n (k + 1) < m ∧
      ¬ HasThreeAP (insert m (stanley n '' Set.Iic (k + 1)))} (stanley n (k + 2)) := by
  rw [← coe_stanleyState_fst]
  obtain ⟨m₀, hm₀⟩ :=
    exists_gt_not_hasThreeAP (stanleyState n (k + 1)).1
      (not_hasThreeAP_stanleyState n (k + 1)) (stanley n (k + 1))
  have hne : Set.Nonempty {m : ℕ | stanley n (k + 1) < m ∧
      ¬ HasThreeAP (insert m ((stanleyState n (k + 1)).1 : Set ℕ))} := ⟨m₀, hm₀⟩
  have hval : stanley n (k + 2) = sInf {m : ℕ | stanley n (k + 1) < m ∧
      ¬ HasThreeAP (insert m ((stanleyState n (k + 1)).1 : Set ℕ))} := rfl
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact Nat.sInf_mem hne
  · intro m hm
    rw [hval]
    exact Nat.sInf_le hm

theorem stanley_lt_succ_succ (n k : ℕ) : stanley n (k + 1) < stanley n (k + 2) :=
  (isLeast_stanley_succ_succ n k).1.1

theorem stanley_strictMono {n : ℕ} (hn : 0 < n) : StrictMono (stanley n) := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  match k with
  | 0 => simpa using hn
  | k + 1 => exact stanley_lt_succ_succ n k

end Erdos271

#print axioms Erdos271.isLeast_stanley_succ_succ
#print axioms Erdos271.stanley_strictMono
#print axioms Erdos271.not_hasThreeAP_prefix
#print axioms Erdos271.stanleyState_fst
#print axioms Erdos271.stanley_succ_succ

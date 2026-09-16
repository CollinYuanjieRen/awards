import Erdos387Proof.SeparatedCertificatePhase
import Mathlib.Data.List.Prime

/-!
# Exact finite Buchstab stopping domains

BNPZ arXiv:2605.21221v2, the combinatorial Buchstab lemma and §10.
The stopping tree retains the residual roughness mask and every original
external predicate. It does not assume a Type-I/II decomposition estimate.
-/

namespace Erdos387Proof.SeparatedBuchstabDecomposition

open scoped BigOperators

structure Leaf where
  chosen : List ℕ
  remaining : List ℕ
  stopped : Bool
  deriving DecidableEq

def Leaf.prepend (p : ℕ) (l : Leaf) : Leaf :=
  { l with chosen := p::l.chosen }

/-- Descending prime candidates are either excluded, included and expanded,
or included and stopped at the first product exceeding R. -/
def leaves (R r : ℕ) : List ℕ → List Leaf
  | [] => [⟨[],[],false⟩]
  | p::ps => leaves R r ps ++
      if R < r*p then [⟨[p],ps,true⟩]
      else (leaves R (r*p) ps).map (Leaf.prepend p)

noncomputable def Leaf.eval (f : ℕ → ℂ) (l : Leaf) : ℂ :=
  (-1)^l.chosen.length * (l.chosen.map f).prod *
    (l.remaining.map fun p => 1-f p).prod

theorem eval_prepend (f : ℕ → ℂ) (p : ℕ) (l : Leaf) :
    (l.prepend p).eval f = -(f p)*l.eval f := by
  simp only [Leaf.prepend, Leaf.eval, List.length_cons, List.map_cons,
    List.prod_cons, pow_succ]
  ring

private theorem sum_eval_prepend (f : ℕ → ℂ) (p : ℕ) (ls : List Leaf) :
    ((ls.map (Leaf.prepend p)).map (Leaf.eval f)).sum =
      -(f p)*(ls.map (Leaf.eval f)).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons, eval_prepend, ih]
    ring

/-- An exact finite identity for arbitrary complex factors. The threshold
changes only the expansion domains, not the value of the product. -/
theorem sum_eval_leaves (R r : ℕ) (ps : List ℕ) (f : ℕ → ℂ) :
    ((leaves R r ps).map (Leaf.eval f)).sum =
      (ps.map fun p => 1-f p).prod := by
  induction ps generalizing r with
  | nil => simp [leaves, Leaf.eval]
  | cons p ps ih =>
    rw [leaves, List.map_append, List.sum_append, ih]
    split_ifs with h
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.prod_cons, Leaf.eval, List.length_cons, List.length_nil, List.prod_nil]
      ring
    · rw [sum_eval_prepend, ih]
      simp only [List.map_cons, List.prod_cons]
      ring

def divisorMask (ps : List ℕ) (n : ℕ) : ℂ :=
  (ps.map fun p => if p ∣ n then (1 : ℂ) else 0).prod

def roughMask (ps : List ℕ) (n : ℕ) : ℂ :=
  (ps.map fun p => if p ∣ n then (0 : ℂ) else 1).prod

theorem eval_divisorMask (ps : List ℕ) (R r n : ℕ) :
    roughMask ps n = ((leaves R r ps).map fun l =>
      (-1 : ℂ)^l.chosen.length * divisorMask l.chosen n * roughMask l.remaining n).sum := by
  have h := sum_eval_leaves R r ps (fun p => if p ∣ n then (1 : ℂ) else 0)
  have he (p : ℕ) : (1 : ℂ)-(if p ∣ n then 1 else 0) = (if p ∣ n then 0 else 1) := by
    by_cases hp : p ∣ n <;> simp [hp]
  unfold Leaf.eval at h
  simp_rw [he] at h
  simpa only [divisorMask, roughMask] using h.symm

/-- Chosen prime lists are actual sublists of the original candidate list. -/
theorem chosen_sublist (R r : ℕ) (ps : List ℕ) (l : Leaf)
    (hl : l ∈ leaves R r ps) : l.chosen.Sublist ps := by
  induction ps generalizing r l with
  | nil =>
    simp only [leaves, List.mem_singleton] at hl
    subst l
    exact List.Sublist.refl _
  | cons p ps ih =>
    rw [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact List.Sublist.cons p (ih r l hl)
    · split_ifs at hl with h
      · simp only [List.mem_singleton] at hl
        subst l
        exact List.Sublist.cons_cons p (List.nil_sublist ps)
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
        exact List.Sublist.cons_cons p (ih (r*p) a ha)

theorem remaining_sublist (R r : ℕ) (ps : List ℕ) (l : Leaf)
    (hl : l ∈ leaves R r ps) : l.remaining.Sublist ps := by
  induction ps generalizing r l with
  | nil =>
    simp only [leaves, List.mem_singleton] at hl
    subst l
    exact List.Sublist.refl _
  | cons p ps ih =>
    rw [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact List.Sublist.cons p (ih r l hl)
    · split_ifs at hl with h
      · simp only [List.mem_singleton] at hl
        subst l
        exact List.Sublist.cons p (List.Sublist.refl _)
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
        exact List.Sublist.cons p (ih (r*p) a ha)

/-- Every leaf is either a fully expanded Type-I term of product≤R, or
the first crossing Type-II term of product in (R,R*y]. -/
theorem leaf_domain (R r y : ℕ) (ps : List ℕ) (l : Leaf)
    (hr : r ≤ R) (hy : ∀ p ∈ ps, p ≤ y) (hl : l ∈ leaves R r ps) :
    (l.stopped = false → l.remaining = [] ∧ r*l.chosen.prod ≤ R) ∧
      (l.stopped = true → R < r*l.chosen.prod ∧ r*l.chosen.prod ≤ R*y ∧ l.chosen ≠ []) := by
  induction ps generalizing r l with
  | nil =>
    simp only [leaves, List.mem_singleton] at hl
    subst l
    simp [hr]
  | cons p ps ih =>
    have hy' : ∀ v ∈ ps, v ≤ y := fun v hv => hy v (List.mem_cons_of_mem p hv)
    rw [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ih r l hr hy' hl
    · split_ifs at hl with h
      · simp only [List.mem_singleton] at hl
        subst l
        have hupper := Nat.mul_le_mul hr (hy p (List.mem_cons_self))
        simp [h, hupper]
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
        have hh := ih (r*p) a (Nat.le_of_not_gt h) hy' ha
        constructor
        · intro hs
          obtain ⟨he,hb⟩ := hh.1 hs
          exact ⟨he, by simpa [Leaf.prepend, Nat.mul_assoc] using hb⟩
        · intro hs
          obtain ⟨hb,hb',hne⟩ := hh.2 hs
          refine ⟨?_, ?_, by simp [Leaf.prepend]⟩
          · simpa [Leaf.prepend, Nat.mul_assoc] using hb
          · simpa [Leaf.prepend, Nat.mul_assoc] using hb'

theorem coefficient_norm (l : Leaf) : ‖(-1 : ℂ)^l.chosen.length‖ = 1 := by simp

/-- The roughness product is exactly its finite no-small-prime predicate. -/
theorem roughMask_eq_indicator (ps : List ℕ) (n : ℕ) :
    roughMask ps n = if ∀ p ∈ ps, ¬p ∣ n then 1 else 0 := by
  induction ps with
  | nil => simp [roughMask]
  | cons p ps ih =>
    change (if p ∣ n then (0 : ℂ) else 1)*roughMask ps n = _
    rw [ih]
    by_cases hp : p ∣ n <;> by_cases hs : ∀ q ∈ ps, ¬q ∣ n <;> simp [hp,hs]

/-- Divisibility of every selected distinct prime is equivalent to
divisibility of their product. Repeated primes are never introduced. -/
theorem divisorMask_eq_indicator (ps : List ℕ) (n : ℕ)
    (hnd : ps.Nodup) (hprime : ∀ p ∈ ps, p.Prime) :
    divisorMask ps n = if ps.prod ∣ n then 1 else 0 := by
  induction ps with
  | nil => simp [divisorMask]
  | cons p ps ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hprime' : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem p hq)
    have hcop : Nat.Coprime p ps.prod := Nat.coprime_list_prod_right_iff.mpr (by
      intro q hq
      exact (Nat.coprime_primes (hprime p (List.mem_cons_self)) (hprime' q hq)).mpr
        (fun he => hnd'.1 (he.symm ▸ hq)))
    have hd : p*ps.prod ∣ n ↔ p ∣ n ∧ ps.prod ∣ n := by
      constructor
      · intro h
        exact ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩
      · rintro ⟨hp,hs⟩
        exact hcop.mul_dvd_of_dvd_of_dvd hp hs
    change (if p ∣ n then (1 : ℂ) else 0)*divisorMask ps n = _
    rw [ih hnd'.2 hprime']
    simp only [List.prod_cons, hd]
    by_cases hp : p ∣ n <;> by_cases hs : ps.prod ∣ n <;> simp [hp,hs]

noncomputable def primeList (y : ℕ) : List ℕ := (Nat.primesBelow y).sort (· ≥ ·)

theorem mem_primeList (y p : ℕ) : p ∈ primeList y ↔ p < y ∧ p.Prime := by
  simp [primeList, Nat.mem_primesBelow]

theorem primeList_nodup (y : ℕ) : (primeList y).Nodup := Finset.sort_nodup _ _

theorem primeList_descending (y : ℕ) : (primeList y).Pairwise (· > ·) :=
  (Finset.sortedGT_sort _).pairwise

noncomputable def roughIndicator (y n : ℕ) : ℂ := by
  classical
  exact if Erdos387.IsZRough y n then 1 else 0

theorem roughMask_primeList (y n : ℕ) :
    roughMask (primeList y) n = roughIndicator y n := by
  classical
  unfold roughIndicator
  rw [roughMask_eq_indicator]
  have he : (∀ p ∈ primeList y, ¬p ∣ n) ↔ Erdos387.IsZRough y n := by
    simp only [mem_primeList, Erdos387.IsZRough]
    aesop
  simp only [he]

noncomputable def Leaf.value (l : Leaf) (n : ℕ) : ℂ :=
  (-1 : ℂ)^l.chosen.length * divisorMask l.chosen n * roughMask l.remaining n

private theorem finite_sum_list_sum (S : Finset ℕ) (ls : List Leaf) (F : Leaf → ℕ → ℂ) :
    (∑ n ∈ S, (ls.map fun l => F l n).sum) =
      (ls.map fun l => ∑ n ∈ S, F l n).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- Exact weighted decomposition retaining any original interval, product,
coprimality or integer-class predicate. No absolute-value enlargement of a
complex sum is used here. -/
theorem weighted_mask_identity (S : Finset ℕ) (R r : ℕ) (ps : List ℕ)
    (P : ℕ → Prop) [DecidablePred P] (W : ℕ → ℂ) :
    (∑ n ∈ S, if P n then roughMask ps n*W n else 0) =
      ((leaves R r ps).map fun l =>
        ∑ n ∈ S, if P n then l.value n*W n else 0).sum := by
  rw [← finite_sum_list_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : P n
  · simp only [hp, if_true]
    rw [List.sum_map_mul_right]
    rw [eval_divisorMask ps R r n]
    rfl
  · simp [hp]

/-- Actual rough-integer decomposition. The external predicate is unchanged
in every term and may contain all original constraints simultaneously. -/
theorem weighted_rough_identity (S : Finset ℕ) (R y : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (W : ℕ → ℂ) :
    (∑ n ∈ S, if P n then
      roughIndicator y n*W n else 0) =
      ((leaves R 1 (primeList y)).map fun l =>
        ∑ n ∈ S, if P n then l.value n*W n else 0).sum := by
  classical
  simpa only [roughMask_primeList] using weighted_mask_identity S R 1 (primeList y) P W

/-- At the E5 threshold R=y, each Type-II factor is already in the exact
source range y<u≤y², before any dyadic decomposition. -/
theorem e5_leaf_domain (y : ℕ) (hy : 1 ≤ y) (l : Leaf)
    (hl : l ∈ leaves y 1 (primeList y)) :
    (l.stopped = false → l.remaining = [] ∧ l.chosen.prod ≤ y) ∧
      (l.stopped = true → y < l.chosen.prod ∧ l.chosen.prod ≤ y^2 ∧ l.chosen ≠ []) := by
  have hh := leaf_domain y 1 y (primeList y) l hy
    (fun p hp => (mem_primeList y p |>.mp hp).1.le) hl
  simpa only [one_mul, pow_two] using hh

/-- Leaf divisibility is by a positive, squarefree product of actual primes. -/
theorem chosen_prime_data (R r y : ℕ) (l : Leaf)
    (hl : l ∈ leaves R r (primeList y)) :
    l.chosen.Nodup ∧ (∀ p ∈ l.chosen, p.Prime) ∧ 0 < l.chosen.prod := by
  have hsub := chosen_sublist R r (primeList y) l hl
  have hprime : ∀ p ∈ l.chosen, p.Prime := fun p hp =>
    (mem_primeList y p |>.mp (hsub.subset hp)).2
  refine ⟨(primeList_nodup y).sublist hsub, hprime, ?_⟩
  exact List.prod_pos (fun p hp => (hprime p hp).pos)

/-- A stopped leaf has exactly the source's descending-prime prefix: the
previous product is≤R and the remaining candidates are precisely those
below the last selected prime. -/
theorem stopped_prefix (R r : ℕ) (ps : List ℕ) (l : Leaf)
    (hdesc : ps.Pairwise (· > ·)) (hr : r ≤ R)
    (hl : l ∈ leaves R r ps) (hstop : l.stopped = true) :
    ∃ (pre : List ℕ) (p : ℕ), l.chosen = pre++[p] ∧
      r*pre.prod ≤ R ∧ p ∈ ps ∧ (∀ q ∈ pre, p < q) ∧
      ∀ q, q ∈ l.remaining ↔ q ∈ ps ∧ q < p := by
  induction ps generalizing r l with
  | nil =>
    simp only [leaves, List.mem_singleton] at hl
    subst l
    simp at hstop
  | cons a ps ih =>
    obtain ⟨hhead,hdesc'⟩ := List.pairwise_cons.mp hdesc
    have extend (p : ℕ) (hp : p ∈ ps) (ls : List ℕ)
        (hc : ∀ q, q ∈ ls ↔ q ∈ ps ∧ q < p) :
        ∀ q, q ∈ ls ↔ q ∈ a::ps ∧ q < p := by
      intro q
      rw [hc, List.mem_cons]
      have hpa := hhead p hp
      constructor
      · rintro ⟨hq,hqp⟩
        exact ⟨Or.inr hq,hqp⟩
      · rintro ⟨rfl | hq,hqp⟩
        · omega
        · exact ⟨hq,hqp⟩
    rw [leaves, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨pre,p,hchosen,hbound,hp,hpre,hrest⟩ := ih r l hdesc' hr hl hstop
      exact ⟨pre,p,hchosen,hbound,List.mem_cons_of_mem a hp,hpre,extend p hp _ hrest⟩
    · split_ifs at hl with h
      · simp only [List.mem_singleton] at hl
        subst l
        refine ⟨[],a,rfl,by simpa using hr,List.mem_cons_self,by simp,?_⟩
        intro q
        change q ∈ ps ↔ q ∈ a::ps ∧ q < a
        simp only [List.mem_cons]
        constructor
        · intro hq
          exact ⟨Or.inr hq,hhead q hq⟩
        · rintro ⟨rfl | hq,hqa⟩
          · omega
          · exact hq
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hl
        obtain ⟨pre,p,hchosen,hbound,hp,hpre,hrest⟩ :=
          ih (r*a) b hdesc' (Nat.le_of_not_gt h) hb hstop
        refine ⟨a::pre,p,?_,?_,List.mem_cons_of_mem a hp,?_,extend p hp _ hrest⟩
        · simpa only [Leaf.prepend, List.cons_append] using congrArg (List.cons a) hchosen
        · simpa only [List.prod_cons, Nat.mul_assoc] using hbound
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hhead p hp
          · exact hpre q hq

/-- On the prime candidate list, the untouched tail is exactly the
original residual roughness predicate at the last selected prime. -/
theorem stopped_roughMask (R r y : ℕ) (l : Leaf) (hr : r ≤ R)
    (hl : l ∈ leaves R r (primeList y)) (hstop : l.stopped = true) :
    ∃ (pre : List ℕ) (p : ℕ), l.chosen = pre++[p] ∧ r*pre.prod ≤ R ∧
      p.Prime ∧ p < y ∧ (∀ q ∈ l.chosen, p ≤ q) ∧
      ∀ n, roughMask l.remaining n = roughIndicator p n := by
  obtain ⟨pre,p,hchosen,hbound,hp,hpre,hrest⟩ :=
    stopped_prefix R r (primeList y) l (primeList_descending y) hr hl hstop
  obtain ⟨hpy,hprime⟩ := (mem_primeList y p).mp hp
  refine ⟨pre,p,hchosen,hbound,hprime,hpy,?_,?_⟩
  · intro q hq
    rw [hchosen, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact (hpre q hq).le
    · exact le_rfl
  · intro n
    classical
    rw [roughMask_eq_indicator]
    unfold roughIndicator
    have he : (∀ q ∈ l.remaining, ¬q ∣ n) ↔ Erdos387.IsZRough p n := by
      constructor
      · intro hh q hq hqp
        exact hh q ((hrest q).mpr ⟨(mem_primeList y q).mpr ⟨hqp.trans hpy,hq⟩,hqp⟩)
      · intro hh q hq
        obtain ⟨hqmem,hqp⟩ := (hrest q).mp hq
        exact hh q ((mem_primeList y q).mp hqmem).2 hqp
    simp only [he]

/-- Dividing out primes all at least p leaves roughness below p unchanged.
The division is exact, as required by the original factorization n=u*m. -/
theorem roughIndicator_div_prod (ps : List ℕ) (n p : ℕ)
    (hprime : ∀ q ∈ ps, q.Prime) (hlower : ∀ q ∈ ps, p ≤ q) (hdvd : ps.prod ∣ n) :
    roughIndicator p n = roughIndicator p (n/ps.prod) := by
  classical
  have he : Erdos387.IsZRough p n ↔ Erdos387.IsZRough p (n/ps.prod) := by
    have hd (q : ℕ) (hq : q.Prime) (hqp : q < p) : q ∣ n ↔ q ∣ n/ps.prod := by
      have hcop : Nat.Coprime q ps.prod := Nat.coprime_list_prod_right_iff.mpr (by
        intro v hv
        exact (Nat.coprime_primes hq (hprime v hv)).mpr (by
          have hvp := hlower v hv
          omega))
      conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
      exact hcop.dvd_mul_left
    constructor
    · intro h q hq hqp hdq
      exact h q hq hqp ((hd q hq hqp).mpr hdq)
    · intro h q hq hqp hdq
      exact h q hq hqp ((hd q hq hqp).mp hdq)
  unfold roughIndicator
  simp only [he]

/-- Exact Type-I leaf contribution, with its original divisibility mask. -/
theorem typeI_value (R r y : ℕ) (l : Leaf) (hr : r ≤ R)
    (hl : l ∈ leaves R r (primeList y)) (hstop : l.stopped = false) (n : ℕ) :
    l.value n = if l.chosen.prod ∣ n then (-1 : ℂ)^l.chosen.length else 0 := by
  obtain ⟨hnd,hprime,_⟩ := chosen_prime_data R r y l hl
  have hrem := (leaf_domain R r y (primeList y) l hr
    (fun p hp => ((mem_primeList y p).mp hp).1.le) hl).1 hstop |>.1
  unfold Leaf.value
  rw [divisorMask_eq_indicator l.chosen n hnd hprime, hrem]
  by_cases hd : l.chosen.prod ∣ n <;> simp [hd,roughMask]

/-- Exact Type-II leaf contribution, retaining rho(n/u,p_last). -/
theorem typeII_value (R r y : ℕ) (l : Leaf) (hr : r ≤ R)
    (hl : l ∈ leaves R r (primeList y)) (hstop : l.stopped = true) :
    ∃ (pre : List ℕ) (p : ℕ), l.chosen = pre++[p] ∧ r*pre.prod ≤ R ∧
      p.Prime ∧ p < y ∧ ∀ n,
      l.value n = if l.chosen.prod ∣ n then
        (-1 : ℂ)^l.chosen.length * roughIndicator p (n/l.chosen.prod) else 0 := by
  obtain ⟨pre,p,hchosen,hbound,hprime,hpy,hlower,hrest⟩ :=
    stopped_roughMask R r y l hr hl hstop
  obtain ⟨hnd,hprime',_⟩ := chosen_prime_data R r y l hl
  refine ⟨pre,p,hchosen,hbound,hprime,hpy,?_⟩
  intro n
  unfold Leaf.value
  rw [divisorMask_eq_indicator l.chosen n hnd hprime', hrest]
  by_cases hd : l.chosen.prod ∣ n
  · simp only [hd, if_true, mul_one]
    rw [roughIndicator_div_prod l.chosen n p hprime' hlower hd]
  · simp [hd]

/-- Different stopping-tree leaves have different selected prime lists. -/
theorem chosen_nodup (R r : ℕ) (ps : List ℕ) (hnd : ps.Nodup) :
    ((leaves R r ps).map Leaf.chosen).Nodup := by
  induction ps generalizing r with
  | nil => simp [leaves]
  | cons p ps ih =>
    obtain ⟨hp,hnd'⟩ := List.nodup_cons.mp hnd
    have hleft := ih r hnd'
    have hexclude (a : List ℕ) (ha : a ∈ (leaves R r ps).map Leaf.chosen) : p ∉ a := by
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp ha
      exact fun hpl => hp ((chosen_sublist R r ps l hl).subset hpl)
    rw [leaves, List.map_append]
    split_ifs with h
    · apply List.Nodup.append hleft (by simp)
      rw [List.disjoint_left]
      intro a ha hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      exact hexclude a ha (by rw [hb]; simp)
    · have heq : (((leaves R (r*p) ps).map (Leaf.prepend p)).map Leaf.chosen) =
          ((leaves R (r*p) ps).map Leaf.chosen).map (List.cons p) := by
        simp only [List.map_map, Function.comp_def, Leaf.prepend]
      rw [heq]
      apply List.Nodup.append hleft ((ih (r*p) hnd').map (by intro a b h; exact (List.cons.inj h).2))
      rw [List.disjoint_left]
      intro a ha hb
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hb
      exact hexclude (p::b) ha (List.mem_cons_self)

/-- Unique prime factorization and descending order make the selected
product injective. Thus later grouping by u cannot sum many sign
coefficients into an unbounded coefficient. -/
theorem chosen_prod_injective (R r y : ℕ) (a b : Leaf)
    (ha : a ∈ leaves R r (primeList y)) (hb : b ∈ leaves R r (primeList y))
    (heq : a.chosen.prod = b.chosen.prod) : a = b := by
  have hasub := chosen_sublist R r (primeList y) a ha
  have hbsub := chosen_sublist R r (primeList y) b hb
  have haprime := (chosen_prime_data R r y a ha).2.1
  have hbprime := (chosen_prime_data R r y b hb).2.1
  have hlists : a.chosen = b.chosen := by
    apply List.Pairwise.eq_of_mem_iff
      ((primeList_descending y).sublist hasub) ((primeList_descending y).sublist hbsub)
    intro p
    constructor
    · intro hp
      apply mem_list_primes_of_dvd_prod (Nat.prime_iff.mp (haprime p hp))
        (fun q hq => Nat.prime_iff.mp (hbprime q hq))
      rw [← heq]
      exact List.dvd_prod hp
    · intro hp
      apply mem_list_primes_of_dvd_prod (Nat.prime_iff.mp (hbprime p hp))
        (fun q hq => Nat.prime_iff.mp (haprime q hq))
      rw [heq]
      exact List.dvd_prod hp
  exact List.inj_on_of_nodup_map (chosen_nodup R r (primeList y) (primeList_nodup y)) ha hb hlists

/-- The source's Type-II length lower bound follows from stopping at R=y. -/
theorem typeII_length_two (y : ℕ) (hy : 1 ≤ y) (l : Leaf)
    (hl : l ∈ leaves y 1 (primeList y)) (hstop : l.stopped = true) :
    2 ≤ l.chosen.length := by
  have hlarge := ((e5_leaf_domain y hy l hl).2 hstop).1
  have hsub := chosen_sublist y 1 (primeList y) l hl
  cases he : l.chosen with
  | nil => simp [he] at hlarge; omega
  | cons p ps =>
    cases ps with
    | nil =>
      have hp : p ∈ l.chosen := by simp [he]
      have hpy := ((mem_primeList y p).mp (hsub.subset hp)).1
      simp only [he, List.prod_cons, List.prod_nil, mul_one] at hlarge
      omega
    | cons q qs => simp

/-- Exact quotient-domain membership, including both interval endpoints
and all original predicates on the product. -/
theorem mul_mem_divisor_domain (A B u m : ℕ) (hu : 0 < u)
    (P : ℕ → Prop) [DecidablePred P] :
    u*m ∈ (Finset.Ioc A B).filter (fun n => u ∣ n ∧ P n) ↔
      m ∈ (Finset.Ioc (A/u) (B/u)).filter (fun m => P (u*m)) := by
  have hlo : A < u*m ↔ A/u < m := by rw [Nat.div_lt_iff_lt_mul hu, Nat.mul_comm m u]
  have hhi : u*m ≤ B ↔ m ≤ B/u := by rw [Nat.le_div_iff_mul_le hu, Nat.mul_comm m u]
  simp [Finset.mem_filter, Finset.mem_Ioc, hlo, hhi]

theorem divisor_domain_eq_image (A B u : ℕ) (hu : 0 < u)
    (P : ℕ → Prop) [DecidablePred P] :
    (Finset.Ioc A B).filter (fun n => u ∣ n ∧ P n) =
      ((Finset.Ioc (A/u) (B/u)).filter (fun m => P (u*m))).image (fun m => u*m) := by
  ext n
  constructor
  · intro hn
    obtain ⟨m,rfl⟩ := (Finset.mem_filter.mp hn).2.1
    exact Finset.mem_image.mpr ⟨m,(mul_mem_divisor_domain A B u m hu P).mp hn,rfl⟩
  · intro hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact (mul_mem_divisor_domain A B u m hu P).mpr hm

/-- Reindexing a leaf by n=u*m changes no original product-window or class
predicate. No approximate dyadic interval is substituted. -/
theorem sum_divisor_domain (A B u : ℕ) (hu : 0 < u)
    (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℂ) :
    (∑ n ∈ (Finset.Ioc A B).filter (fun n => u ∣ n ∧ P n), F n) =
      ∑ m ∈ (Finset.Ioc (A/u) (B/u)).filter (fun m => P (u*m)), F (u*m) := by
  rw [divisor_domain_eq_image A B u hu P, Finset.sum_image]
  intro a ha b hb hab
  exact Nat.eq_of_mul_eq_mul_left hu hab

/-- Exact Type-I interval sum: all original constraints are still evaluated
on the product u*m, and the coefficient has absolute value one. -/
theorem typeI_interval_sum (A B R r y : ℕ) (l : Leaf) (hr : r ≤ R)
    (hl : l ∈ leaves R r (primeList y)) (hstop : l.stopped = false)
    (P : ℕ → Prop) [DecidablePred P] (W : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc A B, if P n then l.value n*W n else 0) =
      (-1 : ℂ)^l.chosen.length *
        ∑ m ∈ (Finset.Ioc (A/l.chosen.prod) (B/l.chosen.prod)).filter
          (fun m => P (l.chosen.prod*m)), W (l.chosen.prod*m) := by
  have hu := (chosen_prime_data R r y l hl).2.2
  calc
    _ = ∑ n ∈ (Finset.Ioc A B).filter (fun n => l.chosen.prod ∣ n ∧ P n),
        (-1 : ℂ)^l.chosen.length * W n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      rw [typeI_value R r y l hr hl hstop n]
      by_cases hp : P n <;> by_cases hd : l.chosen.prod ∣ n <;> simp [hp,hd]
    _ = _ := by
      rw [sum_divisor_domain A B l.chosen.prod hu P, Finset.mul_sum]

/-- Exact Type-II interval sum. The residual rho(m,p_last) is retained;
no assertion of variable separation or arbitrary-weight cancellation is
made here. -/
theorem typeII_interval_sum (A B R r y : ℕ) (l : Leaf) (hr : r ≤ R)
    (hl : l ∈ leaves R r (primeList y)) (hstop : l.stopped = true)
    (P : ℕ → Prop) [DecidablePred P] (W : ℕ → ℂ) :
    ∃ (pre : List ℕ) (p : ℕ), l.chosen = pre++[p] ∧ r*pre.prod ≤ R ∧
      p.Prime ∧ p < y ∧
      (∑ n ∈ Finset.Ioc A B, if P n then l.value n*W n else 0) =
        (-1 : ℂ)^l.chosen.length *
          ∑ m ∈ (Finset.Ioc (A/l.chosen.prod) (B/l.chosen.prod)).filter
            (fun m => P (l.chosen.prod*m)), roughIndicator p m * W (l.chosen.prod*m) := by
  obtain ⟨pre,p,hchosen,hbound,hprime,hpy,hvalue⟩ := typeII_value R r y l hr hl hstop
  have hu := (chosen_prime_data R r y l hl).2.2
  refine ⟨pre,p,hchosen,hbound,hprime,hpy,?_⟩
  calc
    _ = ∑ n ∈ (Finset.Ioc A B).filter (fun n => l.chosen.prod ∣ n ∧ P n),
        (-1 : ℂ)^l.chosen.length * (roughIndicator p (n/l.chosen.prod) * W n) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      rw [hvalue n]
      by_cases hp : P n <;> by_cases hd : l.chosen.prod ∣ n <;> simp [hp,hd,mul_assoc]
    _ = _ := by
      rw [sum_divisor_domain A B l.chosen.prod hu P, Finset.mul_sum]
      simp only [Nat.mul_div_cancel_left _ hu]

/-- The original modulus mask separates into the two exact unit conditions
without losing either one. -/
theorem coprime_product_domain (A B u m Q : ℕ) (hu : 0 < u)
    (P : ℕ → Prop) [DecidablePred P] :
    u*m ∈ (Finset.Ioc A B).filter (fun n => u ∣ n ∧ Nat.Coprime n Q ∧ P n) ↔
      m ∈ Finset.Ioc (A/u) (B/u) ∧ Nat.Coprime u Q ∧ Nat.Coprime m Q ∧ P (u*m) := by
  rw [mul_mem_divisor_domain A B u m hu]
  simp only [Finset.mem_filter, Nat.coprime_mul_iff_left]
  tauto

/-- The largest prime coordinate of the actual error certificate is a
positive y-rough integer, independently of any phase estimate. -/
theorem certificate_largest_rough
    {B K n y medium second gap g : ℕ} {S : Erdos387.CoverBPZ.BPZSection6Input B K}
    (C : SeparatedCertificatePhase.CertificatePhaseData S n y medium second gap g) :
    0 < C.q C.i₀ ∧ Erdos387.IsZRough y (C.q C.i₀) := by
  have htwo : 2 ≤ C.q C.i₀ := C.terminal_prime.two_le.trans (C.largest C.j)
  have hshape : (C.q C.i₀).Prime ∧ y < C.q C.i₀ :=
    (C.shape C.i₀).resolve_left (by omega)
  refine ⟨by omega, ?_⟩
  intro p hp hpy hpd
  have he : p = C.q C.i₀ := ((hshape.1.dvd_iff_eq hp.ne_one).mp hpd).symm
  omega

noncomputable def roughDomain (S : Finset ℕ) (y : ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact S.filter (fun n => 0 < n ∧ Erdos387.IsZRough y n ∧ P n)

theorem mem_roughDomain (S : Finset ℕ) (y n : ℕ) (P : ℕ → Prop) :
    n ∈ roughDomain S y P ↔ n ∈ S ∧ 0 < n ∧ Erdos387.IsZRough y n ∧ P n := by
  classical
  exact Finset.mem_filter

/-- Relaxing primality is legitimate for a nonnegative counting weight
before any signed sieve or complex Fourier expansion. Every original
external predicate remains unchanged. -/
theorem nonnegative_prime_cover (S : Finset ℕ) (y : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (W : ℕ → ℝ) (hW : ∀ n ∈ S, 0 ≤ W n) :
    (∑ n ∈ S.filter (fun n => n.Prime ∧ y < n ∧ P n), W n) ≤
      ∑ n ∈ roughDomain S y P, W n := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnS,hprime,hyn,hP⟩ := Finset.mem_filter.mp hn
    apply (mem_roughDomain S y n P).mpr
    refine ⟨hnS,hprime.pos,?_,hP⟩
    intro p hp hpy hpd
    have he : p = n := ((hprime.dvd_iff_eq hp.ne_one).mp hpd).symm
    omega
  · intro n hn _
    exact hW n ((mem_roughDomain S y n P).mp hn).1

end Erdos387Proof.SeparatedBuchstabDecomposition

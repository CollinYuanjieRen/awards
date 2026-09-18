import CameronErdos.Statement

/-!
# Counting toolbox for the Cameron–Erdős campaign (JSP-000616)

This file collects the elementary counting definitions and lemmas used in Green's
proof of the Cameron–Erdős conjecture (Green, *The Cameron–Erdős conjecture*, 2004,
§4, pp. 7–8), namely:

* `CameronErdos.addTriples` / `CameronErdos.schurTriples` — the number of ordered
  additive (Schur) triples `(x, y, z) ∈ A³` with `x + y = z` (`Def_SchurTriples`);
* `CameronErdos.popularDiff` — the set `D(A, K)` of `K`-popular differences
  (`Def_PopularDifferences`);
* `Lem_OddCount` — the odd numbers of `[1, N]`, all of whose subsets are sum-free;
* `Lem_PairMatchingCount` — counting the sets avoiding a perfect matching;
* `Lem_EvenSetTriples` — dense subsets of the even numbers have many additive triples;
* `Lem8_PopularDiffBound` — Green's Lemma 8;
* `Lem9_DegreeCount` — Green's Lemma 9.
-/

open Finset
open scoped Pointwise

namespace CameronErdos

/-! ## Definitions -/

/-- `addTriples A` is the number of ordered additive (Schur) triples of `A`:
`#{(x, y, z) ∈ A³ : x + y = z}`.  Stated for an arbitrary additive structure with
decidable equality, so that it applies to `ℕ`, `ℤ` and `ZMod p` alike. -/
def addTriples {G : Type*} [Add G] [DecidableEq G] (A : Finset G) : ℕ :=
  #{t ∈ A ×ˢ A ×ˢ A | t.1 + t.2.1 = t.2.2}

/-- `schurTriples A = #{(x, y, z) ∈ A³ : x + y = z}`, the number of ordered additive
triples of a finite set of naturals. -/
def schurTriples (A : Finset ℕ) : ℕ :=
  #{t ∈ A ×ˢ A ×ˢ A | t.1 + t.2.1 = t.2.2}

@[simp] lemma schurTriples_eq_addTriples (A : Finset ℕ) : schurTriples A = addTriples A := rfl

/-- The `ZMod`-valued instance of `addTriples`, spelled out. -/
example (n : ℕ) (A : Finset (ZMod n)) :
    addTriples A = #{t ∈ A ×ˢ A ×ˢ A | t.1 + t.2.1 = t.2.2} := rfl

/-- `popularDiff A K = D(A, K)` is the set of `K`-popular differences of `A`: those `d`
having at least `K` representations `d = a - a'` with `a, a' ∈ A`. -/
noncomputable def popularDiff {G : Type*} [AddGroup G] [DecidableEq G] (A : Finset G) (K : ℝ) :
    Finset G :=
  {d ∈ A - A | K ≤ (#{q ∈ A ×ˢ A | q.1 - q.2 = d} : ℝ)}

/-- The number of representations of `d` as a difference of two elements of `A`. -/
def diffReps {G : Type*} [AddGroup G] [DecidableEq G] (A : Finset G) (d : G) : ℕ :=
  #{q ∈ A ×ˢ A | q.1 - q.2 = d}

section PopularDiff

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma popularDiff_eq (A : Finset G) (K : ℝ) :
    popularDiff A K = {d ∈ A - A | K ≤ (diffReps A d : ℝ)} := rfl

lemma mem_popularDiff_iff {A : Finset G} {K : ℝ} (hK : 0 < K) (d : G) :
    d ∈ popularDiff A K ↔ K ≤ (diffReps A d : ℝ) := by
  classical
  refine ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨?_, h⟩⟩
  have hpos : 0 < diffReps A d := by
    by_contra hc
    have : (diffReps A d : ℝ) = 0 := by
      simp [Nat.le_zero.1 (Nat.not_lt.1 hc)]
    rw [this] at h; exact absurd h (not_le.2 hK)
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_filter, Finset.mem_product] at hq
  exact Finset.mem_sub.2 ⟨q.1, hq.1.1, q.2, hq.1.2, hq.2⟩

/-- The representation counts of `d` and of `-d` agree. -/
lemma diffReps_neg (A : Finset G) (d : G) : diffReps A (-d) = diffReps A d := by
  classical
  refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hq
    rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨hq.1.2, hq.1.1⟩, by
      simp only at hq ⊢
      rw [← neg_sub, hq.2, neg_neg]⟩
  · rintro ⟨a, b⟩ _ ⟨c, e⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · rintro ⟨a, b⟩ hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    refine ⟨(b, a), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hq.1.2, hq.1.1⟩, by
      simp only at hq ⊢
      rw [← neg_sub, hq.2]⟩

lemma mem_sub_neg_iff {A : Finset G} {d : G} : -d ∈ A - A ↔ d ∈ A - A := by
  classical
  constructor <;> intro h <;> obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_sub.1 h
  · exact Finset.mem_sub.2 ⟨b, hb, a, ha, by rw [← neg_sub, hab, neg_neg]⟩
  · exact Finset.mem_sub.2 ⟨b, hb, a, ha, by rw [← neg_sub, hab]⟩

/-- `d` is `K`-popular if and only if `-d` is: `D(A, K) = -D(A, K)`. -/
lemma popularDiff_neg {A : Finset G} {K : ℝ} {d : G} :
    d ∈ popularDiff A K ↔ -d ∈ popularDiff A K := by
  classical
  simp only [popularDiff_eq, Finset.mem_filter, diffReps_neg]
  exact and_congr_left fun _ => mem_sub_neg_iff.symm

/-- `popularDiff` and its symmetry are available on `ZMod t`, as needed in later sections. -/
example (t : ℕ) (A : Finset (ZMod t)) (K : ℝ) (d : ZMod t) :
    d ∈ popularDiff A K ↔ -d ∈ popularDiff A K := popularDiff_neg

end PopularDiff


/-! ## `Lem_OddCount`: the all-odd subsets -/

/-- The odd numbers in `[1, N]` number `⌈N/2⌉ = (N + 1) / 2`. -/
lemma card_filter_odd_Icc (N : ℕ) : #{x ∈ Finset.Icc 1 N | Odd x} = (N + 1) / 2 := by
  have h : {x ∈ Finset.Icc 1 N | Odd x} = (Finset.range ((N + 1) / 2)).image (fun k => 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range, Nat.odd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, hodd⟩
      exact ⟨x / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [h, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]

/-- The even numbers in `[1, N]` number `⌊N/2⌋`. -/
lemma card_filter_even_Icc (N : ℕ) : #{x ∈ Finset.Icc 1 N | Even x} = N / 2 := by
  have h : {x ∈ Finset.Icc 1 N | Even x} = (Finset.range (N / 2)).image (fun k => 2 * k + 2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range,
      Nat.even_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, heven⟩
      exact ⟨x / 2 - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [h, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]

/-- Any set of odd numbers is sum-free. -/
lemma isSumFree_of_subset_odd {A : Finset ℕ} (hA : ∀ x ∈ A, Odd x) : IsSumFree A := by
  intro a ha b hb hab
  have := hA _ ha
  have := hA _ hb
  have := hA _ hab
  simp only [Nat.odd_iff] at *
  omega

/-- `Lem_OddCount`.  The odd numbers of `[1, N]` number `(N+1)/2 = ⌈N/2⌉`; every one of the
`2 ^ ⌈N/2⌉` subsets of this set is a sum-free subset of `[1, N]`. -/
theorem lem_oddCount (N : ℕ) :
    #{x ∈ Finset.Icc 1 N | Odd x} = (N + 1) / 2 ∧
      (#{x ∈ Finset.Icc 1 N | Odd x}.powerset = 2 ^ ((N + 1) / 2)) ∧
      ∀ A ∈ {x ∈ Finset.Icc 1 N | Odd x}.powerset, A ⊆ Finset.Icc 1 N ∧ IsSumFree A := by
  refine ⟨card_filter_odd_Icc N, ?_, ?_⟩
  · rw [Finset.card_powerset, card_filter_odd_Icc]
  · intro A hA
    rw [Finset.mem_powerset] at hA
    refine ⟨hA.trans (Finset.filter_subset _ _), isSumFree_of_subset_odd ?_⟩
    intro x hx
    exact (Finset.mem_filter.1 (hA hx)).2


/-! ## `Lem_PairMatchingCount`: counting the sets avoiding a matching -/

private lemma inter_union_sdiff_self {α : Type*} [DecidableEq α] (X P : Finset α) :
    X ∩ P ∪ X \ P = X := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- **`Lem_PairMatchingCount`.**  If `M` is a family of pairwise disjoint two-element subsets
of a finite set `W`, then the number of subsets of `W` containing none of the members of `M`
entirely is `3 ^ |M| * 2 ^ (|W| - 2|M|)`. -/
theorem card_avoiding_matching {α : Type*} [DecidableEq α] (M : Finset (Finset α)) :
    ∀ W : Finset α, (∀ P ∈ M, P ⊆ W) → (∀ P ∈ M, #P = 2) →
      (M : Set (Finset α)).PairwiseDisjoint id →
      #{X ∈ W.powerset | ∀ P ∈ M, ¬ P ⊆ X} = 3 ^ #M * 2 ^ (#W - 2 * #M) := by
  classical
  induction M using Finset.induction_on with
  | empty =>
      intro W _ _ _
      simp [Finset.card_powerset]
  | insert P Ms hP ih =>
      intro W hsub hcard hdisj
      have hPW : P ⊆ W := hsub P (Finset.mem_insert_self _ _)
      have hPcard : #P = 2 := hcard P (Finset.mem_insert_self _ _)
      have hQdisj : ∀ Q ∈ Ms, Disjoint Q P := by
        intro Q hQ
        refine hdisj (by simp [hQ]) (by simp) ?_
        rintro rfl; exact hP hQ
      have hQsub : ∀ Q ∈ Ms, Q ⊆ W \ P := fun Q hQ =>
        Finset.subset_sdiff.2 ⟨hsub Q (Finset.mem_insert_of_mem hQ), hQdisj Q hQ⟩
      have ih' := ih (W \ P) hQsub (fun Q hQ => hcard Q (Finset.mem_insert_of_mem hQ))
        (hdisj.subset (by
          intro x hx
          simp only [Finset.coe_insert, Set.mem_insert_iff]
          exact Or.inr hx))
      have hbij :
          #{X ∈ W.powerset | ∀ Q ∈ insert P Ms, ¬ Q ⊆ X}
            = #((P.powerset.erase P) ×ˢ {Z ∈ (W \ P).powerset | ∀ Q ∈ Ms, ¬ Q ⊆ Z}) := by
        refine Finset.card_nbij' (fun X => (X ∩ P, X \ P)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_
        · intro X hX
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
            forall_eq_or_imp, Finset.mem_product, Finset.mem_erase] at hX ⊢
          obtain ⟨hXW, hXP, hXQ⟩ := hX
          refine ⟨⟨fun hEq => hXP (hEq ▸ Finset.inter_subset_left), Finset.inter_subset_right⟩,
            Finset.sdiff_subset_sdiff hXW (le_refl P), fun Q hQ hQsubX =>
              hXQ Q hQ (hQsubX.trans Finset.sdiff_subset)⟩
        · rintro ⟨Y, Z⟩ hYZ
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_erase, Finset.mem_powerset,
            Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp] at hYZ ⊢
          obtain ⟨⟨hYne, hYP⟩, hZW, hZQ⟩ := hYZ
          have hZdisj : Disjoint Z P := (Finset.subset_sdiff.1 hZW).2
          refine ⟨Finset.union_subset (hYP.trans hPW) (hZW.trans Finset.sdiff_subset), ?_, ?_⟩
          · intro hPYZ
            refine hYne (Finset.Subset.antisymm hYP ?_)
            intro x hx
            rcases Finset.mem_union.1 (hPYZ hx) with h | h
            · exact h
            · exact absurd hx (Finset.disjoint_left.1 hZdisj h)
          · intro Q hQ hQsub
            refine hZQ Q hQ fun x hx => ?_
            rcases Finset.mem_union.1 (hQsub hx) with h | h
            · exact absurd (hYP h) (Finset.disjoint_left.1 (hQdisj Q hQ) hx)
            · exact h
        · intro X _
          exact inter_union_sdiff_self X P
        · rintro ⟨Y, Z⟩ hYZ
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_erase, Finset.mem_powerset,
            Finset.mem_filter] at hYZ
          obtain ⟨⟨_, hYP⟩, hZW, _⟩ := hYZ
          have hZdisj : Disjoint Z P := (Finset.subset_sdiff.1 hZW).2
          have h1 : (Y ∪ Z) ∩ P = Y := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_union]
            refine ⟨?_, fun h => ⟨Or.inl h, hYP h⟩⟩
            rintro ⟨h | h, hxP⟩
            · exact h
            · exact absurd hxP (Finset.disjoint_left.1 hZdisj h)
          have h2 : (Y ∪ Z) \ P = Z := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_union]
            refine ⟨?_, fun h => ⟨Or.inr h, Finset.disjoint_left.1 hZdisj h⟩⟩
            rintro ⟨h | h, hxP⟩
            · exact absurd (hYP h) hxP
            · exact h
          exact Prod.ext h1 h2
      have hWP : #(W \ P) = #W - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hPW, hPcard]
      rw [hbij, Finset.card_product, ih', Finset.card_erase_of_mem (Finset.mem_powerset.2 le_rfl),
        Finset.card_powerset, hPcard, Finset.card_insert_of_notMem hP, hWP]
      have h3 : (2 : ℕ) ^ 2 - 1 = 3 := by norm_num
      rw [h3]
      have h4 : #W - 2 - 2 * #Ms = #W - 2 * (#Ms + 1) := by omega
      rw [h4]
      ring


/-- `Lem_PairMatchingCount`, indexed version: for pairwise disjoint two-element sets
`P 0, …, P (q-1) ⊆ W`, the number of `X ⊆ W` with `¬ P i ⊆ X` for every `i`
is `3 ^ q * 2 ^ (|W| - 2q)`. -/
theorem card_avoiding_matching_fin {α : Type*} [DecidableEq α] {q : ℕ} (W : Finset α)
    (P : Fin q → Finset α) (hsub : ∀ i, P i ⊆ W) (hcard : ∀ i, #(P i) = 2)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) :
    #{X ∈ W.powerset | ∀ i, ¬ P i ⊆ X} = 3 ^ q * 2 ^ (#W - 2 * q) := by
  classical
  have hinj : Function.Injective P := by
    intro i j hij
    by_contra hne
    have hd := hdisj i j hne
    rw [hij, disjoint_self, Finset.bot_eq_empty] at hd
    have h2 := hcard j
    rw [hd] at h2
    simp at h2
  set M : Finset (Finset α) := Finset.image P Finset.univ with hM
  have hMcard : #M = q := by
    rw [hM, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hMmem : ∀ Q, Q ∈ M ↔ ∃ i, P i = Q := by
    intro Q; rw [hM]; simp
  have hsets : {X ∈ W.powerset | ∀ i, ¬ P i ⊆ X} = {X ∈ W.powerset | ∀ Q ∈ M, ¬ Q ⊆ X} := by
    ext X
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · intro h Q hQ
      obtain ⟨i, rfl⟩ := (hMmem Q).1 hQ
      exact h i
    · intro h i
      exact h _ ((hMmem _).2 ⟨i, rfl⟩)
  rw [hsets, card_avoiding_matching M W ?_ ?_ ?_, hMcard]
  · intro Q hQ; obtain ⟨i, rfl⟩ := (hMmem Q).1 hQ; exact hsub i
  · intro Q hQ; obtain ⟨i, rfl⟩ := (hMmem Q).1 hQ; exact hcard i
  · intro Q1 hQ1 Q2 hQ2 hne
    obtain ⟨i, rfl⟩ := (hMmem Q1) |>.1 (by simpa using hQ1)
    obtain ⟨j, rfl⟩ := (hMmem Q2) |>.1 (by simpa using hQ2)
    exact hdisj i j (fun h => hne (by rw [h]))


/-! ## `Lem_EvenSetTriples`: dense subsets of the even numbers have many additive triples -/

/-- Core counting step.  If `H ⊆ E ⊆ W` and every sum of two elements of `H` lies in `W`,
then the `|H|²` ordered pairs from `H` split into ones producing an additive triple of `E`
and ones whose sum lies in `W \ E`; the latter number at most `|W \ E| · |H|`. -/
lemma sq_card_le_addTriples {W E H : Finset ℕ} (_hEW : E ⊆ W) (hHE : H ⊆ E)
    (hsum : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ W) :
    #H * #H ≤ addTriples E + #(W \ E) * #H := by
  classical
  have hsplit : #{q ∈ H ×ˢ H | q.1 + q.2 ∈ E} + #{q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)}
      = #(H ×ˢ H) := Finset.card_filter_add_card_filter_not _
  have hgood : #{q ∈ H ×ˢ H | q.1 + q.2 ∈ E} ≤ addTriples E := by
    refine Finset.card_le_card_of_injOn (fun q => (q.1, q.2, q.1 + q.2)) ?_ ?_
    · intro q hq
      have hq' : q ∈ {q ∈ H ×ˢ H | q.1 + q.2 ∈ E} := hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq'
      show (q.1, q.2, q.1 + q.2) ∈ {t ∈ E ×ˢ E ×ˢ E | t.1 + t.2.1 = t.2.2}
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hHE hq'.1.1, hHE hq'.1.2, hq'.2⟩, trivial⟩
    · intro a _ b _ hab
      have hab' : (a.1, a.2, a.1 + a.2) = (b.1, b.2, b.1 + b.2) := hab
      exact Prod.ext (congrArg (fun t : ℕ × ℕ × ℕ => t.1) hab')
        (congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) hab')
  have hbad : #{q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)} ≤ #(W \ E) * #H := by
    have hfib : #{q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)}
        = ∑ v ∈ W \ E, #{q ∈ {q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)} | q.1 + q.2 = v} := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro q hq
      have hq' : q ∈ {q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)} := hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq'
      exact Finset.mem_sdiff.2 ⟨hsum _ hq'.1.1 _ hq'.1.2, hq'.2⟩
    rw [hfib]
    calc ∑ v ∈ W \ E, #{q ∈ {q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)} | q.1 + q.2 = v}
        ≤ ∑ _v ∈ W \ E, #H := by
          refine Finset.sum_le_sum fun v _ => ?_
          refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
          · intro q hq
            have hq' : q ∈ {q ∈ {q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)} | q.1 + q.2 = v} := hq
            simp only [Finset.mem_filter, Finset.mem_product] at hq'
            exact hq'.1.1.1
          · intro a ha b hb hab
            have ha' : a ∈ {q ∈ {q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)} | q.1 + q.2 = v} := ha
            have hb' : b ∈ {q ∈ {q ∈ H ×ˢ H | ¬ (q.1 + q.2 ∈ E)} | q.1 + q.2 = v} := hb
            simp only [Finset.mem_filter] at ha' hb'
            have hs : a.1 + a.2 = b.1 + b.2 := by rw [ha'.2, hb'.2]
            exact Prod.ext hab (by omega)
      _ = #(W \ E) * #H := by rw [Finset.sum_const, smul_eq_mul]
  have hprod : #(H ×ˢ H) = #H * #H := Finset.card_product _ _
  omega

/-- **`Lem_EvenSetTriples`.**  For `N ≥ 100`, any subset `E` of the even numbers of `[1, N]`
with `|E| ≥ 12N/25` has at least `N²/100` ordered additive triples.  (The proof in fact
gives the constant `(23N - 75)(21N - 75)/10⁴ ≥ 0.045 N²`.) -/
theorem lem_evenSetTriples {N : ℕ} (hN : 100 ≤ N) {E : Finset ℕ}
    (hE : E ⊆ {x ∈ Finset.Icc 1 N | Even x}) (hEcard : (12 * N : ℝ) / 25 ≤ #E) :
    ((N : ℝ) ^ 2) / 100 ≤ (schurTriples E : ℝ) := by
  classical
  rw [schurTriples_eq_addTriples]
  set W : Finset ℕ := {x ∈ Finset.Icc 1 N | Even x} with hW
  set H : Finset ℕ := {x ∈ E | 2 * x ≤ N} with hH
  have hWcard : #W = N / 2 := card_filter_even_Icc N
  have hHE : H ⊆ E := Finset.filter_subset _ _
  have hsum : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ W := by
    intro x hx y hy
    rw [hH, Finset.mem_filter] at hx hy
    have hx' := hE hx.1
    have hy' := hE hy.1
    rw [hW, Finset.mem_filter, Finset.mem_Icc] at hx' hy' ⊢
    rw [Nat.even_iff] at hx' hy' ⊢
    omega
  have hsmall : {x ∈ W | 2 * x ≤ N} = {x ∈ Finset.Icc 1 (N / 2) | Even x} := by
    ext x
    simp only [hW, Finset.mem_filter, Finset.mem_Icc, Nat.even_iff]
    omega
  have hsplitW : #{x ∈ W | 2 * x ≤ N} + #{x ∈ W | ¬ (2 * x ≤ N)} = #W :=
    Finset.card_filter_add_card_filter_not _
  have hsmallcard : #{x ∈ W | 2 * x ≤ N} = N / 2 / 2 := by
    rw [hsmall, card_filter_even_Icc]
  have hbigcard : #{x ∈ W | ¬ (2 * x ≤ N)} = N / 2 - N / 2 / 2 := by omega
  have hsplitE : #{x ∈ E | 2 * x ≤ N} + #{x ∈ E | ¬ (2 * x ≤ N)} = #E :=
    Finset.card_filter_add_card_filter_not _
  rw [← hH] at hsplitE
  have hEbig : #{x ∈ E | ¬ (2 * x ≤ N)} ≤ #{x ∈ W | ¬ (2 * x ≤ N)} :=
    Finset.card_le_card (Finset.filter_subset_filter _ hE)
  have hHcard : #E ≤ #H + (N / 2 - N / 2 / 2) := by omega
  have hWEcard : #(W \ E) = N / 2 - #E := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hE, hWcard]
  have hEle : #E ≤ N / 2 := by
    rw [← hWcard]; exact Finset.card_le_card hE
  have hkey := sq_card_le_addTriples hE hHE hsum
  rw [hWEcard] at hkey
  -- real arithmetic
  have hn100 : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hhalf : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    have h2 : (N / 2) * 2 ≤ N := by omega
    have : ((N / 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hquarter : ((N : ℝ) - 3) / 4 ≤ ((N / 2 / 2 : ℕ) : ℝ) := by
    have h4 : N ≤ (N / 2 / 2) * 4 + 3 := by omega
    have : (N : ℝ) ≤ ((N / 2 / 2 : ℕ) : ℝ) * 4 + 3 := by exact_mod_cast h4
    linarith
  have hcast1 : (#H : ℝ) * (#H : ℝ)
      ≤ (addTriples E : ℝ) + (((N / 2 : ℕ) : ℝ) - (#E : ℝ)) * (#H : ℝ) := by
    have h0 : ((N / 2 - #E : ℕ) : ℝ) = ((N / 2 : ℕ) : ℝ) - (#E : ℝ) := Nat.cast_sub hEle
    calc (#H : ℝ) * (#H : ℝ) = ((#H * #H : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((addTriples E + (N / 2 - #E) * #H : ℕ) : ℝ) := by exact_mod_cast hkey
      _ = (addTriples E : ℝ) + ((N / 2 - #E : ℕ) : ℝ) * (#H : ℝ) := by
          rw [Nat.cast_add, Nat.cast_mul]
      _ = (addTriples E : ℝ) + (((N / 2 : ℕ) : ℝ) - (#E : ℝ)) * (#H : ℝ) := by rw [h0]
  have hcast2 : (#E : ℝ) ≤ (#H : ℝ) + (((N / 2 : ℕ) : ℝ) - ((N / 2 / 2 : ℕ) : ℝ)) := by
    have hle : N / 2 / 2 ≤ N / 2 := Nat.div_le_self _ _
    have h0 : ((N / 2 - N / 2 / 2 : ℕ) : ℝ) = ((N / 2 : ℕ) : ℝ) - ((N / 2 / 2 : ℕ) : ℝ) :=
      Nat.cast_sub hle
    have hc : ((#E : ℕ) : ℝ) ≤ ((#H + (N / 2 - N / 2 / 2) : ℕ) : ℝ) := by exact_mod_cast hHcard
    rw [Nat.cast_add, h0] at hc
    linarith
  have hhlow : (23 * (N : ℝ) - 75) / 100 ≤ (#H : ℝ) := by linarith
  have hDle : ((N / 2 : ℕ) : ℝ) - (#E : ℝ) ≤ (N : ℝ) / 50 := by linarith
  have hmul : (23 * (N : ℝ) - 75) / 100 * ((23 * (N : ℝ) - 75) / 100 - (N : ℝ) / 50)
      ≤ (#H : ℝ) * ((#H : ℝ) - (((N / 2 : ℕ) : ℝ) - (#E : ℝ))) :=
    mul_le_mul hhlow (by linarith) (by linarith) (by linarith)
  have hfinal : (N : ℝ) ^ 2 / 100
      ≤ (23 * (N : ℝ) - 75) / 100 * ((23 * (N : ℝ) - 75) / 100 - (N : ℝ) / 50) := by
    nlinarith [hn100, sq_nonneg ((N : ℝ) - 100)]
  nlinarith [hcast1, hmul, hfinal]


/-! ## Green's Lemma 8 -/

section Lemma89

variable {N : ℕ} {A : Finset ℤ}

private lemma card_Icc_one_N (N : ℕ) : #(Finset.Icc (1 : ℤ) (N : ℤ)) = N := by
  rw [Int.card_Icc]; omega

/-- The positive `K`-popular differences of `A`. -/
private noncomputable def posPopular (A : Finset ℤ) (K : ℝ) : Finset ℤ :=
  {d ∈ popularDiff A K | 0 < d}

/-- `|D(A, K)| ≤ 2 |D(A, K) ∩ ℤ_{>0}| + 1`: the popular differences come in pairs `±d`,
with the possible exception of `0`. -/
private lemma card_popularDiff_le (A : Finset ℤ) (K : ℝ) :
    #(popularDiff A K) ≤ 2 * #(posPopular A K) + 1 := by
  classical
  have hsub : popularDiff A K ⊆
      (posPopular A K ∪ (posPopular A K).image (fun d => -d)) ∪ {0} := by
    intro d hd
    rcases lt_trichotomy d 0 with h | h | h
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_image.2 ⟨-d, ?_, by ring⟩
      exact Finset.mem_filter.2 ⟨popularDiff_neg.1 hd, by omega⟩
    · exact Finset.mem_union_right _ (by simp [h])
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hd, h⟩))
  calc #(popularDiff A K)
      ≤ #((posPopular A K ∪ (posPopular A K).image (fun d => -d)) ∪ {0}) :=
        Finset.card_le_card hsub
    _ ≤ #(posPopular A K ∪ (posPopular A K).image (fun d => -d)) + #({0} : Finset ℤ) :=
        Finset.card_union_le _ _
    _ ≤ (#(posPopular A K) + #((posPopular A K).image (fun d => -d))) + 1 := by
        simpa using Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ 2 * #(posPopular A K) + 1 := by
        have := Finset.card_image_le (s := posPopular A K) (f := fun d : ℤ => -d)
        omega

/-- At most `√ε N` positive popular differences lie in `A`. -/
private lemma card_posPopular_mem_le (_hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε)
    (hNpos : 0 < N) (htr : (addTriples A : ℝ) ≤ ε * (N : ℝ) ^ 2) :
    (#{d ∈ posPopular A (Real.sqrt ε * N) | d ∈ A} : ℝ) ≤ Real.sqrt ε * N := by
  classical
  set K : ℝ := Real.sqrt ε * N with hK
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hKpos : 0 < K := by positivity
  set Q : Finset ℤ := {d ∈ posPopular A K | d ∈ A} with hQ
  set R : Finset (ℤ × ℤ) := {q ∈ A ×ˢ A | q.1 - q.2 ∈ Q} with hR
  -- every fibre of `R` over `Q` is large
  have hfib : #R = ∑ d ∈ Q, #{q ∈ R | q.1 - q.2 = d} := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro q hq
    have hq' : q ∈ R := hq
    rw [hR, Finset.mem_filter] at hq'
    exact hq'.2
  have hfibeq : ∀ d ∈ Q, {q ∈ R | q.1 - q.2 = d} = {q ∈ A ×ˢ A | q.1 - q.2 = d} := by
    intro d hd
    ext q
    simp only [hR, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hd⟩, h3⟩
  have hlarge : ∀ d ∈ Q, K ≤ (#{q ∈ R | q.1 - q.2 = d} : ℝ) := by
    intro d hd
    rw [hfibeq d hd]
    have hdD : d ∈ popularDiff A K := by
      rw [hQ, Finset.mem_filter] at hd
      exact (Finset.mem_filter.1 hd.1).1
    exact (mem_popularDiff_iff hKpos d).1 hdD
  have hsum : (#Q : ℝ) * K ≤ (#R : ℝ) := by
    have : (#Q : ℝ) * K = ∑ _d ∈ Q, K := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [this, hfib]
    push_cast
    exact Finset.sum_le_sum hlarge
  -- `R` injects into the additive triples of `A`
  have hRle : #R ≤ addTriples A := by
    refine Finset.card_le_card_of_injOn (fun q => (q.2, q.1 - q.2, q.1)) ?_ ?_
    · intro q hq
      have hq' : q ∈ R := hq
      rw [hR, Finset.mem_filter, Finset.mem_product] at hq'
      have hmem : q.1 - q.2 ∈ A := by
        rw [hQ, Finset.mem_filter] at hq'
        exact hq'.2.2
      show (q.2, q.1 - q.2, q.1) ∈ {t ∈ A ×ˢ A ×ˢ A | t.1 + t.2.1 = t.2.2}
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hq'.1.2, hmem, hq'.1.1⟩, by ring⟩
    · intro a _ b _ hab
      have hab' : (a.2, a.1 - a.2, a.1) = (b.2, b.1 - b.2, b.1) := hab
      exact Prod.ext (congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) hab')
        (congrArg (fun t : ℤ × ℤ × ℤ => t.1) hab')
  -- conclude
  have hRR : (#R : ℝ) ≤ ε * (N : ℝ) ^ 2 :=
    le_trans (by exact_mod_cast hRle) htr
  have hεN : ε * (N : ℝ) ^ 2 = K * K := by
    rw [hK]
    have : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    nlinarith [this]
  have : (#Q : ℝ) * K ≤ K * K := by rw [← hεN]; linarith
  exact le_of_mul_le_mul_right (by linarith) hKpos

/-- Core of Lemma 8: the number of **positive** `√ε N`-popular differences of `A` is at most
`√ε N + (N - |A|)`. -/
private lemma card_posPopular_le (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε)
    (htr : (addTriples A : ℝ) ≤ ε * (N : ℝ) ^ 2) :
    (#(posPopular A (Real.sqrt ε * N)) : ℝ) ≤ Real.sqrt ε * N + ((N : ℝ) - #A) := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hAempty : A = ∅ := by
      have h0 : Finset.Icc (1 : ℤ) ((0 : ℕ) : ℤ) = ∅ := by
        apply Finset.Icc_eq_empty; norm_num
      rw [h0] at hA
      exact Finset.subset_empty.1 hA
    subst hAempty
    simp [posPopular, popularDiff]
  set K : ℝ := Real.sqrt ε * N with hK
  set Dp : Finset ℤ := posPopular A K with hDp
  have hAle : #A ≤ N := by
    have := Finset.card_le_card hA
    rwa [card_Icc_one_N] at this
  have hout : {d ∈ Dp | d ∉ A} ⊆ Finset.Icc (1 : ℤ) (N : ℤ) \ A := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have hdD : d ∈ popularDiff A K := (Finset.mem_filter.1 hd.1).1
    have hdpos : 0 < d := (Finset.mem_filter.1 hd.1).2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_sub.1 (Finset.mem_filter.1 hdD).1
    have ha' := Finset.mem_Icc.1 (hA ha)
    have hb' := Finset.mem_Icc.1 (hA hb)
    refine Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨hdpos, ?_⟩, hd.2⟩
    omega
  have houtcard : #{d ∈ Dp | d ∉ A} ≤ N - #A := by
    have h1 := Finset.card_le_card hout
    rwa [Finset.card_sdiff, Finset.inter_eq_left.2 hA, card_Icc_one_N] at h1
  have hsplit : #{d ∈ Dp | d ∈ A} + #{d ∈ Dp | d ∉ A} = #Dp :=
    Finset.card_filter_add_card_filter_not _
  have hQle := card_posPopular_mem_le hA hε hNpos htr
  rw [← hK, ← hDp] at hQle
  have h1 : (#{d ∈ Dp | d ∉ A} : ℝ) ≤ (N : ℝ) - (#A : ℝ) := by
    have hc : ((N - #A : ℕ) : ℝ) = (N : ℝ) - (#A : ℝ) := Nat.cast_sub hAle
    calc (#{d ∈ Dp | d ∉ A} : ℝ) ≤ ((N - #A : ℕ) : ℝ) := by exact_mod_cast houtcard
      _ = (N : ℝ) - (#A : ℝ) := hc
  have h2 : ((#{d ∈ Dp | d ∈ A} : ℕ) : ℝ) + ((#{d ∈ Dp | d ∉ A} : ℕ) : ℝ) = (#Dp : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsplit
  linarith

/-- **`Lem8_PopularDiffBound`** (Green, Lemma 8, inequality (14)).  If `A ⊆ [N]` has at most
`ε N²` additive triples then `⌊|D(A, √ε N)| / 2⌋ + |A| ≤ N (1 + 2 √ε)`.

The halving here is *integer* halving: `⌊|D| / 2⌋` is exactly the number of positive popular
differences.  With exact real halving the inequality can fail by `1/2` when `0` is itself a
popular difference: take `N = 101`, `A` the odd numbers of `[1, 101]` (so `|A| = 51` and `A`
has no additive triple) and `ε = 10⁻⁶`; then `D = A - A` has `101` elements and
`|D|/2 + |A| = 101.5 > 101.202 = N(1 + 2√ε)`.  See `lem8_card_popularDiff_le` for the
real-valued form, which carries the corresponding `+ 1`. -/
theorem lem8_popularDiffBound (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε)
    (htr : (addTriples A : ℝ) ≤ ε * (N : ℝ) ^ 2) :
    ((#(popularDiff A (Real.sqrt ε * N)) / 2 + #A : ℕ) : ℝ)
      ≤ (N : ℝ) * (1 + 2 * Real.sqrt ε) := by
  classical
  have hsqrt0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcore := card_posPopular_le hA hε htr
  have hhalf : #(popularDiff A (Real.sqrt ε * N)) / 2 ≤ #(posPopular A (Real.sqrt ε * N)) := by
    have := card_popularDiff_le A (Real.sqrt ε * N)
    omega
  have hfinal : ((#(popularDiff A (Real.sqrt ε * N)) / 2 + #A : ℕ) : ℝ)
      ≤ (#(posPopular A (Real.sqrt ε * N)) : ℝ) + (#A : ℝ) := by
    push_cast
    have : ((#(popularDiff A (Real.sqrt ε * N)) / 2 : ℕ) : ℝ)
        ≤ (#(posPopular A (Real.sqrt ε * N)) : ℝ) := by exact_mod_cast hhalf
    linarith
  nlinarith [hfinal, hcore]

/-- Lemma 8 in real-valued form: `|D(A, √ε N)| ≤ 2 (√ε N + N - |A|) + 1`.  The `+ 1`
accounts for the difference `0`, which is popular as soon as `|A| ≥ √ε N`. -/
theorem lem8_card_popularDiff_le (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε)
    (htr : (addTriples A : ℝ) ≤ ε * (N : ℝ) ^ 2) :
    (#(popularDiff A (Real.sqrt ε * N)) : ℝ)
      ≤ 2 * (Real.sqrt ε * N + ((N : ℝ) - #A)) + 1 := by
  have hcore := card_posPopular_le hA hε htr
  have hcard := card_popularDiff_le A (Real.sqrt ε * N)
  have : (#(popularDiff A (Real.sqrt ε * N)) : ℝ)
      ≤ 2 * (#(posPopular A (Real.sqrt ε * N)) : ℝ) + 1 := by exact_mod_cast hcard
  linarith

/-! ## Green's Lemma 9 -/

/-- **`Lem9_DegreeCount`** (Green, Lemma 9).  If `A ⊆ [N]`, then for all but at most
`4 ε^{1/4} N` elements `a ∈ A`, at least `|A| - 16 ε^{1/4} N` of the differences `a - a'`
(`a' ∈ A`) are `32 √ε N`-popular.

Green states the exceptional set as `8 ε^{1/4} N`; the degree count actually gives the
constant `4`, which is what is proved here (and which implies Green's statement).  The
hypothesis `A` has at most `ε N²` additive triples is *not* needed for this step. -/
theorem lem9_degreeCount (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    (#{a ∈ A | (#{a' ∈ A | a - a' ∈ popularDiff A (32 * Real.sqrt ε * N)} : ℝ)
          < (#A : ℝ) - 16 * Real.sqrt (Real.sqrt ε) * (N : ℝ)} : ℝ)
      ≤ 4 * Real.sqrt (Real.sqrt ε) * (N : ℝ) := by
  classical
  set η : ℝ := Real.sqrt (Real.sqrt ε) with hη
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hηpos : 0 < η := Real.sqrt_pos.2 hsq
  have hηsq : η * η = Real.sqrt ε := Real.mul_self_sqrt (Real.sqrt_nonneg ε)
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hAempty : A = ∅ := by
      have h0 : Finset.Icc (1 : ℤ) ((0 : ℕ) : ℤ) = ∅ := by
        apply Finset.Icc_eq_empty; norm_num
      rw [h0] at hA
      exact Finset.subset_empty.1 hA
    subst hAempty
    simp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set K : ℝ := 32 * Real.sqrt ε * (N : ℝ) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  set D : Finset ℤ := popularDiff A K with hD
  set bad : Finset (ℤ × ℤ) := {q ∈ A ×ˢ A | q.1 - q.2 ∉ D} with hbad
  -- Step 1: at most `2N` differences, each with fewer than `K` representations
  have hrange : ∀ q ∈ bad, q.1 - q.2 ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1) := by
    intro q hq
    rw [hbad, Finset.mem_filter, Finset.mem_product] at hq
    have h1 := Finset.mem_Icc.1 (hA hq.1.1)
    have h2 := Finset.mem_Icc.1 (hA hq.1.2)
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hfib : #bad = ∑ x ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1), #{q ∈ bad | q.1 - q.2 = x} :=
    Finset.card_eq_sum_card_fiberwise hrange
  have hfibsmall : ∀ x ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1),
      (#{q ∈ bad | q.1 - q.2 = x} : ℝ) ≤ K := by
    intro x _
    by_cases hx : x ∈ D
    · have : {q ∈ bad | q.1 - q.2 = x} = ∅ := by
        ext q
        simp only [hbad, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro ⟨-, hnot⟩ hxq
        exact hnot (hxq ▸ hx)
      rw [this]
      simpa using hKpos.le
    · have hlt : (diffReps A x : ℝ) < K := by
        by_contra hc
        exact hx ((mem_popularDiff_iff hKpos x).2 (not_lt.1 hc))
      have hsub : {q ∈ bad | q.1 - q.2 = x} ⊆ {q ∈ A ×ˢ A | q.1 - q.2 = x} := by
        intro q hq
        rw [Finset.mem_filter, hbad, Finset.mem_filter] at hq
        exact Finset.mem_filter.2 ⟨hq.1.1, hq.2⟩
      have := Finset.card_le_card hsub
      have hcast : (#{q ∈ bad | q.1 - q.2 = x} : ℝ) ≤ (diffReps A x : ℝ) := by
        exact_mod_cast this
      linarith
  have hIcc : #(Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)) ≤ 2 * N := by
    rw [Int.card_Icc]; omega
  have hbadle : (#bad : ℝ) ≤ 2 * (N : ℝ) * K := by
    have h1 : (#bad : ℝ) = ∑ x ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1),
        (#{q ∈ bad | q.1 - q.2 = x} : ℝ) := by
      rw [hfib]; push_cast; ring
    rw [h1]
    calc ∑ x ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1), (#{q ∈ bad | q.1 - q.2 = x} : ℝ)
        ≤ ∑ _x ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1), K := Finset.sum_le_sum hfibsmall
      _ = (#(Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)) : ℝ) * K := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (N : ℝ) * K := by
          have : (#(Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)) : ℝ) ≤ 2 * (N : ℝ) := by
            exact_mod_cast hIcc
          nlinarith [hKpos.le]
  -- Step 2: `#bad` is the sum of the unpopular degrees
  have hdegsum : #bad = ∑ a ∈ A, #{a' ∈ A | a - a' ∉ D} := by
    rw [hbad, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => (Finset.card_filter _ _).symm
  -- Step 3: few vertices of large unpopular degree
  set Bad : Finset ℤ := {a ∈ A | 16 * η * (N : ℝ) < (#{a' ∈ A | a - a' ∉ D} : ℝ)} with hBad
  have hBadsub : Bad ⊆ A := Finset.filter_subset _ _
  have hBadsum : (#Bad : ℝ) * (16 * η * (N : ℝ)) ≤ (#bad : ℝ) := by
    have h1 : (#Bad : ℝ) * (16 * η * (N : ℝ)) = ∑ _a ∈ Bad, 16 * η * (N : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ a ∈ Bad, (16 * η * (N : ℝ)) ≤ ∑ a ∈ Bad, (#{a' ∈ A | a - a' ∉ D} : ℝ) := by
      refine Finset.sum_le_sum fun a ha => ?_
      rw [hBad, Finset.mem_filter] at ha
      exact ha.2.le
    have h3 : ∑ a ∈ Bad, (#{a' ∈ A | a - a' ∉ D} : ℝ)
        ≤ ∑ a ∈ A, (#{a' ∈ A | a - a' ∉ D} : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hBadsub fun a _ _ => by positivity
    have h4 : ∑ a ∈ A, (#{a' ∈ A | a - a' ∉ D} : ℝ) = (#bad : ℝ) := by
      rw [hdegsum]; push_cast; ring
    rw [h1]
    linarith
  have hBadcard : (#Bad : ℝ) ≤ 4 * η * (N : ℝ) := by
    have hpos : 0 < 16 * η * (N : ℝ) := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    have : (4 * η * (N : ℝ)) * (16 * η * (N : ℝ)) = 2 * (N : ℝ) * K := by
      rw [hK, ← hηsq]; ring
    rw [this]
    linarith [hBadsum, hbadle]
  -- Step 4: the exceptional set of the statement is contained in `Bad`
  have hsubBad : {a ∈ A | (#{a' ∈ A | a - a' ∈ D} : ℝ) < (#A : ℝ) - 16 * η * (N : ℝ)} ⊆ Bad := by
    intro a ha
    rw [Finset.mem_filter] at ha
    refine Finset.mem_filter.2 ⟨ha.1, ?_⟩
    have hsplit : #{a' ∈ A | a - a' ∈ D} + #{a' ∈ A | a - a' ∉ D} = #A :=
      Finset.card_filter_add_card_filter_not _
    have hcast : (#{a' ∈ A | a - a' ∈ D} : ℝ) + (#{a' ∈ A | a - a' ∉ D} : ℝ) = (#A : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsplit
    linarith [ha.2]
  exact le_trans (by exact_mod_cast Finset.card_le_card hsubBad) hBadcard

/-- Green's stated form of Lemma 9, with the (weaker) constant `8`. -/
theorem lem9_degreeCount_green (hA : A ⊆ Finset.Icc 1 (N : ℤ)) {ε : ℝ} (hε : 0 < ε) :
    (#{a ∈ A | (#{a' ∈ A | a - a' ∈ popularDiff A (32 * Real.sqrt ε * N)} : ℝ)
          < (#A : ℝ) - 16 * Real.sqrt (Real.sqrt ε) * (N : ℝ)} : ℝ)
      ≤ 8 * Real.sqrt (Real.sqrt ε) * (N : ℝ) := by
  have h := lem9_degreeCount hA hε
  have h1 : 0 ≤ Real.sqrt (Real.sqrt ε) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [h, h1, h2]

end Lemma89

/-! ## Axiom audit -/

#print axioms schurTriples_eq_addTriples
#print axioms popularDiff_eq
#print axioms mem_popularDiff_iff
#print axioms diffReps_neg
#print axioms mem_sub_neg_iff
#print axioms popularDiff_neg
#print axioms card_filter_odd_Icc
#print axioms card_filter_even_Icc
#print axioms isSumFree_of_subset_odd
#print axioms lem_oddCount
#print axioms inter_union_sdiff_self
#print axioms card_avoiding_matching
#print axioms card_avoiding_matching_fin
#print axioms sq_card_le_addTriples
#print axioms lem_evenSetTriples
#print axioms card_Icc_one_N
#print axioms card_popularDiff_le
#print axioms card_posPopular_mem_le
#print axioms card_posPopular_le
#print axioms lem8_popularDiffBound
#print axioms lem8_card_popularDiff_le
#print axioms lem9_degreeCount
#print axioms lem9_degreeCount_green

end CameronErdos

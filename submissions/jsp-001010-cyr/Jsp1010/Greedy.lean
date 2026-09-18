import Jsp1010.Defs

/-!
# JSP-001010 / Erdős #1205 — greedy repair and the small/big split

This file provides the combinatorial ingredients used to assemble the lower bound:

* `exists_repair`: if `|B| * L ≤ |Ioc N x|`, we may pick classes `g n` for the big moduli
  `n ∈ (N, x]` such that every `m ∈ B` satisfies at least `L` of them (an injection
  `B × Fin L ↪ Ioc N x` assigns `L` private big moduli to each bad `m`).
* `coverCount_split`: `[1, x] = [1, N] ∪ (N, x]` splits `coverCount`.
* `card_filter_Icc_eq_smallCount`: the `Fin N`-indexed choice matches the function on moduli.
-/

open Finset

namespace Erdos1205

/-! ### Greedy repair -/

theorem exists_repair (x N L : ℕ) (B : Finset ℕ) (hcard : B.card * L ≤ (Ioc N x).card) :
    ∃ g : ℕ → ℕ, ∀ m ∈ B, L ≤ ((Ioc N x).filter fun n => m % n = g n % n).card := by
  classical
  -- An injection `B × Fin L ↪ (N, x]` exists by cardinality.
  have hcard' : Fintype.card ({m // m ∈ B} × Fin L) ≤ Fintype.card {n // n ∈ Ioc N x} := by
    simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using hcard
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard'
  set f : ({m // m ∈ B} × Fin L) → ℕ := fun p => ((φ p : {n // n ∈ Ioc N x}) : ℕ) with hf
  have hfinj : Function.Injective f := fun _ _ h => φ.injective (Subtype.ext h)
  -- The big modulus `f (m, ℓ)` is privately assigned to `m`.
  set g : ℕ → ℕ := Function.extend f (fun p => p.1.1) (fun _ => 0) with hg
  refine ⟨g, fun m hm => ?_⟩
  have key : ∀ ℓ : Fin L, g (f ((⟨m, hm⟩ : {m // m ∈ B}), ℓ)) = m := fun ℓ =>
    hfinj.extend_apply _ _ _
  have hmap : ∀ ℓ : Fin L, f ((⟨m, hm⟩ : {m // m ∈ B}), ℓ)
      ∈ (Ioc N x).filter fun n => m % n = g n % n := by
    intro ℓ
    rw [mem_filter]
    exact ⟨(φ ((⟨m, hm⟩ : {m // m ∈ B}), ℓ)).2, by rw [key ℓ]⟩
  have hinj : Set.InjOn (fun ℓ : Fin L => f ((⟨m, hm⟩ : {m // m ∈ B}), ℓ))
      (univ : Finset (Fin L)) := fun _ _ _ _ h => congrArg Prod.snd (hfinj h)
  calc L = (univ : Finset (Fin L)).card := by simp
    _ ≤ _ := Finset.card_le_card_of_injOn _ (fun ℓ _ => hmap ℓ) hinj

/-! ### Splitting the moduli -/

theorem coverCount_split (x N : ℕ) (hN : N ≤ x) (a : ℕ → ℕ) (m : ℕ) :
    coverCount a x m =
      ((Icc 1 N).filter fun n => m % n = a n % n).card +
        ((Ioc N x).filter fun n => m % n = a n % n).card := by
  classical
  have hsplit : Icc 1 x = Icc 1 N ∪ Ioc N x := by
    ext n
    simp only [mem_Icc, mem_Ioc, mem_union]
    omega
  have hdisj : Disjoint ((Icc 1 N).filter fun n => m % n = a n % n)
      ((Ioc N x).filter fun n => m % n = a n % n) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [mem_filter, mem_Icc, mem_Ioc] at hn hn'
    omega
  rw [coverCount, hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj]

/-! ### Transfer between `Fin N`-indexed choices and functions on moduli -/

/-- With `a' (i + 1) = a i` and `a i < i + 1`, the two membership conditions agree. -/
private lemma mem_iff_of_choice {N : ℕ} {a : Fin N → ℕ} {a' : ℕ → ℕ}
    (hlt : ∀ i : Fin N, a i < i.1 + 1) (ha' : ∀ i : Fin N, a' (i.1 + 1) = a i) (m : ℕ)
    (i : Fin N) : (m % (i.1 + 1) = a i) ↔ (m % (i.1 + 1) = a' (i.1 + 1) % (i.1 + 1)) := by
  rw [ha' i, Nat.mod_eq_of_lt (hlt i)]

theorem card_filter_Icc_eq_smallCount (N : ℕ) (a : Fin N → ℕ) (ha : a ∈ choices N) (a' : ℕ → ℕ)
    (ha' : ∀ i : Fin N, a' (i.1 + 1) = a i) (m : ℕ) :
    ((Icc 1 N).filter fun n => m % n = a' n % n).card = smallCount N a m := by
  classical
  have hlt : ∀ i : Fin N, a i < i.1 + 1 := by
    intro i
    simpa using Fintype.mem_piFinset.mp ha i
  rw [smallCount]
  refine Finset.card_bij' (fun n hn => (⟨n - 1, by simp only [mem_filter, mem_Icc] at hn; omega⟩ :
      Fin N)) (fun i _ => i.1 + 1) ?_ ?_ ?_ ?_
  · intro n hn
    have hn' := hn
    simp only [mem_filter, mem_Icc] at hn'
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn'
    have hn1 : n - 1 + 1 = n := by omega
    simp only [mem_filter, mem_univ, true_and]
    refine (mem_iff_of_choice (i := (⟨n - 1, by omega⟩ : Fin N)) hlt ha' m).mpr ?_
    show m % (n - 1 + 1) = a' (n - 1 + 1) % (n - 1 + 1)
    rw [hn1]
    exact h3
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨by omega, i.2⟩, (mem_iff_of_choice hlt ha' m i).mp hi⟩
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    show n - 1 + 1 = n
    omega
  · intro i _
    simp

end Erdos1205


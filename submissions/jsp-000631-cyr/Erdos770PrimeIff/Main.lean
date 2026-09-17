import Mathlib

/-!
# Erdős Problem #770: `h(n) = n + 1` if and only if `n + 1` is prime

Let `h(n)` be minimal such that `2^n − 1, 3^n − 1, …, h(n)^n − 1` are mutually coprime.  Erdős
asked whether, for every prime `p`, the density of `{n : h(n) = p}` exists, whether
`liminf h(n) = ∞`, and about the largest prime `p` with `p − 1 ∣ n` (OPEN; not addressed here).
The problem page records: "It is easy to see that `h(n) = n + 1` if and only if `n + 1` is
prime, and that `h(n)` is unbounded for odd `n`."  This file proves the first of these two
remarks, in the exact shape of the formal-conjectures statement
`Erdos770.Nat.Prime.h_eq_add_one` (tagged "textbook" with `sorry`), with the definition
`Erdos770.h` copied verbatim (which reads "mutually coprime" as: the gcd of the whole family is
`1`).  The unboundedness for odd `n` and the open questions are not claimed.

Proof.  Write `p = n + 1`.  If `p` is prime then, by Fermat, `p ∣ iⁿ − 1` for `2 ≤ i ≤ n`, so no
`m ≤ n` works; and for `m = n + 1`, a prime `q` dividing all of `iⁿ − 1` (`2 ≤ i ≤ n + 1`) would
have `q > n + 1` (else `q ∣ qⁿ − 1`), making `1, …, n + 1` distinct roots of `Xⁿ − 1` in
`𝔽_q`, too many; so `h(n) = n + 1`.  Conversely, if `h(n) = n + 1` but `n + 1 = ab` with
`2 ≤ a, b ≤ n`, minimality gives a prime `q ∣ iⁿ − 1` for all `2 ≤ i ≤ n`, hence `q > n`, and
`{1, …, n}` is then the full set of roots of `Xⁿ − 1` in `𝔽_q`, which is closed under
multiplication, so `q ∣ (ab)ⁿ − 1 = (n + 1)ⁿ − 1` as well — contradicting the gcd at `m = n + 1`
being `1`.
-/

open Set ENat Filter

namespace Erdos770

/-- Let $h n$ be the minimal number such that $2 ^ n - 1, \dots, h(n) ^ n - 1$
are collectively coprime. -/
noncomputable def h (n : ℕ) : ℕ∞ := sInf {m | 2 < m ∧
  ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}

end Erdos770

open Erdos770

/-! ### Helper lemmas -/

/-- Divisibility of `i ^ N - 1` (truncated subtraction, but `1 ≤ i ^ N`) read in `ZMod q`. -/
private lemma erdos770_dvd_pow_sub_one_iff {q i N : ℕ} (hi : 1 ≤ i ^ N) :
    q ∣ i ^ N - 1 ↔ ((i : ZMod q) ^ N = 1) := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hi, Nat.cast_pow, Nat.cast_one, sub_eq_zero]

/-- A prime dividing every `i ^ N - 1` for `2 ≤ i ≤ m` must exceed `m`: otherwise `i = q`
gives `q ∣ q ^ N - 1` while also `q ∣ q ^ N`, so `q ∣ 1`. -/
private lemma erdos770_lt_of_forall_dvd {q N m : ℕ} (hq : q.Prime) (hN : 0 < N)
    (hdvd : ∀ i, 2 ≤ i → i ≤ m → q ∣ i ^ N - 1) : m < q := by
  by_contra hle
  have hqm : q ≤ m := Nat.not_lt.mp hle
  have h1 : q ∣ q ^ N - 1 := hdvd q hq.two_le hqm
  have h2 : q ∣ q ^ N := dvd_pow_self q hN.ne'
  have hpos : 1 ≤ q ^ N := Nat.one_le_pow _ _ hq.pos
  have h3 : q ∣ q ^ N - (q ^ N - 1) := Nat.dvd_sub h2 h1
  rw [Nat.sub_sub_self hpos] at h3
  exact hq.one_lt.ne' (Nat.dvd_one.mp h3)

/-- Root counting: if a prime `q > m` divides every `i ^ N - 1` for `2 ≤ i ≤ m`, then the `m`
residues `1, …, m` are distinct roots of `X ^ N - 1` in the field `ZMod q`, so `m ≤ N`. -/
private lemma erdos770_le_of_forall_dvd {q N m : ℕ} (hq : q.Prime) (hN : 0 < N) (hqm : m < q)
    (hdvd : ∀ i, 2 ≤ i → i ≤ m → q ∣ i ^ N - 1) : m ≤ N := by
  have : Fact q.Prime := ⟨hq⟩
  have hroot : ∀ i ∈ Finset.Icc 1 m, ((i : ZMod q)) ^ N = 1 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rcases eq_or_lt_of_le hi.1 with h1 | h1
    · simp [← h1]
    · exact (erdos770_dvd_pow_sub_one_iff (Nat.one_le_pow _ _ (by omega))).mp (hdvd i h1 hi.2)
  have hinj : Set.InjOn (fun i : ℕ => (i : ZMod q)) ↑(Finset.Icc 1 m) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    have hv := congrArg ZMod.val hab
    rwa [ZMod.val_cast_of_lt (show a < q by omega), ZMod.val_cast_of_lt (show b < q by omega)] at hv
  have hsub : (Finset.Icc 1 m).image (fun i : ℕ => (i : ZMod q)) ⊆
      (Polynomial.nthRoots N (1 : ZMod q)).toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hN]
    exact hroot i hi
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at hcard
  have hc2 := Multiset.toFinset_card_le (Polynomial.nthRoots N (1 : ZMod q))
  have hc3 := Polynomial.card_nthRoots N (1 : ZMod q)
  omega

/-- Fermat's little theorem: if `N + 1` is prime then `N + 1 ∣ i ^ N - 1` for `2 ≤ i ≤ N`. -/
private lemma erdos770_prime_dvd {N i : ℕ} (hp : (N + 1).Prime) (h2 : 2 ≤ i) (hi : i ≤ N) :
    (N + 1) ∣ i ^ N - 1 := by
  have : Fact (N + 1).Prime := ⟨hp⟩
  rw [erdos770_dvd_pow_sub_one_iff (Nat.one_le_pow _ _ (by omega))]
  have hne : (i : ZMod (N + 1)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  simpa using ZMod.pow_card_sub_one_eq_one hne

/-- **The numbers `2 ^ N - 1, 3 ^ N - 1, …, (N + 1) ^ N - 1` are always collectively coprime.**
A common prime factor `q` would have to exceed `N + 1`, and then `1, 2, …, N + 1` would be
`N + 1` distinct roots of `X ^ N - 1` in `ZMod q`, one too many. -/
theorem erdos_770_gcd_Icc_succ_eq_one {N : ℕ} (hN : 0 < N) :
    ((Finset.Icc 2 (N + 1)).gcd fun i => i ^ N - 1) = 1 := by
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have hall : ∀ i, 2 ≤ i → i ≤ N + 1 → q ∣ i ^ N - 1 := fun i h2 hi =>
    hqd.trans (Finset.gcd_dvd (Finset.mem_Icc.mpr ⟨h2, hi⟩))
  have h1 : N + 1 < q := erdos770_lt_of_forall_dvd hq hN hall
  have h2 : N + 1 ≤ N := erdos770_le_of_forall_dvd hq hN h1 hall
  omega

/-- If the gcd at `P` is `1` and at no smaller index, then `h N = P`. -/
private lemma erdos770_h_eq {N P : ℕ} (hP2 : 2 < P)
    (h1 : ((Finset.Icc 2 P).gcd fun i => i ^ N - 1) = 1)
    (h2 : ∀ k : ℕ, k < P → ((Finset.Icc 2 k).gcd fun i => i ^ N - 1) ≠ 1) :
    h N = (P : ℕ∞) := by
  have hdef : h N = sInf {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ N - 1)).gcd id = 1} := rfl
  rw [hdef]
  refine IsLeast.csInf_eq ⟨⟨?_, ?_⟩, ?_⟩
  · exact_mod_cast hP2
  · rw [ENat.toNat_natCast, ← Finset.gcd_eq_gcd_image]
    exact h1
  · rintro m ⟨hm2, hm1⟩
    rcases eq_or_ne m ⊤ with rfl | hmtop
    · exact le_top
    lift m to ℕ using hmtop with k
    rw [ENat.toNat_natCast, ← Finset.gcd_eq_gcd_image] at hm1
    rw [ENat.natCast_le_natCast]
    by_contra hlt
    exact h2 k (by omega) hm1

/-- If the gcd is already `1` at some `2 < k < P`, then `h N ≠ P`. -/
private lemma erdos770_h_ne_of_lt {N P k : ℕ} (hk2 : 2 < k) (hkP : k < P)
    (h1 : ((Finset.Icc 2 k).gcd fun i => i ^ N - 1) = 1) : h N ≠ (P : ℕ∞) := by
  have hdef : h N = sInf {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ N - 1)).gcd id = 1} := rfl
  have hmem : (k : ℕ∞) ∈ {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ N - 1)).gcd id = 1} := by
    refine ⟨by exact_mod_cast hk2, ?_⟩
    rw [ENat.toNat_natCast, ← Finset.gcd_eq_gcd_image]
    exact h1
  intro hEq
  have hle := sInf_le hmem
  rw [← hdef, hEq, ENat.natCast_le_natCast] at hle
  omega

/-- If the gcd fails to be `1` at every index `≤ P`, then `h N ≠ P`. -/
private lemma erdos770_h_ne_of_forall {N P : ℕ}
    (h2 : ∀ k : ℕ, k ≤ P → ((Finset.Icc 2 k).gcd fun i => i ^ N - 1) ≠ 1) :
    h N ≠ (P : ℕ∞) := by
  have hdef : h N = sInf {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ N - 1)).gcd id = 1} := rfl
  intro hEq
  have hle : ((P : ℕ∞) + 1) ≤ sInf {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ N - 1)).gcd id = 1} := by
    refine le_sInf ?_
    rintro m ⟨hm2, hm1⟩
    rcases eq_or_ne m ⊤ with rfl | hmtop
    · exact le_top
    lift m to ℕ using hmtop with k
    rw [ENat.toNat_natCast, ← Finset.gcd_eq_gcd_image] at hm1
    rw [ENat.natCast_add_one_le_iff, ENat.natCast_lt_natCast]
    by_contra hlt
    exact h2 k (by omega) hm1
  rw [← hdef, hEq, ENat.natCast_add_one_le_iff, ENat.natCast_lt_natCast] at hle
  omega

/-- **Erdős #770, the page's remark**, in the offset form `n + 3` (so `2 < n + 3` without a
hypothesis): `h (n + 3) = n + 4 ↔ (n + 4).Prime`. -/
theorem erdos_770_h_eq_add_one_succ (n : ℕ) : h (n + 3) = n + 4 ↔ (n + 4).Prime := by
  have hcast : ((n : ℕ∞) + 4) = ((n + 4 : ℕ) : ℕ∞) := by push_cast; ring
  rw [hcast]
  have hmono : ∀ k l : ℕ, k ≤ l →
      ((Finset.Icc 2 l).gcd fun i => i ^ (n + 3) - 1) ∣
        ((Finset.Icc 2 k).gcd fun i => i ^ (n + 3) - 1) :=
    fun _ _ hkl => Finset.gcd_mono (Finset.Icc_subset_Icc_right hkl)
  constructor
  · -- `h (n+3) = n+4` forces `n+4` to be prime.
    intro hEq
    by_contra hnp
    rcases eq_or_ne ((Finset.Icc 2 (n + 3)).gcd fun i => i ^ (n + 3) - 1) 1 with hg | hg
    · exact erdos770_h_ne_of_lt (by omega) (by omega) hg hEq
    · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hg
      have hall : ∀ i, 2 ≤ i → i ≤ n + 3 → q ∣ i ^ (n + 3) - 1 := fun i h2 hi =>
        hqd.trans (Finset.gcd_dvd (Finset.mem_Icc.mpr ⟨h2, hi⟩))
      -- factor the composite `n + 4`
      obtain ⟨a, hadvd, ha2, haP⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
      obtain ⟨b, hab⟩ := hadvd
      have hb2 : 2 ≤ b := by
        rcases Nat.lt_or_ge b 2 with hb | hb
        · interval_cases b <;> omega
        · exact hb
      have hbP : b < n + 4 := by
        have : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha2
        omega
      -- `q ∣ (n+4)^(n+3) - 1`
      have hqP : q ∣ (n + 4) ^ (n + 3) - 1 := by
        have hqa := (erdos770_dvd_pow_sub_one_iff (q := q)
          (Nat.one_le_pow (n + 3) a (by omega))).mp (hall a ha2 (by omega))
        have hqb := (erdos770_dvd_pow_sub_one_iff (q := q)
          (Nat.one_le_pow (n + 3) b (by omega))).mp (hall b hb2 (by omega))
        rw [erdos770_dvd_pow_sub_one_iff (Nat.one_le_pow (n + 3) (n + 4) (by omega)), hab]
        push_cast
        rw [mul_pow, hqa, hqb, one_mul]
      have hqgcd : q ∣ ((Finset.Icc 2 (n + 4)).gcd fun i => i ^ (n + 3) - 1) := by
        refine Finset.dvd_gcd ?_
        intro i hi
        rw [Finset.mem_Icc] at hi
        rcases Nat.lt_or_ge i (n + 4) with hlt | hge
        · exact hall i hi.1 (by omega)
        · have : i = n + 4 := by omega
          subst this
          exact hqP
      refine erdos770_h_ne_of_forall (P := n + 4) ?_ hEq
      intro k hk hk1
      have : q ∣ ((Finset.Icc 2 k).gcd fun i => i ^ (n + 3) - 1) := hqgcd.trans (hmono k (n + 4) hk)
      rw [hk1] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  · -- `n+4` prime forces `h (n+3) = n+4`.
    intro hp
    refine erdos770_h_eq (by omega) (erdos_770_gcd_Icc_succ_eq_one (N := n + 3) (by omega)) ?_
    intro k hk hk1
    have hdvd : (n + 4) ∣ ((Finset.Icc 2 k).gcd fun i => i ^ (n + 3) - 1) := by
      refine Finset.dvd_gcd ?_
      intro i hi
      rw [Finset.mem_Icc] at hi
      exact erdos770_prime_dvd (N := n + 3) hp hi.1 (by omega)
    rw [hk1] at hdvd
    have := Nat.dvd_one.mp hdvd
    omega

namespace Erdos770

/-- `n + 1` is prime iff `h n = n + 1`. This is described as 'easy to see' in [Er74b]. -/
theorem Nat.Prime.h_eq_add_one {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e : ((k + 3 : ℕ) : ℕ∞) + 1 = (k : ℕ∞) + 4 := by push_cast; ring
  rw [e]
  exact erdos_770_h_eq_add_one_succ k

end Erdos770

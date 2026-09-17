import Mathlib

/-!
# Erdős Problem #1212: Stewart's path `(p_k, p_{k+1}) → (p_{k+1}, p_{k+2})`

Let `G` be the graph on the visible lattice points `(x, y) ∈ ℕ²`, `gcd(x, y) = 1`, two vertices
adjacent when they differ by `±1` in exactly one coordinate.  Erdős's current question asks for an
infinite path all of whose vertices have `min(x, y) > 1` and a composite coordinate (OPEN; not
addressed here).  The problem page recounts that Erdős originally asked only for `min(x, y) > 1`,
and that "In the evening Stewart gave the simple proof: `(p_k, p_{k+1})` can be joined to
`(p_{k+1}, p_{k+2})`", via the path
`(p_k, p_{k+1}) → (p_k, p_{k+1} + 1) → ⋯ → (p_k, p_{k+2}) → (p_k + 1, p_{k+2}) → ⋯ → (p_{k+1}, p_{k+2})`,
"permissible provided `[p_{k+1}, p_{k+2}]` contains no multiple of `p_k`, which is true provided
`p_{k+2} < 2p_k`".

This file proves Stewart's step under exactly that proviso: for consecutive primes `a < b < c`
with `c < 2a`, the vertices `(a, b)` and `(b, c)` are joined in `G` by a path all of whose
vertices are visible with both coordinates `> 1`; in particular this holds for `p_k, p_{k+1},
p_{k+2}` (primes indexed from `0` via `Nat.nth Nat.Prime`) whenever `p_{k+2} < 2p_k`.  The
adjacency `Adj` is copied verbatim from the formal-conjectures rendering of #1212; "joined" is
the reflexive-transitive closure of adjacency restricted to such vertices.  The page's further
claim that `p_{k+2} < 2p_k` holds for all `k ≥ 4` (two primes in `(p_k, 2p_k)`), the resulting
infinite path, and the current (composite-coordinate) question are not claimed.
-/

/-- Two lattice points are adjacent iff they differ by exactly 1 in exactly one coordinate. -/
def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
  (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

/-- A vertex of Erdős's original question: a visible lattice point with both coordinates `> 1`. -/
def Visible (p : ℕ × ℕ) : Prop := 1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1

/-- `VisiblyJoined p q`: there is a path in `G` from `p` to `q` all of whose vertices are `Visible`. -/
def VisiblyJoined (p q : ℕ × ℕ) : Prop :=
  Relation.ReflTransGen (fun u v => Visible u ∧ Visible v ∧ Adj u v) p q

/-- The vertical leg `(a, y₀) → (a, y₀ + 1) → ⋯ → (a, y₀ + m)` is a path in `G` when all its
vertices are visible. -/
theorem joined_vertical (a y₀ m : ℕ) (h : ∀ j ≤ m, Visible (a, y₀ + j)) :
    VisiblyJoined (a, y₀) (a, y₀ + m) := by
  induction m with
  | zero => simp only [Nat.add_zero]; exact Relation.ReflTransGen.refl
  | succ m ih =>
    refine Relation.ReflTransGen.tail (ih fun j hj => h j (by omega)) ?_
    exact ⟨h m (by omega), h (m + 1) le_rfl, Or.inl ⟨rfl, Or.inr (by omega)⟩⟩

/-- The horizontal leg `(x₀, c) → (x₀ + 1, c) → ⋯ → (x₀ + m, c)` is a path in `G` when all its
vertices are visible. -/
theorem joined_horizontal (x₀ c m : ℕ) (h : ∀ j ≤ m, Visible (x₀ + j, c)) :
    VisiblyJoined (x₀, c) (x₀ + m, c) := by
  induction m with
  | zero => simp only [Nat.add_zero]; exact Relation.ReflTransGen.refl
  | succ m ih =>
    refine Relation.ReflTransGen.tail (ih fun j hj => h j (by omega)) ?_
    exact ⟨h m (by omega), h (m + 1) le_rfl, Or.inr ⟨rfl, Or.inr (by omega)⟩⟩

/-- **Stewart's step**: for primes `a < b < c` with `c < 2a`, `(a, b)` is joined to `(b, c)`. -/
theorem stewart_joined (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (h2 : c < 2 * a) : VisiblyJoined (a, b) (b, c) := by
  have ha1 : 1 < a := ha.one_lt
  have hb1 : 1 < b := hb.one_lt
  have hc1 : 1 < c := hc.one_lt
  have hvert : VisiblyJoined (a, b) (a, c) := by
    have key : VisiblyJoined (a, b) (a, b + (c - b)) := by
      refine joined_vertical a b (c - b) fun j hj => ?_
      refine ⟨ha1, show (1 : ℕ) < b + j by omega, ?_⟩
      have hnd : ¬ a ∣ (b + j) := by
        rintro ⟨t, ht⟩
        have ht2 : 2 ≤ t := by
          by_contra hcon
          interval_cases t <;> omega
        have hge : 2 * a ≤ a * t := by
          calc 2 * a = a * 2 := by ring
          _ ≤ a * t := Nat.mul_le_mul_left a ht2
        rw [← ht] at hge
        omega
      exact (Nat.Prime.coprime_iff_not_dvd ha).mpr hnd
    rwa [Nat.add_sub_cancel' hbc.le] at key
  have hhoriz : VisiblyJoined (a, c) (b, c) := by
    have key : VisiblyJoined (a, c) (a + (b - a), c) := by
      refine joined_horizontal a c (b - a) fun j hj => ?_
      refine ⟨show (1 : ℕ) < a + j by omega, hc1, ?_⟩
      have hnd : ¬ c ∣ (a + j) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      exact ((Nat.Prime.coprime_iff_not_dvd hc).mpr hnd).symm
    rwa [Nat.add_sub_cancel' hab.le] at key
  exact hvert.trans hhoriz

/-- **Erdős #1212, Stewart's proof for the original question**: whenever `p_{k+2} < 2p_k`,
`(p_k, p_{k+1})` is joined to `(p_{k+1}, p_{k+2})` (primes indexed from `0`). -/
theorem erdos_1212_stewart (k : ℕ) (h : Nat.nth Nat.Prime (k + 2) < 2 * Nat.nth Nat.Prime k) :
    VisiblyJoined (Nat.nth Nat.Prime k, Nat.nth Nat.Prime (k + 1))
      (Nat.nth Nat.Prime (k + 1), Nat.nth Nat.Prime (k + 2)) := by
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  exact stewart_joined _ _ _ (Nat.prime_nth_prime k) (Nat.prime_nth_prime (k + 1))
    (Nat.prime_nth_prime (k + 2)) (hmono (by omega)) (hmono (by omega)) h

/-- Closed form of `erdos_1212_stewart`. -/
theorem erdos_1212_stewart_closed :
    ¬ ∃ k : ℕ, Nat.nth Nat.Prime (k + 2) < 2 * Nat.nth Nat.Prime k ∧
      ¬ VisiblyJoined (Nat.nth Nat.Prime k, Nat.nth Nat.Prime (k + 1))
        (Nat.nth Nat.Prime (k + 1), Nat.nth Nat.Prime (k + 2)) := by
  rintro ⟨k, h, hn⟩
  exact hn (erdos_1212_stewart k h)

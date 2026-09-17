import MerLeanExperiment.Target
import Mathlib.Data.List.OfFn
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Init.Data.BitVec.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace CochromaticTwenty

/-- Number of unordered pairs before the next vertex is appended. -/
def triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangle n + n

theorem triangle_mono : Monotone triangle := by
  exact monotone_nat_of_le_succ (fun n => by simp [triangle])

/-- Position of an unordered pair in the lower-triangular bit encoding. -/
def edgeIndex (i j : ℕ) : ℕ := triangle (max i j) + min i j

theorem edgeIndex_symm (i j : ℕ) : edgeIndex i j = edgeIndex j i := by
  simp only [edgeIndex, max_comm, min_comm]

theorem edgeIndex_lt {n i j : ℕ} (hi : i < n) (hj : j < n) (hne : i ≠ j) :
    edgeIndex i j < triangle n := by
  have hm : min i j < max i j := by omega
  have hn : max i j + 1 ≤ n := by omega
  calc
    edgeIndex i j < triangle (max i j) + max i j := Nat.add_lt_add_left hm _
    _ = triangle (max i j + 1) := rfl
    _ ≤ triangle n := triangle_mono hn

/-- A numeric edge table denotes an ordinary loopless undirected graph. -/
def codeGraph (n code : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ code.testBit (edgeIndex i.val j.val) = true
  symm := by
    constructor
    intro i j h
    exact ⟨Ne.symm h.1, by rw [edgeIndex_symm]; exact h.2⟩
  loopless := by constructor; intro i h; exact h.1 rfl

instance (n code : ℕ) : DecidableRel (codeGraph n code).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true))

/-- Append one vertex whose incidence bits are supplied by `mask`. -/
def extendCode (n code mask : ℕ) : ℕ := 2 ^ triangle n * mask + code

theorem extendCode_old {n code mask : ℕ} (hc : code < 2 ^ triangle n)
    (i j : Fin n) :
    (codeGraph (n + 1) (extendCode n code mask)).Adj i.castSucc j.castSucc ↔
      (codeGraph n code).Adj i j := by
  by_cases h : i = j
  · subst j; simp [codeGraph]
  · have hij : i.val ≠ j.val := fun hval => h (Fin.ext hval)
    have hi := edgeIndex_lt i.isLt j.isLt hij
    simp [codeGraph, extendCode, Nat.testBit_two_pow_mul_add mask hc, hi, h]

theorem extendCode_last {n code mask : ℕ} (hc : code < 2 ^ triangle n) (i : Fin n) :
    (codeGraph (n + 1) (extendCode n code mask)).Adj i.castSucc (Fin.last n) ↔
      mask.testBit i.val = true := by
  have hne : i.castSucc ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at this
    omega
  simp [codeGraph, extendCode, edgeIndex, hne,
    Nat.testBit_two_pow_mul_add mask hc]

/-- Every incidence function has a bounded numeric mask; this is a concrete adapter. -/
theorem exists_mask {n : ℕ} (f : Fin n → Bool) :
    ∃ mask : ℕ, mask < 2 ^ n ∧ ∀ i : Fin n, mask.testBit i.val = f i := by
  let bits := BitVec.ofBoolListLE (List.ofFn f)
  refine ⟨bits.toNat, ?_, ?_⟩
  · simpa only [List.length_ofFn] using bits.isLt
  · intro i
    change bits.getLsbD i.val = f i
    rw [BitVec.getLsbD_ofBoolListLE]
    simp [List.getD, i.isLt]

/-- Extend a relabeling while fixing the newly appended vertex. -/
def extendEquiv {n : ℕ} (e : Fin n ≃ Fin n) : Fin (n + 1) ≃ Fin (n + 1) :=
  finSuccEquivLast.trans ((Equiv.optionCongr e).trans finSuccEquivLast.symm)

@[simp] theorem extendEquiv_last {n : ℕ} (e : Fin n ≃ Fin n) :
    extendEquiv e (Fin.last n) = Fin.last n := by simp [extendEquiv]

@[simp] theorem extendEquiv_castSucc {n : ℕ} (e : Fin n ≃ Fin n) (i : Fin n) :
    extendEquiv e i.castSucc = (e i).castSucc := by simp [extendEquiv]

/-- Any graph obtained by adjoining one vertex to a coded graph has exactly the
numeric extension form, up to the explicitly extended vertex relabeling. -/
theorem exists_extension_iso {n code : ℕ} (hc : code < 2 ^ triangle n)
    (G : SimpleGraph (Fin (n + 1)))
    (e : G.comap Fin.castSucc ≃g codeGraph n code) :
    ∃ mask : ℕ, mask < 2 ^ n ∧
      Nonempty (G ≃g codeGraph (n + 1) (extendCode n code mask)) := by
  classical
  obtain ⟨mask, hm, hmask⟩ := exists_mask
    (fun i : Fin n => decide (G.Adj (e.symm i).castSucc (Fin.last n)))
  refine ⟨mask, hm, ⟨{ toEquiv := extendEquiv e.toEquiv, map_rel_iff' := ?_ }⟩⟩
  intro u v
  induction u using Fin.lastCases with
  | last =>
    induction v using Fin.lastCases with
    | last => simp
    | cast v =>
      rw [extendEquiv_last, extendEquiv_castSucc]
      rw [SimpleGraph.adj_comm, extendCode_last hc, hmask]
      simp [SimpleGraph.adj_comm]
  | cast u =>
    induction v using Fin.lastCases with
    | last =>
      rw [extendEquiv_castSucc, extendEquiv_last, extendCode_last hc, hmask]
      simp
    | cast v =>
      rw [extendEquiv_castSucc, extendEquiv_castSucc, extendCode_old hc]
      exact e.map_rel_iff

end CochromaticTwenty

#print axioms CochromaticTwenty.extendCode_old
#print axioms CochromaticTwenty.extendCode_last
#print axioms CochromaticTwenty.exists_mask

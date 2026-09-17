import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

/-!
The exact twenty-vertex subquestion of Erdős 758. This file states obligations
and contains no proof of the final result. A color class may be empty; this
expresses an upper bound on the number of homogeneous partition classes.
Frozen root signature: theorem cochromatic_twenty : CochromaticTwenty.Target
-/

namespace CochromaticTwenty

/-- A set of vertices induces a clique or an independent set. -/
def Homogeneous {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  s.Pairwise G.Adj ∨ s.Pairwise (fun u v => ¬ G.Adj u v)

/-- An ordinary vertex coloring with at most k homogeneous color classes. -/
def HasCocoloring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ color : V → Fin k, ∀ i : Fin k, Homogeneous G {v | color v = i}

/-- Every twenty-vertex simple graph admits at most six homogeneous classes. -/
def UpperBound : Prop := ∀ G : SimpleGraph (Fin 20), HasCocoloring G 6

/-- Some twenty-vertex simple graph admits no coloring with five such classes. -/
def LowerBound : Prop := ∃ G : SimpleGraph (Fin 20), ¬ HasCocoloring G 5

/-- The maximum cochromatic number among twenty-vertex graphs is exactly six. -/
def Target : Prop := UpperBound ∧ LowerBound

end CochromaticTwenty

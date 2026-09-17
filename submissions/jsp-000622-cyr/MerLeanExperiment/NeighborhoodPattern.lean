import MerLeanExperiment.GraphClauses
import MerLeanExperiment.GraphCode

namespace CochromaticTwenty

/-- Vertex zero has exactly the next `d` vertices as neighbors. Its neighbor
induced graph has code `leftCode`; the complement of its nonneighbor induced
graph has code `rightCode`. Every edge between the two parts remains free. -/
def neighborhoodEdge (n d leftCode rightCode : ℕ) (u v : Fin n) : EdgeRule :=
  let lo := min u.val v.val
  let hi := max u.val v.val
  if lo = 0 then .fixed (decide (hi ≤ d))
  else if hi ≤ d then .fixed (leftCode.testBit (edgeIndex (lo - 1) (hi - 1)))
  else if d < lo then
    .fixed (!(rightCode.testBit (edgeIndex (lo - d - 1) (hi - d - 1))))
  else .variable ((lo - 1) * (n - d - 1) + (hi - d - 1))

def neighborhoodPattern (n d leftCode rightCode : ℕ) : GraphPattern n where
  edge := neighborhoodEdge n d leftCode rightCode
  symmetric := by intro u v; simp only [neighborhoodEdge, min_comm, max_comm]

end CochromaticTwenty

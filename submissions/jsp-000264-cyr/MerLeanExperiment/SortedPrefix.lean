import MerLeanExperiment.FiniteGreedy
import MerLeanExperiment.SquareConstruction

namespace ReciprocalSquares

/-- The suffix after an element in an increasing finite enumeration is its upper filter. -/
theorem sorted_suffix_toFinset (s : Finset ℕ) (pre post : List ℕ) (d : ℕ)
    (hs : s.sort (· ≤ ·) = pre ++ d :: post) :
    post.toFinset = s.filter (fun j => d < j) := by
  have hpw := s.sortedLT_sort.pairwise
  rw [hs, List.pairwise_append] at hpw
  have hpost := (List.pairwise_cons.mp hpw.2.1).1
  ext j
  constructor
  · intro hj
    have hjpost := List.mem_toFinset.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨?_, hpost j hjpost⟩
    apply (Finset.mem_sort (· ≤ ·)).mp
    rw [hs]
    simp [hjpost]
  · intro hj
    obtain ⟨hjs, hdj⟩ := Finset.mem_filter.mp hj
    have hjlist : j ∈ s.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hjs
    rw [hs, List.mem_append, List.mem_cons] at hjlist
    rcases hjlist with hjpre | rfl | hjpost
    · have hjd := hpw.2.2 j hjpre d (by simp)
      omega
    · omega
    · exact List.mem_toFinset.mpr hjpost

/-- Roots of the erased prefix, listed in increasing order and excluding one. -/
def prefixList (N : ℕ) : List ℕ := ((prefixRoots N).erase 1).sort (· ≤ ·)

theorem prefixList_mem_bounds (N d : ℕ) (hd : d ∈ prefixList N) :
    2 ≤ d ∧ d < N ^ 2 := by
  have hde := (Finset.mem_sort (· ≤ ·)).mp hd
  obtain ⟨hd1, hdpre⟩ := Finset.mem_erase.mp hde
  obtain ⟨hdlt, hdsmooth⟩ := Finset.mem_filter.mp hdpre
  have hdpos := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hdsmooth)
  exact ⟨by omega, Finset.mem_range.mp hdlt⟩

theorem prefixList_suffix_mass (N d : ℕ) (pre post : List ℕ)
    (hs : prefixList N = pre ++ d :: post) :
    listMass (fun j : ℕ => (1 : ℚ) / (j : ℚ) ^ 2) post =
      ∑ j ∈ (prefixRoots N).filter (fun j => d < j), (1 : ℚ) / (j : ℚ) ^ 2 := by
  have hdmem : d ∈ prefixList N := by rw [hs]; simp
  have hd2 := (prefixList_mem_bounds N d hdmem).1
  have hfilter := sorted_suffix_toFinset ((prefixRoots N).erase 1) pre post d hs
  have hfilter' : ((prefixRoots N).erase 1).filter (fun j => d < j) =
      (prefixRoots N).filter (fun j => d < j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · exact fun h => ⟨⟨by omega, h.1⟩, h.2⟩
  rw [hfilter'] at hfilter
  have hnodup : post.Nodup := by
    have hn := Finset.sort_nodup ((prefixRoots N).erase 1) (· ≤ ·)
    change (prefixList N).Nodup at hn
    rw [hs, List.nodup_append] at hn
    exact (List.nodup_cons.mp hn.2.1).2
  change (post.map _).sum = _
  rw [← List.sum_toFinset _ hnodup, hfilter]

end ReciprocalSquares

import MerLeanExperiment.TableMonotone
import MerLeanExperiment.TableUpper
import MerLeanExperiment.TableLower
import MerLeanExperiment.NineLowerBound
import MerLeanExperiment.CochromaticNumber
import MerLeanExperiment.TriangleCycleSplit
import MerLeanExperiment.Main

/-!
# The published table of maximum cochromatic numbers (Erdős problem 758)

`z(n)` denotes the maximum cochromatic number of a simple graph on `n`
vertices.  The values published for `n = 1, …, 19` are

```
n    1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
z(n) 1 1 2 2 3 3 3 3 4  4  4  4  5  5  5  6  6  6  6
```

and this file proves all of them, together with `z(20) = 6` (the frozen target
`cochromatic_twenty` of `MerLeanExperiment.Main`).

Because `z` is monotone non-decreasing, the table reduces to six upper anchors
and six lower anchors:

| anchor | source |
|---|---|
| `z(2) ≤ 1` | `fin2_hasCocoloring_one` |
| `z(4) ≤ 2` | `fin4_hasCocoloring_two` |
| `z(8) ≤ 3` | `fin8_hasCocoloring_three` |
| `z(12) ≤ 4` | `fin12_hasCocoloring_four` |
| `z(15) ≤ 5` | `fin15_hasCocoloring_five` |
| `z(20) ≤ 6` | `universal_six_upperBound` |
| `z(1) ≥ 1` | `fin1_not_hasCocoloring_zero` |
| `z(3) ≥ 2` | `fin3_not_hasCocoloring_one` (one edge and an isolated vertex) |
| `z(5) ≥ 3` | `fin5_not_hasCocoloring_two` (the five-cycle) |
| `z(9) ≥ 4` | `fin9_not_hasCocoloring_three` (the four-regular graph `G9`) |
| `z(13) ≥ 5` | `fin13_not_hasCocoloring_four` (Paley of order 17, first 13) |
| `z(16) ≥ 6` | `fin16_not_hasCocoloring_five` (Paley of order 17, first 16) |
-/

namespace CochromaticTwenty

/-- The published values of `z(n)` for `1 ≤ n ≤ 19`; zero outside that range. -/
def zTable : ℕ → ℕ
  | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3 | 6 => 3 | 7 => 3 | 8 => 3
  | 9 => 4 | 10 => 4 | 11 => 4 | 12 => 4 | 13 => 5 | 14 => 5 | 15 => 5
  | 16 => 6 | 17 => 6 | 18 => 6 | 19 => 6 | _ => 0

/-- Every entry of the table between `n = 1` and `n = 19` is at least one. -/
theorem one_le_zTable (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 19) : 1 ≤ zTable n := by
  interval_cases n <;> decide

/-- `z(20) ≤ 6`, in the `∀`-form used by the monotonicity lemma. -/
theorem fin20_hasCocoloring_six : ∀ G : SimpleGraph (Fin 20), HasCocoloring G 6 :=
  universal_six_upperBound

/-- The upper half of the table: every graph on `n ≤ 19` vertices has a
cocoloring with `zTable n` classes.  Each case is one of the six upper anchors
pushed down by `hasCocoloring_of_le`. -/
theorem table_upper (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 19) (G : SimpleGraph (Fin n)) :
    HasCocoloring G (zTable n) := by
  interval_cases n
  · exact hasCocoloring_of_le (by omega) fin2_hasCocoloring_one G
  · exact fin2_hasCocoloring_one G
  · exact hasCocoloring_of_le (by omega) fin4_hasCocoloring_two G
  · exact fin4_hasCocoloring_two G
  all_goals first
    | exact hasCocoloring_of_le (by omega) fin8_hasCocoloring_three G
    | exact hasCocoloring_of_le (by omega) fin12_hasCocoloring_four G
    | exact hasCocoloring_of_le (by omega) fin15_hasCocoloring_five G
    | exact hasCocoloring_of_le (by omega) fin20_hasCocoloring_six G

/-- The lower half of the table: for every `n ≤ 19` some graph on `n` vertices
has no cocoloring with `zTable n - 1` classes.  Each case is one of the six
lower anchors pushed up by `exists_not_hasCocoloring_of_le`. -/
theorem table_lower (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 19) :
    ∃ G : SimpleGraph (Fin n), ¬ HasCocoloring G (zTable n - 1) := by
  obtain ⟨G1, hG1⟩ : ∃ G : SimpleGraph (Fin 1), ¬ HasCocoloring G 0 :=
    exists_fin1_not_hasCocoloring_zero
  obtain ⟨G3, hG3⟩ : ∃ G : SimpleGraph (Fin 3), ¬ HasCocoloring G 1 :=
    ⟨G3, fin3_not_hasCocoloring_one⟩
  obtain ⟨G5, hG5⟩ : ∃ G : SimpleGraph (Fin 5), ¬ HasCocoloring G 2 :=
    ⟨C5, fin5_not_hasCocoloring_two⟩
  obtain ⟨G9, hG9⟩ : ∃ G : SimpleGraph (Fin 9), ¬ HasCocoloring G 3 :=
    ⟨G9, fin9_not_hasCocoloring_three⟩
  obtain ⟨G13, hG13⟩ : ∃ G : SimpleGraph (Fin 13), ¬ HasCocoloring G 4 :=
    ⟨_, fin13_not_hasCocoloring_four⟩
  obtain ⟨G16, hG16⟩ : ∃ G : SimpleGraph (Fin 16), ¬ HasCocoloring G 5 :=
    ⟨_, fin16_not_hasCocoloring_five⟩
  interval_cases n
  all_goals first
    | exact exists_not_hasCocoloring_of_le (by omega) G1 hG1
    | exact exists_not_hasCocoloring_of_le (by omega) G3 hG3
    | exact exists_not_hasCocoloring_of_le (by omega) G5 hG5
    | exact exists_not_hasCocoloring_of_le (by omega) G9 hG9
    | exact exists_not_hasCocoloring_of_le (by omega) G13 hG13
    | exact exists_not_hasCocoloring_of_le (by omega) G16 hG16

end CochromaticTwenty

/-- **The published table.**  For every `1 ≤ n ≤ 19`, the maximum cochromatic
number of a simple graph on `n` vertices is the tabulated value `zTable n`:
every `n`-vertex graph has a cocoloring with `zTable n` homogeneous classes,
and some `n`-vertex graph has none with `zTable n - 1`. -/
theorem cochromatic_table (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 19) :
    CochromaticTwenty.CochromaticValue n (CochromaticTwenty.zTable n) :=
  ⟨fun G ↦ CochromaticTwenty.table_upper n hn1 hn G,
    CochromaticTwenty.table_lower n hn1 hn⟩

#print axioms cochromatic_table

/-- **The published table, as a statement about `z(n)` itself.**  For every
`1 ≤ n ≤ 19`, the maximum of the cochromatic number over all simple graphs on
`n` labelled vertices equals the tabulated value. -/
theorem cochromatic_zmax_table (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 19) :
    CochromaticTwenty.zmax n = CochromaticTwenty.zTable n :=
  (CochromaticTwenty.zmax_eq_iff n (CochromaticTwenty.zTable n)
    (CochromaticTwenty.one_le_zTable n hn1 hn)).mpr (cochromatic_table n hn1 hn)

#print axioms cochromatic_zmax_table

/-- `z(20) = 6`: the frozen twenty-vertex target, restated for `zmax`. -/
theorem cochromatic_zmax_twenty : CochromaticTwenty.zmax 20 = 6 :=
  (CochromaticTwenty.zmax_eq_iff 20 6 (by norm_num)).mpr
    ⟨cochromatic_twenty.1, cochromatic_twenty.2⟩

#print axioms cochromatic_zmax_twenty

/-- `z(12) = 4`: the twelve-vertex value the problem page asks for in
particular, restated for `zmax`. -/
theorem cochromatic_zmax_twelve : CochromaticTwenty.zmax 12 = 4 :=
  cochromatic_zmax_table 12 (by norm_num) (by norm_num)

#print axioms cochromatic_zmax_twelve

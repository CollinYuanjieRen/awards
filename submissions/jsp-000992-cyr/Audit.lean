import Erdos1187ModFour

#print axioms erdos_1187_second_question_closed
#print axioms Erdos1187.no_mono_ap_colourMod4
#print axioms Erdos1187.colourTwo_no_three_ap

/-- Erdős #1187, second question: a `4`-colouring with no monochromatic pair at prime distance. -/
example : ∃ c : ℤ → Fin 4, ∀ (a : ℤ) (p : ℕ), p.Prime → c a ≠ c (a + p) :=
  erdos_1187_second_question_closed.1

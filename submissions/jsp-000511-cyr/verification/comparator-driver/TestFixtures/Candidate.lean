namespace ComparatorFixture

/-- Candidate copy of the supporting definition. -/
def P : Prop := True

/-- Candidate copy included so the definition-body negative test has a controlled target. -/
def expectedStatement : Prop := P

/-- Small honest proof accepted by the infrastructure self-test. -/
theorem root : P := True.intro

end ComparatorFixture

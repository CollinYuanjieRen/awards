import MerLeanExperiment.RunningLower
import MerLeanExperiment.RunningUpper

/-- Beck's running-radius disk discrepancy bounds, with the qualitative unboundedness consequence. -/
theorem disk_discrepancy : DiskDiscrepancy.CompleteTarget :=
  ⟨DiskDiscrepancy.runningLower, DiskDiscrepancy.runningUpper, DiskDiscrepancy.noUniformDiskBound⟩

#print axioms disk_discrepancy

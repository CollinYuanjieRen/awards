import Erdos820HTable

open Erdos820

#print axioms erdos_820_table_closed
#print axioms Erdos820.H_table

/-- Erdős #820: `H(6) = 18`. -/
example : H 6 = 18 := erdos_820_table_closed.2.2.2.2.2.1

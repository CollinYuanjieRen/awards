import CameronErdos
import Jsp616

/-! Kernel audit. Expected for every line: `[propext, Classical.choice, Quot.sound]` (or a subset). -/

#check @CameronErdos.cameronErdos
#print CameronErdos.CameronErdosStatement
#print CameronErdos.sumFreeCount
#print CameronErdos.IsSumFree
#print axioms CameronErdos.cameronErdos
#print axioms CameronErdos.eventually_exceptional_le
#print axioms CameronErdos.cameronErdos_of_exceptional_bound
#print axioms CameronErdos.intervalSumFreeCount_sq_le
#print axioms CameronErdos.prop7
#print axioms CameronErdos.eventually_container_family
#print axioms Finset.add_kneser
#print axioms Erdos748.f_ge_two_pow_half
#print axioms CameronErdos.tendsto_logb_sumFreeCount_div
#print axioms CameronErdos.sumFreeCount_isBigO
#print axioms CameronErdos.two_pow_half_isBigO_sumFreeCount
#print axioms CameronErdos.sumFreeCount_eq_two_pow_half_add_littleO

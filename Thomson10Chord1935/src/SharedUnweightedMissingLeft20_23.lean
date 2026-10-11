import SharedUnweightedData
open Thomson10SharedUnweighted
namespace Thomson10SharedUnweightedMissingLeft20_23
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem row_20 : leftRowCheck 20 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_20
theorem row_21 : leftRowCheck 21 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_21
theorem row_22 : leftRowCheck 22 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_22
theorem row_23 : leftRowCheck 23 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_23
end Thomson10SharedUnweightedMissingLeft20_23

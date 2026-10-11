import SharedUnweightedData
open Thomson10SharedUnweighted
namespace Thomson10SharedUnweightedMissingLeft12_15
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem row_12 : leftRowCheck 12 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_12
theorem row_13 : leftRowCheck 13 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_13
theorem row_14 : leftRowCheck 14 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_14
theorem row_15 : leftRowCheck 15 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_15
end Thomson10SharedUnweightedMissingLeft12_15

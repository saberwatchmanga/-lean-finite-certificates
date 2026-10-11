import SharedUnweightedData
open Thomson10SharedUnweighted
namespace Thomson10SharedUnweightedMissingLeft16_19
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem row_16 : leftRowCheck 16 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_16
theorem row_17 : leftRowCheck 17 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_17
theorem row_18 : leftRowCheck 18 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_18
theorem row_19 : leftRowCheck 19 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_19
end Thomson10SharedUnweightedMissingLeft16_19

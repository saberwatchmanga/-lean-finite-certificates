import SharedUnweightedData
open Thomson10SharedUnweighted
namespace Thomson10SharedUnweightedMissingLeft32_33
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem row_32 : leftRowCheck 32 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_32
theorem row_33 : leftRowCheck 33 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_33
end Thomson10SharedUnweightedMissingLeft32_33

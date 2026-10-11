import SharedUnweightedData
open Thomson10SharedUnweighted
namespace Thomson10SharedUnweightedMissingLeft08_11
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem row_08 : leftRowCheck 8 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_08
theorem row_09 : leftRowCheck 9 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_09
theorem row_10 : leftRowCheck 10 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_10
theorem row_11 : leftRowCheck 11 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_11
end Thomson10SharedUnweightedMissingLeft08_11

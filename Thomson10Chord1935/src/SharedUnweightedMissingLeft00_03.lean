import SharedUnweightedData
open Thomson10SharedUnweighted
namespace Thomson10SharedUnweightedMissingLeft00_03
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem row_00 : leftRowCheck 0 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_00
theorem row_01 : leftRowCheck 1 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_01
theorem row_02 : leftRowCheck 2 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_02
theorem row_03 : leftRowCheck 3 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_03
end Thomson10SharedUnweightedMissingLeft00_03

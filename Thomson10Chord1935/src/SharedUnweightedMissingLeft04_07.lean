import SharedUnweightedData
open Thomson10SharedUnweighted
namespace Thomson10SharedUnweightedMissingLeft04_07
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem row_04 : leftRowCheck 4 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_04
theorem row_05 : leftRowCheck 5 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_05
theorem row_06 : leftRowCheck 6 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_06
theorem row_07 : leftRowCheck 7 := by
  unfold leftRowCheck
  intro hi
  decide +kernel
#print axioms row_07
end Thomson10SharedUnweightedMissingLeft04_07

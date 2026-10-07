import IndexedMatrixPrimitives

noncomputable section
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10Geometry Thomson10Stability Thomson10Bridge
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def distanceNode (k : PairKind) : Nat :=
  match k with
  | .polePair => 5
  | .poleNear => 20
  | .poleFar => 22
  | .ringAdjacent => 23
  | .ringOpposite => 24
  | .crossNear => 28
  | .crossFar => 30

theorem indexed_distance_matches (h : ℝ) (k : PairKind) :
    evaluate matrixProgram h (distanceNode k) = pairKindTarget h k := by
  cases k <;>
    norm_num [distanceNode, primitive_matches0, primitive_matches1, primitive_matches2, primitive_matches3, primitive_matches4, primitive_matches5, primitive_matches6, primitive_matches7, primitive_matches8, primitive_matches9, primitive_matches10, primitive_matches11, primitive_matches12, primitive_matches13, primitive_matches14, primitive_matches15, primitive_matches16, primitive_matches17, primitive_matches18, primitive_matches19, primitive_matches20, primitive_matches21, primitive_matches22, primitive_matches23, primitive_matches24, primitive_matches25, primitive_matches26, primitive_matches27, primitive_matches28, primitive_matches29, primitive_matches30, primitive_matches31, primitive_matches32, primitive_matches33, primitive_matches34, primitive_matches35, primitive_matches36, primitive_matches37, primitive_matches38, primitive_matches39, primitive_matches40, primitive_matches41, primitive_matches42, primitive_matches43, primitive_matches44, primitive_matches45, primitive_matches46, primitive_matches47, primitive_matches48, primitive_matches49, primitive_matches50, primitive_matches51, primitive_matches52, primitive_matches53, primitive_matches54, primitive_matches55, primitive_matches56, primitive_matches57, primitive_matches58, primitive_matches59, primitive_matches60, primitive_matches61, primitive_matches62, primitive_matches63, primitive_matches64, primitive_matches65, primitive_matches66, primitive_matches67, primitive_matches68, primitive_matches69, primitive_matches70, primitive_matches71, primitive_matches72, primitive_matches73, primitive_matches74, primitive_matches75, primitive_matches76, primitive_matches77, primitive_matches78, primitive_matches79, primitive_matches80, primitive_matches81, primitive_matches82, primitive_matches83, primitive_matches84, primitive_matches85, primitive_matches86, primitiveValue0, primitiveValue1, primitiveValue2, primitiveValue3, primitiveValue4, primitiveValue5, primitiveValue6, primitiveValue7, primitiveValue8, primitiveValue9, primitiveValue10, primitiveValue11, primitiveValue12, primitiveValue13, primitiveValue14, primitiveValue15, primitiveValue16, primitiveValue17, primitiveValue18, primitiveValue19, primitiveValue20, primitiveValue21, primitiveValue22, primitiveValue23, primitiveValue24, primitiveValue25, primitiveValue26, primitiveValue27, primitiveValue28, primitiveValue29, primitiveValue30, primitiveValue31, primitiveValue32, primitiveValue33, primitiveValue34, primitiveValue35, primitiveValue36, primitiveValue37, primitiveValue38, primitiveValue39, primitiveValue40, primitiveValue41, primitiveValue42, primitiveValue43, primitiveValue44, primitiveValue45, primitiveValue46, primitiveValue47, primitiveValue48, primitiveValue49, primitiveValue50, primitiveValue51, primitiveValue52, primitiveValue53, primitiveValue54, primitiveValue55, primitiveValue56, primitiveValue57, primitiveValue58, primitiveValue59, primitiveValue60, primitiveValue61, primitiveValue62, primitiveValue63, primitiveValue64, primitiveValue65, primitiveValue66, primitiveValue67, primitiveValue68, primitiveValue69, primitiveValue70, primitiveValue71, primitiveValue72, primitiveValue73, primitiveValue74, primitiveValue75, primitiveValue76, primitiveValue77, primitiveValue78, primitiveValue79, primitiveValue80, primitiveValue81, primitiveValue82, primitiveValue83, primitiveValue84, primitiveValue85, primitiveValue86,
      pairKindTarget, distanceWeightOne, distanceWeightThree, distanceWeightFive,
      geoS, Thomson10Family.s, pow_two, mul_comm, mul_left_comm, mul_assoc]

def weightOneNode (k : PairKind) : Nat :=
  match k with
  | .polePair => 33
  | .poleNear => 41
  | .poleFar => 49
  | .ringAdjacent => 57
  | .ringOpposite => 65
  | .crossNear => 73
  | .crossFar => 81

theorem indexed_weightOne_matches (h : ℝ) (k : PairKind) :
    evaluate matrixProgram h (weightOneNode k) = distanceWeightOne h k := by
  cases k <;>
    norm_num [weightOneNode, primitive_matches0, primitive_matches1, primitive_matches2, primitive_matches3, primitive_matches4, primitive_matches5, primitive_matches6, primitive_matches7, primitive_matches8, primitive_matches9, primitive_matches10, primitive_matches11, primitive_matches12, primitive_matches13, primitive_matches14, primitive_matches15, primitive_matches16, primitive_matches17, primitive_matches18, primitive_matches19, primitive_matches20, primitive_matches21, primitive_matches22, primitive_matches23, primitive_matches24, primitive_matches25, primitive_matches26, primitive_matches27, primitive_matches28, primitive_matches29, primitive_matches30, primitive_matches31, primitive_matches32, primitive_matches33, primitive_matches34, primitive_matches35, primitive_matches36, primitive_matches37, primitive_matches38, primitive_matches39, primitive_matches40, primitive_matches41, primitive_matches42, primitive_matches43, primitive_matches44, primitive_matches45, primitive_matches46, primitive_matches47, primitive_matches48, primitive_matches49, primitive_matches50, primitive_matches51, primitive_matches52, primitive_matches53, primitive_matches54, primitive_matches55, primitive_matches56, primitive_matches57, primitive_matches58, primitive_matches59, primitive_matches60, primitive_matches61, primitive_matches62, primitive_matches63, primitive_matches64, primitive_matches65, primitive_matches66, primitive_matches67, primitive_matches68, primitive_matches69, primitive_matches70, primitive_matches71, primitive_matches72, primitive_matches73, primitive_matches74, primitive_matches75, primitive_matches76, primitive_matches77, primitive_matches78, primitive_matches79, primitive_matches80, primitive_matches81, primitive_matches82, primitive_matches83, primitive_matches84, primitive_matches85, primitive_matches86, primitiveValue0, primitiveValue1, primitiveValue2, primitiveValue3, primitiveValue4, primitiveValue5, primitiveValue6, primitiveValue7, primitiveValue8, primitiveValue9, primitiveValue10, primitiveValue11, primitiveValue12, primitiveValue13, primitiveValue14, primitiveValue15, primitiveValue16, primitiveValue17, primitiveValue18, primitiveValue19, primitiveValue20, primitiveValue21, primitiveValue22, primitiveValue23, primitiveValue24, primitiveValue25, primitiveValue26, primitiveValue27, primitiveValue28, primitiveValue29, primitiveValue30, primitiveValue31, primitiveValue32, primitiveValue33, primitiveValue34, primitiveValue35, primitiveValue36, primitiveValue37, primitiveValue38, primitiveValue39, primitiveValue40, primitiveValue41, primitiveValue42, primitiveValue43, primitiveValue44, primitiveValue45, primitiveValue46, primitiveValue47, primitiveValue48, primitiveValue49, primitiveValue50, primitiveValue51, primitiveValue52, primitiveValue53, primitiveValue54, primitiveValue55, primitiveValue56, primitiveValue57, primitiveValue58, primitiveValue59, primitiveValue60, primitiveValue61, primitiveValue62, primitiveValue63, primitiveValue64, primitiveValue65, primitiveValue66, primitiveValue67, primitiveValue68, primitiveValue69, primitiveValue70, primitiveValue71, primitiveValue72, primitiveValue73, primitiveValue74, primitiveValue75, primitiveValue76, primitiveValue77, primitiveValue78, primitiveValue79, primitiveValue80, primitiveValue81, primitiveValue82, primitiveValue83, primitiveValue84, primitiveValue85, primitiveValue86,
      pairKindTarget, distanceWeightOne, distanceWeightThree, distanceWeightFive,
      geoS, Thomson10Family.s, pow_two, mul_comm, mul_left_comm, mul_assoc]

def weightThreeNode (k : PairKind) : Nat :=
  match k with
  | .polePair => 35
  | .poleNear => 43
  | .poleFar => 51
  | .ringAdjacent => 59
  | .ringOpposite => 67
  | .crossNear => 75
  | .crossFar => 83

theorem indexed_weightThree_matches (h : ℝ) (k : PairKind) :
    evaluate matrixProgram h (weightThreeNode k) = distanceWeightThree h k := by
  cases k <;>
    norm_num [weightThreeNode, primitive_matches0, primitive_matches1, primitive_matches2, primitive_matches3, primitive_matches4, primitive_matches5, primitive_matches6, primitive_matches7, primitive_matches8, primitive_matches9, primitive_matches10, primitive_matches11, primitive_matches12, primitive_matches13, primitive_matches14, primitive_matches15, primitive_matches16, primitive_matches17, primitive_matches18, primitive_matches19, primitive_matches20, primitive_matches21, primitive_matches22, primitive_matches23, primitive_matches24, primitive_matches25, primitive_matches26, primitive_matches27, primitive_matches28, primitive_matches29, primitive_matches30, primitive_matches31, primitive_matches32, primitive_matches33, primitive_matches34, primitive_matches35, primitive_matches36, primitive_matches37, primitive_matches38, primitive_matches39, primitive_matches40, primitive_matches41, primitive_matches42, primitive_matches43, primitive_matches44, primitive_matches45, primitive_matches46, primitive_matches47, primitive_matches48, primitive_matches49, primitive_matches50, primitive_matches51, primitive_matches52, primitive_matches53, primitive_matches54, primitive_matches55, primitive_matches56, primitive_matches57, primitive_matches58, primitive_matches59, primitive_matches60, primitive_matches61, primitive_matches62, primitive_matches63, primitive_matches64, primitive_matches65, primitive_matches66, primitive_matches67, primitive_matches68, primitive_matches69, primitive_matches70, primitive_matches71, primitive_matches72, primitive_matches73, primitive_matches74, primitive_matches75, primitive_matches76, primitive_matches77, primitive_matches78, primitive_matches79, primitive_matches80, primitive_matches81, primitive_matches82, primitive_matches83, primitive_matches84, primitive_matches85, primitive_matches86, primitiveValue0, primitiveValue1, primitiveValue2, primitiveValue3, primitiveValue4, primitiveValue5, primitiveValue6, primitiveValue7, primitiveValue8, primitiveValue9, primitiveValue10, primitiveValue11, primitiveValue12, primitiveValue13, primitiveValue14, primitiveValue15, primitiveValue16, primitiveValue17, primitiveValue18, primitiveValue19, primitiveValue20, primitiveValue21, primitiveValue22, primitiveValue23, primitiveValue24, primitiveValue25, primitiveValue26, primitiveValue27, primitiveValue28, primitiveValue29, primitiveValue30, primitiveValue31, primitiveValue32, primitiveValue33, primitiveValue34, primitiveValue35, primitiveValue36, primitiveValue37, primitiveValue38, primitiveValue39, primitiveValue40, primitiveValue41, primitiveValue42, primitiveValue43, primitiveValue44, primitiveValue45, primitiveValue46, primitiveValue47, primitiveValue48, primitiveValue49, primitiveValue50, primitiveValue51, primitiveValue52, primitiveValue53, primitiveValue54, primitiveValue55, primitiveValue56, primitiveValue57, primitiveValue58, primitiveValue59, primitiveValue60, primitiveValue61, primitiveValue62, primitiveValue63, primitiveValue64, primitiveValue65, primitiveValue66, primitiveValue67, primitiveValue68, primitiveValue69, primitiveValue70, primitiveValue71, primitiveValue72, primitiveValue73, primitiveValue74, primitiveValue75, primitiveValue76, primitiveValue77, primitiveValue78, primitiveValue79, primitiveValue80, primitiveValue81, primitiveValue82, primitiveValue83, primitiveValue84, primitiveValue85, primitiveValue86,
      pairKindTarget, distanceWeightOne, distanceWeightThree, distanceWeightFive,
      geoS, Thomson10Family.s, pow_two, mul_comm, mul_left_comm, mul_assoc]

def weightFiveNode (k : PairKind) : Nat :=
  match k with
  | .polePair => 38
  | .poleNear => 46
  | .poleFar => 54
  | .ringAdjacent => 62
  | .ringOpposite => 70
  | .crossNear => 78
  | .crossFar => 86

theorem indexed_weightFive_matches (h : ℝ) (k : PairKind) :
    evaluate matrixProgram h (weightFiveNode k) = distanceWeightFive h k := by
  cases k <;>
    norm_num [weightFiveNode, primitive_matches0, primitive_matches1, primitive_matches2, primitive_matches3, primitive_matches4, primitive_matches5, primitive_matches6, primitive_matches7, primitive_matches8, primitive_matches9, primitive_matches10, primitive_matches11, primitive_matches12, primitive_matches13, primitive_matches14, primitive_matches15, primitive_matches16, primitive_matches17, primitive_matches18, primitive_matches19, primitive_matches20, primitive_matches21, primitive_matches22, primitive_matches23, primitive_matches24, primitive_matches25, primitive_matches26, primitive_matches27, primitive_matches28, primitive_matches29, primitive_matches30, primitive_matches31, primitive_matches32, primitive_matches33, primitive_matches34, primitive_matches35, primitive_matches36, primitive_matches37, primitive_matches38, primitive_matches39, primitive_matches40, primitive_matches41, primitive_matches42, primitive_matches43, primitive_matches44, primitive_matches45, primitive_matches46, primitive_matches47, primitive_matches48, primitive_matches49, primitive_matches50, primitive_matches51, primitive_matches52, primitive_matches53, primitive_matches54, primitive_matches55, primitive_matches56, primitive_matches57, primitive_matches58, primitive_matches59, primitive_matches60, primitive_matches61, primitive_matches62, primitive_matches63, primitive_matches64, primitive_matches65, primitive_matches66, primitive_matches67, primitive_matches68, primitive_matches69, primitive_matches70, primitive_matches71, primitive_matches72, primitive_matches73, primitive_matches74, primitive_matches75, primitive_matches76, primitive_matches77, primitive_matches78, primitive_matches79, primitive_matches80, primitive_matches81, primitive_matches82, primitive_matches83, primitive_matches84, primitive_matches85, primitive_matches86, primitiveValue0, primitiveValue1, primitiveValue2, primitiveValue3, primitiveValue4, primitiveValue5, primitiveValue6, primitiveValue7, primitiveValue8, primitiveValue9, primitiveValue10, primitiveValue11, primitiveValue12, primitiveValue13, primitiveValue14, primitiveValue15, primitiveValue16, primitiveValue17, primitiveValue18, primitiveValue19, primitiveValue20, primitiveValue21, primitiveValue22, primitiveValue23, primitiveValue24, primitiveValue25, primitiveValue26, primitiveValue27, primitiveValue28, primitiveValue29, primitiveValue30, primitiveValue31, primitiveValue32, primitiveValue33, primitiveValue34, primitiveValue35, primitiveValue36, primitiveValue37, primitiveValue38, primitiveValue39, primitiveValue40, primitiveValue41, primitiveValue42, primitiveValue43, primitiveValue44, primitiveValue45, primitiveValue46, primitiveValue47, primitiveValue48, primitiveValue49, primitiveValue50, primitiveValue51, primitiveValue52, primitiveValue53, primitiveValue54, primitiveValue55, primitiveValue56, primitiveValue57, primitiveValue58, primitiveValue59, primitiveValue60, primitiveValue61, primitiveValue62, primitiveValue63, primitiveValue64, primitiveValue65, primitiveValue66, primitiveValue67, primitiveValue68, primitiveValue69, primitiveValue70, primitiveValue71, primitiveValue72, primitiveValue73, primitiveValue74, primitiveValue75, primitiveValue76, primitiveValue77, primitiveValue78, primitiveValue79, primitiveValue80, primitiveValue81, primitiveValue82, primitiveValue83, primitiveValue84, primitiveValue85, primitiveValue86,
      pairKindTarget, distanceWeightOne, distanceWeightThree, distanceWeightFive,
      geoS, Thomson10Family.s, pow_two, mul_comm, mul_left_comm, mul_assoc]

#print axioms indexed_distance_matches
#print axioms indexed_weightOne_matches
#print axioms indexed_weightThree_matches
#print axioms indexed_weightFive_matches
end Thomson10IndexedMatrix

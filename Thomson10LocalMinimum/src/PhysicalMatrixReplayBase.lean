import IndexedMatrixWeights
import SparseSliceFormula

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10Geometry Thomson10Stability Thomson10Bridge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def replayPoint (h : ℝ) (i : Fin 10) : R3 := fun k =>
  evaluate matrixProgram h (pointNode i k)
def replayMeridian (h : ℝ) (i : Fin 10) : R3 := fun k =>
  evaluate matrixProgram h (meridianNode i k)
def replayAzimuth (h : ℝ) (i : Fin 10) : R3 := fun k =>
  evaluate matrixProgram h (azimuthNode i k)
def replayDirection (h : ℝ) (a : Fin 17) : R3 :=
  if sliceFullIndex a % 2 = 0 then replayMeridian h (sliceOwner a)
  else replayAzimuth h (sliceOwner a)
def replayWeightOne (h : ℝ) (k : PairKind) : ℝ := evaluate matrixProgram h (weightOneNode k)
def replayWeightThree (h : ℝ) (k : PairKind) : ℝ := evaluate matrixProgram h (weightThreeNode k)
def replayWeightFive (h : ℝ) (k : PairKind) : ℝ := evaluate matrixProgram h (weightFiveNode k)
def replayPair (h : ℝ) (a b : Fin 17) (i j : Fin 10) : ℝ :=
  if (sliceOwner a = i ∨ sliceOwner a = j) ∧
      (sliceOwner b = i ∨ sliceOwner b = j) then
    let u := if sliceOwner a=i then replayDirection h a else -replayDirection h a
    let w := if sliceOwner b=i then replayDirection h b else -replayDirection h b
    replayWeightFive h (pairKind i j) * dot3 (replayPoint h i-replayPoint h j) u *
        dot3 (replayPoint h i-replayPoint h j) w -
      replayWeightThree h (pairKind i j) * dot3 u w +
      (if sliceOwner a=sliceOwner b then
        replayWeightOne h (pairKind i j) * dot3 (replayDirection h a) (replayDirection h b)
       else 0)
  else 0
def replayMatrix (h : ℝ) (a b : Fin 17) : ℝ :=
  ∑ ij ∈ Thomson10Stability.pairSet, replayPair h a b ij.1 ij.2
def activeReplayPairs (a b : Fin 17) : Finset (Fin 10 × Fin 10) :=
  Thomson10Stability.pairSet.filter (fun ij =>
    (sliceOwner a=ij.1 ∨ sliceOwner a=ij.2) ∧
    (sliceOwner b=ij.1 ∨ sliceOwner b=ij.2))

theorem replay_point_eq (h : ℝ) (i : Fin 10) : replayPoint h i = configuration h i := by
  funext k
  exact indexed_point_matches h i k
theorem replay_meridian_eq (h : ℝ) (i : Fin 10) : replayMeridian h i = meridianFrame h i := by
  funext k
  exact indexed_meridian_matches h i k
theorem replay_azimuth_eq (h : ℝ) (i : Fin 10) : replayAzimuth h i = azimuthFrame h i := by
  funext k
  exact indexed_azimuth_matches h i k
theorem replay_direction_eq (h : ℝ) (a : Fin 17) : replayDirection h a = sliceDirection h a := by
  simp [replayDirection,sliceDirection,replay_meridian_eq,replay_azimuth_eq]
theorem replay_pair_eq_sparse (h : ℝ) (a b : Fin 17) (i j : Fin 10) :
    replayPair h a b i j = sparseSlicePair h a b i j := by
  simp [replayPair,sparseSlicePair,replay_point_eq,replay_direction_eq,
    replayWeightOne,replayWeightThree,replayWeightFive,
    indexed_weightOne_matches,indexed_weightThree_matches,indexed_weightFive_matches]
theorem replay_matrix_eq_sparse (h : ℝ) (a b : Fin 17) :
    replayMatrix h a b = sparseSliceMatrix h a b := by
  unfold replayMatrix sparseSliceMatrix
  apply Finset.sum_congr rfl
  intro ij hij
  exact replay_pair_eq_sparse h a b ij.1 ij.2
theorem replay_matrix_eq_physical (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1) (a b : Fin 17) :
    replayMatrix h a b = physicalSliceMatrix h a b := by
  rw [replay_matrix_eq_sparse]
  exact (entire_physical_matrix_eq_sparse hh0 hh1 a b).symm
theorem replay_matrix_restrict (h : ℝ) (a b : Fin 17) :
    replayMatrix h a b = ∑ ij ∈ activeReplayPairs a b, replayPair h a b ij.1 ij.2 := by
  unfold replayMatrix activeReplayPairs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases hc : (sliceOwner a=ij.1 ∨ sliceOwner a=ij.2) ∧
      (sliceOwner b=ij.1 ∨ sliceOwner b=ij.2)
  · simp [hc]
  · simp [replayPair,hc]

#print axioms replay_pair_eq_sparse
#print axioms replay_matrix_eq_physical
#print axioms replay_matrix_restrict
def physicalReplayNode (i j : Fin 17) : Nat :=
  match i.val with
  | 0 => match j.val with
    | 0 => 123
    | 1 => 128
    | 2 => 136
    | 3 => 142
    | 4 => 0
    | 5 => 0
    | 6 => 144
    | 7 => 0
    | 8 => 146
    | 9 => 154
    | 10 => 162
    | 11 => 169
    | 12 => 175
    | 13 => 179
    | 14 => 184
    | 15 => 189
    | _ => 193
  | 1 => match j.val with
    | 0 => 128
    | 1 => 201
    | 2 => 0
    | 3 => 0
    | 4 => 144
    | 5 => 136
    | 6 => 0
    | 7 => 142
    | 8 => 0
    | 9 => 154
    | 10 => 202
    | 11 => 179
    | 12 => 205
    | 13 => 169
    | 14 => 208
    | 15 => 189
    | _ => 209
  | 2 => match j.val with
    | 0 => 136
    | 1 => 0
    | 2 => 276
    | 3 => 284
    | 4 => 0
    | 5 => 289
    | 6 => 295
    | 7 => 299
    | 8 => 303
    | 9 => 313
    | 10 => 320
    | 11 => 325
    | 12 => 332
    | 13 => 341
    | 14 => 347
    | 15 => 352
    | _ => 358
  | 3 => match j.val with
    | 0 => 142
    | 1 => 0
    | 2 => 284
    | 3 => 413
    | 4 => 434
    | 5 => 437
    | 6 => 443
    | 7 => 446
    | 8 => 451
    | 9 => 460
    | 10 => 467
    | 11 => 472
    | 12 => 479
    | 13 => 488
    | 14 => 494
    | 15 => 499
    | _ => 505
  | 4 => match j.val with
    | 0 => 0
    | 1 => 144
    | 2 => 0
    | 3 => 434
    | 4 => 554
    | 5 => 559
    | 6 => 561
    | 7 => 564
    | 8 => 566
    | 9 => 570
    | 10 => 574
    | 11 => 579
    | 12 => 582
    | 13 => 586
    | 14 => 591
    | 15 => 595
    | _ => 598
  | 5 => match j.val with
    | 0 => 0
    | 1 => 136
    | 2 => 289
    | 3 => 437
    | 4 => 559
    | 5 => 610
    | 6 => 627
    | 7 => 284
    | 8 => 0
    | 9 => 313
    | 10 => 631
    | 11 => 341
    | 12 => 635
    | 13 => 325
    | 14 => 639
    | 15 => 352
    | _ => 643
  | 6 => match j.val with
    | 0 => 144
    | 1 => 0
    | 2 => 295
    | 3 => 443
    | 4 => 561
    | 5 => 627
    | 6 => 662
    | 7 => 0
    | 8 => 654
    | 9 => 665
    | 10 => 668
    | 11 => 671
    | 12 => 674
    | 13 => 677
    | 14 => 680
    | 15 => 683
    | _ => 686
  | 7 => match j.val with
    | 0 => 0
    | 1 => 142
    | 2 => 299
    | 3 => 446
    | 4 => 564
    | 5 => 284
    | 6 => 0
    | 7 => 698
    | 8 => 715
    | 9 => 460
    | 10 => 719
    | 11 => 488
    | 12 => 723
    | 13 => 472
    | 14 => 727
    | 15 => 499
    | _ => 731
  | 8 => match j.val with
    | 0 => 146
    | 1 => 0
    | 2 => 303
    | 3 => 451
    | 4 => 566
    | 5 => 0
    | 6 => 654
    | 7 => 715
    | 8 => 763
    | 9 => 767
    | 10 => 770
    | 11 => 774
    | 12 => 778
    | 13 => 781
    | 14 => 784
    | 15 => 787
    | _ => 790
  | 9 => match j.val with
    | 0 => 154
    | 1 => 154
    | 2 => 313
    | 3 => 460
    | 4 => 570
    | 5 => 313
    | 6 => 665
    | 7 => 460
    | 8 => 767
    | 9 => 853
    | 10 => 922
    | 11 => 935
    | 12 => 941
    | 13 => 935
    | 14 => 950
    | 15 => 958
    | _ => 964
  | 10 => match j.val with
    | 0 => 162
    | 1 => 202
    | 2 => 320
    | 3 => 467
    | 4 => 574
    | 5 => 631
    | 6 => 668
    | 7 => 719
    | 8 => 770
    | 9 => 922
    | 10 => 1024
    | 11 => 1030
    | 12 => 1036
    | 13 => 1043
    | 14 => 1050
    | 15 => 1055
    | _ => 1060
  | 11 => match j.val with
    | 0 => 169
    | 1 => 179
    | 2 => 325
    | 3 => 472
    | 4 => 579
    | 5 => 341
    | 6 => 671
    | 7 => 488
    | 8 => 774
    | 9 => 935
    | 10 => 1030
    | 11 => 1131
    | 12 => 1194
    | 13 => 1202
    | 14 => 1209
    | 15 => 1219
    | _ => 1226
  | 12 => match j.val with
    | 0 => 175
    | 1 => 205
    | 2 => 332
    | 3 => 479
    | 4 => 582
    | 5 => 635
    | 6 => 674
    | 7 => 723
    | 8 => 778
    | 9 => 941
    | 10 => 1036
    | 11 => 1194
    | 12 => 1284
    | 13 => 1289
    | 14 => 1294
    | 15 => 1299
    | _ => 1304
  | 13 => match j.val with
    | 0 => 179
    | 1 => 169
    | 2 => 341
    | 3 => 488
    | 4 => 586
    | 5 => 325
    | 6 => 677
    | 7 => 472
    | 8 => 781
    | 9 => 935
    | 10 => 1043
    | 11 => 1202
    | 12 => 1289
    | 13 => 1316
    | 14 => 1378
    | 15 => 1219
    | _ => 1384
  | 14 => match j.val with
    | 0 => 184
    | 1 => 208
    | 2 => 347
    | 3 => 494
    | 4 => 591
    | 5 => 639
    | 6 => 680
    | 7 => 727
    | 8 => 784
    | 9 => 950
    | 10 => 1050
    | 11 => 1209
    | 12 => 1294
    | 13 => 1378
    | 14 => 1440
    | 15 => 1445
    | _ => 1450
  | 15 => match j.val with
    | 0 => 189
    | 1 => 189
    | 2 => 352
    | 3 => 499
    | 4 => 595
    | 5 => 352
    | 6 => 683
    | 7 => 499
    | 8 => 787
    | 9 => 958
    | 10 => 1055
    | 11 => 1219
    | 12 => 1299
    | 13 => 1219
    | 14 => 1445
    | 15 => 1498
    | _ => 1556
  | _ => match j.val with
    | 0 => 193
    | 1 => 209
    | 2 => 358
    | 3 => 505
    | 4 => 598
    | 5 => 643
    | 6 => 686
    | 7 => 731
    | 8 => 790
    | 9 => 964
    | 10 => 1060
    | 11 => 1226
    | 12 => 1304
    | 13 => 1384
    | 14 => 1450
    | 15 => 1556
    | _ => 1601

theorem physical_replay_nodes_symmetric : ∀ i j,
    physicalReplayNode i j = physicalReplayNode j i := by
  decide +kernel
theorem physical_replay_nodes_in_range : ∀ i j,
    physicalReplayNode i j < matrixNodeCount := by
  decide +kernel

#print axioms physical_replay_nodes_symmetric
#print axioms physical_replay_nodes_in_range
end Thomson10IndexedMatrix

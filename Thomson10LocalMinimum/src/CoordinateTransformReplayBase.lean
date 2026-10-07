import IndexedMatrixPrimitives
import IndexedMatrixPositivity
import CoordinateChangeCertificate

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10CoordinateChange
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

def coordinateBaseNode (i j : Fin 17) : Nat :=
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

def coordinateBaseMatrix (h : ℝ) (i j : Fin 17) : ℝ :=
  evaluate matrixProgram h (coordinateBaseNode i j)

def coordinateCongruence (A : Fin 17 → Fin 17 → ℝ) (i j : Fin 17) : ℝ :=
  ∑ a, ∑ b, coordinateChange a i * A a b * coordinateChange b j

theorem coordinate_base_nodes_symmetric : ∀ i j,
    coordinateBaseNode i j = coordinateBaseNode j i := by
  decide +kernel

theorem coordinate_base_matrix_symmetric (h : ℝ) (i j : Fin 17) :
    coordinateBaseMatrix h i j = coordinateBaseMatrix h j i := by
  unfold coordinateBaseMatrix
  rw [coordinate_base_nodes_symmetric i j]

theorem coordinateReplayStep (h : ℝ) (i : Nat) (hi : 1601 < i)
    (hrange : i < matrixNodeCount) :
    evaluate matrixProgram h i =
      nodeValue h (evaluate matrixProgram h) (matrixProgram i) :=
  indexed_value_step h i hrange

#print axioms coordinate_base_nodes_symmetric
#print axioms coordinate_base_matrix_symmetric
end Thomson10IndexedMatrix

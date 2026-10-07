import IndexedMatrixCertificate
import IntervalDominance

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10Intervals Thomson10Stability
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def transformedNode (i j : Fin 17) : Nat :=
  match i.val with
  | 0 => match j.val with
    | 0 => 5854
    | 1 => 5855
    | 2 => 5856
    | 3 => 5857
    | 4 => 5858
    | 5 => 5859
    | 6 => 5860
    | 7 => 5861
    | 8 => 5862
    | 9 => 5863
    | 10 => 5864
    | 11 => 5865
    | 12 => 5866
    | 13 => 5867
    | 14 => 5868
    | 15 => 5869
    | _ => 5870
  | 1 => match j.val with
    | 0 => 5855
    | 1 => 5871
    | 2 => 5872
    | 3 => 5873
    | 4 => 5874
    | 5 => 5875
    | 6 => 5876
    | 7 => 5877
    | 8 => 5878
    | 9 => 5879
    | 10 => 5880
    | 11 => 5881
    | 12 => 5882
    | 13 => 5883
    | 14 => 5884
    | 15 => 5885
    | _ => 5886
  | 2 => match j.val with
    | 0 => 5856
    | 1 => 5872
    | 2 => 5889
    | 3 => 5892
    | 4 => 5893
    | 5 => 5896
    | 6 => 5899
    | 7 => 5902
    | 8 => 5905
    | 9 => 5908
    | 10 => 5911
    | 11 => 5914
    | 12 => 5917
    | 13 => 5920
    | 14 => 5923
    | 15 => 5926
    | _ => 5929
  | 3 => match j.val with
    | 0 => 5857
    | 1 => 5873
    | 2 => 5892
    | 3 => 5934
    | 4 => 5937
    | 5 => 5942
    | 6 => 5947
    | 7 => 5952
    | 8 => 5957
    | 9 => 5962
    | 10 => 5967
    | 11 => 5972
    | 12 => 5977
    | 13 => 5982
    | 14 => 5987
    | 15 => 5992
    | _ => 5997
  | 4 => match j.val with
    | 0 => 5858
    | 1 => 5874
    | 2 => 5893
    | 3 => 5937
    | 4 => 6000
    | 5 => 6003
    | 6 => 6006
    | 7 => 6009
    | 8 => 6012
    | 9 => 6015
    | 10 => 6018
    | 11 => 6021
    | 12 => 6024
    | 13 => 6027
    | 14 => 6030
    | 15 => 6033
    | _ => 6036
  | 5 => match j.val with
    | 0 => 5859
    | 1 => 5875
    | 2 => 5896
    | 3 => 5942
    | 4 => 6003
    | 5 => 6045
    | 6 => 6054
    | 7 => 6063
    | 8 => 6072
    | 9 => 6081
    | 10 => 6090
    | 11 => 6099
    | 12 => 6108
    | 13 => 6117
    | 14 => 6126
    | 15 => 6135
    | _ => 6144
  | 6 => match j.val with
    | 0 => 5860
    | 1 => 5876
    | 2 => 5899
    | 3 => 5947
    | 4 => 6006
    | 5 => 6054
    | 6 => 6157
    | 7 => 6170
    | 8 => 6183
    | 9 => 6196
    | 10 => 6209
    | 11 => 6222
    | 12 => 6235
    | 13 => 6248
    | 14 => 6261
    | 15 => 6274
    | _ => 6287
  | 7 => match j.val with
    | 0 => 5861
    | 1 => 5877
    | 2 => 5902
    | 3 => 5952
    | 4 => 6009
    | 5 => 6063
    | 6 => 6170
    | 7 => 6302
    | 8 => 6317
    | 9 => 6332
    | 10 => 6347
    | 11 => 6362
    | 12 => 6377
    | 13 => 6392
    | 14 => 6407
    | 15 => 6422
    | _ => 6437
  | 8 => match j.val with
    | 0 => 5862
    | 1 => 5878
    | 2 => 5905
    | 3 => 5957
    | 4 => 6012
    | 5 => 6072
    | 6 => 6183
    | 7 => 6317
    | 8 => 6454
    | 9 => 6471
    | 10 => 6488
    | 11 => 6505
    | 12 => 6522
    | 13 => 6539
    | 14 => 6556
    | 15 => 6573
    | _ => 6590
  | 9 => match j.val with
    | 0 => 5863
    | 1 => 5879
    | 2 => 5908
    | 3 => 5962
    | 4 => 6015
    | 5 => 6081
    | 6 => 6196
    | 7 => 6332
    | 8 => 6471
    | 9 => 6609
    | 10 => 6628
    | 11 => 6647
    | 12 => 6666
    | 13 => 6685
    | 14 => 6704
    | 15 => 6723
    | _ => 6742
  | 10 => match j.val with
    | 0 => 5864
    | 1 => 5880
    | 2 => 5911
    | 3 => 5967
    | 4 => 6018
    | 5 => 6090
    | 6 => 6209
    | 7 => 6347
    | 8 => 6488
    | 9 => 6628
    | 10 => 6763
    | 11 => 6784
    | 12 => 6805
    | 13 => 6826
    | 14 => 6847
    | 15 => 6868
    | _ => 6889
  | 11 => match j.val with
    | 0 => 5865
    | 1 => 5881
    | 2 => 5914
    | 3 => 5972
    | 4 => 6021
    | 5 => 6099
    | 6 => 6222
    | 7 => 6362
    | 8 => 6505
    | 9 => 6647
    | 10 => 6784
    | 11 => 6912
    | 12 => 6935
    | 13 => 6958
    | 14 => 6981
    | 15 => 7004
    | _ => 7027
  | 12 => match j.val with
    | 0 => 5866
    | 1 => 5882
    | 2 => 5917
    | 3 => 5977
    | 4 => 6024
    | 5 => 6108
    | 6 => 6235
    | 7 => 6377
    | 8 => 6522
    | 9 => 6666
    | 10 => 6805
    | 11 => 6935
    | 12 => 7052
    | 13 => 7077
    | 14 => 7102
    | 15 => 7127
    | _ => 7152
  | 13 => match j.val with
    | 0 => 5867
    | 1 => 5883
    | 2 => 5920
    | 3 => 5982
    | 4 => 6027
    | 5 => 6117
    | 6 => 6248
    | 7 => 6392
    | 8 => 6539
    | 9 => 6685
    | 10 => 6826
    | 11 => 6958
    | 12 => 7077
    | 13 => 7179
    | 14 => 7206
    | 15 => 7233
    | _ => 7260
  | 14 => match j.val with
    | 0 => 5868
    | 1 => 5884
    | 2 => 5923
    | 3 => 5987
    | 4 => 6030
    | 5 => 6126
    | 6 => 6261
    | 7 => 6407
    | 8 => 6556
    | 9 => 6704
    | 10 => 6847
    | 11 => 6981
    | 12 => 7102
    | 13 => 7206
    | 14 => 7288
    | 15 => 7316
    | _ => 7344
  | 15 => match j.val with
    | 0 => 5869
    | 1 => 5885
    | 2 => 5926
    | 3 => 5992
    | 4 => 6033
    | 5 => 6135
    | 6 => 6274
    | 7 => 6422
    | 8 => 6573
    | 9 => 6723
    | 10 => 6868
    | 11 => 7004
    | 12 => 7127
    | 13 => 7233
    | 14 => 7316
    | 15 => 7375
    | _ => 7406
  | _ => match j.val with
    | 0 => 5870
    | 1 => 5886
    | 2 => 5929
    | 3 => 5997
    | 4 => 6036
    | 5 => 6144
    | 6 => 6287
    | 7 => 6437
    | 8 => 6590
    | 9 => 6742
    | 10 => 6889
    | 11 => 7027
    | 12 => 7152
    | 13 => 7260
    | 14 => 7344
    | 15 => 7406
    | _ => 7439

def transformedProgramBounds (i j : Fin 17) : Thomson10Arithmetic.I :=
  matrixBounds (transformedNode i j)

def transformedProgramMatrix (h : ℝ) (i j : Fin 17) : ℝ :=
  evaluate matrixProgram h (transformedNode i j)

theorem transformed_nodes_in_range : ∀ i j, transformedNode i j < matrixNodeCount := by
  decide +kernel

theorem transformed_nodes_symmetric : ∀ i j, transformedNode i j = transformedNode j i := by
  decide +kernel

theorem transformed_program_enclosed (h : ℝ) (hh : Contains matrixHeightBounds h)
    (i j : Fin 17) : Contains (transformedProgramBounds i j) (transformedProgramMatrix h i j) :=
  all_matrix_program_values_enclosed h hh (transformedNode i j) (transformed_nodes_in_range i j)

theorem transformed_program_symmetric (h : ℝ) (i j : Fin 17) :
    transformedProgramMatrix h i j = transformedProgramMatrix h j i := by
  unfold transformedProgramMatrix
  rw [transformed_nodes_symmetric i j]

theorem transformed_program_all_rows : DominanceCertificate transformedProgramBounds := by
  intro i
  fin_cases i <;> decide +kernel

theorem transformed_program_quadratic_positive (h : ℝ) (hh : Contains matrixHeightBounds h)
    (x : Fin 17 → ℝ) (hx : x ≠ 0) : 0 < quadratic (transformedProgramMatrix h) x :=
  interval_certificate_quadratic_positive transformed_program_all_rows
    (transformed_program_enclosed h hh) (transformed_program_symmetric h) x hx

#print axioms transformed_nodes_in_range
#print axioms transformed_nodes_symmetric
#print axioms transformed_program_enclosed
#print axioms transformed_program_all_rows
#print axioms transformed_program_quadratic_positive
end Thomson10IndexedMatrix

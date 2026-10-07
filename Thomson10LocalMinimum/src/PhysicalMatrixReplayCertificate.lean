import PhysicalMatrixReplayRow00
import PhysicalMatrixReplayRow01
import PhysicalMatrixReplayRow02
import PhysicalMatrixReplayRow03
import PhysicalMatrixReplayRow04
import PhysicalMatrixReplayRow05
import PhysicalMatrixReplayRow06
import PhysicalMatrixReplayRow07
import PhysicalMatrixReplayRow08
import PhysicalMatrixReplayRow09
import PhysicalMatrixReplayRow10
import PhysicalMatrixReplayRow11
import PhysicalMatrixReplayRow12
import PhysicalMatrixReplayRow13
import PhysicalMatrixReplayRow14
import PhysicalMatrixReplayRow15
import PhysicalMatrixReplayRow16

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10Geometry Thomson10Stability Thomson10Bridge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

theorem physical_replay_upper (h : ℝ) (i j : Fin 17) (hij : i.val ≤ j.val) :
    evaluate matrixProgram h (physicalReplayNode i j) = replayMatrix h i j := by
  fin_cases i
  · exact physical_replay_row_00 h j hij
  · exact physical_replay_row_01 h j hij
  · exact physical_replay_row_02 h j hij
  · exact physical_replay_row_03 h j hij
  · exact physical_replay_row_04 h j hij
  · exact physical_replay_row_05 h j hij
  · exact physical_replay_row_06 h j hij
  · exact physical_replay_row_07 h j hij
  · exact physical_replay_row_08 h j hij
  · exact physical_replay_row_09 h j hij
  · exact physical_replay_row_10 h j hij
  · exact physical_replay_row_11 h j hij
  · exact physical_replay_row_12 h j hij
  · exact physical_replay_row_13 h j hij
  · exact physical_replay_row_14 h j hij
  · exact physical_replay_row_15 h j hij
  · exact physical_replay_row_16 h j hij

theorem physical_replay_entire_matrix (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1)
    (i j : Fin 17) : evaluate matrixProgram h (physicalReplayNode i j) =
      physicalSliceMatrix h i j := by
  by_cases hij : i.val ≤ j.val
  · rw [physical_replay_upper h i j hij]
    exact replay_matrix_eq_physical h hh0 hh1 i j
  · have hji : j.val ≤ i.val := by omega
    rw [physical_replay_nodes_symmetric i j,physical_replay_upper h j i hji,
      replay_matrix_eq_physical h hh0 hh1 j i,physical_slice_matrix_symmetric h j i]

def physicalReplayBounds (i j : Fin 17) : Thomson10Arithmetic.I :=
  matrixBounds (physicalReplayNode i j)

theorem physical_entire_matrix_enclosed (h : ℝ)
    (hh : Thomson10Intervals.Contains matrixHeightBounds h) (i j : Fin 17) :
    Thomson10Intervals.Contains (physicalReplayBounds i j) (physicalSliceMatrix h i j) := by
  have hh0 : 0 < h := by
    have hlo := hh.1
    norm_num [matrixHeightBounds] at hlo
    linarith
  have hh1 : h < 1 := by
    have hhi := hh.2
    norm_num [matrixHeightBounds] at hhi
    linarith
  have hc := all_matrix_program_values_enclosed h hh (physicalReplayNode i j)
    (physical_replay_nodes_in_range i j)
  rw [physical_replay_entire_matrix h hh0 hh1 i j] at hc
  exact hc

#print axioms physical_replay_upper
#print axioms physical_replay_entire_matrix
#print axioms physical_entire_matrix_enclosed
end Thomson10IndexedMatrix

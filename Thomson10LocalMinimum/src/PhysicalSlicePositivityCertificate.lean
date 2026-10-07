import StagedTransformCertificate
import CoordinateQuadraticTransfer
import PhysicalMatrixReplayCertificate

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10CoordinateChange Thomson10Stability Thomson10Geometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem coordinate_and_physical_node_tables_agree : ∀ i j,
    coordinateBaseNode i j = physicalReplayNode i j := by
  decide +kernel

theorem coordinate_base_matrix_eq_physical (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1)
    (i j : Fin 17) : coordinateBaseMatrix h i j = physicalSliceMatrix h i j := by
  unfold coordinateBaseMatrix
  rw [coordinate_and_physical_node_tables_agree i j]
  exact physical_replay_entire_matrix h hh0 hh1 i j

theorem physical_slice_quadratic_positive (h : ℝ)
    (hh : Thomson10Intervals.Contains matrixHeightBounds h)
    (x : Fin 17 → ℝ) (hx : x ≠ 0) : 0 < quadratic (physicalSliceMatrix h) x := by
  have hh0 : 0 < h := by
    have hlo := hh.1
    norm_num [matrixHeightBounds] at hlo
    linarith
  have hh1 : h < 1 := by
    have hhi := hh.2
    norm_num [matrixHeightBounds] at hhi
    linarith
  have heq : coordinateBaseMatrix h = physicalSliceMatrix h := by
    funext i j
    exact coordinate_base_matrix_eq_physical h hh0 hh1 i j
  have hp := coordinate_base_positive_of_complete_transform_identity h hh
    (transformed_program_eq_congruence h) x hx
  rw [heq] at hp
  exact hp

theorem physical_slice_second_variation_positive (h : ℝ)
    (hh : Thomson10Intervals.Contains matrixHeightBounds h)
    (x : Fin 17 → ℝ) (hx : x ≠ 0) :
    0 < totalSecondVariation (configuration h) (coordinateVelocity (sliceBasis h) x) := by
  have hp := physical_slice_quadratic_positive h hh x hx
  rw [quadratic_eq_double_sum] at hp
  have heq : (∑ i, ∑ j, physicalSliceMatrix h i j * x i * x j) =
      ∑ i, ∑ j, x i * x j * physicalSliceMatrix h i j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq] at hp
  rw [physical_slice_second_variation_identity]
  exact hp

#print axioms coordinate_and_physical_node_tables_agree
#print axioms coordinate_base_matrix_eq_physical
#print axioms physical_slice_quadratic_positive
#print axioms physical_slice_second_variation_positive
end Thomson10IndexedMatrix

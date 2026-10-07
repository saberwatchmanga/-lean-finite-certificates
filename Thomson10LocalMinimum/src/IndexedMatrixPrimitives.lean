import IndexedMatrixCertificate
import SliceMatrix

noncomputable section
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10Geometry Thomson10Stability Thomson10Bridge
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem indexed_value_step (h : ℝ) (i : Nat) (hi : i < matrixNodeCount) :
    evaluate matrixProgram h i = nodeValue h (evaluate matrixProgram h) (matrixProgram i) := by
  apply evaluate_eq_nodeValue matrixProgram h matrixBounds i
  have hc := all_matrix_nodes_checked i hi
  simp only [certifiedNode, Bool.and_eq_true] at hc
  exact hc.1

def primitiveValue0 (h : ℝ) : ℝ := (0/1 : ℝ)
theorem primitive_step0 (h : ℝ) : evaluate matrixProgram h 0 = ((0/1 : Rat) : ℝ) := by
  have hc := indexed_value_step h 0 (by decide)
  change evaluate matrixProgram h 0 = ((0/1 : Rat) : ℝ) at hc
  exact hc
theorem primitive_matches0 (h : ℝ) : evaluate matrixProgram h 0 = primitiveValue0 h := by
  rw [primitive_step0]
  norm_num [primitiveValue0]

def primitiveValue1 (h : ℝ) : ℝ := (1/1 : ℝ)
theorem primitive_step1 (h : ℝ) : evaluate matrixProgram h 1 = ((1/1 : Rat) : ℝ) := by
  have hc := indexed_value_step h 1 (by decide)
  change evaluate matrixProgram h 1 = ((1/1 : Rat) : ℝ) at hc
  exact hc
theorem primitive_matches1 (h : ℝ) : evaluate matrixProgram h 1 = primitiveValue1 h := by
  rw [primitive_step1]
  norm_num [primitiveValue1]

def primitiveValue2 (h : ℝ) : ℝ := h
theorem primitive_step2 (h : ℝ) : evaluate matrixProgram h 2 = h := by
  have hc := indexed_value_step h 2 (by decide)
  change evaluate matrixProgram h 2 = h at hc
  exact hc
theorem primitive_matches2 (h : ℝ) : evaluate matrixProgram h 2 = primitiveValue2 h := by
  rw [primitive_step2]
  norm_num [primitiveValue2]

def primitiveValue3 (h : ℝ) : ℝ := (2/1 : ℝ)
theorem primitive_step3 (h : ℝ) : evaluate matrixProgram h 3 = ((2/1 : Rat) : ℝ) := by
  have hc := indexed_value_step h 3 (by decide)
  change evaluate matrixProgram h 3 = ((2/1 : Rat) : ℝ) at hc
  exact hc
theorem primitive_matches3 (h : ℝ) : evaluate matrixProgram h 3 = primitiveValue3 h := by
  rw [primitive_step3]
  norm_num [primitiveValue3]

def primitiveValue4 (h : ℝ) : ℝ := (3/1 : ℝ)
theorem primitive_step4 (h : ℝ) : evaluate matrixProgram h 4 = ((3/1 : Rat) : ℝ) := by
  have hc := indexed_value_step h 4 (by decide)
  change evaluate matrixProgram h 4 = ((3/1 : Rat) : ℝ) at hc
  exact hc
theorem primitive_matches4 (h : ℝ) : evaluate matrixProgram h 4 = primitiveValue4 h := by
  rw [primitive_step4]
  norm_num [primitiveValue4]

def primitiveValue5 (h : ℝ) : ℝ := (4/1 : ℝ)
theorem primitive_step5 (h : ℝ) : evaluate matrixProgram h 5 = ((4/1 : Rat) : ℝ) := by
  have hc := indexed_value_step h 5 (by decide)
  change evaluate matrixProgram h 5 = ((4/1 : Rat) : ℝ) at hc
  exact hc
theorem primitive_matches5 (h : ℝ) : evaluate matrixProgram h 5 = primitiveValue5 h := by
  rw [primitive_step5]
  norm_num [primitiveValue5]

def primitiveValue6 (h : ℝ) : ℝ := ((primitiveValue2 h) * (primitiveValue2 h))
theorem primitive_step6 (h : ℝ) : evaluate matrixProgram h 6 = ((evaluate matrixProgram h 2) * (evaluate matrixProgram h 2)) := by
  have hc := indexed_value_step h 6 (by decide)
  change evaluate matrixProgram h 6 = ((evaluate matrixProgram h 2) * (evaluate matrixProgram h 2)) at hc
  exact hc
theorem primitive_matches6 (h : ℝ) : evaluate matrixProgram h 6 = primitiveValue6 h := by
  rw [primitive_step6]
  simp only [primitive_matches2, primitiveValue6]

def primitiveValue7 (h : ℝ) : ℝ := ((primitiveValue1 h) - (primitiveValue6 h))
theorem primitive_step7 (h : ℝ) : evaluate matrixProgram h 7 = ((evaluate matrixProgram h 1) - (evaluate matrixProgram h 6)) := by
  have hc := indexed_value_step h 7 (by decide)
  change evaluate matrixProgram h 7 = ((evaluate matrixProgram h 1) - (evaluate matrixProgram h 6)) at hc
  exact hc
theorem primitive_matches7 (h : ℝ) : evaluate matrixProgram h 7 = primitiveValue7 h := by
  rw [primitive_step7]
  simp only [primitive_matches1, primitive_matches6, primitiveValue7]

def primitiveValue8 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue7 h))
theorem primitive_step8 (h : ℝ) : evaluate matrixProgram h 8 = Real.sqrt ((evaluate matrixProgram h 7)) := by
  have hc := indexed_value_step h 8 (by decide)
  change evaluate matrixProgram h 8 = Real.sqrt ((evaluate matrixProgram h 7)) at hc
  exact hc
theorem primitive_matches8 (h : ℝ) : evaluate matrixProgram h 8 = primitiveValue8 h := by
  rw [primitive_step8]
  simp only [primitive_matches7, primitiveValue8]

def primitiveValue9 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue3 h))
theorem primitive_step9 (h : ℝ) : evaluate matrixProgram h 9 = Real.sqrt ((evaluate matrixProgram h 3)) := by
  have hc := indexed_value_step h 9 (by decide)
  change evaluate matrixProgram h 9 = Real.sqrt ((evaluate matrixProgram h 3)) at hc
  exact hc
theorem primitive_matches9 (h : ℝ) : evaluate matrixProgram h 9 = primitiveValue9 h := by
  rw [primitive_step9]
  simp only [primitive_matches3, primitiveValue9]

def primitiveValue10 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue9 h))
theorem primitive_step10 (h : ℝ) : evaluate matrixProgram h 10 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 9)) := by
  have hc := indexed_value_step h 10 (by decide)
  change evaluate matrixProgram h 10 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 9)) at hc
  exact hc
theorem primitive_matches10 (h : ℝ) : evaluate matrixProgram h 10 = primitiveValue10 h := by
  rw [primitive_step10]
  simp only [primitive_matches1, primitive_matches9, primitiveValue10]

def primitiveValue11 (h : ℝ) : ℝ := ((primitiveValue8 h) * (primitiveValue10 h))
theorem primitive_step11 (h : ℝ) : evaluate matrixProgram h 11 = ((evaluate matrixProgram h 8) * (evaluate matrixProgram h 10)) := by
  have hc := indexed_value_step h 11 (by decide)
  change evaluate matrixProgram h 11 = ((evaluate matrixProgram h 8) * (evaluate matrixProgram h 10)) at hc
  exact hc
theorem primitive_matches11 (h : ℝ) : evaluate matrixProgram h 11 = primitiveValue11 h := by
  rw [primitive_step11]
  simp only [primitive_matches8, primitive_matches10, primitiveValue11]

def primitiveValue12 (h : ℝ) : ℝ := ((primitiveValue2 h) * (primitiveValue10 h))
theorem primitive_step12 (h : ℝ) : evaluate matrixProgram h 12 = ((evaluate matrixProgram h 2) * (evaluate matrixProgram h 10)) := by
  have hc := indexed_value_step h 12 (by decide)
  change evaluate matrixProgram h 12 = ((evaluate matrixProgram h 2) * (evaluate matrixProgram h 10)) at hc
  exact hc
theorem primitive_matches12 (h : ℝ) : evaluate matrixProgram h 12 = primitiveValue12 h := by
  rw [primitive_step12]
  simp only [primitive_matches2, primitive_matches10, primitiveValue12]

def primitiveValue13 (h : ℝ) : ℝ := (-1/1 : ℝ)
theorem primitive_step13 (h : ℝ) : evaluate matrixProgram h 13 = ((-1/1 : Rat) : ℝ) := by
  have hc := indexed_value_step h 13 (by decide)
  change evaluate matrixProgram h 13 = ((-1/1 : Rat) : ℝ) at hc
  exact hc
theorem primitive_matches13 (h : ℝ) : evaluate matrixProgram h 13 = primitiveValue13 h := by
  rw [primitive_step13]
  norm_num [primitiveValue13]

def primitiveValue14 (h : ℝ) : ℝ := ((primitiveValue8 h) * (primitiveValue13 h))
theorem primitive_step14 (h : ℝ) : evaluate matrixProgram h 14 = ((evaluate matrixProgram h 8) * (evaluate matrixProgram h 13)) := by
  have hc := indexed_value_step h 14 (by decide)
  change evaluate matrixProgram h 14 = ((evaluate matrixProgram h 8) * (evaluate matrixProgram h 13)) at hc
  exact hc
theorem primitive_matches14 (h : ℝ) : evaluate matrixProgram h 14 = primitiveValue14 h := by
  rw [primitive_step14]
  simp only [primitive_matches8, primitive_matches13, primitiveValue14]

def primitiveValue15 (h : ℝ) : ℝ := ((primitiveValue2 h) * (primitiveValue13 h))
theorem primitive_step15 (h : ℝ) : evaluate matrixProgram h 15 = ((evaluate matrixProgram h 2) * (evaluate matrixProgram h 13)) := by
  have hc := indexed_value_step h 15 (by decide)
  change evaluate matrixProgram h 15 = ((evaluate matrixProgram h 2) * (evaluate matrixProgram h 13)) at hc
  exact hc
theorem primitive_matches15 (h : ℝ) : evaluate matrixProgram h 15 = primitiveValue15 h := by
  rw [primitive_step15]
  simp only [primitive_matches2, primitive_matches13, primitiveValue15]

def primitiveValue16 (h : ℝ) : ℝ := ((primitiveValue11 h) * (primitiveValue13 h))
theorem primitive_step16 (h : ℝ) : evaluate matrixProgram h 16 = ((evaluate matrixProgram h 11) * (evaluate matrixProgram h 13)) := by
  have hc := indexed_value_step h 16 (by decide)
  change evaluate matrixProgram h 16 = ((evaluate matrixProgram h 11) * (evaluate matrixProgram h 13)) at hc
  exact hc
theorem primitive_matches16 (h : ℝ) : evaluate matrixProgram h 16 = primitiveValue16 h := by
  rw [primitive_step16]
  simp only [primitive_matches11, primitive_matches13, primitiveValue16]

def primitiveValue17 (h : ℝ) : ℝ := ((primitiveValue12 h) * (primitiveValue13 h))
theorem primitive_step17 (h : ℝ) : evaluate matrixProgram h 17 = ((evaluate matrixProgram h 12) * (evaluate matrixProgram h 13)) := by
  have hc := indexed_value_step h 17 (by decide)
  change evaluate matrixProgram h 17 = ((evaluate matrixProgram h 12) * (evaluate matrixProgram h 13)) at hc
  exact hc
theorem primitive_matches17 (h : ℝ) : evaluate matrixProgram h 17 = primitiveValue17 h := by
  rw [primitive_step17]
  simp only [primitive_matches12, primitive_matches13, primitiveValue17]

def primitiveValue18 (h : ℝ) : ℝ := ((primitiveValue10 h) * (primitiveValue13 h))
theorem primitive_step18 (h : ℝ) : evaluate matrixProgram h 18 = ((evaluate matrixProgram h 10) * (evaluate matrixProgram h 13)) := by
  have hc := indexed_value_step h 18 (by decide)
  change evaluate matrixProgram h 18 = ((evaluate matrixProgram h 10) * (evaluate matrixProgram h 13)) at hc
  exact hc
theorem primitive_matches18 (h : ℝ) : evaluate matrixProgram h 18 = primitiveValue18 h := by
  rw [primitive_step18]
  simp only [primitive_matches10, primitive_matches13, primitiveValue18]

def primitiveValue19 (h : ℝ) : ℝ := ((primitiveValue1 h) - (primitiveValue2 h))
theorem primitive_step19 (h : ℝ) : evaluate matrixProgram h 19 = ((evaluate matrixProgram h 1) - (evaluate matrixProgram h 2)) := by
  have hc := indexed_value_step h 19 (by decide)
  change evaluate matrixProgram h 19 = ((evaluate matrixProgram h 1) - (evaluate matrixProgram h 2)) at hc
  exact hc
theorem primitive_matches19 (h : ℝ) : evaluate matrixProgram h 19 = primitiveValue19 h := by
  rw [primitive_step19]
  simp only [primitive_matches1, primitive_matches2, primitiveValue19]

def primitiveValue20 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue19 h))
theorem primitive_step20 (h : ℝ) : evaluate matrixProgram h 20 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 19)) := by
  have hc := indexed_value_step h 20 (by decide)
  change evaluate matrixProgram h 20 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 19)) at hc
  exact hc
theorem primitive_matches20 (h : ℝ) : evaluate matrixProgram h 20 = primitiveValue20 h := by
  rw [primitive_step20]
  simp only [primitive_matches19, primitive_matches3, primitiveValue20]

def primitiveValue21 (h : ℝ) : ℝ := ((primitiveValue1 h) + (primitiveValue2 h))
theorem primitive_step21 (h : ℝ) : evaluate matrixProgram h 21 = ((evaluate matrixProgram h 1) + (evaluate matrixProgram h 2)) := by
  have hc := indexed_value_step h 21 (by decide)
  change evaluate matrixProgram h 21 = ((evaluate matrixProgram h 1) + (evaluate matrixProgram h 2)) at hc
  exact hc
theorem primitive_matches21 (h : ℝ) : evaluate matrixProgram h 21 = primitiveValue21 h := by
  rw [primitive_step21]
  simp only [primitive_matches1, primitive_matches2, primitiveValue21]

def primitiveValue22 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue21 h))
theorem primitive_step22 (h : ℝ) : evaluate matrixProgram h 22 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 21)) := by
  have hc := indexed_value_step h 22 (by decide)
  change evaluate matrixProgram h 22 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 21)) at hc
  exact hc
theorem primitive_matches22 (h : ℝ) : evaluate matrixProgram h 22 = primitiveValue22 h := by
  rw [primitive_step22]
  simp only [primitive_matches3, primitive_matches21, primitiveValue22]

def primitiveValue23 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue7 h))
theorem primitive_step23 (h : ℝ) : evaluate matrixProgram h 23 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 7)) := by
  have hc := indexed_value_step h 23 (by decide)
  change evaluate matrixProgram h 23 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 7)) at hc
  exact hc
theorem primitive_matches23 (h : ℝ) : evaluate matrixProgram h 23 = primitiveValue23 h := by
  rw [primitive_step23]
  simp only [primitive_matches3, primitive_matches7, primitiveValue23]

def primitiveValue24 (h : ℝ) : ℝ := ((primitiveValue5 h) * (primitiveValue7 h))
theorem primitive_step24 (h : ℝ) : evaluate matrixProgram h 24 = ((evaluate matrixProgram h 5) * (evaluate matrixProgram h 7)) := by
  have hc := indexed_value_step h 24 (by decide)
  change evaluate matrixProgram h 24 = ((evaluate matrixProgram h 5) * (evaluate matrixProgram h 7)) at hc
  exact hc
theorem primitive_matches24 (h : ℝ) : evaluate matrixProgram h 24 = primitiveValue24 h := by
  rw [primitive_step24]
  simp only [primitive_matches5, primitive_matches7, primitiveValue24]

def primitiveValue25 (h : ℝ) : ℝ := ((primitiveValue3 h) - (primitiveValue9 h))
theorem primitive_step25 (h : ℝ) : evaluate matrixProgram h 25 = ((evaluate matrixProgram h 3) - (evaluate matrixProgram h 9)) := by
  have hc := indexed_value_step h 25 (by decide)
  change evaluate matrixProgram h 25 = ((evaluate matrixProgram h 3) - (evaluate matrixProgram h 9)) at hc
  exact hc
theorem primitive_matches25 (h : ℝ) : evaluate matrixProgram h 25 = primitiveValue25 h := by
  rw [primitive_step25]
  simp only [primitive_matches9, primitive_matches3, primitiveValue25]

def primitiveValue26 (h : ℝ) : ℝ := ((primitiveValue3 h) + (primitiveValue9 h))
theorem primitive_step26 (h : ℝ) : evaluate matrixProgram h 26 = ((evaluate matrixProgram h 3) + (evaluate matrixProgram h 9)) := by
  have hc := indexed_value_step h 26 (by decide)
  change evaluate matrixProgram h 26 = ((evaluate matrixProgram h 3) + (evaluate matrixProgram h 9)) at hc
  exact hc
theorem primitive_matches26 (h : ℝ) : evaluate matrixProgram h 26 = primitiveValue26 h := by
  rw [primitive_step26]
  simp only [primitive_matches9, primitive_matches3, primitiveValue26]

def primitiveValue27 (h : ℝ) : ℝ := ((primitiveValue6 h) * (primitiveValue26 h))
theorem primitive_step27 (h : ℝ) : evaluate matrixProgram h 27 = ((evaluate matrixProgram h 6) * (evaluate matrixProgram h 26)) := by
  have hc := indexed_value_step h 27 (by decide)
  change evaluate matrixProgram h 27 = ((evaluate matrixProgram h 6) * (evaluate matrixProgram h 26)) at hc
  exact hc
theorem primitive_matches27 (h : ℝ) : evaluate matrixProgram h 27 = primitiveValue27 h := by
  rw [primitive_step27]
  simp only [primitive_matches26, primitive_matches6, primitiveValue27]

def primitiveValue28 (h : ℝ) : ℝ := ((primitiveValue25 h) + (primitiveValue27 h))
theorem primitive_step28 (h : ℝ) : evaluate matrixProgram h 28 = ((evaluate matrixProgram h 25) + (evaluate matrixProgram h 27)) := by
  have hc := indexed_value_step h 28 (by decide)
  change evaluate matrixProgram h 28 = ((evaluate matrixProgram h 25) + (evaluate matrixProgram h 27)) at hc
  exact hc
theorem primitive_matches28 (h : ℝ) : evaluate matrixProgram h 28 = primitiveValue28 h := by
  rw [primitive_step28]
  simp only [primitive_matches25, primitive_matches27, primitiveValue28]

def primitiveValue29 (h : ℝ) : ℝ := ((primitiveValue6 h) * (primitiveValue25 h))
theorem primitive_step29 (h : ℝ) : evaluate matrixProgram h 29 = ((evaluate matrixProgram h 6) * (evaluate matrixProgram h 25)) := by
  have hc := indexed_value_step h 29 (by decide)
  change evaluate matrixProgram h 29 = ((evaluate matrixProgram h 6) * (evaluate matrixProgram h 25)) at hc
  exact hc
theorem primitive_matches29 (h : ℝ) : evaluate matrixProgram h 29 = primitiveValue29 h := by
  rw [primitive_step29]
  simp only [primitive_matches25, primitive_matches6, primitiveValue29]

def primitiveValue30 (h : ℝ) : ℝ := ((primitiveValue26 h) + (primitiveValue29 h))
theorem primitive_step30 (h : ℝ) : evaluate matrixProgram h 30 = ((evaluate matrixProgram h 26) + (evaluate matrixProgram h 29)) := by
  have hc := indexed_value_step h 30 (by decide)
  change evaluate matrixProgram h 30 = ((evaluate matrixProgram h 26) + (evaluate matrixProgram h 29)) at hc
  exact hc
theorem primitive_matches30 (h : ℝ) : evaluate matrixProgram h 30 = primitiveValue30 h := by
  rw [primitive_step30]
  simp only [primitive_matches26, primitive_matches29, primitiveValue30]

def primitiveValue31 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue5 h))
theorem primitive_step31 (h : ℝ) : evaluate matrixProgram h 31 = Real.sqrt ((evaluate matrixProgram h 5)) := by
  have hc := indexed_value_step h 31 (by decide)
  change evaluate matrixProgram h 31 = Real.sqrt ((evaluate matrixProgram h 5)) at hc
  exact hc
theorem primitive_matches31 (h : ℝ) : evaluate matrixProgram h 31 = primitiveValue31 h := by
  rw [primitive_step31]
  simp only [primitive_matches5, primitiveValue31]

def primitiveValue32 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue31 h))
theorem primitive_step32 (h : ℝ) : evaluate matrixProgram h 32 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 31)) := by
  have hc := indexed_value_step h 32 (by decide)
  change evaluate matrixProgram h 32 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 31)) at hc
  exact hc
theorem primitive_matches32 (h : ℝ) : evaluate matrixProgram h 32 = primitiveValue32 h := by
  rw [primitive_step32]
  simp only [primitive_matches3, primitive_matches31, primitiveValue32]

def primitiveValue33 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue32 h))
theorem primitive_step33 (h : ℝ) : evaluate matrixProgram h 33 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 32)) := by
  have hc := indexed_value_step h 33 (by decide)
  change evaluate matrixProgram h 33 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 32)) at hc
  exact hc
theorem primitive_matches33 (h : ℝ) : evaluate matrixProgram h 33 = primitiveValue33 h := by
  rw [primitive_step33]
  simp only [primitive_matches32, primitive_matches1, primitiveValue33]

def primitiveValue34 (h : ℝ) : ℝ := ((primitiveValue5 h) * (primitiveValue31 h))
theorem primitive_step34 (h : ℝ) : evaluate matrixProgram h 34 = ((evaluate matrixProgram h 5) * (evaluate matrixProgram h 31)) := by
  have hc := indexed_value_step h 34 (by decide)
  change evaluate matrixProgram h 34 = ((evaluate matrixProgram h 5) * (evaluate matrixProgram h 31)) at hc
  exact hc
theorem primitive_matches34 (h : ℝ) : evaluate matrixProgram h 34 = primitiveValue34 h := by
  rw [primitive_step34]
  simp only [primitive_matches5, primitive_matches31, primitiveValue34]

def primitiveValue35 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue34 h))
theorem primitive_step35 (h : ℝ) : evaluate matrixProgram h 35 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 34)) := by
  have hc := indexed_value_step h 35 (by decide)
  change evaluate matrixProgram h 35 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 34)) at hc
  exact hc
theorem primitive_matches35 (h : ℝ) : evaluate matrixProgram h 35 = primitiveValue35 h := by
  rw [primitive_step35]
  simp only [primitive_matches1, primitive_matches34, primitiveValue35]

def primitiveValue36 (h : ℝ) : ℝ := ((primitiveValue5 h) * (primitiveValue5 h))
theorem primitive_step36 (h : ℝ) : evaluate matrixProgram h 36 = ((evaluate matrixProgram h 5) * (evaluate matrixProgram h 5)) := by
  have hc := indexed_value_step h 36 (by decide)
  change evaluate matrixProgram h 36 = ((evaluate matrixProgram h 5) * (evaluate matrixProgram h 5)) at hc
  exact hc
theorem primitive_matches36 (h : ℝ) : evaluate matrixProgram h 36 = primitiveValue36 h := by
  rw [primitive_step36]
  simp only [primitive_matches5, primitiveValue36]

def primitiveValue37 (h : ℝ) : ℝ := ((primitiveValue31 h) * (primitiveValue36 h))
theorem primitive_step37 (h : ℝ) : evaluate matrixProgram h 37 = ((evaluate matrixProgram h 31) * (evaluate matrixProgram h 36)) := by
  have hc := indexed_value_step h 37 (by decide)
  change evaluate matrixProgram h 37 = ((evaluate matrixProgram h 31) * (evaluate matrixProgram h 36)) at hc
  exact hc
theorem primitive_matches37 (h : ℝ) : evaluate matrixProgram h 37 = primitiveValue37 h := by
  rw [primitive_step37]
  simp only [primitive_matches36, primitive_matches31, primitiveValue37]

def primitiveValue38 (h : ℝ) : ℝ := ((primitiveValue4 h) / (primitiveValue37 h))
theorem primitive_step38 (h : ℝ) : evaluate matrixProgram h 38 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 37)) := by
  have hc := indexed_value_step h 38 (by decide)
  change evaluate matrixProgram h 38 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 37)) at hc
  exact hc
theorem primitive_matches38 (h : ℝ) : evaluate matrixProgram h 38 = primitiveValue38 h := by
  rw [primitive_step38]
  simp only [primitive_matches4, primitive_matches37, primitiveValue38]

def primitiveValue39 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue20 h))
theorem primitive_step39 (h : ℝ) : evaluate matrixProgram h 39 = Real.sqrt ((evaluate matrixProgram h 20)) := by
  have hc := indexed_value_step h 39 (by decide)
  change evaluate matrixProgram h 39 = Real.sqrt ((evaluate matrixProgram h 20)) at hc
  exact hc
theorem primitive_matches39 (h : ℝ) : evaluate matrixProgram h 39 = primitiveValue39 h := by
  rw [primitive_step39]
  simp only [primitive_matches20, primitiveValue39]

def primitiveValue40 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue39 h))
theorem primitive_step40 (h : ℝ) : evaluate matrixProgram h 40 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 39)) := by
  have hc := indexed_value_step h 40 (by decide)
  change evaluate matrixProgram h 40 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 39)) at hc
  exact hc
theorem primitive_matches40 (h : ℝ) : evaluate matrixProgram h 40 = primitiveValue40 h := by
  rw [primitive_step40]
  simp only [primitive_matches3, primitive_matches39, primitiveValue40]

def primitiveValue41 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue40 h))
theorem primitive_step41 (h : ℝ) : evaluate matrixProgram h 41 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 40)) := by
  have hc := indexed_value_step h 41 (by decide)
  change evaluate matrixProgram h 41 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 40)) at hc
  exact hc
theorem primitive_matches41 (h : ℝ) : evaluate matrixProgram h 41 = primitiveValue41 h := by
  rw [primitive_step41]
  simp only [primitive_matches40, primitive_matches1, primitiveValue41]

def primitiveValue42 (h : ℝ) : ℝ := ((primitiveValue20 h) * (primitiveValue39 h))
theorem primitive_step42 (h : ℝ) : evaluate matrixProgram h 42 = ((evaluate matrixProgram h 20) * (evaluate matrixProgram h 39)) := by
  have hc := indexed_value_step h 42 (by decide)
  change evaluate matrixProgram h 42 = ((evaluate matrixProgram h 20) * (evaluate matrixProgram h 39)) at hc
  exact hc
theorem primitive_matches42 (h : ℝ) : evaluate matrixProgram h 42 = primitiveValue42 h := by
  rw [primitive_step42]
  simp only [primitive_matches20, primitive_matches39, primitiveValue42]

def primitiveValue43 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue42 h))
theorem primitive_step43 (h : ℝ) : evaluate matrixProgram h 43 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 42)) := by
  have hc := indexed_value_step h 43 (by decide)
  change evaluate matrixProgram h 43 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 42)) at hc
  exact hc
theorem primitive_matches43 (h : ℝ) : evaluate matrixProgram h 43 = primitiveValue43 h := by
  rw [primitive_step43]
  simp only [primitive_matches1, primitive_matches42, primitiveValue43]

def primitiveValue44 (h : ℝ) : ℝ := ((primitiveValue20 h) * (primitiveValue20 h))
theorem primitive_step44 (h : ℝ) : evaluate matrixProgram h 44 = ((evaluate matrixProgram h 20) * (evaluate matrixProgram h 20)) := by
  have hc := indexed_value_step h 44 (by decide)
  change evaluate matrixProgram h 44 = ((evaluate matrixProgram h 20) * (evaluate matrixProgram h 20)) at hc
  exact hc
theorem primitive_matches44 (h : ℝ) : evaluate matrixProgram h 44 = primitiveValue44 h := by
  rw [primitive_step44]
  simp only [primitive_matches20, primitiveValue44]

def primitiveValue45 (h : ℝ) : ℝ := ((primitiveValue39 h) * (primitiveValue44 h))
theorem primitive_step45 (h : ℝ) : evaluate matrixProgram h 45 = ((evaluate matrixProgram h 39) * (evaluate matrixProgram h 44)) := by
  have hc := indexed_value_step h 45 (by decide)
  change evaluate matrixProgram h 45 = ((evaluate matrixProgram h 39) * (evaluate matrixProgram h 44)) at hc
  exact hc
theorem primitive_matches45 (h : ℝ) : evaluate matrixProgram h 45 = primitiveValue45 h := by
  rw [primitive_step45]
  simp only [primitive_matches44, primitive_matches39, primitiveValue45]

def primitiveValue46 (h : ℝ) : ℝ := ((primitiveValue4 h) / (primitiveValue45 h))
theorem primitive_step46 (h : ℝ) : evaluate matrixProgram h 46 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 45)) := by
  have hc := indexed_value_step h 46 (by decide)
  change evaluate matrixProgram h 46 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 45)) at hc
  exact hc
theorem primitive_matches46 (h : ℝ) : evaluate matrixProgram h 46 = primitiveValue46 h := by
  rw [primitive_step46]
  simp only [primitive_matches4, primitive_matches45, primitiveValue46]

def primitiveValue47 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue22 h))
theorem primitive_step47 (h : ℝ) : evaluate matrixProgram h 47 = Real.sqrt ((evaluate matrixProgram h 22)) := by
  have hc := indexed_value_step h 47 (by decide)
  change evaluate matrixProgram h 47 = Real.sqrt ((evaluate matrixProgram h 22)) at hc
  exact hc
theorem primitive_matches47 (h : ℝ) : evaluate matrixProgram h 47 = primitiveValue47 h := by
  rw [primitive_step47]
  simp only [primitive_matches22, primitiveValue47]

def primitiveValue48 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue47 h))
theorem primitive_step48 (h : ℝ) : evaluate matrixProgram h 48 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 47)) := by
  have hc := indexed_value_step h 48 (by decide)
  change evaluate matrixProgram h 48 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 47)) at hc
  exact hc
theorem primitive_matches48 (h : ℝ) : evaluate matrixProgram h 48 = primitiveValue48 h := by
  rw [primitive_step48]
  simp only [primitive_matches3, primitive_matches47, primitiveValue48]

def primitiveValue49 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue48 h))
theorem primitive_step49 (h : ℝ) : evaluate matrixProgram h 49 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 48)) := by
  have hc := indexed_value_step h 49 (by decide)
  change evaluate matrixProgram h 49 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 48)) at hc
  exact hc
theorem primitive_matches49 (h : ℝ) : evaluate matrixProgram h 49 = primitiveValue49 h := by
  rw [primitive_step49]
  simp only [primitive_matches48, primitive_matches1, primitiveValue49]

def primitiveValue50 (h : ℝ) : ℝ := ((primitiveValue22 h) * (primitiveValue47 h))
theorem primitive_step50 (h : ℝ) : evaluate matrixProgram h 50 = ((evaluate matrixProgram h 22) * (evaluate matrixProgram h 47)) := by
  have hc := indexed_value_step h 50 (by decide)
  change evaluate matrixProgram h 50 = ((evaluate matrixProgram h 22) * (evaluate matrixProgram h 47)) at hc
  exact hc
theorem primitive_matches50 (h : ℝ) : evaluate matrixProgram h 50 = primitiveValue50 h := by
  rw [primitive_step50]
  simp only [primitive_matches22, primitive_matches47, primitiveValue50]

def primitiveValue51 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue50 h))
theorem primitive_step51 (h : ℝ) : evaluate matrixProgram h 51 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 50)) := by
  have hc := indexed_value_step h 51 (by decide)
  change evaluate matrixProgram h 51 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 50)) at hc
  exact hc
theorem primitive_matches51 (h : ℝ) : evaluate matrixProgram h 51 = primitiveValue51 h := by
  rw [primitive_step51]
  simp only [primitive_matches1, primitive_matches50, primitiveValue51]

def primitiveValue52 (h : ℝ) : ℝ := ((primitiveValue22 h) * (primitiveValue22 h))
theorem primitive_step52 (h : ℝ) : evaluate matrixProgram h 52 = ((evaluate matrixProgram h 22) * (evaluate matrixProgram h 22)) := by
  have hc := indexed_value_step h 52 (by decide)
  change evaluate matrixProgram h 52 = ((evaluate matrixProgram h 22) * (evaluate matrixProgram h 22)) at hc
  exact hc
theorem primitive_matches52 (h : ℝ) : evaluate matrixProgram h 52 = primitiveValue52 h := by
  rw [primitive_step52]
  simp only [primitive_matches22, primitiveValue52]

def primitiveValue53 (h : ℝ) : ℝ := ((primitiveValue47 h) * (primitiveValue52 h))
theorem primitive_step53 (h : ℝ) : evaluate matrixProgram h 53 = ((evaluate matrixProgram h 47) * (evaluate matrixProgram h 52)) := by
  have hc := indexed_value_step h 53 (by decide)
  change evaluate matrixProgram h 53 = ((evaluate matrixProgram h 47) * (evaluate matrixProgram h 52)) at hc
  exact hc
theorem primitive_matches53 (h : ℝ) : evaluate matrixProgram h 53 = primitiveValue53 h := by
  rw [primitive_step53]
  simp only [primitive_matches52, primitive_matches47, primitiveValue53]

def primitiveValue54 (h : ℝ) : ℝ := ((primitiveValue4 h) / (primitiveValue53 h))
theorem primitive_step54 (h : ℝ) : evaluate matrixProgram h 54 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 53)) := by
  have hc := indexed_value_step h 54 (by decide)
  change evaluate matrixProgram h 54 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 53)) at hc
  exact hc
theorem primitive_matches54 (h : ℝ) : evaluate matrixProgram h 54 = primitiveValue54 h := by
  rw [primitive_step54]
  simp only [primitive_matches4, primitive_matches53, primitiveValue54]

def primitiveValue55 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue23 h))
theorem primitive_step55 (h : ℝ) : evaluate matrixProgram h 55 = Real.sqrt ((evaluate matrixProgram h 23)) := by
  have hc := indexed_value_step h 55 (by decide)
  change evaluate matrixProgram h 55 = Real.sqrt ((evaluate matrixProgram h 23)) at hc
  exact hc
theorem primitive_matches55 (h : ℝ) : evaluate matrixProgram h 55 = primitiveValue55 h := by
  rw [primitive_step55]
  simp only [primitive_matches23, primitiveValue55]

def primitiveValue56 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue55 h))
theorem primitive_step56 (h : ℝ) : evaluate matrixProgram h 56 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 55)) := by
  have hc := indexed_value_step h 56 (by decide)
  change evaluate matrixProgram h 56 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 55)) at hc
  exact hc
theorem primitive_matches56 (h : ℝ) : evaluate matrixProgram h 56 = primitiveValue56 h := by
  rw [primitive_step56]
  simp only [primitive_matches3, primitive_matches55, primitiveValue56]

def primitiveValue57 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue56 h))
theorem primitive_step57 (h : ℝ) : evaluate matrixProgram h 57 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 56)) := by
  have hc := indexed_value_step h 57 (by decide)
  change evaluate matrixProgram h 57 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 56)) at hc
  exact hc
theorem primitive_matches57 (h : ℝ) : evaluate matrixProgram h 57 = primitiveValue57 h := by
  rw [primitive_step57]
  simp only [primitive_matches56, primitive_matches1, primitiveValue57]

def primitiveValue58 (h : ℝ) : ℝ := ((primitiveValue23 h) * (primitiveValue55 h))
theorem primitive_step58 (h : ℝ) : evaluate matrixProgram h 58 = ((evaluate matrixProgram h 23) * (evaluate matrixProgram h 55)) := by
  have hc := indexed_value_step h 58 (by decide)
  change evaluate matrixProgram h 58 = ((evaluate matrixProgram h 23) * (evaluate matrixProgram h 55)) at hc
  exact hc
theorem primitive_matches58 (h : ℝ) : evaluate matrixProgram h 58 = primitiveValue58 h := by
  rw [primitive_step58]
  simp only [primitive_matches55, primitive_matches23, primitiveValue58]

def primitiveValue59 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue58 h))
theorem primitive_step59 (h : ℝ) : evaluate matrixProgram h 59 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 58)) := by
  have hc := indexed_value_step h 59 (by decide)
  change evaluate matrixProgram h 59 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 58)) at hc
  exact hc
theorem primitive_matches59 (h : ℝ) : evaluate matrixProgram h 59 = primitiveValue59 h := by
  rw [primitive_step59]
  simp only [primitive_matches1, primitive_matches58, primitiveValue59]

def primitiveValue60 (h : ℝ) : ℝ := ((primitiveValue23 h) * (primitiveValue23 h))
theorem primitive_step60 (h : ℝ) : evaluate matrixProgram h 60 = ((evaluate matrixProgram h 23) * (evaluate matrixProgram h 23)) := by
  have hc := indexed_value_step h 60 (by decide)
  change evaluate matrixProgram h 60 = ((evaluate matrixProgram h 23) * (evaluate matrixProgram h 23)) at hc
  exact hc
theorem primitive_matches60 (h : ℝ) : evaluate matrixProgram h 60 = primitiveValue60 h := by
  rw [primitive_step60]
  simp only [primitive_matches23, primitiveValue60]

def primitiveValue61 (h : ℝ) : ℝ := ((primitiveValue55 h) * (primitiveValue60 h))
theorem primitive_step61 (h : ℝ) : evaluate matrixProgram h 61 = ((evaluate matrixProgram h 55) * (evaluate matrixProgram h 60)) := by
  have hc := indexed_value_step h 61 (by decide)
  change evaluate matrixProgram h 61 = ((evaluate matrixProgram h 55) * (evaluate matrixProgram h 60)) at hc
  exact hc
theorem primitive_matches61 (h : ℝ) : evaluate matrixProgram h 61 = primitiveValue61 h := by
  rw [primitive_step61]
  simp only [primitive_matches60, primitive_matches55, primitiveValue61]

def primitiveValue62 (h : ℝ) : ℝ := ((primitiveValue4 h) / (primitiveValue61 h))
theorem primitive_step62 (h : ℝ) : evaluate matrixProgram h 62 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 61)) := by
  have hc := indexed_value_step h 62 (by decide)
  change evaluate matrixProgram h 62 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 61)) at hc
  exact hc
theorem primitive_matches62 (h : ℝ) : evaluate matrixProgram h 62 = primitiveValue62 h := by
  rw [primitive_step62]
  simp only [primitive_matches4, primitive_matches61, primitiveValue62]

def primitiveValue63 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue24 h))
theorem primitive_step63 (h : ℝ) : evaluate matrixProgram h 63 = Real.sqrt ((evaluate matrixProgram h 24)) := by
  have hc := indexed_value_step h 63 (by decide)
  change evaluate matrixProgram h 63 = Real.sqrt ((evaluate matrixProgram h 24)) at hc
  exact hc
theorem primitive_matches63 (h : ℝ) : evaluate matrixProgram h 63 = primitiveValue63 h := by
  rw [primitive_step63]
  simp only [primitive_matches24, primitiveValue63]

def primitiveValue64 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue63 h))
theorem primitive_step64 (h : ℝ) : evaluate matrixProgram h 64 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 63)) := by
  have hc := indexed_value_step h 64 (by decide)
  change evaluate matrixProgram h 64 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 63)) at hc
  exact hc
theorem primitive_matches64 (h : ℝ) : evaluate matrixProgram h 64 = primitiveValue64 h := by
  rw [primitive_step64]
  simp only [primitive_matches3, primitive_matches63, primitiveValue64]

def primitiveValue65 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue64 h))
theorem primitive_step65 (h : ℝ) : evaluate matrixProgram h 65 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 64)) := by
  have hc := indexed_value_step h 65 (by decide)
  change evaluate matrixProgram h 65 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 64)) at hc
  exact hc
theorem primitive_matches65 (h : ℝ) : evaluate matrixProgram h 65 = primitiveValue65 h := by
  rw [primitive_step65]
  simp only [primitive_matches64, primitive_matches1, primitiveValue65]

def primitiveValue66 (h : ℝ) : ℝ := ((primitiveValue24 h) * (primitiveValue63 h))
theorem primitive_step66 (h : ℝ) : evaluate matrixProgram h 66 = ((evaluate matrixProgram h 24) * (evaluate matrixProgram h 63)) := by
  have hc := indexed_value_step h 66 (by decide)
  change evaluate matrixProgram h 66 = ((evaluate matrixProgram h 24) * (evaluate matrixProgram h 63)) at hc
  exact hc
theorem primitive_matches66 (h : ℝ) : evaluate matrixProgram h 66 = primitiveValue66 h := by
  rw [primitive_step66]
  simp only [primitive_matches24, primitive_matches63, primitiveValue66]

def primitiveValue67 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue66 h))
theorem primitive_step67 (h : ℝ) : evaluate matrixProgram h 67 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 66)) := by
  have hc := indexed_value_step h 67 (by decide)
  change evaluate matrixProgram h 67 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 66)) at hc
  exact hc
theorem primitive_matches67 (h : ℝ) : evaluate matrixProgram h 67 = primitiveValue67 h := by
  rw [primitive_step67]
  simp only [primitive_matches1, primitive_matches66, primitiveValue67]

def primitiveValue68 (h : ℝ) : ℝ := ((primitiveValue24 h) * (primitiveValue24 h))
theorem primitive_step68 (h : ℝ) : evaluate matrixProgram h 68 = ((evaluate matrixProgram h 24) * (evaluate matrixProgram h 24)) := by
  have hc := indexed_value_step h 68 (by decide)
  change evaluate matrixProgram h 68 = ((evaluate matrixProgram h 24) * (evaluate matrixProgram h 24)) at hc
  exact hc
theorem primitive_matches68 (h : ℝ) : evaluate matrixProgram h 68 = primitiveValue68 h := by
  rw [primitive_step68]
  simp only [primitive_matches24, primitiveValue68]

def primitiveValue69 (h : ℝ) : ℝ := ((primitiveValue63 h) * (primitiveValue68 h))
theorem primitive_step69 (h : ℝ) : evaluate matrixProgram h 69 = ((evaluate matrixProgram h 63) * (evaluate matrixProgram h 68)) := by
  have hc := indexed_value_step h 69 (by decide)
  change evaluate matrixProgram h 69 = ((evaluate matrixProgram h 63) * (evaluate matrixProgram h 68)) at hc
  exact hc
theorem primitive_matches69 (h : ℝ) : evaluate matrixProgram h 69 = primitiveValue69 h := by
  rw [primitive_step69]
  simp only [primitive_matches68, primitive_matches63, primitiveValue69]

def primitiveValue70 (h : ℝ) : ℝ := ((primitiveValue4 h) / (primitiveValue69 h))
theorem primitive_step70 (h : ℝ) : evaluate matrixProgram h 70 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 69)) := by
  have hc := indexed_value_step h 70 (by decide)
  change evaluate matrixProgram h 70 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 69)) at hc
  exact hc
theorem primitive_matches70 (h : ℝ) : evaluate matrixProgram h 70 = primitiveValue70 h := by
  rw [primitive_step70]
  simp only [primitive_matches4, primitive_matches69, primitiveValue70]

def primitiveValue71 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue28 h))
theorem primitive_step71 (h : ℝ) : evaluate matrixProgram h 71 = Real.sqrt ((evaluate matrixProgram h 28)) := by
  have hc := indexed_value_step h 71 (by decide)
  change evaluate matrixProgram h 71 = Real.sqrt ((evaluate matrixProgram h 28)) at hc
  exact hc
theorem primitive_matches71 (h : ℝ) : evaluate matrixProgram h 71 = primitiveValue71 h := by
  rw [primitive_step71]
  simp only [primitive_matches28, primitiveValue71]

def primitiveValue72 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue71 h))
theorem primitive_step72 (h : ℝ) : evaluate matrixProgram h 72 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 71)) := by
  have hc := indexed_value_step h 72 (by decide)
  change evaluate matrixProgram h 72 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 71)) at hc
  exact hc
theorem primitive_matches72 (h : ℝ) : evaluate matrixProgram h 72 = primitiveValue72 h := by
  rw [primitive_step72]
  simp only [primitive_matches3, primitive_matches71, primitiveValue72]

def primitiveValue73 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue72 h))
theorem primitive_step73 (h : ℝ) : evaluate matrixProgram h 73 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 72)) := by
  have hc := indexed_value_step h 73 (by decide)
  change evaluate matrixProgram h 73 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 72)) at hc
  exact hc
theorem primitive_matches73 (h : ℝ) : evaluate matrixProgram h 73 = primitiveValue73 h := by
  rw [primitive_step73]
  simp only [primitive_matches72, primitive_matches1, primitiveValue73]

def primitiveValue74 (h : ℝ) : ℝ := ((primitiveValue28 h) * (primitiveValue71 h))
theorem primitive_step74 (h : ℝ) : evaluate matrixProgram h 74 = ((evaluate matrixProgram h 28) * (evaluate matrixProgram h 71)) := by
  have hc := indexed_value_step h 74 (by decide)
  change evaluate matrixProgram h 74 = ((evaluate matrixProgram h 28) * (evaluate matrixProgram h 71)) at hc
  exact hc
theorem primitive_matches74 (h : ℝ) : evaluate matrixProgram h 74 = primitiveValue74 h := by
  rw [primitive_step74]
  simp only [primitive_matches28, primitive_matches71, primitiveValue74]

def primitiveValue75 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue74 h))
theorem primitive_step75 (h : ℝ) : evaluate matrixProgram h 75 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 74)) := by
  have hc := indexed_value_step h 75 (by decide)
  change evaluate matrixProgram h 75 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 74)) at hc
  exact hc
theorem primitive_matches75 (h : ℝ) : evaluate matrixProgram h 75 = primitiveValue75 h := by
  rw [primitive_step75]
  simp only [primitive_matches1, primitive_matches74, primitiveValue75]

def primitiveValue76 (h : ℝ) : ℝ := ((primitiveValue28 h) * (primitiveValue28 h))
theorem primitive_step76 (h : ℝ) : evaluate matrixProgram h 76 = ((evaluate matrixProgram h 28) * (evaluate matrixProgram h 28)) := by
  have hc := indexed_value_step h 76 (by decide)
  change evaluate matrixProgram h 76 = ((evaluate matrixProgram h 28) * (evaluate matrixProgram h 28)) at hc
  exact hc
theorem primitive_matches76 (h : ℝ) : evaluate matrixProgram h 76 = primitiveValue76 h := by
  rw [primitive_step76]
  simp only [primitive_matches28, primitiveValue76]

def primitiveValue77 (h : ℝ) : ℝ := ((primitiveValue71 h) * (primitiveValue76 h))
theorem primitive_step77 (h : ℝ) : evaluate matrixProgram h 77 = ((evaluate matrixProgram h 71) * (evaluate matrixProgram h 76)) := by
  have hc := indexed_value_step h 77 (by decide)
  change evaluate matrixProgram h 77 = ((evaluate matrixProgram h 71) * (evaluate matrixProgram h 76)) at hc
  exact hc
theorem primitive_matches77 (h : ℝ) : evaluate matrixProgram h 77 = primitiveValue77 h := by
  rw [primitive_step77]
  simp only [primitive_matches76, primitive_matches71, primitiveValue77]

def primitiveValue78 (h : ℝ) : ℝ := ((primitiveValue4 h) / (primitiveValue77 h))
theorem primitive_step78 (h : ℝ) : evaluate matrixProgram h 78 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 77)) := by
  have hc := indexed_value_step h 78 (by decide)
  change evaluate matrixProgram h 78 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 77)) at hc
  exact hc
theorem primitive_matches78 (h : ℝ) : evaluate matrixProgram h 78 = primitiveValue78 h := by
  rw [primitive_step78]
  simp only [primitive_matches4, primitive_matches77, primitiveValue78]

def primitiveValue79 (h : ℝ) : ℝ := Real.sqrt ((primitiveValue30 h))
theorem primitive_step79 (h : ℝ) : evaluate matrixProgram h 79 = Real.sqrt ((evaluate matrixProgram h 30)) := by
  have hc := indexed_value_step h 79 (by decide)
  change evaluate matrixProgram h 79 = Real.sqrt ((evaluate matrixProgram h 30)) at hc
  exact hc
theorem primitive_matches79 (h : ℝ) : evaluate matrixProgram h 79 = primitiveValue79 h := by
  rw [primitive_step79]
  simp only [primitive_matches30, primitiveValue79]

def primitiveValue80 (h : ℝ) : ℝ := ((primitiveValue3 h) * (primitiveValue79 h))
theorem primitive_step80 (h : ℝ) : evaluate matrixProgram h 80 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 79)) := by
  have hc := indexed_value_step h 80 (by decide)
  change evaluate matrixProgram h 80 = ((evaluate matrixProgram h 3) * (evaluate matrixProgram h 79)) at hc
  exact hc
theorem primitive_matches80 (h : ℝ) : evaluate matrixProgram h 80 = primitiveValue80 h := by
  rw [primitive_step80]
  simp only [primitive_matches3, primitive_matches79, primitiveValue80]

def primitiveValue81 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue80 h))
theorem primitive_step81 (h : ℝ) : evaluate matrixProgram h 81 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 80)) := by
  have hc := indexed_value_step h 81 (by decide)
  change evaluate matrixProgram h 81 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 80)) at hc
  exact hc
theorem primitive_matches81 (h : ℝ) : evaluate matrixProgram h 81 = primitiveValue81 h := by
  rw [primitive_step81]
  simp only [primitive_matches80, primitive_matches1, primitiveValue81]

def primitiveValue82 (h : ℝ) : ℝ := ((primitiveValue30 h) * (primitiveValue79 h))
theorem primitive_step82 (h : ℝ) : evaluate matrixProgram h 82 = ((evaluate matrixProgram h 30) * (evaluate matrixProgram h 79)) := by
  have hc := indexed_value_step h 82 (by decide)
  change evaluate matrixProgram h 82 = ((evaluate matrixProgram h 30) * (evaluate matrixProgram h 79)) at hc
  exact hc
theorem primitive_matches82 (h : ℝ) : evaluate matrixProgram h 82 = primitiveValue82 h := by
  rw [primitive_step82]
  simp only [primitive_matches30, primitive_matches79, primitiveValue82]

def primitiveValue83 (h : ℝ) : ℝ := ((primitiveValue1 h) / (primitiveValue82 h))
theorem primitive_step83 (h : ℝ) : evaluate matrixProgram h 83 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 82)) := by
  have hc := indexed_value_step h 83 (by decide)
  change evaluate matrixProgram h 83 = ((evaluate matrixProgram h 1) / (evaluate matrixProgram h 82)) at hc
  exact hc
theorem primitive_matches83 (h : ℝ) : evaluate matrixProgram h 83 = primitiveValue83 h := by
  rw [primitive_step83]
  simp only [primitive_matches1, primitive_matches82, primitiveValue83]

def primitiveValue84 (h : ℝ) : ℝ := ((primitiveValue30 h) * (primitiveValue30 h))
theorem primitive_step84 (h : ℝ) : evaluate matrixProgram h 84 = ((evaluate matrixProgram h 30) * (evaluate matrixProgram h 30)) := by
  have hc := indexed_value_step h 84 (by decide)
  change evaluate matrixProgram h 84 = ((evaluate matrixProgram h 30) * (evaluate matrixProgram h 30)) at hc
  exact hc
theorem primitive_matches84 (h : ℝ) : evaluate matrixProgram h 84 = primitiveValue84 h := by
  rw [primitive_step84]
  simp only [primitive_matches30, primitiveValue84]

def primitiveValue85 (h : ℝ) : ℝ := ((primitiveValue79 h) * (primitiveValue84 h))
theorem primitive_step85 (h : ℝ) : evaluate matrixProgram h 85 = ((evaluate matrixProgram h 79) * (evaluate matrixProgram h 84)) := by
  have hc := indexed_value_step h 85 (by decide)
  change evaluate matrixProgram h 85 = ((evaluate matrixProgram h 79) * (evaluate matrixProgram h 84)) at hc
  exact hc
theorem primitive_matches85 (h : ℝ) : evaluate matrixProgram h 85 = primitiveValue85 h := by
  rw [primitive_step85]
  simp only [primitive_matches84, primitive_matches79, primitiveValue85]

def primitiveValue86 (h : ℝ) : ℝ := ((primitiveValue4 h) / (primitiveValue85 h))
theorem primitive_step86 (h : ℝ) : evaluate matrixProgram h 86 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 85)) := by
  have hc := indexed_value_step h 86 (by decide)
  change evaluate matrixProgram h 86 = ((evaluate matrixProgram h 4) / (evaluate matrixProgram h 85)) at hc
  exact hc
theorem primitive_matches86 (h : ℝ) : evaluate matrixProgram h 86 = primitiveValue86 h := by
  rw [primitive_step86]
  simp only [primitive_matches4, primitive_matches85, primitiveValue86]

def pointNode (i : Fin 10) (k : Fin 3) : Nat :=
  match i.val, k.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 1
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 13
  | 2, 0 => 8
  | 2, 1 => 0
  | 2, 2 => 2
  | 3, 0 => 14
  | 3, 1 => 0
  | 3, 2 => 2
  | 4, 0 => 0
  | 4, 1 => 8
  | 4, 2 => 2
  | 5, 0 => 0
  | 5, 1 => 14
  | 5, 2 => 2
  | 6, 0 => 11
  | 6, 1 => 11
  | 6, 2 => 15
  | 7, 0 => 11
  | 7, 1 => 16
  | 7, 2 => 15
  | 8, 0 => 16
  | 8, 1 => 11
  | 8, 2 => 15
  | 9, 0 => 16
  | 9, 1 => 16
  | 9, 2 => 15
  | _, _ => 0

def meridianNode (i : Fin 10) (k : Fin 3) : Nat :=
  match i.val, k.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 0
  | 2, 0 => 15
  | 2, 1 => 0
  | 2, 2 => 8
  | 3, 0 => 2
  | 3, 1 => 0
  | 3, 2 => 8
  | 4, 0 => 0
  | 4, 1 => 15
  | 4, 2 => 8
  | 5, 0 => 0
  | 5, 1 => 2
  | 5, 2 => 8
  | 6, 0 => 12
  | 6, 1 => 12
  | 6, 2 => 8
  | 7, 0 => 12
  | 7, 1 => 17
  | 7, 2 => 8
  | 8, 0 => 17
  | 8, 1 => 12
  | 8, 2 => 8
  | 9, 0 => 17
  | 9, 1 => 17
  | 9, 2 => 8
  | _, _ => 0

def azimuthNode (i : Fin 10) (k : Fin 3) : Nat :=
  match i.val, k.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 0
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 0
  | 2, 0 => 0
  | 2, 1 => 1
  | 2, 2 => 0
  | 3, 0 => 0
  | 3, 1 => 13
  | 3, 2 => 0
  | 4, 0 => 13
  | 4, 1 => 0
  | 4, 2 => 0
  | 5, 0 => 1
  | 5, 1 => 0
  | 5, 2 => 0
  | 6, 0 => 18
  | 6, 1 => 10
  | 6, 2 => 0
  | 7, 0 => 10
  | 7, 1 => 10
  | 7, 2 => 0
  | 8, 0 => 18
  | 8, 1 => 18
  | 8, 2 => 0
  | 9, 0 => 10
  | 9, 1 => 18
  | 9, 2 => 0
  | _, _ => 0

theorem indexed_point_matches (h : ℝ) (i : Fin 10) (k : Fin 3) :
    evaluate matrixProgram h (pointNode i k) = configuration h i k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [pointNode, primitive_matches0, primitive_matches1, primitive_matches2, primitive_matches3, primitive_matches4, primitive_matches5, primitive_matches6, primitive_matches7, primitive_matches8, primitive_matches9, primitive_matches10, primitive_matches11, primitive_matches12, primitive_matches13, primitive_matches14, primitive_matches15, primitive_matches16, primitive_matches17, primitive_matches18, primitiveValue0, primitiveValue1, primitiveValue2, primitiveValue3, primitiveValue4, primitiveValue5, primitiveValue6, primitiveValue7, primitiveValue8, primitiveValue9, primitiveValue10, primitiveValue11, primitiveValue12, primitiveValue13, primitiveValue14, primitiveValue15, primitiveValue16, primitiveValue17, primitiveValue18, configuration, north, south, upperXPlus, upperXMinus, upperYPlus, upperYMinus, lowerPP, lowerPM, lowerMP, lowerMM, vec3, geoQ, geoS, Thomson10Family.s, meridianFrame, azimuthFrame, pow_two, div_eq_mul_inv] <;> ring

theorem indexed_meridian_matches (h : ℝ) (i : Fin 10) (k : Fin 3) :
    evaluate matrixProgram h (meridianNode i k) = meridianFrame h i k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [meridianNode, primitive_matches0, primitive_matches1, primitive_matches2, primitive_matches3, primitive_matches4, primitive_matches5, primitive_matches6, primitive_matches7, primitive_matches8, primitive_matches9, primitive_matches10, primitive_matches11, primitive_matches12, primitive_matches13, primitive_matches14, primitive_matches15, primitive_matches16, primitive_matches17, primitive_matches18, primitiveValue0, primitiveValue1, primitiveValue2, primitiveValue3, primitiveValue4, primitiveValue5, primitiveValue6, primitiveValue7, primitiveValue8, primitiveValue9, primitiveValue10, primitiveValue11, primitiveValue12, primitiveValue13, primitiveValue14, primitiveValue15, primitiveValue16, primitiveValue17, primitiveValue18, configuration, north, south, upperXPlus, upperXMinus, upperYPlus, upperYMinus, lowerPP, lowerPM, lowerMP, lowerMM, vec3, geoQ, geoS, Thomson10Family.s, meridianFrame, azimuthFrame, pow_two, div_eq_mul_inv] <;> ring

theorem indexed_azimuth_matches (h : ℝ) (i : Fin 10) (k : Fin 3) :
    evaluate matrixProgram h (azimuthNode i k) = azimuthFrame h i k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [azimuthNode, primitive_matches0, primitive_matches1, primitive_matches2, primitive_matches3, primitive_matches4, primitive_matches5, primitive_matches6, primitive_matches7, primitive_matches8, primitive_matches9, primitive_matches10, primitive_matches11, primitive_matches12, primitive_matches13, primitive_matches14, primitive_matches15, primitive_matches16, primitive_matches17, primitive_matches18, primitiveValue0, primitiveValue1, primitiveValue2, primitiveValue3, primitiveValue4, primitiveValue5, primitiveValue6, primitiveValue7, primitiveValue8, primitiveValue9, primitiveValue10, primitiveValue11, primitiveValue12, primitiveValue13, primitiveValue14, primitiveValue15, primitiveValue16, primitiveValue17, primitiveValue18, configuration, north, south, upperXPlus, upperXMinus, upperYPlus, upperYMinus, lowerPP, lowerPM, lowerMP, lowerMM, vec3, geoQ, geoS, Thomson10Family.s, meridianFrame, azimuthFrame, pow_two, div_eq_mul_inv] <;> ring

#print axioms indexed_value_step
#print axioms primitive_matches0
#print axioms primitive_matches2
#print axioms primitive_matches8
#print axioms primitive_matches86
#print axioms indexed_point_matches
#print axioms indexed_meridian_matches
#print axioms indexed_azimuth_matches
end Thomson10IndexedMatrix

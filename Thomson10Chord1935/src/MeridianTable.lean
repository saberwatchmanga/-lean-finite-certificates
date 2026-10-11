import StationarityGeometryCore

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- A small scalar table for dot products; no distance denominators occur. -/
def meridianFactor (h : ℝ) (i j : Fin 10) : ℝ := by
  letI : Decidable (upperOpposite i j ∨ upperOpposite j i) := by
    unfold upperOpposite
    infer_instance
  letI : Decidable (lowerOpposite i j ∨ lowerOpposite j i) := by
    unfold lowerOpposite
    infer_instance
  letI : Decidable (crossNear i j) := by unfold crossNear; infer_instance
  letI : Decidable (crossNear j i) := by unfold crossNear; infer_instance
  exact if i=j then 0 else
  if j.val=0 then -1 else if j.val=1 then 1 else
  if i.val < 6 then
    if j.val < 6 then
      if upperOpposite i j ∨ upperOpposite j i then -2*h else -h
    else if crossNear i j then h*(1+1/geoS) else h*(1-1/geoS)
  else
    if j.val < 6 then
      if crossNear j i then -h*(1+1/geoS) else -h*(1-1/geoS)
    else if lowerOpposite i j ∨ lowerOpposite j i then 2*h else h

theorem meridian_dot_table (h : ℝ) (i j : Fin 10) (hi : 2 ≤ i.val) :
    dot3 (configuration h i-configuration h j) (meridianFrame h i)=
      geoQ h*meridianFactor h i j := by
  have hinv : geoS⁻¹^2=(1:ℝ)/2 := by simpa only [one_div] using inverse_geoS_sq
  fin_cases i <;> fin_cases j <;> norm_num at hi
  all_goals norm_num [meridianFactor,configuration,meridianFrame,north,south,
    upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,
    vec3,dot3,Pi.sub_apply,upperOpposite,lowerOpposite,crossNear]
  all_goals ring_nf
  all_goals simp only [hinv]
  all_goals ring

#print axioms meridian_dot_table
end Thomson10Stability

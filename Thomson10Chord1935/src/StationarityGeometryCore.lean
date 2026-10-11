import StationarityCore
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge
set_option maxHeartbeats 1600000

/-- The first variation contributed by point `j` to the force at point `i`.
The conditional makes the self-interaction exactly zero. -/
def pointContribution (h : ℝ) (i : Fin 10) (v : R3) : ℝ :=
  ∑ j : Fin 10, if i = j then 0 else
    -dot3 (configuration h i - configuration h j) v /
      (sqDist (configuration h i) (configuration h j) *
        Real.sqrt (sqDist (configuration h i) (configuration h j)))

/-- Meridional unit tangent directions for the fixed 45-degree configuration. -/
def meridianFrame (h : ℝ) (i : Fin 10) : R3 :=
  match i.val with
  | 0 => vec3 1 0 0
  | 1 => vec3 1 0 0
  | 2 => vec3 (-h) 0 (geoQ h)
  | 3 => vec3 h 0 (geoQ h)
  | 4 => vec3 0 (-h) (geoQ h)
  | 5 => vec3 0 h (geoQ h)
  | 6 => vec3 (h / geoS) (h / geoS) (geoQ h)
  | 7 => vec3 (h / geoS) (-h / geoS) (geoQ h)
  | 8 => vec3 (-h / geoS) (h / geoS) (geoQ h)
  | _ => vec3 (-h / geoS) (-h / geoS) (geoQ h)

/-- Azimuthal unit tangent directions for the same point labels. -/
def azimuthFrame (h : ℝ) (i : Fin 10) : R3 :=
  match i.val with
  | 0 => vec3 0 1 0
  | 1 => vec3 0 1 0
  | 2 => vec3 0 1 0
  | 3 => vec3 0 (-1) 0
  | 4 => vec3 (-1) 0 0
  | 5 => vec3 1 0 0
  | 6 => vec3 (-1 / geoS) (1 / geoS) 0
  | 7 => vec3 (1 / geoS) (1 / geoS) 0
  | 8 => vec3 (-1 / geoS) (-1 / geoS) 0
  | _ => vec3 (1 / geoS) (-1 / geoS) 0

def classifiedSqDist (h : ℝ) (i j : Fin 10) : ℝ :=
  pairKindTarget h (if i.val < j.val then pairKind i j else pairKind j i)

theorem sqDist_symmetric (p q : R3) : sqDist p q = sqDist q p := by
  unfold sqDist
  ring

theorem sqDist_configuration_eq_classified {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i j : Fin 10) (hij : i ≠ j) :
    sqDist (configuration h i) (configuration h j) = classifiedSqDist h i j := by
  have hval : i.val ≠ j.val := by
    intro hv
    exact hij (Fin.ext hv)
  by_cases hlt : i.val < j.val
  · simp [classifiedSqDist, hlt]
    exact pair_sqdist_eq_kind hh0 hh1 i j hlt
  · have hgt : j.val < i.val := by omega
    simp [classifiedSqDist, hlt]
    calc
      sqDist (configuration h i) (configuration h j) =
          sqDist (configuration h j) (configuration h i) := sqDist_symmetric _ _
      _ = pairKindTarget h (pairKind j i) := pair_sqdist_eq_kind hh0 hh1 j i hgt

theorem pointContribution_eq_classified {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i : Fin 10) (v : R3) :
    pointContribution h i v =
      ∑ j : Fin 10, if i = j then 0 else
        -dot3 (configuration h i - configuration h j) v /
          (classifiedSqDist h i j * Real.sqrt (classifiedSqDist h i j)) := by
  unfold pointContribution
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · have hd := sqDist_configuration_eq_classified hh0 hh1 i j hij
    simp only [hij, if_false]
    rw [hd]

theorem azimuth_projection_zero {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (i : Fin 10) :
    pointContribution h i (azimuthFrame h i) = 0 := by
  classical
  rw [pointContribution_eq_classified hh0 hh1]
  fin_cases i <;>
    simp [classifiedSqDist, azimuthFrame, configuration, north, south,
      upperXPlus, upperXMinus, upperYPlus, upperYMinus,
      lowerPP, lowerPM, lowerMP, lowerMM, vec3,
      dot3, Pi.sub_apply,
      pairKind, pairKindTarget, upperOpposite, lowerOpposite, crossNear,
      Fin.sum_univ_succ] <;>
    field_simp [geoS_ne] <;> ring_nf

theorem pole_meridian_projection_zero {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    pointContribution h 0 (meridianFrame h 0) = 0 ∧
    pointContribution h 1 (meridianFrame h 1) = 0 := by
  classical
  constructor
  · rw [pointContribution_eq_classified hh0 hh1]
    norm_num [classifiedSqDist, meridianFrame, configuration, north, south,
      upperXPlus, upperXMinus, upperYPlus, upperYMinus,
      lowerPP, lowerPM, lowerMP, lowerMM, vec3,
      dot3, Pi.sub_apply,
      pairKind, pairKindTarget, upperOpposite, lowerOpposite, crossNear,
      Fin.sum_univ_succ] <;>
      field_simp [geoS_ne] <;> ring_nf
  · rw [pointContribution_eq_classified hh0 hh1]
    norm_num [classifiedSqDist, meridianFrame, configuration, north, south,
      upperXPlus, upperXMinus, upperYPlus, upperYMinus,
      lowerPP, lowerPM, lowerMP, lowerMM, vec3,
      dot3, Pi.sub_apply,
      pairKind, pairKindTarget, upperOpposite, lowerOpposite, crossNear,
      Fin.sum_univ_succ] <;>
      field_simp [geoS_ne] <;> ring_nf


#print axioms sqDist_configuration_eq_classified
#print axioms pointContribution_eq_classified
#print axioms azimuth_projection_zero
#print axioms pole_meridian_projection_zero
end Thomson10Stability

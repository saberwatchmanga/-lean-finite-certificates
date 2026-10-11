import ContinuousCore
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Geometry for the explicit ten-point, one-parameter configuration only.
This file proves the unit-sphere and squared-distance facts; it does not
identify the energy of arbitrary configurations or prove global optimality.
-/

noncomputable section

namespace Thomson10Geometry

abbrev R3 := Fin 3 → ℝ

def vec3 (x y z : ℝ) : R3 :=
  fun i => if i.val = 0 then x else if i.val = 1 then y else z

def geoS : ℝ := Thomson10Family.s
def geoQ (h : ℝ) : ℝ := Real.sqrt (1 - h^2)

def north : R3 := vec3 0 0 1
def south : R3 := vec3 0 0 (-1)
def upperXPlus (h : ℝ) : R3 := vec3 (geoQ h) 0 h
def upperXMinus (h : ℝ) : R3 := vec3 (-geoQ h) 0 h
def upperYPlus (h : ℝ) : R3 := vec3 0 (geoQ h) h
def upperYMinus (h : ℝ) : R3 := vec3 0 (-geoQ h) h
def lowerPP (h : ℝ) : R3 := vec3 (geoQ h / geoS) (geoQ h / geoS) (-h)
def lowerPM (h : ℝ) : R3 := vec3 (geoQ h / geoS) (-geoQ h / geoS) (-h)
def lowerMP (h : ℝ) : R3 := vec3 (-geoQ h / geoS) (geoQ h / geoS) (-h)
def lowerMM (h : ℝ) : R3 := vec3 (-geoQ h / geoS) (-geoQ h / geoS) (-h)

def configuration (h : ℝ) (i : Fin 10) : R3 :=
  match i.val with
  | 0 => north
  | 1 => south
  | 2 => upperXPlus h
  | 3 => upperXMinus h
  | 4 => upperYPlus h
  | 5 => upperYMinus h
  | 6 => lowerPP h
  | 7 => lowerPM h
  | 8 => lowerMP h
  | _ => lowerMM h

def sqNorm (x : R3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
def sqDist (x y : R3) : ℝ := (x 0-y 0)^2 + (x 1-y 1)^2 + (x 2-y 2)^2

def upperOpposite (i j : Fin 10) : Prop :=
  (i.val = 2 ∧ j.val = 3) ∨ (i.val = 4 ∧ j.val = 5)

def lowerOpposite (i j : Fin 10) : Prop :=
  (i.val = 6 ∧ j.val = 9) ∨ (i.val = 7 ∧ j.val = 8)

def crossNear (i j : Fin 10) : Prop :=
  (i.val = 2 ∧ (j.val = 6 ∨ j.val = 7)) ∨
  (i.val = 3 ∧ (j.val = 8 ∨ j.val = 9)) ∨
  (i.val = 4 ∧ (j.val = 6 ∨ j.val = 8)) ∨
  (i.val = 5 ∧ (j.val = 7 ∨ j.val = 9))

noncomputable def pairSqTarget (h : ℝ) (i j : Fin 10) : ℝ := by
  classical
  exact if i.val = 0 then
    if j.val = 1 then 4 else if j.val < 6 then 2*(1-h) else 2*(1+h)
  else if i.val = 1 then
    if j.val < 6 then 2*(1+h) else 2*(1-h)
  else if i.val < 6 then
    if j.val < 6 then
      if upperOpposite i j then 4*(1-h^2) else 2*(1-h^2)
    else if crossNear i j then 2-geoS+(2+geoS)*h^2 else 2+geoS+(2-geoS)*h^2
  else if lowerOpposite i j then 4*(1-h^2) else 2*(1-h^2)

theorem geoS_sq : geoS^2 = 2 := by
  dsimp [geoS, Thomson10Family.s]
  exact Real.sq_sqrt (by norm_num)

theorem geoS_cube : geoS^3 = 2*geoS := by
  calc
    geoS^3 = geoS^2 * geoS := by ring
    _ = 2*geoS := by rw [geoS_sq]

theorem geoS_pos : 0 < geoS := by
  dsimp [geoS, Thomson10Family.s]
  positivity

theorem geoQ_sq {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) : geoQ h^2 = 1-h^2 := by
  unfold geoQ
  exact Real.sq_sqrt (by nlinarith [mul_pos hh0 (sub_pos.mpr hh1)])

theorem geoS_ne : geoS ≠ 0 := ne_of_gt geoS_pos

theorem inverse_geoS_sq : (1/geoS)^2 = (1:ℝ)/2 := by
  have hs := geoS_sq
  field_simp [geoS_ne]
  nlinarith

theorem radial_over_geoS_sq {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    (geoQ h / geoS)^2 = (1-h^2)/2 := by
  have hq := geoQ_sq hh0 hh1
  have hs := geoS_sq
  field_simp [geoS_ne]
  nlinarith

theorem all_points_on_unit_sphere {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i : Fin 10) : sqNorm (configuration h i) = 1 := by
  have hq := geoQ_sq hh0 hh1
  have hi := radial_over_geoS_sq hh0 hh1
  have hqNeg : (-geoQ h)^2 = geoQ h^2 := by ring
  have hiNeg : (-geoQ h / geoS)^2 = (1-h^2)/2 := by
    calc
      (-geoQ h / geoS)^2 = (-(geoQ h / geoS))^2 := by congr 1 <;> ring
      _ = (geoQ h / geoS)^2 := by rw [neg_sq]
      _ = _ := hi
  fin_cases i <;> simp [sqNorm, configuration, north, south, upperXPlus,
    upperXMinus, upperYPlus, upperYMinus, lowerPP, lowerPM, lowerMP,
    lowerMM, vec3, hq, hqNeg, hi, hiNeg] <;> ring

theorem all_pair_squared_distances {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i j : Fin 10) (hij : i.val < j.val) :
    sqDist (configuration h i) (configuration h j) = pairSqTarget h i j := by
  classical
  have hq := geoQ_sq hh0 hh1
  have hs := geoS_sq
  have hqi := radial_over_geoS_sq hh0 hh1
  have hsne := geoS_ne
  have hscube := geoS_cube
  fin_cases i <;> fin_cases j <;>
    norm_num at hij <;>
    simp [sqDist, configuration, north, south, upperXPlus, upperXMinus,
      upperYPlus, upperYMinus, lowerPP, lowerPM, lowerMP, lowerMM, vec3,
      pairSqTarget, upperOpposite, lowerOpposite, crossNear] <;>
    field_simp [hsne] <;> ring_nf <;> try simp [hq, hs, hscube] <;> ring

theorem pair_target_counts :
    (1 + 8 + 8 + 8 + 4 + 8 + 8 : ℕ) = 45 := by norm_num

#print axioms all_points_on_unit_sphere
#print axioms all_pair_squared_distances

end Thomson10Geometry

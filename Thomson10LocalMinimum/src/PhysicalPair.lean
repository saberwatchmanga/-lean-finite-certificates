import SpherePaths

noncomputable section
open scoped Topology
open Filter Set
namespace Thomson10Stability
open Thomson10Geometry

def differencePath (p v q w : R3) (k : Fin 3) (t : ℝ) : ℝ :=
  coordinatePath p v k t-coordinatePath q w k t
def differenceRate (p v q w : R3) (k : Fin 3) (t : ℝ) : ℝ :=
  coordinateRate p v k t-coordinateRate q w k t
def pairSqPath (p v q w : R3) (t : ℝ) : ℝ :=
  (differencePath p v q w 0 t)^2+(differencePath p v q w 1 t)^2+
    (differencePath p v q w 2 t)^2
def pairSqRate (p v q w : R3) (t : ℝ) : ℝ :=
  2*differencePath p v q w 0 t*differenceRate p v q w 0 t+
  2*differencePath p v q w 1 t*differenceRate p v q w 1 t+
  2*differencePath p v q w 2 t*differenceRate p v q w 2 t
def accelerationDifference (p v q w : R3) : R3 :=
  fun k => -sqNorm v*p k+sqNorm w*q k
def pairEnergyPath (p v q w : R3) (t : ℝ) : ℝ := 1/Real.sqrt (pairSqPath p v q w t)
def pairEnergyRate (p v q w : R3) (t : ℝ) : ℝ :=
  -pairSqRate p v q w t/(2*pairSqPath p v q w t*Real.sqrt (pairSqPath p v q w t))

theorem differencePath_derivative (p v q w : R3) (k : Fin 3) (t : ℝ) :
    HasDerivAt (differencePath p v q w k) (differenceRate p v q w k t) t :=
  (coordinatePath_derivative p v k t).sub (coordinatePath_derivative q w k t)

theorem pairSqPath_derivative (p v q w : R3) (t : ℝ) :
    HasDerivAt (pairSqPath p v q w) (pairSqRate p v q w t) t := by
  have h := (((differencePath_derivative p v q w 0 t).pow 2).add
    ((differencePath_derivative p v q w 1 t).pow 2)).add
    ((differencePath_derivative p v q w 2 t).pow 2)
  apply h.congr_deriv
  simp only [Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  unfold pairSqRate
  ring

theorem pairSqPath_zero (p v q w : R3) : pairSqPath p v q w 0=sqDist p q := by
  simp [pairSqPath,differencePath,coordinatePath,pathWeight,normFactor,sqDist]

theorem pairSqRate_zero (p v q w : R3) :
    pairSqRate p v q w 0=2*dot3 (p-q) (v-w) := by
  simp [pairSqRate,differencePath,differenceRate,coordinatePath,coordinateRate,
    pathWeight,pathWeightRate,normFactor,normRate]
  unfold dot3
  simp only [Pi.sub_apply]
  ring

theorem differenceRate_derivative_zero (p v q w : R3) (k : Fin 3) :
    HasDerivAt (differenceRate p v q w k) (accelerationDifference p v q w k) 0 := by
  have h := (coordinateRate_derivative_zero p v k).sub (coordinateRate_derivative_zero q w k)
  change HasDerivAt (fun x => coordinateRate p v k x-coordinateRate q w k x)
    (accelerationDifference p v q w k) 0
  apply h.congr_deriv
  unfold accelerationDifference
  ring

theorem pairSqRate_derivative_zero (p v q w : R3) :
    HasDerivAt (pairSqRate p v q w)
      (2*sqNorm (v-w)+2*dot3 (p-q) (accelerationDifference p v q w)) 0 := by
  have ht (k : Fin 3) := ((differencePath_derivative p v q w k 0).const_mul 2).mul
    (differenceRate_derivative_zero p v q w k)
  have h := ((ht 0).add (ht 1)).add (ht 2)
  apply h.congr_deriv
  simp [differenceRate,differencePath,coordinatePath,coordinateRate,pathWeight,pathWeightRate,
    normFactor,normRate]
  unfold sqNorm dot3
  simp only [Pi.sub_apply]
  ring

theorem unit_pair_acceleration_identity (p v q w : R3) (hp : sqNorm p=1) (hq : sqNorm q=1) :
    dot3 (p-q) (accelerationDifference p v q w) =
      -(sqNorm v+sqNorm w)*sqDist p q/2 := by
  have hd : sqDist p q=sqNorm p+sqNorm q-2*dot3 p q := by
    unfold sqDist sqNorm dot3
    ring
  have ha : dot3 (p-q) (accelerationDifference p v q w) =
      -sqNorm v*(sqNorm p-dot3 p q)-sqNorm w*(sqNorm q-dot3 p q) := by
    unfold dot3 accelerationDifference sqNorm
    simp only [Pi.sub_apply]
    ring
  rw [hd,ha,hp,hq]
  ring

theorem pairEnergyPath_second_derivative (p v q w : R3)
    (hp : sqNorm p=1) (hq : sqNorm q=1) (hd : 0 < sqDist p q) :
    HasDerivAt (deriv (pairEnergyPath p v q w))
      (pairSecondVariation (sqDist p q) (dot3 (p-q) (v-w))
        (sqNorm (v-w)) (sqNorm v+sqNorm w)) 0 := by
  have hd0 : 0 < pairSqPath p v q w 0 := by rw [pairSqPath_zero]; exact hd
  have heq : deriv (pairEnergyPath p v q w) =ᶠ[𝓝 (0:ℝ)] pairEnergyRate p v q w := by
    have hpos : ∀ᶠ t in 𝓝 (0:ℝ),0 < pairSqPath p v q w t :=
      (pairSqPath_derivative p v q w 0).continuousAt.eventually (Ioi_mem_nhds hd0)
    filter_upwards [hpos] with t ht
    exact (inverse_root_derivative (pairSqPath_derivative p v q w t) ht).deriv
  have h := inverse_root_slope_derivative (pairSqPath_derivative p v q w 0)
    (pairSqRate_derivative_zero p v q w) rfl hd0
  have hactual := h.congr_of_eventuallyEq heq
  apply hactual.congr_deriv
  rw [pairSqPath_zero,pairSqRate_zero,unit_pair_acceleration_identity p v q w hp hq]
  have hb : 2*sqNorm (v-w)+2*(-(sqNorm v+sqNorm w)*sqDist p q/2) =
      2*sqNorm (v-w)-(sqNorm v+sqNorm w)*sqDist p q := by ring
  rw [hb]
  exact sphere_pair_coefficient (sqDist p q) (dot3 (p-q) (v-w))
    (sqNorm (v-w)) (sqNorm v+sqNorm w) hd

#print axioms pairSqPath_derivative
#print axioms pairSqRate_derivative_zero
#print axioms unit_pair_acceleration_identity
#print axioms pairEnergyPath_second_derivative
end Thomson10Stability

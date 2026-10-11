import TangentPlaneCoordinates
import CircleKernelCore
import Mathlib.Data.Nat.Init

/-! Moment positivity for arbitrary ten points on the unit sphere.
This is the homogeneous circle kernel used by the three-point bound.
The certificate matrices, sixfold symmetrization and diagonal correction
still require a separate connection to the final energy inequality. -/
noncomputable section
open scoped BigOperators
namespace Thomson10SphereMoment
open Thomson10Geometry Thomson10Stability Thomson10TangentCoordinates
open Thomson10CircleKernel
set_option maxHeartbeats 5000000

def homogeneousCircleKernel (u v w : ℝ) : ℕ → ℝ :=
  Nat.twoStepInduction 1 (w-u*v)
    (fun _ q0 q1 => 2*(w-u*v)*q1-(1-u^2)*(1-v^2)*q0)

theorem homogeneous_kernel_equals_circle_power (a b v w : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1) (hab : dot3 a b=0)
    (hv : sqNorm v=1) (hw : sqNorm w=1) (k : ℕ) :
    homogeneousCircleKernel (dot3 a v) (dot3 a w) (dot3 v w) k =
      qCircle k (circleCoordinate a b v * star (circleCoordinate a b w)) := by
  have hre:=circle_product_real a b v w ha hb hab
  have hn : Complex.normSq (circleCoordinate a b v * star (circleCoordinate a b w))=
      (1-(dot3 a v)^2)*(1-(dot3 a w)^2) := by
    rw [Complex.normSq_mul]
    simpa using congrArg₂ (fun x y : ℝ => x*y)
      (unit_circle_normSq a b v ha hb hab hv)
      (unit_circle_normSq a b w ha hb hab hw)
  induction k using Nat.twoStepInduction with
  | zero => simp [homogeneousCircleKernel,Nat.twoStepInduction,qCircle]
  | one => simpa [homogeneousCircleKernel,Nat.twoStepInduction,qCircle] using hre.symm
  | more k hk hk1 =>
    change 2*(dot3 v w-dot3 a v*dot3 a w)*
        homogeneousCircleKernel (dot3 a v) (dot3 a w) (dot3 v w) (k+1) -
        (1-(dot3 a v)^2)*(1-(dot3 a w)^2)*
        homogeneousCircleKernel (dot3 a v) (dot3 a w) (dot3 v w) k = _
    rw [hk,hk1,qCircle_recurrence,hre,hn]

def sphereMomentMatrix (q : Fin 10 → R3) (k d : ℕ) :
    Matrix (Fin d) (Fin d) ℝ := fun r s =>
  ∑ anchor, ∑ j, ∑ l,
    (dot3 (q anchor) (q j))^r.val * (dot3 (q anchor) (q l))^s.val *
    homogeneousCircleKernel (dot3 (q anchor) (q j)) (dot3 (q anchor) (q l))
      (dot3 (q j) (q l)) k

theorem sphere_moment_isPSD (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1) (k d : ℕ) :
    IsPSD (sphereMomentMatrix q k d) := by
  classical
  choose b hb hab using fun i : Fin 10 => exists_unit_perpendicular (q i)
  let coord : Points → Points → ℂ := fun i j => circleCoordinate (q i) (b i) (q j)
  let weight : Points → Fin d → Points → ℝ := fun i r j => (dot3 (q i) (q j))^r.val
  have he : sphereMomentMatrix q k d=rawWeightedMatrix weight coord k := by
    ext r s
    unfold sphereMomentMatrix rawWeightedMatrix
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [weight,coord]
    rw [homogeneous_kernel_equals_circle_power (q i) (b i) (q j) (q l)
      (hunit i) (hb i) (hab i) (hunit j) (hunit l) k]
    rfl
  rw [he]
  exact rawWeightedMatrix_isPSD weight coord k

#print axioms homogeneous_kernel_equals_circle_power
#print axioms sphere_moment_isPSD
end Thomson10SphereMoment

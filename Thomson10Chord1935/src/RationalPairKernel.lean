import SpherePaths
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Exact low-degree Legendre moment positivity for arbitrary finite sets of points
on the unit sphere.  The addition identities are written with homogeneous real
solid harmonics, so their algebraic cores hold for arbitrary vectors.
-/

noncomputable section
open scoped BigOperators
namespace Thomson10PairKernel

open Thomson10Geometry Thomson10Stability
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def legendreP1 (t : ℝ) : ℝ := t
def legendreP2 (t : ℝ) : ℝ := (3*t^2-1)/2
def legendreP3 (t : ℝ) : ℝ := (5*t^3-3*t)/2
def legendreP4 (t : ℝ) : ℝ := (35*t^4-30*t^2+3)/8

def homogeneousP1 (x y : R3) : ℝ := dot3 x y
def homogeneousP2 (x y : R3) : ℝ :=
  (3*(dot3 x y)^2-sqNorm x*sqNorm y)/2
def homogeneousP3 (x y : R3) : ℝ :=
  (5*(dot3 x y)^3-3*sqNorm x*sqNorm y*dot3 x y)/2
def homogeneousP4 (x y : R3) : ℝ :=
  (35*(dot3 x y)^4-30*sqNorm x*sqNorm y*(dot3 x y)^2+
    3*(sqNorm x*sqNorm y)^2)/8

/-! The following are the real and imaginary solid harmonics, in order
`m=0`, then cosine and sine components for `m=1,...,l`. -/

def solidHarmonic1 (x : R3) : Fin 3 → ℝ := fun k =>
  match k.val with
  | 0 => x 2
  | 1 => x 0
  | _ => x 1

def solidWeight1 (k : Fin 3) : ℝ := 1

def solidHarmonic2 (x : R3) : Fin 5 → ℝ := fun k =>
  match k.val with
  | 0 => (3*x 2^2-sqNorm x)/2
  | 1 => -3*x 2*x 0
  | 2 => -3*x 2*x 1
  | 3 => 3*((x 0)^2-(x 1)^2)
  | _ => 6*x 0*x 1

def solidWeight2 (k : Fin 5) : ℝ :=
  match k.val with
  | 0 => 1
  | 1 => 1/3
  | 2 => 1/3
  | 3 => 1/12
  | _ => 1/12

def solidHarmonic3 (x : R3) : Fin 7 → ℝ := fun k =>
  match k.val with
  | 0 => (5*x 2^3-3*x 2*sqNorm x)/2
  | 1 => -((15*x 2^2-3*sqNorm x)/2)*x 0
  | 2 => -((15*x 2^2-3*sqNorm x)/2)*x 1
  | 3 => 15*x 2*((x 0)^2-(x 1)^2)
  | 4 => 30*x 2*x 0*x 1
  | 5 => -15*((x 0)^3-3*x 0*(x 1)^2)
  | _ => -15*(3*(x 0)^2*x 1-(x 1)^3)

def solidWeight3 (k : Fin 7) : ℝ :=
  match k.val with
  | 0 => 1
  | 1 => 1/6
  | 2 => 1/6
  | 3 => 1/60
  | 4 => 1/60
  | 5 => 1/360
  | _ => 1/360

def solidHarmonic4 (x : R3) : Fin 9 → ℝ := fun k =>
  match k.val with
  | 0 => (35*x 2^4-30*x 2^2*sqNorm x+3*(sqNorm x)^2)/8
  | 1 => -((35*x 2^3-15*x 2*sqNorm x)/2)*x 0
  | 2 => -((35*x 2^3-15*x 2*sqNorm x)/2)*x 1
  | 3 => ((105*x 2^2-15*sqNorm x)/2)*((x 0)^2-(x 1)^2)
  | 4 => (105*x 2^2-15*sqNorm x)*x 0*x 1
  | 5 => -105*x 2*((x 0)^3-3*x 0*(x 1)^2)
  | 6 => -105*x 2*(3*(x 0)^2*x 1-(x 1)^3)
  | 7 => 105*((x 0)^4-6*(x 0)^2*(x 1)^2+(x 1)^4)
  | _ => 420*x 0*x 1*((x 0)^2-(x 1)^2)

def solidWeight4 (k : Fin 9) : ℝ :=
  match k.val with
  | 0 => 1
  | 1 => 1/10
  | 2 => 1/10
  | 3 => 1/180
  | 4 => 1/180
  | 5 => 1/2520
  | 6 => 1/2520
  | 7 => 1/20160
  | _ => 1/20160

theorem solid_addition_identity_1 (x y : R3) :
    homogeneousP1 x y = ∑ k : Fin 3,
      solidWeight1 k*solidHarmonic1 x k*solidHarmonic1 y k := by
  simp [homogeneousP1, solidWeight1, solidHarmonic1, dot3, Fin.sum_univ_succ]
  ring

theorem solid_addition_identity_2 (x y : R3) :
    homogeneousP2 x y = ∑ k : Fin 5,
      solidWeight2 k*solidHarmonic2 x k*solidHarmonic2 y k := by
  simp [homogeneousP2, solidWeight2, solidHarmonic2, dot3, sqNorm,
    Fin.sum_univ_succ]
  ring

theorem solid_addition_identity_3 (x y : R3) :
    homogeneousP3 x y = ∑ k : Fin 7,
      solidWeight3 k*solidHarmonic3 x k*solidHarmonic3 y k := by
  simp [homogeneousP3, solidWeight3, solidHarmonic3, dot3, sqNorm,
    Fin.sum_univ_succ]
  ring

theorem solid_addition_identity_4 (x y : R3) :
    homogeneousP4 x y = ∑ k : Fin 9,
      solidWeight4 k*solidHarmonic4 x k*solidHarmonic4 y k := by
  simp [homogeneousP4, solidWeight4, solidHarmonic4, dot3, sqNorm,
    Fin.sum_univ_succ]
  ring

theorem legendre_addition_identity_1 (x y : R3)
    (hx : sqNorm x = 1) (hy : sqNorm y = 1) :
    legendreP1 (dot3 x y) = ∑ k : Fin 3,
      solidWeight1 k*solidHarmonic1 x k*solidHarmonic1 y k := by
  calc
    legendreP1 (dot3 x y) = homogeneousP1 x y := by
      simp [legendreP1, homogeneousP1]
    _ = _ := solid_addition_identity_1 x y

theorem legendre_addition_identity_2 (x y : R3)
    (hx : sqNorm x = 1) (hy : sqNorm y = 1) :
    legendreP2 (dot3 x y) = ∑ k : Fin 5,
      solidWeight2 k*solidHarmonic2 x k*solidHarmonic2 y k := by
  calc
    legendreP2 (dot3 x y) = homogeneousP2 x y := by
      simp [legendreP2, homogeneousP2, hx, hy]
    _ = _ := solid_addition_identity_2 x y

theorem legendre_addition_identity_3 (x y : R3)
    (hx : sqNorm x = 1) (hy : sqNorm y = 1) :
    legendreP3 (dot3 x y) = ∑ k : Fin 7,
      solidWeight3 k*solidHarmonic3 x k*solidHarmonic3 y k := by
  calc
    legendreP3 (dot3 x y) = homogeneousP3 x y := by
      simp [legendreP3, homogeneousP3, hx, hy]
    _ = _ := solid_addition_identity_3 x y

theorem legendre_addition_identity_4 (x y : R3)
    (hx : sqNorm x = 1) (hy : sqNorm y = 1) :
    legendreP4 (dot3 x y) = ∑ k : Fin 9,
      solidWeight4 k*solidHarmonic4 x k*solidHarmonic4 y k := by
  calc
    legendreP4 (dot3 x y) = homogeneousP4 x y := by
      simp [legendreP4, homogeneousP4, hx, hy]
    _ = _ := solid_addition_identity_4 x y

theorem double_feature_sum_eq_weighted_squares
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (weight : κ → ℝ)
    (feature : ι → κ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ t,
      weight k*feature i k*feature j k) =
    ∑ k ∈ t, weight k*(∑ i ∈ s, feature i k)^2 := by
  classical
  calc
    _ = ∑ i ∈ s, ∑ k ∈ t, ∑ j ∈ s,
        weight k*feature i k*feature j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ t, ∑ i ∈ s, ∑ j ∈ s,
        weight k*feature i k*feature j k := by
      exact Finset.sum_comm
    _ = ∑ k ∈ t, weight k*(∑ i ∈ s, feature i k)^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = ∑ i ∈ s, (weight k*feature i k)*(∑ j ∈ s, feature j k) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
        _ = (∑ i ∈ s, weight k*feature i k)*(∑ j ∈ s, feature j k) := by
          rw [Finset.sum_mul]
        _ = weight k*(∑ i ∈ s, feature i k)*(∑ j ∈ s, feature j k) := by
          rw [← Finset.mul_sum]
        _ = weight k*(∑ i ∈ s, feature i k)^2 := by ring

theorem finite_kernel_moment_eq_squares
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (q : ι → R3)
    (kernel : ℝ → ℝ) (weight : κ → ℝ) (feature : R3 → κ → ℝ)
    (hadd : ∀ i ∈ s, ∀ j ∈ s,
      kernel (dot3 (q i) (q j)) =
        ∑ k ∈ t, weight k*feature (q i) k*feature (q j) k) :
    (∑ i ∈ s, ∑ j ∈ s, kernel (dot3 (q i) (q j))) =
      ∑ k ∈ t, weight k*(∑ i ∈ s, feature (q i) k)^2 := by
  classical
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ t,
        weight k*feature (q i) k*feature (q j) k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hadd i hi j hj
    _ = _ := double_feature_sum_eq_weighted_squares s t weight
      (fun i k => feature (q i) k)

theorem finite_kernel_moment_nonneg
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (q : ι → R3)
    (kernel : ℝ → ℝ) (weight : κ → ℝ) (feature : R3 → κ → ℝ)
    (hw : ∀ k ∈ t, 0 ≤ weight k)
    (hadd : ∀ i ∈ s, ∀ j ∈ s,
      kernel (dot3 (q i) (q j)) =
        ∑ k ∈ t, weight k*feature (q i) k*feature (q j) k) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, kernel (dot3 (q i) (q j)) := by
  rw [finite_kernel_moment_eq_squares s t q kernel weight feature hadd]
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hw k hk) (sq_nonneg (∑ i ∈ s, feature (q i) k))

theorem solidWeight1_nonneg (k : Fin 3) : 0 ≤ solidWeight1 k := by
  fin_cases k <;> norm_num [solidWeight1]

theorem solidWeight2_nonneg (k : Fin 5) : 0 ≤ solidWeight2 k := by
  fin_cases k <;> norm_num [solidWeight2]

theorem solidWeight3_nonneg (k : Fin 7) : 0 ≤ solidWeight3 k := by
  fin_cases k <;> norm_num [solidWeight3]

theorem solidWeight4_nonneg (k : Fin 9) : 0 ≤ solidWeight4 k := by
  fin_cases k <;> norm_num [solidWeight4]

theorem legendre_moment_eq_squares_1
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    (∑ i ∈ s, ∑ j ∈ s, legendreP1 (dot3 (q i) (q j))) =
      ∑ k : Fin 3, solidWeight1 k*(∑ i ∈ s, solidHarmonic1 (q i) k)^2 := by
  apply finite_kernel_moment_eq_squares s Finset.univ q legendreP1
    solidWeight1 solidHarmonic1
  intro i hi j hj
  exact legendre_addition_identity_1 (q i) (q j) (hunit i hi) (hunit j hj)

theorem legendre_moment_eq_squares_2
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    (∑ i ∈ s, ∑ j ∈ s, legendreP2 (dot3 (q i) (q j))) =
      ∑ k : Fin 5, solidWeight2 k*(∑ i ∈ s, solidHarmonic2 (q i) k)^2 := by
  apply finite_kernel_moment_eq_squares s Finset.univ q legendreP2
    solidWeight2 solidHarmonic2
  intro i hi j hj
  exact legendre_addition_identity_2 (q i) (q j) (hunit i hi) (hunit j hj)

theorem legendre_moment_eq_squares_3
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    (∑ i ∈ s, ∑ j ∈ s, legendreP3 (dot3 (q i) (q j))) =
      ∑ k : Fin 7, solidWeight3 k*(∑ i ∈ s, solidHarmonic3 (q i) k)^2 := by
  apply finite_kernel_moment_eq_squares s Finset.univ q legendreP3
    solidWeight3 solidHarmonic3
  intro i hi j hj
  exact legendre_addition_identity_3 (q i) (q j) (hunit i hi) (hunit j hj)

theorem legendre_moment_eq_squares_4
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    (∑ i ∈ s, ∑ j ∈ s, legendreP4 (dot3 (q i) (q j))) =
      ∑ k : Fin 9, solidWeight4 k*(∑ i ∈ s, solidHarmonic4 (q i) k)^2 := by
  apply finite_kernel_moment_eq_squares s Finset.univ q legendreP4
    solidWeight4 solidHarmonic4
  intro i hi j hj
  exact legendre_addition_identity_4 (q i) (q j) (hunit i hi) (hunit j hj)

theorem legendre_moment_nonneg_1
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, legendreP1 (dot3 (q i) (q j)) := by
  apply finite_kernel_moment_nonneg s Finset.univ q legendreP1
    solidWeight1 solidHarmonic1 (fun k _ => solidWeight1_nonneg k)
  intro i hi j hj
  exact legendre_addition_identity_1 (q i) (q j) (hunit i hi) (hunit j hj)

theorem legendre_moment_nonneg_2
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, legendreP2 (dot3 (q i) (q j)) := by
  apply finite_kernel_moment_nonneg s Finset.univ q legendreP2
    solidWeight2 solidHarmonic2 (fun k _ => solidWeight2_nonneg k)
  intro i hi j hj
  exact legendre_addition_identity_2 (q i) (q j) (hunit i hi) (hunit j hj)

theorem legendre_moment_nonneg_3
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, legendreP3 (dot3 (q i) (q j)) := by
  apply finite_kernel_moment_nonneg s Finset.univ q legendreP3
    solidWeight3 solidHarmonic3 (fun k _ => solidWeight3_nonneg k)
  intro i hi j hj
  exact legendre_addition_identity_3 (q i) (q j) (hunit i hi) (hunit j hj)

theorem legendre_moment_nonneg_4
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → R3)
    (hunit : ∀ i ∈ s, sqNorm (q i) = 1) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, legendreP4 (dot3 (q i) (q j)) := by
  apply finite_kernel_moment_nonneg s Finset.univ q legendreP4
    solidWeight4 solidHarmonic4 (fun k _ => solidWeight4_nonneg k)
  intro i hi j hj
  exact legendre_addition_identity_4 (q i) (q j) (hunit i hi) (hunit j hj)

#print axioms solid_addition_identity_1
#print axioms solid_addition_identity_2
#print axioms solid_addition_identity_3
#print axioms solid_addition_identity_4
#print axioms legendre_moment_nonneg_1
#print axioms legendre_moment_nonneg_2
#print axioms legendre_moment_nonneg_3
#print axioms legendre_moment_nonneg_4

end Thomson10PairKernel

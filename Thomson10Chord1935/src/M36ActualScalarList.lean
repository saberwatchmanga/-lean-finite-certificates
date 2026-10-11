import ScalarListSemanticsRound15
import M36ScalarCoefficientSupport

/-!
Actual real-function identity through rational coefficient lists.

All saved data below is read from the accepted Round14 Lean definitions.  The
two coefficient-list correspondences are closed exact kernel computations;
the generic Horner semantics then transports that equality to every real x.
-/
noncomputable section
open scoped BigOperators
namespace Thomson10M36ActualScalarList

open Thomson10ScalarListRound15
open Thomson10M36ScalarPolynomial

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def fin13 (i : ℕ) : Fin 13 := ⟨i % 13, Nat.mod_lt _ (by decide)⟩
def fin26 (i : ℕ) : Fin 26 := ⟨i % 26, Nat.mod_lt _ (by decide)⟩

def xPoly : Poly := [0, 1]
def oneMinusXPoly : Poly := [1, -1]

def quadraticArgumentPoly : Poly :=
  add [1] (scale (-quadraticShift) (pow xPoly 2))

def hPolynomial : Poly :=
  sumRange 13 (fun i => scale (hCoefficient (fin13 i))
    (pow quadraticArgumentPoly i))

def bernstein12Polynomial (i : ℕ) : Poly :=
  scale (Nat.choose 12 i : ℚ)
    (mul (pow xPoly i) (pow oneMinusXPoly (12 - i)))

def minorantPolynomial (A : Fin 13 → Fin 13 → ℚ) : Poly :=
  sumRange 13 (fun i => sumRange 13 (fun j =>
    scale (A (fin13 i) (fin13 j))
      (mul (bernstein12Polynomial i) (bernstein12Polynomial j))))

def bernstein25Polynomial (i : ℕ) : Poly :=
  scale (Nat.choose 25 i : ℚ)
    (mul (pow xPoly i) (pow oneMinusXPoly (25 - i)))

def residualPolynomial : Poly :=
  sumRange 26 (fun i => scale (residualBernsteinCoefficient (fin26 i))
    (bernstein25Polynomial i))

def kernelPolynomial : Poly :=
  add [1] (scale (-L) (mul xPoly hPolynomial))

def certificatePolynomial : Poly :=
  add
    (add
      (scale L (mul xPoly (minorantPolynomial minorantSCoefficient)))
      (scale L (mul oneMinusXPoly
        (minorantPolynomial minorantTwoMinusSCoefficient))))
    residualPolynomial

def hFunction (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 13,
    ((hCoefficient (fin13 i) : ℚ) : ℝ) *
      (1 - (quadraticShift : ℝ) * x ^ 2) ^ i

def bernstein12Value (x : ℝ) (i : ℕ) : ℝ :=
  ((Nat.choose 12 i : ℚ) : ℝ) * (x ^ i) * (1 - x) ^ (12 - i)

def minorantFunction (A : Fin 13 → Fin 13 → ℚ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 13, ∑ j ∈ Finset.range 13,
    ((A (fin13 i) (fin13 j) : ℚ) : ℝ) *
      (bernstein12Value x i * bernstein12Value x j)

def bernstein25Value (x : ℝ) (i : ℕ) : ℝ :=
  ((Nat.choose 25 i : ℚ) : ℝ) * (x ^ i) * (1 - x) ^ (25 - i)

def residualFunction (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 26,
    ((residualBernsteinCoefficient (fin26 i) : ℚ) : ℝ) * bernstein25Value x i

def scalarKernelFunction (x : ℝ) : ℝ :=
  1 - (L : ℝ) * x * hFunction x

def scalarCertificateFunction (x : ℝ) : ℝ :=
  (L : ℝ) * x * minorantFunction minorantSCoefficient x +
    (L : ℝ) * (1 - x) * minorantFunction minorantTwoMinusSCoefficient x +
    residualFunction x

@[simp] theorem eval_xPoly (x : ℝ) : eval xPoly x = x := by
  simp [xPoly, eval]

@[simp] theorem eval_oneMinusXPoly (x : ℝ) : eval oneMinusXPoly x = 1 - x := by
  simp [oneMinusXPoly, eval]
  ring

theorem eval_quadraticArgumentPoly (x : ℝ) :
    eval quadraticArgumentPoly x = 1 - (quadraticShift : ℝ) * x ^ 2 := by
  rw [quadraticArgumentPoly, eval_add, eval_scale, eval_pow, eval_xPoly]
  push_cast
  norm_num [quadraticShift]
  ring

theorem eval_hPolynomial (x : ℝ) : eval hPolynomial x = hFunction x := by
  rw [hPolynomial, eval_sumRange]
  unfold hFunction
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_scale, eval_pow, eval_quadraticArgumentPoly]

theorem eval_bernstein12Polynomial (x : ℝ) (i : ℕ) :
    eval (bernstein12Polynomial i) x = bernstein12Value x i := by
  rw [bernstein12Polynomial, eval_scale, eval_mul, eval_pow, eval_pow,
    eval_xPoly, eval_oneMinusXPoly]
  unfold bernstein12Value
  push_cast
  ring

theorem eval_minorantPolynomial (A : Fin 13 → Fin 13 → ℚ) (x : ℝ) :
    eval (minorantPolynomial A) x = minorantFunction A x := by
  rw [minorantPolynomial, eval_sumRange]
  unfold minorantFunction
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_sumRange]
  apply Finset.sum_congr rfl
  intro j hj
  rw [eval_scale, eval_mul, eval_bernstein12Polynomial,
    eval_bernstein12Polynomial]

theorem eval_bernstein25Polynomial (x : ℝ) (i : ℕ) :
    eval (bernstein25Polynomial i) x = bernstein25Value x i := by
  rw [bernstein25Polynomial, eval_scale, eval_mul, eval_pow, eval_pow,
    eval_xPoly, eval_oneMinusXPoly]
  unfold bernstein25Value
  push_cast
  ring

theorem eval_residualPolynomial (x : ℝ) :
    eval residualPolynomial x = residualFunction x := by
  rw [residualPolynomial, eval_sumRange]
  unfold residualFunction
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_scale, eval_bernstein25Polynomial]

theorem eval_kernelPolynomial (x : ℝ) :
    eval kernelPolynomial x = scalarKernelFunction x := by
  rw [kernelPolynomial, eval_add, eval_scale, eval_mul, eval_xPoly,
    eval_hPolynomial]
  unfold scalarKernelFunction
  simp only [eval]
  push_cast
  ring

theorem eval_certificatePolynomial (x : ℝ) :
    eval certificatePolynomial x = scalarCertificateFunction x := by
  rw [certificatePolynomial, eval_add, eval_add, eval_scale, eval_mul,
    eval_xPoly, eval_scale, eval_mul, eval_oneMinusXPoly,
    eval_minorantPolynomial, eval_minorantPolynomial, eval_residualPolynomial]
  unfold scalarCertificateFunction
  push_cast
  ring

theorem kernelPolynomial_coefficients :
    kernelPolynomial = List.ofFn (fun k : Fin 26 => kernelPowerCoefficient k.val) := by
  decide +kernel

theorem certificatePolynomial_coefficients :
    certificatePolynomial =
      List.ofFn (fun k : Fin 26 => certificatePowerCoefficient k.val) := by
  decide +kernel

theorem actual_scalar_list_identity :
    ∀ x : ℝ, scalarKernelFunction x = scalarCertificateFunction x := by
  intro x
  have hlists : kernelPolynomial = certificatePolynomial := by
    calc
      kernelPolynomial = List.ofFn (fun k : Fin 26 => kernelPowerCoefficient k.val) :=
        kernelPolynomial_coefficients
      _ = List.ofFn (fun k : Fin 26 => certificatePowerCoefficient k.val) := by
        congr 1
        funext k
        exact actual_scalar_coefficient_identity k
      _ = certificatePolynomial := certificatePolynomial_coefficients.symm
  calc
    scalarKernelFunction x = eval kernelPolynomial x := (eval_kernelPolynomial x).symm
    _ = eval certificatePolynomial x := congrArg (fun p : Poly => eval p x) hlists
    _ = scalarCertificateFunction x := eval_certificatePolynomial x

#print axioms eval_quadraticArgumentPoly
#print axioms eval_hPolynomial
#print axioms eval_bernstein12Polynomial
#print axioms eval_minorantPolynomial
#print axioms eval_bernstein25Polynomial
#print axioms eval_residualPolynomial
#print axioms eval_kernelPolynomial
#print axioms eval_certificatePolynomial
#print axioms kernelPolynomial_coefficients
#print axioms certificatePolynomial_coefficients
#print axioms actual_scalar_list_identity

end Thomson10M36ActualScalarList

import CoefficientDomainRound17

/-! An integer sparse polynomial for every compact sphere-kernel R entry.
The normalization is kept explicit: the six-permutation sum is unaveraged,
and its three diagonal substitutions are unaveraged as well. -/
noncomputable section
open scoped BigOperators
namespace Thomson10RIntegerSemanticsRound17
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSymmetry
open Thomson10ActualRPolynomial Thomson10Geometry Thomson10Stability
open Thomson10SphereMoment Thomson10SymmetricSphere Thomson10RMatrixLoss Thomson10PairCut
set_option maxHeartbeats 64000000
set_option maxRecDepth 65536

def diagMap (f : Exponent → Exponent) (p : Poly) : Poly :=
  p.map (fun t => (t.1,f t.2))

theorem eval_diagMap (f : Exponent → Exponent) (p : Poly)
    (a b c u v w : ℝ)
    (hf : ∀ e, mono (f e) u v w = mono e a b c) :
    polynomialValue (diagMap f p) u v w = polynomialValue p a b c := by
  induction p with
  | nil => simp [diagMap,polynomialValue]
  | cons t p ih =>
      change termValue (t.1,f t.2) u v w +
        polynomialValue (diagMap f p) u v w =
        termValue t a b c + polynomialValue p a b c
      rw [ih]
      rw [term_value,term_value,hf t.2]
#print axioms eval_diagMap

def diagUExponent (e : Exponent) : Exponent := (e.1+e.2.1,0,0)
def diagVExponent (e : Exponent) : Exponent := (0,e.1+e.2.1,0)
def diagWExponent (e : Exponent) : Exponent := (0,0,e.1+e.2.1)
def diagU (p : Poly) : Poly := diagMap diagUExponent p
def diagV (p : Poly) : Poly := diagMap diagVExponent p
def diagW (p : Poly) : Poly := diagMap diagWExponent p

theorem eval_diagU (p : Poly) (u v w : ℝ) :
    polynomialValue (diagU p) u v w = polynomialValue p u u 1 := by
  apply eval_diagMap diagUExponent p u u 1 u v w
  intro e
  rcases e with ⟨a,b,c⟩
  simp [mono,diagUExponent,pow_add]
#print axioms eval_diagU

theorem eval_diagV (p : Poly) (u v w : ℝ) :
    polynomialValue (diagV p) u v w = polynomialValue p v v 1 := by
  apply eval_diagMap diagVExponent p v v 1 u v w
  intro e
  rcases e with ⟨a,b,c⟩
  simp [mono,diagVExponent,pow_add]
#print axioms eval_diagV

theorem eval_diagW (p : Poly) (u v w : ℝ) :
    polynomialValue (diagW p) u v w = polynomialValue p w w 1 := by
  apply eval_diagMap diagWExponent p w w 1 u v w
  intro e
  rcases e with ⟨a,b,c⟩
  simp [mono,diagWExponent,pow_add]
#print axioms eval_diagW

def compactQTerms (k : Fin 7) : Poly := match k.val with
  | 0 => qTerms0
  | 1 => qTerms1
  | 2 => qTerms2
  | 3 => qTerms3
  | 4 => qTerms4
  | 5 => qTerms5
  | 6 => qTerms6
  | _ => []

theorem eval_compactQTerms (k : Fin 7) (u v w : ℝ) :
    polynomialValue (compactQTerms k) u v w = compactKernel u v w k := by
  fin_cases k <;> rfl
#print axioms eval_compactQTerms

def coordinateMonomialTerms (r s : ℕ) : Poly := [(1,(r,s,0))]
def shiftedKernelTerms (k : Fin 7) (r s : ℕ) : Poly :=
  mul (coordinateMonomialTerms r s) (compactQTerms k)

theorem eval_coordinateMonomialTerms (r s : ℕ) (u v w : ℝ) :
    polynomialValue (coordinateMonomialTerms r s) u v w = u^r*v^s := by
  simp [coordinateMonomialTerms,polynomialValue,termValue,mono]
#print axioms eval_coordinateMonomialTerms

theorem eval_shiftedKernelTerms (k : Fin 7) (r s : ℕ) (u v w : ℝ) :
    polynomialValue (shiftedKernelTerms k r s) u v w =
      compactKernelValue k r s u v w := by
  rw [shiftedKernelTerms,eval_mul,eval_coordinateMonomialTerms,eval_compactQTerms]
  unfold compactKernelValue
  ring
#print axioms eval_shiftedKernelTerms

def zeroExponent : Exponent := (0,0,0)
def k0Correction (k : Fin 7) : Poly :=
  if k.val=0 then [(2,zeroExponent)] else []

theorem eval_shift_zeroExponent (p : Poly) (a : ℤ) (u v w : ℝ) :
    polynomialValue (shift p zeroExponent a) u v w =
      (a : ℝ)*polynomialValue p u v w := by
  rw [eval_shift]
  simp [zeroExponent,mono]
#print axioms eval_shift_zeroExponent

theorem eval_k0Correction (k : Fin 7) (u v w : ℝ) :
    polynomialValue (k0Correction k) u v w = (if k.val=0 then (2:ℝ) else 0) := by
  by_cases hk : k.val=0 <;> simp [k0Correction,hk,zeroExponent,polynomialValue,termValue,mono]
#print axioms eval_k0Correction

def integerRFromSym (mainScale : ℤ) (k : Fin 7) (symmetricTerms : Poly) : Poly :=
  shift symmetricTerms zeroExponent mainScale ++
    shift (diagU symmetricTerms) zeroExponent 3 ++
    shift (diagV symmetricTerms) zeroExponent 3 ++
    shift (diagW symmetricTerms) zeroExponent 3 ++ k0Correction k

theorem eval_integerRFromSym (mainScale : ℤ) (k : Fin 7) (symmetricTerms : Poly)
    (u v w : ℝ) :
    polynomialValue (integerRFromSym mainScale k symmetricTerms) u v w =
      (mainScale : ℝ)*polynomialValue symmetricTerms u v w+
        3*polynomialValue (diagU symmetricTerms) u v w+
        3*polynomialValue (diagV symmetricTerms) u v w+
        3*polynomialValue (diagW symmetricTerms) u v w+
        (if k.val=0 then (2:ℝ) else 0) := by
  unfold integerRFromSym
  simp only [eval_append,eval_shift_zeroExponent,eval_k0Correction]
  ring_nf
#print axioms eval_integerRFromSym

def integerRPolynomialWithScale (mainScale : ℤ) (k : Fin 7) (r s : ℕ) : Poly :=
  integerRFromSym mainScale k (sixPolynomial (shiftedKernelTerms k r s))

def integerRPolynomial (k : Fin 7) (r s : ℕ) : Poly :=
  integerRPolynomialWithScale 24 k r s

theorem eval_integerRPolynomialWithScale (mainScale : ℤ) (k : Fin 7) (r s : ℕ)
    (u v w : ℝ) :
    polynomialValue (integerRPolynomialWithScale mainScale k r s) u v w =
      (mainScale : ℝ)*polynomialValue (sixPolynomial (shiftedKernelTerms k r s)) u v w+
        3*polynomialValue (diagU (sixPolynomial (shiftedKernelTerms k r s))) u v w+
        3*polynomialValue (diagV (sixPolynomial (shiftedKernelTerms k r s))) u v w+
        3*polynomialValue (diagW (sixPolynomial (shiftedKernelTerms k r s))) u v w+
        (if k.val=0 then (2:ℝ) else 0) := by
  exact eval_integerRFromSym mainScale k _ u v w
#print axioms eval_integerRPolynomialWithScale

theorem eval_integerRPolynomial_div18 (k : Fin 7) (r s : ℕ) (u v w : ℝ) :
    polynomialValue (integerRPolynomial k r s) u v w / 18 =
      normalizedRValue k.val r s u v w := by
  rw [normalized_R_equals_compact]
  change polynomialValue (integerRPolynomialWithScale 24 k r s) u v w / 18 = _
  rw [eval_integerRPolynomialWithScale]
  simp only [eval_diagU,eval_diagV,eval_diagW,eval_sixPolynomial]
  have hkernel : (fun a b c => polynomialValue (shiftedKernelTerms k r s) a b c) =
      compactKernelValue k r s := by
    funext a b c
    exact eval_shiftedKernelTerms k r s a b c
  simp_rw [hkernel]
  by_cases hk : k.val=0
  · simp [hk,compactNormalizedR]
    ring
  · simp [hk,compactNormalizedR]
    ring
#print axioms eval_integerRPolynomial_div18

theorem actual_sphere_R_entry_equals_integerR (q : Fin 10→R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k : Fin 7) (r s : ℕ)
    (i j l : Fin 10) :
    actualRentry q k.val r s i j l =
      polynomialValue (integerRPolynomial k r s)
        (dot3 (q i) (q j)) (dot3 (q i) (q l)) (dot3 (q j) (q l)) / 18 := by
  rw [actual_R_entry_equals_coordinate_polynomial q hunit]
  rw [← eval_integerRPolynomial_div18]
#print axioms actual_sphere_R_entry_equals_integerR

end Thomson10RIntegerSemanticsRound17

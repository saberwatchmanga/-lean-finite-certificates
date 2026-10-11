import ActualRPolynomialSemantics
import Mathlib.Tactic.FinCases
noncomputable section
open scoped BigOperators
namespace Thomson10CompactKernels
open Thomson10SphereMoment Thomson10ActualRPolynomial Thomson10Geometry Thomson10Stability Thomson10RMatrixLoss
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
abbrev IntegerTerm := ℤ × (ℕ × ℕ × ℕ)
def termValue (t : IntegerTerm) (u v w : ℝ) : ℝ := (t.1 : ℝ)*u^t.2.1*v^t.2.2.1*w^t.2.2.2
def polynomialValue (p : List IntegerTerm) (u v w : ℝ) : ℝ := (p.map (fun t=>termValue t u v w)).sum
def qTerms0 : List IntegerTerm := [
  (1,(0,0,0))]
def compactQ0 (u v w : ℝ) := polynomialValue qTerms0 u v w
theorem kernel_0_equals_compact (u v w : ℝ) : homogeneousCircleKernel u v w 0=compactQ0 u v w := by
  rw [homogeneous_kernel_zero]
  norm_num [compactQ0,qTerms0,polynomialValue,termValue]
  <;> ring
#print axioms kernel_0_equals_compact
def qTerms1 : List IntegerTerm := [
  (1,(0,0,1)),
  (-1,(1,1,0))]
def compactQ1 (u v w : ℝ) := polynomialValue qTerms1 u v w
theorem kernel_1_equals_compact (u v w : ℝ) : homogeneousCircleKernel u v w 1=compactQ1 u v w := by
  rw [homogeneous_kernel_one]
  norm_num [compactQ1,qTerms1,polynomialValue,termValue]
  <;> ring
#print axioms kernel_1_equals_compact
def qTerms2 : List IntegerTerm := [
  (-1,(0,0,0)),
  (2,(0,0,2)),
  (1,(0,2,0)),
  (1,(2,0,0)),
  (-4,(1,1,1)),
  (1,(2,2,0))]
def compactQ2 (u v w : ℝ) := polynomialValue qTerms2 u v w
theorem kernel_2_equals_compact (u v w : ℝ) : homogeneousCircleKernel u v w 2=compactQ2 u v w := by
  rw [homogeneous_kernel_succ_two u v w 0,kernel_1_equals_compact,kernel_0_equals_compact]
  norm_num [compactQ2,qTerms2,compactQ1,qTerms1,compactQ0,qTerms0,polynomialValue,termValue]
  <;> ring
#print axioms kernel_2_equals_compact
def qTerms3 : List IntegerTerm := [
  (-3,(0,0,1)),
  (3,(1,1,0)),
  (4,(0,0,3)),
  (3,(0,2,1)),
  (3,(2,0,1)),
  (-12,(1,1,2)),
  (-3,(1,3,0)),
  (-3,(3,1,0)),
  (9,(2,2,1)),
  (-1,(3,3,0))]
def compactQ3 (u v w : ℝ) := polynomialValue qTerms3 u v w
theorem kernel_3_equals_compact (u v w : ℝ) : homogeneousCircleKernel u v w 3=compactQ3 u v w := by
  rw [homogeneous_kernel_succ_two u v w 1,kernel_2_equals_compact,kernel_1_equals_compact]
  norm_num [compactQ3,qTerms3,compactQ2,qTerms2,compactQ1,qTerms1,polynomialValue,termValue]
  <;> ring
#print axioms kernel_3_equals_compact
def qTerms4 : List IntegerTerm := [
  (1,(0,0,0)),
  (-8,(0,0,2)),
  (-2,(0,2,0)),
  (-2,(2,0,0)),
  (16,(1,1,1)),
  (8,(0,0,4)),
  (8,(0,2,2)),
  (1,(0,4,0)),
  (8,(2,0,2)),
  (-4,(2,2,0)),
  (1,(4,0,0)),
  (-32,(1,1,3)),
  (-16,(1,3,1)),
  (-16,(3,1,1)),
  (40,(2,2,2)),
  (6,(2,4,0)),
  (6,(4,2,0)),
  (-16,(3,3,1)),
  (1,(4,4,0))]
def compactQ4 (u v w : ℝ) := polynomialValue qTerms4 u v w
theorem kernel_4_equals_compact (u v w : ℝ) : homogeneousCircleKernel u v w 4=compactQ4 u v w := by
  rw [homogeneous_kernel_succ_two u v w 2,kernel_3_equals_compact,kernel_2_equals_compact]
  norm_num [compactQ4,qTerms4,compactQ3,qTerms3,compactQ2,qTerms2,polynomialValue,termValue]
  <;> ring
#print axioms kernel_4_equals_compact
def qTerms5 : List IntegerTerm := [
  (5,(0,0,1)),
  (-5,(1,1,0)),
  (-20,(0,0,3)),
  (-10,(0,2,1)),
  (-10,(2,0,1)),
  (60,(1,1,2)),
  (10,(1,3,0)),
  (10,(3,1,0)),
  (16,(0,0,5)),
  (20,(0,2,3)),
  (5,(0,4,1)),
  (20,(2,0,3)),
  (-40,(2,2,1)),
  (5,(4,0,1)),
  (-80,(1,1,4)),
  (-60,(1,3,2)),
  (-5,(1,5,0)),
  (-60,(3,1,2)),
  (0,(3,3,0)),
  (-5,(5,1,0)),
  (140,(2,2,3)),
  (50,(2,4,1)),
  (50,(4,2,1)),
  (-100,(3,3,2)),
  (-10,(3,5,0)),
  (-10,(5,3,0)),
  (25,(4,4,1)),
  (-1,(5,5,0))]
def compactQ5 (u v w : ℝ) := polynomialValue qTerms5 u v w
theorem kernel_5_equals_compact (u v w : ℝ) : homogeneousCircleKernel u v w 5=compactQ5 u v w := by
  rw [homogeneous_kernel_succ_two u v w 3,kernel_4_equals_compact,kernel_3_equals_compact]
  norm_num [compactQ5,qTerms5,compactQ4,qTerms4,compactQ3,qTerms3,polynomialValue,termValue]
  <;> ring
#print axioms kernel_5_equals_compact
def qTerms6 : List IntegerTerm := [
  (-1,(0,0,0)),
  (18,(0,0,2)),
  (3,(0,2,0)),
  (3,(2,0,0)),
  (-36,(1,1,1)),
  (-48,(0,0,4)),
  (-36,(0,2,2)),
  (-3,(0,4,0)),
  (-36,(2,0,2)),
  (9,(2,2,0)),
  (-3,(4,0,0)),
  (192,(1,1,3)),
  (72,(1,3,1)),
  (72,(3,1,1)),
  (32,(0,0,6)),
  (48,(0,2,4)),
  (18,(0,4,2)),
  (1,(0,6,0)),
  (48,(2,0,4)),
  (-216,(2,2,2)),
  (-27,(2,4,0)),
  (18,(4,0,2)),
  (-27,(4,2,0)),
  (1,(6,0,0)),
  (-192,(1,1,5)),
  (-192,(1,3,3)),
  (-36,(1,5,1)),
  (-192,(3,1,3)),
  (48,(3,3,1)),
  (-36,(5,1,1)),
  (432,(2,2,4)),
  (252,(2,4,2)),
  (15,(2,6,0)),
  (252,(4,2,2)),
  (15,(4,4,0)),
  (15,(6,2,0)),
  (-448,(3,3,3)),
  (-120,(3,5,1)),
  (-120,(5,3,1)),
  (210,(4,4,2)),
  (15,(4,6,0)),
  (15,(6,4,0)),
  (-36,(5,5,1)),
  (1,(6,6,0))]
def compactQ6 (u v w : ℝ) := polynomialValue qTerms6 u v w
theorem kernel_6_equals_compact (u v w : ℝ) : homogeneousCircleKernel u v w 6=compactQ6 u v w := by
  rw [homogeneous_kernel_succ_two u v w 4,kernel_5_equals_compact,kernel_4_equals_compact]
  norm_num [compactQ6,qTerms6,compactQ5,qTerms5,compactQ4,qTerms4,polynomialValue,termValue]
  <;> ring
#print axioms kernel_6_equals_compact
def compactKernel (u v w : ℝ) (k : Fin 7) : ℝ := match k.val with
  | 0 => compactQ0 u v w
  | 1 => compactQ1 u v w
  | 2 => compactQ2 u v w
  | 3 => compactQ3 u v w
  | 4 => compactQ4 u v w
  | 5 => compactQ5 u v w
  | 6 => compactQ6 u v w
  | _ => 0
theorem homogeneous_circle_kernel_equals_compact (u v w : ℝ) (k : Fin 7) : homogeneousCircleKernel u v w k.val=compactKernel u v w k := by
  fin_cases k
  · exact kernel_0_equals_compact u v w
  · exact kernel_1_equals_compact u v w
  · exact kernel_2_equals_compact u v w
  · exact kernel_3_equals_compact u v w
  · exact kernel_4_equals_compact u v w
  · exact kernel_5_equals_compact u v w
  · exact kernel_6_equals_compact u v w
#print axioms homogeneous_circle_kernel_equals_compact

def compactKernelValue (k : Fin 7) (r s : ℕ) (u v w : ℝ) : ℝ := u^r*v^s*compactKernel u v w k
def compactNormalizedR (k : Fin 7) (r s : ℕ) (u v w : ℝ) : ℝ :=
  8*sixCoordinateAverage (compactKernelValue k r s) u v w+
    sixCoordinateAverage (compactKernelValue k r s) u u 1+
    sixCoordinateAverage (compactKernelValue k r s) v v 1+
    sixCoordinateAverage (compactKernelValue k r s) w w 1+(if k.val=0 then 1 else 0)/9
theorem normalized_R_equals_compact (k : Fin 7) (r s : ℕ) (u v w : ℝ) :
    normalizedRValue k.val r s u v w=compactNormalizedR k r s u v w := by
  unfold normalizedRValue compactNormalizedR sixCoordinateAverage kernelValue compactKernelValue
  simp_rw [homogeneous_circle_kernel_equals_compact]
#print axioms normalized_R_equals_compact
theorem actual_sphere_R_entry_equals_compact (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1)
    (k : Fin 7) (r s : ℕ) (i j l : Fin 10) :
    actualRentry q k.val r s i j l=compactNormalizedR k r s (dot3 (q i) (q j)) (dot3 (q i) (q l)) (dot3 (q j) (q l)) := by
  rw [actual_R_entry_equals_coordinate_polynomial q hunit,normalized_R_equals_compact]
#print axioms actual_sphere_R_entry_equals_compact
end Thomson10CompactKernels


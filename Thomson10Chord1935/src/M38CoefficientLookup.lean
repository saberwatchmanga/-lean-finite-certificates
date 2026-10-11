import CoefficientDomainRound17

noncomputable section
namespace M38CoefficientLookup
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10SparseSymmetry Thomson10CoefficientDomain
open Thomson10UnweightedSparseRows Thomson10UnweightedSparseMerge
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

def zeroExponent : Exponent := (0,0,0)

theorem eval_shift_zeroExponent (p : Poly) (a : ℤ) (u v w : ℝ) :
    polynomialValue (shift p zeroExponent a) u v w = (a : ℝ) * polynomialValue p u v w := by
  rw [eval_shift]
  simp [zeroExponent,mono]
#print axioms M38CoefficientLookup.eval_shift_zeroExponent

def totalDegree (e : Exponent) : ℕ := e.1+e.2.1+e.2.2
def exponentIndex (e : Exponent) : ℕ :=
  let n:=totalDegree e
  n*(n+1)*(n+2)/6+(e.1*(n+1)-e.1*(e.1-1)/2)+e.2.1
theorem exponent_index_matches : ∀ j : Fin 455,
    exponentIndex (coefficientExponents.getD j.val (0,0,0))=j.val := by decide +kernel
#print axioms M38CoefficientLookup.exponent_index_matches

def coefficientLookup (cs : List ℤ) (e : Exponent) : ℤ :=
  if totalDegree e≤12 then cs.getD (exponentIndex e) 0 else 0

theorem coefficient_zero_outside (p : Poly) (e : Exponent)
    (hp : ∀ t∈p,t.2∈degree12Support) (he : e∉degree12Support) : coefficient p e=0 := by
  induction p with
  | nil => simp [coefficient]
  | cons t p ih =>
    have ht : t.2≠e := by
      intro ht
      apply he
      rw [←ht]
      exact hp t (by simp)
    have htail : ∀ s∈p,s.2∈degree12Support := fun s hs=>hp s (by simp [hs])
    rw [coefficient_cons,if_neg ht,ih htail]
    simp
#print axioms M38CoefficientLookup.coefficient_zero_outside

theorem indexed_table_gives_lookup (p : Poly) (cs : List ℤ)
    (hp : ∀ t∈p,t.2∈degree12Support)
    (hc : ∀ j : Fin 455,coefficient p (coefficientExponents.getD j.val (0,0,0))=cs.getD j.val 0)
    (e : Exponent) : coefficient p e=coefficientLookup cs e := by
  by_cases he : totalDegree e≤12
  · have hs : e∈degree12Support := (mem_degree12Support e).mpr he
    obtain ⟨j,hj⟩:=every_support_exponent_has_index e hs
    unfold coefficientLookup
    rw [if_pos he,←hj,hc,exponent_index_matches]
  · have hs : e∉degree12Support := by
      intro hs
      exact he ((mem_degree12Support e).mp hs)
    rw [coefficient_zero_outside p e hp hs]
    simp [coefficientLookup,he]
#print axioms M38CoefficientLookup.indexed_table_gives_lookup

def shiftAllowed (s e : Exponent) : Prop := s.1≤e.1∧s.2.1≤e.2.1∧s.2.2≤e.2.2
instance (s e : Exponent) : Decidable (shiftAllowed s e) := by unfold shiftAllowed;infer_instance
def subExponent (e s : Exponent) : Exponent := (e.1-s.1,e.2.1-s.2.1,e.2.2-s.2.2)
def shiftedCoefficient (f : Exponent→ℤ) (s : Exponent) (a : ℤ) (e : Exponent) : ℤ :=
  if shiftAllowed s e then a*f (subExponent e s) else 0

theorem add_exponents_eq_iff (s f e : Exponent) :
    addExp s f=e↔shiftAllowed s e∧f=subExponent e s := by
  rcases s with ⟨a,b,c⟩
  rcases f with ⟨d,g,h⟩
  rcases e with ⟨i,j,k⟩
  simp only [addExp,shiftAllowed,subExponent,Prod.mk.injEq]
  omega
#print axioms M38CoefficientLookup.add_exponents_eq_iff

theorem coefficient_shift (p : Poly) (s : Exponent) (a : ℤ) (e : Exponent) :
    coefficient (shift p s a) e=shiftedCoefficient (coefficient p) s a e := by
  induction p with
  | nil => simp [shift,coefficient,shiftedCoefficient]
  | cons t p ih =>
    change coefficient ((a*t.1,addExp s t.2)::shift p s a) e=_
    rw [coefficient_cons,ih]
    by_cases hs : shiftAllowed s e
    · by_cases ht : t.2=subExponent e s
      · simp [shiftedCoefficient,hs,add_exponents_eq_iff,ht,coefficient_cons,mul_add]
      · simp [shiftedCoefficient,hs,add_exponents_eq_iff,ht,coefficient_cons,mul_add]
    · simp [shiftedCoefficient,hs,add_exponents_eq_iff]
#print axioms M38CoefficientLookup.coefficient_shift

theorem coefficient_shift_zero (p : Poly) (a : ℤ) (e : Exponent) :
    coefficient (shift p zeroExponent a) e=a*coefficient p e := by
  rw [coefficient_shift]
  simp [shiftedCoefficient,shiftAllowed,subExponent,zeroExponent]
#print axioms M38CoefficientLookup.coefficient_shift_zero

def swapUVExponent (e : Exponent) : Exponent := (e.2.1,e.1,e.2.2)
def swapVWExponent (e : Exponent) : Exponent := (e.1,e.2.2,e.2.1)
theorem swapUV_exponent_eq (f e : Exponent) : swapUVExponent f=e↔f=swapUVExponent e := by
  rcases f with ⟨a,b,c⟩
  rcases e with ⟨d,g,h⟩
  simp only [swapUVExponent,Prod.mk.injEq]
  tauto
theorem swapVW_exponent_eq (f e : Exponent) : swapVWExponent f=e↔f=swapVWExponent e := by
  rcases f with ⟨a,b,c⟩
  rcases e with ⟨d,g,h⟩
  simp only [swapVWExponent,Prod.mk.injEq]
  tauto

theorem coefficient_swapUV (p : Poly) (e : Exponent) :
    coefficient (swapUV p) e=coefficient p (swapUVExponent e) := by
  induction p with
  | nil => simp [swapUV,coefficient]
  | cons t p ih =>
    change coefficient ((t.1,swapUVExponent t.2)::swapUV p) e=_
    simp only [coefficient_cons,swapUV_exponent_eq,ih]
#print axioms M38CoefficientLookup.coefficient_swapUV

theorem coefficient_swapVW (p : Poly) (e : Exponent) :
    coefficient (swapVW p) e=coefficient p (swapVWExponent e) := by
  induction p with
  | nil => simp [swapVW,coefficient]
  | cons t p ih =>
    change coefficient ((t.1,swapVWExponent t.2)::swapVW p) e=_
    simp only [coefficient_cons,swapVW_exponent_eq,ih]
#print axioms M38CoefficientLookup.coefficient_swapVW

def sixCoefficients (f : Exponent→ℤ) (e : Exponent) : ℤ :=
  f e+f (swapVWExponent e)+f (swapUVExponent e)+
    f (swapVWExponent (swapUVExponent e))+f (swapUVExponent (swapVWExponent e))+
    f (swapUVExponent (swapVWExponent (swapUVExponent e)))
theorem coefficient_sixPolynomial (p : Poly) (e : Exponent) :
    coefficient (sixPolynomial p) e=sixCoefficients (coefficient p) e := by
  simp only [sixPolynomial,coefficient_append,coefficient_swapUV,coefficient_swapVW,sixCoefficients]
#print axioms M38CoefficientLookup.coefficient_sixPolynomial
end M38CoefficientLookup

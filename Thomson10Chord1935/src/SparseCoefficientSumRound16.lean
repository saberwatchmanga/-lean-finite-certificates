import SparseGramSemanticsRound16

noncomputable section
open scoped BigOperators
namespace Thomson10SparseCoefficientSum
open Thomson10SparsePolynomial
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem coefficient_append (p q : Poly) (e : Exponent) :
    coefficient (p++q) e=coefficient p e+coefficient q e := by
  simp [coefficient]
#print axioms coefficient_append

theorem coefficient_flatten_ofFn (n : ℕ) (f : Fin n→Poly) (e : Exponent) :
    coefficient (List.flatten (List.ofFn f)) e=∑ i,coefficient (f i) e := by
  induction n with
  | zero => simp [coefficient]
  | succ n ih =>
    rw [List.ofFn_succ,List.flatten_cons,coefficient_append,Fin.sum_univ_succ,ih]
#print axioms coefficient_flatten_ofFn

def addCoefficients : List ℤ→List ℤ→List ℤ
  | [],q=>q
  | p,[]=>p
  | a::p,b::q=>(a+b)::addCoefficients p q

def sumCoefficientRows : List (List ℤ)→List ℤ
  | []=>[]
  | p::ps=>addCoefficients p (sumCoefficientRows ps)

theorem getD_addCoefficients (p q : List ℤ) (k : ℕ) :
    (addCoefficients p q).getD k 0=p.getD k 0+q.getD k 0 := by
  induction p generalizing q k with
  | nil => simp [addCoefficients]
  | cons a p ih =>
    cases q with
    | nil => simp [addCoefficients]
    | cons b q =>
      cases k with
      | zero => simp [addCoefficients]
      | succ k => simpa only [addCoefficients,List.getD_cons_succ] using ih q k
#print axioms getD_addCoefficients

theorem getD_sumCoefficientRows (ps : List (List ℤ)) (k : ℕ) :
    (sumCoefficientRows ps).getD k 0=(ps.map (fun p=>p.getD k 0)).sum := by
  induction ps with
  | nil => simp [sumCoefficientRows]
  | cons p ps ih =>
    rw [sumCoefficientRows,getD_addCoefficients,ih]
    simp
#print axioms getD_sumCoefficientRows

theorem integer_sum_ofFn (n : ℕ) (f : Fin n→ℤ) :
    (List.ofFn f).sum=∑ i,f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.ofFn_succ,List.sum_cons,Fin.sum_univ_succ,ih]
#print axioms integer_sum_ofFn

theorem map_getD_in_bounds {α β : Type} (p : List α) (f : α→β) (a : α) (b : β)
    (k : ℕ) (h : k<p.length) : (p.map f).getD k b=f (p.getD k a) := by
  induction p generalizing k with
  | nil => simp at h
  | cons x p ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hk : k<p.length := by simpa using h
      simpa only [List.map_cons,List.getD_cons_succ] using ih k hk
#print axioms map_getD_in_bounds
end Thomson10SparseCoefficientSum

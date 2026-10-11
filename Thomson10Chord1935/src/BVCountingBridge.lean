import ThreePointCounting

/-! Exact repeated-index accounting for the normalized three-point expression.
Here the three endpoint terms are a SUM with coefficient one each. The
six-permutation symmetrization of the actual polynomial is still separate. -/
noncomputable section
open scoped BigOperators
namespace Thomson10BVCounting
open Thomson10ThreePoint
set_option maxHeartbeats 5000000

def allTripleSum (F : Fin 10 → Fin 10 → Fin 10 → ℝ) : ℝ := ∑ i, ∑ j, ∑ k,F i j k
def offEndpointSum (F : Fin 10 → Fin 10 → Fin 10 → ℝ) : ℝ :=
  ∑ i, ∑ j, if i≠j then F i j j else 0

theorem all_triples_decomposition (F : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (hfirst : ∀ i j k,F i j k=F j i k)
    (hlast : ∀ i j k,F i j k=F i k j) :
    allTripleSum F=tripleSum F+3*offEndpointSum F+(∑ i,F i i i) := by
  classical
  have hpoint (i j k : Fin 10) : F i j k=
      (if distinct i j k then F i j k else 0)+
      (if i=j ∧ i≠k then F k i i else 0)+
      (if i=k ∧ i≠j then F j i i else 0)+
      (if j=k ∧ i≠j then F i j j else 0)+
      (if i=j ∧ j=k then F i i i else 0) := by
    by_cases hij : i=j
    · subst j
      by_cases hik : i=k
      · subst k;simp [distinct]
      · simp [distinct,hik,Ne.symm hik]
        rw [hlast i i k,hfirst i k i]
    · by_cases hik : i=k
      · subst k
        simp [distinct,hij,Ne.symm hij]
        rw [hfirst i j i]
      · by_cases hjk : j=k
        · subst k;simp [distinct,hij,hik]
        · simp [distinct,hij,hik,hjk]
  have hcol1 : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if i=j ∧ i≠k then F k i i else 0)=offEndpointSum F := by
    unfold offEndpointSum
    calc
      _ = ∑ i : Fin 10, ∑ k : Fin 10, if i≠k then F k i i else 0 := by
        apply Finset.sum_congr rfl;intro i hi
        rw [Finset.sum_comm]
        simp [ite_and]
      _ = _ := by rw [Finset.sum_comm];simp only [ne_comm]
  have hcol2 : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if i=k ∧ i≠j then F j i i else 0)=offEndpointSum F := by
    unfold offEndpointSum
    simp only [ite_and]
    simp
    rw [Finset.sum_comm]
    rfl
  have hcol3 : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if j=k ∧ i≠j then F i j j else 0)=offEndpointSum F := by
    simp [offEndpointSum,ite_and]
  have hdiag : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if i=j ∧ j=k then F i i i else 0)=(∑ i : Fin 10,F i i i) := by
    simp [ite_and]
  calc
    _ = (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
        ((if distinct i j k then F i j k else 0)+
        (if i=j ∧ i≠k then F k i i else 0)+
        (if i=k ∧ i≠j then F j i i else 0)+
        (if j=k ∧ i≠j then F i j j else 0)+
        (if i=j ∧ j=k then F i i i else 0))) := by
      unfold allTripleSum
      apply Finset.sum_congr rfl;intro i hi
      apply Finset.sum_congr rfl;intro j hj
      apply Finset.sum_congr rfl;intro k hk
      exact hpoint i j k
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [hcol1,hcol2,hcol3,hdiag]
      unfold tripleSum
      ring

theorem three_endpoint_sum (F : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    tripleSum (fun i j k => F i j j+F i k k+F j k k)=24*offEndpointSum F := by
  let B : Fin 10 → Fin 10 → ℝ := fun i j => if i=j then 0 else F i j j
  have he : tripleSum (fun i j k => F i j j+F i k k+F j k k)=
      3*tripleSum (fun i j k => (B i j+B i k+B j k)/3) := by
    unfold tripleSum
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i hi
    apply Finset.sum_congr rfl;intro j hj
    apply Finset.sum_congr rfl;intro k hk
    by_cases hd : distinct i j k
    · simp [hd,B,hd.1,hd.2.1,hd.2.2];ring
    · simp [hd]
  rw [he,three_pair_sum B (by intro i;simp [B])]
  have hb : (∑ i, ∑ j,B i j)=offEndpointSum F := by
    simp [B,offEndpointSum,ite_not]
  rw [hb];ring

theorem normalized_R_sum_equals_eight_all (F : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (c : ℝ) (hfirst : ∀ i j k,F i j k=F j i k)
    (hlast : ∀ i j k,F i j k=F i k j) (hdiag : ∀ i,F i i i=c) :
    tripleSum (fun i j k => 8*F i j k+F i j j+F i k k+F j k k+c/9)=
      8*allTripleSum F := by
  have hs : tripleSum (fun i j k => 8*F i j k+F i j j+F i k k+F j k k+c/9)=
      8*tripleSum F+tripleSum (fun i j k => F i j j+F i k k+F j k k)+
      tripleSum (fun _ _ _ => c/9) := by
    unfold tripleSum
    simp only [←Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i hi
    apply Finset.sum_congr rfl;intro j hj
    apply Finset.sum_congr rfl;intro k hk
    split_ifs <;> ring
  rw [hs,three_endpoint_sum,triple_constant,all_triples_decomposition F hfirst hlast]
  simp only [hdiag]
  simp;ring

#print axioms all_triples_decomposition
#print axioms three_endpoint_sum
#print axioms normalized_R_sum_equals_eight_all
end Thomson10BVCounting

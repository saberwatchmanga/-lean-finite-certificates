import BVCountingBridge
import CertificateMatrixBridge

/-! Connect the actual sphere kernel to six-permutation averages and the
repeated-index correction R. This supplies its moment identity, not the
finite polynomial/SOS certificate or a new distance exclusion. -/
noncomputable section
open scoped BigOperators
namespace Thomson10SymmetricSphere
open Thomson10BVCounting Thomson10SphereMoment Thomson10CircleKernel
open Thomson10ThreePoint
open Thomson10Geometry Thomson10Stability
set_option maxHeartbeats 5000000

def symSix (F : Fin 10 → Fin 10 → Fin 10 → ℝ) (i j k : Fin 10) : ℝ :=
  (F i j k+F j i k+F i k j+F k i j+F j k i+F k j i)/6

theorem symSix_first (F : Fin 10 → Fin 10 → Fin 10 → ℝ) (i j k : Fin 10) :
    symSix F i j k=symSix F j i k := by unfold symSix;ring
theorem symSix_last (F : Fin 10 → Fin 10 → Fin 10 → ℝ) (i j k : Fin 10) :
    symSix F i j k=symSix F i k j := by unfold symSix;ring

theorem all_sum_swap_first (F : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    allTripleSum (fun i j k => F j i k)=allTripleSum F := by
  unfold allTripleSum
  rw [Finset.sum_comm]

theorem all_sum_swap_last (F : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    allTripleSum (fun i j k => F i k j)=allTripleSum F := by
  unfold allTripleSum
  apply Finset.sum_congr rfl;intro i hi
  rw [Finset.sum_comm]

theorem all_sum_symSix (F : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    allTripleSum (symSix F)=allTripleSum F := by
  have h12:=all_sum_swap_first F
  have h23:=all_sum_swap_last F
  have h312 : allTripleSum (fun i j k => F k i j)=allTripleSum F := by
    rw [all_sum_swap_last (fun i j k => F j i k),all_sum_swap_first F]
  have h231 : allTripleSum (fun i j k => F j k i)=allTripleSum F := by
    rw [all_sum_swap_first (fun i j k => F i k j),all_sum_swap_last F]
  have h321 : allTripleSum (fun i j k => F k j i)=allTripleSum F := by
    rw [all_sum_swap_first (fun i j k => F k i j)]
    exact h312
  have he : allTripleSum (symSix F)=
      (allTripleSum F+allTripleSum (fun i j k => F j i k)+
       allTripleSum (fun i j k => F i k j)+allTripleSum (fun i j k => F k i j)+
       allTripleSum (fun i j k => F j k i)+allTripleSum (fun i j k => F k j i))/6 := by
    simp only [allTripleSum,symSix,div_eq_mul_inv,←Finset.sum_mul,Finset.sum_add_distrib]
  rw [he,h12,h23,h312,h231,h321];ring

def indexSphereKernel (q : Fin 10 → R3) (k : ℕ) (r s : ℕ)
    (i j l : Fin 10) : ℝ :=
  (dot3 (q i) (q j))^r*(dot3 (q i) (q l))^s*
    homogeneousCircleKernel (dot3 (q i) (q j)) (dot3 (q i) (q l))
      (dot3 (q j) (q l)) k

theorem homogeneous_all_one (k : ℕ) :
    homogeneousCircleKernel 1 1 1 k=if k=0 then 1 else 0 := by
  cases k with
  | zero => simp [homogeneousCircleKernel,Nat.twoStepInduction]
  | succ k =>
    cases k with
    | zero => simp [homogeneousCircleKernel,Nat.twoStepInduction]
    | succ k => simp [homogeneousCircleKernel,Nat.twoStepInduction]

theorem sym_sphere_diagonal (q : Fin 10 → R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k r s : ℕ) (i : Fin 10) :
    symSix (indexSphereKernel q k r s) i i i=if k=0 then 1 else 0 := by
  have hd : dot3 (q i) (q i)=1 := by rw [dot3_self,hunit i]
  simp only [symSix,indexSphereKernel,hd,one_pow,one_mul,homogeneous_all_one]
  split_ifs <;> norm_num

theorem sym_sphere_sum_is_actual_moment (q : Fin 10 → R3) (k d : ℕ) (r s : Fin d) :
    allTripleSum (symSix (indexSphereKernel q k r.val s.val))=
      sphereMomentMatrix q k d r s := by
  rw [all_sum_symSix]
  rfl

theorem actual_normalized_R_sum (q : Fin 10 → R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k d : ℕ) (r s : Fin d) :
    tripleSum (fun i j l =>
      8*symSix (indexSphereKernel q k r.val s.val) i j l+
      symSix (indexSphereKernel q k r.val s.val) i j j+
      symSix (indexSphereKernel q k r.val s.val) i l l+
      symSix (indexSphereKernel q k r.val s.val) j l l+
      (if k=0 then 1 else 0)/9)=8*sphereMomentMatrix q k d r s := by
  rw [normalized_R_sum_equals_eight_all (symSix (indexSphereKernel q k r.val s.val))
      (if k=0 then 1 else 0)
      (symSix_first _) (symSix_last _) (sym_sphere_diagonal q hunit k r.val s.val)]
  rw [sym_sphere_sum_is_actual_moment]

#print axioms all_sum_symSix
#print axioms homogeneous_all_one
#print axioms sym_sphere_diagonal
#print axioms sym_sphere_sum_is_actual_moment
#print axioms actual_normalized_R_sum
end Thomson10SymmetricSphere

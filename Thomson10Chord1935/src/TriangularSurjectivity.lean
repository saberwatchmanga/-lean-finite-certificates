import DiagonalDominance
import CircleKernelCore
import Mathlib.Data.Fin.VecNotation

/-! Finite back-substitution over real numbers. This generic theorem does
not certify that any saved integer matrix satisfies its hypotheses. -/
noncomputable section
open scoped BigOperators
namespace Thomson10MatrixCongruence
set_option maxHeartbeats 4000000

def matVec {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j,C i j*y j

theorem upper_triangular_matVec_surjective (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hupper : ∀ i j, j.val < i.val → C i j = 0)
    (hdiag : ∀ i,C i i≠0) : Function.Surjective (matVec C) := by
  induction n with
  | zero =>
    intro x
    refine ⟨fun i => Fin.elim0 i,?_⟩
    funext i;exact Fin.elim0 i
  | succ n ih =>
    intro x
    let last : Fin (n+1) := Fin.last n
    let z : ℝ := x last/C last last
    let D : Matrix (Fin n) (Fin n) ℝ := fun i j => C i.castSucc j.castSucc
    have hDu : ∀ i j : Fin n, j.val < i.val → D i j = 0 := by
      intro i j hij;exact hupper i.castSucc j.castSucc hij
    have hDd : ∀ i : Fin n,D i i≠0 := fun i => hdiag i.castSucc
    obtain ⟨y,hy⟩:=ih D hDu hDd (fun i => x i.castSucc-C i.castSucc last*z)
    refine ⟨@Fin.snoc n (fun _ => ℝ) y z,?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change (∑ j,C last j*(@Fin.snoc n (fun _ => ℝ) y z) j)=x last
      rw [Fin.sum_univ_castSucc]
      have hz : C last last*z=x last := by
        dsimp [z];field_simp [hdiag last]
      have hzero (j : Fin n) : C last j.castSucc=0 := by
        apply hupper
        exact j.isLt
      simpa [last,hzero] using hz
    · change (∑ k,C j.castSucc k*(@Fin.snoc n (fun _ => ℝ) y z) k)=x j.castSucc
      rw [Fin.sum_univ_castSucc]
      have hj:=congrFun hy j
      dsimp [matVec,D] at hj
      simpa [last] using (show (∑ k : Fin n,C j.castSucc k.castSucc*y k)+
          C j.castSucc last*z=x j.castSucc by linarith [hj])

#print axioms upper_triangular_matVec_surjective
end Thomson10MatrixCongruence

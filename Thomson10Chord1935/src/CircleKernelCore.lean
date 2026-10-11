import Mathlib.Analysis.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
Round-12 development core for the circle kernel.  This file deliberately stops before
identifying the complex coordinates with projections of arbitrary points on S^2.
-/

noncomputable section
open scoped BigOperators

namespace Thomson10CircleKernel

abbrev Points := Fin 10

/-- The real-part recurrence induced by multiplication by a complex number. -/
theorem re_pow_succ2 (z : ℂ) (k : ℕ) :
    (z ^ (k + 2)).re = 2 * z.re * (z ^ (k + 1)).re - Complex.normSq z * (z ^ k).re := by
  have hp : z ^ (k + 2) = z * (z * z ^ k) := by
    calc
      z ^ (k + 2) = z ^ (k + 1) * z := by rw [pow_succ]
      _ = (z ^ k * z) * z := by rw [pow_succ]
      _ = z * (z * z ^ k) := by ring
  rw [hp, pow_succ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

def qCircle (k : ℕ) (z : ℂ) : ℝ := (z ^ k).re

theorem qCircle_recurrence (z : ℂ) (k : ℕ) :
    qCircle (k + 2) z = 2 * z.re * qCircle (k + 1) z - Complex.normSq z * qCircle k z :=
  re_pow_succ2 z k

theorem qCircle_mul_conj_pow (k : ℕ) (z w : ℂ) :
    qCircle k (z * star w) = (z ^ k * star (w ^ k)).re := by
  unfold qCircle
  rw [mul_pow]
  simp

theorem re_mul_conj_sum (f g : Points → ℂ) :
    ((∑ i, f i) * star (∑ j, g j)).re =
      ∑ i, ∑ j, (f i * star (g j)).re := by
  calc
    ((∑ i, f i) * star (∑ j, g j)).re =
        ((∑ i, f i) * ∑ j, star (g j)).re := by simp
    _ = (∑ i, ∑ j, f i * star (g j)).re := by rw [Fintype.sum_mul_sum]
    _ = ∑ i, ∑ j, (f i * star (g j)).re := by simp

def aggregateFeature {d : ℕ}
    (weight : Points → Fin d → Points → ℝ)
    (coord : Points → Points → ℂ) (k : ℕ) (anchor : Points) (a : Fin d) : ℂ :=
  ∑ j, (weight anchor a j : ℂ) * (coord anchor j) ^ k

def aggregateReal {d : ℕ} (weight : Points → Fin d → Points → ℝ)
    (coord : Points → Points → ℂ) (k : ℕ) : Points → Fin d → ℝ :=
  fun anchor a => (aggregateFeature weight coord k anchor a).re

def aggregateImag {d : ℕ} (weight : Points → Fin d → Points → ℝ)
    (coord : Points → Points → ℂ) (k : ℕ) : Points → Fin d → ℝ :=
  fun anchor a => (aggregateFeature weight coord k anchor a).im

def realGramMatrix {d m : ℕ} (feature : Fin m → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => ∑ i, feature i a * feature i b

def aggregateGramMatrix {d : ℕ} (weight : Points → Fin d → Points → ℝ)
    (coord : Points → Points → ℂ) (k : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  realGramMatrix (aggregateReal weight coord k) + realGramMatrix (aggregateImag weight coord k)

def rawWeightedMatrix {d : ℕ} (weight : Points → Fin d → Points → ℝ)
    (coord : Points → Points → ℂ) (k : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => ∑ anchor, ∑ j, ∑ l,
      weight anchor a j * weight anchor b l *
      qCircle k (coord anchor j * star (coord anchor l))

lemma weighted_kernel_term {d : ℕ} (weight : Points → Fin d → Points → ℝ)
    (coord : Points → Points → ℂ) (k : ℕ) (anchor : Points) (a b : Fin d)
    (j l : Points) :
    weight anchor a j * weight anchor b l *
        qCircle k (coord anchor j * star (coord anchor l)) =
      (((weight anchor a j : ℂ) * (coord anchor j) ^ k) *
        star ((weight anchor b l : ℂ) * (coord anchor l) ^ k)).re := by
  rw [qCircle_mul_conj_pow]
  simp [Complex.mul_re]
  ring

lemma anchor_double_sum_eq_aggregate {d : ℕ}
    (weight : Points → Fin d → Points → ℝ) (coord : Points → Points → ℂ)
    (k : ℕ) (anchor : Points) (a b : Fin d) :
    (∑ j, ∑ l, weight anchor a j * weight anchor b l *
      qCircle k (coord anchor j * star (coord anchor l))) =
      (aggregateFeature weight coord k anchor a).re *
        (aggregateFeature weight coord k anchor b).re +
      (aggregateFeature weight coord k anchor a).im *
        (aggregateFeature weight coord k anchor b).im := by
  calc
    _ = ∑ j, ∑ l,
        (((weight anchor a j : ℂ) * (coord anchor j) ^ k) *
          star ((weight anchor b l : ℂ) * (coord anchor l) ^ k)).re := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      exact weighted_kernel_term weight coord k anchor a b j l
    _ = ((∑ j, (weight anchor a j : ℂ) * (coord anchor j) ^ k) *
        star (∑ l, (weight anchor b l : ℂ) * (coord anchor l) ^ k)).re := by
      symm
      exact re_mul_conj_sum
        (fun j => (weight anchor a j : ℂ) * (coord anchor j) ^ k)
        (fun l => (weight anchor b l : ℂ) * (coord anchor l) ^ k)
    _ = (aggregateFeature weight coord k anchor a).re *
          (aggregateFeature weight coord k anchor b).re +
        (aggregateFeature weight coord k anchor a).im *
          (aggregateFeature weight coord k anchor b).im := by
      change (aggregateFeature weight coord k anchor a *
        star (aggregateFeature weight coord k anchor b)).re = _
      simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
      ring

theorem rawWeighted_eq_aggregateGram {d : ℕ}
    (weight : Points → Fin d → Points → ℝ) (coord : Points → Points → ℂ) (k : ℕ) :
    rawWeightedMatrix weight coord k = aggregateGramMatrix weight coord k := by
  classical
  ext a b
  unfold rawWeightedMatrix aggregateGramMatrix realGramMatrix aggregateReal aggregateImag
  change (∑ anchor, ∑ j, ∑ l,
      weight anchor a j * weight anchor b l *
        qCircle k (coord anchor j * star (coord anchor l))) =
    (∑ anchor, (aggregateFeature weight coord k anchor a).re *
      (aggregateFeature weight coord k anchor b).re) +
    (∑ anchor, (aggregateFeature weight coord k anchor a).im *
      (aggregateFeature weight coord k anchor b).im)
  calc
    _ = ∑ anchor, ((aggregateFeature weight coord k anchor a).re *
        (aggregateFeature weight coord k anchor b).re +
      (aggregateFeature weight coord k anchor a).im *
        (aggregateFeature weight coord k anchor b).im) := by
      apply Finset.sum_congr rfl
      intro anchor hanchor
      exact anchor_double_sum_eq_aggregate weight coord k anchor a b
    _ = _ := by rw [Finset.sum_add_distrib]

def IsPSD {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ a b, M a b = M b a) ∧
  (∀ x : Fin d → ℝ, 0 ≤ ∑ a, ∑ b, x a * M a b * x b)

def gramQuadratic {d m : ℕ} (feature : Fin m → Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ a, ∑ b, x a * (realGramMatrix feature) a b * x b

theorem gramQuadratic_eq_sum_squares {d m : ℕ} (feature : Fin m → Fin d → ℝ)
    (x : Fin d → ℝ) :
    gramQuadratic feature x = ∑ i, (∑ a, x a * feature i a) ^ 2 := by
  classical
  unfold gramQuadratic realGramMatrix
  calc
    _ = ∑ a, ∑ b, ∑ i, x a * (feature i a * feature i b) * x b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ i, ∑ b, x a * (feature i a * feature i b) * x b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ a, ∑ b, x a * (feature i a * feature i b) * x b := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ a, ∑ b, (x a * feature i a) * (x b * feature i b) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ i, (∑ a, x a * feature i a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sq, ← Fintype.sum_mul_sum]

theorem realGramMatrix_isPSD {d m : ℕ} (feature : Fin m → Fin d → ℝ) :
    IsPSD (realGramMatrix feature) := by
  classical
  constructor
  · intro a b
    simp [realGramMatrix, mul_comm]
  · intro x
    change 0 ≤ gramQuadratic feature x
    rw [gramQuadratic_eq_sum_squares feature x]
    exact Finset.sum_nonneg fun i hi => sq_nonneg _

theorem rawWeightedMatrix_isPSD {d : ℕ}
    (weight : Points → Fin d → Points → ℝ) (coord : Points → Points → ℂ) (k : ℕ) :
    IsPSD (rawWeightedMatrix weight coord k) := by
  rw [rawWeighted_eq_aggregateGram]
  unfold IsPSD aggregateGramMatrix
  constructor
  · intro a b
    simp [realGramMatrix, mul_comm]
  · intro x
    have hr := gramQuadratic_eq_sum_squares (aggregateReal weight coord k) x
    have hi := gramQuadratic_eq_sum_squares (aggregateImag weight coord k) x
    calc
      0 ≤ (∑ anchor, (∑ a, x a * aggregateReal weight coord k anchor a) ^ 2) +
          (∑ anchor, (∑ a, x a * aggregateImag weight coord k anchor a) ^ 2) :=
        add_nonneg
          (Finset.sum_nonneg fun anchor hanchor => sq_nonneg _)
          (Finset.sum_nonneg fun anchor hanchor => sq_nonneg _)
      _ = gramQuadratic (aggregateReal weight coord k) x +
          gramQuadratic (aggregateImag weight coord k) x := by rw [← hr, ← hi]
      _ = ∑ a, ∑ b, x a *
          ((realGramMatrix (aggregateReal weight coord k) +
            realGramMatrix (aggregateImag weight coord k)) a b) * x b := by
        simp [gramQuadratic, Matrix.add_apply, realGramMatrix,
          Finset.sum_add_distrib, mul_add, add_mul]

#print axioms re_pow_succ2
#print axioms qCircle_mul_conj_pow
#print axioms rawWeighted_eq_aggregateGram
#print axioms gramQuadratic_eq_sum_squares
#print axioms realGramMatrix_isPSD
#print axioms rawWeightedMatrix_isPSD

end Thomson10CircleKernel

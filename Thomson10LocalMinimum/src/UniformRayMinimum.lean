import RotationSliceGeometry
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open scoped Topology
open Filter Set
namespace Thomson10Stability
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

-- This abstract bridge deliberately retains physical continuity/smoothness hypotheses.
theorem compact_uniform_positive_second_derivatives {U : Type*} [TopologicalSpace U]
    (K : Set U) (hK : IsCompact K) (F : U → ℝ → ℝ)
    (hc : ∀ u ∈ K, ContinuousAt
      (fun z : ℝ × U => deriv (deriv (F z.2)) z.1) (0,u))
    (hp : ∀ u ∈ K, 0<deriv (deriv (F u)) 0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ u ∈ K, ∀ t : ℝ,
      |t|<ε → 0<deriv (deriv (F u)) t := by
  have he : ∀ᶠ t in 𝓝 (0:ℝ), ∀ u ∈ K, 0<deriv (deriv (F u)) t :=
    hK.eventually_forall_of_forall_eventually (fun u hu =>
      (hc u hu).eventually (Ioi_mem_nhds (hp u hu)))
  obtain ⟨ε,hε,hball⟩:=Metric.mem_nhds_iff.mp he
  refine ⟨ε,hε,?_⟩
  intro u hu t ht
  exact hball (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht) u hu

theorem compact_uniform_ray_increase {U : Type*} [TopologicalSpace U]
    (K : Set U) (hK : IsCompact K) (F : U → ℝ → ℝ) (ρ : ℝ) (hρ : 0<ρ)
    (hd : ∀ u ∈ K, ∀ t : ℝ, |t|<ρ → DifferentiableAt ℝ (F u) t)
    (hdd : ∀ u ∈ K, ∀ t : ℝ, |t|<ρ → DifferentiableAt ℝ (deriv (F u)) t)
    (hc : ∀ u ∈ K, ContinuousAt
      (fun z : ℝ × U => deriv (deriv (F z.2)) z.1) (0,u))
    (hp : ∀ u ∈ K, 0<deriv (deriv (F u)) 0)
    (hz : ∀ u ∈ K, deriv (F u) 0=0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ u ∈ K, ∀ t : ℝ,
      0<t → t<ε → F u 0<F u t := by
  obtain ⟨δ,hδ,hpositive⟩:=compact_uniform_positive_second_derivatives K hK F hc hp
  refine ⟨min ρ δ,lt_min hρ hδ,?_⟩
  intro u hu t ht0 htε
  have htρ : t<ρ:=lt_of_lt_of_le htε (min_le_left _ _)
  have htδ : t<δ:=lt_of_lt_of_le htε (min_le_right _ _)
  have hxr (x : ℝ) (hx : x ∈ Icc 0 t) : |x|<ρ := by
    rw [abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 htρ
  have hxd (x : ℝ) (hx : x ∈ Icc 0 t) : |x|<δ := by
    rw [abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 htδ
  have hm : StrictMonoOn (deriv (F u)) (Icc 0 t) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 t)
      (fun x hx => (hdd u hu x (hxr x hx)).continuousAt.continuousWithinAt)
      (fun x hx => hpositive u hu x (hxd x (interior_subset hx)))
  have hfirst (x : ℝ) (hx : x ∈ interior (Icc 0 t)) : 0<deriv (F u) x := by
    have hxi := interior_subset hx
    have hx0 : 0<x := by
      rw [interior_Icc] at hx
      exact hx.1
    have he:=hm ⟨le_refl 0,le_of_lt ht0⟩ hxi hx0
    rwa [hz u hu] at he
  have hf : StrictMonoOn (F u) (Icc 0 t) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 t)
      (fun x hx => (hd u hu x (hxr x hx)).continuousAt.continuousWithinAt) hfirst
  exact hf ⟨le_refl 0,le_of_lt ht0⟩ ⟨le_of_lt ht0,le_refl t⟩ ht0

#print axioms compact_uniform_positive_second_derivatives
#print axioms compact_uniform_ray_increase
end Thomson10Stability

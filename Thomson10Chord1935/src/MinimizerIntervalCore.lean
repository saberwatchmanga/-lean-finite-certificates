import EnergyBridge
import ArithmeticEnclosures

/- Conditional interval transfer. Actual endpoint signs are proved separately. -/
noncomputable section
namespace Thomson10Bounds
open Thomson10Family Thomson10Bridge Set

def heightLower : ℝ := 42268741 / 100000000
def heightUpper : ℝ := 42268743 / 100000000

def PhysicalMinimum (h : ℝ) : Prop :=
  h ∈ Ioo (0:ℝ) 1 ∧ ∀ k ∈ Ioo (0:ℝ) 1, k ≠ h → actualEnergy h < actualEnergy k

theorem endpoint_parameters_in_domain :
    (Thomson10Arithmetic.tLeft : ℝ) ∈ Ioo (0:ℝ) 1 ∧
    (Thomson10Arithmetic.tRight : ℝ) ∈ Ioo (0:ℝ) 1 := by
  norm_num [Thomson10Arithmetic.tLeft, Thomson10Arithmetic.tRight]

theorem stationary_between_endpoints {m : ℝ} (hm : m ∈ Ioo (0:ℝ) 1)
    (hz : slope m = 0)
    (hl : slope (Thomson10Arithmetic.tLeft : ℝ) < 0)
    (hr : 0 < slope (Thomson10Arithmetic.tRight : ℝ)) :
    (Thomson10Arithmetic.tLeft : ℝ) < m ∧ m < (Thomson10Arithmetic.tRight : ℝ) := by
  constructor
  · by_contra h
    have hmono := slope_strictMono.monotoneOn hm endpoint_parameters_in_domain.1 (le_of_not_gt h)
    rw [hz] at hmono
    linarith
  · by_contra h
    have hmono := slope_strictMono.monotoneOn endpoint_parameters_in_domain.2 hm (le_of_not_gt h)
    rw [hz] at hmono
    linarith

theorem stationary_sqrt_in_height_interval {m : ℝ} (hm : m ∈ Ioo (0:ℝ) 1)
    (hz : slope m = 0)
    (hl : slope (Thomson10Arithmetic.tLeft : ℝ) < 0)
    (hr : 0 < slope (Thomson10Arithmetic.tRight : ℝ)) :
    heightLower < Real.sqrt m ∧ Real.sqrt m < heightUpper := by
  obtain ⟨hml, hmr⟩ := stationary_between_endpoints hm hz hl hr
  have hs : (Real.sqrt m)^2 = m := Real.sq_sqrt (le_of_lt hm.1)
  have hp : 0 < Real.sqrt m := Real.sqrt_pos.2 hm.1
  have hlo : heightLower^2 < (Thomson10Arithmetic.tLeft : ℝ) := by
    norm_num [heightLower, Thomson10Arithmetic.tLeft]
  have hhi : (Thomson10Arithmetic.tRight : ℝ) < heightUpper^2 := by
    norm_num [heightUpper, Thomson10Arithmetic.tRight]
  have hup : 0 < heightUpper := by norm_num [heightUpper]
  constructor <;> nlinarith

theorem sqrt_stationary_is_physical_minimum {m : ℝ} (hm : m ∈ Ioo (0:ℝ) 1)
    (hz : slope m = 0) : PhysicalMinimum (Real.sqrt m) := by
  have hs : (Real.sqrt m)^2 = m := Real.sq_sqrt (le_of_lt hm.1)
  have hp : 0 < Real.sqrt m := Real.sqrt_pos.2 hm.1
  have hlt : Real.sqrt m < 1 := by nlinarith [hm.2]
  refine ⟨⟨hp, hlt⟩, ?_⟩
  intro k hk hne
  have hk2 : k^2 ∈ Ioo (0:ℝ) 1 := ⟨sq_pos_of_pos hk.1, by nlinarith [hk.1, hk.2]⟩
  have hkm : k^2 ≠ m := by
    intro heq
    apply hne
    nlinarith [hk.1]
  rw [actual_energy_eq_heightEnergy hp hlt, actual_energy_eq_heightEnergy hk.1 hk.2]
  unfold heightEnergy
  rw [hs]
  exact stationary_strict_minimum hm hz (k^2) hk2 hkm

#print axioms stationary_between_endpoints
#print axioms stationary_sqrt_in_height_interval
#print axioms sqrt_stationary_is_physical_minimum
end Thomson10Bounds

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import ArithmeticEnclosures
import ContinuousCore

/- Soundness lemmas for the rational interval operations used by the
   Thomson-10 endpoint certificates.  The interval computations themselves
   are imported unchanged from ArithmeticEnclosures. -/
namespace Thomson10Intervals

abbrev I := Thomson10Arithmetic.I

def Contains (i : I) (x : ℝ) : Prop :=
  (i.lo : ℝ) ≤ x ∧ x ≤ (i.hi : ℝ)

theorem point_sound (r : Rat) :
    Contains (Thomson10Arithmetic.point r) (r : ℝ) := by
  simp [Contains, Thomson10Arithmetic.point]

theorem add_sound {i j : I} {x y : ℝ}
    (hi : Contains i x) (hj : Contains j y) :
    Contains (Thomson10Arithmetic.add i j) (x + y) := by
  rcases hi with ⟨hilo, hihi⟩
  rcases hj with ⟨hjlo, hjhi⟩
  simp only [Contains, Thomson10Arithmetic.add, Rat.cast_add]
  constructor <;> linarith

theorem neg_sound {i : I} {x : ℝ}
    (hi : Contains i x) :
    Contains (Thomson10Arithmetic.neg i) (-x) := by
  rcases hi with ⟨hilo, hihi⟩
  simp only [Contains, Thomson10Arithmetic.neg, Rat.cast_neg]
  constructor <;> linarith

theorem sub_sound {i j : I} {x y : ℝ}
    (hi : Contains i x) (hj : Contains j y) :
    Contains (Thomson10Arithmetic.sub i j) (x - y) := by
  have h := add_sound hi (neg_sound hj)
  simpa [Thomson10Arithmetic.sub, sub_eq_add_neg] using h

theorem mul_sound {i j : I} {x y : ℝ}
    (hi : Contains i x) (hj : Contains j y) :
    Contains (Thomson10Arithmetic.mul i j) (x * y) := by
  rcases hi with ⟨hilo, hihi⟩
  rcases hj with ⟨hjlo, hjhi⟩
  let a : ℝ := i.lo
  let b : ℝ := i.hi
  let c : ℝ := j.lo
  let d : ℝ := j.hi
  have hax : a ≤ x := hilo
  have hxb : x ≤ b := hihi
  have hcy : c ≤ y := hjlo
  have hyd : y ≤ d := hjhi
  have hab : a ≤ b := le_trans hax hxb
  have hcd : c ≤ d := le_trans hcy hyd
  have hminAc : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ a * c := by
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hminAd : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ a * d := by
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hminBc : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ b * c := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hminBd : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ b * d := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmaxAc : a * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hmaxAd : a * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hmaxBc : b * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hmaxBd : b * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hlower : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · have hxy : 0 ≤ x * y := mul_nonneg hx hy
        by_cases ha : a < 0
        · have had : a * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le (le_trans hy hyd)
          exact le_trans hminAd (le_trans had hxy)
        · by_cases hc : c < 0
          · have hbc : b * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_trans hx hxb) hc.le
            exact le_trans hminBc (le_trans hbc hxy)
          · have hac : a * c ≤ x * y := by
              calc
                a * c ≤ x * c := mul_le_mul_of_nonneg_right hax (le_of_not_gt hc)
                _ ≤ x * y := mul_le_mul_of_nonneg_left hcy hx
            exact le_trans hminAc hac
      · have hy' : y ≤ 0 := le_of_not_ge hy
        have hbc : b * c ≤ x * y := by
          calc
            b * c ≤ x * c := mul_le_mul_of_nonpos_right hxb (le_trans hcy hy')
            _ ≤ x * y := mul_le_mul_of_nonneg_left hcy hx
        exact le_trans hminBc hbc
    · have hx' : x ≤ 0 := le_of_not_ge hx
      by_cases hy : 0 ≤ y
      · have had : a * d ≤ x * y := by
          calc
            a * d ≤ x * d := mul_le_mul_of_nonneg_right hax (le_trans hy hyd)
            _ ≤ x * y := mul_le_mul_of_nonpos_left hyd hx'
        exact le_trans hminAd had
      · have hy' : y ≤ 0 := le_of_not_ge hy
        have hxy : 0 ≤ x * y := mul_nonneg_of_nonpos_of_nonpos hx' hy'
        by_cases hb : 0 < b
        · have hbc : b * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) (le_trans hcy hy')
          exact le_trans hminBc (le_trans hbc hxy)
        · by_cases hd : 0 < d
          · have had : a * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_trans hax hx') hd.le
            exact le_trans hminAd (le_trans had hxy)
          · have hbd : b * d ≤ x * y := by
              have hb' : b ≤ 0 := le_of_not_gt hb
              have hd' : d ≤ 0 := le_of_not_gt hd
              calc
                b * d ≤ x * d := mul_le_mul_of_nonpos_right hxb hd'
                _ ≤ x * y := mul_le_mul_of_nonpos_left hyd hx'
            exact le_trans hminBd hbd
  have hupper : x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · have hbd : x * y ≤ b * d := by
          calc
            x * y ≤ b * y := mul_le_mul_of_nonneg_right hxb hy
            _ ≤ b * d := mul_le_mul_of_nonneg_left hyd (le_trans hx hxb)
        exact le_trans hbd hmaxBd
      · have hy' : y ≤ 0 := le_of_not_ge hy
        by_cases ha : a < 0
        · have hac : 0 ≤ a * c := mul_nonneg_of_nonpos_of_nonpos ha.le (le_trans hcy hy')
          have hxy : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy'
          exact le_trans hxy (le_trans hac hmaxAc)
        · by_cases hd : 0 < d
          · have hbd : 0 ≤ b * d := mul_nonneg (le_trans hx hxb) hd.le
            have hxy : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy'
            exact le_trans hxy (le_trans hbd hmaxBd)
          · have ha' : 0 ≤ a := le_of_not_gt ha
            have hd' : d ≤ 0 := le_of_not_gt hd
            have had : x * y ≤ a * d := by
              calc
                x * y ≤ x * d := mul_le_mul_of_nonneg_left hyd hx
                _ ≤ a * d := mul_le_mul_of_nonpos_right hax hd'
            exact le_trans had hmaxAd
    · have hx' : x ≤ 0 := le_of_not_ge hx
      by_cases hy : 0 ≤ y
      · by_cases hb : 0 < b
        · have hbd : 0 ≤ b * d := mul_nonneg hb.le (le_trans hy hyd)
          have hxy : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx' hy
          exact le_trans hxy (le_trans hbd hmaxBd)
        · by_cases hc : c < 0
          · have hac : 0 ≤ a * c := mul_nonneg_of_nonpos_of_nonpos (le_trans hax hx') hc.le
            have hxy : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx' hy
            exact le_trans hxy (le_trans hac hmaxAc)
          · have hb' : b ≤ 0 := le_of_not_gt hb
            have hc' : 0 ≤ c := le_of_not_gt hc
            have hbc : x * y ≤ b * c := by
              calc
                x * y ≤ x * c := mul_le_mul_of_nonpos_left hcy hx'
                _ ≤ b * c := mul_le_mul_of_nonneg_right hxb hc'
            exact le_trans hbc hmaxBc
      · have hy' : y ≤ 0 := le_of_not_ge hy
        have hac : x * y ≤ a * c := by
          calc
            x * y ≤ a * y := mul_le_mul_of_nonpos_right hax hy'
            _ ≤ a * c := mul_le_mul_of_nonpos_left hcy (le_trans hax hx')
        exact le_trans hac hmaxAc
  change ((min (min (i.lo * j.lo) (i.lo * j.hi))
      (min (i.hi * j.lo) (i.hi * j.hi)) : Rat) : ℝ) ≤ x * y ∧
    x * y ≤ ((max (max (i.lo * j.lo) (i.lo * j.hi))
      (max (i.hi * j.lo) (i.hi * j.hi)) : Rat) : ℝ)
  constructor
  · simpa only [Rat.cast_min, Rat.cast_mul] using hlower
  · simpa only [Rat.cast_max, Rat.cast_mul] using hupper

theorem reciprocal_sound {i : I} {x : ℝ}
    (hi : Contains i x) (hpos : 0 < (i.lo : ℝ)) :
    Contains (Thomson10Arithmetic.reciprocal i) (1 / x) := by
  have hxpos : 0 < x := lt_of_lt_of_le hpos hi.1
  have hhipos : 0 < (i.hi : ℝ) := lt_of_lt_of_le hxpos hi.2
  have hlo : (1 : ℝ) / (i.hi : ℝ) ≤ 1 / x :=
    (div_le_div_iff₀ hhipos hxpos).2 (by linarith [hi.2])
  have hhi : (1 : ℝ) / x ≤ 1 / (i.lo : ℝ) :=
    (div_le_div_iff₀ hxpos hpos).2 (by linarith [hi.1])
  change ((1 / i.hi : Rat) : ℝ) ≤ 1 / x ∧
    1 / x ≤ ((1 / i.lo : Rat) : ℝ)
  constructor
  · simpa only [Rat.cast_div, Rat.cast_one] using hlo
  · simpa only [Rat.cast_div, Rat.cast_one] using hhi

theorem divide_sound {i j : I} {x y : ℝ}
    (hi : Contains i x) (hj : Contains j y) (hpos : 0 < (j.lo : ℝ)) :
    Contains (Thomson10Arithmetic.divide i j) (x / y) := by
  have hr := reciprocal_sound hj hpos
  have hm := mul_sound hi hr
  simpa [Thomson10Arithmetic.divide, div_eq_mul_inv] using hm

theorem cube_sound {i : I} {x : ℝ}
    (hi : Contains i x) :
    Contains (Thomson10Arithmetic.cube i) (x ^ 3) := by
  have hm := mul_sound (mul_sound hi hi) hi
  simpa [Thomson10Arithmetic.cube, pow_succ, pow_two] using hm

theorem cube_sound_pos {i : I} {x : ℝ}
    (hi : Contains i x) (_hpos : 0 < (i.lo : ℝ)) :
    Contains (Thomson10Arithmetic.cube i) (x ^ 3) :=
  cube_sound hi

theorem scale_sound {n : Rat} {i : I} {x : ℝ}
    (hi : Contains i x) :
    Contains (Thomson10Arithmetic.scale n i) ((n : ℝ) * x) := by
  simpa [Thomson10Arithmetic.scale, Thomson10Arithmetic.point] using
    mul_sound (point_sound n) hi

theorem scale_sound_nonneg {n : Rat} {i : I} {x : ℝ}
    (_hn : 0 ≤ n) (hi : Contains i x) :
    Contains (Thomson10Arithmetic.scale n i) ((n : ℝ) * x) :=
  scale_sound hi

theorem root_sound {argument candidate : I} {x : ℝ}
    (hr : Thomson10Arithmetic.RootBounds argument candidate)
    (ha : Contains argument x) :
    Contains candidate (Real.sqrt x) := by
  rcases hr with ⟨harg0, hargOrd, hcan0, hcanOrd, hlowSq, hhighSq⟩
  have harg0R : (0 : ℝ) ≤ (argument.lo : ℝ) := by exact_mod_cast harg0
  have hcan0R : (0 : ℝ) < (candidate.lo : ℝ) := by exact_mod_cast hcan0
  have hx0 : 0 ≤ x := le_trans harg0R ha.1
  have hlowSqR : (candidate.lo : ℝ) ^ 2 ≤ (argument.lo : ℝ) := by
    have hmul : (candidate.lo : ℝ) * (candidate.lo : ℝ) ≤ (argument.lo : ℝ) := by
      exact_mod_cast hlowSq
    simpa [pow_two] using hmul
  have hlowSqX : (candidate.lo : ℝ) ^ 2 ≤ x := le_trans hlowSqR ha.1
  have hlo : (candidate.lo : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (le_of_lt hcan0R) hx0).2 hlowSqX
  have hcanHi0 : (0 : ℝ) ≤ (candidate.hi : ℝ) := by
    exact_mod_cast (le_trans (le_of_lt hcan0) hcanOrd)
  have hhighSqR : (argument.hi : ℝ) ≤ (candidate.hi : ℝ) ^ 2 := by
    have hmul : (argument.hi : ℝ) ≤ (candidate.hi : ℝ) * (candidate.hi : ℝ) := by
      exact_mod_cast hhighSq
    simpa [pow_two] using hmul
  have hxHi : x ≤ (candidate.hi : ℝ) ^ 2 := le_trans ha.2 hhighSqR
  have hhi : Real.sqrt x ≤ (candidate.hi : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨hcanHi0, hxHi⟩
  exact ⟨hlo, hhi⟩

#print axioms point_sound
#print axioms add_sound
#print axioms neg_sound
#print axioms sub_sound
#print axioms mul_sound
#print axioms reciprocal_sound
#print axioms divide_sound
#print axioms cube_sound_pos
#print axioms scale_sound_nonneg
#print axioms root_sound

end Thomson10Intervals

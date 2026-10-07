import IntervalSoundness

/- Real slope signs derived from the already checked rational certificates. -/
noncomputable section
namespace Thomson10Bounds
open Thomson10Arithmetic Thomson10Intervals Thomson10Family

def intervalA (t : Rat) (si : Thomson10Arithmetic.I) : Thomson10Arithmetic.I :=
  add (sub (point 2) si) (scale t (add (point 2) si))
def intervalB (t : Rat) (si : Thomson10Arithmetic.I) : Thomson10Arithmetic.I :=
  add (add (point 2) si) (scale t (sub (point 2) si))
def intervalSlope (t : Rat) (si qi ui vi wi : Thomson10Arithmetic.I) : Thomson10Arithmetic.I :=
  sub (sub
    (divide (add (add (point 1) (scale 2 si))
      (divide (scale 2 (add qi (point 2))) ui)) (cube qi))
    (divide (scale 4 (add (point 2) si)) (mul (intervalA t si) vi)))
    (divide (scale 4 (sub (point 2) si)) (mul (intervalB t si) wi))

theorem endpoint_real_enclosure (t : Rat) (si qi ui vi wi : Thomson10Arithmetic.I) (negative : Bool)
    (hc : EndpointChecks t [si, qi, ui, vi, wi] negative) :
    Contains (intervalSlope t si qi ui vi wi) (slope (t : ℝ)) := by
  dsimp [EndpointChecks] at hc
  rcases hc with ⟨ht0, ht1, hsB, hqB, huB, hvB, hwB, hden, haden, hbden, hsign⟩
  have hs : Contains si s := by
    simpa [s] using root_sound hsB (point_sound 2)
  have hq : Contains qi (q (t : ℝ)) := by
    have hx : Contains (point (1-t)) (1-(t : ℝ)) := by simpa using point_sound (1-t)
    simpa [q] using root_sound hqB hx
  have hu : Contains ui (u (t : ℝ)) := by
    have hx : Contains (add (point 1) qi) (1+q (t : ℝ)) := by
      simpa using add_sound (point_sound 1) hq
    simpa [u] using root_sound huB hx
  have ha : Contains (intervalA t si) (a (t : ℝ)) := by
    have hx := add_sound (sub_sound (point_sound 2) hs)
      (scale_sound (n := t) (add_sound (point_sound 2) hs))
    simpa [intervalA, a, mul_comm] using hx
  have hb : Contains (intervalB t si) (b (t : ℝ)) := by
    have hx := add_sound (add_sound (point_sound 2) hs)
      (scale_sound (n := t) (sub_sound (point_sound 2) hs))
    simpa [intervalB, b, mul_comm] using hx
  have hv : Contains vi (Real.sqrt (a (t : ℝ))) := root_sound hvB ha
  have hw : Contains wi (Real.sqrt (b (t : ℝ))) := root_sound hwB hb
  have hu0 : 0 < (ui.lo : ℝ) := by exact_mod_cast huB.2.2.1
  have hden0 : 0 < ((cube qi).lo : ℝ) := by exact_mod_cast hden
  have haden0 : 0 < ((mul (intervalA t si) vi).lo : ℝ) := by exact_mod_cast haden
  have hbden0 : 0 < ((mul (intervalB t si) wi).lo : ℝ) := by exact_mod_cast hbden
  have hsmallNumerator : Contains (scale 2 (add qi (point 2))) (2*(q (t : ℝ)+2)) := by
    simpa using scale_sound (n := 2) (add_sound hq (point_sound 2))
  have hsmall := divide_sound hsmallNumerator hu hu0
  have hs2 : Contains (scale 2 si) (2*s) := by simpa using scale_sound (n := 2) hs
  have hnum : Contains
      (add (add (point 1) (scale 2 si)) (divide (scale 2 (add qi (point 2))) ui))
      (1+2*s+2*(q (t : ℝ)+2)/u (t : ℝ)) := by
    simpa using add_sound (add_sound (point_sound 1) hs2) hsmall
  have hleading := divide_sound hnum (cube_sound hq) hden0
  have hnearNum : Contains (scale 4 (add (point 2) si)) (4*(2+s)) := by
    simpa using scale_sound (n := 4) (add_sound (point_sound 2) hs
      )
  have hfarNum : Contains (scale 4 (sub (point 2) si)) (4*(2-s)) := by
    simpa using scale_sound (n := 4) (sub_sound (point_sound 2) hs)
  have hnear := divide_sound hnearNum (mul_sound ha hv) haden0
  have hfar := divide_sound hfarNum (mul_sound hb hw) hbden0
  exact sub_sound (sub_sound hleading hnear) hfar

def sLeft : Thomson10Arithmetic.I := ⟨((176776695296636881 : Rat) / 125000000000000000), ((1414213562373095049 : Rat) / 1000000000000000000)⟩
def qLeft : Thomson10Arithmetic.I := ⟨((453137768785608953 : Rat) / 500000000000000000), ((906275537571217907 : Rat) / 1000000000000000000)⟩
def uLeft : Thomson10Arithmetic.I := ⟨((1380679375369682961 : Rat) / 1000000000000000000), ((1380679375369682963 : Rat) / 1000000000000000000)⟩
def vLeft : Thomson10Arithmetic.I := ⟨((68344991951837031 : Rat) / 62500000000000000), ((1093519871229392497 : Rat) / 1000000000000000000)⟩
def wLeft : Thomson10Arithmetic.I := ⟨((937932952191473659 : Rat) / 500000000000000000), ((1875865904382947319 : Rat) / 1000000000000000000)⟩
def sRight : Thomson10Arithmetic.I := ⟨((176776695296636881 : Rat) / 125000000000000000), ((1414213562373095049 : Rat) / 1000000000000000000)⟩
def qRight : Thomson10Arithmetic.I := ⟨((453137766027065989 : Rat) / 500000000000000000), ((906275532054131979 : Rat) / 1000000000000000000)⟩
def uRight : Thomson10Arithmetic.I := ⟨((1380679373371722381 : Rat) / 1000000000000000000), ((690339686685861191 : Rat) / 500000000000000000)⟩
def vRight : Thomson10Arithmetic.I := ⟨((546759943420255223 : Rat) / 500000000000000000), ((1093519886840510447 : Rat) / 1000000000000000000)⟩
def wRight : Thomson10Arithmetic.I := ⟨((234483238243040427 : Rat) / 125000000000000000), ((937932952972161709 : Rat) / 500000000000000000)⟩

theorem left_slope_negative : slope (tLeft : ℝ) < 0 := by
  have hc : EndpointChecks tLeft [sLeft, qLeft, uLeft, vLeft, wLeft] true := by
    simpa [sLeft, qLeft, uLeft, vLeft, wLeft, rootsLeft] using left_endpoint_arithmetic
  have enclosure := endpoint_real_enclosure tLeft sLeft qLeft uLeft vLeft wLeft true hc
  have negative : (intervalSlope tLeft sLeft qLeft uLeft vLeft wLeft).hi < 0 := by
    decide +kernel
  have negativeR : ((intervalSlope tLeft sLeft qLeft uLeft vLeft wLeft).hi : ℝ) < 0 := by
    exact_mod_cast negative
  exact lt_of_le_of_lt enclosure.2 negativeR

theorem right_slope_positive : 0 < slope (tRight : ℝ) := by
  have hc : EndpointChecks tRight [sRight, qRight, uRight, vRight, wRight] false := by
    simpa [sRight, qRight, uRight, vRight, wRight, rootsRight] using right_endpoint_arithmetic
  have enclosure := endpoint_real_enclosure tRight sRight qRight uRight vRight wRight false hc
  have positive : 0 < (intervalSlope tRight sRight qRight uRight vRight wRight).lo := by
    decide +kernel
  have positiveR : 0 < ((intervalSlope tRight sRight qRight uRight vRight wRight).lo : ℝ) := by
    exact_mod_cast positive
  exact lt_of_lt_of_le positiveR enclosure.1

#print axioms endpoint_real_enclosure
#print axioms left_slope_negative
#print axioms right_slope_positive
end Thomson10Bounds

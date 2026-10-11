import GeometryCore

noncomputable section
namespace Thomson10PairCut
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def pairLowerPolynomial (t : ℝ) : ℝ :=
  1701/2000 + (679/1250)*t + (709/2000)*((3*t^2-1)/2) +
  (603/5000)*((5*t^3-3*t)/2) + (111/1250)*((35*t^4-30*t^2+3)/8)

def distancePolynomial (s : ℝ) : ℝ :=
  1-(2447/1250)*s+(32183/20000)*s^3-(13737/16000)*s^5+
    (3711/16000)*s^7-(777/32000)*s^9

def bernstein9 (c : Fin 10 → ℝ) (x : ℝ) : ℝ :=
  c 0*(1-x)^9 + c 1*x*(1-x)^8 + c 2*x^2*(1-x)^7 +
  c 3*x^3*(1-x)^6 + c 4*x^4*(1-x)^5 + c 5*x^5*(1-x)^4 +
  c 6*x^6*(1-x)^3 + c 7*x^7*(1-x)^2 + c 8*x^8*(1-x) + c 9*x^9

theorem bernstein9_nonnegative (c : Fin 10 → ℝ) (hc : ∀ i, 0≤c i)
    {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) : 0≤bernstein9 c x := by
  have h0:=hc 0; have h1:=hc 1; have h2:=hc 2; have h3:=hc 3
  have h4:=hc 4; have h5:=hc 5; have h6:=hc 6; have h7:=hc 7
  have h8:=hc 8; have h9:=hc 9
  have hsub : 0≤1-x := sub_nonneg.mpr hx1
  unfold bernstein9
  positivity

theorem substituted_kernel_polynomial (s : ℝ) :
    1-s*pairLowerPolynomial (1-s^2/2)=distancePolynomial s := by
  unfold pairLowerPolynomial distancePolynomial
  ring


def boxCoefficients0 : Fin 10 → ℝ := ![(1 : ℝ), (359461/50000 : ℝ), (134461/6250 : ℝ), (44251810299/1280000000 : ℝ), (20632141297/640000000 : ℝ), (29110263003491/1638400000000 : ℝ), (2351933928291/409600000000 : ℝ), (2746236677554163/2621440000000000 : ℝ), (128855129707763/1310720000000000 : ℝ), (31292736493346771/8388608000000000000 : ℝ)]

theorem boxCoefficients0_nonnegative : ∀ k, 0≤boxCoefficients0 k := by
  intro k
  fin_cases k <;> norm_num [boxCoefficients0]

theorem box0_identity (s : ℝ) :
    distancePolynomial s=bernstein9 boxCoefficients0 ((s-(0 : ℝ))/((37/40 : ℝ)-(0 : ℝ))) := by
  norm_num [distancePolynomial, bernstein9, boxCoefficients0]
  ring

theorem box0_nonnegative {s : ℝ} (hlo : (0 : ℝ)≤s) (hhi : s≤(37/40 : ℝ)) :
    0≤distancePolynomial s := by
  rw [box0_identity]
  apply bernstein9_nonnegative _ boxCoefficients0_nonnegative
  · norm_num
    linarith
  · norm_num
    linarith


def boxCoefficients1 : Fin 10 → ℝ := ![(31292736493346771/8388608000000000000 : ℝ), (116700062414184299/6710886400000000000 : ℝ), (317160560559847/10737418240000000 : ℝ), (21427306248058863/1073741824000000000 : ℝ), (7429717816122541/1717986918400000000 : ℝ), (13155784736618029/1374389534720000000 : ℝ), (57125994831882027/2748779069440000000 : ℝ), (36251977309233271/2199023255552000000 : ℝ), (40817610105978007/7036874417766400000 : ℝ), (4350182989390751/5629499534213120000 : ℝ)]

theorem boxCoefficients1_nonnegative : ∀ k, 0≤boxCoefficients1 k := by
  intro k
  fin_cases k <;> norm_num [boxCoefficients1]

theorem box1_identity (s : ℝ) :
    distancePolynomial s=bernstein9 boxCoefficients1 ((s-(37/40 : ℝ))/((37/32 : ℝ)-(37/40 : ℝ))) := by
  norm_num [distancePolynomial, bernstein9, boxCoefficients1]
  ring

theorem box1_nonnegative {s : ℝ} (hlo : (37/40 : ℝ)≤s) (hhi : s≤(37/32 : ℝ)) :
    0≤distancePolynomial s := by
  rw [box1_identity]
  apply bernstein9_nonnegative _ boxCoefficients1_nonnegative
  · norm_num
    linarith
  · norm_num
    linarith


def boxCoefficients2 : Fin 10 → ℝ := ![(4350182989390751/5629499534213120000 : ℝ), (114123014310627781/14073748835532800000 : ℝ), (307446879730291919/8796093022208000000 : ℝ), (1751335674696020649/21990232555520000000 : ℝ), (2291094884764115837/21990232555520000000 : ℝ), (4371577070859014263/54975581388800000000 : ℝ), (2383612780159658487/68719476736000000000 : ℝ), (307019327943604741/34359738368000000000 : ℝ), (3516807055012515019/1717986918400000000000 : ℝ), (1894358156405597593/4294967296000000000000 : ℝ)]

theorem boxCoefficients2_nonnegative : ∀ k, 0≤boxCoefficients2 k := by
  intro k
  fin_cases k <;> norm_num [boxCoefficients2]

theorem box2_identity (s : ℝ) :
    distancePolynomial s=bernstein9 boxCoefficients2 ((s-(37/32 : ℝ))/((111/80 : ℝ)-(37/32 : ℝ))) := by
  norm_num [distancePolynomial, bernstein9, boxCoefficients2]
  ring

theorem box2_nonnegative {s : ℝ} (hlo : (37/32 : ℝ)≤s) (hhi : s≤(111/80 : ℝ)) :
    0≤distancePolynomial s := by
  rw [box2_identity]
  apply bernstein9_nonnegative _ boxCoefficients2_nonnegative
  · norm_num
    linarith
  · norm_num
    linarith


def boxCoefficients3 : Fin 10 → ℝ := ![(1894358156405597593/4294967296000000000000 : ℝ), (8390908736972139979/1073741824000000000000 : ℝ), (5394763438214284193/67108864000000000000 : ℝ), (7410640479453699039/16777216000000000000 : ℝ), (11273517219117978439/8388608000000000000 : ℝ), (4941638117494566413/2097152000000000000 : ℝ), (622913257298843757/262144000000000000 : ℝ), (84059156247718651/65536000000000000 : ℝ), (18870358695661217/65536000000000000 : ℝ), (5853130395571/16384000000000000 : ℝ)]

theorem boxCoefficients3_nonnegative : ∀ k, 0≤boxCoefficients3 k := by
  intro k
  fin_cases k <;> norm_num [boxCoefficients3]

theorem box3_identity (s : ℝ) :
    distancePolynomial s=bernstein9 boxCoefficients3 ((s-(111/80 : ℝ))/((37/20 : ℝ)-(111/80 : ℝ))) := by
  norm_num [distancePolynomial, bernstein9, boxCoefficients3]
  ring

theorem box3_nonnegative {s : ℝ} (hlo : (111/80 : ℝ)≤s) (hhi : s≤(37/20 : ℝ)) :
    0≤distancePolynomial s := by
  rw [box3_identity]
  apply bernstein9_nonnegative _ boxCoefficients3_nonnegative
  · norm_num
    linarith
  · norm_num
    linarith


theorem distance_polynomial_nonnegative {s : ℝ} (hs0 : 0≤s) (hs1 : s≤37/20) :
    0≤distancePolynomial s := by
  by_cases h0 : s≤37/40
  · exact box0_nonnegative hs0 h0
  · by_cases h1 : s≤37/32
    · exact box1_nonnegative (le_of_lt (lt_of_not_ge h0)) h1
    · by_cases h2 : s≤111/80
      · exact box2_nonnegative (le_of_lt (lt_of_not_ge h1)) h2
      · exact box3_nonnegative (le_of_lt (lt_of_not_ge h2)) hs1

theorem pair_kernel_underbound {s : ℝ} (hs0 : 0<s) (hs1 : s≤37/20) :
    pairLowerPolynomial (1-s^2/2)≤1/s := by
  apply (le_div_iff₀ hs0).2
  have h:=distance_polynomial_nonnegative (le_of_lt hs0) hs1
  rw [← substituted_kernel_polynomial] at h
  nlinarith

theorem pair_cut_objective_exact :
    45*(1701/2000 : ℝ)-5*(679/1250+709/2000+603/5000+111/1250)=32737/1000 := by
  norm_num

#print axioms distance_polynomial_nonnegative
#print axioms pair_kernel_underbound
#print axioms pair_cut_objective_exact
end Thomson10PairCut

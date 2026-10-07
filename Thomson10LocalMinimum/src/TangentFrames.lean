import StationarityGeometryCore
import TangentFrameCore

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry

theorem configuration_tangent_expansion {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i : Fin 10) (v : R3) (ht : dot3 (configuration h i) v=0) :
    v=dot3 (meridianFrame h i) v • meridianFrame h i+
      dot3 (azimuthFrame h i) v • azimuthFrame h i := by
  have hn : (geoQ h)^2+h^2=1 := by nlinarith [geoQ_sq hh0 hh1]
  have hnn : (geoQ h)^2+(-h)^2=1 := by nlinarith [geoQ_sq hh0 hh1]
  have ha : (1/geoS)^2+(1/geoS)^2=(1:ℝ) := by nlinarith [inverse_geoS_sq]
  fin_cases i
  · have hv : v 2=0 := by
      simp [configuration,north,vec3,dot3] at ht
      exact ht
    funext k
    fin_cases k <;> simp [meridianFrame,azimuthFrame,vec3,dot3,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hv]
  · have hv : v 2=0 := by
      simp [configuration,south,vec3,dot3] at ht
      linarith
    funext k
    fin_cases k <;> simp [meridianFrame,azimuthFrame,vec3,dot3,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hv]
  · have ht' : dot3 (vec3 (geoQ h*(1)) (geoQ h*(0)) h) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) h (1) (0) v hn
      (by norm_num) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he
  · have ht' : dot3 (vec3 (geoQ h*(-1)) (geoQ h*(0)) h) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) h (-1) (0) v hn
      (by norm_num) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he
  · have ht' : dot3 (vec3 (geoQ h*(0)) (geoQ h*(1)) h) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) h (0) (1) v hn
      (by norm_num) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he
  · have ht' : dot3 (vec3 (geoQ h*(0)) (geoQ h*(-1)) h) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) h (0) (-1) v hn
      (by norm_num) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he
  · have ht' : dot3 (vec3 (geoQ h*(1/geoS)) (geoQ h*(1/geoS)) (-h)) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) (-h) (1/geoS) (1/geoS) v hnn
      (by simpa only [neg_div,neg_sq] using ha) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he
  · have ht' : dot3 (vec3 (geoQ h*(1/geoS)) (geoQ h*(-1/geoS)) (-h)) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) (-h) (1/geoS) (-1/geoS) v hnn
      (by simpa only [neg_div,neg_sq] using ha) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he
  · have ht' : dot3 (vec3 (geoQ h*(-1/geoS)) (geoQ h*(1/geoS)) (-h)) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) (-h) (-1/geoS) (1/geoS) v hnn
      (by simpa only [neg_div,neg_sq] using ha) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he
  · have ht' : dot3 (vec3 (geoQ h*(-1/geoS)) (geoQ h*(-1/geoS)) (-h)) v=0 := by
      simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using ht
    have he := radial_tangent_expansion (geoQ h) (-h) (-1/geoS) (-1/geoS) v hnn
      (by simpa only [neg_div,neg_sq] using ha) ht'
    simpa [configuration,meridianFrame,azimuthFrame,north,south,upperXPlus,upperXMinus,upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,div_eq_mul_inv,mul_comm] using he

#print axioms configuration_tangent_expansion
end Thomson10Stability

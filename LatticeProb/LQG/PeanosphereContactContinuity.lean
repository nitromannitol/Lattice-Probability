import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiContinuity

/-! # Continuity of Peanosphere contact images -/

set_option autoImplicit false

open Set

namespace MatedCRTHarmonic.RouteM

/-- The image of the last left-contour contact varies continuously with its
level below the contour at the fixed time. -/
theorem Peanosphere.continuousOn_eta_ellMinus {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (t : ℝ) :
    ContinuousOn (fun level => η (ellMinus ω t level)) (Iio (lCoord ω t)) := by
  have hc : Continuous (fun level : ℝ =>
      shearedStripMap P (stripPoint t (level - lCoord ω t))) :=
    (shearedStripMap_continuous P).comp
      (continuous_stripPoint_pair.comp (continuous_const.prodMk (continuous_id.sub continuous_const)))
  apply hc.continuousOn.congr
  intro level hlevel
  change level < lCoord ω t at hlevel
  have hneg : level - lCoord ω t < 0 := sub_neg.mpr hlevel
  simp only [shearedStripMap, stripPoint, 
    not_le_of_gt hneg, false_and, ite_false, hneg, ite_true]
  congr 2
  ring

/-- The image of the last right-contour contact varies continuously with its
level below the contour at the fixed time. -/
theorem Peanosphere.continuousOn_eta_rhoMinus {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (t : ℝ) :
    ContinuousOn (fun level => η (rhoMinus ω t level)) (Iio (rCoord ω t)) := by
  have hc : Continuous (fun level : ℝ =>
      shearedStripMap P (stripPoint t (1 + rCoord ω t - level))) :=
    (shearedStripMap_continuous P).comp
      (continuous_stripPoint_pair.comp (continuous_const.prodMk ((continuous_const.add continuous_const).sub continuous_id)))
  apply hc.continuousOn.congr
  intro level hlevel
  change level < rCoord ω t at hlevel
  have hpos : 0 ≤ 1 + rCoord ω t - level := by linarith
  have hlarge : ¬1 + rCoord ω t - level ≤ 1 := by linarith
  have hnonneg : ¬1 + rCoord ω t - level < 0 := not_lt_of_ge hpos
  simp only [shearedStripMap, stripPoint, 
    hlarge, and_false, ite_false, hnonneg]
  congr 2
  ring

end MatedCRTHarmonic.RouteM

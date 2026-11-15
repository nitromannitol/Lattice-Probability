import LatticeProb.Prob.CorrelatedBMWedgeSquare
import LatticeProb.Prob.KilledHeatSquarePositive

/-! # Positive Brownian survival in a symmetric wedge -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT LQGMetric.HeatSq LQGMetric.KilledHeat

namespace LatticeProb.CorrelatedBM

/-- The killed heat kernel of a strict symmetric wedge has positive total mass. -/
theorem lintegral_killedHeat_complexSymmetricWedge_pos {a b q : ℝ}
    (ha : 0 < a) (hq : 0 < q) {t : ℝ≥0} (ht : t ≠ 0) :
    0 < ∫⁻ w, ENNReal.ofReal
      (killedHeat (complexSymmetricWedge a b) t (q / a : ℝ) w) := by
  let r := q / (2 * (a + |b| + 1))
  let Q := sqOpen (-r) (2 * r)
  let c : ℂ := (q / a : ℝ)
  have hQ := translated_sqOpen_subset_complexSymmetricWedge (b := b) ha hq
  have hr : 0 < r := hQ.1
  have h0 : (0 : ℂ) ∈ Q := by
    simp only [Q, sqOpen, mem_ofPred_eq, Complex.zero_re, Complex.zero_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hp := LQGMetric.KilledHeatSq.lintegral_killedHeat_sqOpen_pos
    (a := -r) (L := 2 * r) (by positivity) h0 ht
  let V : Set ℂ := {v | v - c ∈ Q}
  have hV : V ⊆ complexSymmetricWedge a b := hQ.2
  have hm : Measurable (fun w : ℂ => ENNReal.ofReal (killedHeat V t c w)) :=
    (measurable_killedHeat_right (by
      dsimp [V]
      exact (isOpen_sqOpen (-r) (2 * r)).preimage (continuous_id.sub continuous_const)) ht c).ennreal_ofReal
  have htrans : (∫⁻ w, ENNReal.ofReal (killedHeat V t c w)) =
      ∫⁻ w, ENNReal.ofReal (killedHeat Q t 0 w) := by
    calc
      _ = ∫⁻ w, ENNReal.ofReal (killedHeat V t c (w + c)) := by
        have h := lintegral_map (μ := (volume : Measure ℂ)) (g := fun w : ℂ => w + c)
          hm (by fun_prop)
        rw [map_add_right_eq_self] at h
        exact h
      _ = _ := by
        apply lintegral_congr
        intro w
        congr 1
        simpa only [zero_add] using killedHeat_translate Q t c 0 w
  have hle : (∫⁻ w, ENNReal.ofReal (killedHeat V t c w)) ≤
      ∫⁻ w, ENNReal.ofReal (killedHeat (complexSymmetricWedge a b) t c w) :=
    lintegral_mono fun w => ENNReal.ofReal_le_ofReal (killedHeat_mono hV t c w)
  rw [htrans] at hle
  exact lt_of_lt_of_le hp hle

/-- A strict symmetric wedge has positive Brownian survival probability at positive time. -/
theorem measure_openSymmetricWedgeBarrier_pos {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) {a b q : ℝ}
    (ha : 0 < a) (hq : 0 < q) {T : ℝ≥0} (hT : T ≠ 0) :
    0 < μ (openSymmetricWedgeBarrier a b q T) := by
  rw [measure_openSymmetricWedgeBarrier_eq_lintegral_killedHeat hμ a b q ha.ne' T hT]
  exact lintegral_killedHeat_complexSymmetricWedge_pos ha hq hT

/-- The same positivity holds for a whitened correlated Brownian pair. -/
theorem measure_openSymmetricWedgeBarrier_whitened_pos
    {γ : ℝ} {μ : Measure Path2} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsCorrelatedBM2 γ μ) (r : ℝ) {a b q : ℝ}
    (ha : 0 < a) (hq : 0 < q) {T : ℝ≥0} (hT : T ≠ 0) :
    0 < (μ.map (whitenAt γ r)) (openSymmetricWedgeBarrier a b q T) :=
  measure_openSymmetricWedgeBarrier_pos (isCorrelatedBM2_map_whitenAt hγ0 hγ2 r hμ) ha hq hT

end LatticeProb.CorrelatedBM

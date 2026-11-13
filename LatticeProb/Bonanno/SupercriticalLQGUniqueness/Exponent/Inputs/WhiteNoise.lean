/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Inputs.WhiteNoise at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Up0
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2




 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Exponent.Inputs.WhiteNoise
open LQGMetric LQGMetric.WhiteNoise LQGMetric.DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 
theorem square_crossing_pos_finite {ξ : ℝ} {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) :
    0 < lenObs ξ Y (rectAB 1 1) ω ∧
      rectLen ξ (fun x => Y x ω) (rectAB 1 1) ≠ ⊤ := by
  constructor
  · exact lenObs_pos hYc (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (by norm_num [rectAB, MarkedRect.crossWidth]) ω
  · exact rectLen_ne_top (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (hYc ω)

 
theorem square_quantile_closed_right {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ P {ω | lenObs ξ Y (rectAB 1 1) ω ≤ ellQ ξ P Y (rectAB 1 1) p} := by
  letI := hW.isProbabilityMeasure
  exact prob_le_ellQ hYc hYm (rectAB 1 1) hp0 hp1

 
theorem square_quantile_pos {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < ellQ ξ P Y (rectAB 1 1) p := by
  letI := hW.isProbabilityMeasure
  let L : Ω → ℝ := lenObs ξ Y (rectAB 1 1)
  have hLm : Measurable L := measurable_lenObs hYc hYm (rectAB 1 1)
  have h0 : P {ω | L ω ≤ 0} = 0 := by
    have e : {ω | L ω ≤ 0} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (square_crossing_pos_finite hYc ω).1
    simp only [e, measure_empty]
  by_contra hq
  have hq0 : ellQ ξ P Y (rectAB 1 1) p ≤ 0 := le_of_not_gt hq
  have h := (le_measure_Iic_iff_lowerQuantile_le (μ := P.map L) hp0 hp1).2 hq0
  rw [Measure.map_apply hLm measurableSet_Iic] at h
  change p ≤ P {ω | L ω ≤ 0} at h
  rw [h0] at h
  exact (not_le.mpr hp0) h

 
theorem square_quantile_strict_left {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    P {ω | lenObs ξ Y (rectAB 1 1) ω < ellQ ξ P Y (rectAB 1 1) p} ≤ p := by
  letI := hW.isProbabilityMeasure
  have h := prob_ge_ellQ (ξ := ξ) (Y := Y) (P := P) hYc hYm (rectAB 1 1) hp0 hp1
  have hm : MeasurableSet {ω | ellQ ξ P Y (rectAB 1 1) p ≤
      lenObs ξ Y (rectAB 1 1) ω} :=
    measurableSet_le measurable_const (measurable_lenObs hYc hYm (rectAB 1 1))
  have e : {ω | lenObs ξ Y (rectAB 1 1) ω < ellQ ξ P Y (rectAB 1 1) p} =
      {ω | ellQ ξ P Y (rectAB 1 1) p ≤ lenObs ξ Y (rectAB 1 1) ω}ᶜ := by
    ext ω; simp
  rw [e, prob_compl_eq_one_sub hm]
  calc 1 - P {ω | ellQ ξ P Y (rectAB 1 1) p ≤ lenObs ξ Y (rectAB 1 1) ω}
      ≤ 1 - (1 - p) := tsub_le_tsub_left h 1
    _ = p := ENNReal.sub_sub_cancel ENNReal.one_ne_top hp1.le

 
theorem dyadic_square_quantile {ξ : ℝ} (hW : IsWhiteNoise P W) (n : ℕ)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < ellN ξ W P n p ∧
      P {ω | lenMN ξ W P 1 1 0 n ω < ellN ξ W P n p} ≤ p ∧
      p ≤ P {ω | lenMN ξ W P 1 1 0 n ω ≤ ellN ξ W P n p} := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  change 0 < ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) p ∧
    P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω <
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) p} ≤ p ∧
    p ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) p}
  exact ⟨square_quantile_pos hW hφ.cont hφ.meas hp0 hp1,
    square_quantile_strict_left hW hφ.cont hφ.meas hp0 hp1,
    square_quantile_closed_right hW hφ.cont hφ.meas hp0 hp1⟩

 
end SupercriticalLQGUniqueness.Exponent.Inputs.WhiteNoise

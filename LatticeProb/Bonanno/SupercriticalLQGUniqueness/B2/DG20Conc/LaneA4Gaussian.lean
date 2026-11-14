/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4Gaussian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L9Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Straight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.HitExponent

 








set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA4_truncated_exp_pointwise {ξ t a x : ℝ}
    (ht : t ≤ ξ) (ha : x ≤ a) :
    Real.exp (ξ * x) ≤ Real.exp ((ξ - t) * a) * Real.exp (t * x) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ha)])

 
theorem laneA4_tilt_exponent (ξ β : ℝ) :
    let t := min ξ β
    (ξ - t) * β + t ^ 2 / 2 =
      ξ * (min ξ β) - (min ξ β) ^ 2 / 2 := by
  dsimp
  by_cases h : ξ ≤ β
  · rw [min_eq_left h]
    ring
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
    ring

 


theorem laneA4_truncated_gaussian_upper
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal 0 v) P) (hXm : Measurable X)
    (ξ β : ℝ) :
    ∫⁻ ω in {ω | X ω ≤ β * (v : ℝ)},
        ENNReal.ofReal (Real.exp (ξ * X ω)) ∂P ≤
      ENNReal.ofReal (Real.exp
        ((ξ * min ξ β - (min ξ β) ^ 2 / 2) * (v : ℝ))) := by
  let t := min ξ β
  have ht : t ≤ ξ := min_le_left _ _
  have hv : 0 ≤ (v : ℝ) := v.property
  have hmoment :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P) ≤
        ENNReal.ofReal (Real.exp ((v : ℝ) * t ^ 2 / 2)) := by
    have hsqrt : (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) := Real.sq_sqrt hv
    simpa only [hsqrt] using
      (LQGMetric.DDDF.lintegral_exp_gauss_le hX (σ := Real.sqrt (v : ℝ))
        (by rw [hsqrt]) t)
  have hpoint : ∀ ω ∈ {ω | X ω ≤ β * (v : ℝ)},
      ENNReal.ofReal (Real.exp (ξ * X ω)) ≤
      ENNReal.ofReal (Real.exp ((ξ - t) * (β * (v : ℝ)))) *
        ENNReal.ofReal (Real.exp (t * X ω)) := by
    intro ω hω
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (laneA4_truncated_exp_pointwise ht hω)
  have hE : MeasurableSet {ω | X ω ≤ β * (v : ℝ)} :=
    measurableSet_le hXm measurable_const
  calc
    ∫⁻ ω in {ω | X ω ≤ β * (v : ℝ)},
        ENNReal.ofReal (Real.exp (ξ * X ω)) ∂P ≤
      ∫⁻ ω in {ω | X ω ≤ β * (v : ℝ)},
        ENNReal.ofReal (Real.exp ((ξ - t) * (β * (v : ℝ)))) *
          ENNReal.ofReal (Real.exp (t * X ω)) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE] with ω hω
      exact hpoint ω hω
    _ = ENNReal.ofReal (Real.exp ((ξ - t) * (β * (v : ℝ)))) *
      ∫⁻ ω in {ω | X ω ≤ β * (v : ℝ)},
        ENNReal.ofReal (Real.exp (t * X ω)) ∂P := by
      rw [lintegral_const_mul _ (hXm.const_mul t |>.exp.ennreal_ofReal)]
    _ ≤ ENNReal.ofReal (Real.exp ((ξ - t) * (β * (v : ℝ)))) *
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (Set.subset_univ {ω | X ω ≤ β * (v : ℝ)}) :
          (∫⁻ ω in {ω | X ω ≤ β * (v : ℝ)},
            ENNReal.ofReal (Real.exp (t * X ω)) ∂P) ≤
          ∫⁻ ω in Set.univ,
            ENNReal.ofReal (Real.exp (t * X ω)) ∂P)
    _ ≤ ENNReal.ofReal (Real.exp ((ξ - t) * (β * (v : ℝ)))) *
      ENNReal.ofReal (Real.exp ((v : ℝ) * t ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hmoment bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 1
      dsimp [t]
      rw [← laneA4_tilt_exponent ξ β]
      ring

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneA4_coarse_phi_truncated_upper
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (K : ℕ) (x : ℂ) (ξ β : ℝ) :
    ∫⁻ ω in {ω | phiMN W P 0 K x ω ≤
      β * ((K : ℝ) * Real.log 2)},
      ENNReal.ofReal (Real.exp
        (ξ * phiMN W P 0 K x ω)) ∂P ≤
      ENNReal.ofReal (Real.exp
        ((ξ * min ξ β - (min ξ β) ^ 2 / 2) *
          ((K : ℝ) * Real.log 2))) := by
  obtain ⟨v, hv, hLaw⟩ := hasLaw_phiMN hW K x
  have hMeas := (isPhiVersion_phiMN hW (Nat.zero_le K)).meas x
  simpa only [hv] using laneA4_truncated_gaussian_upper hLaw hMeas ξ β

end SupercriticalLQGUniqueness.B2.DG20Conc

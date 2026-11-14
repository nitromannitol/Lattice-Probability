/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianBoundaryOscillation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNestedConfinement
import LatticeProb.Bonanno.BouRabeeGwynne.BoundarySurvivalScales
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppingOscillation
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianInnerExit

/-! Uniform control of the original Brownian path between its inner and
outer boundary approaches, including an immediate inner exit. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

theorem HasLipschitzBoundary.uniform_brownian_outer_range {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Euc d)} (hL : HasLipschitzBoundary U) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ a > 0, ∀ p ∈ frontier U, ∀ x ∈ U, dist x p ≤ a →
      ∀ δ : ℝ, 0 < δ → δ ≤ a →
        μ {ω | stoppedBrownianRepresentative (thickening δ U) x ω ∉
          curveRangeEvent (closedBall x η)} ≤ ENNReal.ofReal ε := by
  obtain ⟨s, hs, κ, hκ, q, R, hq, hqone, hR, hsurvive⟩ :=
    hL.uniform_brownian_excursion_survival hd hU hUb μ hμ
  obtain ⟨N, hN, r, hr, a, ha, har, hscale, hsize, hsmall, hqN⟩ :=
    exists_boundary_survival_scales hq hqone hR hs hκ hη hε
  refine ⟨a, ha, ?_⟩
  intro p hp x hx hxp δ hδ hδa
  have hxr : dist x p ≤ (r : ℝ) := hxp.trans har
  have hrR : 0 < (r : ℝ) := hr
  have hsize' : R * ((r : ℝ) * R ^ (N - 1)) + dist x p ≤ η :=
    (add_le_add le_rfl hxr).trans hsize
  apply (brownian_outer_exit_range_bad_le_of_step hd μ hμ U hUb p hrR hR hxr δ
    (self_subset_thickening hδ U hx) N hN η hsize' (ENNReal.ofReal q) ?_).trans hqN
  intro i hi y hy
  have hpos : 0 < (r : ℝ) * R ^ i := mul_pos hrR (pow_pos (lt_trans zero_lt_one hR) i)
  have hbase : (r : ℝ) ≤ (r : ℝ) * R ^ i :=
    le_mul_of_one_le_right hrR.le (one_le_pow₀ hR.le)
  have hδsmall : δ < κ * ((r : ℝ) * R ^ i) / 2 :=
    (hδa.trans_lt hsmall).trans_le
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hκ.le) (by norm_num))
  exact hsurvive p hp ⟨(r : ℝ) * R ^ i, hpos.le⟩ hpos (hscale i hi) y δ hy
    hδsmall

theorem HasLipschitzBoundary.uniform_brownian_boundary_oscillation {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Euc d)} (hL : HasLipschitzBoundary U) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ a > 0, ∀ b : ℝ, 0 < b → b ≤ a → ∀ δ : ℝ, 0 < δ → δ ≤ a →
      ∀ z ∈ U,
        μ {ω | ∃ s ∈ Icc (continuousExitTime (innerDomain U b) z ω).toNNReal
            (continuousExitTime (thickening δ U) z ω).toNNReal,
          ∃ t ∈ Icc (continuousExitTime (innerDomain U b) z ω).toNNReal
            (continuousExitTime (thickening δ U) z ω).toNNReal,
            η < dist (z + ω s) (z + ω t)} ≤ ENNReal.ofReal ε := by
  obtain ⟨a, ha, hconfinement⟩ :=
    hL.uniform_brownian_outer_range hd hU hUb μ hμ (half_pos hη) hε
  refine ⟨a, ha, ?_⟩
  intro b hb hba δ hδ hδa z hz
  let τ := continuousExitTime (innerDomain U b) z
  have hτ := isStoppingTime_continuousExitTime (isOpen_innerDomain U b) z
  have hinner : innerDomain U b ⊆ U :=
    subset_closure.trans (closure_innerDomain_subset U hb)
  have hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞ :=
    standardBrownianLaw_ae_finiteExit hd hμ (hUb.subset hinner) z
  have hnest : innerDomain U b ⊆ thickening δ U :=
    hinner.trans (self_subset_thickening hδ U)
  have hnext (ω : BrownianPath d) :
      brownianNextExitTime (thickening δ U) z τ ω =
        continuousExitTime (thickening δ U) z ω :=
    brownianNextExitTime_from_nested_exit hnest z ω
  have hnextfinite : ∀ᵐ ω ∂μ, brownianNextExitTime (thickening δ U) z τ ω ≠ ∞ := by
    filter_upwards [standardBrownianLaw_ae_finiteExit hd hμ
      (show Bornology.IsBounded (thickening δ U) from hUb.thickening) z] with ω hω
    simpa only [hnext] using hω
  have hbound : ∀ᵐ ω ∂μ,
      μ {γ | ¬ ∀ u : unitInterval,
        dist (stoppedBrownianRepresentative (thickening δ U) (z + ω (τ ω).toNNReal) γ u)
          (z + ω (τ ω).toNNReal) ≤ η / 2} ≤ ENNReal.ofReal ε := by
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ, hfinite] with ω hzero hω
    have hx := (innerExit_position hb hz hzero hω).1
    obtain ⟨p, hp, hxp⟩ := innerExit_exists_frontier_near hd hUb hb hz hzero hω
    exact hconfinement p hp _ hx (hxp.trans hba) δ hδ hδa
  have h := standardBrownianLaw_stopping_oscillation_le hμ isOpen_thickening z hτ
    hfinite hnextfinite (η / 2) (ENNReal.ofReal ε) hbound
  dsimp only [τ] at hnext
  simpa only [hnext, show 2 * (η / 2) = η by ring] using h

end BouRabeeGwynne

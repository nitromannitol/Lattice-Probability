import LatticeProb.LQG.ConeCouplingScaleTail

/-! # Inner window escape from mass bounds -/

set_option autoImplicit false

open MeasureTheory Set Metric MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal

namespace LatticeProb

/-- If a set has less mass than a half-window, both half-window traces of a
mass-parametrized curve escape that set. -/
theorem half_window_traces_not_subset_of_measure_lt
    {E : Type*} [MeasurableSpace E] (μ : Measure E) (η : ℝ → E)
    (hparam : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    {w : ℝ} (hw : 0 ≤ w) (A : Set E)
    (hsmall : μ A < ENNReal.ofReal (w / 2)) :
    ¬ η '' Icc (0 - w / 2) 0 ⊆ A ∧ ¬ η '' Icc 0 (0 + w / 2) ⊆ A := by
  have hh : 0 ≤ w / 2 := by positivity
  constructor
  · intro hsub
    have hm : μ (η '' Icc (0 - w / 2) 0) ≤ μ A := measure_mono hsub
    rw [hparam _ _ (by linarith)] at hm
    simp only [zero_sub, neg_neg] at hm
    exact (not_le_of_gt hsmall) hm
  · intro hsub
    have hm : μ (η '' Icc 0 (0 + w / 2)) ≤ μ A := measure_mono hsub
    rw [hparam _ _ (by linarith)] at hm
    simp only [zero_add, sub_zero] at hm
    exact (not_le_of_gt hsmall) hm

/-- For any almost-sure cone-area limit, the probability that either inner
half-window stays inside a cone-scale ball is bounded by its mass tail. -/
theorem measure_cone_inner_window_containment_le_mass_tail
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (b w : ℝ) (hw : 0 ≤ w) :
    P {ω | let L := CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b
      η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
        η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L} ≤
    P {ω | ENNReal.ofReal (w / 2) ≤ μ ω (ball 0
      (CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b))} := by
  apply measure_mono_ae
  filter_upwards [D.areaParam, hμ] with ω ha hlim hwindow
  by_contra hmass
  have hsmall := lt_of_not_ge hmass
  have hescape := half_window_traces_not_subset_of_measure_lt (μ ω) (η ω)
    (ha.2 (μ ω) hlim) hw _ hsmall
  exact hwindow.elim hescape.1 hescape.2

end LatticeProb

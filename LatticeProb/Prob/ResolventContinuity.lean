/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.ResolventExit
import LatticeProb.Prob.ExitTimeSmall
import LatticeProb.Prob.TVIntegralBound

/-!
# Strong Feller property of the resolvent of a continuous Markov path family

Let `K : E → Prob C(ℝ≥0, E)` be a weakly continuous family of path laws with the Markov property
at deterministic times, `f` a bounded measurable function and `λ > 0`.  The resolvent
`R f (u) = ∫ ∫₀^∞ e^{-λ t} f (x_t) dt d(K u)(x)` is continuous at `z` whenever

* `K z`-almost every path starts at `z` and is nonconstant on every initial interval, and
* the law of the exit point from every ball `B (z, δ)` depends continuously on the starting point
  in total variation, in the sense that for each `δ, ε > 0` and all `w` near `z` the exit laws from
  `z` and from `w` differ by at most `ε` on every measurable set.

* `continuousAt_pathResolvent`: the statement.  The proof reads the resolvent at the exit time of
  a small ball (strong Markov property), uses that the exit time is small uniformly near `z`, and
  controls the difference of the exit-point integrals by total variation.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- **Strong Feller continuity of the resolvent.**  See the module docstring for the hypotheses. -/
theorem continuousAt_pathResolvent {E : Type*} [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {K : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hMk : ∀ v t, MarkovAt K v t) {z : E}
    (hstart : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), x 0 = z)
    (hnc : ∀ ε : ℝ≥0, 0 < ε → ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ∃ s ≤ ε, x s ≠ x 0)
    (hexit : ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 z, ∀ A : Set E, MeasurableSet A →
      |((K z : Measure C(ℝ≥0, E)) {x | x (pathHit (Metric.ball z δ)ᶜ x).toNNReal ∈ A}).toReal -
        ((K w : Measure C(ℝ≥0, E)) {x | x (pathHit (Metric.ball z δ)ᶜ x).toNNReal ∈ A}).toReal| ≤ ε)
    {f : E → ℝ} (hf : Measurable f) {M lam : ℝ} (hlam : 0 < lam) (hM : ∀ e, |f e| ≤ M) :
    ContinuousAt (pathResolvent K lam f) z := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM z)
  set B : ℝ := M / lam with hBdef
  have hB0 : 0 ≤ B := div_nonneg hM0 hlam.le
  have hgm : Measurable (pathResolvent K lam f) := measurable_pathResolvent hK hf lam
  have hgB : ∀ u, |pathResolvent K lam f u| ≤ B := abs_pathResolvent_le (K := K) hlam hM
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- the parameters
  set r : ℝ≥0 := Real.toNNReal (ε / (16 * (M + 1))) with hrdef
  have hrpos' : 0 < ε / (16 * (M + 1)) := div_pos hε (by linarith)
  have hr : 0 < r := Real.toNNReal_pos.2 hrpos'
  have hrR : (r : ℝ) = ε / (16 * (M + 1)) := Real.coe_toNNReal _ hrpos'.le
  have hr0 : (0 : ℝ) ≤ r := r.2
  have hr_eq : (16 * (M + 1)) * (r : ℝ) = ε := by
    rw [hrR]; field_simp
  set η0 : ℝ := ε / (16 * (B + 1)) with hη0def
  have hη0 : 0 < η0 := div_pos hε (by linarith)
  have hη0_eq : (16 * (B + 1)) * η0 = ε := by
    rw [hη0def]; field_simp
  set ε2 : ℝ := ε / (8 * (B + 1)) with hε2def
  have hε2 : 0 < ε2 := div_pos hε (by linarith)
  have hε2_eq : (8 * (B + 1)) * ε2 = ε := by
    rw [hε2def]; field_simp
  obtain ⟨δ, hδ, hev1⟩ := exists_radius_eventually_measure_pathHit_gt_lt hK hstart hnc hr
    (η := ENNReal.ofReal η0) (ENNReal.ofReal_pos.2 hη0)
  have hev2 := hexit δ hδ ε2 hε2
  -- the exit time of the ball
  set σ : C(ℝ≥0, E) → ℝ≥0∞ := pathHit (Metric.ball z δ)ᶜ with hσdef
  have hF : IsClosed (Metric.ball z δ)ᶜ := Metric.isOpen_ball.isClosed_compl
  have hσ : IsStoppingTime (stoppedPathFiltration (E := E)) σ := isStoppingTime_pathHit hF
  have hstop : ∀ x, σ x < ⊤ → σ (stopPath x (σ x).toNNReal) = σ x := fun x hx =>
    pathHit_stopPath hF hx
  have hσm : Measurable σ := measurable_of_isStoppingTime_stoppedPath hσ
  have ham : Measurable fun x : C(ℝ≥0, E) => (σ x).toNNReal := hσm.ennreal_toNNReal
  have hev : Continuous fun q : C(ℝ≥0, E) × ℝ≥0 => q.1 q.2 := ContinuousEval.continuous_eval
  have hYm : Measurable fun x : C(ℝ≥0, E) => x (σ x).toNNReal :=
    hev.measurable.comp (measurable_id.prodMk ham)
  have hz1 := hev1.self_of_nhds
  have tz : ((K z : Measure C(ℝ≥0, E)) {x | (r : ℝ≥0∞) < σ x}).toReal < η0 :=
    ENNReal.toReal_lt_of_lt_ofReal hz1
  filter_upwards [hev1, hev2] with w hw1 hw2
  have tw : ((K w : Measure C(ℝ≥0, E)) {x | (r : ℝ≥0∞) < σ x}).toReal < η0 :=
    ENNReal.toReal_lt_of_lt_ofReal hw1
  have Hz := abs_pathResolvent_sub_exit_le hK (hMk z) hσ hstop hf hlam hM r
  have Hw := abs_pathResolvent_sub_exit_le hK (hMk w) hσ hstop hf hlam hM r
  have hmid : |∫ x, pathResolvent K lam f (x (σ x).toNNReal) ∂(K z : Measure C(ℝ≥0, E)) -
      ∫ x, pathResolvent K lam f (x (σ x).toNNReal) ∂(K w : Measure C(ℝ≥0, E))| ≤ 2 * B * ε2 := by
    have e1 : ∫ x, pathResolvent K lam f (x (σ x).toNNReal) ∂(K z : Measure C(ℝ≥0, E)) =
        ∫ y, pathResolvent K lam f y ∂((K z : Measure C(ℝ≥0, E)).map fun x => x (σ x).toNNReal) :=
      (integral_map hYm.aemeasurable hgm.aestronglyMeasurable).symm
    have e2 : ∫ x, pathResolvent K lam f (x (σ x).toNNReal) ∂(K w : Measure C(ℝ≥0, E)) =
        ∫ y, pathResolvent K lam f y ∂((K w : Measure C(ℝ≥0, E)).map fun x => x (σ x).toNNReal) :=
      (integral_map hYm.aemeasurable hgm.aestronglyMeasurable).symm
    rw [e1, e2]
    have : IsProbabilityMeasure ((K z : Measure C(ℝ≥0, E)).map fun x => x (σ x).toNNReal) :=
      (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).2 inferInstance
    have : IsProbabilityMeasure ((K w : Measure C(ℝ≥0, E)).map fun x => x (σ x).toNNReal) :=
      (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).2 inferInstance
    refine abs_integral_sub_integral_le_of_abs_measureReal_sub_le _ _ hgm hB0 hgB
      (fun A hA => ?_)
    rw [measureReal_def, measureReal_def, Measure.map_apply hYm hA, Measure.map_apply hYm hA]
    exact hw2 A hA
  have hsum : 2 * B * (((K z : Measure C(ℝ≥0, E)) {x | (r : ℝ≥0∞) < σ x}).toReal +
      ((K w : Measure C(ℝ≥0, E)) {x | (r : ℝ≥0∞) < σ x}).toReal) ≤ 2 * B * (2 * η0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [Real.dist_eq, abs_sub_comm]
  rw [← hBdef] at Hz Hw
  set Rz := pathResolvent K lam f z with hRz
  set Rw := pathResolvent K lam f w with hRw
  set Iz := ∫ x, pathResolvent K lam f (x (σ x).toNNReal) ∂(K z : Measure C(ℝ≥0, E)) with hIz
  set Iw := ∫ x, pathResolvent K lam f (x (σ x).toNNReal) ∂(K w : Measure C(ℝ≥0, E)) with hIw
  have htri : |Rz - Rw| ≤ |Rz - Iz| + |Iz - Iw| + |Iw - Rw| := by
    have : Rz - Rw = (Rz - Iz) + (Iz - Iw) + (Iw - Rw) := by ring
    rw [this]
    exact abs_add_three _ _ _
  have hsym : |Iw - Rw| = |Rw - Iw| := abs_sub_comm _ _
  linarith

end LatticeProb

end

import LatticeProb.LQG.ConeRandomCentreMass
import LatticeProb.Topology.LocalizedFirstExitTrace

/-! # Outer window containment from first-exit ball masses -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort MatedCRTHarmonic.CellScaling
open scoped NNReal ENNReal

namespace LatticeProb.LQG

/-- If a mass-parametrized segment escapes a region, a ball in one of its
first-exit traces has mass at most the length of the segment. -/
theorem measure_window_escape_le_exit_failure_add_ball_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ) (U : Ω → Set ℂ)
    {w ρ δ q : ℝ} (hw : 0 ≤ w) (hq : 2 * w ≤ q)
    (hparam : ∀ᵐ ω ∂P, ∀ s t : ℝ, s ≤ t →
      μ ω (η ω '' Icc s t) = ENNReal.ofReal (t - s)) :
    P {ω | ¬ η ω '' Icc (-w) w ⊆ U ω} ≤
      P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ U ω}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ U ω})))} +
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ, μ ω (ball z δ) ≤ ENNReal.ofReal q} := by
  refine (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hparam] with ω ha hesc
  by_cases hballs : ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ U ω}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ U ω})))
  · right
    have hwindow : μ ω (η ω '' Icc (-w) w) = ENNReal.ofReal (2 * w) := by
      rw [ha _ _ (by linarith)]
      congr 1
      ring
    rcases LatticeProb.first_exit_trace_subset_of_not_subset (η ω) (U ω)
      (show -w ≤ 0 by linarith) hw hesc with hl | hr
    · obtain ⟨z, hz, hsub⟩ := hballs.1
      exact ⟨z, hz, (measure_mono (hsub.trans hl)).trans
        (hwindow.le.trans (ENNReal.ofReal_le_ofReal hq))⟩
    · obtain ⟨z, hz, hsub⟩ := hballs.2
      exact ⟨z, hz, (measure_mono (hsub.trans hr)).trans
        (hwindow.le.trans (ENNReal.ofReal_le_ofReal hq))⟩
  · exact Or.inl hballs

/-- For a quantum cone, the probability of window escape is bounded by the
failure of the two exit-ball witnesses and the uniform small-ball lower tail. -/
theorem measure_cone_window_escape_le_exit_failure_add
    {γ : ℝ} (M : MatedCRTHarmonic.GMSLemma27.CellModel γ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {X : M.Ω → DistC} {B B' : ℝ≥0 → M.Ω → ℝ}
    (hX : IsWholePlaneGFF X M.P)
    (hB : IsBrownianReal B M.P) (hB' : IsBrownianReal B' M.P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) M.P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) M.P)
    (harea : ∀ᵐ ω ∂M.P,
      M.area ω = lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))
    (η : M.Ω → ℝ → ℂ) (U : M.Ω → Set ℂ)
    (hparam : ∀ᵐ ω ∂M.P, ∀ s t : ℝ, s ≤ t →
      M.area ω (η ω '' Icc s t) = ENNReal.ofReal (t - s))
    {p ρ e : ℝ} (hp : 0 < p) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ {δ w : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → 0 ≤ w →
      2 * w ≤ δ ^ (2 + γ ^ 2 / 2 + p) →
      M.P {ω | ¬ η ω '' Icc (-w) w ⊆ U ω} ≤
        M.P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
          η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ U ω}) 0) ∧
          (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
          η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ U ω})))} +
        ENNReal.ofReal (C * δ ^ e) := by
  have hdom := MatedCRTHarmonic.GMCFacts.areaDominates_of_cone M hγ hγ2 hX hB hB' hind harea
  obtain ⟨C, hC⟩ := MatedCRTHarmonic.GMSLemma27.lemma28_strict M
    (MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2) hdom hγ hp hρ0 hρ1 he
  refine ⟨C, fun hδ hw hq => ?_⟩
  exact (measure_window_escape_le_exit_failure_add_ball_mass M.P M.area η U hw hq hparam).trans
    (add_le_add_right (hC _ hδ) _)

end LatticeProb.LQG

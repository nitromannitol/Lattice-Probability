/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianUniformLanding at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianGaussianReference
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Data.Finset.Lattice.Fold

/-! A uniform positive unit-time landing probability over a compact set of
centers. Full support comes from the strictly positive Gaussian density and
the actual finite-product marginal identity. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped Classical NNReal ENNReal Topology

namespace BouRabeeGwynne

/-- The actual unit-time spatial Brownian marginal gives positive mass to
every nonempty open set, including in dimension zero. -/
theorem standardBrownianLaw_eval_one_isOpenPosMeasure {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    Measure.IsOpenPosMeasure (μ.map (fun ω : BrownianPath d => ω 1)) := by
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) (by norm_num)).isOpenPosMeasure
  have hsupport : Measure.IsOpenPosMeasure
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
        (WithLp.toLp 2 : (Fin d → ℝ) → Euc d)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).isOpenPosMeasure_map
      (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (WithLp.toLp_surjective 2)
  have heq := standardBrownianLaw_map_translated_eval hμ (0 : Euc d) 1
  simp only [PiLp.zero_apply, zero_add] at heq
  rw [heq]
  exact hsupport

/-- For any positive radius, unit-time Brownian motion has one strictly
positive lower landing probability for all ball centers of norm at most two.
This is an actual path-event probability, with no support assumption added. -/
theorem standardBrownianLaw_uniform_landing_probability {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ c : Euc d, ‖c‖ ≤ 2 →
      ENNReal.ofReal p ≤ μ {ω : BrownianPath d | ω 1 ∈ ball c κ} := by
  let : IsProbabilityMeasure μ := hμ.1
  have heval : Measurable (fun ω : BrownianPath d => ω 1) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d => ω 1)).measurable
  let ν : Measure (Euc d) := μ.map (fun ω : BrownianPath d => ω 1)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff heval.aemeasurable).mpr inferInstance
  let : Measure.IsOpenPosMeasure ν := standardBrownianLaw_eval_one_isOpenPosMeasure hμ
  have hhalf : 0 < κ / 2 := half_pos hκ
  obtain ⟨F, hF⟩ := (isCompact_closedBall (0 : Euc d) 2).elim_finite_subcover
    (fun c : Euc d => ball c (κ / 2)) (fun _ => isOpen_ball)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_ball_self hhalf⟩)
  have hzero : (0 : Euc d) ∈ closedBall 0 2 := by simp
  have hFne : F.Nonempty := by
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hF hzero)
    obtain ⟨haF, _⟩ := mem_iUnion.mp ha
    exact ⟨a, haF⟩
  let m : Euc d → ℝ := fun c => (ν (ball c (κ / 2))).toReal
  have hm (c : Euc d) : 0 < m c :=
    ENNReal.toReal_pos (isOpen_ball.measure_ne_zero ν ⟨c, mem_ball_self hhalf⟩)
      (measure_ne_top ν _)
  let p : ℝ := min 1 (F.inf' hFne m)
  have hp : 0 < p := lt_min zero_lt_one
    ((Finset.lt_inf'_iff hFne).mpr (fun c _ => hm c))
  refine ⟨p, hp, min_le_left _ _, ?_⟩
  intro c hc
  have hcK : c ∈ closedBall (0 : Euc d) 2 := by
    simpa only [mem_closedBall, dist_zero_right] using hc
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hF hcK)
  obtain ⟨haF, hca⟩ := mem_iUnion.mp ha
  have hsub : ball a (κ / 2) ⊆ ball c κ := by
    apply ball_subset_ball'
    have hd : dist a c < κ / 2 := by simpa only [mem_ball, dist_comm] using hca
    linarith
  have hpm : p ≤ m a := (min_le_right _ _).trans (Finset.inf'_le m haF)
  have hmap : ν (ball c κ) = μ {ω : BrownianPath d | ω 1 ∈ ball c κ} :=
    Measure.map_apply heval isOpen_ball.measurableSet
  rw [← hmap]
  calc
    ENNReal.ofReal p ≤ ENNReal.ofReal (m a) := ENNReal.ofReal_le_ofReal hpm
    _ = ν (ball a (κ / 2)) := ENNReal.ofReal_toReal (measure_ne_top ν _)
    _ ≤ ν (ball c κ) := measure_mono hsub

end BouRabeeGwynne

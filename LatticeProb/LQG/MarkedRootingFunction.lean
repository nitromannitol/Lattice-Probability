import Mathlib
import LatticeProb.LQG.MarkedRootingMeasurableSet
import LatticeProb.Prob.RandomMeasureIntensityFun

/-!
# The marked rooting identity for nonnegative functions of the marks

The identity of `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lqgMeasure_marked_eq_of_measurableSet` for
indicators of measurable sets `S ⊆ ℂ × ℝ^m` of (point, mark) pairs is extended to every measurable function
`f : ℂ × ℝ^m → [0, ∞]`:
`E [∫_{𝔻} f (z, X) dμ (z)] = ∫_{𝔻} E [f (z, X + γ c(z))] dz`,
where `X = ((h, φ_i))_i` and `c(z) = (∫ φ_i(x) Cov (h(x), h(z)) dx)_i`.

## Main statement

* `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lqgMeasure_marked_fun_eq`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **The marked rooting identity for measurable functions of the marks.** For a measurable
`f : ℂ × ℝ^m → [0, ∞]`, `E [∫_{𝔻} f (z, X) dμ (z)] = ∫_{𝔻} E [f (z, X + γ c(z))] dz`, with
`X = ((h, φ_i))_i` and `c(z) = (∫ φ_i(x) Cov (h(x), h(z)) dx)_i`; the left integrand is almost everywhere
measurable. -/
theorem lintegral_lqgMeasure_marked_fun_eq (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {m : ℕ}
    {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {f : ℂ × (Fin m → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ z in Metric.ball (0 : ℂ) 1, f (z, fun i => hC ω (φ i)) ∂(μ ω)) P ∧
    ∫⁻ ω, ∫⁻ z in Metric.ball (0 : ℂ) 1, f (z, fun i => hC ω (φ i)) ∂(μ ω) ∂P =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω,
        f (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  have hP := hh.isProbabilityMeasure
  have hmeasP : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hsm : ∀ i, Measurable fun z : ℂ => ∫ x, φ i x * wholePlaneCov x z := fun i =>
    measurable_integral_mul_wholePlaneCov (hφ i)
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  set Y : ℂ × Ω → (Fin m → ℝ) := fun q i => hC q.2 (φ i) + γ * ∫ x, φ i x * wholePlaneCov x q.1 with hY
  have hYm : Measurable Y := measurable_pi_iff.2 fun i =>
    ((hmeasP i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ)
  set F : ℂ × Ω → ℂ × (Fin m → ℝ) := fun q => (q.1, Y q) with hF
  have hFm : Measurable F := measurable_fst.prodMk hYm
  let ν : Ω → Measure (ℂ × (Fin m → ℝ)) := fun ω =>
    ((μ ω).restrict (Metric.ball (0 : ℂ) 1)).map (fun z => (z, fun i => hC ω (φ i)))
  let ρ : Measure (ℂ × (Fin m → ℝ)) := ((volume.restrict (Metric.ball (0 : ℂ) 1)).prod P).map F
  have hνg : ∀ g : ℂ × (Fin m → ℝ) → ℝ≥0∞, Measurable g → ∀ ω, ∫⁻ y, g y ∂(ν ω) =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, g (z, fun i => hC ω (φ i)) ∂(μ ω) := fun g hg ω => by
    simp only [ν]
    exact lintegral_map hg (measurable_id.prodMk measurable_const)
  have hρg : ∀ g : ℂ × (Fin m → ℝ) → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂ρ =
      ∫⁻ z in Metric.ball (0 : ℂ) 1, ∫⁻ ω,
        g (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := fun g hg => by
    simp only [ρ]
    rw [lintegral_map hg hFm]
    exact lintegral_prod (fun q => g (F q)) (hg.comp hFm).aemeasurable
  have key := aemeasurable_and_lintegral_eq_of_forall_measurableSet (P := P) ν ρ (fun S hS => by
    have h := hh.lintegral_lqgMeasure_marked_eq_of_measurableSet hγ0 hγ2 hμ hφ hS
    have hind : Measurable (S.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hS
    have hνS : ∀ ω, ν ω S = ∫⁻ z in Metric.ball (0 : ℂ) 1,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun i => hC ω (φ i)) ∂(μ ω) := fun ω =>
      (lintegral_indicator_one hS).symm.trans (hνg _ hind ω)
    have hρS := (lintegral_indicator_one hS).symm.trans (hρg _ hind)
    exact ⟨h.1.congr (Filter.Eventually.of_forall fun ω => (hνS ω).symm),
      (lintegral_congr fun ω => hνS ω).trans (h.2.trans hρS.symm)⟩) f hf
  refine ⟨key.1.congr (Filter.Eventually.of_forall fun ω => hνg f hf ω), ?_⟩
  rw [← hρg f hf, ← key.2]
  exact lintegral_congr fun ω => (hνg f hf ω).symm

end IsWholePlaneGFF

end LatticeProb.Gauss

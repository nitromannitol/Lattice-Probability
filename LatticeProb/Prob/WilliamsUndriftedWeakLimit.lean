import LatticeProb.Prob.WilliamsWeakLimitIdentification

/-! # The undrifted conditioned Brownian weak limit -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace LatticeProb

open QuantumZipper QuantumZipper.Williams

/-- The conditioned weak limit is the post-last-zero path with its linear
    drift removed. -/
theorem weakLimit_eq_undrifted_williamsPostLastPath_law
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {d : ℝ} (hd : 0 < d) (hind : IndepFun (pathOf b) (pathOf b') P)
    (ν : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto (fun δ : ℝ =>
      ∫ w, f w ∂((P.map (pathMap b hb.cont))[|driftMap d ⁻¹' staySet δ]))
      (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ν = P.map (fun ω => driftMap (-d) (williamsPostLastPath hb' 1 d ω)) := by
  have h := congrArg (fun μ : Measure C(ℝ≥0, ℝ) => μ.map (driftMap (-d)))
    (driftMap_weakLimit_eq_williamsPostLastPath_law hb hb' hd hind ν hν)
  rw [Measure.map_map (measurable_driftMap _) (measurable_driftMap _),
    Measure.map_map (measurable_driftMap _) (measurable_williamsPostLastPath _ _ _)] at h
  have hid : (driftMap (-d)) ∘ (driftMap d) = id := by
    funext w
    ext t
    simp only [Function.comp_apply, driftMap_apply, neg_mul, id_eq]
    ring
  simpa only [hid, Measure.map_id, Function.comp_def] using h

end LatticeProb

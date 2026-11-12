/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3C

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: Step 4, `h̊` side, in the limit coupling (items R1 + R2)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1240–1256) and Step 4 (T:1270–1273). On the canonical space `(S, μ)` of the field
coordinates, with the field `N` (a GFF plus a bounded continuous function, e.g. `Ñ` of
L2_17Core2H.lean) and the bump-truncated harmonic part `Fb` (supported in a fixed compact `K`),
let `ρ` be a weak limit of the laws of `(x, (D^{εₙ}_{N x})^, (D^{εₙ}_{N x − Fb x})^)` (as produced
by `indep_stage_limit`). Then for every dyadic domain `W`

  `σ(D₁(·,·;W)) ⊆ σ(Fb, d₂_W)` up to `ρ`-null sets  (`comap_intFn_le_aeClosure_coupling`),

the paper's "`D_h(·,·;W')` is a measurable function of `𝔥` and `D_{h−φ𝔥}(·,·;W')`" (T:1272).

Proof (the paper's route): stable convergence (`tendsto_law_of_fixed_marginal`) adds `Fb x`;
Skorokhod's theorem (`exists_skorokhod_representation_sb`) gives a.s. convergence on a standard
Borel space; there, along every sample, Lemma 2.12 with varying fields (`weyl_of_sample`) gives
`D₁ = e^{ξ Fb}·D₂` (T:1250, T:1271), and Lemma 2.5 B and the locality of Weyl scaling give the
fibre property (`intFn_eq_of_weyl`); Lusin separation on the Skorokhod space and the equality of
laws transfer it to `ρ` (`comap_le_aeClosure_of_rep`, `comap_comp_le_aeClosure`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint MetricGeometry LFPP GM.Bilip

/-- pointwise convergence of random elements implies convergence of their laws -/
theorem tendsto_map_of_forall_tendsto {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    {Z : ℕ → Ω → T} {Z₀ : Ω → T} (hZ : ∀ n, Measurable (Z n)) (hZ₀ : Measurable Z₀)
    (hc : ∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (Z₀ ω))) :
    Tendsto (β := ProbabilityMeasure T) (fun n => (⟨P.map (Z n),
      (Measure.isProbabilityMeasure_map_iff (hZ n).aemeasurable).2 inferInstance⟩ :
        ProbabilityMeasure T)) atTop
      (𝓝 (⟨P.map Z₀, (Measure.isProbabilityMeasure_map_iff hZ₀.aemeasurable).2 inferInstance⟩ :
        ProbabilityMeasure T)) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 ?_
  intro f
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map hZ₀.aemeasurable f.continuous.aestronglyMeasurable]
  have e : ∀ n, ∫ x, f x ∂(P.map (Z n)) = ∫ ω, f (Z n ω) ∂P := fun n =>
    integral_map (hZ n).aemeasurable f.continuous.aestronglyMeasurable
  simp only [e]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.continuous.measurable.comp (hZ n)).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun ω => f.norm_coe_le_norm _) (Eventually.of_forall fun ω =>
      (f.continuous.tendsto _).comp (hc ω))

end L217

end LQGMetric.DFGPS

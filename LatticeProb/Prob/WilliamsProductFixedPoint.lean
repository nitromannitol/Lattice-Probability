import LatticeProb.Prob.WilliamsContinuousUnconditional

/-! # Product fixed points for the Williams decomposition -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

open QuantumZipper QuantumZipper.Williams

/-- The drifted path and the post-last-zero path of independent Brownian motions are independent. -/
theorem indepFun_dpath_williamsPostLastPath
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    (hind : IndepFun (pathOf b) (pathOf b') P) (σ μ : ℝ) :
    IndepFun (fun ω => (⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩ : C(ℝ≥0, ℝ)))
      (williamsPostLastPath hb' σ μ) P := by
  have hc : ∀ ω, Continuous (dpath σ μ b' ω) := continuous_dpath hb' σ μ
  have hX : Measurable[MeasurableSpace.comap (pathOf b) MeasurableSpace.pi]
      (fun ω => (⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩ : C(ℝ≥0, ℝ))) := by
    let _ : MeasurableSpace Ω := MeasurableSpace.comap (pathOf b) MeasurableSpace.pi
    have hp : Measurable (pathOf b) := comap_measurable _
    refine ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact (((measurable_pi_apply t).comp hp).const_mul σ).add_const ((-μ) * t)
  have hZ : Measurable[MeasurableSpace.comap (pathOf b') MeasurableSpace.pi]
      (williamsPostLastPath hb' σ μ) := by
    let _ : MeasurableSpace Ω := MeasurableSpace.comap (pathOf b') MeasurableSpace.pi
    have hp : Measurable (pathOf b') := comap_measurable _
    have hm : ∀ t, Measurable fun ω => dpath σ μ b' ω t := fun t =>
      (((measurable_pi_apply t).comp hp).const_mul σ).add_const (μ * t)
    refine ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 fun t => ?_
    exact measurable_postLast_gen hc hm measurable_const
  rw [IndepFun_iff_Indep] at hind ⊢
  exact indep_of_indep_of_le hind hX.comap_le hZ.comap_le

/-- The post-last-zero law is a fixed point of independent Williams gluing. -/
theorem map_prod_williamsPostLastPath_glueC
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {σ μ c : ℝ} (hσ : 0 < σ) (hμ : 0 < μ)
    (hind : IndepFun (pathOf b) (pathOf b') P) (hc : 0 < c) :
    ((P.map (fun ω => (⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩ : C(ℝ≥0, ℝ)))).prod
      (P.map (williamsPostLastPath hb' σ μ))).map (fun p => glueC c p.1 p.2) =
      P.map (williamsPostLastPath hb' σ μ) := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hX : Measurable (fun ω =>
      (⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩ : C(ℝ≥0, ℝ))) :=
    ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 (fun t => measurable_dpath hb σ (-μ) t)
  have hZ := measurable_williamsPostLastPath hb' σ μ
  rw [← (indepFun_dpath_williamsPostLastPath hb hb' hind σ μ).map_prod_eq_prod_map_map
    hX.aemeasurable hZ.aemeasurable,
    Measure.map_map (measurable_glueC c) (hX.prodMk hZ)]
  exact map_williams_glueC_eq_map_postLast_unconditional hb hb' hσ hμ hind hc

/-- The law of a unit-diffusion drifted path is the drifted Brownian path law. -/
theorem map_dpath_one_eq_driftLaw
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (μ : ℝ) :
    P.map (fun ω => (⟨dpath 1 μ b ω, continuous_dpath hb 1 μ ω⟩ : C(ℝ≥0, ℝ))) =
      driftLaw P b hb.cont μ := by
  symm
  rw [driftLaw, Measure.map_map (measurable_driftMap μ) (measurable_pathMap b hb.meas hb.cont)]
  apply congrArg (fun f : Ω → C(ℝ≥0, ℝ) => P.map f)
  funext ω
  ext t
  change b t ω + μ * t = 1 * b t ω + μ * t
  rw [one_mul]

/-- The post-last-zero law is a fixed point for gluing with the negative drift law. -/
theorem driftLaw_prod_williamsPostLastPath_glueC
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {μ c : ℝ} (hμ : 0 < μ) (hind : IndepFun (pathOf b) (pathOf b') P) (hc : 0 < c) :
    ((driftLaw P b hb.cont (-μ)).prod (P.map (williamsPostLastPath hb' 1 μ))).map
      (fun p => glueC c p.1 p.2) = P.map (williamsPostLastPath hb' 1 μ) := by
  rw [← map_dpath_one_eq_driftLaw hb (-μ)]
  exact map_prod_williamsPostLastPath_glueC hb hb' (by norm_num) hμ hind hc

end LatticeProb

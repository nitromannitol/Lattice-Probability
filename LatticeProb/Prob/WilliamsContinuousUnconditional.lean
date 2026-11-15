import LatticeProb.Prob.WilliamsContinuousLaw

/-! # Continuous-path Williams decomposition -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

open QuantumZipper QuantumZipper.Williams

/-- A negatively drifted Brownian path reaches any negative level almost surely. -/
theorem ae_dpath_hits_negative {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) {σ μ c : ℝ}
    (hσ : 0 < σ) (hμ : 0 < μ) (hc : 0 < c) :
    ∀ᵐ ω ∂P, ∃ t, dpath σ (-μ) b ω t = -c := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  filter_upwards [WedgeTrans.ae_exists_below hb.pre hb.meas
    (μ := μ * Real.sqrt 2 / σ) (c := c * Real.sqrt 2 / σ)
    (by positivity) (by positivity)] with ω h
  obtain ⟨n, hn⟩ := h
  apply exists_eq_of_le (continuous_dpath hb σ (-μ) ω) (dpath_zero hb σ (-μ) ω) hc
    (t := (n : ℝ≥0))
  have e1 : σ * b n ω - μ * n = σ / Real.sqrt 2 *
      (Real.sqrt 2 * b n ω - μ * Real.sqrt 2 / σ * n) := by field_simp
  have e2 : -c = σ / Real.sqrt 2 * (-(c * Real.sqrt 2 / σ)) := by field_simp
  have hlt := mul_lt_mul_of_pos_left hn (show 0 < σ / Real.sqrt 2 by positivity)
  rw [← e1, ← e2] at hlt
  simpa [dpath] using hlt.le

/-- The Williams gluing law on continuous paths requires no pointwise hitting condition. -/
theorem map_williams_glueC_eq_map_postLast_unconditional
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {σ μ c : ℝ} (hσ : 0 < σ) (hμ : 0 < μ)
    (hind : IndepFun (pathOf b) (pathOf b') P) (hc : 0 < c) :
    P.map (fun ω => glueC c ⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩
      (williamsPostLastPath hb' σ μ ω)) = P.map (williamsPostLastPath hb' σ μ) := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hraw := williamsDriftDecomposition_holds μ σ c hμ hσ hc P b b'
    ⟨hb.pre, Eventually.of_forall hb.cont⟩ ⟨hb'.pre, Eventually.of_forall hb'.cont⟩ hind
  have hraw' : P.map (fun ω u => glued c (dpath σ (-μ) b ω) (dpath σ μ b' ω) u) =
      P.map (fun ω u => postLast (dpath σ μ b' ω) 0 u) := by
    convert hraw using 1 <;> congr 1 <;> funext ω u
    · exact (zp_eq_glued (σ := σ) (μ := μ) (B' := fun t => b' t ω)
        hc (hb.cont ω) (hb.zero ω) u rfl rfl).symm
    · exact (yh_eq_postLast (σ := σ) (μ := μ) (fun t => b' t ω) u rfl).symm
  have hX : Measurable (fun ω =>
      (⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩ : C(ℝ≥0, ℝ))) :=
    ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 (fun t => measurable_dpath hb σ (-μ) t)
  have hZ := measurable_williamsPostLastPath hb' σ μ
  have hF := (measurable_glueC c).comp (hX.prodMk hZ)
  apply map_continuousPath_eq_of_ae_coe_eq hF hZ ?_ (Eventually.of_forall fun _ => rfl) hraw'
  filter_upwards [ae_dpath_hits_negative hb hσ hμ hc, ae_williamsPostLastPath_zero hb' hσ hμ]
    with ω ⟨t, ht⟩ hz
  let X : C(ℝ≥0, ℝ) := ⟨dpath σ (-μ) b ω, continuous_dpath hb σ (-μ) ω⟩
  have hfin : hitFrom (-c) 0 (X : ℝ≥0 → ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hitFrom_le zero_le ht)
  exact (glued_eq_glueC (dpath_zero hb σ (-μ) ω) hz hfin (fun _ => rfl)).symm

end LatticeProb

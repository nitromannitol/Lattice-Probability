/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent3Wn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Vague
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentL1
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist

/-!
# Law transfer, part 3: inputs of the identification for the white-noise field (P2-GMCID3)

The white-noise field `wnField W ω := circExt (wnCircVec W ω)` (the circles inside `𝕍` carry
`√π W(K_σ)`, everything else `0`) is not a zero-boundary GFF, but by `map_circVec_eq` its circle
family has the law of the circle family of any zero-boundary GFF `X`. The inputs of
`GMCIdent.ae_tendsto_wnGMC` that used `hX` transfer:

* `avgReg_ae_eq_wn`: `h_{2^{-k}}(t) = √π W(K_{σ_{t,2^{-k}}})` a.s. (from `avgReg_ae_eq` for `X`);
* `tendsto_eLpNorm_areaApprox_sub_wn`: `∫ f dμ_k → ∫ f dM_γ` in `L¹(P')` and integrability (from
  `tendsto_eLpNorm_areaApprox_sub` for `X`);
* `ae_isVagueLimitOn_wn` (part 2): `M_γ` of the white-noise field is a.s. the vague limit.

Transfers go through `eLpNorm_map_measure` / `integrable_map_measure` for functions on
`CircIdx → ℝ` that are a.e.-strongly measurable for the circle law (D85).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent3

open GMCIdent WhiteNoise

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

/-- the white-noise field: the white-noise circle family extended by `0` -/
def wnField (W : WNSpace → Ω' → ℝ) (ω : Ω') : FieldSample := circExt (wnCircVec W ω)

lemma circleUnif_eq_of_foldedCircle_eq {i j : CircIdx}
    (h : foldedCircle i.1.1 i.1.2 = foldedCircle j.1.1 j.1.2) :
    circleUnif i.1.1 i.1.2 = circleUnif j.1.1 j.1.2 := by
  rw [← foldedCircle_eq_of_inSq (inSq_of_closedBall i.2.1 i.2.2) i.2.1, h,
    foldedCircle_eq_of_inSq (inSq_of_closedBall j.2.1 j.2.2) j.2.1]

lemma wnField_circle (ω : Ω') (j : CircIdx) :
    wnField W ω (foldedCircle j.1.1 j.1.2) = wnCircVec W ω j := by
  unfold wnField
  rw [circExt_apply]
  exact congrArg (fun μ => Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) μ) ω)
    (circleUnif_eq_of_foldedCircle_eq
      (⟨j, rfl⟩ : ∃ i : CircIdx, foldedCircle i.1.1 i.1.2 = foldedCircle j.1.1 j.1.2).choose_spec)

/-- **circle coupling of the white-noise field**: `h_{2^{-k}}(t) = √π W(K_{σ_{t,2^{-k}}})` a.s. -/
theorem avgReg_ae_eq_wn [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {t : ℂ} {k : ℕ} (hB : closedBall t (2 * radius k) ⊆ openSquare) :
    (fun ω => avgReg (wnField W ω) k t) =ᵐ[P'] fun ω =>
      Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif t (radius k))) ω := by
  have hr := radius_pos k
  have hB' : closedBall t (radius k) ⊆ openSquare :=
    (closedBall_subset_closedBall (by linarith)).trans hB
  set j : CircIdx := ⟨(t, radius k), hr, hB'⟩
  set p : (CircIdx → ℝ) → Prop := fun v =>
    avgReg (circExt v) k t = circExt v (foldedCircle t (radius k))
  have hE : MeasurableSet {v | p v} :=
    measurableSet_eq_fun ((measurable_avgReg k).comp (measurable_circExt.prodMk measurable_const))
      (measurable_pi_iff.1 measurable_circExt (foldedCircle t (radius k)))
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  have hsq : t ∈ sqIn (2 * radius k) := by
    obtain ⟨a, b, c, d⟩ := inSq_of_closedBall (by positivity) hB
    exact ⟨a.le, by linarith, c.le, by linarith⟩
  have hν : ∀ᵐ v ∂(circLaw P X), p v := by
    refine (ae_map_iff (p := p) hm.aemeasurable hE).2 ?_
    filter_upwards [avgReg_ae_eq hX hB] with ω h
    simp only [p]
    rw [avgReg_circExt (by linarith) hsq, h]
    exact (circExt_circVec (X ω) j).symm
  have hW' : ∀ᵐ ω ∂P', p (wnCircVec W ω) := by
    refine ae_of_ae_map (p := p) (measurable_wnCircVec hW).aemeasurable ?_
    rw [← map_circVec_eq hX hW]; exact hν
  filter_upwards [hW'] with ω h
  have h' : avgReg (wnField W ω) k t = wnField W ω (foldedCircle j.1.1 j.1.2) := h
  rw [h', wnField_circle]
  rfl

/-! ## `L¹` data -/

lemma exists_integral_areaApprox_circExt (γ : ℝ) {f : ℂ → ℝ} (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ openSquare) : ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ x : FieldSample,
      ∫ z, f z ∂(areaApprox γ (circExt (circVec x)) k) = ∫ z, f z ∂(areaApprox γ x k) := by
  obtain ⟨s, hs, hTs⟩ := exists_sqIn_of_isCompact hfc.isCompact hfU
  have hfS : ∀ z ∉ sqIn s, f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hTs h)
  obtain ⟨k₀, hk₀⟩ := exists_radius_le hs
  exact ⟨k₀, fun k hk x =>
    integral_areaApprox_circExt γ (by linarith [hk₀ k hk, radius_pos k]) x hfS⟩

lemma eLpNorm_comp_wn_eq (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W)
    {F : (CircIdx → ℝ) → ℝ} (hF : AEStronglyMeasurable F (circLaw P X)) (p : ℝ≥0∞) :
    eLpNorm (fun ω => F (wnCircVec W ω)) p P' = eLpNorm (fun ω => F (circVec (X ω))) p P := by
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  have hF' : AEStronglyMeasurable F (P'.map (wnCircVec W)) := by
    rw [← map_circVec_eq hX hW]; exact hF
  have e1 : eLpNorm (fun ω => F (wnCircVec W ω)) p P' = eLpNorm F p (P'.map (wnCircVec W)) :=
    (eLpNorm_map_measure hF' (measurable_wnCircVec hW).aemeasurable).symm
  have e2 : eLpNorm F p (circLaw P X) = eLpNorm (fun ω => F (circVec (X ω))) p P :=
    eLpNorm_map_measure hF hm.aemeasurable
  rw [e1, ← map_circVec_eq hX hW]; exact e2

lemma integrable_comp_wn_iff (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W)
    {F : (CircIdx → ℝ) → ℝ} (hF : AEStronglyMeasurable F (circLaw P X)) :
    Integrable (fun ω => F (wnCircVec W ω)) P' ↔ Integrable (fun ω => F (circVec (X ω))) P := by
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  have hF' : AEStronglyMeasurable F (P'.map (wnCircVec W)) := by
    rw [← map_circVec_eq hX hW]; exact hF
  have e1 : Integrable (fun ω => F (wnCircVec W ω)) P' ↔ Integrable F (P'.map (wnCircVec W)) :=
    (integrable_map_measure hF' (measurable_wnCircVec hW).aemeasurable).symm
  have e2 : Integrable F (circLaw P X) ↔ Integrable (fun ω => F (circVec (X ω))) P :=
    integrable_map_measure hF hm.aemeasurable
  rw [e1, ← map_circVec_eq hX hW]; exact e2

lemma aestronglyMeasurable_integral_qArea [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare) :
    AEStronglyMeasurable (fun v => ∫ z, f z ∂(qAreaMeasureOn γ (circExt v) openSquare))
      (circLaw P X) := by
  have hΦ : ∀ k, StronglyMeasurable fun v : CircIdx → ℝ =>
      ∫ z, f z ∂(areaApprox γ (circExt v) k) := fun k =>
    ((measurable_integral_areaApprox_cpt γ k hf hfc hfU).comp measurable_circExt).stronglyMeasurable
  refine ⟨fun v => limUnder atTop fun k => ∫ z, f z ∂(areaApprox γ (circExt v) k),
    StronglyMeasurable.limUnder hΦ, ?_⟩
  filter_upwards [ae_isVagueLimitOn_circExt hX hγ hγ2] with v h
  exact ((h.2.2 f hf hfc hfU).limUnder_eq).symm

/-- **`L¹` convergence for the white-noise field** (transfer of `tendsto_eLpNorm_areaApprox_sub`) -/
theorem tendsto_eLpNorm_areaApprox_sub_wn [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ openSquare) :
    ∃ k₀ : ℕ, (∀ k, k₀ ≤ k →
        Integrable (fun ω => ∫ z, f z ∂(areaApprox γ (wnField W ω) k)) P') ∧
      Integrable (fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (wnField W ω) openSquare)) P' ∧
      Tendsto (fun k => eLpNorm ((fun ω => ∫ z, f z ∂(areaApprox γ (wnField W ω) (k₀ + k))) -
        fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (wnField W ω) openSquare)) 1 P') atTop (𝓝 0) := by
  obtain ⟨k₀, hint, hYl, hL1⟩ := tendsto_eLpNorm_areaApprox_sub hX hγ hγ2 hf hfc hfU
  obtain ⟨k₁, hk₁⟩ := exists_integral_areaApprox_circExt γ hfc hfU
  set Φ : ℕ → (CircIdx → ℝ) → ℝ := fun k v => ∫ z, f z ∂(areaApprox γ (circExt v) k)
  set Ψ : (CircIdx → ℝ) → ℝ := fun v => ∫ z, f z ∂(qAreaMeasureOn γ (circExt v) openSquare)
  have hΦm : ∀ k, AEStronglyMeasurable (Φ k) (circLaw P X) := fun k =>
    ((measurable_integral_areaApprox_cpt γ k hf hfc hfU).comp measurable_circExt).aestronglyMeasurable
  have hΨm : AEStronglyMeasurable Ψ (circLaw P X) :=
    aestronglyMeasurable_integral_qArea hX hγ hγ2 hf hfc hfU
  have eX : ∀ k, k₁ ≤ k → (fun ω => Φ k (circVec (X ω))) =
      fun ω => ∫ z, f z ∂(areaApprox γ (X ω) k) := fun k hk => funext fun ω => hk₁ k hk (X ω)
  have eXl : (fun ω => Ψ (circVec (X ω))) =
      fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (X ω) openSquare) :=
    funext fun ω => by simp only [Ψ, qAreaMeasureOn_circExt]
  set K := max k₀ k₁
  refine ⟨K, fun k hk => ?_, ?_, ?_⟩
  · refine (integrable_comp_wn_iff hX hW (hΦm k)).2 ?_
    rw [eX k (le_trans (le_max_right _ _) hk)]
    exact hint k (le_trans (le_max_left _ _) hk)
  · refine (integrable_comp_wn_iff hX hW hΨm).2 ?_
    rw [eXl]; exact hYl
  · have e : ∀ k, eLpNorm ((fun ω => ∫ z, f z ∂(areaApprox γ (wnField W ω) (K + k))) -
        fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (wnField W ω) openSquare)) 1 P' =
        eLpNorm ((fun ω => ∫ z, f z ∂(areaApprox γ (X ω) (k₀ + (k + (K - k₀))))) -
        fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (X ω) openSquare)) 1 P := by
      intro k
      have h := eLpNorm_comp_wn_eq hX hW ((hΦm (K + k)).sub hΨm) 1
      have hk' : k₀ + (k + (K - k₀)) = K + k := by omega
      rw [hk', ← eX _ (by omega), ← eXl]
      exact h
    exact ((tendsto_add_atTop_iff_nat (K - k₀)).2 hL1).congr fun k => (e k).symm

end GMCIdent3
end LQGMetric

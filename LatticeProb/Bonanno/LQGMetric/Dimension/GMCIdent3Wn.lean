/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent3Wn at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Vague
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist

/-!
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

end GMCIdent3
end LQGMetric

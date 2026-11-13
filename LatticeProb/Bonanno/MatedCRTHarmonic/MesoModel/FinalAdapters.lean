/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.FinalAdapters at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.SLEInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Bookkeeping

/-!
# Cell-model assembly through bundle-free adapters

Two adapters used by the final cell-model assembly. They connect the area parametrization
and segment-ball estimates to the coupling's cell model.

* **Area parametrization:** the coupling states the area parametrization of the curve for *every* dyadic vague limit
  of the area approximations of the cone field. `CellScaling.AreaParametrization` is stated for
  `CellScaling.lqgArea`. `final_areaParametrization_of_vagueLimits` closes the
  gap with the SLE-free existence of the vague limit (`GMCFacts.coneAreaExists_holds`): almost surely
  the limit exists, so `lqgArea` is that limit and the every-limit statement applies to it.
* **GHM15 Prop 3.4 transfer**: the bundle's superpolynomial segment-ball bound for the Lebesgue-parametrized curve
  `ηL` gives Lemma 2.7's little-o interface `GMSLemma27.SegmentsContainBalls` for any cell model whose curve is a.s. an
  increasing reparametrization of `ηL` (the images of segments are the same sets). This is MTC's
  `MoTInput.segmentsContainBalls_of_coupling` argument, stated for an arbitrary cell model so that the final assembly
  applies it directly to the cone realization's cell model `CellScaling.ConeRealization.toCellModel`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Asymptotics
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-! ### Area parametrization from the every-vague-limit form -/

/-- When the dyadic area approximations of a field have a vague limit, the library's `CellScaling.lqgArea` (zero
fallback otherwise) is one. -/
theorem final_isVagueLimitC_lqgArea {γ : ℝ} {h : LQGMetric.DistC}
    (hx : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) :
    CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) (CellScaling.lqgArea γ h) := by
  simp only [CellScaling.lqgArea, hx, ↓reduceDIte]
  exact Classical.choose_spec hx

/-- **Area parametrization on a sample space.** For a γ-cone field `h = coneFieldOf γ X B B'` built from a whole-plane GFF `X` and
standard Brownian motions `B, B'` with the bundle's independence (`0 < γ < 2`), if almost surely every dyadic vague
limit `μ` of the area approximations of `h` gives the segments of a curve `c` the masses `μ(c([s, t])) = t − s`, then
almost surely so does `CellScaling.lqgArea γ h`: the vague limit exists a.s.
by `GMCFacts.coneAreaExists_holds`. -/
theorem final_ae_lqgArea_curve_of_vagueLimits {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} {B B' : ℝ≥0 → Ω → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : LQGMetric.IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P)
    {c : Ω → C(ℝ, ℂ)}
    (h : ∀ᵐ ω ∂P, ∀ μ : Measure ℂ, CellScaling.IsVagueLimitC
        (CellScaling.lqgAreaApprox γ (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) μ →
      ∀ s t : ℝ, s ≤ t → μ (c ω '' Icc s t) = ENNReal.ofReal (t - s)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, s ≤ t →
      CellScaling.lqgArea γ (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) (c ω '' Icc s t) =
        ENNReal.ofReal (t - s) := by
  filter_upwards [h, GMCFacts.coneAreaExists_holds hγ hγ2 hX hB hB' hind] with ω hω hexω
  exact hω _ (final_isVagueLimitC_lqgArea hexω)

/-- **Area-parametrization adapter.** For a cone realization of a unit-mesh model (`0 < γ < 2` is a field of the model), if almost
surely `η(0) = 0` and every dyadic vague limit `μ` of the area approximations of the cone field satisfies
`μ(η([s, t])) = t − s`, then `CellScaling.AreaParametrization` holds (`final_ae_lqgArea_curve_of_vagueLimits`). -/
theorem final_areaParametrization_of_vagueLimits {γ : ℝ} {M : MatedCRTUnitMesoModel γ}
    (C : CellScaling.ConeRealization M)
    (h : ∀ᵐ ω ∂M.coupled.family.P, C.curve ω 0 = 0 ∧
      ∀ μ : Measure ℂ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ (C.field ω)) μ →
        ∀ s t : ℝ, s ≤ t → μ (C.curve ω '' Icc s t) = ENNReal.ofReal (t - s)) :
    CellScaling.AreaParametrization C := by
  have harea := final_ae_lqgArea_curve_of_vagueLimits M.hγ.1 M.hγ.2 C.gff C.brownian C.brownian' C.indep
    (c := C.curve) (h.mono fun _ hω => hω.2)
  filter_upwards [h, harea] with ω hω hareaω
  exact ⟨hω.1, hareaω⟩

/-- **Area-parametrization adapter, in the shape of the v3 bundle fields.** If the realization's curve is a.s. a curve `η` which is
an increasing reparametrization `η = ηL ∘ φ` with `φ 0 = 0` of a curve `ηL` with `ηL 0 = 0`, and every dyadic vague
limit of the area approximations of the cone field gives `η([s, t])` mass `t − s` (the v3 field `areaParam`, R1),
then `CellScaling.AreaParametrization` holds. -/
theorem final_areaParametrization_of_reparam {γ : ℝ} {M : MatedCRTUnitMesoModel γ}
    (C : CellScaling.ConeRealization M) (ηL η : M.coupled.family.Ω → C(ℝ, ℂ))
    (hcurve : ∀ᵐ ω ∂M.coupled.family.P, C.curve ω = η ω)
    (hηL0 : ∀ᵐ ω ∂M.coupled.family.P, ηL ω 0 = 0)
    (harea : ∀ᵐ ω ∂M.coupled.family.P, (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, η ω t = ηL ω (φ t)) ∧
      ∀ μ : Measure ℂ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ (C.field ω)) μ →
        ∀ s t : ℝ, s ≤ t → μ (η ω '' Icc s t) = ENNReal.ofReal (t - s)) :
    CellScaling.AreaParametrization C := by
  apply final_areaParametrization_of_vagueLimits C
  filter_upwards [hcurve, hηL0, harea] with ω hcω h0 hω
  rcases hω with ⟨⟨φ, hφ0, hφ⟩, hall⟩
  refine ⟨?_, fun μ hμ s t hst => ?_⟩
  · rw [hcω, hφ 0, hφ0, h0]
  · rw [hcω]
    exact hall μ hμ s t hst

/-! ### GHM15 Prop 3.4: transfer along an increasing reparametrization -/

/-- The bundle's event `E_ε(R, r)` of GHM15 Prop 3.4 for a curve, written out (the body of the frozen
`MatedCRT.SegmentsContainBalls`, so that this file does not depend on the bundle's definition files). -/
def FinalSegmentBallGood (c : C(ℝ, ℂ)) (R r ε : ℝ) : Prop :=
  ∀ δ ∈ Ioc (0 : ℝ) ε, ∀ a b : ℝ, a < b → c '' Icc a b ⊆ ball 0 R →
    δ ^ (1 - r) ≤ diam (c '' Icc a b) → ∃ w : ℂ, ball w δ ⊆ c '' Icc a b

private theorem final_image_reparam_Icc {φ : ℝ ≃o ℝ} {c : C(ℝ, ℂ)} {f : ℝ → ℂ}
    (hf : ∀ t, f t = c (φ t)) (a b : ℝ) :
    f '' Icc a b = c '' Icc (φ a) (φ b) := by
  rw [show f = (c : ℝ → ℂ) ∘ φ from funext hf, Set.image_comp, φ.image_Icc]

/-- Pathwise: the segment-ball event for `c` gives Lemma 2.7's segment-ball event for any increasing reparametrization. -/
private theorem final_segmentBallEvent_of_reparam {γ : ℝ} (M : GMSLemma27.CellModel γ) {ω : M.Ω}
    {c : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ} (hf : ∀ t, M.curve ω t = c (φ t)) {R r ε : ℝ}
    (hgood : FinalSegmentBallGood c R r ε) :
    ω ∈ GMSLemma27.segmentBallEvent M R r ε := by
  intro δ hδε a b hab hball hdiam
  have himage := final_image_reparam_Icc hf a b
  rw [himage] at hball hdiam
  obtain ⟨w, hw⟩ := hgood δ hδε (φ a) (φ b) (φ.strictMono hab) hball hdiam
  exact ⟨w, δ, le_rfl, himage ▸ hw⟩

/-- **GHM15 Prop 3.4 with Remark 3.9, transferred to Lemma 2.7's interface.** If the curve of a cell model is almost surely
an increasing reparametrization of a curve `c`, and `c` satisfies the superpolynomial outer bound of the bundle field
`segmentsContainBalls`, then `GMSLemma27.SegmentsContainBalls M`. -/
theorem final_segmentsContainBalls_of_reparam {γ : ℝ} (M : GMSLemma27.CellModel γ) (c : M.Ω → C(ℝ, ℂ))
    (hrep : ∀ᵐ ω ∂M.P, ∃ φ : ℝ ≃o ℝ, ∀ t, M.curve ω t = c ω (φ t))
    (hbound : ∀ R : ℝ, 0 < R → ∀ r ∈ Ioo (0 : ℝ) 1, ∀ N : ℕ, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ¬ FinalSegmentBallGood (c ω) R r ε} ≤ ENNReal.ofReal (C * ε ^ N)) :
    GMSLemma27.SegmentsContainBalls M := by
  intro r hr R hR s
  obtain ⟨N, hsN⟩ := exists_nat_gt s
  obtain ⟨C, hC⟩ := hbound R hR r hr N
  have hdecay : 0 < (N : ℝ) - s := sub_pos.mpr hsN
  have hlim0 : Tendsto (fun ε : ℝ => ε ^ ((N : ℝ) - s)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (GMSLemma27.tendsto_rpow_nhdsGT_zero hdecay).mono_right nhdsWithin_le_nhds
  have hlim' : Tendsto (fun ε : ℝ => max C 0 * ε ^ ((N : ℝ) - s)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hlim0.const_mul (max C 0)
  have hprob : ∀ ε : ℝ, M.P (GMSLemma27.segmentBallEvent M R r ε)ᶜ ≤
      M.P {ω | ¬ FinalSegmentBallGood (c ω) R r ε} := by
    intro ε
    apply measure_mono_ae
    filter_upwards [hrep] with ω hω
    rcases hω with ⟨φ, hφ⟩
    intro hbad hgood
    exact hbad (final_segmentBallEvent_of_reparam M hφ hgood)
  rw [Asymptotics.isLittleO_iff]
  intro c' hc'
  have hsmall := hlim'.eventually (gt_mem_nhds hc')
  filter_upwards [hsmall, self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos] with ε hsmall hε hεlt
  have hεpos : 0 < ε := hε
  have hpow : 0 ≤ ε ^ N := pow_nonneg hεpos.le N
  have hCpow : 0 ≤ max C 0 * ε ^ N := mul_nonneg (le_max_right _ _) hpow
  have hCmono : C * ε ^ N ≤ max C 0 * ε ^ N :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) hpow
  have hprob' : M.P (GMSLemma27.segmentBallEvent M R r ε)ᶜ ≤ ENNReal.ofReal (max C 0 * ε ^ N) :=
    (hprob ε).trans ((hC ε hεlt).trans (ENNReal.ofReal_le_ofReal hCmono))
  have hreal : (M.P (GMSLemma27.segmentBallEvent M R r ε)ᶜ).toReal ≤ max C 0 * ε ^ N :=
    ENNReal.toReal_le_of_le_ofReal hCpow hprob'
  have hrpow : ε ^ (N : ℝ) = ε ^ s * ε ^ ((N : ℝ) - s) := by
    rw [← Real.rpow_add hεpos]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hεpos.le s)]
  calc
    (M.P (GMSLemma27.segmentBallEvent M R r ε)ᶜ).toReal ≤ max C 0 * ε ^ N := hreal
    _ = ε ^ s * (max C 0 * ε ^ ((N : ℝ) - s)) := by
      rw [← Real.rpow_natCast ε N, hrpow]
      ring
    _ ≤ c' * ε ^ s := by
      simpa only [mul_comm c' (ε ^ s)] using
        mul_le_mul_of_nonneg_left (le_of_lt hsmall) (Real.rpow_nonneg hεpos.le s)

end MatedCRTHarmonic.MesoModel

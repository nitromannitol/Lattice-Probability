/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P6B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P5A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P6A
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# DFGPS Thm 1.2, P-4 item 1: Axioms I and III for a GFF plus a continuous function

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1339–1386 (Axioms I, III are checked for `h + f`, `h` a GFF, through Lemma 2.12 and the
Weyl-scaling identity). Steps:

* `T12Good` — the conclusions of the coupling for the glued metric `patchT`: at every normalized
  whole-plane GFF, a.s. `patchT h` is a length metric and the LFPP converges to it locally
  uniformly (`t12Good_of_coupling`, as in `ae_weyl_patchT_of_coupling`).
* `isGFFPlusCont_decomp` — a whole-plane GFF plus a continuous `f₀` is
  `h₀ + (f₀ + h_1(0))` with `h₀ := (h − f₀) − (h − f₀)_1(0)` a normalized whole-plane GFF.
* `ae_patchT_isGFFPlusCont` — hence a.s. `patchT h = e^{ξ g}·patchT h₀` (Lemma 2.12 via
  `ae_patchT_addFun_eq_weyl`), giving **Axiom I** (`weylMetric_isLength`) and **Axiom III**
  (`weylScale_weylMetric`, composition of Weyl scalings).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- conclusions of the coupling for the glued metric `patchT` along `εs` -/
def T12Good (γ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ k, 0 < εs k) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWPGFF h P →
      (∀ᵐ ω ∂P, (patchT (xiGamma γ) εs hεs (h ω)).IsLength) ∧
      ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n p => (aEpsDF (xiGamma γ) (εs n))⁻¹ * lfppDist (xiGamma γ) (εs n) (h ω) p)
        (fun p => (patchT (xiGamma γ) εs hεs (h ω)).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)

theorem t12Good_of_coupling (h28 : Lem2_8) (HG : Lem2_1GffApprox.{0})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} {Dh : Ω → ContMetric} (hh : IsNormalizedWPGFF h P)
    {εs : ℕ → ℝ} (hεs : ∀ k, 0 < εs k) (hε0 : Tendsto εs atTop (𝓝 0))
    (hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength)
    (hconv : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF (xiGamma γ) (εs n))⁻¹ * lfppDist (xiGamma γ) (εs n) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) :
    T12Good γ εs hεs := by
  intro Ω' _ P' _ h' hh'
  set ξ := xiGamma γ
  have hcont : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {h₀ : Ω₀ → DistC},
      IsNormalizedWPGFF h₀ P₀ → ∀ᵐ ω ∂P₀, ∀ k, Continuous (heatMollify (εs k) (h₀ ω)) :=
    fun hh₀ => ae_all_iff.2 fun k =>
      (hh₀.1.ae_tendstoLocallyUniformly_heatMollify _ (hεs k).ne').mono fun ω hω => hω.2
  have hA : ∀ᵐ ω ∂P, Tendsto (fun k => lfppC ξ (εs k) (h ω)) atTop
      (𝓝 ((fun g => (patchT ξ εs hεs g).1) (h ω))) := by
    filter_upwards [hconv, hcont hh, ae_patchT_eq HG hh hεs hε0 hlen hconv] with ω hcv hc hP
    show Tendsto _ atTop (𝓝 (patchT ξ εs hεs (h ω)).1)
    rw [hP]
    refine tendsto_contMap_of_tendstoUniformlyOn_balls fun R hR0 => ?_
    refine (hcv R hR0).congr (Eventually.of_forall fun k p _ => ?_)
    show _ = lfppC ξ (εs k) (h ω) p
    rw [lfppC_apply_of_continuous (hc k) p]
    rfl
  have hA' := ae_tendsto_lfppC_transfer hh hh' hεs
    (measurable_subtype_coe.comp measurable_patchT) hA
  have hconv' : ∀ᵐ ω ∂P', ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) (h' ω) p)
      (fun p => (patchT ξ εs hεs (h' ω)).1 p) atTop
      (closedBall 0 R ×ˢ closedBall 0 R) := by
    filter_upwards [hA', hcont hh'] with ω h1 h2 R _
    exact tendstoUniformlyOn_of_tendsto_lfppC h2 h1 R
  exact ⟨(ae_isLength_agree h28 hγ hγ2 P' (fun ω => h' ω)
    (fun ω => patchT ξ εs hεs (h' ω)) εs (isGFFPlusBddCont_of_normalizedWP hh') hεs hε0
    hconv').mono fun ω hω => hω.1, hconv'⟩

/-- `ofCont` is additive -/
theorem ofCont_add' (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

theorem addFun_addFun' (h : DistC) (f g : C(ℂ, ℝ)) :
    addFun (addFun h f) g = addFun h (f + g) := by
  simp only [addFun, ofCont_add', add_assoc]

/-- **GFF plus continuous = normalized GFF plus continuous** -/
theorem isGFFPlusCont_decomp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusCont h P) :
    ∃ (h₀ : Ω → DistC) (g : Ω → C(ℂ, ℝ)), IsNormalizedWPGFF h₀ P ∧ Measurable g ∧
      ∀ ω, h ω = addFun (h₀ ω) (g ω) := by
  obtain ⟨-, f₀, hf₀, hk⟩ := hh
  set k : Ω → DistC := fun ω => h ω - ofCont (f₀ ω)
  have hN := measurable_circleAvg_left 1 0
  have hcm : Measurable fun ω => circleAvg (k ω) 1 0 := hN.comp hk.measurable
  refine ⟨fun ω => addConst (k ω) (-circleAvg (k ω) 1 0),
    fun ω => f₀ ω + ContinuousMap.const ℂ (circleAvg (k ω) 1 0), ⟨hk.addConst hcm.neg, ?_⟩,
    ?_, fun ω => ?_⟩
  · filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hk] with ω hω
    rw [hω]; ring
  · have hc : Measurable fun ω => ContinuousMap.const ℂ (circleAvg (k ω) 1 0) :=
      (ContinuousMap.continuous_const'.measurable).comp hcm
    exact hf₀.add hc
  · simp only [addConst, addFun_addFun']
    rw [addFun, ofCont_add', ofCont_add']
    simp only [k]
    have : ofCont (ContinuousMap.const ℂ (-circleAvg (h ω - ofCont (f₀ ω)) 1 0)) +
        ofCont (ContinuousMap.const ℂ (circleAvg (h ω - ofCont (f₀ ω)) 1 0)) = 0 := by
      rw [← ofCont_add']
      have e : ContinuousMap.const ℂ (-circleAvg (h ω - ofCont (f₀ ω)) 1 0) +
          ContinuousMap.const ℂ (circleAvg (h ω - ofCont (f₀ ω)) 1 0) = 0 := by
        ext; simp
      rw [e]; ext φ; simp [ofCont]
    rw [add_left_comm _ (ofCont (f₀ ω)), this, add_zero, sub_add_cancel]

/-- a.s. `patchT h = e^{ξ g}·patchT h₀` for `h = h₀ + g` (Lemma 2.12) -/
theorem ae_patchT_isGFFPlusCont (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsNormalizedWPGFF h₀ P) :
    ∀ᵐ ω ∂P, ∃ hD : (patchT (xiGamma γ) εs hεs (h₀ ω)).IsLength, ∀ f : C(ℂ, ℝ),
      patchT (xiGamma γ) εs hεs (addFun (h₀ ω) f) =
        weylMetric (xiGamma γ) f (patchT (xiGamma γ) εs hεs (h₀ ω)) hD :=
  ae_patchT_addFun_eq_weyl HG h12 hγ hγ2 hh₀ hεs hε0 (hG P h₀ hh₀).1 (hG P h₀ hh₀).2

/-- **Axioms I and III** for `patchT` at a GFF plus a continuous function -/
theorem ae_length_weyl_isGFFPlusCont (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P) :
    (∀ᵐ ω ∂P, (patchT (xiGamma γ) εs hεs (h ω)).IsLength) ∧
    ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), ∀ z w : ℂ,
      weylScale (xiGamma γ) f (patchT (xiGamma γ) εs hεs (h ω)) z w =
        ENNReal.ofReal ((patchT (xiGamma γ) εs hεs (addFun (h ω) f)).1 (z, w)) := by
  obtain ⟨h₀, g, hh₀, -, hdec⟩ := isGFFPlusCont_decomp hh
  have H := ae_patchT_isGFFPlusCont HG h12 hγ hγ2 hε0 hG hh₀
  refine ⟨H.mono fun ω ⟨hD, hW⟩ => ?_, H.mono fun ω ⟨hD, hW⟩ f z w => ?_⟩
  · rw [hdec ω, hW]; exact weylMetric_isLength hD
  · rw [hdec ω, hW, addFun_addFun', hW, weylScale_weylMetric, weylMetric_spec]

end LQGMetric.DFGPS.T12

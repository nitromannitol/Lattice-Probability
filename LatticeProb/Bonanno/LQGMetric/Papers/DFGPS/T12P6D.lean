/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P6D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P6C
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20TranslB
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate

/-!
# DFGPS Thm 1.2, P-4 item 3: translation invariance (Axiom IV′) for `patchT`

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1339–1386 ("Axiom IV′ is immediate from the translation invariance of the law of `h` modulo
additive constant and of LFPP", with Lemma 2.20's translation step T:1323–1324). Steps:

* `ae_patchT_translate_norm` — normalized `h₀`: the LFPP identity
  `L220.ae_lfppResc_translate` (`r = 1`) passes to the a.s. limits (`T12Good` at `h₀` and at the
  normalized `h₀(· + z) − h₀,1(z)`), and the constant is removed with Axioms I/III
  (`dist_addConst_of_weyl`);
* `ae_patchT_translate` — a GFF plus a continuous function `h = h₀ + g`: Axiom III at
  `h₀(· + z)` and at `h₀`, and `weylScale_affine` (Weyl scaling commutes with translation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP GM.Tight

theorem contMetric_nonneg (D : ContMetric) (p : ℂ × ℂ) : 0 ≤ D.1 p :=
  dist_nonneg (x := D.pt p.1) (y := D.pt p.2)

theorem isGFFPlusCont_of_wp' {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) : IsGFFPlusCont h P := by
  refine ⟨hh.measurable, fun _ => 0, measurable_const, ?_⟩
  have h0 : ofCont 0 = 0 := by ext φ; simp [ofCont]
  simpa [h0] using hh

theorem ae_tendsto_lfppC_patchT {γ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) :
    ∀ᵐ ω ∂P, Tendsto (fun k => lfppC (xiGamma γ) (εs k) (h ω)) atTop
      (𝓝 (patchT (xiGamma γ) εs hεs (h ω)).1) := by
  have hcont : ∀ᵐ ω ∂P, ∀ k, Continuous (heatMollify (εs k) (h ω)) :=
    ae_all_iff.2 fun k =>
      (hh.1.ae_tendstoLocallyUniformly_heatMollify _ (hεs k).ne').mono fun ω hω => hω.2
  filter_upwards [(hG P h hh).2, hcont] with ω hcv hc
  refine tendsto_contMap_of_tendstoUniformlyOn_balls fun R hR0 => ?_
  refine (hcv R hR0).congr (Eventually.of_forall fun k p _ => ?_)
  show _ = lfppC (xiGamma γ) (εs k) (h ω) p
  rw [lfppC_apply_of_continuous (hc k) p]
  rfl

/-- translation for a normalized GFF -/
theorem ae_patchT_translate_norm (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h₀ : Ω → DistC} (hh₀ : IsNormalizedWPGFF h₀ P)
    (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (patchT (xiGamma γ) εs hεs (affineComp 1 z (h₀ ω))).1 (u, v) =
      (patchT (xiGamma γ) εs hεs (h₀ ω)).1 (u + z, v + z) := by
  set ξ := xiGamma γ
  have hT : IsWholePlaneGFF (fun ω => affineComp 1 z (h₀ ω)) P := hh₀.1.affineComp one_pos z
  have hcm : Measurable fun ω => circleAvg (h₀ ω) 1 z :=
    (measurable_circleAvg_left 1 z).comp hh₀.1.measurable
  have hg : IsNormalizedWPGFF
      (fun ω => addConst (affineComp 1 z (h₀ ω)) (-circleAvg (h₀ ω) 1 z)) P := by
    refine ⟨hT.addConst hcm.neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst hT 0 one_pos] with ω h1
    rw [h1, circleAvg_affineComp_one]; ring
  obtain ⟨hlT, hwT⟩ := ae_length_weyl_isGFFPlusCont HG h12 hγ hγ2 hε0 hG (isGFFPlusCont_of_wp' hT)
  have hid := ae_all_iff.2 fun k => L220.ae_lfppResc_translate hh₀.1 ξ (hεs k) one_pos z
  filter_upwards [hid, ae_tendsto_lfppC_patchT hG hg, ae_tendsto_lfppC_patchT hG hh₀, hg.2,
    hlT, hwT] with ω hk h1 h2 hc0 hl hw u v
  set c := circleAvg (h₀ ω) 1 z
  set g := addConst (affineComp 1 z (h₀ ω)) (-c)
  have t1 : Tendsto (fun k => L220.lfppResc ξ (εs k) 1 0 g) atTop
      (𝓝 (Real.exp (-ξ * circleAvg g 1 0) • (patchT ξ εs hεs g).1.comp (affArgs 1 0))) :=
    (((ContinuousMap.continuous_precomp (affArgs 1 0)).tendsto _).comp h1).const_smul _
  have t2 : Tendsto (fun k => L220.lfppResc ξ (εs k) 1 z (h₀ ω)) atTop
      (𝓝 (Real.exp (-ξ * c) • (patchT ξ εs hεs (h₀ ω)).1.comp (affArgs 1 z))) :=
    (((ContinuousMap.continuous_precomp (affArgs 1 z)).tendsto _).comp h2).const_smul _
  have heq := tendsto_nhds_unique t1 (t2.congr fun k => (hk k).symm)
  have hp := congrArg (fun F : C(ℂ × ℂ, ℝ) => F (u, v)) heq
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, affArgs_apply, smul_eq_mul,
    Complex.ofReal_one, one_mul, add_zero] at hp
  rw [show circleAvg g 1 0 = 0 from hc0, mul_zero, Real.exp_zero, one_mul] at hp
  have hs := dist_addConst_of_weyl (Dm := patchT ξ εs hεs) hl hw (-c) u v
  rw [hp] at hs
  have hx : Real.exp (ξ * -c) * (patchT ξ εs hεs (affineComp 1 z (h₀ ω))).1 (u, v) =
      Real.exp (ξ * -c) * (patchT ξ εs hεs (h₀ ω)).1 (u + z, v + z) := by
    rw [← hs, mul_neg, neg_mul]
  exact mul_left_cancel₀ (Real.exp_pos _).ne' hx

/-- **Axiom IV′** (translation invariance) for `patchT` at a GFF plus a continuous function -/
theorem ae_patchT_translate (HG : Lem2_1GffApprox.{0}) (h12 : Lem2_12) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (hG : T12Good γ εs hεs) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (patchT (xiGamma γ) εs hεs (affineComp 1 z (h ω))).1 (u, v) =
      (patchT (xiGamma γ) εs hεs (h ω)).1 (u + z, v + z) := by
  obtain ⟨h₀, g, hh₀, -, hdec⟩ := isGFFPlusCont_decomp hh
  have hT : IsWholePlaneGFF (fun ω => affineComp 1 z (h₀ ω)) P := hh₀.1.affineComp one_pos z
  obtain ⟨-, hwT⟩ := ae_length_weyl_isGFFPlusCont HG h12 hγ hγ2 hε0 hG (isGFFPlusCont_of_wp' hT)
  obtain ⟨-, hw0⟩ := ae_length_weyl_isGFFPlusCont HG h12 hγ hγ2 hε0 hG
    (isGFFPlusCont_of_wp' hh₀.1)
  filter_upwards [ae_patchT_translate_norm HG h12 hγ hγ2 hε0 hG hh₀ z, hwT, hw0]
    with ω htr hwT hw0 u v
  have hA : patchT (xiGamma γ) εs hεs (affineComp 1 z (h₀ ω)) =
      (patchT (xiGamma γ) εs hεs (h₀ ω)).affine 1 one_ne_zero z :=
    Subtype.ext (ContinuousMap.ext fun p => by
      rw [ContMetric.affine_apply, htr p.1 p.2]
      simp [affinePt_apply, add_comm])
  have e1 := hwT ((g ω).comp (affinePt 1 z)) u v
  rw [hA, weylScale_affine, hw0] at e1
  have := (ENNReal.ofReal_eq_ofReal_iff (contMetric_nonneg _ _) (contMetric_nonneg _ _)).1 e1
  rw [hdec ω, GM.affineComp_addFun one_pos, ← this]
  simp only [affinePt_apply, Complex.ofReal_one, one_mul]

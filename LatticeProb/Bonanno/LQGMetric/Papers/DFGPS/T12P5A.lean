/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P5A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P4B
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P0
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2: Axiom III for every normalized GFF (law transfer)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1343–1356: the limit metric is a measurable function of the field, so a.s. statements about
`(h, D_h)` in the Skorokhod coupling hold for every normalized whole-plane GFF (the law of `h` is
`normGFFLaw`). Implicit in the paper.

* `ae_tendsto_lfppC_transfer` — a.s. convergence `𝔞⁻¹D^{ε_k}_h → G(h)` for a measurable `G`
  transfers between any two normalized whole-plane GFFs (measurable versions of `lfppC`,
  `measurableSet_tendsto_fun`, `normGFFLaw_eq`).
* `tendstoUniformlyOn_of_tendsto_lfppC` — the `C(ℂ × ℂ, ℝ)` form gives the uniform form.
* `ae_weyl_patchT_of_coupling` — **Axiom III** for `patchT` at every normalized GFF, from a
  coupling in which the LFPP converges a.s. along `ε_k`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- **law transfer of a.s. LFPP convergence** between normalized whole-plane GFFs -/
theorem ae_tendsto_lfppC_transfer {ξ : ℝ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWPGFF h P) (hh' : IsNormalizedWPGFF h' P')
    {εs : ℕ → ℝ} (hεs : ∀ k, 0 < εs k) {G : DistC → C(ℂ × ℂ, ℝ)} (hG : Measurable G)
    (hA : ∀ᵐ ω ∂P, Tendsto (fun k => lfppC ξ (εs k) (h ω)) atTop (𝓝 (G (h ω)))) :
    ∀ᵐ ω ∂P', Tendsto (fun k => lfppC ξ (εs k) (h' ω)) atTop (𝓝 (G (h' ω))) := by
  have : PolishSpace C(ℂ × ℂ, ℝ) := polishSpace_continuousMap _ _
  have hm := hh.1.measurable.aemeasurable (μ := P)
  have hm' := hh'.1.measurable.aemeasurable (μ := P')
  have e : P.map h = P'.map h' := (GM.normGFFLaw_eq hh).symm.trans (GM.normGFFLaw_eq hh')
  have : IsProbabilityMeasure (P.map h) := (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  have hμ : IsNormalizedWPGFF (id : DistC → DistC) (P.map h) :=
    isNormalizedWPGFF_of_map_eq measurable_id hh (by rw [Measure.map_id])
  have hmk : ∀ k, AEMeasurable (lfppC ξ (εs k)) (P.map h) := fun k =>
    aemeasurable_lfppC (isGFFPlusBddCont_of_normalizedWP hμ) (hεs k).ne'
  let L : ℕ → DistC → C(ℂ × ℂ, ℝ) := fun k => (hmk k).mk
  have hS : MeasurableSet {g | Tendsto (fun k => L k g) atTop (𝓝 (G g))} :=
    measurableSet_tendsto_fun (fun k => (hmk k).measurable_mk) hG
  have hEq : ∀ᵐ g ∂(P.map h), ∀ k, L k g = lfppC ξ (εs k) g :=
    ae_all_iff.2 fun k => (hmk k).ae_eq_mk.symm
  have hPS : ∀ᵐ ω ∂P, h ω ∈ {g | Tendsto (fun k => L k g) atTop (𝓝 (G g))} := by
    filter_upwards [hA, ae_of_ae_map hm hEq] with ω hω hL
    show Tendsto (fun k => L k (h ω)) atTop (𝓝 (G (h ω)))
    simpa only [hL] using hω
  have hμS := (ae_map_iff hm hS).2 hPS
  rw [e] at hμS hEq
  filter_upwards [ae_of_ae_map hm' hμS, ae_of_ae_map hm' hEq] with ω h1 h2
  simpa only [mem_ofPred_eq, h2] using h1

/-- convergence of `lfppC` in `C(ℂ × ℂ, ℝ)` gives the uniform form on the squares `B̄_R(0)²` -/
theorem tendstoUniformlyOn_of_tendsto_lfppC {ξ : ℝ} {εs : ℕ → ℝ} {g : DistC}
    (hc : ∀ k, Continuous (heatMollify (εs k) g)) {D : C(ℂ × ℂ, ℝ)}
    (hA : Tendsto (fun k => lfppC ξ (εs k) g) atTop (𝓝 D)) (R : ℝ) :
    TendstoUniformlyOn (fun n p => (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) g p) (fun p => D p)
      atTop (closedBall 0 R ×ˢ closedBall 0 R) := by
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformly_iff_forall_isCompact] at hA
  refine (hA _ ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).congr
    (Eventually.of_forall fun k p _ => ?_)
  show lfppC ξ (εs k) g p = _
  rw [lfppC_apply_of_continuous (hc k) p]
  rfl

end LQGMetric.DFGPS.T12

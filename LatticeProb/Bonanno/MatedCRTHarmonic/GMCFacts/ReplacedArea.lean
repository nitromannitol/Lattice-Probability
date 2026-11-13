/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.ReplacedArea at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.Replaced
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.NoAtom
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4D
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3B

/-!
# Normalization and LQG measure of the replaced field

* `ae_circleAvg_replField_one`: if `W(0) = 0`, the replaced field `X̃ = lateral(X) + W(−log|·|)` has
  `X̃_1(0) = 0` a.s. (the lateral part has mean zero on `∂𝔻`, and `W(−log|·|) = W(0) = 0` there);
  hence `X̃` is a whole-plane GFF normalized by `h_1(0) = 0` (`isNormalizedWPGFF_replField`).
* `exists_isLQGAreaOf`: for every normalized whole-plane GFF `Y` (LQGMetric's `IsNormalizedWPGFF`) and `γ ∈ (0, 2)`,
  there is a measurable circle-average process `H` of `Y` (`IsGFFCircleAverage`) such that the ported MoT whole-plane
  LQG measure `qAreaC γ Y` is the LQG measure of `H` in the sense (`IsLQGAreaOf`): existence of the vague limit is
  the ported MoT `ConeArea4D.ae_areaGood_univ` (Duplantier–Sheffield arXiv:0808.1560 Prop 1.1), and the approximations
  of `H` and of `Y` agree a.s. (Fubini).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMCFacts

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

lemma mollAvg_add (x y : DistC) (n : ℕ) (z : ℂ) (r : ℝ) :
    mollAvg (x + y) n z r = mollAvg x n z r + mollAvg y n z r := by
  simp only [mollAvg_eq, add_apply]

lemma continuousOn_radialW (w : C(ℝ, ℝ)) : ContinuousOn (radialW w) {z : ℂ | z ≠ 0} := by
  refine w.continuous.comp_continuousOn ?_
  refine (Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz => ?_).neg
  exact norm_ne_zero_iff.2 hz

lemma sphere_one_subset_ne : sphere (0 : ℂ) 1 ⊆ {z : ℂ | z ≠ 0} := fun z hz => by
  rw [mem_sphere_zero_iff_norm] at hz
  exact norm_ne_zero_iff.1 (by rw [hz]; exact one_ne_zero)

/-- **Normalization of the replaced field**: `X̃_1(0) = 0` a.s. when `W(0) = 0`. -/
theorem ae_circleAvg_replField_one (hX : IsWholePlaneGFF X P) {W : Ω → C(ℝ, ℝ)}
    (hW0 : ∀ ω, W ω 0 = 0) : ∀ᵐ ω ∂P, circleAvg (replField X W ω) 1 0 = 0 := by
  have := hX.gaussian.isProbabilityMeasure
  obtain ⟨H, hH, hR⟩ := ConeArea7.ae_radialFun_eq_version hX
  filter_upwards [hR, hH.ae_eq 1 one_pos 0, ae_tendsto_mollAvg hX 0 one_pos,
    ConeArea4.ae_radial_R2 hX] with ω hR1 hH1 ⟨a, ha⟩ hR2
  set g : ℂ → ℝ := fun z => H ‖z‖ 0 ω
  obtain ⟨R, -, -, hRe, hRl⟩ := hR2
  have hloc : LocallyIntegrable (radialFun (X ω)) volume := hRl.congr hRe.symm
  have hgl : LocallyIntegrable (fun z => -g z) volume := (hloc.congr hR1).neg
  have hgc : ContinuousOn (fun z => -g z) {z : ℂ | z ≠ 0} := by
    refine ((hH.cont ω).comp (f := fun z : ℂ => ((‖z‖, (0 : ℂ)) : ℝ × ℂ))
      (by fun_prop : Continuous fun z : ℂ => ((‖z‖, (0 : ℂ)) : ℝ × ℂ)).continuousOn
      fun z hz => ⟨norm_pos_iff.2 hz, mem_univ _⟩).neg
  have hca : circleAvg (X ω) 1 0 = a := circleAvg_eq_of_tendsto ha
  have hcirc : Real.circleAverage (fun z => -g z) 0 1 = -a := by
    refine Real.circleAverage_const_on_circle fun z hz => ?_
    rw [abs_one, mem_sphere_zero_iff_norm] at hz
    simp only [g, hz]
    rw [hH1, hca]
  -- the lateral part is `X + ofFunC (−g)`
  have hlat : lateralPartC (X ω) = X ω + ofFunC (fun z => -g z) := by
    rw [lateralPartC, ConeArea3.ofFunC_congr_ae hR1, show (fun z => -g z) = -g from rfl, ofFunC,
      ofFunC, Distribution.ofFun_neg, sub_eq_add_neg]
  have hlatT : Tendsto (fun n => mollAvg (lateralPartC (X ω)) n 0 1) atTop (𝓝 0) := by
    rw [hlat]
    simp only [mollAvg_add]
    have := ha.add (ConeArea3.tendsto_mollAvg_ofFunC hgl isOpen_ne hgc one_pos sphere_one_subset_ne)
    rwa [hcirc, add_neg_cancel] at this
  by_cases hWl : LocallyIntegrable (radialW (W ω)) volume
  · rw [replField, ConeArea3.circleAvg_add_ofFunC hWl isOpen_ne (continuousOn_radialW (W ω)) one_pos
      sphere_one_subset_ne hlatT, circleAvg_eq_of_tendsto hlatT, zero_add]
    refine Real.circleAverage_const_on_circle fun z hz => ?_
    rw [abs_one, mem_sphere_zero_iff_norm] at hz
    simp only [radialW, hz, Real.log_one, neg_zero, hW0]
  · have h0 : ofFunC (radialW (W ω)) = 0 := by
      rw [ofFunC]
      exact Distribution.ofFun_eq_zero (by rwa [TopologicalSpace.Opens.coe_top, locallyIntegrableOn_univ])
    rw [replField, h0, add_zero]
    exact circleAvg_eq_of_tendsto hlatT

/-- The dyadic radii of the cell-model approximation and of the ported MoT area approximation agree. -/
lemma lqgApprox_eq_areaApproxC {Ω' : Type*} {H : ℝ → ℂ → Ω' → ℝ} {Y : Ω' → DistC} (γ : ℝ) (k : ℕ)
    {ω : Ω'} (h : ∀ᵐ z ∂(volume : Measure ℂ),
      H (QuantumZipper.radius k) z ω = circleAvg (Y ω) (QuantumZipper.radius k) z) :
    GMSLemma27.lqgApprox γ H k ω = areaApproxC γ (Y ω) k := by
  rw [GMSLemma27.lqgApprox, areaApproxC, dyadicRadius_eq_radius]
  refine withDensity_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz]

/-- **The LQG measure of a normalized whole-plane GFF in the sense**: there is a measurable circle-average process
`H` of `Y` whose LQG measure (`IsLQGAreaOf`) is the ported MoT whole-plane measure `qAreaC γ Y`. -/
theorem exists_isLQGAreaOf {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGDimension.IsGFFCircleAverage H P ∧ (∀ r z, Measurable (H r z)) ∧
      (∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (Y ω) r z) ∧
      GMSLemma27.IsLQGAreaOf γ H (fun ω => qAreaC γ (Y ω)) P := by
  have := hY.1.gaussian.isProbabilityMeasure
  obtain ⟨H₀, hH₀, -, hH₀ae⟩ := exists_isGFFCircleAverage_normalized hY
  obtain ⟨H, hH, hHm, hHpath⟩ := exists_measurable_version hH₀
  have hHae : ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (Y ω) r z :=
    fun r hr z => by
      filter_upwards [hHpath r hr, hH₀ae r hr z] with ω h1 h2
      rw [h1 z, h2]
  -- the approximations agree a.s.
  have happ : ∀ᵐ ω ∂P, ∀ k, GMSLemma27.lqgApprox γ H k ω = areaApproxC γ (Y ω) k := by
    rw [ae_all_iff]
    intro k
    set r := QuantumZipper.radius k
    have hr : 0 < r := QuantumZipper.radius_pos k
    have hS : MeasurableSet {p : Ω × ℂ | H r p.2 p.1 = circleAvg (Y p.1) r p.2} := by
      refine measurableSet_eq_fun ?_ ?_
      · exact (measurable_uncurry_coord hH hHm hr).comp (measurable_snd.prodMk measurable_fst)
      · exact measurable_circleAvg.comp (f := fun p : Ω × ℂ => (Y p.1, r, p.2))
          ((hY.1.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
    have h : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), H r z ω = circleAvg (Y ω) r z := by
      rw [Measure.ae_ae_comm hS]
      exact Eventually.of_forall fun z => hHae r hr z
    filter_upwards [h] with ω hω
    exact lqgApprox_eq_areaApproxC γ k hω
  refine ⟨H, hH, hHm, hHae, ?_⟩
  filter_upwards [happ, ConeArea4.ae_areaGood_univ hY.1 hγ hγ2] with ω h1 h2
  refine ⟨inferInstance, fun f hf hfs => ?_⟩
  have hv := ConeArea.isVagueLimitOn_qAreaC h2.1
  simp only [h1]
  exact hv.2.2 f hf hfs (subset_univ _)

end MatedCRTHarmonic.GMCFacts

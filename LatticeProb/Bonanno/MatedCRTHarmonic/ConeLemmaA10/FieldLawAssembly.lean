/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.FieldLawAssembly at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Changed for Lean v4.35: eLpNorm_one_eq_lintegral_enorm takes the measurability argument; MemLp is now the bound eLpNorm < ∞ and UniformIntegrable no longer contains measurability. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaExactMass
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaTestL1
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3B
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLimit
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgVar
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.DistNormalization
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.LimitPassage
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CircleAvgApproxTest
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CompactTestRootMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CylinderIntegralLimit
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteProcessMixture
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteDensityScheffe

/-!
# Exact area normalization for whole-plane rooting

The rooted-field identity is normalized by the mean mass of the unit disk. This adapter proves
that mean exactly, using a measurable version of the GFF circle-average process and the existing
compact-test first-moment theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA
/-- Multiplication by a bounded observable preserves convergence of densities in `L¹`. -/
theorem tendsto_integral_mul_of_abs_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : ℕ → X → ℝ} {g F : X → ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ n, Integrable (G n) μ) (hg : Integrable g μ)
    (hF : AEStronglyMeasurable F μ)
    (hFbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ B)
    (hL1 : Tendsto (fun n => ∫ x, |G n x - g x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, G n x * F x ∂μ) atTop (𝓝 (∫ x, g x * F x ∂μ)) := by
  have hGF : ∀ n, Integrable (fun x => G n x * F x) μ := by
    intro n
    have hmul := (hG n).bdd_mul hF hFbound
    exact hmul.congr (ae_of_all _ fun x => by ring)
  have hgf : Integrable (fun x => g x * F x) μ := by
    have hmul := hg.bdd_mul hF hFbound
    exact hmul.congr (ae_of_all _ fun x => by ring)
  have hdiffInt : ∀ n, Integrable (fun x => (G n x - g x) * F x) μ := by
    intro n
    have hmul := ((hG n).sub hg).bdd_mul hF hFbound
    simpa only [Pi.sub_apply, mul_comm] using hmul
  have hbound : ∀ n, |∫ x, G n x * F x ∂μ - ∫ x, g x * F x ∂μ| ≤
      B * ∫ x, |G n x - g x| ∂μ := by
    intro n
    rw [← integral_sub (hGF n) hgf]
    have hEq : (∫ x, G n x * F x - g x * F x ∂μ) =
        ∫ x, (G n x - g x) * F x ∂μ :=
      integral_congr_ae (μ := μ) (Filter.Eventually.of_forall fun x => by ring)
    calc
      |∫ x, G n x * F x - g x * F x ∂μ| =
          |∫ x, (G n x - g x) * F x ∂μ| := by rw [hEq]
      _ ≤
          ∫ x, |(G n x - g x) * F x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, |G n x - g x| * B ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
        · simpa only [Pi.sub_apply, mul_comm] using (((hG n).sub hg).abs.const_mul B)
        · filter_upwards [hFbound] with x hx
          calc
            |(G n x - g x) * F x| = |G n x - g x| * ‖F x‖ := by
              rw [abs_mul, Real.norm_eq_abs]
            _ ≤ |G n x - g x| * B := by
              exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ = B * ∫ x, |G n x - g x| ∂μ := by
        rw [integral_mul_const]
        ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hL1' : Tendsto (fun n => B * ∫ x, |G n x - g x| ∂μ) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hL1)
  refine squeeze_zero_norm (fun n => ?_) hL1'
  simpa [Real.norm_eq_abs] using hbound n

/-- Integral form of the finite-stage Cameron--Martin rooting identity. It follows by evaluating
the already-proved equality of complete mean-zero pairing-process laws. -/
theorem integral_finiteCircleTiltMixture_eq_covShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistC}
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hh : LQGMetric.IsNormalizedWPGFF h P) (γ : ℝ) (n : ℕ) (ε : ℝ)
    (I : Finset LQGMetric.TestC0) {F : (I → ℝ) → ℝ} (hF : Measurable F) :
    ∫ p : Ω × ℂ, F (I.restrict (LQGMetric.pair0 (h p.1))) ∂
        ((P.prod ν).withDensity fun p =>
          finiteCircleDensity (h := h) γ n p.2 ε p.1) =
      ∫ p : Ω × ℂ, F (I.restrict fun ψ =>
        LQGMetric.pair0 (h p.1) ψ + γ * LQGMetric.logCov ψ.1
          (finiteCircleIndex n p.2 ε).1) ∂(P.prod ν) := by
  let X : Ω × ℂ → I → ℝ := fun p => I.restrict (LQGMetric.pair0 (h p.1))
  let Y : Ω × ℂ → I → ℝ := fun p => I.restrict fun ψ =>
    LQGMetric.pair0 (h p.1) ψ + γ * LQGMetric.logCov ψ.1
      (finiteCircleIndex n p.2 ε).1
  let ρ : Measure (Ω × ℂ) := (P.prod ν).withDensity fun p =>
    finiteCircleDensity (h := h) γ n p.2 ε p.1
  have hX : Measurable X := by
    dsimp [X]
    exact (Finset.measurable_restrict I).comp <|
      measurable_pi_iff.2 fun ψ =>
        ((LQGMetric.measurable_evalDist ψ.1).comp hh.1.measurable).comp measurable_fst
  have hY : Measurable Y := by
    dsimp [Y]
    exact (Finset.measurable_restrict I).comp <| measurable_pi_iff.2 fun ψ =>
      (((LQGMetric.measurable_evalDist ψ.1).comp hh.1.measurable).comp measurable_fst).add
        ((measurable_finiteCircleCovShift hh γ n ε ψ).comp measurable_snd)
  have hlaw := map_finiteCircleTiltMixture_restrict_eq_covShift (ν := ν) hh γ n ε I
  have hlaw' : ρ.map X = (P.prod ν).map Y := by
    simpa only [ρ, X, Y] using hlaw
  calc
    ∫ p : Ω × ℂ, F (X p) ∂ρ = ∫ x, F x ∂(ρ.map X) :=
      (integral_map hX.aemeasurable
        (hF.aestronglyMeasurable (μ := ρ.map X))).symm
    _ = ∫ x, F x ∂((P.prod ν).map Y) := by rw [hlaw']
    _ = ∫ p : Ω × ℂ, F (Y p) ∂(P.prod ν) :=
      integral_map hY.aemeasurable
        (hF.aestronglyMeasurable (μ := (P.prod ν).map Y))

/-- At fixed circle radius, the limiting Wick density has exactly the cylinder law given by the
log-potential covariance shift. This assembles finite Gaussian tilting, the product Scheffé
limit, and the bounded-observable cylinder limit. -/
theorem integral_circleAvgDensity_mul_cylinder_eq_logPotShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistC}
    (hh : LQGMetric.IsNormalizedWPGFF h P)
    {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hagree : ∀ r, 0 < r → ∀ z,
      (fun ω => H r z ω) =ᵐ[P]
        fun ω => LQGMetric.circleAvg (h ω) r z)
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ + ε < 1)
    (I : Finset LQGMetric.TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) (hFbounded : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) :
    ∫ p : Ω × ℂ,
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg (h p.1) ε p.2) *
          F (I.restrict (LQGMetric.pair0 (h p.1))) ∂(P.prod ν) =
      ∫ p : Ω × ℂ, F (I.restrict fun ψ =>
        LQGMetric.pair0 (h p.1) ψ + γ *
          (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) p.2 ε -
            Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1)) ∂(P.prod ν) := by
  let μ : Measure (Ω × ℂ) := P.prod ν
  let d : ℕ → Ω × ℂ → ℝ≥0∞ := fun n p =>
    finiteCircleDensity (h := h) γ n p.2 ε p.1
  let G : ℕ → Ω × ℂ → ℝ := fun n p => (d n p).toReal
  let g : Ω × ℂ → ℝ := fun p =>
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg (h p.1) ε p.2)
  let X : Ω × ℂ → I → ℝ := fun p => I.restrict (LQGMetric.pair0 (h p.1))
  let Y : ℕ → Ω × ℂ → I → ℝ := fun n p => I.restrict fun ψ =>
    LQGMetric.pair0 (h p.1) ψ + γ *
      LQGMetric.logCov ψ.1 (finiteCircleIndex n p.2 ε).1
  let Obs : Ω × ℂ → ℝ := fun p => F (X p)
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hνball : ∀ᵐ z ∂ν, z ∈ Metric.ball (0 : ℂ) 1 := by
    filter_upwards [hν] with z hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hX : Measurable X := by
    dsimp [X]
    exact (Finset.measurable_restrict I).comp <|
      measurable_pi_iff.2 fun ψ =>
        ((LQGMetric.measurable_evalDist ψ.1).comp hh.1.measurable).comp measurable_fst
  have hObs : AEStronglyMeasurable Obs μ :=
    (hF.measurable.comp hX).aestronglyMeasurable
  rcases hFbounded with ⟨C, hC⟩
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hObsBound : ∀ᵐ p ∂μ, ‖Obs p‖ ≤ B :=
    Filter.Eventually.of_forall fun p => (hC (X p)).trans (le_max_left C 0)
  have hd : ∀ n, Measurable (d n) := by
    intro n
    exact measurable_finiteCircleDensity hh γ n ε
  have hmassD : ∀ n, ∫⁻ p, d n p ∂μ = ν Set.univ := by
    intro n
    simpa only [μ, d] using
      lintegral_finiteCircleDensity_prod_eq_rootMass (ν := ν) hh γ n ε
  have hgNonneg : ∀ p, 0 ≤ g p := by
    intro p
    dsimp [g]
    positivity
  have hmassG : ∫⁻ p, ENNReal.ofReal (g p) ∂μ = ν Set.univ := by
    simpa only [μ, g] using
      lintegral_circleAvgDensity_prod_eq_rootMass hh hH hagree γ hε hν
  have hGint : ∀ n, Integrable (G n) μ := by
    intro n
    have hto := integrable_toReal_of_lintegral_ne_top (hd n).aemeasurable
      (by rw [hmassD n]; exact measure_ne_top ν Set.univ)
    simpa only [G, d, μ] using hto
  have hgint : Integrable g μ := by
    have hdg : Measurable (fun p : Ω × ℂ => ENNReal.ofReal (g p)) := by
      have hp : Measurable fun p : Ω × ℂ =>
          ((h p.1, ε, p.2) : LQGMetric.DistC × ℝ × ℂ) :=
        (hh.1.measurable.comp measurable_fst).prodMk
          (measurable_const.prodMk measurable_snd)
      have hc : Measurable fun p : Ω × ℂ =>
          LQGMetric.circleAvg (h p.1) ε p.2 :=
        LQGMetric.measurable_circleAvg.comp
          (f := fun p : Ω × ℂ => ((h p.1, ε, p.2) : LQGMetric.DistC × ℝ × ℂ)) hp
      exact ENNReal.measurable_ofReal.comp <|
        measurable_const.mul (Real.measurable_exp.comp
          (measurable_const.mul hc))
    have hto := integrable_toReal_of_lintegral_ne_top hdg.aemeasurable
      (by rw [hmassG]; exact measure_ne_top ν Set.univ)
    have hEq : (fun p : Ω × ℂ => (ENNReal.ofReal (g p)).toReal) = g := by
      funext p
      dsimp [g]
      rw [ENNReal.toReal_ofReal (hgNonneg p)]
    exact hto.congr (ae_of_all _ fun p => congrFun hEq p)
  have hL1 : Tendsto (fun n => ∫ p, |G n p - g p| ∂μ) atTop (𝓝 0) := by
    simpa only [μ, G, d, g] using
      tendsto_integral_abs_sub_finiteCircleDensity_prod hh
        hH hagree γ hε hν
  have hObsWeighted := tendsto_integral_mul_of_abs_sub hB hGint hgint hObs
    hObsBound hL1
  have hmix (n : ℕ) :
      ∫ p, G n p * Obs p ∂μ = ∫ p, F (Y n p) ∂μ := by
    have hwith :
        ∫ p, F (X p) ∂(μ.withDensity (d n)) =
          ∫ p, (d n p).toReal * F (X p) ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul]
      · rfl
      · exact hd n
      · exact Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top
    calc
      _ = ∫ p, F (X p) ∂(μ.withDensity (d n)) := hwith.symm
      _ = ∫ p, F (Y n p) ∂μ := by
        simpa only [μ, d, X, Y, finiteCircleCovShift] using
          integral_finiteCircleTiltMixture_eq_covShift hh γ n ε I hF.measurable
      _ = _ := rfl
  have hmixFun :
      (fun n => ∫ p, G n p * Obs p ∂μ) = fun n => ∫ p, F (Y n p) ∂μ := funext hmix
  have hObsWeighted' :
      Tendsto (fun n => ∫ p, F (Y n p) ∂μ) atTop (𝓝 (∫ p, g p * Obs p ∂μ)) := by
    rw [← hmixFun]
    exact hObsWeighted
  have hCylinder := tendsto_integral_cylinder_observable_iterated_limit
    hh γ I (ν := ν) hνball F hF ⟨C, hC⟩
  have hright := hCylinder.1 ε hε
  have heq := tendsto_nhds_unique hObsWeighted' hright
  simpa only [μ, g, Obs, X] using heq

/-- For integrable real functions, convergence to zero in `L¹` is the same as convergence of
the integrals of the absolute differences to zero. -/
theorem tendsto_integral_abs_sub_of_tendsto_eLpNorm_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : ℕ → X → ℝ} {g : X → ℝ}
    (hG : ∀ n, MemLp (G n) 1 μ) (hg : MemLp g 1 μ)
    (hL1 : Tendsto (fun n => eLpNorm (G n - g) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |G n x - g x| ∂μ) atTop (𝓝 0) := by
  have hEq : ∀ n, eLpNorm (G n - g) 1 μ =
      ENNReal.ofReal (∫ x, |G n x - g x| ∂μ) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm ((hG n).sub hg).aestronglyMeasurable]
    have hInt : Integrable (fun x => |G n x - g x|) μ :=
      memLp_one_iff_integrable.mp (((hG n).sub hg).abs)
    have hnonneg : 0 ≤ᵐ[μ] fun x => |G n x - g x| :=
      ae_of_all _ fun x => abs_nonneg _
    have hreal := ofReal_integral_eq_lintegral_ofReal hInt hnonneg
    have hfun : (fun x => ‖(G n - g) x‖ₑ) = fun x => ENNReal.ofReal |G n x - g x| := by
      funext x
      rw [Real.enorm_eq_ofReal_abs]
      rfl
    rw [hfun]
    exact hreal.symm
  have hto := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
  have hEq' : (fun n => (eLpNorm (G n - g) 1 μ).toReal) =
      fun n => ∫ x, |G n x - g x| ∂μ := by
    funext n
    rw [hEq n, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => abs_nonneg _)
  exact Tendsto.congr' (Filter.Eventually.of_forall fun n => congrFun hEq' n) hto

/-- The area-test approximations remain convergent after multiplication by any bounded
measurable field observable. -/
theorem tendsto_integral_mul_approxTestIntegral_to_areaTest
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : ℝ → ℂ → Ω → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ Metric.ball (0 : ℂ) 1)
    {F : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : AEStronglyMeasurable F P) (hFbound : ∀ᵐ ω ∂P, ‖F ω‖ ≤ B) :
    Tendsto
      (fun k => ∫ ω, F ω * approxTestIntegral (γ := γ) (H := H) f k ω ∂P)
      atTop
      (𝓝 (∫ ω, F ω * areaTestIntegral (μ := μ) f ω ∂P)) := by
  let G : ℕ → Ω → ℝ := fun k ω => approxTestIntegral (γ := γ) (H := H) f k ω
  let g : Ω → ℝ := fun ω => areaTestIntegral (μ := μ) f ω
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hμ] with ω hω
    exact hω.2 f hf (hasCompactSupport_of_tsupport_subset_unitDisk hfs)
  have hUI : UniformIntegrable G 1 P := by
    simpa only [G] using uniformIntegrable_approxTestIntegral hH hHm hγ hγ2 hf hfs
  have hgMem : MemLp g 1 P := by
    simpa only [g, G] using hUI.memLp_of_ae_tendsto hconv
  have hGMem : ∀ k, MemLp (G k) 1 P := by
    obtain ⟨C, hC⟩ := hUI.2
    intro k
    exact (hC k).trans_lt ENNReal.coe_lt_top
  have hL1e : Tendsto (fun k => eLpNorm (G k - g) 1 P) atTop (𝓝 0) := by
    have hseqEq : (fun k => eLpNorm (G k - g) 1 P) = fun k =>
        eLpNorm (fun ω => approxTestIntegral (γ := γ) (H := H) f k ω -
          areaTestIntegral (μ := μ) f ω) 1 P := by
      funext k
      congr 1
    rw [hseqEq]
    exact tendsto_approxTestIntegral_L1 hH hHm hγ hγ2 hμ hf hfs
  have hL1 := tendsto_integral_abs_sub_of_tendsto_eLpNorm_one hGMem hgMem hL1e
  have hGInt : ∀ k, Integrable (G k) P := fun k => memLp_one_iff_integrable.mp (hGMem k)
  have hgInt : Integrable g P := memLp_one_iff_integrable.mp hgMem
  have hweighted := tendsto_integral_mul_of_abs_sub hB hGInt hgInt hF hFbound hL1
  simpa only [G, g, mul_comm] using hweighted

/-- The compact-test root measure is almost surely concentrated on the test's topological
support. -/
theorem compactTestRootMeasure_ae_mem_tsupport {f : ℂ → ℝ} :
    ∀ᵐ z ∂(compactTestRootMeasure f), z ∈ tsupport f := by
  apply mem_ae_iff.2
  change compactTestRootMeasure f (tsupport f)ᶜ = 0
  exact compactTestRootMeasure_compl_tsupport_eq_zero (f := f)

/-- Integrating the limiting circle-average Wick density against a compact root measure is the
same as integrating the corresponding GMC approximation test against the field observable. -/
theorem integral_circleAvgDensity_mul_fieldObservable_eq_approxTest
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistC}
    {H : ℝ → ℂ → Ω → ℝ}
    (hh : LQGMetric.IsNormalizedWPGFF h P)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z))
    (hagree : ∀ r, 0 < r → ∀ z,
      (fun ω => H r z ω) =ᵐ[P]
        fun ω => LQGMetric.circleAvg (h ω) r z)
    {γ : ℝ} (k : ℕ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ Metric.ball (0 : ℂ) 1)
    (hf_nonneg : ∀ z, 0 ≤ f z)
    (hν : ∀ᵐ z ∂(compactTestRootMeasure f),
      ‖z‖ + MatedCRTHarmonic.GMSLemma27.dyadicRadius k < 1)
    (I : Finset LQGMetric.TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) (hFbounded : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) :
    ∫ p : Ω × ℂ,
      MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp
          (γ * LQGMetric.circleAvg (h p.1)
            (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) p.2) *
        F (I.restrict (LQGMetric.pair0 (h p.1)))
      ∂(P.prod (compactTestRootMeasure f)) =
    ∫ ω, F (I.restrict (LQGMetric.pair0 (h ω))) *
      approxTestIntegral (γ := γ) (H := H) f k ω ∂P := by
  let ν : Measure ℂ := compactTestRootMeasure f
  let μ : Measure (Ω × ℂ) := P.prod ν
  let r : ℝ := MatedCRTHarmonic.GMSLemma27.dyadicRadius k
  let d : Ω × ℂ → ℝ := fun p =>
    r ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg (h p.1) r p.2)
  let X : Ω → I → ℝ := fun ω => I.restrict (LQGMetric.pair0 (h ω))
  let Obs : Ω × ℂ → ℝ := fun p => F (X p.1)
  have hr : 0 < r := by
    dsimp [r]
    rw [MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius]
    exact QuantumZipper.radius_pos k
  have hνfinite : IsFiniteMeasure ν := by
    dsimp [ν]
    exact isFiniteMeasure_compactTestRootMeasure hf
      (hasCompactSupport_of_tsupport_subset_unitDisk hfs) hf_nonneg
  letI := hνfinite
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hX : Measurable X := by
    dsimp [X]
    exact (Finset.measurable_restrict I).comp <|
      measurable_pi_iff.2 fun ψ =>
        (LQGMetric.measurable_evalDist ψ.1).comp hh.1.measurable
  have hObsMeas : AEStronglyMeasurable Obs μ :=
    (hF.measurable.comp (hX.comp measurable_fst)).aestronglyMeasurable
  rcases hFbounded with ⟨C, hC⟩
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hObsBound : ∀ᵐ p ∂μ, ‖Obs p‖ ≤ B :=
    Filter.Eventually.of_forall fun p => (hC (X p.1)).trans (le_max_left C 0)
  have hdMeas : Measurable (fun p : Ω × ℂ => ENNReal.ofReal (d p)) := by
    have hp : Measurable fun p : Ω × ℂ => ((h p.1, r, p.2) :
        LQGMetric.DistC × ℝ × ℂ) :=
      (hh.1.measurable.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)
    have hc : Measurable fun p : Ω × ℂ =>
        LQGMetric.circleAvg (h p.1) r p.2 :=
      LQGMetric.measurable_circleAvg.comp
        (f := fun p : Ω × ℂ => ((h p.1, r, p.2) :
          LQGMetric.DistC × ℝ × ℂ)) hp
    exact ENNReal.measurable_ofReal.comp <|
      measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hc))
  have hνmass : ∫⁻ p, ENNReal.ofReal (d p) ∂μ = ν Set.univ := by
    dsimp [μ, ν, d, r]
    exact lintegral_circleAvgDensity_prod_eq_rootMass hh hH hagree γ hr hν
  have hdInt : Integrable d μ := by
    have hto := integrable_toReal_of_lintegral_ne_top hdMeas.aemeasurable
      (by rw [hνmass]; exact measure_ne_top ν Set.univ)
    have hEq : (fun p : Ω × ℂ => (ENNReal.ofReal (d p)).toReal) = d := by
      funext p
      exact ENNReal.toReal_ofReal (by positivity)
    exact hto.congr (ae_of_all _ fun p => congrFun hEq p)
  have hweighted : Integrable (fun p : Ω × ℂ => d p * Obs p) μ := by
    simpa only [mul_comm] using hdInt.bdd_mul hObsMeas hObsBound
  have hcircleLeft : Measurable (fun p : Ω × ℂ =>
      LQGMetric.circleAvg (h p.1) r p.2) := by
    exact LQGMetric.measurable_circleAvg.comp
      (f := fun p : Ω × ℂ => ((h p.1, r, p.2) :
        LQGMetric.DistC × ℝ × ℂ))
      ((hh.1.measurable.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))
  have hcircleRight : Measurable (fun p : Ω × ℂ => H r p.2 p.1) := by
    exact (MatedCRTHarmonic.GMCFacts.measurable_uncurry_coord hH hHm hr).comp
      measurable_swap
  have hset : MeasurableSet {p : Ω × ℂ |
      LQGMetric.circleAvg (h p.1) r p.2 = H r p.2 p.1} :=
    measurableSet_eq_fun hcircleLeft hcircleRight
  have haeRoot : ∀ᵐ z ∂ν, ∀ᵐ ω ∂P,
      LQGMetric.circleAvg (h ω) r z = H r z ω := by
    filter_upwards [] with z
    filter_upwards [hagree r hr z] with ω hω
    exact hω.symm
  have haeField : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν,
      LQGMetric.circleAvg (h ω) r z = H r z ω :=
    (Measure.ae_ae_comm (μ := P) (ν := ν)
      (p := fun ω z => LQGMetric.circleAvg (h ω) r z = H r z ω)
      (by simpa using hset)).2 haeRoot
  have haeProd : ∀ᵐ p ∂μ,
      LQGMetric.circleAvg (h p.1) r p.2 = H r p.2 p.1 :=
    (Measure.ae_prod_iff_ae_ae
      (p := fun p : Ω × ℂ =>
        LQGMetric.circleAvg (h p.1) r p.2 = H r p.2 p.1)
      (by simpa [μ] using hset)).2 haeField
  have hprodInt := integral_prod (fun p : Ω × ℂ => d p * Obs p) hweighted
  have hiterEq :
      (∫ ω, ∫ z, d (ω, z) * Obs (ω, z) ∂ν ∂P) =
      ∫ ω, ∫ z,
        r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω) * F (X ω) ∂ν ∂P := by
    apply integral_congr_ae
    filter_upwards [haeField] with ω hω
    apply integral_congr_ae
    filter_upwards [hω] with z hz
    simp [d, Obs, hz, X]
  have hinner (ω : Ω) :
      ∫ z, r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω) * F (X ω) ∂ν =
        F (X ω) * approxTestIntegral (γ := γ) (H := H) f k ω := by
    calc
      ∫ z, r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω) * F (X ω) ∂ν =
          (∫ z, r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω) ∂ν) * F (X ω) := by
        exact integral_mul_const (F (X ω))
          (fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω))
      _ = F (X ω) * approxTestIntegral (γ := γ) (H := H) f k ω := by
        rw [approxTestIntegral_eq_compactTestRootMeasure_integral hH hf
          (hasCompactSupport_of_tsupport_subset_unitDisk hfs)
          hf_nonneg k ω]
        dsimp [ν, r]
        ring
  calc
    _ = ∫ ω, ∫ z, d (ω, z) * Obs (ω, z) ∂ν ∂P := by
      simpa only [μ] using hprodInt
    _ = ∫ ω, ∫ z,
        r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω) * F (X ω) ∂ν ∂P := hiterEq
    _ = ∫ ω, F (X ω) * approxTestIntegral (γ := γ) (H := H) f k ω ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ hinner
    _ = _ := by
      rfl

/-- Compact-support Palm identity for the whole-plane GFF and its GMC area. This is the
test-function form of the origin-rooting change of measure: the shifted field law integrated
against a compact root test equals the unrooted field law weighted by the corresponding area. -/
theorem compactTest_rootingPalm_identity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistC}
    {H : ℝ → ℂ → Ω → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hh : LQGMetric.IsNormalizedWPGFF h P)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z))
    (hagree : ∀ r, 0 < r → ∀ z,
      (fun ω => H r z ω) =ᵐ[P]
        fun ω => LQGMetric.circleAvg (h ω) r z)
    (hArea : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ Metric.ball (0 : ℂ) 1)
    (hf_nonneg : ∀ z, 0 ≤ f z)
    (I : Finset LQGMetric.TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) (hFbounded : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) :
    ∫ p : Ω × ℂ,
      F (I.restrict (LQGMetric.pair0 (h p.1 +
        logRootingShift γ p.2)))
      ∂(P.prod (compactTestRootMeasure f)) =
    ∫ ω, F (I.restrict (LQGMetric.pair0 (h ω))) *
      areaTestIntegral (μ := μ) f ω ∂P := by
  let ν : Measure ℂ := compactTestRootMeasure f
  let X : Ω → I → ℝ := fun ω => I.restrict (LQGMetric.pair0 (h ω))
  let F₀ : Ω → ℝ := fun ω => F (X ω)
  let rseq : ℕ → ℝ := MatedCRTHarmonic.GMSLemma27.dyadicRadius
  let dseq : ℕ → ℝ := fun k =>
    ∫ p : Ω × ℂ,
      rseq k ^ (γ ^ 2 / 2) * Real.exp
        (γ * LQGMetric.circleAvg (h p.1) (rseq k) p.2) * F₀ p.1
      ∂(P.prod ν)
  let aseq : ℕ → ℝ := fun k =>
    ∫ ω, F₀ ω * approxTestIntegral (γ := γ) (H := H) f k ω ∂P
  let lseq : ℕ → ℝ := fun k =>
    ∫ p : Ω × ℂ,
      F (I.restrict fun ψ => LQGMetric.pair0 (h p.1) ψ + γ *
        (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) p.2 (rseq k) -
          Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1))
      ∂(P.prod ν)
  haveI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_unitDisk hfs
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    exact isFiniteMeasure_compactTestRootMeasure hf hfc hf_nonneg
  have hνball : ∀ᵐ z ∂ν, z ∈ Metric.ball (0 : ℂ) 1 := by
    filter_upwards [compactTestRootMeasure_ae_mem_tsupport (f := f)] with z hz
    exact hfs hz
  obtain ⟨δ, hδ, hmargin⟩ := exists_uniform_tsupport_margin hf hfs
  have hrad0 : Tendsto
      (fun k : ℕ => MatedCRTHarmonic.GMSLemma27.dyadicRadius k) atTop (𝓝 0) := by
    simpa only [MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius,
      QuantumZipper.radius] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
  have hrad0' : Tendsto rseq atTop (𝓝 0) := by
    simpa only [rseq] using hrad0
  have hradPos : ∀ k, 0 < rseq k := by
    intro k
    dsimp [rseq]
    rw [MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius]
    exact QuantumZipper.radius_pos k
  have hradWithin : Tendsto rseq atTop (𝓝[Ioi 0] 0) := by
    change Tendsto
      (fun k : ℕ => MatedCRTHarmonic.GMSLemma27.dyadicRadius k)
      atTop (𝓝[Ioi 0] 0)
    rw [nhdsWithin]
    refine tendsto_inf.2 ⟨hrad0, tendsto_principal.2 ?_⟩
    exact Filter.Eventually.of_forall fun k => hradPos k
  have hsmall : ∀ᶠ k : ℕ in atTop, rseq k < δ :=
    hrad0'.eventually (Iio_mem_nhds hδ)
  have hνmargin : ∀ᶠ k : ℕ in atTop,
      ∀ᵐ z ∂ν, ‖z‖ + rseq k < 1 := by
    filter_upwards [hsmall] with k hk
    filter_upwards [compactTestRootMeasure_ae_mem_tsupport (f := f)] with z hz
    have hzδ := hmargin z hz
    have hkr : rseq k ≤ δ := le_of_lt hk
    linarith
  have hDensEqApprox : dseq =ᶠ[atTop] aseq := by
    filter_upwards [hνmargin] with k hνk
    simpa only [dseq, aseq, rseq, F₀, X] using
      integral_circleAvgDensity_mul_fieldObservable_eq_approxTest
        hh hH hHm hagree k hf hfs hf_nonneg hνk I F hF hFbounded
  have hDensEqLog : dseq =ᶠ[atTop] lseq := by
    filter_upwards [hνmargin] with k hνk
    have hr : 0 < rseq k := hradPos k
    simpa only [dseq, lseq, rseq, F₀, X] using
      integral_circleAvgDensity_mul_cylinder_eq_logPotShift
        hh hH hagree γ hr hνk I F hF hFbounded
  have hX : Measurable X := by
    dsimp [X]
    exact (Finset.measurable_restrict I).comp <|
      measurable_pi_iff.2 fun ψ =>
        (LQGMetric.measurable_evalDist ψ.1).comp hh.1.measurable
  have hF₀ : AEStronglyMeasurable F₀ P :=
    (hF.measurable.comp hX).aestronglyMeasurable
  rcases hFbounded with ⟨C, hC⟩
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hF₀bound : ∀ᵐ ω ∂P, ‖F₀ ω‖ ≤ B :=
    Filter.Eventually.of_forall fun ω => (hC (X ω)).trans (le_max_left C 0)
  have hApproxLimit := tendsto_integral_mul_approxTestIntegral_to_areaTest
    hH hHm hγ hγ2 hArea hf hfs hB hF₀ hF₀bound
  have hApproxSeq : Tendsto aseq atTop
      (𝓝 (∫ ω, F₀ ω * areaTestIntegral (μ := μ) f ω ∂P)) := by
    simpa only [aseq, F₀, X] using hApproxLimit
  have hDensLimit : Tendsto dseq atTop
      (𝓝 (∫ ω, F₀ ω * areaTestIntegral (μ := μ) f ω ∂P)) :=
    Tendsto.congr' hDensEqApprox.symm hApproxSeq
  have hCylinder := tendsto_integral_cylinder_observable_iterated_limit
    hh γ I (ν := ν) hνball F hF ⟨C, hC⟩
  have hLogLimit : Tendsto lseq atTop
      (𝓝 (∫ p : Ω × ℂ,
        F (I.restrict (LQGMetric.pair0 (h p.1 +
          logRootingShift γ p.2))) ∂(P.prod ν))) := by
    convert hCylinder.2.comp hradWithin using 1 <;> rfl
  have hDensLogLimit : Tendsto dseq atTop
      (𝓝 (∫ p : Ω × ℂ,
        F (I.restrict (LQGMetric.pair0 (h p.1 +
          logRootingShift γ p.2))) ∂(P.prod ν))) :=
    Tendsto.congr' hDensEqLog.symm hLogLimit
  have hEq := tendsto_nhds_unique hDensLimit hDensLogLimit
  simpa only [F₀, X, ν] using hEq.symm

/-- The minimal non-SLE data for the field-law part of DMS14 Lemma A.10. The conclusion
`fieldLaw_eq_areaBiased` is deliberately absent: it is what the A.10 proof establishes. The
stronger ambient lift and the unrelated moment outputs are absent as well. -/
structure WholePlaneRootingFieldLawInputs (Ω : Type*) [MeasurableSpace Ω] where
  gamma : ℝ
  gamma_pos : 0 < gamma
  gamma_lt_two : gamma < 2
  field : Ω → LQGMetric.DistC
  unrootedLaw : Measure Ω
  normalizedWPGFF : LQGMetric.IsNormalizedWPGFF field unrootedLaw
  area : WholePlaneGMCUnitDiskArea Ω gamma field unrootedLaw
  rootSample : Ω × ℂ → Ω
  rootSample_measurable : Measurable rootSample
  rootSample_field_eq : ∀ ω z,
    field (rootSample (ω, z)) =
      LQGMetric.addConst (field ω + logRootingShift gamma z)
        (-LQGMetric.circleAvg (field ω + logRootingShift gamma z) 1 0)
  rootedLaw : Measure Ω
  rootedLaw_eq_rootSample_map :
    rootedLaw = (unrootedLaw.prod normalizedLebesgueOnRootingDisk).map rootSample

/-- The disk mass expected under the inputs' unrooted field law. -/
def WholePlaneRootingFieldLawInputs.expectedUnitDiskMass
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) : ℝ≥0∞ :=
  ∫⁻ ω, D.area.unitDiskMass ω ∂D.unrootedLaw

/-- A jointly measurable circle-average version with the same GMC area limit and the same
coordinates as the supplied normalized field, up to a.e. equality. -/
theorem exists_measurableAreaVersion
    {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {field : Ω → LQGMetric.DistC}
    {P : Measure Ω} (A : WholePlaneGMCUnitDiskArea Ω γ field P) :
    ∃ H' : ℝ → ℂ → Ω → ℝ,
      LQGDimension.IsGFFCircleAverage H' P ∧
      (∀ r z, Measurable (H' r z)) ∧
      MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf
        γ H' A.areaMeasure P ∧
      (∀ r, 0 < r → ∀ z,
        (fun ω => H' r z ω) =ᵐ[P]
          fun ω => LQGMetric.circleAvg (field ω) r z) := by
  obtain ⟨H', hH', hHm', hversion⟩ :=
    MatedCRTHarmonic.GMCFacts.exists_measurable_version A.circleAverage_isGFF
  have happrox : ∀ k : ℕ, ∀ᵐ ω ∂P,
      MatedCRTHarmonic.GMSLemma27.lqgApprox γ H' k ω =
        MatedCRTHarmonic.GMSLemma27.lqgApprox γ A.circleAverage k ω := by
    intro k
    let r := MatedCRTHarmonic.GMSLemma27.dyadicRadius k
    have hr : 0 < r := by
      dsimp [r]
      rw [MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius]
      exact QuantumZipper.radius_pos k
    filter_upwards [hversion r hr] with ω hω
    rw [MatedCRTHarmonic.GMSLemma27.lqgApprox,
      MatedCRTHarmonic.GMSLemma27.lqgApprox]
    congr 1
    funext z
    rw [hω z]
  have happroxAll : ∀ᵐ ω ∂P, ∀ k : ℕ,
      MatedCRTHarmonic.GMSLemma27.lqgApprox γ H' k ω =
        MatedCRTHarmonic.GMSLemma27.lqgApprox γ A.circleAverage k ω :=
    ae_all_iff.2 happrox
  have harea' : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf
      γ H' A.areaMeasure P := by
    filter_upwards [A.isLQGAreaOf, happroxAll] with ω hω hωapprox
    refine ⟨hω.1, ?_⟩
    intro f hf hfc
    have hconv := hω.2 f hf hfc
    have hEq : (fun k : ℕ =>
        ∫ z, f z ∂(MatedCRTHarmonic.GMSLemma27.lqgApprox γ H' k ω)) =ᶠ[atTop]
        fun k => ∫ z, f z ∂(MatedCRTHarmonic.GMSLemma27.lqgApprox
          γ A.circleAverage k ω) := by
      filter_upwards [] with k
      rw [hωapprox k]
    exact Tendsto.congr' hEq.symm hconv
  have hagree : ∀ r, 0 < r → ∀ z,
      (fun ω => H' r z ω) =ᵐ[P]
        fun ω => LQGMetric.circleAvg (field ω) r z := by
    intro r hr z
    filter_upwards [hversion r hr, A.circleAverage_eq_field r hr z] with ω hv heq
    exact (hv z).trans heq
  exact ⟨H', hH', hHm', harea', hagree⟩

/-- The interface's rooted field law is the pushforward of the independent field and uniform
root through the source's normalized logarithmic shift. This merely expands the supplied sample
map; the area-bias identity remains the main theorem. -/
theorem WholePlaneRootingFieldLawInputs.rootedFieldLaw_eq_rootingMap
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) :
    D.rootedLaw.map D.field =
      (D.unrootedLaw.prod normalizedLebesgueOnRootingDisk).map
        (fun p : Ω × ℂ =>
          LQGMetric.addConst (D.field p.1 + logRootingShift D.gamma p.2)
            (-LQGMetric.circleAvg
              (D.field p.1 + logRootingShift D.gamma p.2) 1 0)) := by
  rw [D.rootedLaw_eq_rootSample_map]
  rw [Measure.map_map D.normalizedWPGFF.1.measurable D.rootSample_measurable]
  apply Measure.map_congr
  exact ae_of_all _ fun p => D.rootSample_field_eq p.1 p.2

/-- For any whole-plane GMC output over the normalized whole-plane GFF, the expected mass of
the open unit disk is exactly Lebesgue area, namely `π`. -/
theorem WholePlaneGMCUnitDiskArea.expectedUnitDiskMass_eq_pi
    {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {field : Ω → LQGMetric.DistC}
    {P : Measure Ω} (A : WholePlaneGMCUnitDiskArea Ω γ field P)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    (∫⁻ ω, A.unitDiskMass ω ∂P) = ENNReal.ofReal Real.pi := by
  obtain ⟨H', hH', hHm', harea', _hagree⟩ := exists_measurableAreaVersion A
  have hmass := lintegral_areaMeasure_unitDisk_eq hH' hHm' hγ hγ2 harea'
  calc
    (∫⁻ ω, A.unitDiskMass ω ∂P) =
        ∫⁻ ω, A.areaMeasure ω (Metric.ball (0 : ℂ) 1) ∂P := by
          congr 1
          funext ω
          rw [A.unitDiskMass_eq]
          rfl
    _ = volume (Metric.ball (0 : ℂ) 1) := hmass.2
    _ = ENNReal.ofReal Real.pi := by
      rw [← MatedCRTHarmonic.GMS4.GMSA.volume_rootingDisk,
        MatedCRTHarmonic.GMS4.GMSA.rootingDisk]

end MatedCRTHarmonic.ConeLemmaA10


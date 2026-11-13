/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase1.FieldLaw at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.ProductLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaBiasNormalization
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaExactMass
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.ProductRooting
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FieldLawAssembly
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingMeasurable
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Data
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.WeightedMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.OuterMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.AreaFunctional
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPArea
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P0
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.WholePlaneFieldLaw

/-!
# DMS14 Lemma A.10 on the field space

[18] Proposition 4.10, Case 1 uses DMS14
Lemma A.10 : if `h₀` is a whole-plane GFF with
`h₀_1(0) = 0` and `z` is an independent uniform point of `𝔻`, then
`h₁ = h₀ − γ log|· − z| + γ log max(|·|, 1)` (with its unit-circle average reset to zero) has the
law of `h₀` weighted by `μ_{h₀}(𝔻) / E[μ_{h₀}(𝔻)]`.

The rooting construction proved this (`ConeLemmaA10.WholePlaneRootingFieldLawInputs.fieldLaw_eq_areaBiased_holds`) for
any instance of its input record. Here the record is instantiated **on the field space itself**
(`Ω := DistC`, the field is `id`, the rooting map is CANON's `Canon.rootedField`), with the GMC
area of the field (`CellScaling.lqgArea`); the result is stated for the law of an arbitrary normalized
whole-plane GFF, with the explicit **measurable** density
`areaDensity γ h = areaOpenFun γ 𝔻 h / π` (`ConeScaling.areaOpenFun` agrees with `lqgArea γ h 𝔻`
whenever the dyadic GMC limit exists, which holds almost surely).

The file also constructs the analytic construction area record `WholePlaneGMCUnitDiskArea` for every normalized
whole-plane GFF (`wholePlaneGMCUnitDiskAreaOf`): no constructor of that record existed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.GMS4.GMSA

/-! ## The GMC area record of a normalized whole-plane GFF -/

/-- **Constructor of the analytic construction's whole-plane area record** for any normalized whole-plane GFF `Y`:
The circle-average version of `GMCFacts.exists_isLQGAreaOf`, the area `CellScaling.lqgArea γ (Y ω)`
(the canonical GMC, `= qAreaC`), and its unit-disk mass. -/
def wholePlaneGMCUnitDiskAreaOf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    WholePlaneGMCUnitDiskArea Ω γ Y P where
  circleAverage := (GMCFacts.exists_isLQGAreaOf hY hγ.1 hγ.2).choose
  circleAverage_isGFF := (GMCFacts.exists_isLQGAreaOf hY hγ.1 hγ.2).choose_spec.1
  circleAverage_eq_field := (GMCFacts.exists_isLQGAreaOf hY hγ.1 hγ.2).choose_spec.2.2.1
  areaMeasure := fun ω => CellScaling.lqgArea γ (Y ω)
  isLQGAreaOf := by
    have h := (GMCFacts.exists_isLQGAreaOf hY hγ.1 hγ.2).choose_spec.2.2.2
    simpa only [LQGCone.lqgArea_eq_qAreaC] using h
  unitDiskMass := fun ω => CellScaling.lqgArea γ (Y ω) (ball 0 1)
  unitDiskMass_eq := fun _ => rfl
  unitDiskMass_aemeasurable := by
    have hspec := (GMCFacts.exists_isLQGAreaOf hY hγ.1 hγ.2).choose_spec
    have h := GMCFacts.aemeasurable_measure_ball hspec.1 hspec.2.1 hspec.2.2.2 0 1
    simpa only [LQGCone.lqgArea_eq_qAreaC] using h

@[simp] theorem wholePlaneGMCUnitDiskAreaOf_areaMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) :
    (wholePlaneGMCUnitDiskAreaOf hY hγ).areaMeasure ω = CellScaling.lqgArea γ (Y ω) := rfl

@[simp] theorem wholePlaneGMCUnitDiskAreaOf_unitDiskMass {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) :
    (wholePlaneGMCUnitDiskAreaOf hY hγ).unitDiskMass ω = CellScaling.lqgArea γ (Y ω) (ball 0 1) :=
  rfl

/-- The unit-disk GMC mass of a normalized whole-plane GFF has every moment of order
`p < 4/γ²` ([RV14, Theorem 2.11] as cited in [18] Case 1; `GMCFacts.lintegral_ball_one_rpow_lt_top`). -/
theorem lintegral_unitDiskMass_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {p : ℝ} (hp0 : 0 < p) (hp : p < 4 / γ ^ 2) :
    ∫⁻ ω, CellScaling.lqgArea γ (Y ω) (ball 0 1) ^ p ∂P < ⊤ := by
  obtain ⟨hH, hHm, -, hμ⟩ := (GMCFacts.exists_isLQGAreaOf hY hγ.1 hγ.2).choose_spec
  have h := GMCFacts.lintegral_ball_one_rpow_lt_top hH hHm hγ.1 hμ hp0 hp
  simpa only [LQGCone.lqgArea_eq_qAreaC] using h

/-! ## The measurable area density -/

/-- The DMS A.10 weight `μ_h(𝔻) / E[μ_h(𝔻)] = μ_h(𝔻) / π`, as a measurable function of the field. -/
def areaDensity (γ : ℝ) (h : DistC) : ℝ≥0∞ :=
  ConeScaling.areaOpenFun γ (ball (0 : ℂ) 1) h / ENNReal.ofReal Real.pi

theorem measurable_areaDensity (γ : ℝ) : Measurable (areaDensity γ) :=
  (ConeScaling.measurable_areaOpenFun γ _).div_const _

/-- On fields whose dyadic GMC limit exists the density is the canonical unit-disk mass over `π`. -/
theorem areaDensity_eq_of_vague {γ : ℝ} {h : DistC}
    (hv : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ h) μ) :
    areaDensity γ h = CellScaling.lqgArea γ h (ball 0 1) / ENNReal.ofReal Real.pi := by
  rw [areaDensity, ConeScaling.areaOpenFun_eq_lqgArea isOpen_ball isBounded_ball hv]

/-- For a whole-plane GFF the density is a.s. the canonical unit-disk mass over `π`. -/
theorem ae_areaDensity_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → DistC}
    (hY : IsWholePlaneGFF Y P) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, areaDensity γ (Y ω) =
      CellScaling.lqgArea γ (Y ω) (ball 0 1) / ENNReal.ofReal Real.pi := by
  have : IsProbabilityMeasure P := hY.gaussian.isProbabilityMeasure
  filter_upwards [LQGCoord.ae_exists_isVagueLimitC_wp hY hγ.1 hγ.2] with ω hω
  exact areaDensity_eq_of_vague hω

/-! ## The field-space instance of the rooting construction's input record -/

/-- CANON's rooting map `(h, z) ↦ normalize(h − γ log|·−z| + γ log max(|·|,1))` is measurable. -/
theorem measurable_rootingMap (γ : ℝ) :
    Measurable fun p : DistC × ℂ => Canon.rootedField γ p.1 p.2 :=
  ConeLemmaA10.measurable_normalizedRootingMap γ

/-- the rooting construction's DMS A.10 input record on the field space `DistC` with field `id`. -/
def fieldSpaceRootingInputs {ν : Measure DistC} (hν : IsNormalizedWPGFF id ν) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : ConeLemmaA10.WholePlaneRootingFieldLawInputs DistC where
  gamma := γ
  gamma_pos := hγ.1
  gamma_lt_two := hγ.2
  field := id
  unrootedLaw := ν
  normalizedWPGFF := hν
  area := wholePlaneGMCUnitDiskAreaOf hν hγ
  rootSample := fun p => Canon.rootedField γ p.1 p.2
  rootSample_measurable := measurable_rootingMap γ
  rootSample_field_eq := fun _ _ => rfl
  rootedLaw := (ν.prod Canon.rootMeasure).map fun p => Canon.rootedField γ p.1 p.2
  rootedLaw_eq_rootSample_map := rfl

/-- **DMS14 Lemma A.10 on the field space.** For the law `ν` of a normalized whole-plane GFF and
an independent root with normalized Lebesgue law on `𝔻`, the rooted field has law
`ν.withDensity (areaDensity γ)`. -/
theorem map_rootingMap_eq_withDensity {ν : Measure DistC} (hν : IsNormalizedWPGFF id ν) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (ν.prod Canon.rootMeasure).map (fun p => Canon.rootedField γ p.1 p.2) =
      ν.withDensity (areaDensity γ) := by
  have h := (fieldSpaceRootingInputs hν hγ).fieldLaw_eq_areaBiased_holds
  rw [ConeLemmaA10.WholePlaneRootingFieldLawInputs.withDensity_areaBias_eq_div_pi] at h
  change ((ν.prod Canon.rootMeasure).map fun p => Canon.rootedField γ p.1 p.2).map id =
    (ν.withDensity fun h =>
      CellScaling.lqgArea γ (id h) (ball 0 1) / ENNReal.ofReal Real.pi).map id at h
  rw [Measure.map_id, Measure.map_id] at h
  rw [h]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_areaDensity_eq hν.1 hγ] with g hg
  exact hg.symm

/-- **DMS14 Lemma A.10 for an arbitrary normalized whole-plane GFF `Y`** on `(Ω, P)`: with an
independent root `z ∼ Canon.rootMeasure`, the rooted field `Canon.rootedField γ (Y ω) z` has the
law of `Y` weighted by `areaDensity γ`. -/
theorem map_rootedField_eq_withDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ((P.map Y).prod Canon.rootMeasure).map (fun p => Canon.rootedField γ p.1 p.2) =
      (P.map Y).withDensity (areaDensity γ) := by
  have hν : IsNormalizedWPGFF id (P.map Y) :=
    LQGMetric.DFGPS.T12.isNormalizedWPGFF_of_map_eq measurable_id hY (Measure.map_id)
  exact map_rootingMap_eq_withDensity hν hγ

end MatedCRTHarmonic.GMSCase1

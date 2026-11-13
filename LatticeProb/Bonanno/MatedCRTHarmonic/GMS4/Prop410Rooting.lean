/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop410Rooting at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingMeasurable
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The whole-plane rooting input for [18] Proposition 4.10, Case 1

This file records producer interfaces for the source-law identity and the
whole-sample-space and moment outputs needed by Case 1, then specializes the
already proved `GMS4.withDensity_badEvent_le_holder` adapter. It does not prove
The DMS14 or RV14 inputs, Proposition 4.10, or Proposition 2.10.
DMS14 Lemma A.10 and Proposition 4.13(i) are SLE-free; the latter is the
separate quantum-cone area-scaling result ([14, Proposition 4.13(i)]), not used by this rooting file
and not an input to the SLE bundle. The repository's SLE-free producer
paths are `ConeLemmaA10/*` for A.10 and `ConeScaling.ConeRealization.map_rescaledField_eq`
for the field-law part of Proposition 4.13(i). In this file the still-missing
A.10 conclusion is named `WholePlaneRootedLQGLaw.fieldLaw_eq_areaBiased`;
`gmsaAmbientRootingLift` is the separate stronger joint-law obligation needed
when the event also sees auxiliary coordinates.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

namespace GMSA

/-- The open unit disk used for the whole-plane rooting in DMS14 Lemma A.10. -/
def rootingDisk : Set ℂ := Metric.ball 0 1

/-- Lebesgue measure normalized to be a probability measure on the open unit disk. -/
def normalizedLebesgueOnRootingDisk : Measure ℂ :=
  ENNReal.ofReal (Real.pi⁻¹) • (volume.restrict rootingDisk)

lemma volume_rootingDisk : volume rootingDisk = ENNReal.ofReal Real.pi := by
  simp [rootingDisk, ← NNReal.coe_real_pi]

instance : IsProbabilityMeasure normalizedLebesgueOnRootingDisk := by
  refine ⟨?_⟩
  rw [normalizedLebesgueOnRootingDisk, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ]
  rw [volume_rootingDisk]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi⁻¹)]
  rw [inv_mul_cancel₀ (ne_of_gt Real.pi_pos), ENNReal.ofReal_one]

/-- The whole-plane GMC area output used by the rooting construction. The repository's
canonical whole-plane area is available as `MoTPort.qAreaC` (identified with
The area convention in `LQGCone.AreaBridge`). This Gaussian and local interface records
The version on the present sample space and its exact mass on the rooting disk.
The measure is not an arbitrary density parameter. -/
structure WholePlaneGMCUnitDiskArea (Ω : Type*) [MeasurableSpace Ω]
    (γ : ℝ) (field : Ω → LQGMetric.DistC) (P : Measure Ω) where
  /-- A jointly-versioned circle-average process of the whole-plane field. -/
  circleAverage : ℝ → ℂ → Ω → ℝ
  circleAverage_isGFF : LQGDimension.IsGFFCircleAverage circleAverage P
  /-- The version is the circle average of the supplied normalized WPGFF. -/
  circleAverage_eq_field : ∀ r, 0 < r → ∀ z,
    (fun ω => circleAverage r z ω) =ᵐ[P] fun ω => LQGMetric.circleAvg (field ω) r z
  /-- The whole-plane `γ`-LQG area measure of the field. -/
  areaMeasure : Ω → Measure ℂ
  /-- Its defining dyadic GMC vague-limit property from the Gaussian and local construction. -/
  isLQGAreaOf : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf
    γ circleAverage areaMeasure P
  /-- The random area of the open unit disk. -/
  unitDiskMass : Ω → ℝ≥0∞
  /-- This scalar is exactly the mass of the named LQG area measure on `D`. -/
  unitDiskMass_eq : ∀ ω, unitDiskMass ω = areaMeasure ω rootingDisk
  unitDiskMass_aemeasurable : AEMeasurable unitDiskMass P

/-- **the analytic construction producer interface for the whole-plane clause of DMS14 Lemma A.10.**

The source ([14, Lemma A.10]) says, in its final paragraph,
"sampling h according to its unweighted law, then picking z0
∈ D according to Lebesgue measure". It starts with a whole-plane GFF whose
additive constant is fixed so that its average on `∂D` is zero and weights its
law by `μ_h(D)`; equivalently, sample that point independently, add
`z ↦ −γ log |z − z₀| + γ log max (|z|, 1)`, and finally reset the additive
constant so that the new field has average zero on `∂D`. This interface uses
normalized Lebesgue measure on the unit disk so the rooted law is a probability,
and expresses the corresponding normalized `μ_h(D)` bias.

The source identifies the law of the resulting normalized *field*, namely
after pushing both measures forward to `DistC` ([14, Lemma A.10]; [18, proof of Proposition
4.10, Case 1]). Here `Ω` may
also carry auxiliary data, `rootSample` is a map on that whole sample space,
and `gmsaAmbientRootingLift` identifies measures on `Ω` itself. This is a
strictly stronger ambient lift of the source field-law identity: an additional
The analytic construction producer obligation beyond DMS14's literal field-law identity. This field
records the obligation; it does not construct the lift. The lift is retained
because the downstream Case 1 adapter tests an arbitrary event in `Ω`.
The underlying field-law identity is the SLE-free DMS14 input, not a SLE
bundle field. This source identity is an SLE-free analytic
proof obligation, not a theorem established by this interface file. The source's
unnormalized `μ_h(D) dh` weighting is normalized here
by its expected unit-disk mass, matching [18, Case 1]'s density
`μ_h(D) / E[μ_h(D)]`. The finite moment needed for the Hölder step is a separate
The analytic construction producer output, recorded in the field below from [RV14, Theorem 2.11] as
cited by [18, proof of Proposition 4.10, Case 1]. This record does not prove that
output. -/
structure WholePlaneRootedLQGLaw (Ω : Type*) [MeasurableSpace Ω] where
  /-- The LQG parameter used in the rooted field. -/
  gamma : ℝ
  gamma_pos : 0 < gamma
  gamma_lt_two : gamma < 2
  /-- The field-valued random variable before rooting. -/
  field : Ω → LQGMetric.DistC
  /-- The unweighted law of the normalized whole-plane GFF. -/
  unrootedLaw : Measure Ω
  unrootedLaw_isProbability : IsProbabilityMeasure unrootedLaw
  /-- The unweighted field law is the normalized whole-plane GFF law. -/
  normalizedWPGFF : LQGMetric.IsNormalizedWPGFF field unrootedLaw
  /-- The whole-plane GMC area output whose unit-disk mass weights the law. -/
  area : WholePlaneGMCUnitDiskArea Ω gamma field unrootedLaw
  /-- The expected unit-disk LQG mass is positive. -/
  expectedUnitDiskLQGMass_pos : 0 < ∫⁻ ω, area.unitDiskMass ω ∂unrootedLaw
  /-- The expected unit-disk LQG mass is finite. -/
  expectedUnitDiskLQGMass_lt_top : ∫⁻ ω, area.unitDiskMass ω ∂unrootedLaw < ⊤
  /-- **the analytic construction producer output for the Case 1 Hölder step.** The unit-disk GMC
  mass of the normalized whole-plane GFF has a finite moment of some order
  `p > 1`; [18, proof of Proposition 4.10, Case 1,
  ] invokes this from [RV14,
  Theorem 2.11]. This is a required produced by the analytic construction fact, not a theorem proved by
  this record. Together with the positive finite first moment above, it yields
  a finite `L^p` moment for `density`. -/
  unitDiskMass_has_finite_pos_moment : ∃ p : ℝ, 1 < p ∧
    (∫⁻ ω, area.unitDiskMass ω ^ p ∂unrootedLaw) < ⊤
  /-- A pointwise distributional representative of the logarithmic rooting
  shift `w ↦ -γ log|w-z₀| + γ log max(|w|,1)`. Its canonical repository
  producer is `ConeLemmaA10.logRootingShift`; the exact pairing identity and
  measurability needed to instantiate this field are proved in
  `ConeLemmaA10.LogShift` and `ConeLemmaA10.RootingMeasurable`. -/
  rootingLogShift : ℂ → LQGMetric.DistC
  /-- The rooting shift acts on each test function by integration against the
  source's exact logarithmic function. -/
  rootingLogShift_apply : ∀ z (φ : LQGMetric.TestC),
    rootingLogShift z φ =
      ∫ w, φ w * (-gamma * Real.log ‖w - z‖ +
        gamma * Real.log (max ‖w‖ (1 : ℝ))) ∂volume
  /-- The ambient sample-space lift of the independent-point field rooting.
  DMS14 A.10 specifies its composition with `field`, not this map on arbitrary
  auxiliary coordinates. -/
  rootSample : Ω × ℂ → Ω
  rootSample_measurable : Measurable rootSample
  /-- Exact field transformation: add the logarithmic singularity and reset
  the circle average on `∂D` to zero. -/
  rootSample_field_eq : ∀ ω z,
    field (rootSample (ω, z)) =
      LQGMetric.addConst (field ω + rootingLogShift z)
        (-LQGMetric.circleAvg (field ω + rootingLogShift z) 1 0)
  /-- The ambient law chosen after independent normalized-Lebesgue field
  rooting on `D`. -/
  rootedLaw : Measure Ω
  /-- The the analytic construction ambient realization of the DMS14 construction: sample the field
  and the independent uniform point from the product law, then apply the chosen
  lift `rootSample`. The source itself asserts only the induced field law. -/
  rootedLaw_eq_rootSample_map :
    rootedLaw = (unrootedLaw.prod normalizedLebesgueOnRootingDisk).map rootSample
  /-- **SLE-free DMS14 Lemma A.10 field-law producer obligation**, stated after pushing both laws
  forward to `DistC`. It identifies the field produced by independent uniform
  disk rooting with the normalized `μ_h(D)`-biased field law. This is the
  SLE-free source statement, which remains a required input; it is not proved
  by this interface declaration and it does not identify measures on an
  ambient `Ω`. -/
  fieldLaw_eq_areaBiased : rootedLaw.map field =
    (unrootedLaw.withDensity
      (fun ω => area.unitDiskMass ω / ∫⁻ ω, area.unitDiskMass ω ∂unrootedLaw)).map field
  /-- **Additional ambient-rooting producer output.** This strictly stronger output
  identifies measures on the whole sample space `Ω`, so it can transfer an
  arbitrary ambient event used by the Case 1 adapter. DMS14 A.10 supplies the
  field-space identity above, not this lift; when `Ω` has auxiliary
  coordinates, the lift requires a separate producer argument. If those
  coordinates include the independent SLE path, that argument is a mixed
  mixed field-and-curve output: the source's SLE-free field identity alone cannot identify
  the joint ambient law. The right side is normalized to have total mass one. -/
  gmsaAmbientRootingLift : rootedLaw = unrootedLaw.withDensity
    (fun ω => area.unitDiskMass ω / ∫⁻ ω, area.unitDiskMass ω ∂unrootedLaw)

end GMSA

end MatedCRTHarmonic.GMS4


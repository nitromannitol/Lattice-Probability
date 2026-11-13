/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalStatement at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48Statement
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Observable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Prop45
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TModel
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.L46TInputs

/-!
# The canonical carrier for Proposition 4.8

The earlier `GMS4.Prop48WholePlaneAllScalesProducer` is retained for the
Case 0 adapter, but its arbitrary rooted law does not carry the
IG phase or an area-parametrized curve. The active source data here are the
frozen coupling's 0-cone area-time curve `η₀`, the reference field `X₀`, and
The actual phase-aware IG average. On the unit disk this 0-cone field has the
normalized whole-plane GFF restriction law (`Prop48ConeDisk`).

The structures below record geometric realization data, not the probability
conclusion of Proposition 4.8. Analytic bounds must be proved separately.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The literal real `u_*^ε(z)` on the zero-cone area-time curve. -/
def uStar (ε : ℝ) (η₀ : Ω → C(ℝ, ℂ)) (ω : Ω) (z : ℂ) : ℝ :=
  (MatedCRTHarmonic.Canon.realLocalPoint ε (η₀ ω) z).uStar

/-- The source event (4.22), with the IG phase that drives the frozen curve. -/
def localEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) : Set Ω :=
  MatedCRTHarmonic.Canon.referenceLocalEvent D hγ ε q ζ z

/-- The literal masked density from (4.22), without a freely chosen
observable field. -/
def maskedUStar
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  (localEvent D hγ ε q ζ z).indicator (fun ω' => uStar ε η₀ ω' z) ω

theorem maskedUStar_nonneg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) :
    0 ≤ maskedUStar D hγ ε q ζ z ω := by
  by_cases hω : ω ∈ localEvent D hγ ε q ζ z
  · simp only [maskedUStar, Set.indicator_of_mem hω, uStar,
      MatedCRTHarmonic.Canon.realLocalPoint]
    exact MatedCRTHarmonic.GMS4F.realUStar_nonneg ε (η₀ ω) z
  · simp [maskedUStar, Set.indicator_of_notMem hω]
/-- The source global event `E^ε`: every local test within `B_ρ(0)`
satisfies the three conditions of (4.22). -/
def goodEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ ρ : ℝ) : Set Ω :=
  {ω | ∀ z ∈ Metric.ball (0 : ℂ) ρ, ω ∈ localEvent D hγ ε q ζ z}

/-- A measurable representative of the frozen uniform IG phase. -/
def phaseVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Ω → ℝ :=
  MatedCRTHarmonic.BundleSec4.phaseVersion D

theorem measurable_phaseVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Measurable (phaseVersion D hγ) :=
  MatedCRTHarmonic.BundleSec4.measurable_phaseVersion D

theorem ae_phaseVersion_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : phaseVersion D hγ =ᵐ[P] U :=
  MatedCRTHarmonic.BundleSec4.phaseVersion_ae_eq D

private theorem aemeasurable_fieldAverage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (r : ℝ) (z : ℂ) :
    AEMeasurable (fun ω => LQGMetric.circleAvg
      (MatedCRTHarmonic.Canon.referenceSample D hγ ω).zeroConeField r z) P :=
  (LQGMetric.measurable_circleAvg_left r z).comp_aemeasurable
    (MatedCRTHarmonic.Canon.aemeasurable_reference_field D hγ)

/-- A measurable version of the zero-cone circle average at one point. -/
def fieldAverageVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (r : ℝ) (z : ℂ) : Ω → ℝ :=
  (aemeasurable_fieldAverage D hγ r z).mk
    (fun ω => LQGMetric.circleAvg
      (MatedCRTHarmonic.Canon.referenceSample D hγ ω).zeroConeField r z)

theorem measurable_fieldAverageVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (r : ℝ) (z : ℂ) :
    Measurable (fieldAverageVersion D hγ r z) :=
  (aemeasurable_fieldAverage D hγ r z).measurable_mk

/-- The selected measurable version of the physical pair of averages. -/
def circleObservation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) : ℝ × ℝ :=
  (fieldAverageVersion D hγ
      (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω,
    LQGMetric.circleAvg (hIG₀ ω)
      (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z + phaseVersion D hγ ω)

theorem measurable_circleObservation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    Measurable (circleObservation D hγ ε q ζ z) := by
  exact (measurable_fieldAverageVersion D hγ
    (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z).prodMk
        (((LQGMetric.measurable_circleAvg_left
          (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z).comp
            D.igField.1.1.measurable).add (measurable_phaseVersion D hγ))

/-- The selected conditioning pair agrees a.s. with the literal zero-cone
field average and the physical IG average used by the source event. -/
theorem ae_circleObservation_eq_actual
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    circleObservation D hγ ε q ζ z =ᵐ[P]
      fun ω => (LQGMetric.circleAvg
          (MatedCRTHarmonic.Canon.referenceSample D hγ ω).zeroConeField
          (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z,
        MatedCRTHarmonic.Canon.actualIGAverage hIG₀ U
          (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω) := by
  filter_upwards [
    (aemeasurable_fieldAverage D hγ
      (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z).ae_eq_mk.symm,
    ae_phaseVersion_eq D hγ] with ω hfield hphase
  simp only [circleObservation, fieldAverageVersion,
    MatedCRTHarmonic.Canon.actualIGAverage]
  rw [hfield, hphase]

/-- The two actual circle-average processes on the reference sample. -/
def fieldCircleAverage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (r : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  LQGMetric.circleAvg (MatedCRTHarmonic.Canon.referenceSample D hγ ω).zeroConeField r z

def igCircleAverage (hIG₀ : Ω → MatedCRT.Field) (U : Ω → ℝ)
    (r : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  MatedCRTHarmonic.Canon.actualIGAverage hIG₀ U r z ω

/-- The (4.28) conditional mean of the literal masked density. -/
def conditionalMean
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  P[(maskedUStar D hγ ε q ζ z) |
    MeasurableSpace.comap (circleObservation D hγ ε q ζ z) inferInstance] ω

/-- The canonical pointwise masked source variable is measurable modulo null
sets. The event includes the actual IG phase. -/
theorem aemeasurable_maskedUStar
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) (z : ℂ) :
    AEMeasurable (maskedUStar D hγ ε q ζ z) P := by
  have hc : Measurable (fun ω => uStar ε η₀ ω z) := by
    have hp : Measurable (fun ω : Ω => (η₀ ω, z)) :=
      D.measurable_curves.2.2.1.prodMk measurable_const
    simpa only [Function.comp_def, uStar, MatedCRTHarmonic.Canon.realLocalPoint,
      MatedCRTHarmonic.GMS4F.realUStar] using
      (MatedCRTHarmonic.GMS4F.measurable_realUStar hε).comp hp
  have hE : NullMeasurableSet (localEvent D hγ ε q ζ z) P :=
    MatedCRTHarmonic.Canon.nullMeasurableSet_referenceLocalEvent D hγ hε z
  exact hc.aemeasurable.indicator₀ hE

/-- A fixed test pair realized on the canonical coupling. Its conditional
mean and global good event belong to the localized-observable construction;
The two geometric coordinates are fixed here by the frozen sample. -/
structure FixedTestRealization
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (ε q ζ ρ meanBound : ℝ) (domain : Set ℂ) (f : ℂ → ℝ) where
  observable : GMS4.Prop48LocalizedObservable P
  domain_eq : observable.domain = domain
  test_eq : observable.test = f
  meanConstant_eq : observable.meanConstant = meanBound
  uStar_eq : observable.uStar = uStar ε η₀
  localEvent_eq : observable.localEvent = localEvent D hγ ε q ζ
  goodEvent_eq : observable.goodEvent = goodEvent D hγ ε q ζ ρ
  conditionalMean_eq : observable.conditionalMean = conditionalMean D hγ ε q ζ

/-- The fixed-scale realization map is tied to the canonical sample. -/
structure AtScale
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ ρ : ℝ) where
  meanBound : ℝ
  realize_source : ∀ (domain : Set ℂ) (f : ℂ → ℝ),
    GMS4.Prop48TestPairAdmissible ρ domain f →
      FixedTestRealization D hγ ε q ζ ρ meanBound domain f

/-- Canonical all-scales realization data, with a common exponent chosen
before the test radius. The `atScale` field contains no probability estimate;
it only selects the actual localized observable on the frozen coupling. -/
structure Prop48WholePlaneAllScalesProducer
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (q ζ : ℝ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  meanBound : ℝ → ℝ
  atScale : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
    ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → AtScale D hγ ε q ζ ρ
  meanBound_eq : ∀ ρ (hρ : ρ ∈ Ioo (0 : ℝ) 1)
      ε (hε : ε ∈ Ioo (0 : ℝ) 1),
    (atScale ρ hρ ε hε).meanBound = meanBound ρ

end MatedCRTHarmonic.GMS4.Canonical


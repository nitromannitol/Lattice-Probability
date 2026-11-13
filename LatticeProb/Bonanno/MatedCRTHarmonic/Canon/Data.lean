/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Canon.Data at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.ConeRealization
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.MassClock
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.LogShift
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFWP
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge

/-!
# The two canonical quantum surfaces of the frozen mating coupling

The cone is the existing `MoTInput.cellModelOfCoupling`. The reference surface
uses the zero-quantum cone supplied by `areaParam₀`, retaining its underlying
normalized whole-plane GFF, IG field, phase, and Lebesgue-time curve. All
area and clock identities below are almost-sure, as in the frozen bundle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The zero-cone reference with its whole-plane GFF and IG/SLE inputs. -/
structure ReferenceSample where
  wholePlaneGFF : MatedCRT.Field
  wholePlaneArea : Measure ℂ
  igField : MatedCRT.Field
  phase : ℝ
  lebesgueCurve : C(ℝ, ℂ)
  zeroConeField : MatedCRT.Field
  area : Measure ℂ
  areaCurve : C(ℝ, ℂ)

/-- Fix the additive constant of a whole-plane GFF by its unit-circle average. -/
def normalizeWholePlane (h : MatedCRT.Field) : MatedCRT.Field :=
  LQGMetric.addConst h (-LQGMetric.circleAvg h 1 0)

/-- The `X₀` coordinate yields the required unit-circle-normalized
whole-plane GFF, with no extra probabilistic input. -/
theorem normalizedWPGFF_of_coupling
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    LQGMetric.IsNormalizedWPGFF (fun ω => normalizeWholePlane (X₀ ω)) P := by
  have hc : Measurable fun ω => -LQGMetric.circleAvg (X₀ ω) 1 0 :=
    ((LQGMetric.measurable_circleAvg_left 1 0).comp D.gff₀.measurable).neg
  refine ⟨D.gff₀.addConst hc, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero D.gff₀] with ω hω
  change LQGMetric.circleAvg
    (LQGMetric.addConst (X₀ ω) (-LQGMetric.circleAvg (X₀ ω) 1 0)) 1 0 = 0
  rw [hω, add_neg_cancel]

/-- The normalized whole-plane field is a measurable coordinate of the
frozen GFF, including its fixing additive constant. -/
theorem measurable_normalizedWholePlane
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable fun ω => normalizeWholePlane (X₀ ω) := by
  exact LQGMetric.DFGPS.L219.measurable_addConst_of D.gff₀.measurable
    (((LQGMetric.measurable_circleAvg_left 1 0).comp D.gff₀.measurable).neg)

def referenceSample
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) : ReferenceSample :=
  { wholePlaneGFF := normalizeWholePlane (X₀ ω)
    wholePlaneArea := CellScaling.lqgArea γ (normalizeWholePlane (X₀ ω))
    igField := hIG₀ ω
    phase := U ω
    lebesgueCurve := ηL ω
    zeroConeField := coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
    area := CellScaling.lqgArea γ (coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))
    areaCurve := η₀ ω }

/-- The frozen uniform phase law is non-atomic, so Mathlib's junk Dirac
branch for a non-a.e.-measurable `Measure.map` cannot occur. -/
theorem aemeasurable_phase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (fun ω => (referenceSample D hγ ω).phase) P := by
  have hχ : 0 < igChi γ := by
    have hsq : γ ^ 2 < 4 := by nlinarith [hγ.1, hγ.2]
    dsimp [igChi]
    apply sub_pos.mpr
    exact (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hγ.1).2 (by nlinarith)
  have hr : 0 < 2 * Real.pi * igChi γ := by positivity
  exact MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hr D.igField.2.1

/-- Normalized Lebesgue law of the independently sampled root. -/
def rootMeasure : Measure ℂ :=
  GMS4.GMSA.normalizedLebesgueOnRootingDisk

/-- The independent marked-root extension. Its second marginal is normalized
Lebesgue area on the open unit disk, and its first marginal is `P`. -/
def rootedLaw (P : Measure Ω) : Measure (Ω × ℂ) :=
  P.prod rootMeasure

/-- DMS A.10's field after adding the logarithmic root shift and resetting
its unit-circle average. -/
def rootedField (γ : ℝ) (h : MatedCRT.Field) (z₀ : ℂ) : MatedCRT.Field :=
  normalizeWholePlane (h + ConeLemmaA10.logRootingShift γ z₀)

/-- The Case 2 field removes `γ log max(|w|,1)` from the rooted field. -/
def case2Field (γ : ℝ) (h : MatedCRT.Field) (z₀ : ℂ) : MatedCRT.Field :=
  rootedField γ h z₀ - CellScaling.ofFunC (fun w => γ * Real.log (max ‖w‖ 1))

end MatedCRTHarmonic.Canon

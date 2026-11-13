/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Canon.Observable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Density
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.ClockMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Lemma49Observable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Transfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4F.RealObservable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.BundleAdapter
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.UStarMoments
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Packing
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ZeroConeScalingCells

/-!
# Real and measurable views of the canonical localized observables

The geometric degrees retain `ℕ∞` values. Their natural representatives are
total and agree with the geometry on the finite event. The local event uses
the actual two field averages at the radius in [18] (4.22).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The radius of the two conditioning circle averages in (4.22). -/
def conditioningRadius (ε q ζ : ℝ) : ℝ := ε ^ (q - 4 * ζ)

/-- The circle average of the IG field that actually drives the frozen
space-filling curve. The shared phase is a separate random coordinate. -/
def actualIGAverage (hIG₀ : Ω → MatedCRT.Field) (U : Ω → ℝ)
    (r : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  LQGMetric.circleAvg (hIG₀ ω) r z + U ω

theorem aemeasurable_actualIGAverage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (r : ℝ) (z : ℂ) :
    AEMeasurable (actualIGAverage hIG₀ U r z) P :=
  ((LQGMetric.measurable_circleAvg_left r z).comp
    D.igField.1.1.measurable).aemeasurable.add (aemeasurable_phase D hγ)

/-- Natural and real representatives of the geometric local quantities. -/
structure RealLocalPoint where
  areaRatio : ℝ
  degreeIn : ℕ
  degreeOut : ℕ
  uStar : ℝ

def realLocalPoint (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) : RealLocalPoint :=
  { areaRatio := GMS4F.realAreaRatio ε c z
    degreeIn := GMS4F.natDegreeIn ε c z
    degreeOut := GMS4F.natDegreeOut ε c z
    uStar := GMS4F.realUStar ε c z }

theorem realLocalPoint_formula (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) :
    (realLocalPoint ε c z).uStar = (realLocalPoint ε c z).areaRatio *
      (((realLocalPoint ε c z).degreeIn +
        (realLocalPoint ε c z).degreeOut : ℕ) : ℝ) := rfl

/-- Identification with the extended source objects on the exact finite
geometric event. This is the adapter needed before a natural-valued view. -/
theorem realLocalPoint_eq_geometric_of_finite
    {ε : ℝ} {c : C(ℝ, ℂ)} {z : ℂ}
    (hDA : GMS4b.areaRatio ε c z ≠ ⊤)
    (hIn : GMS4b.degreeIn ε c z ≠ ⊤)
    (hOut : GMS4b.degreeOut ε c z ≠ ⊤) :
    ENNReal.ofReal (realLocalPoint ε c z).areaRatio = (localPoint ε c z).DA ∧
    (((realLocalPoint ε c z).degreeIn : ℕ) : ℕ∞) = (localPoint ε c z).degreeIn ∧
    (((realLocalPoint ε c z).degreeOut : ℕ) : ℕ∞) =
      (localPoint ε c z).degreeOut ∧
    ENNReal.ofReal (realLocalPoint ε c z).uStar = (localPoint ε c z).uStar := by
  refine ⟨ENNReal.ofReal_toReal hDA, ENat.natCast_toNat_eq_self.mpr hIn,
    ENat.natCast_toNat_eq_self.mpr hOut, ?_⟩
  exact GMS4F.ofReal_realUStar_eq_geometric hDA hIn hOut

def referenceConditioningInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) :
    GMS4c.Lemma49Input :=
  (η₀ ω, (LQGMetric.circleAvg (referenceSample D hγ ω).zeroConeField
      (conditioningRadius ε q ζ) z,
    actualIGAverage hIG₀ U (conditioningRadius ε q ζ) z ω))

/-- The same (4.22) event on the zero-cone reference data. -/
def referenceLocalEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) : Set Ω :=
  (referenceConditioningInput D hγ ε q ζ z) ⁻¹' GMS4c.lemma49Event ε q ζ z

theorem aemeasurable_referenceConditioningInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    AEMeasurable (referenceConditioningInput D hγ ε q ζ z) P := by
  have hfield : AEMeasurable (fun ω => LQGMetric.circleAvg
      (referenceSample D hγ ω).zeroConeField (conditioningRadius ε q ζ) z) P :=
    (LQGMetric.measurable_circleAvg_left _ _).comp_aemeasurable
      (aemeasurable_reference_field D hγ)
  have hig := aemeasurable_actualIGAverage D hγ (conditioningRadius ε q ζ) z
  exact D.measurable_curves.2.2.1.aemeasurable.prodMk
    (hfield.prodMk hig)

theorem nullMeasurableSet_referenceLocalEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε q ζ : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    NullMeasurableSet (referenceLocalEvent D hγ ε q ζ z) P :=
  (aemeasurable_referenceConditioningInput D hγ ε q ζ z).nullMeasurableSet_preimage
    (GMS4c.measurableSet_lemma49Event hε z)

end MatedCRTHarmonic.Canon

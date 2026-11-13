/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalClockMeasurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.MassClock
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ContVersion
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea

/-!
# Measurable local mass clocks on the configuration space

On the finite-area part of the local configuration, the area of each compact
subsegment of a rational-point excursion is a Borel function of the stored
measure and stored excursion. This is the measurable input for reconstructing
quantum time from Lebesgue time in [18] Lemma 4.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open MatedCRTHarmonic.MoTPort
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

/-- The finite-area locus in the local configuration. Bounded `V` and a
locally finite LQG area measure place the source configuration here. -/
abbrev FiniteLocalConfiguration (V : TopologicalSpace.Opens ℂ) : Type :=
  {x : LocalConfiguration V // IsFiniteMeasure x.1.1}

/-- The restricted area measure, viewed as a finite measure on the
finite-area locus. -/
def finiteLocalArea {V : TopologicalSpace.Opens ℂ}
    (x : FiniteLocalConfiguration V) : FiniteMeasure ℂ :=
  ⟨x.1.1.1, x.2⟩

theorem measurable_finiteLocalArea (V : TopologicalSpace.Opens ℂ) :
    Measurable (finiteLocalArea (V := V)) :=
  (measurable_fst.comp (measurable_fst.comp measurable_subtype_coe)).subtype_mk

/-- A continuous version of the excursion segment at the rational point `q`.
For a genuine excursion this is the original segment. -/
def finiteLocalSegment {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) : C(ℝ, ℂ) :=
  contVersion (x.1.2 q)

theorem measurable_finiteLocalSegment (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) : Measurable (finiteLocalSegment (V := V) q) :=
  measurable_contVersion.comp
    ((measurable_pi_apply q).comp (measurable_snd.comp measurable_subtype_coe))

/-- The mass of a compact subsegment, determined by the finite local
configuration. -/
def localSegmentMass {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (a b : ℝ) (x : FiniteLocalConfiguration V) : ℝ≥0∞ :=
  massClock a b (finiteLocalArea x) (finiteLocalSegment q x)

theorem measurable_localSegmentMass (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) (a b : ℝ) :
    Measurable (localSegmentMass (V := V) q a b) :=
  (measurable_massClock a b).comp
    ((measurable_finiteLocalArea V).prodMk (measurable_finiteLocalSegment V q))

/-- The elapsed quantum-time coordinate of a compact excursion subsegment. -/
def localQuantumElapsed {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (a b : ℝ) (x : FiniteLocalConfiguration V) : ℝ :=
  (localSegmentMass q a b x).toReal

theorem measurable_localQuantumElapsed (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) (a b : ℝ) :
    Measurable (localQuantumElapsed (V := V) q a b) :=
  ENNReal.measurable_toReal.comp (measurable_localSegmentMass V q a b)

end MatedCRTHarmonic.GMS4c

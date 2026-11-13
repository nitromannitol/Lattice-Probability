/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.NaturalFiltration at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Minimal usual-augmentation adapter. Reuses mathlib's natural filtration,
measure completion and right continuation; adds only the null-event sigma algebra. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal

namespace ReflectedGMS.ProcessFiltration

/-- All subsets of null events in the original sample law. -/
def nullEventSigma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    MeasurableSpace (NullMeasurableSpace Ω P) :=
  MeasurableSpace.generateFrom {s : Set Ω | P s = 0}

/-- The usual augmentation of the natural filtration: reuse the actual natural
filtration, add all null events of the sample law in its measure completion,
and take mathlib's right continuation. No filtration is an extra hypothesis. -/
noncomputable def completedNaturalFiltration {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ) (hX : ∀ t, Measurable (X t)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
  let N : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
    Filtration.natural (Ω := NullMeasurableSpace Ω P) X (fun t =>
      (hX t).nullMeasurable.measurable'.stronglyMeasurable)
  Filtration.rightCont {
    seq := fun t => N t ⊔ nullEventSigma P
    mono' := fun _ _ h => sup_le_sup (N.mono h) le_rfl
    le' := fun t => sup_le (N.le t)
      (MeasurableSpace.generateFrom_le (fun _ hs => NullMeasurableSet.of_null hs)) }

end ReflectedGMS.ProcessFiltration

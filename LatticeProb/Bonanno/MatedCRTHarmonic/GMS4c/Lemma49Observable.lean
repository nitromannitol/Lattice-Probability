/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.Lemma49Observable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable

/-!
# The measurable masked point observable of [18] Lemma 4.9

For fixed `z`, the event `F^ε(z)` of [18] (4.22) is a Borel condition on
The quantum-time curve and two circle averages. The masked `u_*` is Borel.
The conditional moment estimate remains a separate proof obligation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b

/-- Input `(η, h_r(z), h^IG_r(z))` at a fixed spatial point. -/
abbrev Lemma49Input : Type := C(ℝ, ℂ) × (ℝ × ℝ)

private def lemma49At (z : ℂ) : Lemma49Input → C(ℝ, ℂ) × ℂ :=
  fun x => (x.1, z)

private theorem measurable_lemma49At (z : ℂ) : Measurable (lemma49At z) :=
  measurable_fst.prodMk measurable_const

private def lemma49Window (ε : ℝ) (z : ℂ) : Lemma49Input → ℝ :=
  (fun p : C(ℝ, ℂ) × ℂ => windowDiam ε p.1 p.2) ∘ lemma49At z

private def lemma49DegIn (ε : ℝ) (z : ℂ) : Lemma49Input → ℕ∞ :=
  (fun p : C(ℝ, ℂ) × ℂ => degreeIn ε p.1 p.2) ∘ lemma49At z

private def lemma49DegOut (ε : ℝ) (z : ℂ) : Lemma49Input → ℕ∞ :=
  (fun p : C(ℝ, ℂ) × ℂ => degreeOut ε p.1 p.2) ∘ lemma49At z

private theorem measurable_lemma49Window (ε : ℝ) (z : ℂ) :
    Measurable (lemma49Window ε z) :=
  (measurable_windowDiam ε).comp (measurable_lemma49At z)

private theorem measurable_lemma49DegIn (ε : ℝ) (z : ℂ) :
    Measurable (lemma49DegIn ε z) :=
  (measurable_degreeIn ε).comp (measurable_lemma49At z)

private theorem measurable_lemma49DegOut {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    Measurable (lemma49DegOut ε z) :=
  (measurable_degreeOut hε).comp (measurable_lemma49At z)

/-- [18] (4.22)'s three conditions. Infinite degree fails the finite cap. -/
def lemma49Event (ε q ζ : ℝ) (z : ℂ) : Set Lemma49Input :=
  {x | lemma49Window ε z x ≤ ε ^ q ∧
    (((lemma49DegIn ε z x + lemma49DegOut ε z x : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (ε ^ (-ζ))) ∧
    max |x.2.1| |x.2.2| ≤ 2 * q * Real.log ε⁻¹}

/-- The source event `F^ε(z)` is Borel. -/
theorem measurableSet_lemma49Event {ε q ζ : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    MeasurableSet (lemma49Event ε q ζ z) := by
  have hcoe : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := measurable_of_countable _
  have hsum : Measurable fun x : Lemma49Input =>
      (((lemma49DegIn ε z x + lemma49DegOut ε z x : ℕ∞) : ℝ≥0∞)) :=
    hcoe.comp ((measurable_of_countable (fun y : ℕ∞ × ℕ∞ => y.1 + y.2)).comp
      ((measurable_lemma49DegIn ε z).prodMk (measurable_lemma49DegOut hε z)))
  have hA : Measurable fun x : Lemma49Input => max |x.2.1| |x.2.2| :=
    ((measurable_fst.comp measurable_snd).abs).max
      ((measurable_snd.comp measurable_snd).abs)
  simpa only [lemma49Event, Set.ofPred_and] using
    (measurableSet_le (measurable_lemma49Window ε z)
      (measurable_const : Measurable fun _ : Lemma49Input => ε ^ q)).inter
      ((measurableSet_le hsum
        (measurable_const : Measurable fun _ : Lemma49Input => ENNReal.ofReal (ε ^ (-ζ)))).inter
      (measurableSet_le hA
        (measurable_const : Measurable fun _ : Lemma49Input => 2 * q * Real.log ε⁻¹)))

end MatedCRTHarmonic.GMS4c

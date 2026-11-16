import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # An integrated distance on measurable profiles -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

variable {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
  (μ : Measure α) [IsFiniteMeasure μ]

/-- Almost-everywhere measurable representatives of profiles. -/
def MeasurableProfile := {f : α → E // AEMeasurable f μ}

namespace MeasurableProfile

/-- The integrated truncated distance between two profile representatives. -/
noncomputable def integralDist (f g : MeasurableProfile (E := E) μ) : ℝ≥0∞ :=
  ∫⁻ x, min 1 (edist (f.1 x) (g.1 x)) ∂μ

omit [OpensMeasurableSpace E] [SecondCountableTopology E] in
lemma integralDist_ne_top (f g : MeasurableProfile (E := E) μ) :
    integralDist μ f g ≠ ∞ := by
  apply ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
  calc
    integralDist μ f g ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂μ :=
      lintegral_mono fun _ => min_le_left _ _
    _ = μ Set.univ := by simp

omit [OpensMeasurableSpace E] [SecondCountableTopology E] [IsFiniteMeasure μ] in
lemma integralDist_self (f : MeasurableProfile (E := E) μ) : integralDist μ f f = 0 := by
  simp [integralDist]

omit [OpensMeasurableSpace E] [SecondCountableTopology E] [IsFiniteMeasure μ] in
lemma integralDist_comm (f g : MeasurableProfile (E := E) μ) :
    integralDist μ f g = integralDist μ g f := by
  simp only [integralDist, edist_comm]

omit [IsFiniteMeasure μ] in
lemma integralDist_triangle (f g h : MeasurableProfile (E := E) μ) :
    integralDist μ f h ≤ integralDist μ f g + integralDist μ g h := by
  have hm : AEMeasurable (fun x => min 1 (edist (f.1 x) (g.1 x))) μ :=
    aemeasurable_const.min (f.2.edist g.2)
  calc
    integralDist μ f h ≤ ∫⁻ x, (min 1 (edist (f.1 x) (g.1 x)) +
        min 1 (edist (g.1 x) (h.1 x))) ∂μ := by
      apply lintegral_mono
      intro x
      have ht := edist_triangle (f.1 x) (g.1 x) (h.1 x)
      by_cases ha : 1 ≤ edist (f.1 x) (g.1 x)
      · simp [min_eq_left ha]
      by_cases hb : 1 ≤ edist (g.1 x) (h.1 x)
      · simp [min_eq_left hb]
      · simp only [min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb)]
        exact (min_le_right _ _).trans ht
    _ = integralDist μ f g + integralDist μ g h := lintegral_add_left' hm _

/-- Profiles carry the integrated truncated-distance pseudometric. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (MeasurableProfile (E := E) μ) where
  dist f g := (integralDist μ f g).toReal
  dist_self f := by rw [integralDist_self, ENNReal.toReal_zero]
  dist_comm f g := by rw [integralDist_comm μ f g]
  dist_triangle f g h := by
    have hfg := integralDist_ne_top μ f g
    have hgh := integralDist_ne_top μ g h
    rw [← ENNReal.toReal_add hfg hgh]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfg, hgh⟩)
      (integralDist_triangle μ f g h)

end MeasurableProfile
end LatticeProb

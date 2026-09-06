/-
The Harris inequality on the two cases the papers use: the discrete cube
`ι → Bool` and the continuous cube `ι → ℝ`.

`LatticeProb.infinitePi_harris` is stated for an arbitrary family of linearly
ordered measurable spaces, so both cases are instances of it.  They are recorded
separately because they are how the inequality is cited: an i.i.d. field of
open and closed sites is a product measure on `ι → Bool`, and an i.i.d. field of
real weights is a product measure on `ι → ℝ`.
-/
import LatticeProb.Prob.HarrisVariants

open MeasureTheory Measure

namespace LatticeProb

variable {ι : Type*}

/-- **The Harris inequality on the discrete cube.**  For a product of Bernoulli
measures on `ι → Bool` and two increasing measurable events, the events are
positively correlated. -/
theorem infinitePi_harris_bool (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] {A B : Set (ι → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real A * (infinitePi μ).real B ≤ (infinitePi μ).real (A ∩ B) :=
  infinitePi_harris μ hA hB hAm hBm

/-- **The Harris inequality on the continuous cube.**  For a product measure on
`ι → ℝ` and two increasing measurable events, the events are positively
correlated. -/
theorem infinitePi_harris_real (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {A B : Set (ι → ℝ)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real A * (infinitePi μ).real B ≤ (infinitePi μ).real (A ∩ B) :=
  infinitePi_harris μ hA hB hAm hBm

/-- The Harris inequality on the discrete cube for decreasing events. -/
theorem infinitePi_harris_bool_lower (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] {A B : Set (ι → Bool)}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real A * (infinitePi μ).real B ≤ (infinitePi μ).real (A ∩ B) :=
  infinitePi_harris_lower μ hA hB hAm hBm

/-- The Harris inequality on the discrete cube for one increasing and one
decreasing event: they are negatively correlated. -/
theorem infinitePi_harris_bool_upper_lower (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] {A B : Set (ι → Bool)}
    (hA : IsUpperSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real (A ∩ B) ≤ (infinitePi μ).real A * (infinitePi μ).real B :=
  infinitePi_harris_upper_lower μ hA hB hAm hBm

end LatticeProb

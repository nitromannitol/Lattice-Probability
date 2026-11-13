/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop410 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Hölder transfer for [18] Proposition 4.10

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*. In Case 1 of the proof
, the law of the rooted field is the whole-plane GFF law weighted
by its LQG mass, and Hölder's inequality transfers a polynomial bad-event
probability under the unweighted law to the weighted law.

This file isolates that measure-theoretic step. It does not assert Proposition
4.10 or any field-law identification. A later producer must supply the
source-specific density identity. For the first rooting step this identity is
The whole-plane clause of DMS14 Lemma A.10
.

The proof specializes Mathlib's `ENNReal.lintegral_mul_le_Lp_mul_Lq`. The
closest project result is `GMSAppA.lintegral_rpow_indicator_le`, which proves a
more specialized indicator estimate for the long-range argument; the theorem
below works directly with `Measure.withDensity`, the form needed here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

/-- Hölder transfer of an event mass through an explicit nonnegative
Radon–Nikodym density. If `Q = P.withDensity d` and `p,q` are Hölder
conjugates, then
`Q(A) ≤ (∫ d^p dP)^(1/p) P(A)^(1/q)`.

The statement is valid for an arbitrary measure `P`; probability-measure
instances enter only in the source-specific applications.

This is the abstract probability-transfer step used in [18], proof of
Proposition 4.10, Case 1. -/
theorem withDensity_event_le_holder {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : Ω → ℝ≥0∞) (hd : AEMeasurable d P)
    {A : Set Ω} (hA : MeasurableSet A) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    (P.withDensity d) A ≤
      (∫⁻ ω, d ω ^ p ∂P) ^ (1 / p) * P A ^ (1 / q) := by
  rw [withDensity_apply d hA]
  rw [← lintegral_indicator hA]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hd
    ((aemeasurable_const : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P).indicator hA)
  have hleft :
      (fun x => d x * A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) x) = A.indicator d := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hright :
      (fun x => (A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) x) ^ q) =
        A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx, ENNReal.zero_rpow_of_pos hpq.symm.pos]
  change (∫⁻ x, d x * A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) x ∂P) ≤
    (∫⁻ x, d x ^ p ∂P) ^ (1 / p) *
      (∫⁻ x, (A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) x) ^ q ∂P) ^ (1 / q) at h
  have hone : (∫⁻ x, A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) x ∂P) = P A := by
    simp [hA]
  rw [hleft, hright, hone] at h
  simpa only [one_div] using h

/-- Quantitative bad-event form of `withDensity_event_le_holder`: a reference
event-mass bound `P(A) ≤ δ` transfers with exponent `1/q`. -/
theorem withDensity_badEvent_le_holder {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : Ω → ℝ≥0∞) (hd : AEMeasurable d P)
    {A : Set Ω} (hA : MeasurableSet A) {p q : ℝ}
    (hpq : p.HolderConjugate q) {δ : ℝ≥0∞} (hbad : P A ≤ δ) :
    (P.withDensity d) A ≤
      (∫⁻ ω, d ω ^ p ∂P) ^ (1 / p) * δ ^ (1 / q) := by
  refine (withDensity_event_le_holder P d hd hA hpq).trans ?_
  gcongr
  exact hpq.symm.one_div_nonneg

end MatedCRTHarmonic.GMS4


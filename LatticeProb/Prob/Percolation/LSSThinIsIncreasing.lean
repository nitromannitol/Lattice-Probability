/-
# Event-side transport of the thin-form complement bridge on the planar carrier

The complement bridge of `LatticeProb.Prob.Percolation.LSSThinInstantiation` turns dense
domination on increasing events into thin domination.  This module records that transport at the
level of events on the concrete planar carrier `ℤ × ℤ`: the membership relation for the complement
image, the order reversal of the bit complement, the equivalence between an increasing event and
the decreasing complement image, the measure-complement inequality that carries dense domination
from increasing events to decreasing ones, and finally the exact conclusion
`μ A ≤ bernoulliField(1/8) A` for every measurable increasing `A`, given the dense hypothesis.

The dense half is an explicit hypothesis throughout; no domination statement is proved here, no
`Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/

import LatticeProb.Prob.Percolation.LSSThinInstantiation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

variable {S : Type}

/-- The planar Bernoulli product field `bernoulliField p` of the thin-form input, on `ℤ × ℤ`. -/
noncomputable def bernoulliFieldPlanar (p : NNReal) (hp : p ≤ 1) :
    Measure (PlanarCarrier → Bool) :=
  bitProduct p hp PlanarCarrier

instance bernoulliFieldPlanar.instIsProbabilityMeasure (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliFieldPlanar p hp) := by
  unfold bernoulliFieldPlanar; infer_instance

/-! ### The event-side complement relations -/

/-- Membership in the complement image: `ω` lies in `bitCompl '' A` exactly when its bit
complement lies in `A`. -/
theorem mem_bitCompl_image_iff (A : Set (PlanarCarrier → Bool)) (ω : PlanarCarrier → Bool) :
    ω ∈ bitCompl '' A ↔ bitCompl ω ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨bitCompl ω, by simpa using h, by simp⟩

/-- **The bit complement reverses the coordinatewise order.** -/
theorem leField_bitCompl_iff {x y : PlanarCarrier → Bool} :
    leField (bitCompl y) (bitCompl x) ↔ leField x y := by
  unfold leField
  constructor
  · intro h s hx
    by_contra hy
    have hy' : y s = false := by
      cases hys : y s with
      | false => rfl
      | true => exact absurd hys hy
    have hx' : bitCompl x s = true := h s (by rw [bitCompl_apply, hy']; rfl)
    rw [bitCompl_apply, hx] at hx'
    exact Bool.noConfusion hx'
  · intro h s hy
    by_contra hx
    have hxt : x s = true := by
      cases hxs : x s with
      | true => rfl
      | false => exact absurd (by rw [bitCompl_apply, hxs]; rfl) hx
    have hyt : y s = true := h s hxt
    rw [bitCompl_apply, hyt] at hy
    exact Bool.noConfusion hy

/-- **An increasing event is exactly the complement image of a decreasing event**, and
conversely.  Both directions of the complement relation are recorded. -/
theorem isIncreasingSet_iff_isDecreasingSet_compl (A : Set (PlanarCarrier → Bool)) :
    StrassenAux.IsIncreasingSet A ↔ IsDecreasingSet (bitCompl '' A) := by
  constructor
  · exact isDecreasingSet_bitCompl_image
  · intro hA
    rw [isIncreasingSet_iff_leField]
    intro x y hx hle
    have hx' : bitCompl x ∈ bitCompl '' A := ⟨x, hx, rfl⟩
    have hle' : leField (bitCompl y) (bitCompl x) := leField_bitCompl_iff.mpr hle
    obtain ⟨a, ha, haeq⟩ := hA (bitCompl x) (bitCompl y) hx' hle'
    rwa [show a = y from by
      rw [← bitCompl_involutive a, haeq, bitCompl_involutive]] at ha

/-! ### The measure-complement inequality -/

/-- **Dense domination bounds every decreasing planar event from above.** -/
theorem measure_complement_inequality {Q ν : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] (hdense : DenseLower Q ν)
    {D : Set (PlanarCarrier → Bool)} (hD : MeasurableSet D) (hdec : IsDecreasingSet D) :
    ν D ≤ Q D :=
  le_of_dense_of_isDecreasing hdense D hD hdec

/-- The complement image of an increasing event carries the original probability under the
complement field. -/
theorem measure_bitCompl_image {ν μ : Measure (PlanarCarrier → Bool)}
    (hν : μ.map bitCompl = ν) {A : Set (PlanarCarrier → Bool)} (hA : MeasurableSet A) :
    ν (bitCompl '' A) = μ A := by
  rw [← hν, Measure.map_apply measurable_bitCompl (measurableSet_bitCompl_image hA),
    bitCompl_preimage_image]

/-! ### The complementary-parameter fields -/

theorem one_sub_one_eighth : (1 : NNReal) - 1 / 8 = 7 / 8 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub one_eighth_le_one]
  push_cast
  norm_num

/-- Two product fields with the same parameter are equal regardless of the proof of the
parameter bound. -/
theorem bitProduct_congr {p q : NNReal} (hp : p ≤ 1) (hq : q ≤ 1) (h : p = q) :
    bitProduct p hp S = bitProduct q hq S := by
  subst h
  exact congrArg (fun h' : p ≤ 1 => bitProduct p h' S) (Subsingleton.elim hp hq)

/-- **The planar `7/8` field is the complement pushforward of the `1/8` field.** -/
theorem bernoulliFieldPlanar_seven_eighths_eq_map {A : Set (PlanarCarrier → Bool)}
    (hA : MeasurableSet A) :
    bernoulliFieldPlanar (7 / 8) seven_eighths_le_one (bitCompl '' A)
      = bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  have hcomp : (bernoulliFieldPlanar (1 / 8) one_eighth_le_one).map bitCompl
      = bernoulliFieldPlanar (7 / 8) seven_eighths_le_one := by
    rw [bernoulliFieldPlanar, bernoulliFieldPlanar,
      bitProduct_map_bitCompl (S := PlanarCarrier) (1 / 8) one_eighth_le_one,
      bitProduct_congr (S := PlanarCarrier) tsub_le_self seven_eighths_le_one
        one_sub_one_eighth]
  rw [← hcomp, Measure.map_apply measurable_bitCompl (measurableSet_bitCompl_image hA),
    bitCompl_preimage_image]

/-! ### The thin conclusion for the exact increasing event -/

/-- **The event-side thin conclusion.**  Given the dense domination hypothesis at density `7/8`
on the complement field, every measurable increasing planar event `A` satisfies
`μ A ≤ bernoulliField(1/8) A`.  This is the measure-complement inequality applied to the
complement image of `A`, with the parameter arithmetic `1 - 7/8 = 1/8`. -/
theorem thin_of_dense_isIncreasing {ν μ : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : μ.map bitCompl = ν)
    (hdense : DenseLower (bernoulliFieldPlanar (7 / 8) seven_eighths_le_one) ν)
    {A : Set (PlanarCarrier → Bool)} (hA : MeasurableSet A)
    (hinc : StrassenAux.IsIncreasingSet A) :
    μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  have hDmeas : MeasurableSet (bitCompl '' A) := measurableSet_bitCompl_image hA
  have hDdec : IsDecreasingSet (bitCompl '' A) := isDecreasingSet_bitCompl_image hinc
  have hupper : ν (bitCompl '' A)
      ≤ bernoulliFieldPlanar (7 / 8) seven_eighths_le_one (bitCompl '' A) :=
    measure_complement_inequality hdense hDmeas hDdec
  have hμA : ν (bitCompl '' A) = μ A := measure_bitCompl_image hν hA
  calc μ A = ν (bitCompl '' A) := hμA.symm
    _ ≤ bernoulliFieldPlanar (7 / 8) seven_eighths_le_one (bitCompl '' A) := hupper
    _ = bernoulliFieldPlanar (1 / 8) one_eighth_le_one A :=
        bernoulliFieldPlanar_seven_eighths_eq_map hA

end LatticeProb.Percolation

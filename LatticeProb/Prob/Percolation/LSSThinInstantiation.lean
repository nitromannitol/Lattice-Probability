/-
# Instantiation of the thin-form complement bridge on the planar carrier

The deterministic complement bridge of `LatticeProb.Prob.Percolation.LSSThinComplement` is
stated for a general carrier `S → Bool`.  This module instantiates it on the concrete planar
carrier `ℤ × ℤ`, with finite-range parameter `k = 2`, which is the carrier and range of the
thin-form domination input.  It proves the carrier-specific transport lemmas — the finite-range
dependence predicate in the `ℓ^∞` form, its transport across the bit complement, the one-site
probability transport, and the pushforward of the concrete Bernoulli product field — and then
the full bridge with the dense half entering as an explicit transported hypothesis.

No domination statement is proved here; the dense half is an explicit hypothesis of
`thinUpper_of_transported_dense_planar`.  No `Prop` is frozen and nothing is claimed about
`Rotor.External.LSS`.
-/

import LatticeProb.Prob.Percolation.LSSThinComplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-- The planar carrier `ℤ × ℤ` of the rotor percolation model. -/
abbrev PlanarCarrier := ℤ × ℤ

/-! ### Carrier measurability -/

theorem measurable_finsetRestrict_planar (I : Finset PlanarCarrier) :
    Measurable (fun ω : PlanarCarrier → Bool => fun i : I => ω i) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : PlanarCarrier)

theorem measurable_finsetCompl_planar (I : Finset PlanarCarrier) :
    Measurable (fun f : I → Bool => fun i : I => !(f i)) :=
  measurable_pi_lambda _ fun i => measurable_bool_not.comp (measurable_pi_apply i)

/-- The complement image of an increasing planar event is decreasing. -/
theorem isDecreasingSet_bitCompl_image_planar {A : Set (PlanarCarrier → Bool)}
    (hA : StrassenAux.IsIncreasingSet A) : IsDecreasingSet (bitCompl '' A) :=
  isDecreasingSet_bitCompl_image hA

/-! ### Finite-range dependence on the planar carrier -/

/-- The finite-range dependence predicate on the planar carrier: two finite index sets
separated by more than `k` in one of the two coordinates have independent restrictions.  This
is the `ℓ^∞` form of the dependence condition of the Liggett--Schonmann--Stacey statement. -/
def KDependentPlanar (k : ℕ) (μ : Measure (PlanarCarrier → Bool)) : Prop :=
  ∀ I J : Finset PlanarCarrier,
    (∀ i ∈ I, ∀ j ∈ J, (k : ℤ) < max |i.1 - j.1| |i.2 - j.2|) →
    IndepFun (fun ω : PlanarCarrier → Bool => fun i : I => ω i)
      (fun ω => fun j : J => ω j) μ

/-- **Finite-range dependence transports across the bit complement** on the planar carrier: a
`k`-dependent planar field remains `k`-dependent after complementing every bit. -/
theorem kDependentPlanar_map_bitCompl (k : ℕ) {μ : Measure (PlanarCarrier → Bool)}
    [IsFiniteMeasure μ] (h : KDependentPlanar k μ) :
    KDependentPlanar k (μ.map bitCompl) := by
  intro I J hfar
  have h' := h I J hfar
  refine (indepFun_map_iff_of_measurable (T := bitCompl) measurable_bitCompl
    (measurable_finsetRestrict_planar I) (measurable_finsetRestrict_planar J) μ).mpr ?_
  have := h'.comp (measurable_finsetCompl_planar I) (measurable_finsetCompl_planar J)
  exact this

/-! ### One-site transport and the Bernoulli pushforward -/

/-- The complement field exchanges the one-site events on the planar carrier. -/
theorem compl_map_oneSite_planar (μ : Measure (PlanarCarrier → Bool)) (s : PlanarCarrier) :
    (μ.map bitCompl) {ω | ω s = true} = μ {ω | ω s = false} := by
  have hs : MeasurableSet {ω : PlanarCarrier → Bool | ω s = true} := by
    have h : {ω : PlanarCarrier → Bool | ω s = true} =
        (fun f : PlanarCarrier → Bool => f s) ⁻¹' ({true} : Set Bool) := by
      ext ω; simp
    rw [h]
    exact (measurable_pi_apply s) (measurableSet_singleton true)
  rw [Measure.map_apply measurable_bitCompl hs]
  congr 1
  ext ω
  simp [bitCompl]

/-- **The concrete Bernoulli product field on `ℤ × ℤ` is complemented by complementing its
parameter.**  For `p = 1/8` this is the pushforward of the field the thin input dominates by. -/
theorem bernoulliProductPlanar_map_bitCompl (p : NNReal) (hp : p ≤ 1) :
    (bitProduct p hp PlanarCarrier).map bitCompl
      = bitProduct (1 - p) tsub_le_self PlanarCarrier :=
  bitProduct_map_bitCompl (S := PlanarCarrier) p hp

/-! ### The bridge on the planar carrier -/

/-- **The `1/8` thin form on `ℤ × ℤ` from the dense form at `7/8`.** -/
theorem thinUpper_eighth_planar {ν μ : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : μ.map bitCompl = ν)
    (hdense : DenseLower (bitProduct (7 / 8) seven_eighths_le_one PlanarCarrier) ν) :
    ThinUpper (bitProduct (1 / 8) one_eighth_le_one PlanarCarrier) μ :=
  thinUpper_eighth_of_dense_seven_eighths (S := PlanarCarrier) hν hdense

/-- **The deterministic bridge on the planar carrier, parameterised by the exact transported
dense-domination hypothesis.**  The dense half is an explicit hypothesis on the complement
field; its dependence and one-site-density preconditions are met on the complement field by
`kDependentPlanar_map_bitCompl` and `compl_map_oneSite_planar`, and the parameter arithmetic is
`1 - 7/8 = 1/8`. -/
theorem thinUpper_of_transported_dense_planar (p : ℝ)
    (hdense : ∀ ν : Measure (PlanarCarrier → Bool), IsProbabilityMeasure ν →
      KDependentPlanar 2 ν →
      (∀ s : PlanarCarrier, ENNReal.ofReal p ≤ ν {ω | ω s = true}) →
      DenseLower (bitProduct (7 / 8) seven_eighths_le_one PlanarCarrier) ν)
    {μ : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure μ]
    (hKD : KDependentPlanar 2 μ)
    (hsite : ∀ s : PlanarCarrier, ENNReal.ofReal p ≤ μ {ω | ω s = false}) :
    ThinUpper (bitProduct (1 / 8) one_eighth_le_one PlanarCarrier) μ := by
  haveI : IsProbabilityMeasure (μ.map bitCompl) :=
    Measure.isProbabilityMeasure_map measurable_bitCompl.aemeasurable
  have hKDν : KDependentPlanar 2 (μ.map bitCompl) := kDependentPlanar_map_bitCompl 2 hKD
  have hsiteν : ∀ s : PlanarCarrier,
      ENNReal.ofReal p ≤ (μ.map bitCompl) {ω | ω s = true} := by
    intro s
    rw [compl_map_oneSite_planar]
    exact hsite s
  have hd : DenseLower (bitProduct (7 / 8) seven_eighths_le_one PlanarCarrier)
      (μ.map bitCompl) :=
    hdense (μ.map bitCompl) inferInstance hKDν hsiteν
  exact thinUpper_eighth_of_dense_seven_eighths (S := PlanarCarrier) rfl hd

end LatticeProb.Percolation

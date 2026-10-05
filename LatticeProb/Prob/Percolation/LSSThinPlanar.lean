/-
# The final planar thin statement assembled from the complement bridge

This module composes the planar dependence transport and the event-side complement bridge into
one statement: for a probability field law `μ` on `ℤ × ℤ` that is `2`-dependent, has one-site
probability at most `2ε`, and whose bit complement satisfies the dense domination hypothesis at
density `7/8`, every measurable increasing event `A` satisfies
`μ A ≤ bernoulliField(1/8) A`.

The dense half is an explicit hypothesis, quantified uniformly over the field law; no domination
statement is proved here, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/

import LatticeProb.Prob.Percolation.LSSThinIsIncreasing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-! ### The one-site complement relation on the planar carrier -/

/-- The one-site probabilities of a planar probability law sum to one. -/
theorem planar_oneSite_compl (μ : Measure (PlanarCarrier → Bool)) [IsProbabilityMeasure μ]
    (s : PlanarCarrier) :
    μ {ω | ω s = false} = 1 - μ {ω | ω s = true} := by
  have hs : MeasurableSet {ω : PlanarCarrier → Bool | ω s = true} := by
    have h : {ω : PlanarCarrier → Bool | ω s = true} =
        (fun f : PlanarCarrier → Bool => f s) ⁻¹' ({true} : Set Bool) := by
      ext ω; simp
    rw [h]
    exact (measurable_pi_apply s) (measurableSet_singleton true)
  have h : {ω : PlanarCarrier → Bool | ω s = false} = {ω | ω s = true}ᶜ := by
    ext ω; simp
  rw [h, prob_compl_eq_one_sub hs]

/-- The arithmetic identity `ofReal (1 - 2ε) = 1 - ofReal (2ε)` for `0 ≤ ε`; no upper bound on
`2ε` is needed, since both sides collapse to `0` when `2ε > 1`. -/
theorem ofReal_one_sub_two_mul {ε : ℝ} (hε : 0 ≤ ε) :
    ENNReal.ofReal (1 - 2 * ε) = 1 - ENNReal.ofReal (2 * ε) := by
  rw [ENNReal.ofReal_sub (1 : ℝ) (q := 2 * ε) (by linarith), ENNReal.ofReal_one]

/-! ### The dense hypothesis and the one-site transfer -/

/-- The dense domination hypothesis at density `7/8`, uniform over the field law: a probability
`2`-dependent field whose one-site probability is at least `p` dominates the `7/8` product field
on increasing events. -/
def DenseSevenEighths (p : ℝ) : Prop :=
  ∀ ν : Measure (PlanarCarrier → Bool), IsProbabilityMeasure ν → KDependentPlanar 2 ν →
    (∀ s : PlanarCarrier, ENNReal.ofReal p ≤ ν {ω | ω s = true}) →
    DenseLower (bernoulliFieldPlanar (7 / 8) seven_eighths_le_one) ν

/-- **The one-site transfer.**  If a planar law has one-site probability at most `2ε` and
`p ≤ 1 - 2ε`, then the complement field has one-site probability at least `p`. -/
theorem oneSite_compl_le {μ : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure μ]
    {p ε : ℝ} (hε : 0 ≤ ε) (hp : p ≤ 1 - 2 * ε)
    (hsite : ∀ s : PlanarCarrier, μ {ω | ω s = true} ≤ ENNReal.ofReal (2 * ε))
    (s : PlanarCarrier) :
    ENNReal.ofReal p ≤ (μ.map bitCompl) {ω | ω s = true} := by
  rw [compl_map_oneSite_planar]
  calc ENNReal.ofReal p ≤ ENNReal.ofReal (1 - 2 * ε) := ENNReal.ofReal_le_ofReal hp
    _ = 1 - ENNReal.ofReal (2 * ε) := ofReal_one_sub_two_mul hε
    _ ≤ μ {ω | ω s = false} := by
        rw [planar_oneSite_compl]
        exact tsub_le_tsub_left (hsite s) 1

/-! ### The final planar thin statement -/

/-- **The final planar thin statement.**  Let `μ` be a probability field law on `ℤ × ℤ` that is
`2`-dependent, has one-site probability at most `2ε`, and whose complement field satisfies the
dense domination hypothesis `DenseSevenEighths p` for some density `p ≤ 1 - 2ε`.  Then every
measurable increasing event `A` satisfies `μ A ≤ bernoulliField(1/8) A`.  The dependence
condition passes to the complement field by the planar transport, and the one-site condition
passes by the complement inequality; the two feed the event-side bridge.  The parameter `ε` and
the density `p` are uniform over the field law. -/
theorem thinPlanar_of_dense {p ε : ℝ} (hε : 0 ≤ ε)
    (hp : p ≤ 1 - 2 * ε) (hdense : DenseSevenEighths p)
    {μ : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure μ]
    (hKD : KDependentPlanar 2 μ)
    (hsite : ∀ s : PlanarCarrier, μ {ω | ω s = true} ≤ ENNReal.ofReal (2 * ε))
    {A : Set (PlanarCarrier → Bool)} (hA : MeasurableSet A)
    (hinc : StrassenAux.IsIncreasingSet A) :
    μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  haveI : IsProbabilityMeasure (μ.map bitCompl) :=
    Measure.isProbabilityMeasure_map measurable_bitCompl.aemeasurable
  have hKDν : KDependentPlanar 2 (μ.map bitCompl) := kDependentPlanar_map_bitCompl 2 hKD
  have hsiteν : ∀ s : PlanarCarrier,
      ENNReal.ofReal p ≤ (μ.map bitCompl) {ω | ω s = true} :=
    fun s => oneSite_compl_le hε hp hsite s
  have hbridge : DenseLower (bernoulliFieldPlanar (7 / 8) seven_eighths_le_one)
      (μ.map bitCompl) :=
    hdense (μ.map bitCompl) inferInstance hKDν hsiteν
  exact thin_of_dense_isIncreasing (ν := μ.map bitCompl) rfl hbridge hA hinc

end LatticeProb.Percolation

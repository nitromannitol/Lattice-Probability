/-
# The one-site probability transport of the planar complement bridge

The complement bridge on `ℤ × ℤ` is fed by two hypotheses on the field law: finite-range
dependence and a one-site probability bound.  This module isolates the one-site side.  It proves
the one-site marginal pushforward under the bit complement, the resulting one-site probability
transport, and the bound transfer that turns a one-site upper bound `≤ 2ε` into the lower bound
`ofReal (1 - 2ε)` on the complement field, uniformly in the site.  That lower bound is exactly the
density input the dense domination hypothesis needs, with `ε ≤ (1 - p)/2`.

No domination statement is proved here, no `Prop` is frozen, no rotor file is touched, and
nothing is claimed about `Rotor.External.LSS`.
-/

import LatticeProb.Prob.Percolation.LSSThinPlanar

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-! ### The one-site marginal under the bit complement -/

/-- **The one-site marginal of the complement field is the bit complement of the one-site
marginal.**  Pushing a planar field forward by the bit complement and then reading the site `s`
is the same as reading the site first and then complementing the resulting bit. -/
theorem oneSite_marginal_pushforward (μ : Measure (PlanarCarrier → Bool)) (s : PlanarCarrier) :
    Measure.map (fun ω : PlanarCarrier → Bool => ω s) (μ.map bitCompl)
      = Measure.map (fun b : Bool => !b)
          (Measure.map (fun ω : PlanarCarrier → Bool => ω s) μ) := by
  rw [Measure.map_map (measurable_pi_apply s) measurable_bitCompl,
    Measure.map_map measurable_bool_not (measurable_pi_apply s)]
  rfl

/-- **The one-site probability transport.**  The complement field sets the site `s` exactly when
the original field clears it. -/
theorem oneSite_prob_pushforward (μ : Measure (PlanarCarrier → Bool)) (s : PlanarCarrier) :
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

/-- The one-site marginal identification, read as an equality of the two scalar marginals. -/
theorem oneSite_marginal_map_eq (μ : Measure (PlanarCarrier → Bool)) (s : PlanarCarrier) :
    (μ.map bitCompl).map (fun ω : PlanarCarrier → Bool => ω s)
      = (μ.map (fun ω : PlanarCarrier → Bool => ω s)).map (fun b : Bool => !b) :=
  oneSite_marginal_pushforward μ s

/-! ### The bound transfer -/

/-- **The one-site bound transfer.**  If every one-site probability of the planar field is at
most `2ε`, then every one-site probability of the complement field is at least `ofReal (1 - 2ε)`.
This is the uniform density input the dense domination hypothesis consumes, with `ε ≤ (1-p)/2`
for a required lower bound `p`. -/
theorem oneSite_compl_lower_bound {μ : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure μ]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsite : ∀ s : PlanarCarrier, μ {ω | ω s = true} ≤ ENNReal.ofReal (2 * ε))
    (s : PlanarCarrier) :
    ENNReal.ofReal (1 - 2 * ε) ≤ (μ.map bitCompl) {ω | ω s = true} := by
  rw [oneSite_prob_pushforward]
  calc ENNReal.ofReal (1 - 2 * ε) = 1 - ENNReal.ofReal (2 * ε) := ofReal_one_sub_two_mul hε
    _ ≤ μ {ω | ω s = false} := by
        rw [planar_oneSite_compl]
        exact tsub_le_tsub_left (hsite s) 1

/-- The one-site bound transfer stated as a lower bound at every site, with the density chosen
so that the dense hypothesis threshold is `1 - 2ε`. -/
theorem oneSite_forall_compl_lower_bound {μ : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure μ] {ε p : ℝ} (hε : 0 ≤ ε) (hp : p ≤ 1 - 2 * ε)
    (hsite : ∀ s : PlanarCarrier, μ {ω | ω s = true} ≤ ENNReal.ofReal (2 * ε)) :
    ∀ s : PlanarCarrier, ENNReal.ofReal p ≤ (μ.map bitCompl) {ω | ω s = true} := by
  intro s
  exact le_trans (ENNReal.ofReal_le_ofReal hp) (oneSite_compl_lower_bound hε hsite s)

end LatticeProb.Percolation

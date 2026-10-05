/-
# The complete conditional thin-LSS bridge

This module packages every deterministic ingredient of the thin-form Liggett--Schonmann--Stacey
bridge into one consumer theorem.  The dense half is an explicit hypothesis on the planar
carner; from it the theorem produces `ε > 0` such that every probability `2`-dependent planar
field with one-site probability at most `2ε` is dominated on increasing events by the product
Bernoulli field of density `1/8`.  The proof composes the complement dependence transport, the
one-site bound transfer, and the increasing-event complement relation, with `ε` uniform over the
field law.

A companion statement transports the same result to the two-dimensional lattice carrier
`Fin 2 → ℤ` through the coordinate identification, so that the bridge can be consumed on either
carrier.

No domination statement is proved here, no `Prop` is frozen, no rotor file is touched, and
nothing is claimed unconditionally about `Rotor.External.LSS`.
-/

import LatticeProb.Prob.Percolation.LSSThinOneSite
import LatticeProb.Prob.Percolation.LSSThinKDependent

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-! ### The packaged planar bridge -/

/-- **The complete conditional thin-LSS bridge.**  Assume the dense domination hypothesis at
some density `p < 1` on the planar carrier `ℤ × ℤ`.  Then there is `ε > 0`, with `p = 1 - 2ε`,
such that every probability `2`-dependent planar field whose one-site probability is at most
`2ε` satisfies `μ A ≤ bernoulliField(1/8) A` for every measurable increasing event `A`.  The
dependence condition passes to the complement field (`kDependentPlanar_map_bitCompl`), the
one-site condition passes to the density lower bound (`oneSite_compl_lower_bound`), and the
increasing-event complement relation (`isIncreasingSet_iff_isDecreasingSet_compl`) supplies the
final bound; `ε` and the conclusion are uniform over the field law. -/
theorem thinLSS_bridge {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  refine ⟨(1 - p) / 2, by linarith, ?_⟩
  intro μ hμ hKD hsite A hA hinc
  haveI := hμ
  exact thinPlanar_of_dense (p := p) (ε := (1 - p) / 2)
    (by linarith) (by linarith) hdense hKD hsite hA hinc

/-! ### The carrier-transported lattice form -/

/-- The one-site probability of a planar field is read at the corresponding lattice site, for
either value of the bit. -/
theorem fieldEquivPlanar_oneSite' (μ : Measure (PlanarCarrier → Bool))
    (s : LatticeProb.Site 2) (b : Bool) :
    (μ.map fieldEquivPlanar.toFun) {η | η s = b} = μ {ω | ω (ofSite2 s) = b} := by
  have hs : MeasurableSet {η : LatticeProb.Site 2 → Bool | η s = b} := by
    have h : {η : LatticeProb.Site 2 → Bool | η s = b} =
        (fun f : LatticeProb.Site 2 → Bool => f s) ⁻¹' ({b} : Set Bool) := by
      ext η; simp
    rw [h]
    exact (measurable_pi_apply s) (measurableSet_singleton b)
  rw [Measure.map_apply measurable_toSite2Field hs]
  rfl

/-- **The complete conditional thin-LSS bridge on the lattice carrier.**  The same hypotheses as
`thinLSS_bridge`, but the conclusion is read after transporting the planar field to the
two-dimensional lattice carrier through the coordinate identification.  The dependence
condition travels by `kDependentPlanar_map_fieldEquivPlanar`, the one-site bound by the planar
one-site transport, and the event bound is the lattice form of the complement bridge. -/
theorem thinLSS_bridge_site2 {p : ℝ} (hp : p < 1)
    (hdense : ∀ ν : Measure (LatticeProb.Site 2 → Bool), IsProbabilityMeasure ν →
      KDependent 2 ν →
      (∀ s : LatticeProb.Site 2, ENNReal.ofReal p ≤ ν {ω | ω s = true}) →
      DenseLower (bitProduct (7 / 8) seven_eighths_le_one (LatticeProb.Site 2)) ν) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (LatticeProb.Site 2 → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          (μ.map fieldEquivPlanar.toFun) A
            ≤ bitProduct (1 / 8) one_eighth_le_one (LatticeProb.Site 2) A := by
  refine ⟨(1 - p) / 2, by linarith, ?_⟩
  intro μ hμ hKD hsite A hA hinc
  haveI := hμ
  haveI : IsProbabilityMeasure (μ.map fieldEquivPlanar.toFun) :=
    Measure.isProbabilityMeasure_map measurable_toSite2Field.aemeasurable
  have hKD2 : KDependent 2 (μ.map fieldEquivPlanar.toFun) :=
    kDependentPlanar_map_fieldEquivPlanar 2 hKD
  have hsite2 : ∀ s : LatticeProb.Site 2,
      ENNReal.ofReal p ≤ (μ.map fieldEquivPlanar.toFun) {η | η s = false} := by
    intro s
    rw [fieldEquivPlanar_oneSite' μ s false]
    have h := oneSite_compl_lower_bound (μ := μ) (ε := (1 - p) / 2)
      (by linarith) hsite (ofSite2 s)
    have hp_eq : 1 - 2 * ((1 - p) / 2) = p := by ring
    rwa [hp_eq, oneSite_prob_pushforward] at h
  exact thinUpper_of_transported_dense (d := 2) p hdense hKD2 hsite2 A hA hinc

end LatticeProb.Percolation

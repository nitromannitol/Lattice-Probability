/-
# Non-vacuity of the dense hypothesis: a concrete witness

The discharge of the frozen thin statement is conditional on the dense domination hypothesis
`DenseSevenEighths p`.  This module shows that hypothesis is not vacuous: it exhibits a concrete
`p < 1` and a probability measure on the planar carrier that is `KDependentPlanar 2`, has
one-site probability at least `p`, and satisfies the domination conclusion.  The witness is the
product Bernoulli field of density `7/8`, which for `p = 7/8` is `2`-dependent, has one-site
probability `7/8`, and dominates itself on increasing events.

The dependence and one-site facts are the genuinely new content.  No domination statement is
proved, no `Prop` is frozen, no rotor file is touched, and nothing is claimed unconditionally.
-/

import LatticeProb.Prob.Percolation.LSSThinDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-! ### The product field is finitely dependent -/

/-- **The product Bernoulli field is finite-range dependent.**  Distinct coordinates of a
product measure are independent, so two finite index sets separated by more than `k` in one
coordinate (hence disjoint) have independent restrictions. -/
theorem kDependentPlanar_bernoulliFieldPlanar (k : ℕ) (p : NNReal) (hp : p ≤ 1) :
    KDependentPlanar k (bernoulliFieldPlanar p hp) := by
  intro I J hfar
  have hdisj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have h := hfar i hi i hj
    have h0 : max |i.1 - i.1| |i.2 - i.2| = 0 := by simp
    rw [h0] at h
    omega
  exact (iIndepFun_infinitePi (X := fun _ (a : Bool) => a) (fun _ => measurable_id)).indepFun_finset
    I J hdisj (fun i => measurable_pi_apply i)

/-! ### The one-site probability of the product field -/

set_option linter.deprecated false in
/-- The one-site probability of the product Bernoulli field of density `p` is `p`. -/
theorem bernoulliFieldPlanar_oneSite (p : NNReal) (hp : p ≤ 1) (s : PlanarCarrier) :
    bernoulliFieldPlanar p hp {ω | ω s = true} = ENNReal.ofReal p := by
  have hpre : (fun f : PlanarCarrier → Bool => f s) ⁻¹' ({true} : Set Bool) =
      {ω : PlanarCarrier → Bool | ω s = true} := by
    ext ω; simp
  have hEq : bernoulliFieldPlanar p hp {ω | ω s = true} = (bernoulli p hp) {true} := by
    rw [← hpre]
    rw [← Measure.map_apply (measurable_pi_apply s) (measurableSet_singleton true)]
    simp only [bernoulliFieldPlanar, bitProduct]
    rw [Measure.infinitePi_map_eval]
  have htrue : (bernoulli p hp) {true} = ENNReal.ofReal p := by
    unfold bernoulli
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true), PMF.bernoulli_apply]
    exact (ENNReal.ofReal_coe_nnreal).symm
  rw [hEq, htrue]

/-! ### The witness -/

/-- **The dense hypothesis has a concrete legitimate witness.**  With `p = 7/8`, the product
Bernoulli field of density `7/8` is a probability measure on `ℤ × ℤ → Bool`, is
`2`-dependent, has every one-site probability equal to `7/8 ≥ p`, and satisfies the domination
conclusion (it dominates itself).  Hence the hypothesis set of `DenseSevenEighths (7/8)` is
non-empty and the conditional discharge is not vacuous. -/
theorem denseHypothesis_witness :
    ∃ p : ℝ, p < 1 ∧ ∃ ν : Measure (PlanarCarrier → Bool),
      IsProbabilityMeasure ν ∧ KDependentPlanar 2 ν ∧
        (∀ s : PlanarCarrier, ENNReal.ofReal p ≤ ν {ω | ω s = true}) ∧
        DenseLower (bernoulliFieldPlanar (7 / 8) seven_eighths_le_one) ν := by
  refine ⟨7 / 8, by norm_num, bernoulliFieldPlanar (7 / 8) seven_eighths_le_one,
    inferInstance, kDependentPlanar_bernoulliFieldPlanar 2 (7 / 8) seven_eighths_le_one, ?_, ?_⟩
  · intro s
    rw [bernoulliFieldPlanar_oneSite]
    norm_num
  · intro C _ _
    exact le_rfl

end LatticeProb.Percolation

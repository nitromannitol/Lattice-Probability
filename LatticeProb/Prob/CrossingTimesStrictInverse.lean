/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesClock15
import LatticeProb.Analysis.NNRatRightInf

/-!
# The inverse crossing clock of a time-changed Brownian path is strictly increasing and unbounded

For a path `X = B ∘ τ` obtained from a path `B` whose crossing clock is the identity by a time change `τ`
(continuous, strictly increasing, from `0` and unbounded), the crossing clock of `X` is `τ`, so its inverse
`A = τ⁻¹` is strictly increasing and unbounded.  The two properties are recorded along the nonnegative
rationals, where they define a measurable set of paths and transfer to the law of `X`.

* `InvClockStrict m x`: the inverse crossing clock `t ↦ A_t(x)` is strictly increasing and unbounded along
  the nonnegative rationals;
* `measurableSet_invClockStrict`: the paths with this property form a measurable set;
* `invClockStrict_of_crossClock_eq`: the deterministic statement for a path with crossing clock `τ`;
* `ae_map_invClockStrict`: the transfer to the law of the time-changed process `X = B ∘ τ`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Strict

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- **Strict and unbounded inverse crossing clock.**  The inverse crossing clock `t ↦ A_t(x)` of the path `x`
is strictly increasing and unbounded along the nonnegative rationals. -/
def InvClockStrict (m : ℝ≥0∞) (x : C(ℝ≥0, E)) : Prop :=
  (∀ p q : ℚ≥0, p < q → pathClockInv m x p < pathClockInv m x q) ∧
    ∀ n : ℕ, ∃ q : ℚ≥0, (n : ℝ≥0∞) ≤ pathClockInv m x q

/-- The paths with strictly increasing, unbounded inverse crossing clock along the rationals form a
measurable set. -/
theorem measurableSet_invClockStrict (m : ℝ≥0∞) :
    MeasurableSet {x : C(ℝ≥0, E) | InvClockStrict m x} := by
  have hm : ∀ t : ℝ≥0, Measurable fun x : C(ℝ≥0, E) => pathClockInv m x t :=
    fun t => measurable_pathClockInv m t
  have h1 : MeasurableSet {x : C(ℝ≥0, E) |
      ∀ p q : ℚ≥0, p < q → pathClockInv m x p < pathClockInv m x q} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hm p) (hm q)
  have h2 : MeasurableSet {x : C(ℝ≥0, E) |
      ∀ n : ℕ, ∃ q : ℚ≥0, (n : ℝ≥0∞) ≤ pathClockInv m x q} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q =>
      measurableSet_le measurable_const (hm q)
  exact h1.inter h2

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- **A path with crossing clock `τ` has a strictly increasing, unbounded inverse crossing clock.** -/
theorem invClockStrict_of_crossClock_eq {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) (hτu : Tendsto τ atTop atTop) {m : ℝ≥0∞} {x : C(ℝ≥0, E)}
    (hx : crossClock m (fun u => x u) = fun u => (τ u : ℝ≥0∞)) : InvClockStrict m x := by
  have hA : ∀ t : ℝ≥0, pathClockInv m x t = clockInv (fun u => (τ u : ℝ≥0∞)) t := by
    intro t
    unfold pathClockInv
    rw [hx]
  refine ⟨fun p q hpq => ?_, fun n => ?_⟩
  · obtain ⟨σp, hσp⟩ := exists_eq_of_unbounded hτc hτ0 hτu (p : ℝ≥0)
    obtain ⟨σq, hσq⟩ := exists_eq_of_unbounded hτc hτ0 hτu (q : ℝ≥0)
    rw [hA, hA, clockInv_coe_eq hτm hσp, clockInv_coe_eq hτm hσq]
    have hpq' : ((p : ℝ≥0)) < (q : ℝ≥0) := by exact_mod_cast hpq
    have : σp < σq := hτm.lt_iff_lt.1 (by rw [hσp, hσq]; exact hpq')
    exact_mod_cast this
  · obtain ⟨q, hq1, -⟩ := exists_nnrat_between_nnreal (show τ n < τ n + 1 by simp)
    refine ⟨q, ?_⟩
    obtain ⟨σ, hσ⟩ := exists_eq_of_unbounded hτc hτ0 hτu (q : ℝ≥0)
    rw [hA, clockInv_coe_eq hτm hσ]
    have : (n : ℝ≥0) < σ := hτm.lt_iff_lt.1 (by rw [hσ]; exact hq1)
    exact_mod_cast this.le

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Transfer of the strict, unbounded inverse crossing clock** to the law of the time-changed process
`X = B ∘ τ`. -/
theorem ae_map_invClockStrict {Q : Measure Ω} {X : Ω → C(ℝ≥0, E)} {B : Ω → ℝ≥0 → E}
    {τ : Ω → ℝ≥0 → ℝ≥0} {m : ℝ≥0∞} (hX : AEMeasurable X Q)
    (hτ : ∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧
      Tendsto (τ ω) atTop atTop ∧ ∀ u, X ω u = B ω (τ ω u))
    (hB : ∀ᵐ ω ∂Q, ∀ u, crossClock m (B ω) u = u) :
    ∀ᵐ x ∂(Q.map X), InvClockStrict m x := by
  rw [ae_map_iff hX (measurableSet_invClockStrict m)]
  filter_upwards [hτ, hB] with ω ⟨hc, hm, h0, hu, hx⟩ hBω
  have hxf : (fun u => X ω u) = B ω ∘ τ ω := funext hx
  refine invClockStrict_of_crossClock_eq hc hm h0 hu ?_
  rw [hxf]
  exact crossClock_comp_of_clock_id hc hm h0 hBω

end Transfer

end Strict

end LatticeProb

end

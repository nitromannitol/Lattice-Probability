import LatticeProb.Prob.Cadlag.HalfLine.Defs
import LatticeProb.Prob.Cadlag.HalfLine.Paths
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measurability of stopped discrepancies

Right continuity reduces the time supremum to nonnegative rational times.
Countability of path discontinuities then gives measurability in the stopping time.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

variable {E : Type*} [MetricSpace E]

/-- Rational times truncated at zero form a dense subset of the half-line. -/
theorem denseRange_rat_toNNReal : DenseRange (fun r : ℚ => (r : ℝ).toNNReal) := by
  have hs : Function.Surjective Real.toNNReal := fun t => ⟨t, Real.toNNReal_coe⟩
  exact hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal

/-- Right continuity computes the stopped discrepancy on rational times alone. -/
theorem discrepancy_eq_iSup_rat (x y : D E) (l : LambdaPrime) (u : Time) :
    discrepancy x y l u =
      ⨆ r : ℚ, q (x.1 (min (r : ℝ).toNNReal u))
        (y.1 (min (l (r : ℝ).toNNReal) u)) := by
  let S := range (fun r : ℚ => (r : ℝ).toNNReal)
  have hS : Dense S := denseRange_rat_toNNReal
  apply le_antisymm
  · apply iSup_le
    intro t
    have hn : NeBot (𝓝[S ∩ Ioi t] t) := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [mem_closure_iff]
      intro U hU htU
      have hne : (U ∩ Ioi t).Nonempty := by
        exact Filter.nonempty_of_mem
          (inter_mem (mem_inf_of_left (hU.mem_nhds htU)) self_mem_nhdsWithin :
            U ∩ Ioi t ∈ 𝓝[>] t)
      obtain ⟨s, hs⟩ := hS.inter_open_nonempty (U ∩ Ioi t) (hU.inter isOpen_Ioi) hne
      exact ⟨s, hs.1.1, hs.2, hs.1.2⟩
    letI := hn
    have hsub : S ∩ Ioi t ⊆ Ici t := fun s hs =>
      (show t < s from hs.2).le
    have hx := ((x.2.stop u).1 t).mono hsub
    have hy := (((y.2.stop u).comp_lambdaPrime l).1 t).mono hsub
    apply le_of_tendsto ((hx.edist hy).min continuousWithinAt_const)
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨r, rfl⟩ := hs.1
    exact le_iSup (fun r : ℚ => q (x.1 (min (r : ℝ).toNNReal u))
      (y.1 (min (l (r : ℝ).toNNReal) u))) r
  · apply iSup_le
    intro r
    unfold discrepancy
    exact le_iSup (fun t : Time => q (x.1 (min t u))
      (y.1 (min (l t) u))) (r : ℝ).toNNReal

/-- A càdlàg half-line path is Borel measurable, even in a nonseparable state space. -/
theorem measurable_isCadlag [MeasurableSpace E] [BorelSpace E]
    {x : Time → E} (hx : IsCadlag x) : Measurable x :=
  measurable_of_countable_not_continuousAt hx.countable_discontinuities

/-- The stopped discrepancy is measurable as a function of the stopping time. -/
theorem measurable_discrepancy (x y : D E) (l : LambdaPrime) :
    Measurable (discrepancy x y l) := by
  change Measurable (fun u => discrepancy x y l u)
  simp_rw [discrepancy_eq_iSup_rat]
  apply Measurable.iSup
  intro r
  have hx := x.2.stop (r : ℝ).toNNReal
  have hy := y.2.stop (l (r : ℝ).toNNReal)
  apply measurable_of_countable_not_continuousAt
  apply (hx.countable_discontinuities.union hy.countable_discontinuities).mono
  intro u hu
  by_contra hnot
  have ha : ContinuousAt (fun u => x.1 (min u (r : ℝ).toNNReal)) u := by
    simpa only [mem_union, mem_setOf_eq, not_or, not_not] using (not_or.mp hnot).1
  have hb : ContinuousAt (fun u => y.1 (min u (l (r : ℝ).toNNReal))) u := by
    simpa only [mem_union, mem_setOf_eq, not_or, not_not] using (not_or.mp hnot).2
  apply hu
  simpa only [ContinuousAt, q, min_comm] using (ha.edist hb).min continuousAt_const

/-- Real stopping times are truncated at zero by a continuous measurable map. -/
theorem measurable_discrepancy_toNNReal (x y : D E) (l : LambdaPrime) :
    Measurable (fun u : ℝ => discrepancy x y l u.toNNReal) :=
  (measurable_discrepancy x y l).comp continuous_real_toNNReal.measurable

/-- The actual exponentially weighted integrand in the EK distance is measurable. -/
theorem measurable_integratedDiscrepancy_integrand (x y : D E) (l : LambdaPrime) :
    Measurable (fun u : ℝ =>
      ENNReal.ofReal (Real.exp (-u)) * discrepancy x y l u.toNNReal) := by
  exact (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal.mul
    (measurable_discrepancy_toNNReal x y l)

/-- The Lebesgue integral of two discrepancy integrands splits as their sum. -/
theorem integratedDiscrepancy_lintegral_add (x y z w : D E) (l m : LambdaPrime) :
    (∫⁻ u : ℝ in Ioi 0,
      (ENNReal.ofReal (Real.exp (-u)) * discrepancy x y l u.toNNReal) +
      (ENNReal.ofReal (Real.exp (-u)) * discrepancy z w m u.toNNReal)) =
      integratedDiscrepancy x y l + integratedDiscrepancy z w m := by
  exact lintegral_add_left (measurable_integratedDiscrepancy_integrand x y l) _

end LatticeProb.Cadlag.HalfLine

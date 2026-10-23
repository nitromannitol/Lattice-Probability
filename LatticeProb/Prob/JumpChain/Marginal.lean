import LatticeProb.Prob.JumpChain.Position
import LatticeProb.Prob.JumpChain.Uniformization

/-!
# Clock-zero events for the constructed position process

The initial state and first clock retain their exact product law on the full-measure
space of regular histories. This identifies the zero-ring contribution to the one-time
position law at every nonnegative time.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section

variable {S : Type*}

namespace RegularHistory

/-- The event of no clock rings is the event that the first holding interval exceeds time. -/
theorem ringCount_eq_zero_iff (h : RegularHistory S) (t : ℝ≥0) :
    h.ringCount t = 0 ↔ (t : ℝ) < (h.val 0).2 := by
  rw [h.ringCount_eq_iff]
  simp only [jumpTime_zero, jumpTime_succ, zero_add]
  exact and_iff_right t.property

end RegularHistory

namespace BoundedRates

/-- The survival probability of a holding interval is the exact exponential tail. -/
theorem clockLaw_Ioi (rates : BoundedRates S) (t : ℝ≥0) :
    rates.clockLaw (Ioi (t : ℝ)) = ENNReal.ofReal (Real.exp (-(rates.R * t))) := by
  letI := isProbabilityMeasure_expMeasure rates.R_pos
  have hnonneg : 0 ≤ 1 - Real.exp (-(rates.R * t)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg rates.R_pos.le t.property)
  have ht : 0 ≤ (t : ℝ) := t.property
  rw [rates.clockLaw_eq_expMeasure, ← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    ← ofReal_cdf, cdf_expMeasure_eq rates.R_pos]
  simp only [if_pos ht]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hnonneg, sub_sub_cancel]

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The initial pair on regular histories has exactly its original product law. -/
theorem regularLaw_map_zero (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    (rates.regularLaw μ).map (fun h ↦ h.val 0) = μ.prod rates.clockLaw := by
  change (rates.regularLaw μ).map ((fun h : History S ↦ h 0) ∘ Subtype.val) = _
  rw [← Measure.map_map (by fun_prop) measurable_subtype_coe,
    rates.regularLaw_map_val, rates.historyLaw_map_zero]

/-- The zero-ring position event has the initial-state mass times the first-clock tail. -/
theorem regularLaw_zero_ring_position (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (j : S) :
    rates.regularLaw μ {h | h.ringCount t = 0 ∧ h.position t = j} =
      μ {j} * rates.clockLaw (Ioi (t : ℝ)) := by
  have hevent : {h : RegularHistory S | h.ringCount t = 0 ∧ h.position t = j} =
      (fun h : RegularHistory S ↦ h.val 0) ⁻¹' ({j} ×ˢ Ioi (t : ℝ)) := by
    ext h
    simp only [mem_setOf_eq, mem_preimage, mem_prod, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨hn, hp⟩
      exact ⟨by simpa only [RegularHistory.position, hn] using hp,
        (h.ringCount_eq_zero_iff t).mp hn⟩
    · rintro ⟨hp, ht⟩
      have hn := (h.ringCount_eq_zero_iff t).mpr ht
      exact ⟨hn, by simpa only [RegularHistory.position, hn] using hp⟩
  have hm : Measurable (fun h : RegularHistory S ↦ h.val 0) :=
    (measurable_pi_apply (X := fun _ : ℕ ↦ S × ℝ) 0).comp measurable_subtype_coe
  rw [hevent, ← Measure.map_apply hm
    ((measurableSet_singleton j).prod measurableSet_Ioi), rates.regularLaw_map_zero,
    Measure.prod_prod]

/-- Partition the position event by the exact clock-ring count. -/
theorem regularLaw_position_eq_tsum (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (j : S) :
    rates.regularLaw μ {h | h.position t = j} =
      ∑' n : ℕ, rates.regularLaw μ {h | h.ringCount t = n ∧ h.position t = j} := by
  have hm (n : ℕ) : MeasurableSet
      {h : RegularHistory S | h.ringCount t = n ∧ h.position t = j} :=
    ((RegularHistory.measurable_ringCount t) (measurableSet_singleton n)).inter
      ((RegularHistory.measurable_position t) (measurableSet_singleton j))
  have hd : Pairwise (fun n m : ℕ ↦ Disjoint
      {h : RegularHistory S | h.ringCount t = n ∧ h.position t = j}
      {h : RegularHistory S | h.ringCount t = m ∧ h.position t = j}) := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro h hn hm
    exact hnm (hn.1.symm.trans hm.1)
  rw [← measure_iUnion hd hm]
  congr 1
  ext h
  simp only [mem_iUnion, mem_setOf_eq]
  exact ⟨fun hp ↦ ⟨h.ringCount t, rfl, hp⟩, fun ⟨_, _, hp⟩ ↦ hp⟩

/-- The zero-ring contribution has exactly the zeroth Poisson weight. -/
theorem regularLaw_zero_ring_position_eq_exp (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (j : S) :
    rates.regularLaw μ {h | h.ringCount t = 0 ∧ h.position t = j} =
      μ {j} * ENNReal.ofReal (Real.exp (-(rates.R * t))) := by
  rw [rates.regularLaw_zero_ring_position, rates.clockLaw_Ioi]

end BoundedRates

end

end LatticeProb.JumpChain

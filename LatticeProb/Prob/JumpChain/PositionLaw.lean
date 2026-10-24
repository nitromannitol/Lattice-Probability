import LatticeProb.Prob.JumpChain.RingCount
import LatticeProb.Prob.JumpChain.StateChain
import LatticeProb.Prob.JumpChain.Marginal
import LatticeProb.Prob.JumpChain.Semigroup
import LatticeProb.Prob.JumpChain.Embedded

/-!
# The one-time law of the constructed chain

Independence of the embedded states and clocks factors each ring-count contribution.
Summing these contributions identifies the position law with the uniformized kernel.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

namespace BoundedRates

/-- A fixed ring-count contribution factors into its embedded-state mass and Poisson weight. -/
theorem regularLaw_ringCount_position (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (n : ℕ) (j : S) :
    rates.regularLaw μ {h | h.ringCount t = n ∧ h.position t = j} =
      ((rates.kernel ^ n) ∘ₘ μ) {j} *
        ENNReal.ofReal (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) := by
  let window : Set (ℕ → ℝ) :=
    {c | (∑ k ∈ Finset.range n, c k) ≤ t ∧
      (t : ℝ) < ∑ k ∈ Finset.range (n + 1), c k}
  have hw : MeasurableSet window := by
    have hm (m : ℕ) : Measurable (fun c : ℕ → ℝ ↦ ∑ k ∈ Finset.range m, c k) := by
      fun_prop
    exact (measurableSet_le (hm n) measurable_const).inter
      (measurableSet_lt measurable_const (hm (n + 1)))
  let event : Set (History S) :=
    {h | (h n).1 = j ∧ jumpTime h n ≤ t ∧ (t : ℝ) < jumpTime h (n + 1)}
  have he : MeasurableSet event :=
    ((measurable_pi_apply n).fst (measurableSet_singleton j)).inter
      ((measurableSet_le (measurable_jumpTime n) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_jumpTime (n + 1))))
  have hpre : {h : RegularHistory S | h.ringCount t = n ∧ h.position t = j} =
      Subtype.val ⁻¹' event := by
    ext h
    change (_ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor
    · rintro ⟨hn, hp⟩
      exact ⟨by simpa only [RegularHistory.position, hn] using hp,
        (h.ringCount_eq_iff t n).mp hn⟩
    · rintro ⟨hp, ht⟩
      have hn := (h.ringCount_eq_iff t n).mpr ht
      exact ⟨hn, by simpa only [RegularHistory.position, hn] using hp⟩
  rw [hpre, ← Measure.map_apply measurable_subtype_coe he, rates.regularLaw_map_val]
  have hi := ((rates.indepFun_states_clocks μ).comp
    (measurable_pi_apply n) measurable_id).measure_inter_preimage_eq_mul
      {j} window (measurableSet_singleton j) hw
  change rates.historyLaw μ event = _ at hi
  rw [hi]
  have hs := congrArg (fun ν : Measure S ↦ ν {j}) (rates.historyLaw_map_state μ n)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton j)] at hs
  change rates.historyLaw μ ((fun h ↦ (h n).1) ⁻¹' {j}) *
    rates.historyLaw μ {h | jumpTime h n ≤ t ∧ (t : ℝ) < jumpTime h (n + 1)} = _
  rw [hs]
  exact congrArg (((rates.kernel ^ n) ∘ₘ μ) {j} * ·)
    (rates.historyLaw_jumpTime_window μ t n)

/-- The constructed position at time `t` has the uniformized transition law. -/
theorem regularLaw_position (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (t : ℝ≥0) (j : S) :
    rates.regularLaw μ {h | h.position t = j} = (rates.transitionKernel t ∘ₘ μ) {j} := by
  rw [rates.regularLaw_position_eq_tsum, rates.transitionKernel_comp_singleton]
  simp_rw [rates.regularLaw_ringCount_position, Measure.bind_apply
    (measurableSet_singleton j) (Kernel.aemeasurable _), lintegral_countable']
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro i
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  ac_rfl

/-- From a fixed initial state, the constructed position has the corresponding kernel row. -/
theorem regularLaw_dirac_position (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    rates.regularLaw (Measure.dirac i) {h | h.position t = j} =
      rates.transitionKernel t i {j} := by
  rw [rates.regularLaw_position]
  exact congrArg (fun ν : Measure S ↦ ν {j})
    (Measure.dirac_bind (rates.transitionKernel t).measurable i)

end BoundedRates

end

end LatticeProb.JumpChain

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.UCPBracketLocalization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.MeasurableBracketError
import LatticeProb.Bonanno.ReflectedGMS.Limit.ContinuousBracketLocalization

/-!
# Localization of a bracket from ucp convergence

This file assembles the measurable compact-time bracket error, the continuous
threshold stopping time, and the localized integrable envelope.  In
particular, the stopped-bracket bound also covers paths whose threshold is
already exceeded at time zero: the project's indicator-stopped process then
vanishes identically on that path.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Actual threshold localization of a continuous increasing nonnegative
bracket whose compact-time error converges to zero in probability.  The
constructed stopping times are the literal first hitting times of `Ici K`;
their exits before `T` are rare, their actual indicator-stopped brackets are
bounded by `K`, and their stopped bracket errors admit integrable all-time
envelopes with means tending to zero. -/
theorem exists_threshold_bracket_localization_of_ucp
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℕ → Filtration ℝ≥0 m} {B : ℕ → ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) {v K : ℝ} (hv : 0 ≤ v) (hKT : v * (T : ℝ) < K)
    (hB : ∀ n, Adapted (F n) (B n))
    (hnull : ∀ n (t : ℝ≥0) (A : Set Ω),
      P A = 0 → MeasurableSet[(F n) t] A)
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => B n t ω))
    (hm : ∀ n, ∀ᵐ ω ∂P, Monotone (fun t => B n t ω))
    (h0 : ∀ n, ∀ᵐ ω ∂P, ∀ t, 0 ≤ B n t ω)
    (hucp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T,
        ε < |B n t ω - v * (t : ℝ)|}) atTop (𝓝 0)) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, τ n = hittingAfter (B n) (Ici K) 0) ∧
      (∀ n, IsStoppingTime (F n) (τ n)) ∧
      Tendsto (fun n => P {ω | τ n ω ≤ T}) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T,
        |stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (B n s))
          (τ n) t ω| ≤ K) ∧
      ∃ R : ℕ → Ω → ℝ,
        (∀ n, Integrable (R n) P) ∧
        (∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T,
          |stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (B n s))
              (τ n) t ω - v * (t : ℝ)| ≤ R n ω) ∧
        Tendsto (fun n => ∫ ω, R n ω ∂P) atTop (𝓝 0) := by
  have hK : 0 ≤ K :=
    (mul_nonneg hv T.2).trans hKT.le
  have hBmeas : ∀ n t, Measurable (B n t) := by
    intro n t
    exact (hB n t).mono ((F n).le t) le_rfl
  obtain ⟨E, hEmeas, hE0, herror, hElim⟩ :=
    exists_measurable_uniform_bracket_error T v hBmeas hc hm h0 hucp
  have hterminal : TendstoInMeasure P (fun n ω => B n T ω) atTop
      (fun _ => v * (T : ℝ)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hu := hucp (ε / 2) (half_pos hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => zero_le) ?_
    intro n
    apply measure_mono
    intro ω hω
    refine ⟨T, ⟨zero_le, le_rfl⟩, ?_⟩
    have hhalf : ε / 2 < dist (B n T ω) (v * (T : ℝ)) :=
      (half_lt_self hε).trans_le hω
    simpa only [Real.dist_eq] using hhalf
  let τ : ℕ → Ω → WithTop ℝ≥0 :=
    fun n => hittingAfter (B n) (Ici K) 0
  have hτ (n : ℕ) : IsStoppingTime (F n) (τ n) := by
    exact isStoppingTime_continuous_diagonal_bracket_hitting
      (hB n) (hnull n) (hc n) (hm n) K
  have hexit : Tendsto (fun n => P {ω | τ n ω ≤ T}) atTop (𝓝 0) := by
    exact continuous_diagonal_bracket_threshold_exit_tendsto_zero
      T hKT hc hm hterminal
  have hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T,
      |stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (B n s))
        (τ n) t ω| ≤ K := by
    intro n
    filter_upwards [hc n, h0 n] with ω hωc hω0
    intro t ht
    by_cases hz : B n 0 ω ≤ K
    · exact indicator_stopped_continuous_bracket_abs_le
        hωc hz hω0 hK (τ n) le_rfl t
    · have hhit0 : τ n ω ≤ (0 : ℝ≥0) := by
        exact hittingAfter_le_of_mem bot_le (le_of_not_ge hz)
      have hτzero : τ n ω = ⊥ := by
        exact le_bot_iff.mp (by simpa using hhit0)
      simp [stoppedProcess, hτzero, hK]
  have hexitmeas (n : ℕ) : MeasurableSet {ω | τ n ω ≤ T} :=
    (F n).le T _ (hτ n T)
  obtain ⟨R, hRint, hRerror, hRlim⟩ :=
    exists_integrable_localized_bracket_error T hv hK hEmeas hE0 hElim
      herror hbound hexitmeas hexit
  exact ⟨τ, fun n => rfl, hτ, hexit, hbound, R, hRint, hRerror, hRlim⟩

end ReflectedGMS.MartingaleLimit

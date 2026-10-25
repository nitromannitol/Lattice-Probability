import LatticeProb.External.EthierKurtzSkorokhod

/-!
# Stopping-time compactness criterion of Ethier–Kurtz

Literal draft of Chapter 3, Theorem 8.6(c) implies (a), and Remark 8.7(b).
These are propositions for a cited input, not proofs of that input.
-/

namespace LatticeProb.External

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open LatticeProb.Cadlag.HalfLine

noncomputable section

/-- Discrete stopping times for the raw natural filtration, bounded everywhere by `T`.
The countable-range condition is the book's definition of discrete, not finite range. -/
def discreteNaturalStopping {E Ω : Type*} [MetricSpace E] [MeasurableSpace E]
    (Y : Ω → D E) (T : ℝ) (tau : Ω → Time) : Prop :=
  (Set.range tau).Countable ∧ (∀ w, (tau w : ℝ) ≤ T) ∧
    ∀ t : Time, @MeasurableSet Ω (naturalSigma Y t) {w | tau w ≤ t}

/-- Zero is a genuine discrete natural stopping time at every nonnegative horizon. -/
theorem discreteNaturalStopping_zero {E Ω : Type*} [MetricSpace E] [MeasurableSpace E]
    (Y : Ω → D E) {T : ℝ} (hT : 0 ≤ T) :
    discreteNaturalStopping Y T (fun _ => 0) := by
  refine ⟨?_, (fun _ => hT), ?_⟩
  · exact (Set.countable_singleton 0).mono (by intro t ht; rcases ht with ⟨w, rfl⟩; rfl)
  · intro t
    simp only [zero_le, setOf_true, MeasurableSet.univ]

/-- The exact quantity (8.31), with the past supremum inside the expectation.
`Time` is nonnegative; subtraction is truncated, and the bound on `v` prevents truncation. -/
def stoppingOscillation {E Ω : Type*} [MetricSpace E] [MeasurableSpace E]
    [m : MeasurableSpace Ω] (P : ProbabilityMeasure Ω) (Y : Ω → D E)
    (beta T delta : ℝ) : ℝ≥0∞ :=
  ⨆ tau : Ω → Time, ⨆ (_ : discreteNaturalStopping Y T tau),
    ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ delta),
      ∫⁻ w, ⨆ v : Time, ⨆ (_ : (v : ℝ) ≤ min delta (tau w)),
        incrementPower Y beta (tau w + u) (tau w) w *
          incrementPower Y beta (tau w) (tau w - v) w ∂P

/-- The implication (c) implies (a) with a specified outer aggregation of process indices.
Only `iSup` and sequential `limsup` are used in the cited proposition below. -/
def stoppingCompactnessImplication (A : Type)
    (aggregate : (A → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  ∀ (E : Type) [MetricSpace E] [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E]
    [BorelSpace E] (Ω : A → Type) (m : ∀ a, MeasurableSpace (Ω a))
    (P : ∀ a, @ProbabilityMeasure (Ω a) (m a)) (Y : ∀ a, Ω a → D E)
    (hY : ∀ a, @Measurable (Ω a) (D E) (m a) inferInstance (Y a)),
    (∀ a t, @Measurable (Ω a) E (m a) inferInstance (fun w => (Y a w).1 t)) →
    (∀ eta : ℝ, 0 < eta → ∀ t : ℚ, 0 ≤ t → ∃ K : Set E, IsCompact K ∧
      ∀ a, ENNReal.ofReal (1 - eta) ≤
        (P a : @Measure (Ω a) (m a)) {w | (Y a w).1 (t : ℝ).toNNReal ∈ K}) →
    (∀ T : ℝ, 0 < T → ∃ beta : ℝ, 0 < beta ∧
      Tendsto (fun delta : ℝ => aggregate (fun a =>
        @stoppingOscillation E (Ω a) _ _ (m a) (P a) (Y a) beta T delta))
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun delta : ℝ => aggregate (fun a =>
        ∫⁻ w, incrementPower (Y a) beta delta.toNNReal 0 w
          ∂(P a : @Measure (Ω a) (m a)))) (𝓝[>] 0) (𝓝 0)) →
    IsCompact (closure (Set.range (fun a =>
      (P a).map (@Measurable.aemeasurable (Ω a) (D E) (m a) inferInstance
        (Y a) (P a) (hY a)))))

/-- Ethier–Kurtz, Chapter 3, Theorem 8.6(c) implies (a), together with Remark 8.7(b).
The first conjunct is the family statement; the second replaces both outer suprema
by sequential limsups. Rational-time marginal compactness is retained in both. -/
def EthierKurtzRelativeCompactnessStopping : Prop :=
  (∀ A : Type, stoppingCompactnessImplication A (fun f => ⨆ a, f a)) ∧
    stoppingCompactnessImplication ℕ (fun f => Filter.limsup f atTop)

/-- Every stopped oscillation of a constant process vanishes at exponent one. -/
theorem stoppingOscillation_const (A : Type) [MeasurableSpace A]
    (P : ProbabilityMeasure A) (a T delta : ℝ) :
    stoppingOscillation P (fun _ => const a) 1 T delta = 0 := by
  simp only [stoppingOscillation, incrementPower, const, dist_self,
    min_eq_left zero_le_one, Real.rpow_one, ENNReal.ofReal_zero, zero_mul,
    ENNReal.iSup_zero, lintegral_zero]

/-- The implication has actual constant-process hypotheses for any aggregation preserving zero. -/
theorem stoppingCompactnessImplication_const {A : Type}
    (aggregate : (A → ℝ≥0∞) → ℝ≥0∞) (hz : aggregate (fun _ => 0) = 0)
    (h : stoppingCompactnessImplication A aggregate) (a : ℝ) :
    IsCompact (closure (Set.range (fun _ : A => constantProcessLaw a))) := by
  refine h ℝ (fun _ => Unit) (fun _ => inferInstance) (fun _ => unitLaw)
    (fun _ _ => const a) (fun _ => measurable_const) (fun _ _ => measurable_const) ?_ ?_
  · intro eta heta t ht
    refine ⟨{a}, isCompact_singleton, ?_⟩
    intro index
    simp only [const, mem_singleton_iff, setOf_true, measure_univ]
    exact (ENNReal.ofReal_le_ofReal (sub_le_self 1 heta.le)).trans_eq
      ENNReal.ofReal_one
  · intro T hT
    refine ⟨1, zero_lt_one, ?_, ?_⟩
    · simp only [stoppingOscillation_const, hz]
      exact tendsto_const_nhds
    · simp only [incrementPower, const, dist_self, min_eq_left zero_le_one,
        Real.rpow_one, ENNReal.ofReal_zero, lintegral_zero, hz]
      exact tendsto_const_nhds

/-- The family conjunct applies to a constant real process on a one-point probability space. -/
theorem ethierKurtzRelativeCompactnessStopping_const
    (h : EthierKurtzRelativeCompactnessStopping) (a : ℝ) :
    IsCompact (closure (Set.range (fun _ : Unit => constantProcessLaw a))) := by
  exact stoppingCompactnessImplication_const _ (by simp only [ENNReal.iSup_zero]) (h.1 Unit) a

/-- The sequence conjunct applies to the same genuine constant process. -/
theorem ethierKurtzRelativeCompactnessStopping_sequence_const
    (h : EthierKurtzRelativeCompactnessStopping) (a : ℝ) :
    IsCompact (closure (Set.range (fun _ : ℕ => constantProcessLaw a))) := by
  exact stoppingCompactnessImplication_const _ (by simp) h.2 a


end

end LatticeProb.External

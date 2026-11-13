/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TraceLaplaceConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ProcessOccupationLaplace
import LatticeProb.Bonanno.ReflectedWalk.ContinuousTimeChain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Laplace convergence of approximating trace transition probabilities

Fixed-time almost-sure eventual agreement already gives convergence of every one-time
transition probability in `ReflectedWalk.Theorem16.tendsto_measure_of_approximated`.
This file records the bounded-convergence consequence for the positive-discount Laplace
transform.  It also supplies the time-measurability input for the canonical continuous-time
chain read from an embedded path and its holding times.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal ReflectedWalk

universe u

namespace ReflectedGMS.TraceLaplaceConvergence

open ReflectedWalk ReflectedWalk.Theorem16

variable {V Ω : Type u} [MeasurableSpace Ω]

/-- For the canonical continuous-time chain, the event that the path is at `y` is jointly
measurable in real time and in the embedded path/holding-time pair. -/
theorem measurableSet_jumpPath_real_eq_some
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] (y : V) :
    MeasurableSet {q : ℝ × ((ℕ → V) × (ℕ → ℝ)) |
      ContinuousTimeChain.jumpPath q.2 (Real.toNNReal q.1) = some y} := by
  let τ : ℝ × ((ℕ → V) × (ℕ → ℝ)) → ℝ≥0∞ :=
    fun q => (Real.toNNReal q.1 : ℝ≥0∞)
  have hτ : Measurable τ := by fun_prop
  have hc : ∀ k : ℕ, Measurable fun q : ℝ × ((ℕ → V) × (ℕ → ℝ)) =>
      ContinuousTimeChain.jumpClock q.2.2 k := fun k =>
    (ContinuousTimeChain.measurable_jumpClock k).comp measurable_snd
  have hy : ∀ k : ℕ, Measurable fun q : ℝ × ((ℕ → V) × (ℕ → ℝ)) => q.2.1 k :=
    fun k => (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)
  rw [show {q : ℝ × ((ℕ → V) × (ℕ → ℝ)) |
      ContinuousTimeChain.jumpPath q.2 (Real.toNNReal q.1) = some y} =
      ⋃ k, (({q | ContinuousTimeChain.jumpClock q.2.2 k ≤ τ q} ∩
        {q | τ q < ContinuousTimeChain.jumpClock q.2.2 (k + 1)}) ∩
        {q | q.2.1 k = y}) by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      ContinuousTimeChain.jumpPath_eq_some_iff, ContinuousTimeChain.InJump, τ,
      and_assoc]]
  exact MeasurableSet.iUnion fun k =>
    ((measurableSet_le (hc k) hτ).inter (measurableSet_lt hτ (hc (k + 1)))).inter
      (hy k (measurableSet_singleton y))

/-- The canonical jump-path transition probability is measurable in real time. -/
theorem measurable_jumpPath_vertexProbability
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (P : Measure ((ℕ → V) × (ℕ → ℝ))) [SFinite P] (y : V) :
    Measurable fun t : ℝ =>
      P {p | ContinuousTimeChain.jumpPath p (Real.toNNReal t) = some y} := by
  simpa only [Set.preimage_ofPred_eq] using
    measurable_measure_prodMk_left (measurableSet_jumpPath_real_eq_some y)

/-- Positive-discount Laplace transforms of transition probabilities converge under the
fixed-time approximation furnished by Step 2. -/
theorem tendsto_integral_exp_neg_mul_measureReal_of_approximated
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → Option V} {Q : ℕ → ℝ≥0 → Ω → Option V}
    (hQm : ∀ n t, Measurable (Q n t)) (hXm : ∀ t, Measurable (X t))
    (happ : ApproximatedAtFixedTimes P X Q) (y : V)
    (hQt : ∀ n, Measurable fun t : ℝ =>
      (P {ω | Q n (Real.toNNReal t) ω = some y}).toReal)
    (_hXt : Measurable fun t : ℝ =>
      (P {ω | X (Real.toNNReal t) ω = some y}).toReal)
    {alpha : ℝ} (ha : 0 < alpha) :
    Tendsto (fun n => ∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      (P {ω | Q n (Real.toNNReal t) ω = some y}).toReal) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
        (P {ω | X (Real.toNNReal t) ω = some y}).toReal)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ => Real.exp (-alpha * t))
  · intro n
    exact (by fun_prop : Measurable fun t : ℝ => Real.exp (-alpha * t) *
      (P {ω | Q n (Real.toNNReal t) ω = some y}).toReal).aestronglyMeasurable
  · exact integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0
  · intro n
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
      ENNReal.toReal_nonneg)]
    apply mul_le_of_le_one_right (Real.exp_nonneg _)
    calc
      (P {ω | Q n (Real.toNNReal t) ω = some y}).toReal ≤ (P Set.univ).toReal :=
        ENNReal.toReal_mono (by simp) (measure_mono (subset_univ _))
      _ = 1 := by simp
  · filter_upwards [] with t
    apply tendsto_const_nhds.mul
    exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp
      (tendsto_measure_of_approximated hQm hXm happ (Real.toNNReal t) y)

end ReflectedGMS.TraceLaplaceConvergence

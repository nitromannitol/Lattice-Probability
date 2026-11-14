/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSkeletonExcursion at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonClock
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianObservedHistoryMeasurability
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionSampler

/-! Successive full excursions extracted from one actual continuous path.
The clock remains the original path's clock, and termination is permanent. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

set_option linter.unusedSectionVars false

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def brownianSkeletonExcursion (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) : ℕ → BrownianPath d → Bool × C(unitInterval, Euc d)
  | 0 => selectedBrownianExcursionSampler U (some j₀, z)
  | n + 1 => fun ω ↦
      selectedBrownianExcursionSampler U
        (brownianClockChoice z (selector (n + 1))
          (brownianSkeletonClock U z j₀ selector n) ω,
          z + ω (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal)
        (shiftedBrownianPath (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal ω)

theorem measurable_brownianSkeletonExcursion (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    {selector : ℕ → Euc d → Option J} (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    Measurable (brownianSkeletonExcursion U z j₀ selector n) := by
  cases n with
  | zero =>
    change Measurable (selectedBrownianExcursionSampler U (some j₀, z))
    exact measurable_selectedBrownianExcursionSampler U hU (some j₀, z)
  | succ n =>
    have hclock := measurable_brownianSkeletonClock U hU z j₀ hselector n
    have ht : Measurable (fun ω ↦ (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal) :=
      ENNReal.measurable_toNNReal.comp (measurable_snd.comp hclock)
    have heval : Measurable (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2) := by fun_prop
    have hp : Measurable (fun ω : BrownianPath d ↦
        z + ω (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal) := by
      simpa only [Pi.add_def, Function.comp_def, id_eq] using
        (measurable_const (a := z)).add (heval.comp (measurable_id.prodMk ht))
    exact (measurable_selectedBrownianExcursionSampler_joint U hU).comp
      (((measurable_brownianClockChoice z (hselector (n + 1)) hclock).prodMk hp).prodMk
        (measurable_variable_shiftedBrownianPath ht))

theorem brownianSkeletonExcursion_flag (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d) :
    (brownianSkeletonExcursion U z j₀ selector n ω).1 =
      (brownianSkeletonClock U z j₀ selector n ω).1 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases hc : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) ω <;>
      simp only [brownianSkeletonExcursion, brownianSkeletonClock, brownianClockUpdate,
        hc, selectedBrownianExcursionSampler, Option.isNone_none, Option.isNone_some]

theorem brownianSkeletonExcursion_endPoint (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) :
    (brownianSkeletonExcursion U z j₀ selector n ω).2 1 =
      z + ω (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal := by
  cases n with
  | zero =>
    exact stoppedBrownianRepresentative_endPoint (U j₀) z ω
  | succ n =>
    cases hc : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) ω with
    | none =>
      simp only [brownianSkeletonExcursion, hc, selectedBrownianExcursionSampler,
        ContinuousMap.const_apply, brownianSkeletonClock, brownianClockUpdate,
        brownianSelectedNextExitTime]
    | some j =>
      have hf : brownianNextExitTime (U j) z
          (fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2) ω ≠ ∞ := by
        simpa only [brownianSkeletonClock, brownianClockUpdate,
          brownianSelectedNextExitTime, hc] using hfinite
      simpa only [brownianSkeletonExcursion, hc, selectedBrownianExcursionSampler,
        brownianSkeletonClock, brownianClockUpdate, brownianSelectedNextExitTime, hc] using
        stoppedBrownianRepresentative_next_endPoint (U j) z
          (fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2) ω hf

theorem brownianSkeletonExcursion_frozen_of_le (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (t : ℝ≥0) (ω : BrownianPath d)
    (ht : (brownianSkeletonClock U z j₀ selector n ω).2 ≤ (t : ℝ≥0∞)) :
    brownianSkeletonExcursion U z j₀ selector n (frozenBrownianPath t ω) =
      brownianSkeletonExcursion U z j₀ selector n ω := by
  cases n with
  | zero =>
    exact congrArg (fun c ↦ (false, c))
      (stoppedBrownianRepresentative_frozen_of_exit_le (hU j₀) z ω t ht)
  | succ n =>
    have hprev := (brownianSkeletonClock_time_le_succ U z j₀ selector n ω).trans ht
    have hclock := brownianSkeletonClock_frozen_of_le U hU z j₀ selector n t ω hprev
    have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top hprev
    have htime : (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfinite]
      exact hprev
    have hc : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) (frozenBrownianPath t ω) =
        brownianClockChoice z (selector (n + 1))
          (brownianSkeletonClock U z j₀ selector n) ω := by
      simp only [brownianClockChoice, hclock, frozenBrownianPath_apply, min_eq_left htime]
    cases hchoice : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) ω with
    | none =>
      simp only [brownianSkeletonExcursion, hc, hchoice, selectedBrownianExcursionSampler,
        hclock, frozenBrownianPath_apply, min_eq_left htime]
    | some j =>
      have hnext : brownianNextExitTime (U j) z
          (fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2) ω ≤ (t : ℝ≥0∞) := by
        simpa only [brownianSkeletonClock, brownianClockUpdate,
          brownianSelectedNextExitTime, hchoice] using ht
      simpa only [brownianSkeletonExcursion, hc, hchoice, selectedBrownianExcursionSampler] using
        congrArg (fun c ↦ (false, c))
          (stoppedBrownianNextRepresentative_frozen (hU j) z
            (brownianSkeletonClock_frozen U hU z j₀ selector n) t ω hnext)

theorem measurable_brownianSkeletonExcursion_stopping (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    {selector : ℕ → Euc d → Option J} (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    Measurable[(isStoppingTime_brownianSkeletonClock U hU z j₀ hselector n).measurableSpace]
      (brownianSkeletonExcursion U z j₀ selector n) :=
  measurable_brownianHistory_stopping_of_frozen
    (isStoppingTime_brownianSkeletonClock U hU z j₀ hselector n)
    (measurable_brownianSkeletonExcursion U hU z j₀ hselector n)
    (brownianSkeletonExcursion_frozen_of_le U hU z j₀ selector n)

theorem brownianSkeletonExcursion_eq_absorbingSampler (U : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞) :
    brownianSkeletonExcursion U z j₀ selector (n + 1) ω =
      absorbingBrownianExcursionSampler U (selector (n + 1))
        (brownianSkeletonExcursion U z j₀ selector n ω)
        (shiftedBrownianPath (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal ω) := by
  rw [absorbingBrownianExcursionSampler, brownianSkeletonExcursion_flag,
    brownianSkeletonExcursion_endPoint U z j₀ selector n ω hfinite]
  rfl

end BouRabeeGwynne

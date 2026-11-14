/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSkeletonClock at commit fdb5cad; the module paths of local imports and lint-related details are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSelectedExit

/-!
# Actual successive Brownian excursion clocks

State zero ends the first genuine excursion in the prescribed initial domain.
Each later domain is chosen from the preceding spatial endpoint. The Boolean
flag makes termination permanent, independently of later stage selectors.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def brownianClockChoice (z : Euc d) (selector : Euc d → Option J)
    (state : BrownianPath d → Bool × ℝ≥0∞) (ω : BrownianPath d) : Option J :=
  if (state ω).1 = true then none else selector (z + ω (state ω).2.toNNReal)

noncomputable def brownianClockUpdate (U : J → Set (Euc d)) (z : Euc d)
    (selector : Euc d → Option J) (state : BrownianPath d → Bool × ℝ≥0∞)
    (ω : BrownianPath d) : Bool × ℝ≥0∞ :=
  ((brownianClockChoice z selector state ω).isNone,
    brownianSelectedNextExitTime U z (fun η ↦ (state η).2)
      (brownianClockChoice z selector state) ω)

noncomputable def brownianSkeletonClock (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) : ℕ → BrownianPath d → Bool × ℝ≥0∞
  | 0 => fun ω ↦ (false, continuousExitTime (U j₀) z ω)
  | n + 1 => brownianClockUpdate U z (selector (n + 1))
      (brownianSkeletonClock U z j₀ selector n)

omit [Countable J] [MeasurableSingletonClass (Option J)] in
lemma measurable_brownianClockChoice (z : Euc d) {selector : Euc d → Option J}
    (hselector : Measurable selector) {state : BrownianPath d → Bool × ℝ≥0∞}
    (hstate : Measurable state) : Measurable (brownianClockChoice z selector state) := by
  have heval : Measurable (fun p : BrownianPath d × ℝ≥0 ↦ p.1 p.2) := by fun_prop
  have ht : Measurable (fun ω ↦ (state ω).2.toNNReal) :=
    ENNReal.measurable_toNNReal.comp (measurable_snd.comp hstate)
  have hp : Measurable (fun ω : BrownianPath d ↦ z + ω (state ω).2.toNNReal) := by
    simpa only [Pi.add_def, Function.comp_def, id_eq] using
      (measurable_const (a := z)).add (heval.comp (measurable_id.prodMk ht))
  exact (measurable_const : Measurable (fun _ : BrownianPath d ↦ (none : Option J))).piecewise
    ((measurable_fst.comp hstate) (measurableSet_singleton true)) (hselector.comp hp)

lemma measurable_brownianClockUpdate (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (z : Euc d) {selector : Euc d → Option J} (hselector : Measurable selector)
    {state : BrownianPath d → Bool × ℝ≥0∞} (hstate : Measurable state) :
    Measurable (brownianClockUpdate U z selector state) := by
  have hc := measurable_brownianClockChoice z hselector hstate
  exact ((measurable_of_countable (fun a : Option J ↦ a.isNone)).comp hc).prodMk
    (measurable_brownianSelectedNextExitTime U hU z (measurable_snd.comp hstate) hc)

lemma measurable_brownianSkeletonClock (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (z : Euc d) (j₀ : J) {selector : ℕ → Euc d → Option J}
    (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    Measurable (brownianSkeletonClock U z j₀ selector n) := by
  induction n with
  | zero => exact measurable_const.prodMk (measurable_continuousExitTime (hU j₀) z)
  | succ n ih => exact measurable_brownianClockUpdate U hU z (hselector (n + 1)) ih

private def ClockRespectsFreezing (state : BrownianPath d → Bool × ℝ≥0∞) : Prop :=
  (∀ t ω, (state (frozenBrownianPath t ω)).2 =
    if (state ω).2 ≤ (t : ℝ≥0∞) then (state ω).2 else ∞) ∧
  ∀ (t : ℝ≥0) ω, (state ω).2 ≤ (t : ℝ≥0∞) → state (frozenBrownianPath t ω) = state ω

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
private lemma clockChoice_frozen (z : Euc d) (selector : Euc d → Option J)
    {state : BrownianPath d → Bool × ℝ≥0∞} (hstate : ClockRespectsFreezing state)
    (t : ℝ≥0) (ω : BrownianPath d) (ht : (state ω).2 ≤ (t : ℝ≥0∞)) :
    brownianClockChoice z selector state (frozenBrownianPath t ω) =
      brownianClockChoice z selector state ω := by
  have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  have htime : (state ω).2.toNNReal ≤ t := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfinite]
    exact ht
  simp only [brownianClockChoice, hstate.2 t ω ht, frozenBrownianPath_apply,
    min_eq_left htime]

private lemma clockUpdate_respectsFreezing (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (selector : Euc d → Option J)
    {state : BrownianPath d → Bool × ℝ≥0∞} (hstate : ClockRespectsFreezing state) :
    ClockRespectsFreezing (brownianClockUpdate U z selector state) := by
  have hc := clockChoice_frozen z selector hstate
  have htime := brownianSelectedNextExitTime_frozen U hU z hstate.1 hc
  refine ⟨htime, ?_⟩
  intro t ω ht
  have hprev : (state ω).2 ≤ (t : ℝ≥0∞) :=
    (le_brownianSelectedNextExitTime U z (fun η ↦ (state η).2)
      (brownianClockChoice z selector state) ω).trans ht
  apply Prod.ext
  · exact congrArg Option.isNone (hc t ω hprev)
  · have he := htime t ω
    change (brownianClockUpdate U z selector state (frozenBrownianPath t ω)).2 =
      (if (brownianClockUpdate U z selector state ω).2 ≤ (t : ℝ≥0∞)
        then (brownianClockUpdate U z selector state ω).2 else ∞) at he
    simpa only [ite_eq_left ht] using he

private lemma skeletonClock_respectsFreezing (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) :
    ClockRespectsFreezing (brownianSkeletonClock U z j₀ selector n) := by
  induction n with
  | zero =>
    refine ⟨fun t ω ↦ continuousExitTime_frozen (hU j₀) z ω t, ?_⟩
    intro t ω ht
    change continuousExitTime (U j₀) z ω ≤ (t : ℝ≥0∞) at ht
    change (false, continuousExitTime (U j₀) z (frozenBrownianPath t ω)) =
      (false, continuousExitTime (U j₀) z ω)
    rw [continuousExitTime_frozen (hU j₀), ite_eq_left ht]
  | succ n ih => exact clockUpdate_respectsFreezing U hU z (selector (n + 1)) ih

theorem brownianSkeletonClock_frozen (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (t : ℝ≥0) (ω : BrownianPath d) :
    (brownianSkeletonClock U z j₀ selector n (frozenBrownianPath t ω)).2 =
      if (brownianSkeletonClock U z j₀ selector n ω).2 ≤ (t : ℝ≥0∞)
      then (brownianSkeletonClock U z j₀ selector n ω).2 else ∞ :=
  (skeletonClock_respectsFreezing U hU z j₀ selector n).1 t ω

theorem brownianSkeletonClock_frozen_of_le (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (t : ℝ≥0) (ω : BrownianPath d)
    (ht : (brownianSkeletonClock U z j₀ selector n ω).2 ≤ (t : ℝ≥0∞)) :
    brownianSkeletonClock U z j₀ selector n (frozenBrownianPath t ω) =
      brownianSkeletonClock U z j₀ selector n ω :=
  (skeletonClock_respectsFreezing U hU z j₀ selector n).2 t ω ht

theorem isStoppingTime_brownianSkeletonClock (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    {selector : ℕ → Euc d → Option J} (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    IsStoppingTime (brownianNaturalFiltration d)
      (fun ω ↦ (brownianSkeletonClock U z j₀ selector n ω).2) := by
  apply isStoppingTime_of_frozen_events
    (measurable_snd.comp (measurable_brownianSkeletonClock U hU z j₀ hselector n))
  intro t ω
  simp only [Function.comp_apply]
  rw [brownianSkeletonClock_frozen U hU z j₀ selector n]
  split_ifs <;> simp_all

theorem standardBrownianLaw_ae_finiteSkeletonClock (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (z : Euc d) (j₀ : J)
    {selector : ℕ → Euc d → Option J} (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    ∀ᵐ ω ∂μ, (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞ := by
  induction n with
  | zero => exact standardBrownianLaw_ae_finiteExit hd hμ (hUb j₀) z
  | succ n ih =>
    exact standardBrownianLaw_ae_finiteSelectedNextExit hd hμ U hU hUb z
      (isStoppingTime_brownianSkeletonClock U hU z j₀ hselector n) ih _

theorem brownianSkeletonClock_time_le_succ (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d) :
    (brownianSkeletonClock U z j₀ selector n ω).2 ≤
      (brownianSkeletonClock U z j₀ selector (n + 1) ω).2 := by
  exact le_brownianSelectedNextExitTime U z
    (fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2)
    (brownianClockChoice z (selector (n + 1)) (brownianSkeletonClock U z j₀ selector n)) ω

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
theorem brownianSkeletonClock_absorbed (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hstop : (brownianSkeletonClock U z j₀ selector n ω).1 = true) :
    brownianSkeletonClock U z j₀ selector (n + 1) ω =
      brownianSkeletonClock U z j₀ selector n ω := by
  apply Prod.ext
  · simp only [brownianSkeletonClock, brownianClockUpdate, brownianClockChoice,
      hstop, ite_eq_left, Option.isNone_none]
  · simp only [brownianSkeletonClock, brownianClockUpdate, brownianClockChoice,
      hstop, ite_eq_left, brownianSelectedNextExitTime]

end BouRabeeGwynne

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ClockTraceApproximation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetOccupationClock

/-!
# Approximation by occupation-clock traces

This file isolates the deterministic compression step needed to compare a path with
candidate traces on increasing vertex targets.  The only link between a candidate trace
and the original path is the explicit clock-compatibility hypothesis below.  Establishing
that compatibility from a future trace representation is a separate, still-unproved task;
the results here do not assert that the candidate traces are associated with any form.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal ReflectedWalk

universe u

namespace ReflectedGMS.ClockTraceApproximation

open ReflectedGMS.TargetOccupationClock
open ReflectedWalk ReflectedWalk.Theorem16

variable {V : Type u} {Ω : Type u} [MeasurableSpace Ω]

/-- A candidate trace reads the original path at its target occupation clock.

This is an intermediate representation input.  A later construction of the trace process
must prove it; it is not a final reflected-walk or form-association hypothesis. -/
def ClockCompatible (A : ℕ → Set V) (X : ℝ≥0 → Ω → Option V)
    (Q : ℕ → ℝ≥0 → Ω → Option V) (ω : Ω) : Prop :=
  ∀ n u, X u ω ∈ some '' A n →
    Q n (occupationClock (A n) X u ω).toNNReal ω = X u ω

/-- Deterministic compression comparison at one time and outcome.

If `X` stays at a target vertex just to the right of `t`, clock convergence makes the lag
`t - Cₙ(t)` smaller than that constant interval.  The clock then reaches `t` at original
time `t + (t - Cₙ(t))`, where compatibility identifies the trace with `X t`. -/
theorem eventually_eq_of_clockCompatible {A : ℕ → Set V} (hAmono : Monotone A)
    (hAcov : ∀ x, ∃ n, x ∈ A n) (X : ℝ≥0 → Ω → Option V)
    (Q : ℕ → ℝ≥0 → Ω → Option V) (ω : Ω) (t : ℝ≥0) (y : V)
    (hy : X t ω = some y) (ε : ℝ≥0) (hε : 0 < ε)
    (hstay : ∀ u ∈ Icc t (t + ε), X u ω = some y)
    (hclock : Tendsto (fun n => occupationClock (A n) X t ω) atTop
      (𝓝 (t : ℝ≥0∞)))
    (hcompat : ClockCompatible A X Q ω) :
    ∀ᶠ n in atTop, Q n t ω = X t ω := by
  have hfinite : ∀ n, occupationClock (A n) X t ω ≠ ∞ := fun n =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (occupationClock_le (A n) X t ω)
  have hclock_nn : Tendsto
      (fun n => (occupationClock (A n) X t ω).toNNReal) atTop (𝓝 t) := by
    change Tendsto (ENNReal.toNNReal ∘ fun n => occupationClock (A n) X t ω)
      atTop (𝓝 ((t : ℝ≥0∞).toNNReal))
    exact (ENNReal.tendsto_toNNReal ENNReal.coe_ne_top).comp hclock
  have hlag : Tendsto
      (fun n => t - (occupationClock (A n) X t ω).toNNReal) atTop (𝓝 0) := by
    simpa only [tsub_self] using (tendsto_const_nhds (x := t)).sub hclock_nn
  have hsmall : ∀ᶠ n in atTop,
      t - (occupationClock (A n) X t ω).toNNReal < ε :=
    hlag (gt_mem_nhds hε)
  obtain ⟨n₀, hyn₀⟩ := hAcov y
  filter_upwards [hsmall, eventually_ge_atTop n₀] with n hn hnn
  let c : ℝ≥0 := (occupationClock (A n) X t ω).toNNReal
  let δ : ℝ≥0 := t - c
  have hc : c ≤ t := by
    apply (ENNReal.toNNReal_le_toNNReal (hfinite n) ENNReal.coe_ne_top).2
    exact occupationClock_le (A n) X t ω
  have hδ : δ < ε := hn
  have hyAn : y ∈ A n := hAmono hnn hyn₀
  have hstayδ : ∀ u ∈ Icc t (t + δ), X u ω = some y := by
    intro u hu
    exact hstay u ⟨hu.1, hu.2.trans (by simpa [add_comm] using add_le_add_left hδ.le t)⟩
  have hclock_forward : occupationClock (A n) X (t + δ) ω = (t : ℝ≥0∞) := by
    rw [occupationClock_add_of_stays_in_target (A n) X t δ ω y hyAn hstayδ]
    calc
      occupationClock (A n) X t ω + (δ : ℝ≥0∞) = (c : ℝ≥0∞) + (δ : ℝ≥0∞) := by
        rw [ENNReal.coe_toNNReal (hfinite n)]
      _ = ((c + δ : ℝ≥0) : ℝ≥0∞) := by simp
      _ = (t : ℝ≥0∞) := by rw [add_tsub_cancel_of_le hc]
  have hXu : X (t + δ) ω = some y := hstayδ _ ⟨le_add_right le_rfl, le_rfl⟩
  have hQ := hcompat n (t + δ) ⟨y, hyAn, hXu.symm⟩
  rw [hclock_forward, ENNReal.toNNReal_coe] at hQ
  exact hQ.trans (hXu.trans hy.symm)

/-- Almost-sure fixed-time approximation supplied by an actual reflected walk and its true
occupation clocks.  The explicit `ClockCompatible` event is the remaining representation
packet that a future construction of `Q` must discharge. -/
theorem IsReflectedWalk.approximatedAtFixedTimes_of_clockCompatible [Countable V]
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {𝓧 : ProcessFamily V} (hwalk : IsReflectedWalk G w hmin 𝓧)
    {A : ℕ → Set V} (hAmono : Monotone A) (hAcov : ∀ x, ∃ n, x ∈ A n)
    (Q : ℕ → ℝ≥0 → 𝓧.Ω → Option V) (z : V)
    (hcompat : ∀ᵐ ω ∂𝓧.P z, ClockCompatible A 𝓧.X Q ω) :
    ApproximatedAtFixedTimes (𝓧.P z) 𝓧.X Q := by
  intro t
  filter_upwards [(hwalk z).2.1 t, (hwalk z).2.2.1,
    ReflectedGMS.TargetOccupationClock.IsReflectedWalk.ae_tendsto_occupationClock_all_t
      hwalk hAmono hAcov z, hcompat]
      with ω hdefined hright hclock hcompatω
  obtain ⟨y, hy⟩ := hdefined.1
  obtain ⟨ε, hε, hrightε⟩ := hright t ⟨y, hy⟩
  let η : ℝ≥0 := ε / 2
  have hη : 0 < η := div_pos hε (by norm_num)
  have hηε : η < ε := by
    simpa only [η] using (half_lt_self hε)
  have hstay : ∀ u ∈ Icc t (t + η), 𝓧.X u ω = some y := by
    intro u hu
    rw [← hy]
    exact hrightε u ⟨hu.1,
      hu.2.trans_lt (by simpa [add_comm] using add_lt_add_left hηε t)⟩
  exact eventually_eq_of_clockCompatible hAmono hAcov 𝓧.X Q ω t y hy η hη hstay
    (hclock t) hcompatω

end ReflectedGMS.ClockTraceApproximation

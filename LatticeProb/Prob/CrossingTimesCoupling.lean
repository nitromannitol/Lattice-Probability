import Mathlib
import LatticeProb.Prob.CrossingTimesClock6
import LatticeProb.Prob.MarkovStepShiftedPath

/-!
# Time-changed paths and the crossing clock: transfer along a coupling

Let `x = f ∘ τ` be a path obtained from `f : ℝ≥0 → E` by an increasing homeomorphism `τ` of
`ℝ≥0` (continuous, strictly increasing, `τ 0 = 0`, unbounded).  If the crossing clock of `f` is the
identity (`crossClock m f u = u`) then the crossing clock of `x` is `τ`, so `x` has a good clock
(`GoodClock`), `clockInv (crossClock m x) t = τ⁻¹ t`, and the path read in the time scale of its
crossing clock is `f` again.  If moreover the crossing clock of the time-`t` shift of `f` is the
identity, then at the optional time `A_t = clockInv (crossClock m x) t` we have the shift identity

* `A_{t+s}(x) = A_t(x) + A_s (x (A_t + ·))` and
* `x (A_t + ·)` read in its own clock at time `s` equals `x` read in its clock at time `t + s`.

These are statements about the single path `x`, for fixed `t` and `s` (`ShiftIdentity m t s x`);
the set of paths satisfying them is measurable.  Hence they hold almost surely for the law of
`x` whenever they hold almost surely on a probability space carrying a coupling `X = B ∘ τ` with
`B` having the identity crossing clock (also after the deterministic time shift `t`).

* `shiftIdentity_of_timeChange`: the deterministic statement;
* `measurableSet_shiftIdentity`: measurability of the set of such paths;
* `ae_map_goodClock`, `ae_map_shiftIdentity`: transfer to the law of `X`;
* `map_clockPath_eq`: the clock-read path of `X` has the law of `B`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

section Deterministic

variable {E : Type*} [MetricSpace E]

/-- The inverse crossing clock of a continuous path. -/
def pathClockInv (m : ℝ≥0∞) (x : C(ℝ≥0, E)) (t : ℝ≥0) : ℝ≥0∞ :=
  clockInv (crossClock m (fun u => x u)) t

/-- The shift identity at the optional time `A_t` for the path `x`, with fixed `t` and `s`:
`A_t < ⊤`, `A_{t+s}(x) = A_t(x) + A_s (x (A_t + ·))`, and the path `x (A_t + ·)` read in its own
crossing clock at time `s` equals `x` read in its crossing clock at time `t + s`. -/
def ShiftIdentity (m : ℝ≥0∞) (t s : ℝ≥0) (x : C(ℝ≥0, E)) : Prop :=
  pathClockInv m x t < ⊤ ∧
    pathClockInv m x (t + s) =
      pathClockInv m x t + pathClockInv m (pathShift x (pathClockInv m x t).toNNReal) s ∧
    clockPath m (fun u => pathShift x (pathClockInv m x t).toNNReal u) s =
      clockPath m (fun u => x u) (t + s)

/-- The clock `u ↦ τ u` of an increasing homeomorphism of `ℝ≥0` is good. -/
theorem goodClock_coe {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ) (hτ0 : τ 0 = 0)
    (hτu : Tendsto τ atTop atTop) : GoodClock fun u => (τ u : ℝ≥0∞) := by
  refine ⟨by simp [hτ0], fun _ => ENNReal.coe_lt_top, fun r r' h => ?_, fun n => ?_⟩
  · show ((τ (ratTime r) : ℝ≥0) : ℝ≥0∞) < (τ (ratTime r') : ℝ≥0)
    exact_mod_cast hτm h
  · obtain ⟨σ, hσ⟩ := exists_eq_of_unbounded hτc hτ0 hτu (n : ℝ≥0)
    obtain ⟨q, hq⟩ := exists_rat_gt (σ : ℝ)
    refine ⟨q, ?_⟩
    have h1 : τ σ ≤ τ (ratTime q) := hτm.monotone (le_ratTime_of_lt hq)
    calc (n : ℝ≥0∞) = ((τ σ : ℝ≥0) : ℝ≥0∞) := by rw [hσ, ENNReal.coe_natCast]
      _ ≤ τ (ratTime q) := by exact_mod_cast h1

/-- **The deterministic shift identity for a time-changed path.** -/
theorem shiftIdentity_of_timeChange {f : ℝ≥0 → E} {τ : ℝ≥0 → ℝ≥0} {m : ℝ≥0∞} (x : C(ℝ≥0, E))
    (hx : ∀ u, x u = f (τ u)) (hτc : Continuous τ) (hτm : StrictMono τ) (hτ0 : τ 0 = 0)
    (hτu : Tendsto τ atTop atTop) (hf : ∀ u, crossClock m f u = u) {t : ℝ≥0}
    (hft : ∀ u, crossClock m (fun w => f (t + w)) u = u) (s : ℝ≥0) : ShiftIdentity m t s x := by
  have hxf : (fun u => x u) = f ∘ τ := funext hx
  obtain ⟨a, ha⟩ := exists_eq_of_unbounded hτc hτ0 hτu t
  have hA : pathClockInv m x t = a := by
    unfold pathClockInv
    rw [hxf]
    exact clockInv_comp hτc hτm hτ0 hf ha
  have hsh : (fun v => pathShift x a v) = fun v => (f ∘ τ) (a + v) := by
    funext v
    simp [hx]
  have hs := clockInv_shift hτc hτm hτ0 hτu hf (a := a) (by rw [ha]; exact hft) s
  rw [ha] at hs
  obtain ⟨h1, h2⟩ := hs
  have e1 : pathClockInv m x (t + s) = clockInv (crossClock m (f ∘ τ)) (t + s) := by
    unfold pathClockInv
    rw [hxf]
  have e2 : pathClockInv m (pathShift x a) s =
      clockInv (crossClock m (fun v => (f ∘ τ) (a + v))) s := by
    unfold pathClockInv
    rw [hsh]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    exact ENNReal.coe_lt_top
  · rw [hA, ENNReal.toNNReal_coe, e1, e2]
    exact h1
  · rw [hA, ENNReal.toNNReal_coe, hsh, hxf]
    exact h2

end Deterministic

section Transfer

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_pathClockInv (m : ℝ≥0∞) (t : ℝ≥0) :
    Measurable fun y : C(ℝ≥0, E) => pathClockInv m y t :=
  measurable_clockInv m t

/-- The paths with the shift identity at fixed `t` and `s` form a measurable set. -/
theorem measurableSet_shiftIdentity (m : ℝ≥0∞) (t s : ℝ≥0) :
    MeasurableSet {x : C(ℝ≥0, E) | ShiftIdentity m t s x} := by
  have hA : Measurable fun y : C(ℝ≥0, E) => pathClockInv m y t := measurable_pathClockInv m t
  have hsh : Measurable fun y : C(ℝ≥0, E) => pathShift y (pathClockInv m y t).toNNReal :=
    continuous_pathShift_uncurry.measurable.comp (measurable_id.prodMk hA.ennreal_toNNReal)
  have hB : Measurable fun y : C(ℝ≥0, E) =>
      pathClockInv m (pathShift y (pathClockInv m y t).toNNReal) s :=
    (measurable_pathClockInv m s).comp hsh
  have hP : Measurable fun y : C(ℝ≥0, E) =>
      clockPath m (fun u => pathShift y (pathClockInv m y t).toNNReal u) s :=
    (measurable_clockPath m s).comp hsh
  have hQ : Measurable fun y : C(ℝ≥0, E) => clockPath m (fun u => y u) (t + s) :=
    measurable_clockPath m (t + s)
  have h1 : MeasurableSet {y : C(ℝ≥0, E) | pathClockInv m y t < ⊤} :=
    measurableSet_lt hA measurable_const
  have h2 : MeasurableSet {y : C(ℝ≥0, E) | pathClockInv m y (t + s) =
      pathClockInv m y t + pathClockInv m (pathShift y (pathClockInv m y t).toNNReal) s} :=
    measurableSet_eq_fun (measurable_pathClockInv m (t + s)) (hA.add hB)
  have h3 : MeasurableSet {y : C(ℝ≥0, E) | clockPath m (fun u => pathShift y
      (pathClockInv m y t).toNNReal u) s = clockPath m (fun u => y u) (t + s)} :=
    measurableSet_eq_fun hP hQ
  exact h1.inter (h2.inter h3)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Transfer of the good clock** to the law of the time-changed process `X = B ∘ τ`. -/
theorem ae_map_goodClock {Q : Measure Ω} {X : Ω → C(ℝ≥0, E)} {B : Ω → ℝ≥0 → E}
    {τ : Ω → ℝ≥0 → ℝ≥0} {m : ℝ≥0∞} (hX : AEMeasurable X Q)
    (hτ : ∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧
      Tendsto (τ ω) atTop atTop ∧ ∀ u, X ω u = B ω (τ ω u))
    (hB : ∀ᵐ ω ∂Q, ∀ u, crossClock m (B ω) u = u) :
    ∀ᵐ x ∂(Q.map X), GoodClock (crossClock m (fun u => (x : C(ℝ≥0, E)) u)) := by
  rw [ae_map_iff hX (measurableSet_goodClock m)]
  filter_upwards [hτ, hB] with ω ⟨hc, hm, h0, hu, hx⟩ hBω
  have hxf : (fun u => X ω u) = B ω ∘ τ ω := funext hx
  rw [hxf, crossClock_comp_of_clock_id hc hm h0 hBω]
  exact goodClock_coe hc hm h0 hu

/-- **Transfer of the shift identity** (fixed `t` and `s`) to the law of the time-changed process
`X = B ∘ τ`, when the crossing clock of `B` and of its time-`t` shift is the identity. -/
theorem ae_map_shiftIdentity {Q : Measure Ω} {X : Ω → C(ℝ≥0, E)} {B : Ω → ℝ≥0 → E}
    {τ : Ω → ℝ≥0 → ℝ≥0} {m : ℝ≥0∞} (hX : AEMeasurable X Q)
    (hτ : ∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧
      Tendsto (τ ω) atTop atTop ∧ ∀ u, X ω u = B ω (τ ω u))
    (hB : ∀ᵐ ω ∂Q, ∀ u, crossClock m (B ω) u = u) (t s : ℝ≥0)
    (hBt : ∀ᵐ ω ∂Q, ∀ u, crossClock m (fun w => B ω (t + w)) u = u) :
    ∀ᵐ x ∂(Q.map X), ShiftIdentity m t s x := by
  rw [ae_map_iff hX (measurableSet_shiftIdentity m t s)]
  filter_upwards [hτ, hB, hBt] with ω ⟨hc, hm, h0, hu, hx⟩ hBω hBtω
  exact shiftIdentity_of_timeChange (X ω) hx hc hm h0 hu hBω hBtω s

/-- **The clock-read path has the law of the base process**: reading `X = B ∘ τ` in the time scale
of its crossing clock returns `B`. -/
theorem map_clockPath_eq {Q : Measure Ω} {X : Ω → C(ℝ≥0, E)} {B : Ω → ℝ≥0 → E}
    {τ : Ω → ℝ≥0 → ℝ≥0} {m : ℝ≥0∞} (hX : AEMeasurable X Q)
    (hτ : ∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧
      Tendsto (τ ω) atTop atTop ∧ ∀ u, X ω u = B ω (τ ω u))
    (hB : ∀ᵐ ω ∂Q, ∀ u, crossClock m (B ω) u = u) :
    (Q.map X).map (fun (y : C(ℝ≥0, E)) (t : ℝ≥0) => clockPath m (fun u => y u) t) =
      Q.map B := by
  have hmeas : Measurable fun (y : C(ℝ≥0, E)) (t : ℝ≥0) => clockPath m (fun u => y u) t :=
    Measurable.of_eval fun t => measurable_clockPath m t
  rw [AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hX]
  refine Measure.map_congr ?_
  filter_upwards [hτ, hB] with ω ⟨hc, hm, h0, hu, hx⟩ hBω
  funext t
  obtain ⟨a, ha⟩ := exists_eq_of_unbounded hc h0 hu t
  have hxf : (fun u => X ω u) = B ω ∘ τ ω := funext hx
  simp only [Function.comp_apply]
  rw [hxf]
  exact clockPath_comp hc hm h0 hBω ha

end Transfer

end LatticeProb

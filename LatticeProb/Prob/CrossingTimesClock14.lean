/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesCoupling
import LatticeProb.Prob.CrossingTimesClock6
import LatticeProb.Prob.CrossingTimesClock3
import LatticeProb.Prob.BrownianMarkov

/-!
# Clock data for a time-changed Brownian motion

For a Brownian motion `B` with continuous paths in `ℝ ^ d` and the constant `m` of
`exists_ae_crossClock_eq_self`, the crossing clock of `B` and of each of its fixed-time shifts is the
identity almost surely (`exists_ae_crossClock_eq_self_shift`).  We also record, for the law of a
time-changed process `X = B ∘ τ`:

* `measurable_crossCount_comp`, `measurable_crossClock_comp`: the crossing count and the crossing
  clock of a continuous path, read at a measurable random time, are measurable;
* `measurableSet_attained`: the paths for which the infimum defining the inverse crossing clock at
  time `t` is attained form a measurable set;
* `ae_map_attained`: attainment transfers to the law of `X = B ∘ τ`;
* `ae_continuous_pathClockInv_of_good`: for a good clock the inverse clock is continuous.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- Adding a constant to a path does not change its crossing clock. -/
theorem crossClock_add_const {G : Type*} [SeminormedAddCommGroup G] (m : ℝ≥0∞) (f : ℝ≥0 → G)
    (c : G) (u : ℝ≥0) : crossClock m (fun s => f s + c) u = crossClock m f u := by
  unfold crossClock
  simp only [crossCount_add_const]

section Measurability

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The number of `ε`-crossings of a continuous path in `[0, g y]` is measurable in the path
when `g` is a measurable random time. -/
theorem measurable_crossCount_comp {ε : ℝ} (hε : 0 < ε) {g : C(ℝ≥0, E) → ℝ≥0}
    (hg : Measurable g) :
    Measurable fun y : C(ℝ≥0, E) => crossCount ε (fun s => y s) (g y) := by
  rw [ENat.measurable_iff]
  intro n
  have h1 : MeasurableSet {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) n ≤ (g y : ℝ≥0∞)} :=
    measurableSet_le (measurable_crossTime hε n) hg.coe_nnreal_ennreal
  have h2 : MeasurableSet {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) (n + 1) ≤ (g y : ℝ≥0∞)} :=
    measurableSet_le (measurable_crossTime hε (n + 1)) hg.coe_nnreal_ennreal
  have h3 : (fun y : C(ℝ≥0, E) => crossCount ε (fun s => y s) (g y)) ⁻¹' {(n : ℕ∞)} =
      {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) n ≤ (g y : ℝ≥0∞)} \
        {y : C(ℝ≥0, E) | crossTime ε (fun s => y s) (n + 1) ≤ (g y : ℝ≥0∞)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    rw [← le_crossCount_iff, ← le_crossCount_iff]
    generalize crossCount ε (fun s => y s) (g y) = c
    constructor
    · rintro rfl
      exact ⟨le_rfl, fun h => by have := Nat.cast_le.1 h; omega⟩
    · rintro ⟨h1, h2⟩
      induction c using ENat.recTopCoe with
      | top => exact absurd le_top h2
      | coe k =>
        have h1' := Nat.cast_le.1 h1
        have h2' : ¬ (n + 1 ≤ k) := fun h => h2 (Nat.cast_le.2 h)
        have : k = n := by omega
        rw [this]
  rw [h3]
  exact h1.diff h2

/-- The crossing clock of a continuous path at a measurable random time is measurable. -/
theorem measurable_crossClock_comp (m : ℝ≥0∞) {g : C(ℝ≥0, E) → ℝ≥0} (hg : Measurable g) :
    Measurable fun y : C(ℝ≥0, E) => crossClock m (fun s => y s) (g y) := by
  refine Measurable.limsup fun n => ?_
  have h1 := measurable_crossCount_comp (E := E) (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n) hg
  have h2 : Measurable fun y : C(ℝ≥0, E) =>
      ENat.toENNReal (crossCount ((2 : ℝ)⁻¹ ^ n) (fun s => y s) (g y)) :=
    (Measurable.of_discrete (f := ENat.toENNReal)).comp h1
  exact measurable_const.mul h2

/-- The paths for which the infimum defining the inverse crossing clock at `t` is attained form a
measurable set. -/
theorem measurableSet_attained (m : ℝ≥0∞) (t : ℝ≥0) :
    MeasurableSet {x : C(ℝ≥0, E) |
      (t : ℝ≥0∞) ≤ crossClock m (fun w => x w) (pathClockInv m x t).toNNReal} :=
  measurableSet_le measurable_const
    (measurable_crossClock_comp m (measurable_pathClockInv m t).ennreal_toNNReal)

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- For a good crossing clock the inverse crossing clock is continuous. -/
theorem ae_continuous_pathClockInv_of_good {μ : Measure C(ℝ≥0, E)} (m : ℝ≥0∞)
    (h : ∀ᵐ x ∂μ, GoodClock (crossClock m fun u => x u)) :
    ∀ᵐ x ∂μ, Continuous fun u : ℝ≥0 => (pathClockInv m x u).toReal :=
  h.mono fun _ hx => hx.continuous_clockInv_toReal (crossClock_mono m _)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Transfer of attainment** to the law of the time-changed process `X = B ∘ τ`, when the crossing
clock of `B` is the identity. -/
theorem ae_map_attained {Q : Measure Ω} {X : Ω → C(ℝ≥0, E)} {B : Ω → ℝ≥0 → E}
    {τ : Ω → ℝ≥0 → ℝ≥0} {m : ℝ≥0∞} (hX : AEMeasurable X Q)
    (hτ : ∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧
      Tendsto (τ ω) atTop atTop ∧ ∀ u, X ω u = B ω (τ ω u))
    (hB : ∀ᵐ ω ∂Q, ∀ u, crossClock m (B ω) u = u) (t : ℝ≥0) :
    ∀ᵐ x ∂(Q.map X),
      (t : ℝ≥0∞) ≤ crossClock m (fun w => (x : C(ℝ≥0, E)) w) (pathClockInv m x t).toNNReal := by
  rw [ae_map_iff hX (measurableSet_attained m t)]
  filter_upwards [hτ, hB] with ω ⟨hc, hm, h0, hu, hx⟩ hBω
  have hxf : (fun u => X ω u) = B ω ∘ τ ω := funext hx
  obtain ⟨a, ha⟩ := exists_eq_of_unbounded hc h0 hu t
  have hA : pathClockInv m (X ω) t = a := by
    unfold pathClockInv
    rw [hxf]
    exact clockInv_comp hc hm h0 hBω ha
  show (t : ℝ≥0∞) ≤ crossClock m (fun w => X ω w) (pathClockInv m (X ω) t).toNNReal
  rw [hA, ENNReal.toNNReal_coe, hxf, crossClock_comp_of_clock_id hc hm h0 hBω]
  show (t : ℝ≥0∞) ≤ ((τ ω a : ℝ≥0) : ℝ≥0∞)
  rw [ha]

end Measurability

section Brownian

/-- **The crossing clock of Brownian motion, and of its shifts, is the identity.**  There is
`m ∈ (0, ∞)`, depending only on `d`, such that for every Brownian motion `B` in `ℝ ^ d` with
continuous paths, almost surely `crossClock m B u = u` for all `u ≥ 0`, and for each fixed `t ≥ 0`
the same holds almost surely for the shifted path `w ↦ B (t + w)`. -/
theorem exists_ae_crossClock_eq_self_shift (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ⊤ ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (x : EuclideanSpace ℝ (Fin d))
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
      (∀ ω, Continuous fun t => B t ω) →
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, crossClock m (fun t => B t ω) u = u) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ u : ℝ≥0, crossClock m (fun w => B (t + w) ω) u = u := by
  obtain ⟨m, hm0, hmt, h⟩ := exists_ae_crossClock_eq_self d hd
  refine ⟨m, hm0, hmt, fun Ω _ P _ x B hB hmeas hcont => ⟨h Ω P x B hB hmeas hcont, fun t => ?_⟩⟩
  have hmeas' : ∀ s, StronglyMeasurable (fun ω => B (t + s) ω - B t ω) := fun s =>
    (hmeas (t + s)).sub (hmeas t)
  have hcont' : ∀ ω, Continuous fun s => B (t + s) ω - B t ω := fun ω =>
    ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  filter_upwards [h Ω P 0 (fun s ω => B (t + s) ω - B t ω) (hB.shift t) hmeas' hcont'] with ω hω u
  have h1 := crossClock_add_const m (fun s => B (t + s) ω - B t ω) (B t ω) u
  simp only [sub_add_cancel] at h1
  rw [h1]
  exact hω u

end Brownian

end LatticeProb

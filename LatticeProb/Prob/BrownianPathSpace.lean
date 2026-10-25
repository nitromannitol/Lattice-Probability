module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/StoppedCurveLaws.lean, BouRabeeGwynne/ContinuousExitProperties.lean,
BouRabeeGwynne/BrownianExitStoppingTime.lean, BouRabeeGwynne/StoppedBrownianMeasurable.lean,
BouRabeeGwynne/BrownianFiniteExit.lean.
-/

public import LatticeProb.Topology.ContinuousMapBorel
public import LatticeProb.Prob.BrownianOpenExit
public import LatticeProb.Prob.BrownianOpenExitStopping
public import LatticeProb.Prob.BrownianOpenExitFinite
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Stopping

@[expose] public section

/-!
# Brownian paths: exit times from open sets and their finiteness

A Brownian path is a continuous map `ℝ≥0 → Euc d`, with the Borel σ-algebra of the compact-open
topology (`LatticeProb.continuousMapMeasurableSpace`). For a path `ω` and a point `z`, the
continuous exit time `continuousExitTime U z ω` is the first time at which the shifted path
`t ↦ z + ω t` lies outside `U`. It is `LatticeProb.openExitTime` applied to that shifted path, so
the deterministic facts about open-set exit times transfer.

The exit time from an open set is a stopping time for the natural filtration of the coordinate
evaluations, and it is measurable. For a standard Brownian law in positive dimension, the exit
time from a bounded set is almost surely finite, and its tail beyond `(n + 1)^2` is bounded
uniformly in the starting point.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The Euclidean space of dimension `d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A continuous Euclidean path on all nonnegative times. Its measurable structure is the Borel
σ-algebra of the compact-open topology, found from `LatticeProb.continuousMapMeasurableSpace`. -/
abbrev BrownianPath (d : ℕ) := C(ℝ≥0, Euc d)

example (d : ℕ) : MeasurableSpace (BrownianPath d) := inferInstance
example (d : ℕ) : BorelSpace (BrownianPath d) := inferInstance

/-- Standard zero-start Brownian law: a probability measure on Brownian paths under which the
coordinate processes are independent and each is a real Brownian motion. -/
def IsStandardBrownianLaw {d : ℕ} (μ : Measure (BrownianPath d)) : Prop :=
  IsProbabilityMeasure μ ∧
  (∀ i : Fin d, IsBrownianReal (fun t ω => ω t i) μ) ∧
  iIndepFun (fun (i : Fin d) (ω : BrownianPath d) => fun t : ℝ≥0 => ω t i) μ

/-- First continuous exit from `U` of the path shifted to start at `z`.
An empty set of exit times has infimum infinity. -/
noncomputable def continuousExitTime {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (ω : BrownianPath d) : ℝ≥0∞ :=
  openExitTime (fun (t : ℝ≥0) (γ : BrownianPath d) ↦ z + γ t) U ω

/-- The continuous exit time is the infimum of the times at which the shifted path lies outside
`U`. -/
lemma continuousExitTime_eq_iInf {d : ℕ} (U : Set (Euc d)) (z : Euc d) (ω : BrownianPath d) :
    continuousExitTime U z ω = ⨅ t : {t : ℝ≥0 // z + ω t ∉ U}, (t.val : ℝ≥0∞) :=
  rfl

section Deterministic

variable {d : ℕ} {U : Set (Euc d)} {z : Euc d} {ω : BrownianPath d}

/-- The continuous exit time is at most every time at which the shifted path is outside `U`. -/
lemma continuousExitTime_le_of_not_mem {t : ℝ≥0} (ht : z + ω t ∉ U) :
    continuousExitTime U z ω ≤ (t : ℝ≥0∞) :=
  openExitTime_le_of_not_mem (B := fun (t : ℝ≥0) (γ : BrownianPath d) ↦ z + γ t) ht

/-- Before its continuous exit time, the shifted path lies in `U`. -/
lemma mem_of_lt_continuousExitTime {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < continuousExitTime U z ω) : z + ω t ∈ U :=
  mem_of_lt_openExitTime (B := fun (t : ℝ≥0) (γ : BrownianPath d) ↦ z + γ t) ht

/-- A shifted path that starts outside `U` has continuous exit time zero. -/
lemma continuousExitTime_eq_zero_of_not_mem (hstart : z + ω 0 ∉ U) :
    continuousExitTime U z ω = 0 :=
  openExitTime_eq_zero_of_not_mem (B := fun (t : ℝ≥0) (γ : BrownianPath d) ↦ z + γ t) hstart

/-- For an open set `U`, a finite continuous exit time is attained: the shifted path is outside
`U` at that time. -/
theorem continuousExitTime_not_mem (hU : IsOpen U)
    (hfinite : continuousExitTime U z ω ≠ ∞) :
    z + ω (continuousExitTime U z ω).toNNReal ∉ U :=
  openExitTime_not_mem (B := fun (t : ℝ≥0) (γ : BrownianPath d) ↦ z + γ t) hU
    (continuous_const.add ω.continuous) hfinite

/-- A finite continuous exit time of a shifted path starting in the open set `U` lies on the
frontier of `U`. -/
theorem continuousExitTime_mem_frontier (hU : IsOpen U)
    (hstart : z + ω 0 ∈ U) (hfinite : continuousExitTime U z ω ≠ ∞) :
    z + ω (continuousExitTime U z ω).toNNReal ∈ frontier U :=
  openExitTime_mem_frontier (B := fun (t : ℝ≥0) (γ : BrownianPath d) ↦ z + γ t) hU
    (continuous_const.add ω.continuous) hstart hfinite

end Deterministic

/-- The natural filtration of the coordinate evaluations `γ ↦ γ t` on Brownian paths. -/
noncomputable def brownianNaturalFiltration (d : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (BrownianPath d)) :=
  Filtration.natural (fun t (γ : BrownianPath d) ↦ γ t)
    (fun t ↦ (by fun_prop : Continuous (fun γ : BrownianPath d ↦ γ t)).stronglyMeasurable)

/-- The restriction of a Brownian path to the compact time interval `[0, t]`. -/
def restrictBrownianPath {d : ℕ} (t : ℝ≥0) (γ : BrownianPath d) :
    C(Icc (0 : ℝ≥0) t, Euc d) :=
  ⟨fun s ↦ γ s, γ.continuous.comp continuous_subtype_val⟩

/-- The restriction of a Brownian path to `[0, t]` is measurable for the natural filtration at
time `t`. -/
lemma measurable_restrictBrownianPath {d : ℕ} (t : ℝ≥0) :
    Measurable[brownianNaturalFiltration d t] (restrictBrownianPath (d := d) t) := by
  letI : MeasurableSpace (BrownianPath d) := brownianNaturalFiltration d t
  apply ContinuousMapBorel.ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact (comap_measurable (fun γ : BrownianPath d ↦ γ s.val)).mono
    (le_iSup₂_of_le s.val s.property.2 le_rfl) le_rfl

/-- The continuous exit time is at most `t` exactly when the shifted path leaves `U` before
time `t`. The path is continuous, so the infimum defining the exit time is attained. -/
theorem continuousExitTime_le_iff_not_mapsTo {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) (z : Euc d) (ω : BrownianPath d) (t : ℝ≥0) :
    continuousExitTime U z ω ≤ (t : ℝ≥0∞) ↔
      ¬ MapsTo ω (Icc (0 : ℝ≥0) t) ((fun x ↦ z + x) ⁻¹' U) :=
  openExitTime_le_iff_not_mapsTo (B := fun (t : ℝ≥0) (γ : BrownianPath d) ↦ z + γ t) hU
    (continuous_const.add ω.continuous) t

private lemma shift_stronglyMeasurable {d : ℕ} (z : Euc d) (s : ℝ≥0) :
    StronglyMeasurable fun γ : BrownianPath d ↦ z + γ s :=
  (by fun_prop : Continuous fun γ : BrownianPath d ↦ z + γ s).stronglyMeasurable

private lemma shift_continuous {d : ℕ} (z : Euc d) (γ : BrownianPath d) :
    Continuous fun s : ℝ≥0 ↦ z + γ s :=
  continuous_const.add γ.continuous

/-- The continuous exit time from an open set is a stopping time for the natural filtration of
the coordinate evaluations. -/
theorem isStoppingTime_continuousExitTime {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) (z : Euc d) :
    IsStoppingTime (brownianNaturalFiltration d) (continuousExitTime U z) := by
  have hstop := isStoppingTime_openExitTime
    (B := fun (s : ℝ≥0) (γ : BrownianPath d) ↦ z + γ s) (shift_stronglyMeasurable z)
    (shift_continuous z) hU
  have hle (t : ℝ≥0) :
      natFiltration (fun (s : ℝ≥0) (γ : BrownianPath d) ↦ z + γ s)
        (shift_stronglyMeasurable z) t ≤ brownianNaturalFiltration d t := by
    rw [natFiltration_eq_comap]
    letI : MeasurableSpace (BrownianPath d) := brownianNaturalFiltration d t
    have hadd : Measurable fun x : Euc d ↦ z + x :=
      (continuous_const.add continuous_id).measurable
    have hmeas : Measurable (fun (γ : BrownianPath d) (s : Set.Iic t) ↦ z + γ (s : ℝ≥0)) := by
      refine measurable_pi_lambda _ fun s ↦ ?_
      have hγ : Measurable (fun γ : BrownianPath d ↦ γ (s : ℝ≥0)) :=
        (comap_measurable (fun γ : BrownianPath d ↦ γ (s : ℝ≥0))).mono
          (le_iSup₂_of_le (s : ℝ≥0) (Set.mem_Iic.mp s.2) le_rfl) le_rfl
      exact hadd.comp hγ
    exact measurable_iff_comap_le.mp hmeas
  intro t
  change MeasurableSet[brownianNaturalFiltration d t]
    {γ : BrownianPath d | continuousExitTime U z γ ≤ (t : ℝ≥0∞)}
  exact hle t _ (hstop t)

/-- The continuous exit time from an open set is measurable on Brownian paths. -/
theorem measurable_continuousExitTime {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) :
    Measurable (continuousExitTime U z) :=
  measurable_openExitTime (B := fun (s : ℝ≥0) (γ : BrownianPath d) ↦ z + γ s)
    (shift_stronglyMeasurable z) (shift_continuous z) hU

/-- Under a standard Brownian law in positive dimension, the continuous exit time from a bounded
set is almost surely finite, from every starting point `z`. -/
theorem standardBrownianLaw_ae_finiteExit {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (z : Euc d) :
    ∀ᵐ ω ∂μ, continuousExitTime U z ω ≠ ∞ := by
  obtain ⟨R, hRpos, hR⟩ := hU.exists_pos_norm_le
  let i : Fin d := ⟨0, hd⟩
  have hnot := preBrownian_ae_not_bounded_square_times
    (hμ.2.1 i).toIsPreBrownianReal (R := R + ‖z‖) (add_nonneg hRpos.le (norm_nonneg _))
  filter_upwards [hnot] with ω hω
  intro hnever
  apply hω
  intro n
  let t : ℝ≥0 := ((n : ℝ≥0) + 1) ^ 2
  have hin : z + ω t ∈ U := by
    by_contra hout
    have hle : continuousExitTime U z ω ≤ (t : ℝ≥0∞) := continuousExitTime_le_of_not_mem hout
    rw [hnever] at hle
    exact ENNReal.coe_ne_top (top_le_iff.mp hle)
  calc
    |ω t i| = ‖ω t i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖ω t‖ := PiLp.norm_apply_le (ω t) i
    _ ≤ ‖z + ω t‖ + ‖z‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (z + ω t) z
    _ ≤ R + ‖z‖ := add_le_add (hR _ hin) le_rfl

/-- For a standard Brownian law, the probability that the continuous exit time exceeds
`(n + 1)^2` is at most the Gaussian probability that a coordinate of variance `(n + 1)^2` lies in
`[-2R, 2R]`, where `R` bounds the norms of the points of `U`. -/
theorem standardBrownianLaw_measure_lateExit_le {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} {R : ℝ} (hR : ∀ x ∈ U, ‖x‖ ≤ R)
    {z : Euc d} (hz : z ∈ U) (n : ℕ) :
    μ {ω | ((((n : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ≥0∞) < continuousExitTime U z ω} ≤
      gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) {x : ℝ | |x| ≤ 2 * R} := by
  let i : Fin d := ⟨0, hd⟩
  let t : ℝ≥0 := ((n : ℝ≥0) + 1) ^ 2
  calc
    _ ≤ μ {ω | |ω t i| ≤ 2 * R} := by
      apply measure_mono
      intro ω hω
      have hin : z + ω t ∈ U := by
        by_contra hout
        exact (not_le_of_gt hω) (continuousExitTime_le_of_not_mem hout)
      calc
        |ω t i| = ‖ω t i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ω t‖ := PiLp.norm_apply_le (ω t) i
        _ ≤ ‖z + ω t‖ + ‖z‖ := by
          simpa only [add_sub_cancel_left] using norm_sub_le (z + ω t) z
        _ ≤ R + R := add_le_add (hR _ hin) (hR _ hz)
        _ = 2 * R := (two_mul R).symm
    _ = _ := ((hμ.2.1 i).toIsPreBrownianReal.hasLaw_eval t).measure_eq
      (isClosed_le continuous_abs continuous_const).measurableSet

/-- Standard Brownian exit tails vanish uniformly over starting points in a bounded set, in
positive dimension: for every positive `ε`, eventually in `n` the probability that the continuous
exit time exceeds `(n + 1)^2` is at most `ε`, for every starting point in `U`. -/
theorem standardBrownianLaw_uniform_exitTail {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ U,
      μ {ω | ((((n : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ≥0∞) < continuousExitTime U z ω} ≤ ε := by
  obtain ⟨R, hRpos, hR⟩ := hU.exists_pos_norm_le
  have hlim := gaussian_square_time_measure_bounded_tendsto_zero
    (mul_nonneg zero_le_two hRpos.le : (0 : ℝ) ≤ 2 * R)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  exact (standardBrownianLaw_measure_lateExit_le hd hμ hR hz n).trans hn.le

namespace BrownianPathSpaceExample

/-- The unit vector `e₀` of `Euc 1`. -/
noncomputable def unitVec : Euc 1 := EuclideanSpace.single 0 1

/-- The unit vector `e₀` has norm one. -/
lemma unitVec_norm : ‖unitVec‖ = 1 := by
  simp [unitVec]

/-- The straight-line path `t ↦ t • v` in `Euc 1`, as a continuous map. -/
def rampPath (v : Euc 1) : BrownianPath 1 :=
  ⟨fun t ↦ (t : ℝ) • v, NNReal.continuous_coe.smul continuous_const⟩

/-- The value of `rampPath v` at `t` is `t • v`. -/
lemma rampPath_apply (v : Euc 1) (t : ℝ≥0) : rampPath v t = (t : ℝ) • v :=
  rfl

/-- The path `t ↦ t • e₀` starts at the origin, which lies in the open unit ball. -/
lemma rampPath_start_mem :
    (0 : Euc 1) + rampPath unitVec 0 ∈ Metric.ball (0 : Euc 1) 1 := by
  simp [rampPath_apply]

/-- The path `t ↦ t • e₀` is outside the open unit ball at time `2`. -/
lemma rampPath_two_not_mem :
    (0 : Euc 1) + rampPath unitVec 2 ∉ Metric.ball (0 : Euc 1) 1 := by
  simp [rampPath_apply, norm_smul, unitVec_norm]

/-- The continuous exit of the path `t ↦ t • e₀` from the open unit ball is finite, since it is
at most `2`. -/
lemma rampPath_exitTime_ne_top :
    continuousExitTime (Metric.ball (0 : Euc 1) 1) 0 (rampPath unitVec) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top
    (continuousExitTime_le_of_not_mem (t := 2) rampPath_two_not_mem)

/-- The continuous exit point of the path `t ↦ t • e₀` from the open unit ball lies on the
frontier of the ball. -/
theorem rampPath_exit_mem_frontier :
    (0 : Euc 1) + rampPath unitVec (continuousExitTime (Metric.ball (0 : Euc 1) 1) 0
        (rampPath unitVec)).toNNReal ∈ frontier (Metric.ball (0 : Euc 1) 1) :=
  continuousExitTime_mem_frontier Metric.isOpen_ball rampPath_start_mem rampPath_exitTime_ne_top

/-- Every standard Brownian law on `Euc 1` exits the open unit ball almost surely, from the
origin. -/
theorem standardBrownianLaw_ae_exit_ball (μ : Measure (BrownianPath 1))
    (hμ : IsStandardBrownianLaw μ) :
    ∀ᵐ ω ∂μ, continuousExitTime (Metric.ball (0 : Euc 1) 1) 0 ω ≠ ∞ :=
  standardBrownianLaw_ae_finiteExit le_rfl hμ Metric.isBounded_ball 0

end BrownianPathSpaceExample

end LatticeProb

module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianExitStoppingTime.lean and BouRabeeGwynne/StoppedBrownianMeasurable.lean.
-/

public import LatticeProb.Prob.BrownianOpenExit
public import LatticeProb.Prob.BrownianMarkov
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-!
# Open-set exit times are stopping times and measurable

For a family of paths `B t ω` with continuous sample paths, the exit time `openExitTime B U` of an
open set `U` is a stopping time for the natural filtration `natFiltration B hm`, and it is
measurable.

Leaving `U` before time `t` is an event about the path on the compact interval `[0, t]`, and that
event is closed rather than open, so it is not decided by countably many times directly. It is
written instead as the countable intersection, over `n`, of the events that the distance from the
path to the complement of `U` drops below `1 / (n + 1)` at some time in `[0, t]`. Each of these
is an open condition and is decided by a countable dense set of times, as in
`measurableSet_exists_le_lt_norm` for balls.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- Having a value of `g ∘ B` below `c` at some time in `[0, t]` is an event of the past up to
`t`, for a continuous function `g` and continuous paths. The strict inequality is open, so a
countable dense set of times in `[0, t]` decides the event. -/
theorem measurableSet_comap_exists_lt {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hcont : ∀ ω, Continuous fun s ↦ B s ω)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g) (c : ℝ) (t : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap (fun ω (s : Set.Iic t) ↦ B (s : ℝ≥0) ω) inferInstance]
      {ω | ∃ s ≤ t, g (B s ω) < c} := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense ↥(Set.Icc (0 : ℝ≥0) t)
  have hEq : {ω | ∃ s ≤ t, g (B s ω) < c} = ⋃ q ∈ D, {ω | g (B (q : ℝ≥0) ω) < c} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨s, hs, hsc⟩
      have hcont' : Continuous fun r : ↥(Set.Icc (0 : ℝ≥0) t) ↦ g (B (r : ℝ≥0) ω) :=
        hg.comp ((hcont ω).comp continuous_subtype_val)
      have hopen : IsOpen {r : ↥(Set.Icc (0 : ℝ≥0) t) | g (B (r : ℝ≥0) ω) < c} :=
        isOpen_lt hcont' continuous_const
      have hne : ({r : ↥(Set.Icc (0 : ℝ≥0) t) | g (B (r : ℝ≥0) ω) < c}).Nonempty :=
        ⟨⟨s, zero_le, hs⟩, hsc⟩
      obtain ⟨q, hqD, hq⟩ := hDdense.exists_mem_open hopen hne
      exact ⟨q, hqD, hq⟩
    · rintro ⟨q, hqD, hq⟩
      exact ⟨(q : ℝ≥0), q.2.2, hq⟩
  rw [hEq]
  refine MeasurableSet.biUnion hDcount (fun q _ => ?_)
  have hpre : {ω | g (B (q : ℝ≥0) ω) < c}
      = (fun ω (s : Set.Iic t) ↦ B (s : ℝ≥0) ω) ⁻¹'
        {x : Set.Iic t → EuclideanSpace ℝ (Fin d) | g (x ⟨(q : ℝ≥0), q.2.2⟩) < c} := rfl
  rw [hpre]
  exact ⟨_, measurableSet_lt (hg.measurable.comp (measurable_pi_apply _)) measurable_const, rfl⟩

/-- Leaving the open set `U` before time `t` is an event of the past up to `t`, for continuous
paths. -/
theorem measurableSet_comap_exists_not_mem {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hcont : ∀ ω, Continuous fun s ↦ B s ω)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (t : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap (fun ω (s : Set.Iic t) ↦ B (s : ℝ≥0) ω) inferInstance]
      {ω | ∃ s ≤ t, B s ω ∉ U} := by
  by_cases hne : Uᶜ.Nonempty
  · have hEq : {ω | ∃ s ≤ t, B s ω ∉ U}
        = {ω | ∀ n : ℕ, ∃ s ≤ t, Metric.infDist (B s ω) Uᶜ < 1 / ((n : ℝ) + 1)} := by
      ext ω
      simp only [mem_setOf_eq]
      constructor
      · rintro ⟨s, hs, hout⟩ n
        exact ⟨s, hs, by rw [Metric.infDist_zero_of_mem hout]; positivity⟩
      · intro h
        have hgc : ContinuousOn (fun s ↦ Metric.infDist (B s ω) Uᶜ) (Icc (0 : ℝ≥0) t) :=
          ((Metric.continuous_infDist_pt Uᶜ).comp (hcont ω)).continuousOn
        obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
          ⟨0, left_mem_Icc.mpr zero_le⟩ hgc
        have h0 : Metric.infDist (B s₀ ω) Uᶜ = 0 := by
          by_contra hpos
          have hpos' : 0 < Metric.infDist (B s₀ ω) Uᶜ :=
            lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hpos)
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos'
          obtain ⟨s, hs, hlt⟩ := h n
          have hle : Metric.infDist (B s₀ ω) Uᶜ ≤ Metric.infDist (B s ω) Uᶜ :=
            isMinOn_iff.mp hmin s ⟨zero_le, hs⟩
          linarith
        have hmem : B s₀ ω ∈ closure Uᶜ := (Metric.mem_closure_iff_infDist_zero hne).mpr h0
        rw [hU.isClosed_compl.closure_eq] at hmem
        exact ⟨s₀, hs₀.2, hmem⟩
    rw [hEq, setOf_forall]
    exact MeasurableSet.iInter fun n ↦
      measurableSet_comap_exists_lt hcont (Metric.continuous_infDist_pt Uᶜ) _ t
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ x, x ∈ U := fun x => by
      by_contra h
      have h' : x ∈ Uᶜ := h
      rw [hne] at h'
      simp at h'
    have hEq : {ω | ∃ s ≤ t, B s ω ∉ U} = ∅ := by
      ext ω
      simp [hall]
    rw [hEq]
    exact @MeasurableSet.empty Ω (MeasurableSpace.comap (fun ω (s : Set.Iic t) ↦ B (s : ℝ≥0) ω)
      inferInstance)

/-- A path stays in the open set `U` up to time `t` exactly when its exit time from `U` is
greater than `t`. The path is assumed continuous, which makes the infimum defining the exit time
attained. -/
theorem openExitTime_le_iff_not_mapsTo {Ω E : Type*} [TopologicalSpace E] {B : ℝ≥0 → Ω → E}
    {U : Set E} (hU : IsOpen U) {ω : Ω} (hcont : Continuous fun s ↦ B s ω) (t : ℝ≥0) :
    openExitTime B U ω ≤ (t : ℝ≥0∞) ↔ ¬ MapsTo (fun s ↦ B s ω) (Icc (0 : ℝ≥0) t) U := by
  constructor
  · intro hle hsurvive
    have hfinite : openExitTime B U ω ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    have htime : (openExitTime B U ω).toNNReal ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfinite]
      exact hle
    exact openExitTime_not_mem hU hcont hfinite (hsurvive ⟨bot_le, htime⟩)
  · intro hsurvive
    change ¬ ∀ s ∈ Icc (0 : ℝ≥0) t, B s ω ∈ U at hsurvive
    push Not at hsurvive
    obtain ⟨s, hs, hout⟩ := hsurvive
    exact (openExitTime_le_of_not_mem hout).trans (ENNReal.coe_le_coe.mpr hs.2)

/-- **The exit time of an open set is a stopping time** for the natural filtration of a family of
paths with continuous sample paths. -/
theorem isStoppingTime_openExitTime {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun s ↦ B s ω) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) :
    IsStoppingTime (natFiltration B hm) (openExitTime B U) := by
  intro t
  have hset : {ω | openExitTime B U ω ≤ (t : ℝ≥0∞)} = {ω | ∃ s ≤ t, B s ω ∉ U} := by
    ext ω
    rw [mem_setOf_eq, openExitTime_le_iff_not_mapsTo hU (hcont ω) t]
    constructor
    · intro h
      by_contra hno
      apply h
      intro s hs
      by_contra hout
      exact hno ⟨s, hs.2, hout⟩
    · rintro ⟨s, hs, hout⟩ hsurv
      exact hout (hsurv (show s ∈ Icc (0 : ℝ≥0) t from ⟨zero_le, hs⟩))
  change MeasurableSet[natFiltration B hm t] {ω | openExitTime B U ω ≤ (t : ℝ≥0∞)}
  rw [hset, natFiltration_eq_comap B hm t]
  exact measurableSet_comap_exists_not_mem hcont hU t

/-- The exit time of an open set from paths with continuous sample paths is measurable. -/
theorem measurable_openExitTime {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hm : ∀ t, StronglyMeasurable (B t))
    (hcont : ∀ ω, Continuous fun s ↦ B s ω) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) :
    Measurable (openExitTime B U) := by
  have hle : ∀ t : ℝ≥0, MeasurableSet {ω | openExitTime B U ω ≤ (t : ℝ≥0∞)} := fun t ↦
    (natFiltration B hm).le t _ (isStoppingTime_openExitTime hm hcont hU t)
  obtain ⟨S, hSc, hSd, _, hStop⟩ := ENNReal.exists_countable_dense_no_zero_top
  letI : Countable S := hSc.to_subtype
  apply measurable_of_Iio
  intro a
  have heq : openExitTime B U ⁻¹' Iio a =
      ⋃ r : S, ⋃ (_ : r.1 < a), {ω | openExitTime B U ω ≤ r.1} := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_setOf_eq]
    constructor
    · intro hω
      obtain ⟨⟨t, ht⟩, hta⟩ := iInf_lt_iff.mp hω
      obtain ⟨r, hrS, htr, hra⟩ := hSd.exists_between hta
      exact ⟨⟨r, hrS⟩, hra, (openExitTime_le_of_not_mem ht).trans htr.le⟩
    · rintro ⟨r, hra, hle⟩
      exact hle.trans_lt hra
  rw [heq]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro _
  have hrne : r.1 ≠ ∞ := fun h ↦ hStop (h ▸ r.2)
  have h := hle r.1.toNNReal
  rwa [ENNReal.coe_toNNReal hrne] at h

namespace BrownianOpenExitStoppingExample

/-- The constant process `B t ω = x` on an arbitrary measurable space, with the open unit ball. -/
theorem const_isStoppingTime {Ω : Type*} [MeasurableSpace Ω] (x : EuclideanSpace ℝ (Fin 1)) :
    IsStoppingTime (natFiltration (fun _ : ℝ≥0 ↦ fun _ : Ω ↦ x)
        (fun _ ↦ stronglyMeasurable_const))
      (openExitTime (fun _ : ℝ≥0 ↦ fun _ : Ω ↦ x) (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
  isStoppingTime_openExitTime (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    Metric.isOpen_ball

/-- The constant process `B t ω = x` on an arbitrary measurable space, with the open unit ball. -/
theorem const_measurable {Ω : Type*} [MeasurableSpace Ω] (x : EuclideanSpace ℝ (Fin 1)) :
    Measurable (openExitTime (fun _ : ℝ≥0 ↦ fun _ : Ω ↦ x)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
  measurable_openExitTime (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    Metric.isOpen_ball

/-- The moving process `B t ω = t • v` on `Unit`, with `v` in one dimension and the open unit
ball. -/
theorem ramp_isStoppingTime (v : EuclideanSpace ℝ (Fin 1)) :
    IsStoppingTime (natFiltration (fun t : ℝ≥0 ↦ fun _ : Unit ↦ (t : ℝ) • v)
        (fun _ ↦ stronglyMeasurable_const))
      (openExitTime (fun t : ℝ≥0 ↦ fun _ : Unit ↦ (t : ℝ) • v)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
  isStoppingTime_openExitTime (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ (NNReal.continuous_coe.smul continuous_const)) Metric.isOpen_ball

/-- The moving process `B t ω = t • v` on `Unit`, with `v` in one dimension and the open unit
ball. -/
theorem ramp_measurable (v : EuclideanSpace ℝ (Fin 1)) :
    Measurable (openExitTime (fun t : ℝ≥0 ↦ fun _ : Unit ↦ (t : ℝ) • v)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
  measurable_openExitTime (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ (NNReal.continuous_coe.smul continuous_const)) Metric.isOpen_ball

end BrownianOpenExitStoppingExample

end LatticeProb

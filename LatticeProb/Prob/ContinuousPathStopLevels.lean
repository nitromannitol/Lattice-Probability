/-
Stopping continuous paths at their first hit of a high level.

For a level `b` and a continuous path `w : ℝ≥0 → ℝ` the stopped path `stopHit b w` follows `w` up to
the first time it hits `b` (`hitFrom b 0 w`, possibly `⊤`) and is constant afterwards.  For a
fixed path, `hitFrom b 0 w` tends to `⊤` as `b → ∞` (a continuous path is bounded on each compact
time interval), so the stopped paths converge to the path itself, uniformly on compacts.
Consequently the law of a random continuous path is determined by the laws of its stopped
versions at any sequence of levels tending to infinity (`map_eq_of_map_stopHit_eq`).
-/
import Mathlib
import LatticeProb.Prob.UpcrossMeasurable
import LatticeProb.Topology.ContinuousMapBorel

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

/-- The time change of the stopped path: `s` before the first hit of `b`, the hitting time after. -/
def stopHitTime (b : ℝ) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) : ℝ≥0 :=
  if (s : ℝ≥0∞) ≤ hitFrom b 0 w then s else (hitFrom b 0 w).toNNReal

lemma continuous_stopHitTime (b : ℝ) (w : C(ℝ≥0, ℝ)) : Continuous (stopHitTime b w) := by
  by_cases h : hitFrom b 0 w = ⊤
  · have : stopHitTime b w = id := by
      funext s
      simp [stopHitTime, h]
    rw [this]
    exact continuous_id
  · have : stopHitTime b w = fun s => min s (hitFrom b 0 w).toNNReal := by
      funext s
      simp only [stopHitTime]
      split_ifs with hs
      · have h1 : (s : ℝ≥0∞) ≤ ((hitFrom b 0 w).toNNReal : ℝ≥0∞) := by
          rw [ENNReal.coe_toNNReal h]
          exact hs
        exact (min_eq_left (ENNReal.coe_le_coe.1 h1)).symm
      · have h2 : ((hitFrom b 0 w).toNNReal : ℝ≥0∞) < s := by
          rw [ENNReal.coe_toNNReal h]
          exact not_le.1 hs
        exact (min_eq_right (ENNReal.coe_lt_coe.1 h2).le).symm
    rw [this]
    exact continuous_id.min continuous_const

/-- The path `w` stopped at its first hit of the level `b`: `s ↦ w (min s τ)` with
`τ = hitFrom b 0 w` (and `w` itself if `τ = ⊤`). -/
def stopHit (b : ℝ) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun s => w (stopHitTime b w s), w.continuous.comp (continuous_stopHitTime b w)⟩

lemma stopHit_apply (b : ℝ) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) : stopHit b w s = w (stopHitTime b w s) :=
  rfl

/-- Before the first hit of `b` the stopped path agrees with the path. -/
lemma stopHit_apply_of_le {b : ℝ} {w : C(ℝ≥0, ℝ)} {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ hitFrom b 0 w) :
    stopHit b w s = w s := by
  simp only [stopHit_apply, stopHitTime, hs, ↓reduceIte]

/-- Stopping at the first hit of a level is measurable on `C(ℝ≥0, ℝ)`. -/
lemma measurable_stopHit (b : ℝ) : Measurable (stopHit b) := by
  refine ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 fun s => ?_
  have hτ : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom b 0 w :=
    measurable_hitFrom (r := fun _ => 0) measurable_const b
  have hset : MeasurableSet {w : C(ℝ≥0, ℝ) | (s : ℝ≥0∞) ≤ hitFrom b 0 w} :=
    measurableSet_le measurable_const hτ
  have hidx : Measurable fun w : C(ℝ≥0, ℝ) => stopHitTime b w s :=
    Measurable.ite hset measurable_const (ENNReal.measurable_toNNReal.comp hτ)
  exact measurable_eval_comp hidx

/-- For a fixed path and time `T`, the first hit of `b n` is eventually at least `T` when the
levels `b n` tend to infinity. -/
lemma eventually_le_hitFrom {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) (w : C(ℝ≥0, ℝ)) (T : ℝ≥0) :
    ∀ᶠ n in atTop, (T : ℝ≥0∞) ≤ hitFrom (b n) 0 w := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).bddAbove_image
    w.continuous.continuousOn
  filter_upwards [hb.eventually_gt_atTop M] with n hn
  refine le_iInf₂ fun s hs => ?_
  by_contra hlt
  have hsT : s < T := ENNReal.coe_lt_coe.1 (not_le.1 hlt)
  have : w s ≤ M := hM ⟨s, ⟨zero_le, hsT.le⟩, rfl⟩
  linarith [hs.2]

/-- The coercion of a continuous path to a function. -/
private abbrev coeFun' (f : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ := f

/-- **A law on continuous paths is determined by its stopped versions at high levels.**  If two
probability measures on `C(ℝ≥0, ℝ)` have the same image under `stopHit (b n)` for every `n`, where
`b n → ∞`, then they are equal. -/
theorem map_eq_of_map_stopHit_eq (mu nu : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (b : ℕ → ℝ) (hb : Tendsto b atTop atTop)
    (h : ∀ n, mu.map (stopHit (b n)) = nu.map (stopHit (b n))) : mu = nu := by
  have hΦm : Measurable coeFun' :=
    measurable_pi_iff.2 fun s => ContinuousMapBorel.ContinuousMap.measurable_eval s
  have hmeq : (continuousMapMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.comap coeFun' MeasurableSpace.pi := by
    rw [ContinuousMapBorel.ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    rfl
  have hgen : (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.generateFrom
        {A | ∃ T ∈ measurableCylinders (fun _ : ℝ≥0 => ℝ), coeFun' ⁻¹' T = A} := by
    show continuousMapMeasurableSpace = _
    rw [hmeq, ← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
    rfl
  have hpi := (isPiSystem_measurableCylinders (α := fun _ : ℝ≥0 => ℝ)).comap coeFun'
  refine ext_of_generate_finite _ hgen hpi ?_ (by simp)
  rintro _ ⟨T, hT, rfl⟩
  have hAm : MeasurableSet (coeFun' ⁻¹' T) := hΦm (MeasurableSet.of_mem_measurableCylinders hT)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hT
  have hsm : ∀ n, Measurable (stopHit (b n)) := fun n => measurable_stopHit _
  have key : ∀ (ρ : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure ρ],
      Tendsto (fun n => ρ (stopHit (b n) ⁻¹' (coeFun' ⁻¹' cylinder I S))) atTop
        (𝓝 (ρ (coeFun' ⁻¹' cylinder I S))) := by
    intro ρ _
    refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hAm
      (fun n => hsm n hAm) (Eventually.of_forall fun w => ?_)
    filter_upwards [(Filter.eventually_all_finset I).2 fun i _ => eventually_le_hitFrom hb w i]
      with n hn
    have hres : I.restrict (coeFun' (stopHit (b n) w)) = I.restrict (coeFun' w) :=
      funext fun i => stopHit_apply_of_le (hn i i.2)
    simp only [mem_preimage, mem_cylinder, hres]
  have e : ∀ n, mu (stopHit (b n) ⁻¹' (coeFun' ⁻¹' cylinder I S)) =
      nu (stopHit (b n) ⁻¹' (coeFun' ⁻¹' cylinder I S)) := fun n => by
    rw [← Measure.map_apply (hsm n) hAm, ← Measure.map_apply (hsm n) hAm, h n]
  exact tendsto_nhds_unique (key mu) (Tendsto.congr (fun n => (e n).symm) (key nu))

end LatticeProb

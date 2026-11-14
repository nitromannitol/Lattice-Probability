import LatticeProb.Prob.BrownianRestartCanonical
import LatticeProb.Prob.BrownianRestartPath
import LatticeProb.Prob.BrownianFiniteStopping

/-!
# Pasting a stopped path and a restarted path

A continuous path is recovered from its values up to a time `s` and its increments after `s`:
`pastePath s η w` follows `η` up to time `s` and then the increments of `w`, so that the path of a
motion is the paste, at a stopping time `σ`, of the path stopped at `σ` and of the restarted path
at `σ`. The paste is jointly continuous in the time and the two paths, and the stopped path is
measurable for the σ-algebra of the past at `σ`.

A stopping time `ρ` of the canonical filtration of continuous paths, read along the pastes
`w ↦ pastePath s η w` and counted from time `s`, is again a stopping time of the canonical
filtration: the paste up to time `s + t` depends only on `w` up to time `t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- The path that follows `η` up to time `s` and the increments of `w` after time `s`. -/
noncomputable def pastePath {d : ℕ} (s : ℝ≥0) (η w : BrownianPath d) : BrownianPath d :=
  ⟨fun t => η (min t s) + (w (t - s) - w 0), by fun_prop⟩

/-- The path of a motion with continuous paths stopped at the random time `σ`. -/
noncomputable def stopPath {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (σ : Ω → ℝ≥0) (ω : Ω) : BrownianPath d :=
  ⟨fun t => B (min t (σ ω)) ω, (hcont ω).comp (continuous_id.min continuous_const)⟩

section

variable {d : ℕ}

/-- The paste is jointly continuous in the pasting time and the two paths. -/
theorem continuous_pastePath :
    Continuous fun p : ℝ≥0 × BrownianPath d × BrownianPath d => pastePath p.1 p.2.1 p.2.2 := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous fun q : (ℝ≥0 × BrownianPath d × BrownianPath d) × ℝ≥0 =>
    q.1.2.1 (min q.2 q.1.1) + (q.1.2.2 (q.2 - q.1.1) - q.1.2.2 0)
  fun_prop

/-- **A canonical stopping time read along pastes is a canonical stopping time.** For a stopping
time `ρ` of the canonical filtration of continuous paths, a time `s` and a path `η`, the time
`ρ (pastePath s η w) - s` is a stopping time of the canonical filtration in `w`. -/
theorem isStoppingTime_pastePath_sub {ρ : BrownianPath d → ℝ≥0}
    (hρ : IsStoppingTime (brownianNaturalFiltration d) fun w => (ρ w : ℝ≥0∞)) (s : ℝ≥0)
    (η : BrownianPath d) :
    IsStoppingTime (brownianNaturalFiltration d)
      fun w => ((ρ (pastePath s η w) - s : ℝ≥0) : ℝ≥0∞) := by
  intro t
  have hA := hρ (s + t)
  rw [brownianNaturalFiltration_eq_comap] at hA
  obtain ⟨A, hAm, hAeq⟩ := hA
  have hres : Measurable[brownianNaturalFiltration d t]
      fun w : BrownianPath d => fun r : Set.Iic (s + t) => pastePath s η w r := by
    rw [brownianNaturalFiltration_eq_comap]
    let _ : MeasurableSpace (BrownianPath d) := MeasurableSpace.comap
      (fun (ω : BrownianPath d) (v : Set.Iic t) => ω v) inferInstance
    have hev : ∀ u : Set.Iic t, Measurable fun w : BrownianPath d => w u := fun u =>
      (measurable_pi_apply u).comp
        (comap_measurable fun (ω : BrownianPath d) (v : Set.Iic t) => ω v)
    refine measurable_pi_iff.2 fun r => ?_
    have hr : (r : ℝ≥0) - s ≤ t := tsub_le_iff_left.2 r.2
    exact measurable_const.add ((hev ⟨(r : ℝ≥0) - s, hr⟩).sub (hev ⟨0, Set.mem_Iic.2 zero_le⟩))
  have hset : {w : BrownianPath d | ((ρ (pastePath s η w) - s : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
      = (fun w : BrownianPath d => fun r : Set.Iic (s + t) => pastePath s η w r) ⁻¹' A := by
    ext w
    have h := Set.ext_iff.1 hAeq (pastePath s η w)
    exact ENNReal.coe_le_coe.trans (tsub_le_iff_left.trans (ENNReal.coe_le_coe.symm.trans h.symm))
  show MeasurableSet[brownianNaturalFiltration d t]
    {w : BrownianPath d | ((ρ (pastePath s η w) - s : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  rw [hset]
  exact hres hAm

variable {Ω : Type*}

/-- The path of a motion is the paste, at any random time `σ`, of the path stopped at `σ` and of
the path restarted at `σ`. -/
theorem pathMap_eq_pastePath (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (σ : Ω → ℝ≥0) (ω : Ω) :
    pathMap B hcont ω = pastePath (σ ω) (stopPath B hcont σ ω) (restartPath B hcont σ ω) := by
  ext t : 1
  change B t ω = B (min (min t (σ ω)) (σ ω)) ω +
    ((B (σ ω + (t - σ ω)) ω - B (σ ω) ω) - (B (σ ω + 0) ω - B (σ ω) ω))
  rw [add_zero, sub_self, sub_zero, min_assoc, min_self]
  rcases le_total t (σ ω) with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le h, add_zero, sub_self, add_zero]
  · rw [min_eq_right h, add_tsub_cancel_of_le h, add_sub_cancel]

variable [MeasurableSpace Ω]

/-- **The stopped path is settled by the past.** For a stopping time `σ` of the natural filtration
of a motion with continuous paths, the path stopped at `σ` is measurable for the σ-algebra of the
past at `σ`. -/
theorem measurable_stopPath {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (natFiltration B hm) fun ω => (σ ω : ℝ≥0∞)) :
    Measurable[hσ.measurableSpace] (stopPath B hcont σ) := by
  have hprog : IsStronglyProgressive (natFiltration B hm) B :=
    (stronglyAdapted_natFiltration B hm).isStronglyProgressive_of_continuous hcont
  have heval : ∀ s : ℝ≥0, Measurable[hσ.measurableSpace] fun ω => stopPath B hcont σ ω s := by
    intro s
    have hπ : IsStoppingTime (natFiltration B hm) fun ω => min (σ ω : ℝ≥0∞) (s : ℝ≥0∞) :=
      hσ.min_const s
    have h2 : Measurable[hπ.measurableSpace]
        fun ω => B (min (σ ω : ℝ≥0∞) (s : ℝ≥0∞)).untopA ω :=
      measurable_stoppedValue hprog hπ
    have h3 := h2.mono (hπ.measurableSpace_mono hσ fun ω => min_le_left _ _) le_rfl
    have heq : (fun ω => stopPath B hcont σ ω s)
        = fun ω => B (min (σ ω : ℝ≥0∞) (s : ℝ≥0∞)).untopA ω := by
      funext ω
      change B (min s (σ ω)) ω = _
      rw [untopA_eq_toNNReal ((min_le_right _ _).trans_lt ENNReal.coe_lt_top).ne,
        ← ENNReal.coe_min, ENNReal.toNNReal_coe, min_comm]
    rw [heq]
    exact h3
  let _ : MeasurableSpace Ω := hσ.measurableSpace
  exact ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 heval

end

end LatticeProb

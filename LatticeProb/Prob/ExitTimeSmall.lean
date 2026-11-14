/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.PathHitTime

/-!
# Small balls are left quickly, uniformly near the starting point

Let `K : E → Prob C(ℝ≥0, E)` be a weakly continuous family of path laws.  Suppose that `K z`-almost
every path starts at `z` and is not constant on any initial interval.  Then for every `r > 0` and
`η > 0` there is a radius `δ > 0` such that, for all starting points `w` close enough to `z`, the
path law `K w` gives mass `< η` to the event that the path has not left the ball `B (z, δ)` before
time `r`.

* `exists_radius_eventually_measure_pathHit_gt_lt`: the statement, by the portmanteau theorem
  applied to the closed set of paths that stay within distance `1 / (n + 1)` of `z` up to time `r`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- **Uniformly small exit time from small balls.**  If `K` is weakly continuous, `K z`-almost every
path starts at `z` and leaves every neighbourhood of `z` immediately in the sense that it is
nonconstant on each interval `[0, ε]`, then for `r > 0` and `η > 0` there is `δ > 0` with
`K w {x | r < pathHit (ball z δ)ᶜ x} < η` for all `w` near `z`. -/
theorem exists_radius_eventually_measure_pathHit_gt_lt {E : Type*} [MetricSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K) {z : E}
    (hstart : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), x 0 = z)
    (hnc : ∀ ε : ℝ≥0, 0 < ε → ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), ∃ s ≤ ε, x s ≠ x 0)
    {r : ℝ≥0} (hr : 0 < r) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in 𝓝 z,
      (K w : Measure C(ℝ≥0, E)) {x | (r : ℝ≥0∞) < pathHit (Metric.ball z δ)ᶜ x} < η := by
  set F : ℕ → Set C(ℝ≥0, E) :=
    fun n => {x | ∀ s : ℝ≥0, s < r → dist (x s) z ≤ 1 / ((n : ℝ) + 1)} with hF
  have hFclosed : ∀ n, IsClosed (F n) := fun n => by
    have : F n = ⋂ s : ℝ≥0, ⋂ _ : s < r, {x : C(ℝ≥0, E) | dist (x s) z ≤ 1 / ((n : ℝ) + 1)} := by
      ext x; simp [hF]
    rw [this]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_le ((continuous_eval_const s).dist continuous_const) continuous_const
  have hFanti : Antitone F := fun m n hmn x hx s hs =>
    (hx s hs).trans (one_div_le_one_div_of_le (by positivity)
      (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
          linarith))
  have hae : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), x 0 = z ∧ ∃ s ≤ r / 2, x s ≠ x 0 :=
    hstart.and (hnc (r / 2) (half_pos hr))
  have hnull : (K z : Measure C(ℝ≥0, E)) (⋂ n, F n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x hx hcontra
    obtain ⟨h0, s, hs, hne⟩ := hcontra
    apply hne
    have hsr : s < r := lt_of_le_of_lt hs (half_lt_self hr)
    have hd : dist (x s) z ≤ 0 :=
      ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat
        (fun n => (Set.mem_iInter.1 hx n) s hsr)
    rw [h0]
    exact dist_le_zero.1 hd
  have hlim := tendsto_measure_iInter_atTop (μ := (K z : Measure C(ℝ≥0, E))) (s := F)
    (fun n => (hFclosed n).measurableSet.nullMeasurableSet) hFanti ⟨0, measure_ne_top _ _⟩
  rw [hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  have hn' : (K z : Measure C(ℝ≥0, E)) (F n) < η := hn
  have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hK.tendsto z)
    (hFclosed n)
  have hev : ∀ᶠ w in 𝓝 z, (K w : Measure C(ℝ≥0, E)) (F n) < η :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimsup hn')
  refine ⟨1 / ((n : ℝ) + 1), by positivity, hev.mono fun w hw => lt_of_le_of_lt
    (measure_mono ?_) hw⟩
  intro x hx s hs
  by_contra hlt
  have hlt' := not_le.1 hlt
  have hmem : x s ∈ (Metric.ball z (1 / ((n : ℝ) + 1)))ᶜ := fun h => by
    rw [Metric.mem_ball] at h; linarith
  have hle := pathHit_le_of_mem hmem
  exact absurd (ENNReal.coe_lt_coe.1 (lt_of_lt_of_le hx hle)) (not_lt.2 hs.le)

end LatticeProb

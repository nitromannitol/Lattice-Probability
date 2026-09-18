/- Adapted from nitromannitol/Parking-Sharpness, Apache-2.0. -/
/-
Lyapunov's moment monotonicity for a nonnegative random variable, via Jensen's inequality at
the concave map `t ↦ t^{s/p}`: if `Y ≥ 0` has an integrable `p`-th moment bounded by `M`, then
for every exponent `s` with `0 < s ≤ p`, `Y` also has an integrable `s`-th moment, bounded by
`M^{s/p}`. This is the step that turns a Kolmogorov-Chentsov `p`-th
moment bound (`p` large, needed for the chaining argument) into the `L²` bound a variance-type
estimate needs.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable section

namespace LatticeProb.Lyapunov

/-- **Lyapunov's moment monotonicity via Jensen's inequality**: if a nonnegative,
`AEStronglyMeasurable` `Y` has an integrable `p`-th moment bounded by `M`, then for any exponent
`s` with `0 < s ≤ p`, `Y` also has an integrable `s`-th moment, bounded by `M^{s/p}`. -/
theorem integrable_rpow_and_integral_rpow_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hYnn : ∀ ω, 0 ≤ Y ω) (hYaesm : AEStronglyMeasurable Y μ)
    {s p : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hYpint : Integrable (fun ω => (Y ω) ^ p) μ) {M : ℝ}
    (hYpbound : ∫ ω, (Y ω) ^ p ∂μ ≤ M) :
    Integrable (fun ω => (Y ω) ^ s) μ ∧ ∫ ω, (Y ω) ^ s ∂μ ≤ M ^ (s / p) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hs hsp
  have hr2 : (0 : ℝ) ≤ s / p := by positivity
  have hr1 : s / p ≤ 1 := by rw [div_le_one hp0]; exact hsp
  have hg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun y : ℝ => y ^ (s / p)) := Real.concaveOn_rpow hr2 hr1
  have hgc : ContinuousOn (fun y : ℝ => y ^ (s / p)) (Set.Ici (0 : ℝ)) :=
    continuousOn_id.rpow_const (fun x _ => Or.inr hr2)
  have hseq : ∀ ω, ((Y ω) ^ p) ^ (s / p) = (Y ω) ^ s := by
    intro ω
    rw [← Real.rpow_mul (hYnn ω)]
    congr 1
    field_simp
  have hYpmem : ∀ᵐ ω ∂μ, (Y ω) ^ p ∈ Set.Ici (0 : ℝ) := by
    filter_upwards with ω; exact Real.rpow_nonneg (hYnn ω) p
  have hYs_le_aux : ∀ ω, (Y ω) ^ s ≤ 1 + (Y ω) ^ p := by
    intro ω
    rcases le_total (Y ω) (1 : ℝ) with h | h
    · have h1 : (Y ω) ^ s ≤ 1 := Real.rpow_le_one (hYnn ω) h hs.le
      have h2 : (0 : ℝ) ≤ (Y ω) ^ p := Real.rpow_nonneg (hYnn ω) p
      linarith
    · have h2' : (Y ω) ^ s ≤ (Y ω) ^ p := Real.rpow_le_rpow_of_exponent_le h hsp
      have h3 : (0 : ℝ) ≤ (Y ω) ^ p := Real.rpow_nonneg (hYnn ω) p
      linarith
  have hYs_meas : AEStronglyMeasurable (fun ω => (Y ω) ^ s) μ :=
    (Real.continuous_rpow_const hs.le).comp_aestronglyMeasurable hYaesm
  have hYs_int : Integrable (fun ω => (Y ω) ^ s) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hYpint) hYs_meas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hYnn ω) _)]
    exact hYs_le_aux ω
  refine ⟨hYs_int, ?_⟩
  have hgi : Integrable ((fun y : ℝ => y ^ (s / p)) ∘ (fun ω => (Y ω) ^ p)) μ := by
    have heq : ((fun y : ℝ => y ^ (s / p)) ∘ (fun ω => (Y ω) ^ p)) = fun ω => (Y ω) ^ s := by
      funext ω; exact hseq ω
    rw [heq]; exact hYs_int
  have hjensen := hg.le_map_integral hgc isClosed_Ici hYpmem hYpint hgi
  have heq2 : (∫ ω, ((Y ω) ^ p) ^ (s / p) ∂μ) = ∫ ω, (Y ω) ^ s ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    exact hseq ω
  rw [heq2] at hjensen
  refine hjensen.trans ?_
  have hYpnn : (0 : ℝ) ≤ ∫ ω, (Y ω) ^ p ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (hYnn ω) p
  exact Real.rpow_le_rpow hYpnn hYpbound hr2

end LatticeProb.Lyapunov

end

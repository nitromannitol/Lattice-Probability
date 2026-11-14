/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianLandingRange at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianScaledLanding
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousPathRange

/-! A positive probability of scaled landing with a deterministic bound on
the entire preceding path. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A unit-time bound on the scaled path controls every original time up to
`r²`, with the original spatial bound multiplied by `r`. -/
lemma pathRangeEvent_of_scaledBrownianPath {d : ℕ} {r : ℝ≥0} (hr : 0 < r)
    {L : ℝ} {ω : BrownianPath d}
    (hω : scaledBrownianPath r ω ∈ pathRangeEvent 1 L) :
    ω ∈ pathRangeEvent (r ^ 2) (L * (r : ℝ)) := by
  have hrR : 0 < (r : ℝ) := hr
  intro t ht
  let s : ℝ≥0 := t / r ^ 2
  have hs : s ∈ Icc (0 : ℝ≥0) 1 := by
    refine ⟨bot_le, ?_⟩
    exact (div_le_iff₀ (pow_pos hr 2)).mpr (by simpa using ht.2)
  have htime : r ^ 2 * s = t := mul_div_cancel₀ t (pow_ne_zero 2 hr.ne')
  have hbound := hω s hs
  simp only [scaledBrownianPath_apply, htime, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos hrR, ← div_eq_inv_mul] at hbound
  exact (div_le_iff₀ hrR).mp hbound

/-- Uniformly in positive scale and in starting points and centers separated
by at most twice that scale, there is positive probability of landing in the
target ball while keeping the whole preceding path within a fixed multiple
of the scale. Both constants are chosen before the scale and the points. -/
theorem standardBrownianLaw_uniform_scaled_landing_and_range_probability {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ p L : ℝ, 0 < p ∧ p ≤ 1 ∧ 1 ≤ L ∧ ∀ r : ℝ≥0, 0 < r → ∀ x c : Euc d,
      dist c x ≤ 2 * (r : ℝ) →
      ENNReal.ofReal (p / 2) ≤ μ {ω : BrownianPath d |
        x + ω (r ^ 2) ∈ ball c (κ * (r : ℝ)) ∧
          ω ∈ pathRangeEvent (r ^ 2) (L * (r : ℝ))} := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨p, hp, hp1, hlanding⟩ := standardBrownianLaw_uniform_scaled_landing_probability hμ hκ
  obtain ⟨L, hL, htail⟩ := exists_pathRangeEvent_compl_lt μ 1 (half_pos hp)
  refine ⟨p, L, hp, hp1, hL, ?_⟩
  intro r hr x c hc
  let A : Set (BrownianPath d) := {ω | x + ω (r ^ 2) ∈ ball c (κ * (r : ℝ))}
  let B : Set (BrownianPath d) := pathRangeEvent (r ^ 2) (L * (r : ℝ))
  have hsub : Bᶜ ⊆ scaledBrownianPath r ⁻¹' (pathRangeEvent 1 L)ᶜ := by
    intro ω hbad hgood
    exact hbad (pathRangeEvent_of_scaledBrownianPath hr hgood)
  have hbad : μ Bᶜ < ENNReal.ofReal (p / 2) := by
    calc
      μ Bᶜ ≤ μ (scaledBrownianPath r ⁻¹' (pathRangeEvent 1 L)ᶜ) := measure_mono hsub
      _ = (μ.map (scaledBrownianPath r)) (pathRangeEvent 1 L)ᶜ :=
        (Measure.map_apply (measurable_scaledBrownianPath r)
          (isClosed_pathRangeEvent (d := d) 1 L).measurableSet.compl).symm
      _ = μ (pathRangeEvent 1 L)ᶜ := by rw [standardBrownianLaw_map_scale hμ hr]
      _ < ENNReal.ofReal (p / 2) := htail
  have hcover : μ A ≤ μ (A ∩ B) + μ Bᶜ :=
    (measure_le_inter_add_sdiff μ A B).trans
      (add_le_add le_rfl (measure_mono (fun _ h => h.2)))
  have hhalf : ENNReal.ofReal (p / 2) + ENNReal.ofReal (p / 2) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_add (half_pos hp).le (half_pos hp).le]
    congr 1
    exact add_halves p
  change ENNReal.ofReal (p / 2) ≤ μ (A ∩ B)
  by_contra hnot
  have hsmall : μ (A ∩ B) < ENNReal.ofReal (p / 2) := lt_of_not_ge hnot
  have hsum := (ENNReal.add_lt_add hsmall hbad).trans_eq hhalf
  exact (not_lt_of_ge ((hlanding r hr x c hc).trans hcover)) hsum

end BouRabeeGwynne

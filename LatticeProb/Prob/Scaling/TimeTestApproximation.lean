/- Uniform approximation of a compactly supported time derivative by forward differences.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.TimeTest
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology
noncomputable section
namespace LatticeProb.Scaling.TimeTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A single time-step modulus works at every time and spatial point. -/
theorem exists_forward_difference_modulus {ψ : ℝ × E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ), 0 < h → h < δ → ∀ (s : ℝ) (x : E),
      |(ψ (s + h, x) - ψ (s, x)) / h - timeDeriv ψ (s, x)| < ε := by
  have huc : UniformContinuous (timeDeriv ψ) :=
    (hasCompactSupport_timeDeriv (hψ.differentiable (by simp)) hc).uniformContinuous_of_continuous
      (contDiff_timeDeriv hψ).continuous
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨δ, hδ, fun h hh hd s x => ?_⟩
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ψ (t, x)) :=
    hψ.comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope (fun t : ℝ => ψ (t, x))
    (by linarith : s < s + h) hs.continuous.continuousOn
    (hs.differentiable (by simp)).differentiableOn
  have hdist : dist (c, x) (s, x) < δ := by
    simp only [Prod.dist_eq, dist_self, Real.dist_eq]
    rw [abs_of_pos (sub_pos.mpr hc.1)]
    exact max_lt (by linarith [hc.2]) hδ
  have hm' := hm hdist
  simpa only [timeDeriv, Real.dist_eq, heq, add_sub_cancel_left] using hm'

end LatticeProb.Scaling.TimeTest

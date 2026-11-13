import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HasBoundedConvexity
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.DirichletEnergy
import LatticeProb.Analysis.AnnulusShortPath
import LatticeProb.Analysis.AnnulusThickeningVolume
import LatticeProb.Analysis.AnnulusLogRegularity
import LatticeProb.Analysis.AnnulusLogEnergy

/-!
# The logarithmic test function of an annulus is in the energy class of the mated-CRT energy bound

The quantitative Dirichlet energy bound for mated-CRT maps (Gwynne-Miller-Sheffield, *Harmonic functions on mated-CRT
maps*, Theorem 3.2) applies to pairs `(D, f)` with `D ⊆ B_ρ(0)` open, `area(B_δ(∂D)) ≤ C δ` for `δ ∈ (0, 1)`,
`C`-bounded convexity of `D`, and `f` differentiable on `D` with `‖f‖_∞`, `‖∇f‖_∞` and the Lipschitz constant of `∇f`
at most `K`. Berestycki-Gwynne (*Random walks on mated-CRT maps and Liouville Brownian motion*, Lemma 4.3) apply it to
the annulus `D = B_r(c) \ B̄_s(c)` and the radial function `f = log(r/|· - c|) / log(r/s)`, whose Dirichlet energy is
`2π / log(r/s)`.

This file collects these facts in the form of the hypotheses of that theorem:
* `isOpen_annulus`, `hasBoundedConvexity_annulus` (constant `C ≥ 1 + 2π`); the boundary-area hypothesis (constant
  `C ≥ 16π`, for `0 ≤ s ≤ r ≤ 1`) is `volume_thickening_frontier_annulus_le_mul`, and
  `one_add_two_mul_pi_le_sixteen_mul_pi` lets one constant `C ≥ 16π` serve both;
* `annulus_log_regular` (the five regularity hypotheses with constant `K`, given `1 ≤ K`, `(s log(r/s))⁻¹ ≤ K` and
  `(s² log(r/s))⁻¹ ≤ K`), and `dirichletEnergy_annulus_log` (the energy `2π / log(r/s)`).
-/

noncomputable section

namespace LatticeProb

open Set Metric MeasureTheory

/-- The open annulus `B_r(c) \ B̄_s(c)` is open. -/
theorem isOpen_annulus (c : ℂ) (s r : ℝ) : IsOpen (ball c r \ closedBall c s) :=
  isOpen_ball.sdiff isClosed_closedBall

/-- The open annulus `B_r(c) \ B̄_s(c)` (`0 ≤ s`) has `C`-bounded convexity for every `C ≥ 1 + 2π`: any two of its points
are joined inside it by a path of length at most `C` times their distance. -/
theorem hasBoundedConvexity_annulus (c : ℂ) {s r C : ℝ} (hs : 0 ≤ s) (hC : 1 + 2 * Real.pi ≤ C) :
    MatedCRTHarmonic.HasBoundedConvexity C (ball c r \ closedBall c s) := by
  intro z hz w hw
  have hz' : z ∈ {v : ℂ | s < dist v c ∧ dist v c < r} :=
    ⟨not_le.1 (mt mem_closedBall.2 hz.2), mem_ball.1 hz.1⟩
  have hw' : w ∈ {v : ℂ | s < dist v c ∧ dist v c < r} :=
    ⟨not_le.1 (mt mem_closedBall.2 hw.2), mem_ball.1 hw.1⟩
  obtain ⟨p, hp, hp0, hp1, hpm, hpv⟩ := exists_path_eVariationOn_le_annulus c hs hz' hw'
  refine ⟨p, hp, hp0, hp1, fun t ht => ?_, hpv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · have h := hpm ht
    exact ⟨mem_ball.2 h.2, mt mem_closedBall.1 (not_le.2 h.1)⟩
  · exact mul_le_mul_of_nonneg_right hC dist_nonneg

/-- `16π ≥ 1 + 2π`: one constant `C ≥ 16π` serves both the boundary-area and the bounded-convexity hypotheses. -/
theorem one_add_two_mul_pi_le_sixteen_mul_pi : 1 + 2 * Real.pi ≤ 16 * Real.pi := by
  linarith [Real.pi_gt_three]

/-- Regularity of the logarithmic test function `f = log(r/|· - c|) / log(r/s)` on the annulus `B_r(c) \ B̄_s(c)`
(`0 < s < r`) with a constant `K ≥ 1` such that `(s log(r/s))⁻¹ ≤ K` and `(s² log(r/s))⁻¹ ≤ K`: `f` is differentiable,
`∇f` is `K`-Lipschitz, `|f| ≤ K`, `|∇f| ≤ K` on the annulus, and `f` is continuous on its closure. -/
theorem annulus_log_regular (c : ℂ) {s r K : ℝ} (hs : 0 < s) (hsr : s < r) (hK : 1 ≤ K)
    (hK1 : (s * Real.log (r / s))⁻¹ ≤ K) (hK2 : (s ^ 2 * Real.log (r / s))⁻¹ ≤ K) :
    DifferentiableOn ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) (ball c r \ closedBall c s) ∧
      (∀ z ∈ ball c r \ closedBall c s, ∀ w ∈ ball c r \ closedBall c s,
        ‖fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / Real.log (r / s)) z -
          fderiv ℝ (fun x : ℂ => Real.log (r / ‖x - c‖) / Real.log (r / s)) w‖ ≤ K * dist z w) ∧
      (∀ z ∈ ball c r \ closedBall c s, |Real.log (r / ‖z - c‖) / Real.log (r / s)| ≤ K) ∧
      (∀ z ∈ ball c r \ closedBall c s,
        ‖fderiv ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) z‖ ≤ K) ∧
      ContinuousOn (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s))
        (closure (ball c r \ closedBall c s)) :=
  annulus_log_div_norm_sub_regular c hs hsr hK hK1 hK2

/-- The Dirichlet energy of the logarithmic test function on the annulus `B_r(c) \ B̄_s(c)` (`0 < s < r`) is
`2π / log(r/s)`. -/
theorem dirichletEnergy_annulus_log (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r)
    (hD : IsOpen (ball c r \ closedBall c s))
    (hf : DifferentiableOn ℝ (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s)) (ball c r \ closedBall c s)) :
    MatedCRTHarmonic.dirichletEnergy (fun w : ℂ => Real.log (r / ‖w - c‖) / Real.log (r / s))
        (ball c r \ closedBall c s) hD hf = ENNReal.ofReal (2 * Real.pi / Real.log (r / s)) :=
  lintegral_annulus_norm_fderiv_log_div_sq c hs hsr

end LatticeProb

end

import LatticeProb.Analysis.JensenWeak
import LatticeProb.Analysis.WeakLaplaceMollify
import LatticeProb.Analysis.WeakHessianW2pMeas
import LatticeProb.Analysis.MorreyOscillation
import LatticeProb.Analysis.HessianExpansion
import LatticeProb.Analysis.PeanoOfW2pLimit

/-!
# Proposition 2.4 of Pegden-Smart in Peano form

Let `E` be a finite-dimensional real inner product space of dimension `d` with an additive Haar
measure `μ`. A continuous weak solution `u` of `Δ u = s` in the unit ball, with `s` essentially
bounded there, has a second-order Taylor expansion with Peano remainder and self-adjoint second
derivative at almost every point of the unit ball.

The result is conditional on the interior `L^p` Hessian bound for smooth functions,
`‖D² w‖_{L^p(B_{r/2}(a))} ≤ C (‖Δ w‖_{L^p(B_r(a))} + ‖w‖_{L^∞(B_r(a))})`, which is taken as a
hypothesis. Only the exponent `p = d + 2` is used, so that `2 ≤ p`, `d < p` and `p < ∞`.

The proof mollifies `u` and `s` (`weakLaplace_mollify`), obtains a measurable `L^p` limit `G` of the
Hessians of the mollifications (`weakHessianW2p_meas`), and applies the Peano expansion of
`W^{2,p}` limits (`peanoOfW2pLimit_of_hessianExpansion`), whose Hessian expansion hypothesis follows
from Morrey's oscillation estimate (`hessianExpansion_of_morrey_gradientLimit`,
`morrey_oscillation`).

## Main results

* `LatticeProb.PegdenSmart.pegdenSmartProp24Peano_of_hessianLpAt`: the conclusion, given the
  interior Hessian bound at the exponent `d + 2`.
* `LatticeProb.PegdenSmart.pegdenSmartProp24Peano`: the conclusion, given the interior Hessian
  bound for every exponent `2 ≤ p < ∞`.
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal
open Laplacian

namespace LatticeProb.PegdenSmart

/-- **Proposition 2.4 of Pegden-Smart, Peano form**, conditional on the interior `L^p` Hessian bound
at the single exponent `p = d + 2`, where `d` is the dimension of `E`. A continuous weak solution
`u` of `Δ u = s` in the unit ball, with `s` essentially bounded there, has a second-order Taylor
expansion with Peano remainder and self-adjoint second derivative at almost every point of the unit
ball. -/
theorem pegdenSmartProp24Peano_of_hessianLpAt
    (hQ2 : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : E → ℝ, ContDiffOn ℝ ∞ w (ball a r) →
        eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) ((Module.finrank ℝ E : ℝ≥0∞) + 2)
            (μ.restrict (ball a (r / 2))) ≤
          C * (eLpNorm (Δ w) ((Module.finrank ℝ E : ℝ≥0∞) + 2) (μ.restrict (ball a r)) +
            eLpNorm w ⊤ (μ.restrict (ball a r)))) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure],
      ∀ s u : E → ℝ, MemLp s ⊤ (μ.restrict (ball (0 : E) 1)) → ContinuousOn u (ball 0 1) →
        IsWeakSolutionLaplace μ (ball 0 1) u s →
          ∀ᵐ x ∂(μ.restrict (ball (0 : E) 1)), PeanoAt u x := by
  intro E _ _ _ _ _ μ _ s u hs hu hweak
  obtain ⟨M, hM0, hM⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ x ∂(μ.restrict (ball (0 : E) 1)), |s x| ≤ K := by
    refine ⟨(eLpNormEssSup s (μ.restrict (ball (0 : E) 1))).toReal, ENNReal.toReal_nonneg, ?_⟩
    have hfin : eLpNormEssSup s (μ.restrict (ball (0 : E) 1)) < ⊤ := by
      have := hs.eLpNorm_lt_top
      rw [eLpNorm_exponent_top] at this
      · exact this
      · exact hs.aestronglyMeasurable
    filter_upwards [ae_le_eLpNormEssSup (f := s) (μ := μ.restrict (ball (0 : E) 1))] with x hx
    have h := ENNReal.toReal_mono hfin.ne hx
    rwa [toReal_enorm, Real.norm_eq_abs] at h
  obtain ⟨ε, ρ, hε0, hε, hρ⟩ := exists_mollifier_sequence (E := E) μ
  obtain ⟨hsmooth, hΔ, -, hunif, hsε⟩ := weakLaplace_mollify μ (ball (0 : E) 1) u s M ε ρ
    isOpen_ball hu hM0 hM hs.aestronglyMeasurable hweak hε0 hε hρ
  set p : ℝ≥0∞ := (Module.finrank ℝ E : ℝ≥0∞) + 2 with hp
  have hpt : p ≠ ⊤ := by simp [hp]
  have hp2 : 2 ≤ p := le_add_self
  have hpd : (Module.finrank ℝ E : ℝ≥0∞) < p :=
    ENNReal.lt_add_right (by simp) (by norm_num)
  obtain ⟨G, hGm, hG, -⟩ := weakHessianW2p_meas E μ p (one_le_two.trans hp2) hpt (hQ2 E μ)
    (ball 0 1) u s
    (fun n => convolution ((ball (0 : E) 1).indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ)
    (fun n => convolution ((ball (0 : E) 1).indicator s) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ) ε
    isOpen_ball hε0 hε hsmooth hΔ hunif (hsε p (one_le_two.trans hp2) hpt)
  exact peanoOfW2pLimit_of_hessianExpansion
    (hessianExpansion_of_morrey_gradientLimit morrey_oscillation) E μ p hpd hpt (ball 0 1) u _ ε G
    isOpen_ball hε0 hε hsmooth hunif hGm hG

/-- **Proposition 2.4 of Pegden-Smart, Peano form**, conditional on the interior `L^p` Hessian bound
for every exponent `2 ≤ p < ∞`. A continuous weak solution `u` of `Δ u = s` in the unit ball, with
`s` essentially bounded there, has a second-order Taylor expansion with Peano remainder and
self-adjoint second derivative at almost every point of the unit ball. -/
theorem pegdenSmartProp24Peano :
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞),
      2 ≤ p → p ≠ ⊤ →
      ∀ (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : E → ℝ, ContDiffOn ℝ ∞ w (ball a r) →
        eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
          C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r)))) →
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure],
      ∀ s u : E → ℝ, MemLp s ⊤ (μ.restrict (ball (0 : E) 1)) → ContinuousOn u (ball 0 1) →
        IsWeakSolutionLaplace μ (ball 0 1) u s →
          ∀ᵐ x ∂(μ.restrict (ball (0 : E) 1)), PeanoAt u x := fun hQ2 =>
  pegdenSmartProp24Peano_of_hessianLpAt fun E _ _ _ _ _ μ _ =>
    hQ2 E μ _ le_add_self (by simp)

end LatticeProb.PegdenSmart

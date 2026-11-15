import LatticeProb.Analysis.PegdenSmartProp24Peano
import LatticeProb.Analysis.PeanoCoefficientOfW2pLimit
import LatticeProb.Analysis.W2pApproxTrace

/-!
# Proposition 2.4 of Pegden-Smart in printed form

Let `E` be a finite-dimensional real inner product space of dimension `d` with an additive Haar
measure `μ`. A continuous weak solution `u` of `Δ u = s` in the unit ball, with `s` essentially
bounded there, has at almost every point `x` of the unit ball a second-order Taylor expansion
`u y = u x + q (y - x) + 1 / 2 * H (y - x) (y - x) + o (‖y - x‖ ^ 2)` with a symmetric second
derivative `H` whose trace is `s x`, that is, `Δ u = s` almost everywhere.

The result is conditional on the interior `L^p` Hessian bound for smooth functions,
`‖D² w‖_{L^p(B_{r/2}(a))} ≤ C (‖Δ w‖_{L^p(B_r(a))} + ‖w‖_{L^∞(B_r(a))})`, which is taken as a
hypothesis. Only the exponent `p = d + 2` is used.

The proof mollifies `u` and `s` (`weakLaplace_mollify`), obtains the measurable `L^p` limit `G` of
the Hessians of the mollifications (`weakHessianW2p_meas`), and records the approximation as an
`IsW2pApprox`. The coefficient of the Peano expansion is then `G x`
(`peanoCoefficient_of_w2pApprox`), and its trace is `s x` almost everywhere
(`ae_trace_eq_of_w2pApprox`).

## Main results

* `LatticeProb.PegdenSmart.pegdenSmartProp24Printed_of_hessianLpAt`: the conclusion, given the
  interior Hessian bound at the exponent `d + 2`.
* `LatticeProb.PegdenSmart.pegdenSmartProp24Printed`: the conclusion, given the interior Hessian
  bound for every exponent `2 ≤ p < ∞`.
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal
open Laplacian

namespace LatticeProb.PegdenSmart

/-- **Proposition 2.4 of Pegden-Smart, printed form**, conditional on the interior `L^p` Hessian
bound at the single exponent `p = d + 2`, where `d` is the dimension of `E`. A continuous weak
solution `u` of `Δ u = s` in the unit ball, with `s` essentially bounded there, has at almost every
point `x` of the unit ball a second-order Taylor expansion with Peano remainder whose symmetric
second derivative `H` has trace `s x`, so that `Δ u = s` almost everywhere. -/
theorem pegdenSmartProp24Printed_of_hessianLpAt
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
          ∀ᵐ x ∂(μ.restrict (ball (0 : E) 1)), ∃ (q : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ),
            (∀ v w, H v w = H w v) ∧
            (fun y => u y - u x - q (y - x) - 1 / 2 * H (y - x) (y - x)) =o[𝓝 x]
              (fun y => ‖y - x‖ ^ 2) ∧
            ∑ i, H (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) = s x := by
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
  have hp1 : 1 ≤ p := one_le_two.trans hp2
  obtain ⟨G, hGm, hG, -⟩ := weakHessianW2p_meas E μ p hp1 hpt (hQ2 E μ)
    (ball 0 1) u s
    (fun n => convolution ((ball (0 : E) 1).indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ)
    (fun n => convolution ((ball (0 : E) 1).indicator s) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ) ε
    isOpen_ball hε0 hε hsmooth hΔ hunif (hsε p hp1 hpt)
  have hA : IsW2pApprox μ p (ball (0 : E) 1) u
      (fun n => convolution ((ball (0 : E) 1).indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) μ)
      ε G :=
    ⟨isOpen_ball, hε0, hε, hsmooth, hunif, hGm, hG⟩
  have hpeano := peanoCoefficient_of_w2pApprox E μ p hpd hpt _ u _ ε G hA
  have htrace := ae_trace_eq_of_w2pApprox μ hp1 hA hΔ hs.aestronglyMeasurable
    (hsε p hp1 hpt)
  filter_upwards [hpeano, htrace] with x hx hx'
  obtain ⟨hsymm, q, hq⟩ := hx
  exact ⟨q, G x, hsymm, hq, hx'⟩

/-- **Proposition 2.4 of Pegden-Smart, printed form**, conditional on the interior `L^p` Hessian
bound for every exponent `2 ≤ p < ∞`. A continuous weak solution `u` of `Δ u = s` in the unit ball,
with `s` essentially bounded there, has at almost every point `x` of the unit ball a second-order
Taylor expansion with Peano remainder whose symmetric second derivative `H` has trace `s x`, so
that `Δ u = s` almost everywhere. -/
theorem pegdenSmartProp24Printed :
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
          ∀ᵐ x ∂(μ.restrict (ball (0 : E) 1)), ∃ (q : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ),
            (∀ v w, H v w = H w v) ∧
            (fun y => u y - u x - q (y - x) - 1 / 2 * H (y - x) (y - x)) =o[𝓝 x]
              (fun y => ‖y - x‖ ^ 2) ∧
            ∑ i, H (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) = s x := fun hQ2 =>
  pegdenSmartProp24Printed_of_hessianLpAt fun E _ _ _ _ _ μ _ =>
    hQ2 E μ _ le_add_self (by simp)

end LatticeProb.PegdenSmart

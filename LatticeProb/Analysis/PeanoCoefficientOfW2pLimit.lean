import LatticeProb.Analysis.MorreyOscillation
import LatticeProb.Analysis.HessianExpansion
import LatticeProb.Analysis.PeanoOfW2pLimit

/-! # Peano coefficients of `W^{2,p}` limits

The limiting Hessian is the symmetric coefficient in the almost-everywhere second-order Peano
expansion of a `W^{2,p}` limit.
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal

namespace LatticeProb.PegdenSmart

/-- A Hessian expansion gives a Peano expansion with the limiting Hessian as coefficient. -/
theorem peanoCoefficient_of_hessianExpansion
    (h8 : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞), (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∃ C : ℝ≥0, ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ)
        (G : E → E →L[ℝ] E →L[ℝ] ℝ), IsW2pApprox μ p U u uε ε G → ∀ V : E → E →L[ℝ] ℝ,
        (∀ K : Set E, IsCompact K → K ⊆ U →
          TendstoUniformlyOn (fun n => fderiv ℝ (uε n)) V atTop K) →
        (∀ (x : E) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ y ∈ ball x r,
          ‖V y - V x - G x (y - x)‖ₑ ≤
            (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
              eLpNorm (fun w => G w - G x) p (μ.restrict (ball x r))) ∧
        (∀ x ∈ U, Tendsto
          (fun r => (∫⁻ y in closedBall x r, ‖G y - G x‖ₑ ^ p.toReal ∂μ) / μ (closedBall x r))
          (𝓝[>] 0) (𝓝 0) → HasFDerivAt V (G x) x)) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞),
      (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ),
      IsW2pApprox μ p U u uε ε G →
      ∀ᵐ x ∂(μ.restrict U), (∀ v w, G x v w = G x w v) ∧ ∃ q : E →L[ℝ] ℝ,
        (fun y => u y - u x - q (y - x) - 1 / 2 * G x (y - x) (y - x)) =o[𝓝 x]
          (fun y => ‖y - x‖ ^ 2) := by
  intro E _ _ _ _ _ μ _ p hdp hpt U u uε ε G hA
  rcases subsingleton_or_nontrivial E with hE | hE
  · filter_upwards with x
    refine ⟨fun v w => by rw [Subsingleton.elim v w], 0, ?_⟩
    refine (isLittleO_zero _ _).congr_left fun y => ?_
    rw [Subsingleton.elim y x]
    simp
  have ⟨hU, hε, hε0, hsm, hconv, hG, hL⟩ := hA
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_trans (by exact_mod_cast Module.finrank_pos) hdp.le
  obtain ⟨V, -, hVconv, hVd⟩ := gradientLimit_of_uniformCauchy
    (gradientUniformCauchy_of_supBound gradient_sup_bound) E μ p hdp hpt U u uε ε G hA
  obtain ⟨K, hK⟩ := h8 E μ p hdp hpt
  have hdiff := (hK U u uε ε G hA V hVconv).2
  have hleb := lp_lebesgue_points E μ p.toReal (by simpa using ENNReal.toReal_mono hpt hp1)
    (E →L[ℝ] E →L[ℝ] ℝ) U G hU hG fun C hC hCU =>
      lintegral_enorm_rpow_lt_top_of_isW2pApprox hp1 hpt hA hC hCU
  filter_upwards [hleb, ae_restrict_mem hU.measurableSet] with x hx hxU
  have h := peano_of_fderiv E u V (G x) x (eventually_of_mem (hU.mem_nhds hxU) hVd)
    (hdiff x hxU hx)
  exact ⟨h.1, V x, h.2.1⟩

/-- The limiting Hessian is the coefficient of the Peano expansion almost everywhere. -/
theorem peanoCoefficient_of_w2pApprox :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞),
      (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ),
      IsW2pApprox μ p U u uε ε G →
      ∀ᵐ x ∂(μ.restrict U), (∀ v w, G x v w = G x w v) ∧ ∃ q : E →L[ℝ] ℝ,
        (fun y => u y - u x - q (y - x) - 1 / 2 * G x (y - x) (y - x)) =o[𝓝 x]
          (fun y => ‖y - x‖ ^ 2) :=
  peanoCoefficient_of_hessianExpansion
    (hessianExpansion_of_morrey_gradientLimit morrey_oscillation)

end LatticeProb.PegdenSmart

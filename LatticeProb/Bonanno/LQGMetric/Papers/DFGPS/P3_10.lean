/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10Neg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
Proposition 3.10 (`prop-internal-moment`, T:1757–1762). Its proof (T:1871–1916) has two parts:

* `p < 0`: the lower bound of Proposition 3.1 (T:1872), `prop3_10_nonpos`;
* `p > 0`: Steps 1–3 (T:1875–1912) prove the tail bound
  `P[𝔠_𝕣⁻¹ e^{-ξh_𝕣(0)} sup_{z,w∈𝕣𝕊} D_h(z,w;𝕣𝕊) > C̃] ≤ C̃^{-4d_γ/γ² + o_{C̃}(1)}` uniformly in
  `𝕣` (display T:1909–1912), which is `DiamTailRS` below; the moment bound then follows by
  integrating the tail (T:1914–1915), `lintegral_rpow_le_of_tail`.

`DiamTailRS` is the paper's displayed estimate T:1909–1912 (with the `o_{C̃}(1)` written as: for
every `a < 4d_γ/γ²` there are `C, t₀` with `P[X > t] ≤ C t^{-a}` for `t ≥ t₀`), stated for every
realization `(Ω, P, h)` with constants independent of it and of `𝕣`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-- **DFGPS, proof of Prop 3.10, Steps 1–3** (display T:1909–1912): the upper tail of the
normalized internal diameter of `𝕣𝕊`, polynomial of every order `a < 4d_γ/γ²`, uniformly in `𝕣`. -/
def DiamTailRS : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ a : ℝ, a < 4 * dGamma γ / γ ^ 2 → ∃ C t₀ : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ t : ℝ, t₀ ≤ t →
        P {ω | ENNReal.ofReal t < ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) 𝕣 0)⁻¹ *
          internalDiam (D (h ω)) (rS 𝕣) (rS 𝕣)} ≤ ENNReal.ofReal (C * t ^ (-a))

/-- **DFGPS Proposition 3.10** from Proposition 3.1 (negative moments) and the tail bound of
Steps 1–3 (positive moments). -/
theorem prop3_10_of_tail (h31 : Prop3_1) (hT : DiamTailRS) : Prop3_10 := by
  intro γ hγ0 hγ2 D c hD p hp
  rcases le_or_gt p 0 with hp0 | hp0
  · exact prop3_10_nonpos h31 hγ0 hγ2 hD hp0
  set a := (p + 4 * dGamma γ / γ ^ 2) / 2 with ha
  obtain ⟨C, t₀, hC⟩ := hT γ hγ0 hγ2 D c hD a (by rw [ha]; linarith)
  refine ⟨momBd p a (max C 0) (max t₀ 1), fun P _ h hh 𝕣 h𝕣 => ?_⟩
  refine lintegral_rpow_le_of_tail P _ hp0 (by rw [ha]; linarith) (le_max_right _ _)
    (le_max_right _ _) fun t ht => ?_
  have ht0 : 0 < t := by have := le_max_right t₀ 1; linarith
  exact (hC P h hh 𝕣 h𝕣 t ((le_max_left _ _).trans ht)).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht0.le _)))

end LQGMetric.DFGPS

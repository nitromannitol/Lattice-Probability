import LatticeProb.LQG.ConeLocalizedPowerWindowLimit
import LatticeProb.Topology.FirstHitExitReversalPolynomial

/-! # Localized diameter limits from first-hit estimates -/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped Topology NNReal ENNReal

namespace LatticeProb.LQG

/-- Separate first-hit estimates for the forward curve and an equal-law reversed
reference curve imply the localized power-window diameter limit. -/
theorem tendsto_measure_cone_localized_diameter_of_firstHit
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} (ν : Measure Ξ)
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    (ηf : Ω → ℝ → ℂ) (zf : ℂ)
    (g : Ω → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (h : Ξ → C(ℝ, EuclideanSpace ℝ (Fin 2))) (ηb : Ξ → ℝ → ℂ) (zb : ℂ)
    (hrev : ∀ ω t, g ω t = (F ∘ ηL) ω (-t))
    (hlaw : IdentDistrib g h P ν)
    {af₀ af₁ ab₀ ab₁ : ℝ} (haf₀ : 0 ≤ af₀) (haf₁ : 0 < af₁)
    (hab₀ : 0 ≤ ab₀) (hab₁ : 0 < ab₁)
    (hpathf : ∀ᵐ ω ∂P, Continuous (ηf ω) ∧
      Tendsto (ηf ω) (cocompact ℝ) (cocompact ℂ) ∧ zf ∈ range (ηf ω) ∧
      ∀ s, (F ∘ ηL) ω s = Complex.orthonormalBasisOneI.repr
        (ηf ω (MatedCRTHarmonic.GMS4b.hitTime (ηf ω) zf + s) - zf))
    (hboundf : ∀ ρ : ℝ, 0 < ρ → ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ ∃ w, ball w (δ * ρ) ⊆
        ηf ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (ηf ω) zf)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (ηf ω) zf ≤ t ∧
            ηf ω t ∉ ball zf ρ})} ≤ ENNReal.ofReal (af₀ * Real.exp (-af₁ / δ)))
    (hpathb : ∀ᵐ ω ∂ν, Continuous (ηb ω) ∧
      Tendsto (ηb ω) (cocompact ℝ) (cocompact ℂ) ∧ zb ∈ range (ηb ω) ∧
      ∀ s, h ω s = Complex.orthonormalBasisOneI.repr
        (ηb ω (MatedCRTHarmonic.GMS4b.hitTime (ηb ω) zb + s) - zb))
    (hboundb : ∀ ρ : ℝ, 0 < ρ → ∀ δ ∈ Ioo (0 : ℝ) 1,
      ν {ω | ¬ ∃ w, ball w (δ * ρ) ⊆
        ηb ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (ηb ω) zb)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (ηb ω) zb ≤ t ∧
            ηb ω t ∉ ball zb ρ})} ≤ ENNReal.ofReal (ab₀ * Real.exp (-ab₁ / δ)))
    (n : ℕ) (hn : 0 < n) {q ρ r e s a ell : ℝ} (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) {M : ℕ} (hM : 0 < M)
    (he : 0 < e) (heupper : e < (n : ℝ) ^ 2 / (2 * γ ^ 2) - 2)
    (hs : 0 < s) (hsγ : s < 4 / γ ^ 2 - 1) (ha : 0 < a) (hell : 0 < ell) :
    Tendsto (fun δ : ℝ =>
      P {ω | ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
        MatedCRTHarmonic.GMS4b.locDA (δ ^ (2 + γ ^ 2 / 2 + (n : ℝ)) / 4) (η ω) 0})
      (𝓝[>] 0) (𝓝 0) := by
  let Cf : ℝ := af₀ * ((n.factorial : ℝ) / af₁ ^ n)
  let Cb : ℝ := ab₀ * ((n.factorial : ℝ) / ab₁ ^ n)
  have hCf : 0 ≤ Cf := mul_nonneg haf₀ (div_nonneg (by positivity) (by positivity))
  have hCb : 0 ≤ Cb := mul_nonneg hab₀ (div_nonneg (by positivity) (by positivity))
  have hf := eventually_uniform_scale_bound P (forwardExitBallFailure (F ∘ ηL)) Cf (n : ℝ)
    (fun δ hδ k => measure_forwardExitBallFailure_le_polynomial_of_firstHit
      P (F ∘ ηL) ηf zf haf₀ haf₁ hpathf hboundf n hδ k)
  have hb := eventually_uniform_scale_bound P (backwardExitBallFailure (F ∘ ηL)) Cb (n : ℝ)
    (fun δ hδ k => measure_backwardExitBallFailure_le_polynomial_of_firstHit
      P ν (F ∘ ηL) g h ηb hrev hlaw zb hab₀ hab₁ hpathb hboundb n hδ k)
  exact tendsto_measure_cone_localized_diameter D hstd hγ μ hμ F hFm hF
    (by exact_mod_cast hn) hq hqρ hρ1 hr hM he heupper hs hsγ ha hell Cf Cb hCf hCb hf hb

end LatticeProb.LQG

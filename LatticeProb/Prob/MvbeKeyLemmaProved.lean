import Mathlib
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeSmoothing
import LatticeProb.Prob.MvbeKeyLemma
import LatticeProb.Prob.MvbeSmoothSmallAngle

/-!
# Raič's Lemma 2.7, unconditional form

`mvbe_keyLemma_gammaStar` (`MvbeKeyLemma.lean`) assembles Lemma 2.7 from the small-angle estimate
(2.17) for the smoothing function, which `MvbeSmoothSmallAngle.lean` proves for `smoothOuter` and
`smoothInner`.  This file plugs the two together.
-/

open MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder

namespace LatticeProb

variable {m : ℕ} {κ : ℝ}

/-- **Raič's Lemma 2.7.**  For a regular class `C` with `{ρ_A < 0}` open (`MvbeNegOpen`) and finite
Gaussian perimeter, a member `A`, `ε > 0`, the smoothing `f ∈ {f_A^{ε}, f_A^{-ε}}`, a random vector
`W` that is `D`-close to `N(μ, S)` on the class (`σ I ≤ S^{1/2}`, `σ ≤ 1`), there is a measurable
majorant `b` of `|E⟨∇³U_a f(W), u^{⊗3}⟩|` (uniformly in `‖u‖ ≤ 1`) with
`∫_0^{π/2} b(a) tan a da ≤ c₃/(6σ³) + √(2(1+κ)c₁c₃) (γ*/σ + 4D/ε)`. -/
theorem mvbe_keyLemma_proved (C : MvbeRegularClass m κ) (hneg : MvbeNegOpen C)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) ≠ ⊤)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : f = C.smoothOuter A ε ∨ f = C.smoothInner A ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {σ D : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hS : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S)
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D) :
    ∃ b : ℝ → ℝ, Measurable b ∧ (∀ a ∈ Ioo 0 (Real.pi / 2), 0 ≤ b a) ∧
      (∀ a ∈ Ioo 0 (Real.pi / 2), ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ ≤ 1 →
        |mvbeH a f u P W| ≤ b a) ∧
      IntervalIntegrable (fun a => b a * Real.tan a) volume 0 (Real.pi / 2) ∧
      ∫ a in (0 : ℝ)..(Real.pi / 2), b a * Real.tan a
        ≤ mvbeHermiteConst 3 / (6 * σ ^ 3)
          + Real.sqrt (2 * (1 + κ) * mvbeHermiteConst 1 * mvbeHermiteConst 3)
            * ((C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal / σ
              + 4 * D / ε) := by
  refine mvbe_keyLemma_gammaStar C hneg hA hε hf P hW μ S hσ hσ1 hS hD ?_
  intro a ha0 ha1 u hu
  rcases hf with rfl | rfl
  · exact mvbe_smooth_small_angle_outer C hneg P hW μ S hσ hσ1 hS hD hγ hA hε ha0 ha1 hu
  · exact mvbe_smooth_small_angle_inner C hneg P hW μ S hσ hσ1 hS hD hγ hA hε ha0 ha1 hu

end LatticeProb

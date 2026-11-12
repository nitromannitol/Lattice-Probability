import LatticeProb.LQG.LQGMetricUniv
import LatticeProb.LQG.WeylCompositionOuter
import LatticeProb.Gauss.PairingSigmaAlgebraShift

/-!
# Locality of the Weyl scaling of the LQG metric by a deterministic continuous function

Let `𝔇` be a γ-LQG metric with Weyl exponent `ξ` (`IsLQGMetric`), `h^ℂ` a whole-plane GFF and `f` a deterministic
continuous function. The axioms of `𝔇` for the field `h^ℂ + f` give:

* `LatticeProb.LQG.IsLQGMetric.ae_eq_toReal_weylScaling`: a.s. `D_{h^ℂ + f} = e^{ξ f} · D_{h^ℂ}` as real-valued
  functions (Weyl scaling, Axiom III, together with the nonnegativity of the length metric `D_{h^ℂ + f}`, Axiom I).
* `LatticeProb.LQG.IsLQGMetric.exists_measurable_internalMetric_weylScaling`: for every deterministic open set `U`, the
  internal metric of `e^{ξ f} · D_{h^ℂ}` on `U` is a.s. equal to a random function whose values are measurable for the
  σ-algebra of the logarithmically shifted field `h^ℂ - α₀ log |·|` on `U` (`fieldSigmaAlgebra`), for every `α₀`
  (locality, Axiom II, for `h^ℂ + f`, whose σ-algebra on `U` is that of `h^ℂ` since `f` is deterministic).
-/

open MeasureTheory Set
open scoped ENNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Weyl scaling by a deterministic continuous function, as an equality of real-valued functions: a.s.
`D_{h^ℂ + f} = (e^{ξ f} · D_{h^ℂ}).toReal`. -/
theorem IsLQGMetric.ae_eq_toReal_weylScaling (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    {f : ℂ → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂P, 𝔇 (addFunPairing (hC ω) f) = fun u v => (weylScaling (𝔇 (hC ω)) ξ f u v).toReal := by
  have h0 := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => (0 : ℝ)) hG (fun _ => continuous_const)
    (fun _ => measurable_const)
  have hS := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => f) hG (fun _ => hf) (fun _ => measurable_const)
  filter_upwards [h0.ae_weylScaling, hS.ae_isEuclideanLengthMetric] with ω hW hE
  have hW' : ∀ u v, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) u v) = weylScaling (𝔇 (hC ω)) ξ f u v := by
    intro u v
    have h := hW f hf u v
    simp only [addFunPairing_zero_fun] at h
    exact h
  have hE' : IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) := hE
  funext u v
  rw [← hW' u v, ENNReal.toReal_ofReal (hE'.nonneg' u v)]

/-- **Locality of `e^{ξ f} · D_{h^ℂ}` for a deterministic continuous `f`.** For every deterministic open set `U`, the
internal metric on `U` of the Weyl scaling `e^{ξ f} · D_{h^ℂ}` is a.s. equal to a random function `G` whose values are
measurable for `fieldSigmaAlgebra α₀ hC U`, the σ-algebra of `h^ℂ - α₀ log |·|` on `U`. -/
theorem IsLQGMetric.exists_measurable_internalMetric_weylScaling (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {f : ℂ → ℝ} (hf : Continuous f) {U : Set ℂ} (hU : IsOpen U) :
    ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC U] fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
        internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ f u v).toReal) U z w = G ω z w := by
  have hS := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => f) hG (fun _ => hf) (fun _ => measurable_const)
  obtain ⟨G, hGm, hGeq⟩ := hS.locality U hU
  refine ⟨G, fun z w => ?_, ?_⟩
  · rw [← pairingSigmaAlgebra_addFunPairing_eq_fieldSigmaAlgebra α₀ hC f U]
    exact hGm z w
  · filter_upwards [hGeq, h𝔇.ae_eq_toReal_weylScaling hG hf] with ω hω hE
    rw [← hE]
    exact hω

end LatticeProb.LQG

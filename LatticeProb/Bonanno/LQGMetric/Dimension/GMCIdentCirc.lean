/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentCirc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentBoch
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg

/-!
# `E(μ_ε(·) 1_B)` for `B ∈ 𝓖_n`: the circle-average step of Berestycki's argument
(P2-GMCID, D67)

Hypothesis `WNCircleCoupling W X P`: the zero-boundary GFF `X` on `𝕍` is realized by the white
noise `W` on circles, `(h, ∂B(z, r)) = √π W(K^{(0,∞)}_{∂B(z,r)})` a.s. (DZZ l. 430–433 with
`δ → 0`; this is what the white-noise construction of `X` provides).

`setIntegral_exp_circle`: for `B ∈ 𝓖_n` and `r = 2^{-k}` with `B̄(z, 2r) ⊆ 𝕍`,

  `E[r^{γ²/2} e^{γ h_r(z)} 1_B] = e^{γ²/2 (hS(z,z) − π‖K₂‖²)} E[e^{γ√π W(K₂)} 1_B]`,

`K₂ = K^{(4^{-n},∞)}_{∂B(z,r)}` the coarse part. Proof: split `K = K₁ + K₂` into fine and coarse
scales (`measKerL2_split`), condition on `𝓖_n` (`condExp_exp_wn`), and identify
`π‖K₁‖² = Var h_r(z) − π‖K₂‖² = −log r + hS(z,z) − π‖K₂‖²` (`circleCov_same`, orthogonality of
the two pieces). This is `E(μ_ε(S) | 𝓕_n) = μ^n_ε(S)` of Berestycki (arXiv:1506.09113, §4,
l. 683–685) at a single point, tested against `B ∈ 𝓕_n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {X : Ω → Measure ℂ → ℝ}

lemma measurable_measKer {A : Set ℂ} (hA : IsOpen A) {I : Set ℝ} (hI : MeasurableSet I)
    (μ : Measure ℂ) [SFinite μ] : Measurable (measKer A I μ) := by
  unfold measKer
  exact ((measurable_wndKernel_uncurry hA hI).stronglyMeasurable.integral_prod_left).measurable

lemma measKer_nonneg (A : Set ℂ) (I : Set ℝ) (μ : Measure ℂ) (p : ℝ × ℂ) :
    0 ≤ measKer A I μ p :=
  integral_nonneg fun _ => wndKernel_nonneg _ _ _ _

lemma foldedCircle_compl_closedBall {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ openSquare) : foldedCircle z r (closedBall z r)ᶜ = 0 := by
  rw [foldedCircle_eq_of_inSq (inSq_of_closedBall hr hB) hr]
  exact circleUnif_compl_closedBall hr z

lemma variance_sqrtPi_wn (hW : IsWhiteNoise P W) (g : WNSpace) :
    Var[fun ω => Real.sqrt Real.pi * W g ω; P] = Real.pi * ‖g‖ ^ 2 := by
  rw [variance_const_mul, (hW.hasLaw_single g).variance_eq, variance_id_gaussianReal,
    Real.sq_sqrt Real.pi_pos.le, Real.coe_toNNReal _ (sq_nonneg _)]

end GMCIdent
end LQGMetric

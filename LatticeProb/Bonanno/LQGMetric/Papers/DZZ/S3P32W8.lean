/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L8

/-!
# D97, packet P-1: `IsChaosLimit` for `M^W` (DZZ (eq-def-M-eta))

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-M-eta), l. 1209–1213): `M^W = M_γ^{h̃}` is the
a.s. limit of `∫_A e^{γ h̃_{2^{-n}}(z) − γ²/2 E h̃_{2^{-n}}(z)²} dz`. Here, for the continuous version
`ζ_{2^{-n}} = coarseVer hW n` of `h̃_{2^{-n}}` and `V = tildeVar = Var h̃` (the normalisations of
`dzz_lemma310_var`):

* `wickMeasC_lt_top`: the approximations are finite on compacts (continuous density);
* **`isChaosLimit_wickQArea`**: a.s. `IsChaosLimit γ ζ tildeVar 2^{-n} (M^W)`, given that a.s. no
  mass of the approximations escapes to `∂𝕍` (`StripTight`) and `M^W` does not charge the
  rational circles. Proof: `ae_isVagueLimitOn_wickMeasC` and the portmanteau
  `tendsto_ball_of_vague`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

lemma continuous_wickDensC (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) (ω : Ω') :
    Continuous fun z =>
      Real.exp (γ * coarseVer hW n z ω - γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ n) z) := by
  have hδ : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  unfold tildeVar
  exact Real.continuous_exp.comp ((((coarseVer_spec hW n).1 ω).const_mul γ).sub
    (continuous_const.mul (continuous_const.mul
      ((GMCIdent.continuous_tildeKer hW hδ).norm.pow 2))))

lemma wickMeasC_lt_top (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) (ω : Ω') {K : Set ℂ}
    (hK : IsCompact K) : wickMeasC hW γ n ω K < ⊤ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_wickDensC hW γ n ω).continuousOn
  rw [wickMeasC, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal
        (Real.exp (γ * coarseVer hW n z ω - γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ n) z))
      ≤ ∫⁻ _z in K, ENNReal.ofReal C := by
        refine setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal ?_
        have := hC z hz
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
    _ = ENNReal.ofReal C * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- **`M^W` is DZZ's `M_γ^{h̃}` in the sense of `IsChaosLimit`** (eq-def-M-eta), given the
absence of mass escape to `∂𝕍` and null rational circles. -/
theorem isChaosLimit_wickQArea (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (ζ : ℝ → ℂ → Ω' → ℝ) (hζ : ∀ n z ω, ζ ((1 / 2 : ℝ) ^ n) z ω = coarseVer hW n z ω)
    (hT : ∀ᵐ ω ∂P', StripTight fun n => wickMeasC hW γ n ω)
    (hS : ∀ᵐ ω ∂P', ∀ (c : ℚ × ℚ) (q : ℚ), wickQArea γ W ω (sphere (ratPt c) q) = 0) :
    ∀ᵐ ω ∂P', IsChaosLimit γ (fun s z => ζ s z ω) tildeVar (fun n => (1 / 2 : ℝ) ^ n)
      (wickQArea γ W ω) := by
  filter_upwards [ae_isVagueLimitOn_wickMeasC hW hγ hγ2, hT, hS] with ω hv ht hs
  intro c q _
  refine (tendsto_ball_of_vague hv (fun n K hK _ => wickMeasC_lt_top hW γ n ω hK) ht
    (ratPt c) q (hs c q)).congr fun n => ?_
  rw [wickMeasC, withDensity_apply _ (measurableSet_ball.inter measurableSet_dzzV)]
  have h' : ∀ z, ζ ((2 : ℝ)⁻¹ ^ n) z ω = coarseVer hW n z ω := fun z => by
    rw [← one_div]; exact hζ n z ω
  simp only [one_div, h']

end DZZ
end LQGMetric

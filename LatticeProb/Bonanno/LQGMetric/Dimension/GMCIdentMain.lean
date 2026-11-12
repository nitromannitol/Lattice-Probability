/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentDCT
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentL1
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The circle-average LQG measure is the limit of the white-noise martingale (P2-GMCID, D67)

**Main theorem** (`ae_tendsto_wnGMC`): let `W` be a white noise and `X` a zero-boundary GFF on
`𝕍 = (0,1)²` realized by `W` on circles (`WNCircleCoupling`) and measurable with respect to
`𝓖_∞ = ⨆ 𝓖_n`. For `0 < γ < 2` and `f` continuous with compact support in `𝕍`, almost surely

  `∫ f(z) CR(z)^{γ²/2} e^{γ h̃_{2^{-n}}(z) − γ²/2 Var h̃_{2^{-n}}(z)} dz → ∫ f dM_γ`,

`M_γ = qAreaMeasureOn γ X 𝕍` the circle-average (Duplantier–Sheffield) LQG measure,
`CR^{γ²/2} = e^{γ²/2 hS(z,z)}`, `Var h̃_δ(z) = π‖κ_z‖²` (DZZ (eq-cov-tildeh)).

This is DZZ `LBM_LGDarXiv.tex` l. 648–658 ("it follows from martingale convergence that the
sequence (eq-03172018-a) almost surely weakly converges … the limit is precisely `M_γ`"), proved
by Berestycki's argument (arXiv:1506.09113, §4, `main.tex` l. 680–700): `E[M_γ(f) | 𝓖_n] = Z_n`
(set integrals, `tendsto_setIntegral_areaApprox` + `L¹` convergence) and Lévy's upward theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper Metric
open scoped ENNReal NNReal ComplexConjugate

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {X : Ω → Measure ℂ → ℝ}

lemma measurable_hS_diag : Measurable fun z => hS z z := by
  have e : (fun z => hS z z) = fun z => Real.log ‖sqM z - conj (sqM z)‖ -
      Real.log ‖deriv sqM z‖ := by
    funext z; simp [hS, dslope_same]
  rw [e]
  exact ((measurable_sqM.sub (Complex.continuous_conj.measurable.comp measurable_sqM)).norm.log).sub
    (measurable_deriv sqM).norm.log

/-- `CR^{γ²/2} e^{−γ²/2 Var h̃_{2^{-n}}}` -/
def wnWeight (γ : ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  Real.exp (γ ^ 2 / 2 * (hS z z - Real.pi *
    ‖wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) z‖ ^ 2))

lemma measurable_wnWeight (hW : IsWhiteNoise P W) (γ : ℝ) (n : ℕ) :
    Measurable (wnWeight γ n) := by
  have hδ : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  unfold wnWeight
  exact Real.measurable_exp.comp ((measurable_hS_diag.sub
    (((continuous_tildeKer hW hδ).norm.pow 2).measurable.const_mul _)).const_mul _)

/-- the white-noise approximation `Z_n(f) = ∫ f wnWeight e^{γ h̃_{2^{-n}}}` -/
def wnGMC (W : WNSpace → Ω → ℝ) (γ : ℝ) (n : ℕ) (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z, f z * (wnWeight γ n z * Real.exp (γ * tildeVer W n z ω))

lemma measurable_tildeVer' (hW : IsWhiteNoise P W) (n : ℕ) :
    Measurable fun p : ℂ × Ω => tildeVer W n p.1 p.2 :=
  (measurable_tildeVer hW n).mono (sup_le_sup le_rfl
    (MeasurableSpace.comap_mono (wnSigma_le hW _))) le_rfl

lemma integral_exp_tildeHInf (hW : IsWhiteNoise P W) (γ : ℝ) (n : ℕ) (z : ℂ) :
    ∫ ω, Real.exp (γ * tildeHInf W ((2 : ℝ)⁻¹ ^ n) z ω) ∂P =
      Real.exp (γ ^ 2 / 2 * (Real.pi *
        ‖wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) z‖ ^ 2)) := by
  have := integral_exp_wn hW (γ * Real.sqrt Real.pi)
    (wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) z)
  rw [mul_pow, Real.sq_sqrt Real.pi_pos.le] at this
  simp only [tildeHInf, wnField, ← mul_assoc]
  rw [this]; ring_nf

lemma integrable_exp_tildeHInf (hW : IsWhiteNoise P W) (γ : ℝ) (n : ℕ) (z : ℂ) :
    Integrable (fun ω => Real.exp (γ * tildeHInf W ((2 : ℝ)⁻¹ ^ n) z ω)) P := by
  refine (integrable_exp_wn hW (γ * Real.sqrt Real.pi)
    (wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) z)).congr
    (Eventually.of_forall fun ω => ?_)
  simp only [tildeHInf, wnField]; ring_nf

lemma wnWeight_mul_integral (hW : IsWhiteNoise P W) (γ : ℝ) (n : ℕ) (z : ℂ) :
    wnWeight γ n z * ∫ ω, Real.exp (γ * tildeVer W n z ω) ∂P = Real.exp (γ ^ 2 / 2 * hS z z) := by
  have h : (fun ω => Real.exp (γ * tildeVer W n z ω)) =ᵐ[P]
      fun ω => Real.exp (γ * tildeHInf W ((2 : ℝ)⁻¹ ^ n) z ω) := by
    filter_upwards [tildeVer_ae_eq hW n z] with ω hω
    rw [hω]
  rw [integral_congr_ae h, integral_exp_tildeHInf hW, wnWeight, ← Real.exp_add]
  congr 1; ring

/-- `Z_n(f)` is `𝓖_n`-measurable. -/
lemma stronglyMeasurable_wnGMC (hW : IsWhiteNoise P W) (γ : ℝ) (n : ℕ) {f : ℂ → ℝ}
    (hf : Measurable f) : StronglyMeasurable[wnFil hW n] (wnGMC W γ n f) := by
  have hm := measurable_tildeVer hW n
  have hwm := measurable_wnWeight hW γ n
  let _ : MeasurableSpace Ω := wnFil hW n
  have hj : Measurable fun p : ℂ × Ω =>
      f p.1 * (wnWeight γ n p.1 * Real.exp (γ * tildeVer W n p.1 p.2)) :=
    (hf.comp measurable_fst).mul ((hwm.comp measurable_fst).mul
      (Real.measurable_exp.comp (hm.const_mul γ)))
  exact hj.stronglyMeasurable.integral_prod_left

end GMCIdent
end LQGMetric

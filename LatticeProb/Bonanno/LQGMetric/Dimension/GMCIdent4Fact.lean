/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4Fact at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Vague
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Exp
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Tele
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentCirc
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqRate
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCov
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.Complex.Schwarz
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqLip
import LatticeProb.Bonanno.LQGDimension.Gaussian.SteinIBP
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationLip
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqGauss
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueOpenExist
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# The DZZ factorization `M_γ = e^{γ h̃_δ − γ²/2 Var h̃_δ} M̃_{γ,δ}` (P2-GMCID4, item 4b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-def-tilde-M), l. 676–683):
`M̃_{γ,δ}(B) = lim_n ∫_B e^{γ h̃^δ_{2^{-n}}(z) − γ²/2 Var h̃^δ_{2^{-n}}(z)} dz`. For `δ = 2^{-m}`
and the white-noise field:

* `coarseVer hW m`: a version of `h̃_δ` continuous in `z` (`DZZ.exists_continuous_tildeHInf`);
* `cDens`: `CR(z)^{γ²/2} e^{γ h̃_δ(z) − γ²/2 Var h̃_δ(z)}`, positive and continuous on `𝕍`;
* `tildeM := cDens⁻¹ · M_γ`, so that **`qArea_eq_withDensity_tildeM`**: `M_γ = cDens · M̃_{γ,δ}`;
* `bandMeas n := (wnDens n / cDens) dz`, the band approximation; **`ae_isVagueLimitOn_bandMeas`**:
  a.s. `bandMeas n → M̃_{γ,δ}` vaguely on `𝕍`, i.e. `M̃_{γ,δ}` is DZZ's limit (pathwise from the a.s.
  vague convergence `ae_isVagueLimitOn_wnMeas`, with the random test function `f / cDens`);
* **`bandDens_ae_eq`**: for `n ≥ m` and each `z`, a.s. the band density is DZZ's
  `e^{γ h̃^δ_{2^{-n}}(z) − γ²/2 Var h̃^δ_{2^{-n}}(z)}` (`DZZ.tildeH`).

Own glue (D85); the constant `CR^{γ²/2}` is absorbed in `cDens` (our normalization, handoff
P2-GMCID Notes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal ComplexConjugate RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent4

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

lemma continuousOn_hS_diag : ContinuousOn (fun z => hS z z) openSquare := by
  have e : (fun z => hS z z) = fun z => Real.log ‖sqM z - conj (sqM z)‖ -
      Real.log ‖deriv sqM z‖ := by
    funext z; simp [hS, dslope_same]
  rw [e]
  have hc := differentiableOn_sqM.continuousOn
  refine (continuousOn_log_norm (hc.sub (Complex.continuous_conj.comp_continuousOn hc))
    fun y hy => sub_conj_ne_zero hy hy).sub
    (continuousOn_log_norm ((differentiableOn_sqM.deriv isOpen_openSquare).continuousOn)
      fun y hy => ?_)
  have := dslope_sqM_ne_zero hy hy
  rwa [dslope_same] at this

lemma continuousOn_wnWeight (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) :
    ContinuousOn (wnWeight γ n) openSquare := by
  have hδ : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  unfold wnWeight
  exact Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (continuousOn_hS_diag.sub
    (continuousOn_const.mul ((continuous_tildeKer hW hδ).norm.pow 2).continuousOn)))

/-- a version of `h̃_{2^{-m}}` continuous in `z` -/
def coarseVer (hW : IsWhiteNoise P' W) (m : ℕ) : ℂ → Ω' → ℝ :=
  (exists_continuous_tildeHInf hW (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ m by positivity)).choose

lemma coarseVer_spec (hW : IsWhiteNoise P' W) (m : ℕ) :
    (∀ ω, Continuous fun z => coarseVer hW m z ω) ∧ (∀ z, Measurable (coarseVer hW m z)) ∧
      ∀ z, coarseVer hW m z =ᵐ[P'] tildeHInf W ((2 : ℝ)⁻¹ ^ m) z :=
  (exists_continuous_tildeHInf hW (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ m by positivity)).choose_spec

/-- `CR(z)^{γ²/2} e^{γ h̃_δ(z) − γ²/2 Var h̃_δ(z)}`, `δ = 2^{-m}` -/
def cDens (hW : IsWhiteNoise P' W) (γ : ℝ) (m : ℕ) (z : ℂ) (ω : Ω') : ℝ :=
  wnWeight γ m z * Real.exp (γ * coarseVer hW m z ω)

lemma cDens_pos (hW : IsWhiteNoise P' W) (γ : ℝ) (m : ℕ) (z : ℂ) (ω : Ω') :
    0 < cDens hW γ m z ω :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

lemma measurable_cDens (hW : IsWhiteNoise P' W) (γ : ℝ) (m : ℕ) (ω : Ω') :
    Measurable fun z => cDens hW γ m z ω :=
  (measurable_wnWeight hW γ m).mul (Real.continuous_exp.measurable.comp
    (((coarseVer_spec hW m).1 ω).measurable.const_mul γ))

lemma continuousOn_cDens_inv (hW : IsWhiteNoise P' W) (γ : ℝ) (m : ℕ) (ω : Ω') :
    ContinuousOn (fun z => (cDens hW γ m z ω)⁻¹) openSquare :=
  ((continuousOn_wnWeight hW γ m).mul (Real.continuous_exp.comp
    (((coarseVer_spec hW m).1 ω).const_mul γ)).continuousOn).inv₀
    fun z _ => (cDens_pos hW γ m z ω).ne'

/-- DZZ's `M̃_{γ,δ}` for `δ = 2^{-m}`: `M_γ` with the coarse factor removed -/
def tildeM (hW : IsWhiteNoise P' W) (γ : ℝ) (m : ℕ) (ω : Ω') : Measure ℂ :=
  (qAreaMeasureOn γ (wnField W ω) openSquare).withDensity
    fun z => ENNReal.ofReal (cDens hW γ m z ω)⁻¹

/-- **the factorization** `M_γ(dz) = CR^{γ²/2} e^{γ h̃_δ(z) − γ²/2 Var h̃_δ(z)} M̃_{γ,δ}(dz)` -/
theorem qArea_eq_withDensity_tildeM (hW : IsWhiteNoise P' W) (γ : ℝ) (m : ℕ) (ω : Ω') :
    qAreaMeasureOn γ (wnField W ω) openSquare =
      (tildeM hW γ m ω).withDensity fun z => ENNReal.ofReal (cDens hW γ m z ω) := by
  have hm := measurable_cDens hW γ m ω
  have h1 : Measurable fun z => ENNReal.ofReal (cDens hW γ m z ω)⁻¹ :=
    ENNReal.measurable_ofReal.comp hm.inv
  have h2 : Measurable fun z => ENNReal.ofReal (cDens hW γ m z ω) :=
    ENNReal.measurable_ofReal.comp hm
  unfold tildeM
  rw [← withDensity_mul _ h1 h2]
  conv_lhs => rw [← withDensity_one (μ := qAreaMeasureOn γ (wnField W ω) openSquare)]
  congr 1
  funext z
  simp only [Pi.mul_apply, Pi.one_apply]
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (cDens_pos hW γ m z ω).le),
    inv_mul_cancel₀ (cDens_pos hW γ m z ω).ne', ENNReal.ofReal_one]

lemma integral_withDensity_ofReal {μ : Measure ℂ} {d : ℂ → ℝ} (hd : Measurable d)
    (h0 : ∀ z, 0 ≤ d z) (f : ℂ → ℝ) :
    ∫ z, f z ∂(μ.withDensity fun z => ENNReal.ofReal (d z)) = ∫ z, d z * f z ∂μ := by
  change ∫ z, f z ∂(μ.withDensity fun z => ((d z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hd.real_toNNReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (h0 z)]

/-- the band approximation `e^{γ h̃^δ_{2^{-n}} − γ²/2 Var h̃^δ_{2^{-n}}} dz` -/
def bandMeas (hW : IsWhiteNoise P' W) (γ : ℝ) (m n : ℕ) (ω : Ω') : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (wnDens W γ n z ω / cDens hW γ m z ω)

/-- **`M̃_{γ,δ}` is DZZ's limit (eq-def-tilde-M)**: a.s. the band approximations converge
vaguely to `M̃_{γ,δ}` on `𝕍` -/
theorem ae_isVagueLimitOn_bandMeas [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (m : ℕ) :
    ∀ᵐ ω ∂P', IsVagueLimitOn openSquare (fun n => bandMeas hW γ m n ω) (tildeM hW γ m ω) := by
  filter_upwards [ae_isVagueLimitOn_wnMeas hX hW hγ hγ2] with ω h
  set M := qAreaMeasureOn γ (wnField W ω) openSquare
  have hm := measurable_cDens hW γ m ω
  have hci := continuousOn_cDens_inv hW γ m ω
  refine ⟨withDensity_absolutelyContinuous _ _ h.1, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hci.mono hKU)
    rw [tildeM, withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, ENNReal.ofReal (cDens hW γ m z ω)⁻¹ ∂M
        ≤ ∫⁻ _z in K, ENNReal.ofReal C ∂M := by
          refine setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal ?_
          have := hC z hz
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal C * M K := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.2.1 K hK hKU)
  · set g : ℂ → ℝ := fun z => f z * (cDens hW γ m z ω)⁻¹
    have hgU : tsupport g ⊆ openSquare := (tsupport_mul_subset_left).trans hfU
    have hgc : Continuous g :=
      (hf.continuousOn.mul hci).continuous_of_tsupport_subset isOpen_openSquare hgU
    have hg := h.2.2 g hgc hfc.mul_right hgU
    have e1 : ∀ n, ∫ z, f z ∂(bandMeas hW γ m n ω) = ∫ z, g z ∂(wnMeas W γ n ω) := by
      intro n
      rw [bandMeas, wnMeas, integral_withDensity_ofReal
          (d := fun z => wnDens W γ n z ω / cDens hW γ m z ω) ((measurable_wnDens hW γ n ω).div hm)
          (fun z => div_nonneg (wnDens_nonneg γ n z ω) (cDens_pos hW γ m z ω).le),
        integral_withDensity_ofReal (measurable_wnDens hW γ n ω) (fun z => wnDens_nonneg γ n z ω)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [g]; ring
    have e2 : ∫ z, f z ∂(tildeM hW γ m ω) = ∫ z, g z ∂M := by
      rw [tildeM, integral_withDensity_ofReal (d := fun z => (cDens hW γ m z ω)⁻¹) hm.inv
        (fun z => inv_nonneg.2 (cDens_pos hW γ m z ω).le)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [g]; ring
    simp_rw [e1, e2]
    exact hg

/-- **the band density is DZZ's**: for `n ≥ m` and each `z`, a.s.
`wnDens n / cDens = e^{γ h̃^δ_{2^{-n}}(z) − γ²/2 Var h̃^δ_{2^{-n}}(z)}`, `δ = 2^{-m}` -/
theorem bandDens_ae_eq (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    (fun ω => wnDens W γ n z ω / cDens hW γ m z ω) =ᵐ[P'] fun ω =>
      Real.exp (γ * tildeH W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) z ω -
        γ ^ 2 / 2 * Var[tildeH W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) z; P']) := by
  set a : ℝ := (2 : ℝ)⁻¹ ^ n
  set b : ℝ := (2 : ℝ)⁻¹ ^ m
  have ha : 0 < a := by positivity
  have hab : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) 2
  set κa := wndKernelL2 openSquare (Ioi (a ^ 2)) z
  set κb := wndKernelL2 openSquare (Ioi (b ^ 2)) z
  set κab := wndKernelL2 openSquare (Ioo (a ^ 2) (b ^ 2)) z
  have hsplit : κa = κb + κab := wndKernelL2_split (by positivity) hab z
  have horth : ⟪κb, κab⟫ = 0 := by
    refine inner_eq_zero_of_supportedIn ?_ (supportedIn_wndKernelL2 _ measurableSet_Ioi z)
      (supportedIn_wndKernelL2 _ measurableSet_Ioo z)
    refine Disjoint.set_prod_left (Set.disjoint_left.2 fun x h1 h2 => ?_) _ _
    exact lt_asymm (mem_Ioi.1 h1) h2.2
  have hnorm : ‖κa‖ ^ 2 = ‖κb‖ ^ 2 + ‖κab‖ ^ 2 := by
    rw [hsplit, @norm_add_sq_real, horth]; ring
  have hvar : Var[tildeH W a b z; P'] = Real.pi * ‖κab‖ ^ 2 := variance_sqrtPi_wn hW κab
  have hadd : W κa =ᵐ[P'] fun ω => W κb ω + W κab ω := by rw [hsplit]; exact hW.add_ae κb κab
  filter_upwards [tildeVer_ae_eq hW n z, (coarseVer_spec hW m).2.2 z, hadd] with ω h1 h2 h3
  rw [hvar, div_eq_iff (cDens_pos hW γ m z ω).ne', wnDens, cDens, wnWeight, wnWeight, h1, h2]
  simp only [tildeHInf, tildeH, DZZ.wnField]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [show W κa ω = W κb ω + W κab ω from h3, hnorm]
  ring

end GMCIdent4
end LQGMetric

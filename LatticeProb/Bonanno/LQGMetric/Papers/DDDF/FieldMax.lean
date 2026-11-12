/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.FieldMax at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOsc
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# DDDF Prop. 2, (2.10): the maximum tail of `φ_{0,n}` (task P2-DDDFFIELD, WP-94)

DDDF (arXiv:1904.08021, `tightness.tex` l. 299–305), (2.10): for `α > 0`, `n ≥ 0`,
`P(max_{[0,1]²} |φ_{0,n}| ≥ α(n + C√n)) ≤ C 4^n e^{−α² n/log 4}`. DDDF give no proof ("corresponds
to Lemma 10.1 [...] in [DF18]"); we follow DF (arXiv:1809.02607) Lemma 10.1, l. 1823–1858:
union bound and Gaussian tails on the grid `2^{-n}ℤ² ∩ [0,1)²`, then
`sup_{[0,1]²} |φ| ≤ max_grid |φ| + 2 · 2^{-n} sup_{[0,1]²} |∇φ|` (mean value theorem) and the
gradient tail (2.16) (`prop3_tail`). Constants differ from DF: here `Var φ_{0,n}(x) = n log 2`
(`variance_phi_delta`; DF: `(n+1) log 2`), and the grid has the `4^n` lower-left corners of the
dyadic squares, at distance `≤ 2 · 2^{-n}` from every point of their square.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two-sided Gaussian tail: `P(|U| ≥ y) ≤ 2 e^{−y²/(2v)}` for `U ~ N(0, v)`, `v > 0`, `y ≥ 0`
(Chernoff, mathlib `measure_ge_le_exp_mul_mgf`). -/
lemma tail_abs_of_hasLaw [IsProbabilityMeasure P] {U : Ω → ℝ} {v : NNReal} (hv : 0 < (v : ℝ))
    (hU : HasLaw U (gaussianReal 0 v) P) {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | y ≤ |U ω|} ≤ 2 * Real.exp (-y ^ 2 / (2 * v)) := by
  have hint : ∀ t, Integrable (fun ω => Real.exp (t * U ω)) P := fun t => by
    have := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hU.map_eq] at this
    exact (integrable_map_measure (by fun_prop) hU.aemeasurable).1 this
  have hmgf : ∀ t, mgf U P t = Real.exp (v * t ^ 2 / 2) := fun t => by
    rw [← mgf_id_map hU.aemeasurable, hU.map_eq, mgf_id_gaussianReal]; ring_nf
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := U) y (t := y / v) (by positivity)
    (hint _)
  have h2 := measure_le_le_exp_mul_mgf (μ := P) (X := U) (-y) (t := -(y / v))
    (by have : 0 ≤ y / v := by positivity
        linarith) (hint _)
  rw [hmgf] at h1 h2
  have e1 : Real.exp (-(y / v) * y) * Real.exp (v * (y / v) ^ 2 / 2) =
      Real.exp (-y ^ 2 / (2 * v)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have e2 : Real.exp (-(-(y / v)) * -y) * Real.exp (v * (-(y / v)) ^ 2 / 2) =
      Real.exp (-y ^ 2 / (2 * v)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have hsub : {ω | y ≤ |U ω|} ⊆ {ω | y ≤ U ω} ∪ {ω | U ω ≤ -y} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; exact h
  calc P.real {ω | y ≤ |U ω|} ≤ P.real ({ω | y ≤ U ω} ∪ {ω | U ω ≤ -y}) := measureReal_mono hsub
    _ ≤ P.real {ω | y ≤ U ω} + P.real {ω | U ω ≤ -y} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-y ^ 2 / (2 * v)) := by linarith

lemma convex_unitBox : Convex ℝ (ferniqueBox 0 1) :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

variable {W : WNSpace → Ω → ℝ}

lemma hasLaw_phi (hW : IsWhiteNoise P W) (a b : ℝ) (x : ℂ) :
    HasLaw (phi W a b x) (gaussianReal 0 (Real.pi * ‖phiKernelL2 a b x‖ ^ 2).toNNReal) P := by
  have hl := hW.hasLaw ![phiKernelL2 a b x] ![Real.sqrt Real.pi]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_zero,
    Finset.sum_singleton] at hl
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt Real.pi_pos.le] at hl
  exact hl.congr (Eventually.of_forall fun ω => rfl)

/-- **DDDF Prop. 2, (2.10)** (`tightness.tex` l. 299–305; DF Lemma 10.1, l. 1823–1858): there is
`C > 0` such that for every white noise, every `n ≥ 0`, every continuous modification `Y` of
`φ_{0,n} = φ_{2^{-n},1}` and every `α > 0`,
`P(sup_{[0,1]²} |Y| ≥ α(n + C√n)) ≤ C 4^n e^{−α² n/log 4}`. -/
theorem prop2_tail : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (n : ℕ) (Y : ℂ → Ω → ℝ), (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
    (∀ ω, Continuous fun x => Y x ω) → ∀ α : ℝ, 0 < α →
    P.real {ω | α * (n + C * Real.sqrt n) ≤ ⨆ z : ferniqueBox 0 1, |Y z ω|} ≤
      C * 4 ^ n * Real.exp (-α ^ 2 * n / Real.log 4) := by
  obtain ⟨C₃, σ2, hC₃, hσ2, h3⟩ := prop3_tail
  refine ⟨3 * Real.sqrt σ2 + C₃ + 2, by positivity, ?_⟩
  intro Ω _ P W hW n Y hY hYc α hα
  have := hW.isProbabilityMeasure
  set C := 3 * Real.sqrt σ2 + C₃ + 2 with hC
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2 := Real.log_two_gt_d9
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine measureReal_le_one.trans ?_
    simp only [pow_zero, Nat.cast_zero, mul_zero, neg_mul, zero_div, neg_zero, Real.exp_zero,
      mul_one]
    linarith [Real.sqrt_nonneg σ2]
  set a : ℝ := ((2 : ℝ) ^ n)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have haN : a * 2 ^ n = 1 := inv_mul_cancel₀ (by positivity)
  obtain ⟨Y', -, hY', -, hY'c, -⟩ := exists_C1_modification_phi hW ha ha1
  have hsame := ae_eq_of_continuous_modification (P := P) hYc (fun ω => (hY'c ω).continuous)
    (fun x => (hY x).trans (hY' x).symm)
  set S := ferniqueBox (0 : ℂ) 1
  haveI : Nonempty S := ⟨⟨0, mem_ferniqueBox_self zero_le_one⟩⟩
  set A : Fin (2 ^ n) × Fin (2 ^ n) → Set Ω := fun ik =>
    {ω | α * n ≤ |Y' ⟨a * ik.1, a * ik.2⟩ ω|} with hA
  set B : Set Ω := {ω | α * C * Real.sqrt n / 2 ≤
    ((2 : ℝ) ^ n)⁻¹ * ⨆ z : S, ‖fderiv ℝ (fun x => Y' x ω) z‖} with hB
  set bad : Set Ω := {ω | ¬ ∀ x, Y x ω = Y' x ω}
  have hbad : P.real bad = 0 := by
    simp only [Measure.real, bad, ae_iff.mp hsame, ENNReal.toReal_zero]
  have hsub : {ω | α * (n + C * Real.sqrt n) ≤ ⨆ z : S, |Y z ω|} ⊆
      bad ∪ ((⋃ ik, A ik) ∪ B) := by
    intro ω hω
    by_cases hgood : ∀ x, Y x ω = Y' x ω
    · right
      simp only [mem_ofPred_eq] at hω
      have hYY : (fun x => Y x ω) = fun x => Y' x ω := funext hgood
      simp only [hgood] at hω
      have hc' : Continuous fun z => |Y' z ω| := continuous_abs.comp (hY'c ω).continuous
      obtain ⟨zs, hzs, hmax⟩ := (isCompact_ferniqueBox 0 1).exists_isMaxOn
        ⟨0, mem_ferniqueBox_self zero_le_one⟩ hc'.continuousOn
      have h1 : α * (n + C * Real.sqrt n) ≤ |Y' zs ω| :=
        hω.trans (ciSup_le fun z => hmax z.2)
      obtain ⟨i, k, hik⟩ := exists_dyadic_square n hzs
      set g : ℂ := ⟨a * i, a * k⟩
      have hi : (i : ℝ) ≤ 2 ^ n := by exact_mod_cast i.2.le
      have hk : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast k.2.le
      have hg : g ∈ S := by
        refine ⟨⟨by simp [g]; positivity, ?_⟩, ⟨by simp [g]; positivity, ?_⟩⟩
        · simp only [g, Complex.zero_re, zero_add]; nlinarith
        · simp only [g, Complex.zero_im, zero_add]; nlinarith
      have hcont : Continuous fun z => ‖fderiv ℝ (fun x => Y' x ω) z‖ :=
        continuous_norm.comp ((hY'c ω).continuous_fderiv (by norm_num))
      have hbdd : BddAbove (Set.range fun z : S => ‖fderiv ℝ (fun x => Y' x ω) z‖) := by
        have := (isCompact_ferniqueBox (0 : ℂ) 1).bddAbove_image hcont.continuousOn
        rwa [Set.image_eq_range] at this
      set M := ⨆ z : S, ‖fderiv ℝ (fun x => Y' x ω) z‖
      have hmv := convex_unitBox.norm_image_sub_le_of_norm_fderiv_le
        (f := fun x => Y' x ω) (C := M)
        (fun x _ => ((hY'c ω).differentiable (by norm_num)).differentiableAt)
        (fun x hx => le_ciSup hbdd ⟨x, hx⟩) hg hzs
      have hd : ‖zs - g‖ ≤ 2 * a := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := hik
        simp only [Complex.sub_re, Complex.sub_im, g] at r1 r2 i1 i2 ⊢
        have e1 : |zs.re - a * i| ≤ a := abs_le.2 ⟨by linarith, by linarith⟩
        have e2 : |zs.im - a * k| ≤ a := abs_le.2 ⟨by linarith, by linarith⟩
        linarith
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (le_ciSup hbdd ⟨zs, hzs⟩)
      have h2 : |Y' zs ω| ≤ |Y' g ω| + M * (2 * a) := by
        have := abs_sub_abs_le_abs_sub (Y' zs ω) (Y' g ω)
        rw [← Real.norm_eq_abs (Y' zs ω - Y' g ω)] at this
        nlinarith [mul_le_mul_of_nonneg_left hd hM0]
      by_cases hAk : α * n ≤ |Y' g ω|
      · left; exact Set.mem_iUnion.2 ⟨(i, k), hAk⟩
      · right
        simp only [hB, mem_ofPred_eq]
        rw [← ha_def]
        nlinarith
    · left; exact hgood
  have hA_le : ∀ ik, P.real (A ik) ≤ 2 * Real.exp (-α ^ 2 * n / Real.log 4) := by
    intro ik
    set g : ℂ := ⟨a * ik.1, a * ik.2⟩
    have hl := (hasLaw_phi hW a 1 g).congr (hY' g)
    set v := (Real.pi * ‖phiKernelL2 a 1 g‖ ^ 2).toNNReal
    have hv : (v : ℝ) = n * Real.log 2 := by
      have h1 := (hasLaw_phi hW (P := P) a 1 g).variance_eq
      rw [variance_id_gaussianReal, variance_phi_delta hW ha ha1, ha_def, inv_inv,
        Real.log_pow] at h1
      exact h1.symm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hv0 : 0 < (v : ℝ) := by rw [hv]; positivity
    refine (tail_abs_of_hasLaw hv0 hl (by positivity)).trans (le_of_eq ?_)
    congr 2
    rw [hv, hlog4]
    have : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
  have hB_le : P.real B ≤ C₃ * 4 ^ n * Real.exp (-α ^ 2 * n / Real.log 4) := by
    have hx : 0 ≤ α * C * Real.sqrt n / 2 := by positivity
    refine (h3 hW n Y' hY' hY'c _ hx).trans ?_
    have hCs : 9 * σ2 ≤ C ^ 2 := by
      have hs := Real.sq_sqrt hσ2.le
      have : 3 * Real.sqrt σ2 ≤ C := by rw [hC]; linarith
      nlinarith [Real.sqrt_nonneg σ2]
    have hsn := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hl4 : 0 < Real.log 4 := by rw [hlog4]; linarith
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have : (α * C * Real.sqrt n / 2) ^ 2 = α ^ 2 * C ^ 2 * n / 4 := by
      rw [div_pow, mul_pow, mul_pow, hsn]; ring
    rw [this, neg_div, neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff₀ hl4 (by positivity)]
    have h98 : (8 : ℝ) / 9 ≤ Real.log 4 := by rw [hlog4]; linarith
    have key : 2 * σ2 ≤ C ^ 2 * Real.log 4 / 4 := by nlinarith
    have hp : 0 ≤ α ^ 2 * n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key hp]
  calc P.real {ω | α * (n + C * Real.sqrt n) ≤ ⨆ z : S, |Y z ω|}
      ≤ P.real (bad ∪ ((⋃ ik, A ik) ∪ B)) := measureReal_mono hsub
    _ ≤ P.real bad + (P.real (⋃ ik, A ik) + P.real B) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ 0 + (∑ _ik : Fin (2 ^ n) × Fin (2 ^ n), 2 * Real.exp (-α ^ 2 * n / Real.log 4) +
          C₃ * 4 ^ n * Real.exp (-α ^ 2 * n / Real.log 4)) := by
        rw [hbad]
        gcongr
        exact (measureReal_iUnion_fintype_le A).trans (Finset.sum_le_sum fun ik _ => hA_le ik)
    _ = (2 + C₃) * 4 ^ n * Real.exp (-α ^ 2 * n / Real.log 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, zero_add]
        push_cast
        rw [show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        ring
    _ ≤ C * 4 ^ n * Real.exp (-α ^ 2 * n / Real.log 4) := by
        gcongr
        rw [hC]; linarith [Real.sqrt_nonneg σ2]

end DDDF
end LQGMetric

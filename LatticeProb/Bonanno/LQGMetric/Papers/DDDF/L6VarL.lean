/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6VarL at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6VarH
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

/-!
# DDDF Lemma 6, the low-frequency field `φ_L`: reduction to deterministic kernel bounds

DDDF (arXiv:1904.08021, `tightness.tex` l. 577–640, Step 2 and Step 3 "First term",
"Second term"). `φ_L^{(δ)}(x) = √π [W(lKer x) + W'(gKer x)]` (`phiL`), where `lKer` is the
`W`-kernel (DDDF's `−φ₁ − φ_{2,1} − φ_{2,3}`) and `gKer x = k_{δ,F(x)} 1_{((0,∞)×V)ᶜ}` the
`W'`-kernel (DDDF's `φ_{2,2}`).

* `integral_sq_phiL_sub_le`: `E(φ_L(x) − φ_L(x'))² ≤ 2π (‖lKer x − lKer x'‖² + ‖gKer x − gKer x'‖²)`
  (Itô isometry for `W` and `W'` separately and `(a + b)² ≤ 2a² + 2b²`; DDDF Step 3 bounds the
  three terms `φ₁, φ₂` separately in the same way).
* `variance_phiL_le`: `Var φ_L(x) ≤ 2π (‖lKer x‖² + ‖gKer x‖²)`.
* `coeFn_lKer`: the explicit a.e. form of `lKer` (for the kernel estimates of Step 3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The `W'`-kernel of `φ_L^{(δ)}(x)`: `k_{δ,F(x)}` outside `(0,∞) × V` (DDDF's `φ_{2,2}`). -/
def gKer (h : ConfHyp F U) (δ : ℝ) (x : ℂ) : WNSpace :=
  cutL2 h.measurableSet_pushTarget.compl (phiKernelL2 δ 1 (F x))

/-- The explicit function representing `lKer F U δ x`. -/
def lKerFun (F : ℂ → ℂ) (U : Set ℂ) (δ : ℝ) (x : ℂ) (p : ℝ × ℂ) : ℝ :=
  (timeHigh δ).indicator (pushFunOf F U (phiKernel δ 1 (F x))) p - phiKernel δ 1 x p

lemma coeFn_lKer (h : ConfHyp F U) {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    (lKer F U δ x : ℝ × ℂ → ℝ) =ᵐ[volume] lKerFun F U δ x := by
  have hae : ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)),
      (pushL2 F U (phiKernelL2 δ 1 (F x)) : ℝ × ℂ → ℝ) q =
        pushFunOf F U (phiKernel δ 1 (F x)) q :=
    (coeFn_pushL2 h.1 h.2 h.3 h.4 _).trans
      (pushFunOf_congr h.1 h.2 h.3 h.4 (coeFn_phiKernelL2 δ 1 hδ (F x)))
  filter_upwards [hae, Lp.coeFn_sub (cutL2 (measurableSet_timeHigh δ)
      (pushL2 F U (phiKernelL2 δ 1 (F x)))) (phiKernelL2 δ 1 x),
    coeFn_cutL2 (measurableSet_timeHigh δ) (pushL2 F U (phiKernelL2 δ 1 (F x))),
    coeFn_phiKernelL2 δ 1 hδ x] with p h1 h2 h3 h4
  rw [lKer, h2, Pi.sub_apply, h3, h4, lKerFun]
  by_cases hp : p ∈ timeHigh δ
  · rw [indicator_of_mem hp, indicator_of_mem hp, h1]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma phiL_eq (h : ConfHyp F U) (W W' : WNSpace → Ω → ℝ) (δ : ℝ) (x : ℂ) (ω : Ω) :
    phiL h W W' δ x ω = Real.sqrt Real.pi * (W (lKer F U δ x) ω + W' (gKer h δ x) ω) := rfl

lemma sub_ae {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (f g : WNSpace) :
    W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
  have e : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  filter_upwards [hW.add_ae f ((-1 : ℝ) • g), hW.smul_ae (-1) g] with ω h1 h2
  rw [e, h1, h2]; ring

lemma memLp_two_W {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (f : WNSpace) :
    MemLp (W f) 2 P := by
  have := hW.isProbabilityMeasure
  exact (hW.hasLaw_single f).hasGaussianLaw.memLp_two

lemma integrable_sq_W {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (f : WNSpace) :
    Integrable (fun ω => W f ω ^ 2) P :=
  (memLp_two_W hW f).integrable_sq

/-- `E(√π (W f + W' g))² ≤ 2π (‖f‖² + ‖g‖²)`. -/
lemma integral_sq_pair_le {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P W') (f g : WNSpace) {Y : Ω → ℝ}
    (hY : Y =ᵐ[P] fun ω => Real.sqrt Real.pi * (W f ω + W' g ω)) :
    ∫ ω, Y ω ^ 2 ∂P ≤ 2 * Real.pi * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have hpi := Real.pi_pos
  have hint : Integrable (fun ω => 2 * Real.pi * (W f ω ^ 2 + W' g ω ^ 2)) P :=
    ((integrable_sq_W hW f).add (integrable_sq_W hW' g)).const_mul _
  calc ∫ ω, Y ω ^ 2 ∂P ≤ ∫ ω, 2 * Real.pi * (W f ω ^ 2 + W' g ω ^ 2) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hint ?_
        filter_upwards [hY] with ω hω
        rw [hω, mul_pow, Real.sq_sqrt hpi.le]
        nlinarith [sq_nonneg (W f ω - W' g ω)]
    _ = 2 * Real.pi * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
        rw [integral_const_mul, integral_add (integrable_sq_W hW f) (integrable_sq_W hW' g),
          integral_sq_W hW, integral_sq_W hW']

/-- **Increment of `φ_L`** reduced to the kernels (DDDF Step 3, l. 577–640). -/
theorem integral_sq_phiL_sub_le (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W') (δ : ℝ) (x x' : ℂ) :
    ∫ ω, (phiL h W W' δ x ω - phiL h W W' δ x' ω) ^ 2 ∂P ≤
      2 * Real.pi * (‖lKer F U δ x - lKer F U δ x'‖ ^ 2 + ‖gKer h δ x - gKer h δ x'‖ ^ 2) := by
  refine integral_sq_pair_le hW hW' _ _ ?_
  filter_upwards [sub_ae hW (lKer F U δ x) (lKer F U δ x'),
    sub_ae hW' (gKer h δ x) (gKer h δ x')] with ω h1 h2
  rw [phiL_eq, phiL_eq, h1, h2]; ring

/-- **Variance of `φ_L`** reduced to the kernels. -/
theorem variance_phiL_le (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W') (δ : ℝ) (x : ℂ) :
    Var[phiL h W W' δ x; P] ≤
      2 * Real.pi * (‖lKer F U δ x‖ ^ 2 + ‖gKer h δ x‖ ^ 2) := by
  have := hW.isProbabilityMeasure
  have hm : AEStronglyMeasurable (phiL h W W' δ x) P :=
    (((hW.measurable _).add (hW'.measurable _)).const_mul _).aestronglyMeasurable
  refine (variance_le_expectation_sq hm).trans ?_
  exact integral_sq_pair_le hW hW' _ _ (Eventually.of_forall fun ω => phiL_eq h W W' δ x ω)

end DDDF
end LQGMetric

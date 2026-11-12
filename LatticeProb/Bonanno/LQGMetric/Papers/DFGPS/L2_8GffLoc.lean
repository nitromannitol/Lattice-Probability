/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffLoc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8Couple
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Ratio
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Localized metrics of `h` and of `h̊` are bi-Lipschitz (DFGPS L2.8, T:886–887)

DFGPS (arXiv:1905.00380, T:886–887): "Since `h − h̊` is a.s. equal to a continuous function on a
neighborhood of `[0,1]²`, we infer from (eqn-localized-property) that a.s. the metrics
`D̂^ε_{h̊}(·,·;[0,1]²)` and `D̂^ε_h(·,·;[0,1]²)` are bi-Lipschitz equivalent with (random)
`ε`-independent Lipschitz constants." With the Markov coupling `markov_zb_coupling`
(`h − h_r(z) = 𝔥 + h̊`, `𝔥|_V` given by a harmonic function `g`):

* `testOnOf` / `restrictTo_testOnOf` : a test function on `ℂ` supported in `V` as an element of
  `𝓓(V)`;
* `integral_locTest_le_one` : `0 ≤ ∫ ψ_ε(z − ·) p_{ε²/2}(z, ·) ≤ 1`;
* `abs_locMollify_sub_le` : if `h + c = 𝔥 + h̊`, `𝔥 = g` on `V`, `|g| ≤ B` on `K ⊆ V` and
  `B̄_{√ε}(x) ⊆ K`, then `|ĥ*_ε(x) − h̊̂*_ε(x)| ≤ |c| + B` (eqn-localized-property: `ĥ*_ε` only
  sees the field near `x`);
* `lfppLocOn_le_of_decomp` : the corresponding bi-Lipschitz bound for `D̂^ε(·,·;S)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric.DFGPS

open LFPP

/-- a test function on `ℂ` supported in `V`, as an element of `𝓓(V)` -/
def testOnOf (V : Opens ℂ) (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ V) : TestOn V where
  toFun := φ
  contDiff' := φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport
  tsupport_subset' := hφ

lemma restrictTo_testOnOf (V : Opens ℂ) (h : DistC) (φ : TestC)
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ V) : restrictTo V h (testOnOf V φ hφ) = h φ := by
  change h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) _) = h φ
  congr 1
  ext x
  simp [TestFunction.monoCLM_apply, testOnOf]

lemma locTest_nonneg (ε : ℝ) (hε : 0 < ε) (z w : ℂ) : 0 ≤ locTest ε hε z w :=
  mul_nonneg (locBump_nonneg ε hε _) (heatKernel_nonneg _ (by positivity) z w)

lemma integrable_locTest (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    Integrable (locTest ε hε z : ℂ → ℝ) :=
  (locTest ε hε z).continuous.integrable_of_hasCompactSupport (locTest ε hε z).hasCompactSupport

lemma integral_locTest_le_one (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ∫ w, locTest ε hε z w ≤ 1 := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  rw [← integral_heatKernel _ hs z]
  refine integral_mono (integrable_locTest ε hε z) (integrable_heatKernel _ hs z) fun w => ?_
  show locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w ≤ heatKernel (ε ^ 2 / 2) z w
  exact mul_le_of_le_one_left (heatKernel_nonneg _ hs.le z w) (locBump_le_one ε hε _)

/-- **eqn-localized-property for the Markov decomposition.** -/
theorem abs_locMollify_sub_le {V : Opens ℂ} {h hh hz : DistC} {c : ℝ}
    (hsum : addConst h c = hh + hz) {g : ℂ → ℝ}
    (hg : ∀ φ : TestOn V, restrictTo V hh φ = ∫ x, g x * φ x) {K : Set ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hgB : ∀ y ∈ K, |g y| ≤ B) (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hball : closedBall x (Real.sqrt ε) ⊆ K) :
    |locMollify ε hε h x - locMollify ε hε hz x| ≤ |c| + B := by
  set φ := locTest ε hε x
  have hsupp : tsupport (φ : ℂ → ℝ) ⊆ K := (tsupport_locTest_subset ε hε x).trans hball
  have hφV : tsupport (φ : ℂ → ℝ) ⊆ V := hsupp.trans hKV
  have e1 : h φ + c * ∫ w, φ w = hh φ + hz φ := by
    have := congrArg (fun d : DistC => d φ) hsum
    simp only [addConst, addFun, ContinuousLinearMap.add_apply, ofCont_apply,
      ContinuousMap.const_apply] at this
    rw [← this, integral_mul_const, mul_comm]
  have e2 : hh φ = ∫ w, g w * φ w := by
    rw [← restrictTo_testOnOf V hh φ hφV, hg]; rfl
  have hI0 : 0 ≤ ∫ w, φ w := integral_nonneg fun w => locTest_nonneg ε hε x w
  have hI1 : ∫ w, φ w ≤ 1 := integral_locTest_le_one ε hε x
  have hgφ : |∫ w, g w * φ w| ≤ B := by
    have h1 : ‖∫ w, g w * φ w‖ ≤ ∫ w, B * φ w := by
      refine norm_integral_le_of_norm_le ((integrable_locTest ε hε x).const_mul B)
        (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (locTest_nonneg ε hε x w)]
      by_cases hw : w ∈ K
      · exact mul_le_mul_of_nonneg_right (hgB w hw) (locTest_nonneg ε hε x w)
      · have : φ w = 0 := image_eq_zero_of_notMem_tsupport fun h' => hw (hsupp h')
        rw [this, mul_zero, mul_zero]
    rw [Real.norm_eq_abs, integral_const_mul] at h1
    exact h1.trans (mul_le_of_le_one_right hB hI1)
  have hd : locMollify ε hε h x - locMollify ε hε hz x = hh φ - c * ∫ w, φ w := by
    show h φ - hz φ = _
    linarith
  rw [hd, e2]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hI0]
  have : |c| * ∫ w, φ w ≤ |c| := mul_le_of_le_one_right (abs_nonneg c) hI1
  linarith

end LQGMetric.DFGPS

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatMollifyPoint at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Pointwise a.s. existence of `h*_ε(z)` for the whole-plane GFF (task P2-FHEAT, part 2a)

For `IsWholePlaneGFF h P`, `ε ≠ 0` and a fixed `z ∈ ℂ`, almost surely the truncated pairings
`⟨h, p_{ε²/2}(z,·) χ_n⟩` converge, i.e. the limit in `heatMollify ε (h ω) z` exists
(GM (1.2), `uniqueness-final.tex` l. 170–177; FOUNDATIONS §3: "the truncation differences are
pairings with test functions whose Gaussian-tailed kernel beats the logarithmic growth of the
GFF").

The GFF is only specified on mean-zero test functions, so a test function `φ` is split as
`φ = (φ − (∫φ) ρ) + (∫φ) ρ` with the fixed reference bump `ρ = refTest` (`∫ρ = 1`); the second
part contributes `(∫φ) ⟨h, ρ⟩` with a fixed finite random variable `⟨h, ρ⟩` (this is how the
additive constant enters: it shifts `h*_ε` by the same constant since `∫ p = 1`).
The truncation differences `D_n = p(z,·)(χ_{n+1} − χ_n)` are `≤ K e^{-n}` and supported in
`B_{n+3}`; the mean-zero parts have variance `≤ poly(n) e^{-2n}` (`abs_logCov_le`), so
`∑ E|⟨h, D_n⟩| < ∞` and the increments are a.s. absolutely summable. Own elementary argument
along the route prescribed in FOUNDATIONS §3 (GM give no proof: footnote l. 212).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric

/-! ### Mean-zero decomposition -/

/-- reference test function `ρ` with `∫ρ = 1`, supported in `B_1(0)` -/
def refTest : TestC := bumpTest 0 0

lemma integral_refTest : ∫ x, refTest x = 1 := ContDiffBump.integral_normed _

lemma refTest_eq_zero (x : ℂ) (hx : 1 ≤ ‖x‖) : refTest x = 0 := by
  have : x ∉ Function.support (refTest : ℂ → ℝ) := by
    show x ∉ Function.support (ContDiffBump.normed _ volume)
    rw [ContDiffBump.support_normed_eq]
    simpa using hx
  simpa using this

lemma exists_bound_refTest : ∃ C, 0 ≤ C ∧ ∀ x, |refTest x| ≤ C := by
  obtain ⟨C, hC⟩ := refTest.hasCompactSupport.exists_bound_of_continuous refTest.continuous
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun x => by simpa using hC x⟩

/-- the mean-zero part `φ − (∫φ) ρ` -/
def meanZeroPart (φ : TestC) : TestC0 :=
  ⟨φ - (∫ x, φ x) • refTest, by
    have h1 : Integrable (φ : ℂ → ℝ) := φ.continuous.integrable_of_hasCompactSupport
      φ.hasCompactSupport
    have h2 : Integrable (refTest : ℂ → ℝ) := refTest.continuous.integrable_of_hasCompactSupport
      refTest.hasCompactSupport
    show ∫ x, (φ x - (∫ x, φ x) * refTest x) = 0
    rw [integral_sub h1 (h2.const_mul _), integral_const_mul, integral_refTest]
    ring⟩

lemma meanZeroPart_apply (φ : TestC) (x : ℂ) :
    (meanZeroPart φ).1 x = φ x - (∫ x, φ x) * refTest x := rfl

lemma pair_eq_meanZeroPart (g : DistC) (φ : TestC) :
    g φ = g (meanZeroPart φ).1 + (∫ x, φ x) * g refTest := by
  show g φ = g (φ - (∫ x, φ x) • refTest) + _
  rw [map_sub, map_smul, smul_eq_mul]
  ring

/-! ### Moments of the GFF pairings -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma IsWholePlaneGFF.memLp_two (hh : IsWholePlaneGFF h P) (φ : TestC0) :
    MemLp (fun ω => h ω φ.1) 2 P :=
  (hh.gaussian.hasGaussianLaw_eval φ).memLp_two

lemma IsWholePlaneGFF.integral_sq (hh : IsWholePlaneGFF h P) (φ : TestC0) :
    ∫ ω, (h ω φ.1) ^ 2 ∂P = logCov φ.1 φ.1 := by
  have hm := (hh.gaussian.aemeasurable φ)
  rw [← hh.covariance_eq φ φ, covariance_self hm, variance_of_integral_eq_zero hm
    (hh.centered φ)]

/-- `E|⟨h,φ⟩| ≤ (logCov(φ,φ)/δ + δ)/2` for every `δ > 0` (AM–GM, avoids square roots). -/
lemma IsWholePlaneGFF.integral_abs_le (hh : IsWholePlaneGFF h P) (φ : TestC0) {δ : ℝ}
    (hδ : 0 < δ) : ∫ ω, |h ω φ.1| ∂P ≤ (logCov φ.1 φ.1 / δ + δ) / 2 := by
  haveI := hh.gaussian.isProbabilityMeasure
  have hL2 := hh.memLp_two φ
  have hint : Integrable (fun ω => ((h ω φ.1) ^ 2 / δ + δ) / 2) P :=
    ((hL2.integrable_sq.div_const δ).add (integrable_const δ)).div_const 2
  calc ∫ ω, |h ω φ.1| ∂P ≤ ∫ ω, ((h ω φ.1) ^ 2 / δ + δ) / 2 ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hint
          (Eventually.of_forall fun ω => ?_)
        have hx := sq_nonneg (|h ω φ.1| - δ)
        rw [sub_sq, sq_abs] at hx
        show |h ω φ.1| ≤ ((h ω φ.1) ^ 2 / δ + δ) / 2
        rw [div_add' _ _ _ hδ.ne', div_div, le_div_iff₀ (by positivity)]
        nlinarith
    _ = (logCov φ.1 φ.1 / δ + δ) / 2 := by
        rw [integral_div, integral_add (hL2.integrable_sq.div_const δ) (integrable_const δ),
          integral_div, hh.integral_sq, integral_const]
        simp

/-- summable first moments give a.s. absolute summability -/
lemma ae_summable_of_summable_integral_abs {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Integrable (X n) P) (hs : Summable fun n => ∫ ω, |X n ω| ∂P) :
    ∀ᵐ ω ∂P, Summable fun n => |X n ω| := by
  have hlin : ∫⁻ ω, ∑' n, ENNReal.ofReal |X n ω| ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hX n).abs.aemeasurable.ennreal_ofReal]
    have : ∀ n, ∫⁻ ω, ENNReal.ofReal |X n ω| ∂P = ENNReal.ofReal (∫ ω, |X n ω| ∂P) :=
      fun n => (ofReal_integral_eq_lintegral_ofReal (hX n).abs
        (Eventually.of_forall fun _ => abs_nonneg _)).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => abs_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum fun n =>
    (hX n).abs.aemeasurable.ennreal_ofReal) hlin] with ω hω
  have h1 : (∑' n, ((|X n ω|).toNNReal : ENNReal)) ≠ ⊤ := by
    simpa [ENNReal.ofReal] using hω.ne
  have h2 := ENNReal.tsum_coe_ne_top_iff_summable.1 h1
  have h3 := NNReal.summable_coe.2 h2
  simpa [Real.coe_toNNReal _ (abs_nonneg _)] using h3

/-! ### Decay of the truncation differences -/

lemma heatTrunc_succ_sub_eq_zero (s : ℝ) (z : ℂ) (n : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (n : ℝ) + 1) :
    heatTrunc s z (n + 1) w - heatTrunc s z n w = 0 := by
  have h1 : (cutoff (n + 1) : ℂ → ℝ) w = 1 := (cutoff (n + 1)).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, dist_zero_right]; show ‖w‖ ≤ ((n + 1 : ℕ) : ℝ) + 1; push_cast
    linarith)
  have h2 : (cutoff n : ℂ → ℝ) w = 1 := (cutoff n).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hw)
  simp [heatTrunc_apply, h1, h2]

lemma heatTrunc_eq_zero (s : ℝ) (z : ℂ) (n : ℕ) (w : ℂ) (hw : (n : ℝ) + 2 ≤ ‖w‖) :
    heatTrunc s z n w = 0 := by
  have : w ∉ Function.support (cutoff n : ℂ → ℝ) := by
    rw [ContDiffBump.support_eq]; simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact hw
  simp [heatTrunc_apply, Function.notMem_support.1 this]

lemma exp_neg_sq_div_le (s t : ℝ) (hs : 0 < s) :
    Real.exp (-t ^ 2 / (2 * s)) ≤ Real.exp (s / 2 - t) := by
  apply Real.exp_le_exp.2
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (t - s)]

/-- `|D_n| ≤ K e^{-n}` with `K = (2πs)⁻¹ e^{s/2 + r}` for `‖z‖ ≤ r`. -/
lemma abs_heatTrunc_succ_sub_le (s : ℝ) (hs : 0 < s) (z : ℂ) (r : ℝ) (hz : ‖z‖ ≤ r) (n : ℕ)
    (w : ℂ) : |heatTrunc s z (n + 1) w - heatTrunc s z n w| ≤
      (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + r) * Real.exp (-(n : ℝ)) := by
  by_cases hw : ‖w‖ ≤ (n : ℝ) + 1
  · rw [heatTrunc_succ_sub_eq_zero s z n w hw, abs_zero]; positivity
  push_neg at hw
  simp only [heatTrunc_apply]
  have hp := heatKernel_nonneg s hs.le z w
  have hc : |(cutoff (n + 1) : ℂ → ℝ) w - (cutoff n : ℂ → ℝ) w| ≤ 1 := by
    have := (cutoff (n + 1)).nonneg (x := w); have := (cutoff (n + 1)).le_one (x := w)
    have := (cutoff n).nonneg (x := w); have := (cutoff n).le_one (x := w)
    rw [abs_le]; constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_nonneg hp]
  refine (mul_le_of_le_one_right hp hc).trans ?_
  unfold heatKernel
  rw [mul_assoc _ (Real.exp (s / 2 + r))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (2 * Real.pi * s)⁻¹)
  refine (exp_neg_sq_div_le s _ hs).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le w z
  linarith

lemma heatTrunc_succ_sub_eq_zero' (s : ℝ) (z : ℂ) (n : ℕ) (w : ℂ) (hw : (n : ℝ) + 3 ≤ ‖w‖) :
    heatTrunc s z (n + 1) w - heatTrunc s z n w = 0 := by
  rw [heatTrunc_eq_zero s z (n + 1) w (by push_cast; linarith),
    heatTrunc_eq_zero s z n w (by linarith), sub_zero]

/-! ### Summability -/

lemma summable_shift_pow_mul_exp (k : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) + 3) ^ k * Real.exp (-(n : ℝ)) := by
  have h := (summable_nat_add_iff 3).2 (Real.summable_pow_mul_exp_neg_nat_mul k one_pos)
  have h2 := h.mul_left (Real.exp 3)
  refine h2.congr fun n => ?_
  push_cast
  rw [show -1 * ((n : ℝ) + 3) = -(n : ℝ) + -3 by ring, Real.exp_add]
  rw [show Real.exp 3 * (((n : ℝ) + 3) ^ k * (Real.exp (-(n : ℝ)) * Real.exp (-3))) =
    ((n : ℝ) + 3) ^ k * Real.exp (-(n : ℝ)) * (Real.exp 3 * Real.exp (-3)) by ring,
    ← Real.exp_add]
  simp

lemma abs_integral_le_of_bound {φ : ℂ → ℝ} {M R : ℝ} (hR : 0 ≤ R) (hφ : ∀ x, |φ x| ≤ M)
    (hφR : ∀ x, R < ‖x‖ → φ x = 0) : |∫ x, φ x| ≤ M * (Real.pi * R ^ 2) := by
  have hB : volume (closedBall (0 : ℂ) R) < ⊤ := measure_closedBall_lt_top
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (g := (closedBall (0 : ℂ) R).indicator fun _ => M)
    ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hB.ne))
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
  · by_cases hx : x ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem hx, Real.norm_eq_abs]; exact hφ x
    · rw [indicator_of_notMem hx, hφR x (by simpa using hx), norm_zero]
  · rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
      measureReal_def, volume_closedBall_toReal R hR]; ring

/-- **a.s. absolute summability of pairings with exponentially small test functions**
supported in `B_{n+3}`. -/
theorem IsWholePlaneGFF.ae_summable_abs_of_decay (hh : IsWholePlaneGFF h P) (φ : ℕ → TestC)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ (n : ℕ) (w : ℂ), |φ n w| ≤ K * Real.exp (-(n : ℝ)))
    (hs : ∀ (n : ℕ) (w : ℂ), (n : ℝ) + 3 ≤ ‖w‖ → φ n w = 0) :
    ∀ᵐ ω ∂P, Summable fun n => |h ω (φ n)| := by
  have := hh.gaussian.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_bound_refTest
  set I : ℕ → ℝ := fun n => ∫ x, φ n x with hI
  set t : ℕ → ℝ := fun n => (n : ℝ) + 3 with ht
  have ht1 : ∀ n, 1 ≤ t n := fun n => by simp only [ht]; linarith [n.cast_nonneg (α := ℝ)]
  have hsupp : ∀ n w, t n < ‖w‖ → φ n w = 0 := fun n w hw => hs n w hw.le
  have hIb : ∀ n, |I n| ≤ K * Real.exp (-(n : ℝ)) * (Real.pi * t n ^ 2) := fun n =>
    abs_integral_le_of_bound (by linarith [ht1 n]) (hb n) (hsupp n)
  -- the mean-zero parts
  set M : ℕ → ℝ := fun n => K * Real.exp (-(n : ℝ)) * (1 + Real.pi * t n ^ 2 * C) with hM
  have hmzb : ∀ n w, |(meanZeroPart (φ n)).1 w| ≤ M n := by
    intro n w
    rw [meanZeroPart_apply]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul (hIb n) (hC w) (abs_nonneg _) (by positivity)
    simp only [hM]
    nlinarith [hb n w]
  have hmzs : ∀ n w, t n < ‖w‖ → (meanZeroPart (φ n)).1 w = 0 := by
    intro n w hw
    rw [meanZeroPart_apply, hsupp n w hw, refTest_eq_zero w (by linarith [ht1 n]), mul_zero,
      sub_zero]
  set A : ℝ := K ^ 2 * (1 + Real.pi * C) ^ 2 * Real.pi * (2 * Real.pi + logBallConst)
  have hC1 := logBallConst_nonneg
  have hvar : ∀ n, logCov (meanZeroPart (φ n)).1 (meanZeroPart (φ n)).1 / Real.exp (-(n : ℝ))
      ≤ A * (t n ^ 9 * Real.exp (-(n : ℝ))) := by
    intro n
    have hb' := (le_abs_self _).trans (abs_logCov_le (by linarith [ht1 n]) (hmzb n) (hmzb n)
      (hmzs n) (hmzs n))
    rw [div_le_iff₀ (Real.exp_pos _)]
    refine hb'.trans ?_
    have e1 : 1 + Real.pi * t n ^ 2 * C ≤ (1 + Real.pi * C) * t n ^ 2 := by
      have : 1 ≤ t n ^ 2 := one_le_pow₀ (ht1 n)
      nlinarith [Real.pi_pos]
    have e2 : 2 * Real.pi * t n ^ 3 + logBallConst ≤ (2 * Real.pi + logBallConst) * t n ^ 3 := by
      have : 1 ≤ t n ^ 3 := one_le_pow₀ (ht1 n)
      nlinarith [Real.pi_pos]
    have e0 : 0 ≤ 1 + Real.pi * t n ^ 2 * C := by
      have := Real.pi_pos; have := ht1 n; positivity
    have e3 : 2 * t n * (Real.pi * t n ^ 2) + logBallConst =
        2 * Real.pi * t n ^ 3 + logBallConst := by ring
    rw [e3]
    calc M n * M n * (Real.pi * t n ^ 2) * (2 * Real.pi * t n ^ 3 + logBallConst)
        = K ^ 2 * (1 + Real.pi * t n ^ 2 * C) ^ 2 * (Real.pi * t n ^ 2) *
            (2 * Real.pi * t n ^ 3 + logBallConst) *
              (Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ))) := by simp only [hM]; ring
      _ ≤ K ^ 2 * ((1 + Real.pi * C) * t n ^ 2) ^ 2 * (Real.pi * t n ^ 2) *
          ((2 * Real.pi + logBallConst) * t n ^ 3) *
            (Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ))) := by
          have := Real.pi_pos
          gcongr
      _ = A * (t n ^ 9 * Real.exp (-(n : ℝ))) * Real.exp (-(n : ℝ)) := by ring
  -- first moments of the mean-zero parts
  have hE : Summable fun n => ∫ ω, |h ω (meanZeroPart (φ n)).1| ∂P := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => abs_nonneg _)
      (fun n => (hh.integral_abs_le _ (Real.exp_pos (-(n : ℝ)))).trans ?_)
      ((((summable_shift_pow_mul_exp 9).mul_left A).add
        (Real.summable_exp_neg_nat)).div_const 2)
    have := hvar n
    simp only [ht] at this
    have e : Real.exp (-(n : ℝ)) = Real.exp (-1 * (n : ℝ)) := by ring_nf
    linarith [show Real.exp (-1 * (n : ℝ)) = Real.exp (-(n : ℝ)) by ring_nf]
  have hint : ∀ n, Integrable (fun ω => h ω (meanZeroPart (φ n)).1) P := fun n =>
    (hh.memLp_two _).integrable one_le_two
  filter_upwards [ae_summable_of_summable_integral_abs hint hE] with ω hω
  have hdet : Summable fun n => |I n| * |h ω refTest| :=
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hIb
      (((summable_shift_pow_mul_exp 2).mul_left (K * Real.pi)).congr fun n => by
        simp only [ht]; ring)).mul_right _
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) (hω.add hdet)
  rw [pair_eq_meanZeroPart (h ω) (φ n)]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]

/-- **Pointwise a.s. existence of `h*_ε(z)`**: for fixed `z`, a.s. the truncated pairings
converge, hence to `heatMollify ε (h ω) z`. -/
theorem IsWholePlaneGFF.ae_tendsto_heatMollify (hh : IsWholePlaneGFF h P) (ε : ℝ) (hε : ε ≠ 0)
    (z : ℂ) : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => h ω (heatTrunc (ε ^ 2 / 2) z n)) atTop
      (𝓝 (heatMollify ε (h ω) z)) := by
  set s := ε ^ 2 / 2
  have hs : 0 < s := by positivity
  set φ : ℕ → TestC := fun n => heatTrunc s z (n + 1) - heatTrunc s z n
  have hdec := hh.ae_summable_abs_of_decay φ (K := (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + ‖z‖))
    (by positivity) (fun n w => abs_heatTrunc_succ_sub_le s hs z ‖z‖ le_rfl n w)
    (fun n w hw => heatTrunc_succ_sub_eq_zero' s z n w hw)
  filter_upwards [hdec] with ω hω
  have hsum : Summable fun n => h ω (heatTrunc s z (n + 1)) - h ω (heatTrunc s z n) := by
    refine Summable.of_norm (hω.congr fun n => ?_)
    simp only [φ, map_sub, Real.norm_eq_abs]
  have hlim := (hsum.hasSum.tendsto_sum_nat).const_add (h ω (heatTrunc s z 0))
  simp_rw [Finset.sum_range_sub (fun n => h ω (heatTrunc s z n)), add_sub_cancel] at hlim
  have hlim' : Tendsto (fun n : ℕ => h ω (heatTrunc s z n)) atTop
      (𝓝 (h ω (heatTrunc s z 0) + ∑' n, (h ω (heatTrunc s z (n + 1)) -
        h ω (heatTrunc s z n)))) := by
    exact hlim
  exact tendsto_nhds_limUnder ⟨_, hlim'⟩

end LQGMetric

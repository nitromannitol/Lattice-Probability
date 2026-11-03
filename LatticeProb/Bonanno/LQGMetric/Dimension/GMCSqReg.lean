/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqReg at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCov
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqLip
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity

/-!
# The regularized circle average of the square GFF equals the circle average (P2-GMC, WP-24)

For `hX : IsZeroBoundaryGFFOn openSquare X P` and a circle `∂B(t, r)` well inside `𝕍`:

* `variance_circle_sub_le` : `Var(h_r(d) − h_r(t)) ≤ (2/r + 2C) ‖d − t‖` (circles in a compact
  convex `K ⊆ 𝕍`, `C` the Lipschitz constant of `hS` on `K`);
* `avgReg_ae_eq` : a.s. `avgReg (X ω) k t = X ω (fc(t, 2^{-k}))`, i.e. QZ's regularization
  (limit along dyadic centres) is not junk.

This is the square analogue of QZ `AreaExist.ae_avgReg_spec` (there via a continuous
modification); here the per-point statement suffices and follows from summable `L¹` increments
(QZ `AreaExist.ae_tendsto_of_L1_rate`) and Fatou. Own adaptation of the QZ argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal ComplexConjugate

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- `(E|Z|)² ≤ Var Z` for a centred square-integrable `Z` -/
lemma integral_abs_sq_le {Z : Ω → ℝ} [IsProbabilityMeasure P] (hZ : MemLp Z 2 P)
    (h0 : ∫ ω, Z ω ∂P = 0) : (∫ ω, |Z ω| ∂P) ^ 2 ≤ Var[Z; P] := by
  have hA : MemLp (fun ω => |Z ω|) 2 P := hZ.abs
  have h1 := variance_nonneg (fun ω => |Z ω|) P
  rw [variance_eq_sub hA] at h1
  rw [variance_eq_sub hZ]
  have e : P[(fun ω => |Z ω|) ^ 2] = P[Z ^ 2] := by
    congr 1; funext ω; simp [sq_abs]
  rw [e] at h1
  have e2 : P[Z] = 0 := h0
  rw [e2]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  linarith

lemma memLp_circle (hX : IsZeroBoundaryGFFOn openSquare X P) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ openSquare) : MemLp (fun ω => X ω (foldedCircle z r)) 2 P :=
  (hX.gaussian.hasGaussianLaw_eval
    ⟨_, isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall hr hB) hr⟩).memLp_two

lemma integral_circle (hX : IsZeroBoundaryGFFOn openSquare X P) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ openSquare) : ∫ ω, X ω (foldedCircle z r) ∂P = 0 :=
  hX.centered _ (isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall hr hB) hr)

/-- **`L²` continuity of circle averages in the centre** -/
theorem variance_circle_sub_le (hX : IsZeroBoundaryGFFOn openSquare X P) {K : Set ℂ}
    (hKU : K ⊆ openSquare) {C : ℝ} (hC : ∀ a ∈ K, ∀ b ∈ K, ∀ b' ∈ K, |hS a b - hS a b'| ≤ C * ‖b - b'‖)
    {d t : ℂ} {r : ℝ} (hr : 0 < r) (hd : closedBall d r ⊆ K) (ht : closedBall t r ⊆ K) :
    Var[fun ω => X ω (foldedCircle d r) - X ω (foldedCircle t r); P] ≤
      (2 / r + 2 * C) * ‖d - t‖ := by
  have hP : IsProbabilityMeasure P := (hX.gaussian.hasGaussianLaw_eval
    ⟨_, isAdmissibleDual_openSquare_foldedCircle
      (inSq_of_closedBall hr (hd.trans hKU)) hr⟩).isProbabilityMeasure
  have hdK : d ∈ K := hd (mem_closedBall_self hr.le)
  have htK : t ∈ K := ht (mem_closedBall_self hr.le)
  have hB₁ := hd.trans hKU
  have hB₂ := ht.trans hKU
  rw [variance_fun_sub (memLp_circle hX hr hB₁) (memLp_circle hX hr hB₂),
    ← covariance_self (memLp_circle hX hr hB₁).aemeasurable,
    ← covariance_self (memLp_circle hX hr hB₂).aemeasurable,
    circleCov_same hX hr hr hB₁ hB₁, circleCov_same hX hr hr hB₂ hB₂,
    circleCov_eq_kernel hX hr hr hB₁ hB₂, max_self]
  -- lower bound for the cross covariance
  have hcongr : (fun x => ∫ y, greenH (sqM x) (sqM y) ∂circleUnif t r) =ᵐ[circleUnif d r]
      fun x => -Real.log (max r ‖t - x‖) + hS x t := by
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif d hr.le] with x hx
    rw [integral_greenH_sqM_circle (hB₁ hx) hr hB₂]
  have hcont : ContinuousOn (fun x => -Real.log (max r ‖t - x‖)) (closedBall d r) :=
    ((continuous_const.max (continuous_const.sub continuous_id).norm).continuousOn.log
      fun x _ => (lt_max_of_lt_left hr).ne').neg
  have hmeas : Measurable fun x : ℂ => -Real.log (max r ‖t - x‖) :=
    (Real.measurable_log.comp (measurable_const.max (measurable_const.sub measurable_id).norm)).neg
  have hi1 := CoordReg.integrable_circleUnif_of_continuousOn hmeas hr.le hcont
  have hi2 : Integrable (fun x => hS x t) (circleUnif d r) := by
    simp_rw [hS_symm _ t]; exact integrable_hS_right (hB₂ (mem_closedBall_self hr.le)) hr.le hB₁
  have hlow : -Real.log (r + ‖d - t‖) ≤ ∫ x, -Real.log (max r ‖t - x‖) ∂circleUnif d r := by
    have := integral_mono_ae (integrable_const (-Real.log (r + ‖d - t‖))) hi1
      ((CoordReg.ae_mem_closedBall_circleUnif d hr.le).mono fun x hx => by
        rw [mem_closedBall, dist_eq_norm] at hx
        have h1 : max r ‖t - x‖ ≤ r + ‖d - t‖ := max_le (by linarith [norm_nonneg (d - t)]) (by
          have := norm_sub_le_norm_sub_add_norm_sub t d x
          rw [norm_sub_rev t d, norm_sub_rev d x] at this; linarith)
        exact neg_le_neg (Real.log_le_log (lt_max_of_lt_left hr) h1))
    simpa using this
  rw [integral_congr_ae hcongr, integral_add hi1 hi2,
    integral_hS_circle_left (hB₂ (mem_closedBall_self hr.le)) hr.le hB₁]
  -- the `hS` terms
  have e1 := hC d hdK d hdK t htK
  have e2 := hC t htK t htK d hdK
  rw [hS_symm t d] at e2
  -- the logarithmic terms
  have hlog : Real.log (r + ‖d - t‖) - Real.log r ≤ ‖d - t‖ / r := by
    rw [← Real.log_div (by positivity) hr.ne']
    rw [add_div, div_self hr.ne']
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + ‖d - t‖ / r by positivity)]
  have hdt : ‖t - d‖ = ‖d - t‖ := norm_sub_rev t d
  rw [hdt] at e2
  have := abs_le.mp e1; have := abs_le.mp e2
  have hdiv : 2 / r * ‖d - t‖ = 2 * (‖d - t‖ / r) := by ring
  nlinarith

/-- `E|Z| ≤ √B` from `Var Z ≤ B` (centred) -/
lemma integral_abs_le_sqrt {Z : Ω → ℝ} [IsProbabilityMeasure P] (hZ : MemLp Z 2 P)
    (h0 : ∫ ω, Z ω ∂P = 0) {B : ℝ} (hB : Var[Z; P] ≤ B) : ∫ ω, |Z ω| ∂P ≤ Real.sqrt B :=
  Real.le_sqrt_of_sq_le ((integral_abs_sq_le hZ h0).trans hB)

/-- **`avgReg` is the circle average, a.s., at each point well inside `𝕍`** -/
theorem avgReg_ae_eq (hX : IsZeroBoundaryGFFOn openSquare X P) {t : ℂ} {k : ℕ}
    (hB : closedBall t (2 * radius k) ⊆ openSquare) :
    (fun ω => avgReg (X ω) k t) =ᵐ[P] fun ω => X ω (foldedCircle t (radius k)) := by
  set r := radius k
  have hr : 0 < r := radius_pos k
  have hP : IsProbabilityMeasure P := (hX.gaussian.hasGaussianLaw_eval
    ⟨_, isAdmissibleDual_openSquare_foldedCircle (inSq_of_closedBall hr
      ((closedBall_subset_closedBall (by linarith)).trans hB)) hr⟩).isProbabilityMeasure
  set K := closedBall t (2 * r)
  obtain ⟨C, hC0, hC⟩ := exists_hS_lip hB (convex_closedBall t _) (isCompact_closedBall t _)
  set Bc := 2 / r + 2 * C
  have hBc : 0 ≤ Bc := by positivity
  set d : ℕ → ℂ := fun n => dyadicRoundC n t
  have hdt : ∀ n, ‖d n - t‖ ≤ 2 * (1 / 2 ^ n) := fun n => CircleCont.norm_dyadicRoundC_sub_le n t
  -- eventually the circles around `d n` lie in `K`
  have hsmall : Tendsto (fun n : ℕ => 2 * (1 / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul 2
    simpa [one_div, inv_pow] using this
  obtain ⟨n₀, hn₀⟩ := (hsmall.eventually (gt_mem_nhds hr)).exists_forall_of_atTop
  have hK : ∀ n, n₀ ≤ n → closedBall (d n) r ⊆ K := fun n hn x hx => by
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle x (d n) t
    rw [dist_eq_norm (d n) t] at this
    linarith [hdt n, hn₀ n hn]
  have htK : closedBall t r ⊆ K := closedBall_subset_closedBall (by linarith)
  set a : ℕ → Ω → ℝ := fun n ω => X ω (foldedCircle (d n) r)
  set b : Ω → ℝ := fun ω => X ω (foldedCircle t r)
  have hma : ∀ n, n₀ ≤ n → MemLp (a n) 2 P := fun n hn => memLp_circle hX hr ((hK n hn).trans hB)
  have hmb : MemLp b 2 P := memLp_circle hX hr (htK.trans hB)
  have hia : ∀ n, n₀ ≤ n → ∫ ω, a n ω ∂P = 0 := fun n hn =>
    integral_circle hX hr ((hK n hn).trans hB)
  have hib : ∫ ω, b ω ∂P = 0 := integral_circle hX hr (htK.trans hB)
  -- step bound
  set q : ℝ := Real.sqrt (1 / 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hqsq : ∀ n : ℕ, (q ^ n) ^ 2 = (1 / 2 : ℝ) ^ n := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have hstep : ∀ n, n₀ ≤ n → ∫ ω, |a (n + 1) ω - a n ω| ∂P ≤ Real.sqrt (4 * Bc) * q ^ n := by
    intro n hn
    have hZ := (hma (n + 1) (by omega)).sub (hma n hn)
    have h0 : ∫ ω, (a (n + 1) ω - a n ω) ∂P = 0 := by
      rw [integral_sub ((hma _ (by omega)).integrable one_le_two) ((hma n hn).integrable one_le_two),
        hia _ (by omega), hia n hn, sub_zero]
    have hV := variance_circle_sub_le hX hB hC hr (hK (n + 1) (by omega)) (hK n hn)
    have hdd : ‖d (n + 1) - d n‖ ≤ 4 * (1 / 2) ^ n := by
      have := norm_sub_le_norm_sub_add_norm_sub (d (n + 1)) t (d n)
      rw [norm_sub_rev t (d n)] at this
      have h1 := hdt (n + 1); have h2 := hdt n
      simp only [one_div, inv_pow, pow_succ] at h1 h2 ⊢
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
      have : ((2 : ℝ) ^ n * 2)⁻¹ = ((2 : ℝ) ^ n)⁻¹ / 2 := by rw [mul_inv]; ring
      rw [this] at h1
      linarith
    have hV' : Var[fun ω => a (n + 1) ω - a n ω; P] ≤ (Real.sqrt (4 * Bc) * q ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hqsq]
      exact hV.trans (by nlinarith)
    have := integral_abs_le_sqrt hZ h0 hV'
    rwa [Real.sqrt_sq (by positivity)] at this
  have hconv := AreaExist.ae_tendsto_of_L1_rate (P := P) (G := a) (k₀ := n₀) hq0 hq1
    (fun n hn => (hma n hn).integrable one_le_two) hstep
  -- identification of the limit: `E|a n − b| → 0`
  have hdist : ∀ n, n₀ ≤ n → ∫ ω, |a n ω - b ω| ∂P ≤ Real.sqrt (Bc * (2 * (1 / 2 ^ n))) := by
    intro n hn
    have hZ := (hma n hn).sub hmb
    have h0 : ∫ ω, (a n ω - b ω) ∂P = 0 := by
      rw [integral_sub ((hma n hn).integrable one_le_two) (hmb.integrable one_le_two), hia n hn,
        hib, sub_zero]
    refine integral_abs_le_sqrt hZ h0 ((variance_circle_sub_le hX hB hC hr (hK n hn) htK).trans ?_)
    exact mul_le_mul_of_nonneg_left (hdt n) hBc
  have hlim0 : Tendsto (fun n => ENNReal.ofReal (∫ ω, |a n ω - b ω| ∂P)) atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => Real.sqrt (Bc * (2 * (1 / 2 ^ n)))) atTop (𝓝 0) := by
      have h' : Tendsto (fun n : ℕ => Bc * (2 * (1 / 2 ^ n))) atTop (𝓝 0) := by
        simpa using hsmall.const_mul Bc
      have := (Real.continuous_sqrt.tendsto 0).comp h'
      rw [Real.sqrt_zero] at this
      exact this
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (squeeze_zero' (Eventually.of_forall fun n =>
      integral_nonneg fun ω => abs_nonneg _) ?_ hs)
    exact (eventually_ge_atTop n₀).mono fun n hn => hdist n hn
  have hmeasd : ∀ n, Measurable fun ω => ENNReal.ofReal |a n ω - b ω| := fun n =>
    ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp ((hX.measurable_coord _).sub (hX.measurable_coord _)))
  have hfat := lintegral_liminf_le (μ := P) (u := atTop) hmeasd
  have hlimEq : liminf (fun n => ∫⁻ ω, ENNReal.ofReal |a n ω - b ω| ∂P) atTop = 0 := by
    have : ∀ᶠ n in atTop, ∫⁻ ω, ENNReal.ofReal |a n ω - b ω| ∂P =
        ENNReal.ofReal (∫ ω, |a n ω - b ω| ∂P) :=
      (eventually_ge_atTop n₀).mono fun n hn => (ofReal_integral_eq_lintegral_ofReal
        ((hma n hn).sub hmb |>.integrable one_le_two).abs
        (ae_of_all _ fun _ => abs_nonneg _)).symm
    rw [liminf_congr this, hlim0.liminf_eq]
  rw [hlimEq] at hfat
  have hzero : ∀ᵐ ω ∂P, liminf (fun n => ENNReal.ofReal |a n ω - b ω|) atTop = 0 := by
    have hm : Measurable fun ω => liminf (fun n => ENNReal.ofReal |a n ω - b ω|) atTop :=
      Measurable.liminf hmeasd
    exact (lintegral_eq_zero_iff hm).mp (le_antisymm hfat (zero_le))
  filter_upwards [hconv, hzero] with ω ⟨l, hl⟩ hz
  have hav : avgReg (X ω) k t = l := hl.limUnder_eq
  have hc : Tendsto (fun n => ENNReal.ofReal |a n ω - b ω|) atTop
      (𝓝 (ENNReal.ofReal |l - b ω|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hl.sub_const _).abs)
  rw [hc.liminf_eq] at hz
  have : |l - b ω| = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (abs_nonneg _)
  rw [hav]
  linarith [abs_eq_zero.mp this]

end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.OuterMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.BallMoment

/-!
# Finite moments of the LQG mass of the unit disc

For a whole-plane GFF circle-average process `H` normalized by `h_1(0) = 0` (measurable coordinates) with LQG measure
`μ` and `0 < q < 4/γ²`: `E[μ(𝔻)^q] < ∞` (`lintegral_ball_one_rpow_lt_top`).

* `q ≤ 1`: Jensen and the first moment, `E μ(𝔻) ≤ 5^{γ²} |B_2(0)|` (Fatou; `Var h_r(z) ≤ −log r + 2 log 5` for
  `|z| ≤ 4`);
* `1 < q < 4/γ²`: the square `[−2, 2)²` is covered by 16 unit squares; on each, Kahane's inequality with an additive
  constant compares the (un-recentred) Riemann sums with the discrete chaos of the reference family (`refZ`), whose
  `q`-th moments are bounded uniformly (LQGMetric `LogCorr.exists_uniform_moment`); then the direct covering, Jensen and
  Fatou (Rhodes–Vargas arXiv:1305.6221 Thm 2.11; [16] (A.6)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter Topology
open LQGMetric.DGMC LQGMetric.DGMC.Neg3 LQGMetric.CircleAvg
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-! ### Upper bounds for circle covariances -/

/-- `circCov z r w s ≤ log max(s, |z − w| + r)`. -/
lemma circCov_le_log {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    circCov z r w s ≤ Real.log (max s (‖z - w‖ + r)) := by
  refine Real.circleAverage_mono_on_of_le_circle
    ((continuous_circLog hs.ne' w).continuousOn.circleIntegrable') fun x hx => ?_
  rw [mem_sphere_iff_norm, abs_of_pos hr] at hx
  rw [circLog_eq_log_max hs]
  refine Real.log_le_log (lt_max_of_lt_left hs) (max_le_max le_rfl ?_)
  calc ‖w - x‖ = ‖(w - z) - (x - z)‖ := by congr 1; abel
    _ ≤ ‖w - z‖ + ‖x - z‖ := norm_sub_le _ _
    _ = ‖z - w‖ + r := by rw [hx, norm_sub_rev]

/-- Upper bound on the circle-average covariance of two circles of the same radius `r ≤ 1` centred in `B̄_4(0)`:
`Cov(h_r(w), h_r(w')) ≤ −log max(r, |w − w'|) + 2 log 5`. -/
lemma gffCircleCov_le_neg_log {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {w w' : ℂ} (hw : ‖w‖ ≤ 4)
    (hw' : ‖w'‖ ≤ 4) :
    LQGDimension.gffCircleCov r w r w' ≤ -Real.log (max r ‖w - w'‖) + 2 * Real.log 5 := by
  rw [gffCircleCov_eq_circCov hr hr, circCov_concentric one_pos one_pos, max_self, Real.log_one]
  have h1 := (circCov_same_radius_bounds hr w w').1
  have h2 : circCov w r 0 1 ≤ Real.log 5 := (circCov_le_log hr one_pos w 0).trans
    (Real.log_le_log (lt_max_of_lt_left one_pos) (max_le (by norm_num) (by rw [sub_zero]; linarith)))
  have h3 : circCov 0 1 w' r ≤ Real.log 5 := (circCov_le_log one_pos hr 0 w').trans
    (Real.log_le_log (lt_max_of_lt_left hr) (max_le (by linarith)
      (by rw [zero_sub, norm_neg]; linarith)))
  linarith

/-- `Var h_r(w) ≤ −log r + 2 log 5` for `r ≤ 1`, `|w| ≤ 4`. -/
lemma gffCircleCov_self_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {w : ℂ} (hw : ‖w‖ ≤ 4) :
    LQGDimension.gffCircleCov r w r w ≤ -Real.log r + 2 * Real.log 5 := by
  have := gffCircleCov_le_neg_log hr hr1 hw hw
  rwa [sub_self, norm_zero, max_eq_left hr.le] at this

/-! ### Kahane comparison for unit squares -/

/-- The un-recentred shifted Riemann sum of the approximation `r^{γ²/2} e^{γ h_r}` (`r = 2^{-k}`) on the unit square
with corner `z₀`. -/
def uM (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (z₀ : ℂ) (k j : ℕ) (v : ℂ) (ω : Ω) : ℝ :=
  ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j * (QuantumZipper.radius k ^ (γ ^ 2 / 2) *
    Real.exp (γ * H (QuantumZipper.radius k) (z₀ + (cpt j i + v)) ω))

/-- **Kahane comparison of the unit-square Riemann sums with the reference family** (`q ≥ 1`, square inside
`B̄_4(0)`). -/
theorem integral_uM_rpow_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} {z₀ : ℂ}
    (hz₀ : ∀ y ∈ unitSq, ‖z₀ + y‖ ≤ 4) {q : ℝ} (hq : 1 ≤ q) (k j : ℕ) {v : ℂ}
    (hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq) :
    ∫ ω, uM γ H z₀ k j v ω ^ q ∂P ≤
      Real.exp (γ ^ 2 * Real.log 5) ^ q * (Real.exp (q * (q - 1) * (γ ^ 2 * (2 * Real.log 5)) / 2) *
        ∫ ω, gM (refZ γ H k) P j (grid j) ω ^ q ∂P) := by
  have hP := hH.isProbabilityMeasure
  set r := QuantumZipper.radius k with hr_def
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set a₀ := QuantumZipper.radius 2 with ha₀_def
  have ha₀ : a₀ = 1 / 4 := radius_two
  set r₀ := QuantumZipper.radius (2 + k) with hr₀_def
  have hr₀ : 0 < r₀ := QuantumZipper.radius_pos _
  have hr₀a : r₀ ≤ a₀ := by
    rw [hr₀_def, radius_add]
    exact mul_le_of_le_one_right (QuantumZipper.radius_pos 2).le
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hne : Nonempty ↥(grid j) := LQGMetric.DGMC.grid_nonempty j
  set pX : ↥(grid j) → ℂ := fun i => z₀ + (cpt j i + v)
  set pY : ↥(grid j) → ℂ := fun i => sqCorner 0 a₀ + a₀ • clampC (cpt j i)
  have hpX : ∀ i, ‖pX i‖ ≤ 4 := fun i => hz₀ _ (hv i i.2)
  have hpY : ∀ i, ‖pY i - 0‖ ≤ 1 / 2 := fun i =>
    (norm_sqPoint_sub_le 0 (QuantumZipper.radius_pos 2).le (clampC_mem _)).trans
      (by rw [radius_two]; norm_num)
  have hproc : IsGaussianProcess (fun (i : ↥(grid j)) (ω : Ω) => γ • H r (pX i) ω) P :=
    (hH.isGaussianProcess.comp_right fun i : ↥(grid j) =>
      ((⟨r, hr⟩ : Ioi (0 : ℝ)), pX i)).smul fun _ => γ
  have hXv : HasGaussianLaw (fun ω (i : ↥(grid j)) => γ * H r (pX i) ω) P :=
    hasGaussianLaw_fintype hproc id
  have hYv : HasGaussianLaw (fun ω (i : ↥(grid j)) => refZ γ H k (cpt j i) ω) P :=
    hasGaussianLaw_fintype (isGaussianProcess_recentred hH γ one_pos 0 (fun _ => r₀)
      (fun _ => hr₀) (fun y => sqCorner 0 a₀ + a₀ • clampC y)) (fun i : ↥(grid j) => cpt j i)
  have hXm : ∀ i : ↥(grid j), ∫ ω, γ * H r (pX i) ω ∂P = 0 := fun i => by
    rw [integral_const_mul, hH.integral_eq_zero r hr, mul_zero]
  have hYm : ∀ i : ↥(grid j), ∫ ω, refZ γ H k (cpt j i) ω ∂P = 0 := fun i =>
    integral_recentred hH γ one_pos hr₀ 0 _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog5 : Real.log 2 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
  have hcov : ∀ i i' : ↥(grid j),
      cov[fun ω => γ * H r (pX i) ω, fun ω => γ * H r (pX i') ω; P] ≤
      cov[fun ω => refZ γ H k (cpt j i) ω, fun ω => refZ γ H k (cpt j i') ω; P] +
        ((⟨γ ^ 2 * (2 * Real.log 5), by positivity⟩ : ℝ≥0) : ℝ) := by
    intro i i'
    show _ ≤ _ + γ ^ 2 * (2 * Real.log 5)
    have e : cov[fun ω => refZ γ H k (cpt j i) ω, fun ω => refZ γ H k (cpt j i') ω; P] =
        cov[fun ω => γ * (H r₀ (pY i) ω - H 1 0 ω), fun ω => γ * (H r₀ (pY i') ω - H 1 0 ω); P] :=
      rfl
    rw [e, covariance_const_mul_left, covariance_const_mul_right, covariance_const_mul_left,
      covariance_const_mul_right, hH.covariance_eq r hr r hr]
    have h1 := gffCircleCov_le_neg_log hr hr1 (hpX i) (hpX i')
    have h2 := abs_le.1 (abs_cov_recentred_add_log_sub_log_le (P := P) hH one_pos hr₀
      (hr₀a.trans (by rw [ha₀]; norm_num)) (hpY i) (hpY i'))
    set L := Real.log (max ((2 : ℝ)⁻¹ ^ k) ‖cpt j i - cpt j i'‖)
    have hLX : Real.log (max r ‖pX i - pX i'‖) = L := by
      congr 1
      simp only [pX, hr_def, QuantumZipper.radius]
      rw [add_sub_add_left_eq_sub, add_sub_add_right_eq_sub]
    have hLY : Real.log (max r₀ ‖pY i - pY i'‖) = Real.log a₀ + L := by
      rw [norm_smul_sub _ (QuantumZipper.radius_pos 2).le, clampC_eq (cpt_mem_unitSq i.2),
        clampC_eq (cpt_mem_unitSq i'.2), hr₀_def, radius_add,
        ← mul_max_of_nonneg _ _ (QuantumZipper.radius_pos 2).le,
        Real.log_mul (QuantumZipper.radius_pos 2).ne' (lt_max_of_lt_left (by positivity)).ne']
    rw [hLX] at h1
    rw [hLY, Real.log_one] at h2
    have hla₀ : Real.log a₀ = -(2 * Real.log 2) := by
      rw [ha₀, one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    set C2 := cov[fun ω => H r₀ (pY i) ω - H 1 0 ω, fun ω => H r₀ (pY i') ω - H 1 0 ω; P]
    have key : LQGDimension.gffCircleCov r (pX i) r (pX i') ≤ C2 + 2 * Real.log 5 := by linarith
    nlinarith [sq_nonneg γ]
  have hKa := LQGMetric.Kahane.kahane_rpow_le_add_const (Or.inr hq)
    (p := fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) (fun _ => by positivity) hXv hYv hXm hYm _ hcov
  -- normalization: `r^{γ²/2} e^{γ h} ≤ 5^{γ²} e^{X − Var X/2}`
  set A := Real.exp (γ ^ 2 * Real.log 5)
  have hvar : ∀ i : ↥(grid j), Var[fun ω => γ * H r (pX i) ω; P] ≤
      γ ^ 2 * (-Real.log r + 2 * Real.log 5) := fun i => by
    have hm : AEMeasurable (fun ω => γ * H r (pX i) ω) P := hproc.aemeasurable i
    rw [← covariance_self hm, covariance_const_mul_left, covariance_const_mul_right,
      hH.covariance_eq r hr r hr]
    have := gffCircleCov_self_le hr hr1 (hpX i)
    nlinarith [sq_nonneg γ]
  set SX : Ω → ℝ := fun ω => ∑ i : ↥(grid j), (4 : ℝ)⁻¹ ^ j *
    Real.exp (γ * H r (pX i) ω - Var[fun ω => γ * H r (pX i) ω; P] / 2)
  have hSX : ∀ ω, 0 < SX ω := fun ω =>
    Finset.sum_pos (fun _ _ => by positivity) Finset.univ_nonempty
  have hpt : ∀ ω, uM γ H z₀ k j v ω ≤ A * SX ω := fun ω => by
    rw [uM, ← Finset.sum_coe_sort (grid j), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have e1 : (4 : ℝ)⁻¹ ^ j * (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r (pX i) ω)) =
        (4 : ℝ)⁻¹ ^ j * Real.exp (Real.log r * (γ ^ 2 / 2) + γ * H r (pX i) ω) := by
      rw [Real.rpow_def_of_pos hr, Real.exp_add]
    have e2 : A * ((4 : ℝ)⁻¹ ^ j * Real.exp (γ * H r (pX i) ω -
        Var[fun ω => γ * H r (pX i) ω; P] / 2)) =
        (4 : ℝ)⁻¹ ^ j * Real.exp (γ ^ 2 * Real.log 5 + (γ * H r (pX i) ω -
        Var[fun ω => γ * H r (pX i) ω; P] / 2)) := by
      rw [Real.exp_add]; ring
    show (4 : ℝ)⁻¹ ^ j * (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r (pX i) ω)) ≤
      A * ((4 : ℝ)⁻¹ ^ j * Real.exp (γ * H r (pX i) ω - Var[fun ω => γ * H r (pX i) ω; P] / 2))
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := hvar i
    nlinarith
  have huM0 : ∀ ω, 0 ≤ uM γ H z₀ k j v ω := fun ω => Finset.sum_nonneg fun _ _ => by positivity
  have hX : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => γ * H r (pX i) ω) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => γ * H r (pX i) ω) ω i; P] / 2)) ^ q) =
      fun ω => SX ω ^ q := rfl
  have hY : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => refZ γ H k (cpt j i) ω) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => refZ γ H k (cpt j i) ω) ω i; P] / 2)) ^ q) =
      fun ω => gM (refZ γ H k) P j (grid j) ω ^ q := by
    funext ω
    rw [gM, ← Finset.sum_coe_sort (grid j)]
  rw [hX, hY] at hKa
  -- integrability of `SX^q`
  have hSXm : Measurable SX := Finset.measurable_sum _ fun i _ =>
    ((((hHm r _).const_mul γ).sub_const _).exp).const_mul _
  have hw : ∑ i : ↥(grid j), (4 : ℝ)⁻¹ ^ j = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, card_grid_mul]
  have hint : Integrable (fun ω => SX ω ^ q) P := by
    refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ =>
      ((integral_exp_mul_of_hasGaussianLaw (hproc.hasGaussianLaw_eval i) (hXm i) q).1.const_mul
        (((4 : ℝ)⁻¹ ^ j) * Real.exp (-(q * Var[fun ω => γ * H r (pX i) ω; P] / 2)))))
      (hSXm.pow_const q).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hSX ω).le _)]
    have hpm := Real.rpow_arith_mean_le_arith_mean_rpow (s := (Finset.univ : Finset ↥(grid j)))
      (fun _ => (4 : ℝ)⁻¹ ^ j)
      (fun i => Real.exp (γ * H r (pX i) ω - Var[fun ω => γ * H r (pX i) ω; P] / 2))
      (fun _ _ => by positivity) hw (fun i _ => (Real.exp_pos _).le) hq
    refine hpm.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [← Real.exp_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc ∫ ω, uM γ H z₀ k j v ω ^ q ∂P ≤ ∫ ω, A ^ q * SX ω ^ q ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω =>
          Real.rpow_nonneg (huM0 ω) _) (hint.const_mul _) (Eventually.of_forall fun ω => ?_)
        beta_reduce
        rw [← Real.mul_rpow (Real.exp_pos _).le (hSX ω).le]
        exact Real.rpow_le_rpow (huM0 ω) (hpt ω) (by linarith)
    _ = A ^ q * ∫ ω, SX ω ^ q ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hKa (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- **Uniform moments of the unit-square Riemann sums** (`1 < q < 4/γ²`). -/
theorem exists_uniform_moment_uM (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q : ℝ} (hγ : 0 < γ) (hq1 : 1 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ, ∀ (z₀ : ℂ) (k j : ℕ) (v : ℂ), (∀ y ∈ unitSq, ‖z₀ + y‖ ≤ 4) → k ≤ j →
      (∀ i ∈ grid j, cpt j i + v ∈ unitSq) → ∫ ω, uM γ H z₀ k j v ω ^ q ∂P ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (logCorr_refZ hH hHm γ).exists_uniform_moment (by positivity) hq1 hq
  refine ⟨Real.exp (γ ^ 2 * Real.log 5) ^ q * (Real.exp (q * (q - 1) * (γ ^ 2 * (2 * Real.log 5)) / 2) * C₀),
    fun z₀ k j v hz₀ hkj hv => ?_⟩
  refine (integral_uM_rpow_le hH hHm hz₀ hq1.le k j hv).trans ?_
  gcongr
  exact hC₀ k j hkj

lemma uM_pos (γ : ℝ) (z₀ : ℂ) (k j : ℕ) (v : ℂ) (ω : Ω) : 0 < uM γ H z₀ k j v ω :=
  Finset.sum_pos (fun _ _ => mul_pos (by positivity) (mul_pos (Real.rpow_pos_of_pos
    (QuantumZipper.radius_pos _) _) (Real.exp_pos _))) (grid_nonempty j)

lemma measurable_uM (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (z₀ : ℂ) (k j : ℕ) (v : ℂ) :
    Measurable (uM γ H z₀ k j v) :=
  Finset.measurable_sum _ fun _ _ => (((hHm _ _).const_mul γ).exp.const_mul _).const_mul _

/-- `uM^q` is integrable for `q ≥ 1`. -/
lemma integrable_uM_rpow (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (z₀ : ℂ) (k j : ℕ) (v : ℂ) {q : ℝ} (hq : 1 ≤ q) :
    Integrable (fun ω => uM γ H z₀ k j v ω ^ q) P := by
  have hP := hH.isProbabilityMeasure
  set r := QuantumZipper.radius k
  have hr : 0 < r := QuantumZipper.radius_pos _
  set K := r ^ (γ ^ 2 / 2)
  have hK : 0 < K := Real.rpow_pos_of_pos hr _
  have hterm : ∀ i : ℕ × ℕ, Integrable (fun ω =>
      (K * Real.exp (γ * H r (z₀ + (cpt j i + v)) ω)) ^ q) P := by
    intro i
    have hg : HasGaussianLaw (H r (z₀ + (cpt j i + v))) P :=
      hH.isGaussianProcess.hasGaussianLaw_eval (⟨r, hr⟩, _)
    obtain ⟨h1, -⟩ := integral_exp_mul_of_hasGaussianLaw hg (hH.integral_eq_zero r hr _) (q * γ)
    refine (h1.const_mul (K ^ q)).congr (Eventually.of_forall fun ω => ?_)
    simp only
    rw [Real.mul_rpow hK.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  refine Integrable.mono' (integrable_finsetSum (grid j) fun i _ => (hterm i).const_mul ((4 : ℝ)⁻¹ ^ j))
    ((measurable_uM hHm γ z₀ k j v).pow_const q).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (uM_pos (H := H) γ z₀ k j v ω).le _)]
  have hw : ∑ i ∈ grid j, (4 : ℝ)⁻¹ ^ j = 1 := by
    rw [sum_const, nsmul_eq_mul, card_grid_mul]
  exact Real.rpow_arith_mean_le_arith_mean_rpow (s := grid j) (fun _ => (4 : ℝ)⁻¹ ^ j)
    (fun i => K * Real.exp (γ * H r (z₀ + (cpt j i + v)) ω)) (fun _ _ => by positivity) hw
    (fun i _ => by positivity) hq

/-- **Uniform moments of the approximation on a unit square** inside `B̄_4(0)` (`1 < q < 4/γ²`). -/
theorem exists_lintegral_unitSq_rpow_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q : ℝ} (hγ : 0 < γ) (hq1 : 1 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z₀ : ℂ) (k : ℕ), (∀ y ∈ unitSq, ‖z₀ + y‖ ≤ 4) →
      ∫⁻ ω, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ^ q ∂P ≤ C := by
  have hP := hH.isProbabilityMeasure
  obtain ⟨C₀, hC₀⟩ := exists_uniform_moment_uM hH hHm hγ hq1 hq
  set C₁ := max C₀ 0
  refine ⟨ENNReal.ofReal C₁, ENNReal.ofReal_lt_top, fun z₀ k hz₀ => ?_⟩
  set j := k
  set r := QuantumZipper.radius k
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hjm : Measurable (fun p : ℂ × Ω => H r p.1 p.2) := measurable_uncurry_coord hH hHm hr
  set F : Ω → ℂ → ℝ≥0∞ := fun ω w => ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r w ω))
  have hFm : ∀ ω, Measurable (F ω) := fun ω => ENNReal.measurable_ofReal.comp
    (measurable_const.mul (((hjm.comp (measurable_id.prodMk measurable_const)).const_mul γ).exp))
  have hA : ∀ ω, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) = ∫⁻ w in sqQ z₀ 0, F ω w := fun ω => by
    rw [GMSLemma27.lqgApprox, withDensity_apply _ (measurableSet_sqQ _ _), dyadicRadius_eq_radius]
  set W : ℂ → Ω → ℝ≥0∞ := fun t ω => ∑ i ∈ grid j,
    ENNReal.ofReal (QuantumZipper.radius 0 ^ 2 * (4 : ℝ)⁻¹ ^ j) *
      F ω (z₀ + QuantumZipper.radius 0 • cellMap j i t)
  have h2 : ∀ ω, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ≤ ∫⁻ t in cell0, W t ω := fun ω => by
    rw [hA]; exact lintegral_sqQ_le_W (F ω) (hFm ω) z₀ 0 j
  have hrad0 : QuantumZipper.radius 0 = 1 := by simp [QuantumZipper.radius]
  have hWm : Measurable (fun q : ℂ × Ω => W q.1 q.2) := by
    have hterm : ∀ i, Measurable (fun q : ℂ × Ω =>
        F q.2 (z₀ + QuantumZipper.radius 0 • cellMap j i q.1)) := fun i => by
      have hc : Measurable fun q : ℂ × Ω => cellMap j i q.1 := (measurable_cellMap j i).comp measurable_fst
      have hpt : Measurable fun q : ℂ × Ω => z₀ + QuantumZipper.radius 0 • cellMap j i q.1 :=
        measurable_const.add ((measurable_const_smul _).comp hc)
      have hA' : Measurable (fun q : ℂ × Ω =>
          H r (z₀ + QuantumZipper.radius 0 • cellMap j i q.1) q.2) :=
        hjm.comp (hpt.prodMk measurable_snd)
      exact ENNReal.measurable_ofReal.comp ((hA'.const_mul γ).exp.const_mul _)
    exact Finset.measurable_sum _ fun i _ => (hterm i).const_mul _
  have hWeq : ∀ t ω, W t ω = ENNReal.ofReal (uM γ H z₀ k j (vOff j t) ω) := by
    intro t ω
    rw [uM, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F, hrad0, one_smul, one_pow, one_mul, cellMap_eq]
    exact (ENNReal.ofReal_mul (by positivity)).symm
  have hpoint : ∀ t ∈ cell0, ∫⁻ ω, W t ω ^ q ∂P ≤ ENNReal.ofReal C₁ := by
    intro t ht
    set v := vOff j t
    have hv : ∀ i ∈ grid j, cpt j i + v ∈ unitSq := fun i hi => by
      rw [← cellMap_eq]
      exact cell0_subset_unitSq (cell_subset_cell0 hi ((cellMap_mem_cell_iff j i t).2 ht))
    have hint := integrable_uM_rpow hH hHm γ z₀ k j v hq1.le
    calc ∫⁻ ω, W t ω ^ q ∂P = ∫⁻ ω, ENNReal.ofReal (uM γ H z₀ k j v ω ^ q) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hWeq, ENNReal.ofReal_rpow_of_pos (uM_pos (H := H) γ z₀ k j v ω)]
      _ = ENNReal.ofReal (∫ ω, uM γ H z₀ k j v ω ^ q ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
            Real.rpow_nonneg (uM_pos (H := H) γ z₀ k j v ω).le _)).symm
      _ ≤ ENNReal.ofReal C₁ :=
          ENNReal.ofReal_le_ofReal ((hC₀ z₀ k j v hz₀ le_rfl hv).trans (le_max_left _ _))
  calc ∫⁻ ω, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ^ q ∂P
      ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω) ^ q ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (h2 ω) (by linarith)
    _ ≤ ∫⁻ ω, (∫⁻ t in cell0, W t ω ^ q) ∂P :=
        lintegral_mono fun ω =>
          rpow_lintegral_le (hWm.comp (measurable_id.prodMk measurable_const)).aemeasurable hq1
    _ = ∫⁻ t in cell0, ∫⁻ ω, W t ω ^ q ∂P :=
        lintegral_lintegral_swap ((hWm.comp (measurable_snd.prodMk measurable_fst)).pow_const
          q).aemeasurable
    _ ≤ ∫⁻ (_t : ℂ) in cell0, ENNReal.ofReal C₁ :=
        setLIntegral_mono' measurableSet_cell0 hpoint
    _ = ENNReal.ofReal C₁ := by rw [setLIntegral_const, volume_cell0, mul_one]

/-! ### Fatou along the vague convergence -/

/-- The plateau mass of an approximation. -/
def platMass (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (x : ℂ) (ρ : ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (plat x ρ z) ∂(GMSLemma27.lqgApprox γ H k ω)

lemma platMass_eq (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ) (x : ℂ) (ρ : ℝ) (k : ℕ) (ω : Ω) :
    platMass γ H x ρ k ω = ∫⁻ z, ENNReal.ofReal (plat x ρ z) * ENNReal.ofReal
      (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) := by
  have hdr : 0 < GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have hfc : Continuous (plat x ρ) := continuous_plat _ _
  have hcontd : Continuous fun z => H (GMSLemma27.dyadicRadius k) z ω := hH.continuous _ hdr ω
  have hd : Measurable fun z => ENNReal.ofReal (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul (continuous_const.mul hcontd).rexp).measurable
  simp only [platMass, GMSLemma27.lqgApprox]
  rw [lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable
    (g := fun z => ENNReal.ofReal (plat x ρ z)) (ENNReal.measurable_ofReal.comp hfc.measurable).aemeasurable]
  exact lintegral_congr fun z => by simp only [Pi.mul_apply]; exact mul_comm _ _

lemma measurable_platMass_uncurry (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (x : ℂ) (ρ : ℝ) (k : ℕ) :
    Measurable fun p : ℂ × Ω => ENNReal.ofReal (plat x ρ p.1) * ENNReal.ofReal
      (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) p.1 p.2)) := by
  have hdr : 0 < GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have hj := measurable_uncurry_coord hH hHm hdr
  exact (ENNReal.measurable_ofReal.comp ((continuous_plat x ρ).measurable.comp measurable_fst)).mul
    (ENNReal.measurable_ofReal.comp (measurable_const.mul ((hj.const_mul γ).exp)))

lemma measurable_platMass (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (x : ℂ) (ρ : ℝ) (k : ℕ) :
    Measurable (platMass γ H x ρ k) := by
  have e : platMass γ H x ρ k = fun ω => _ := funext (platMass_eq hH γ x ρ k)
  rw [e]
  exact (measurable_platMass_uncurry hH hHm γ x ρ k).lintegral_prod_left'

lemma measurable_lqgApprox_set (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (k : ℕ) {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable fun ω => GMSLemma27.lqgApprox γ H k ω A := by
  have hdr : 0 < GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have hj := measurable_uncurry_coord hH hHm hdr
  have hm : Measurable fun p : ℂ × Ω => ENNReal.ofReal
      (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hj.const_mul γ).exp))
  simp only [GMSLemma27.lqgApprox, withDensity_apply _ hA]
  exact hm.lintegral_prod_left'

/-- `E[r^{γ²/2} e^{γ h_r(z)}] ≤ 5^{γ²}` for `r ≤ 1`, `|z| ≤ 4`. -/
lemma lintegral_dens_le_five (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 4) :
    ∫⁻ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 5)) := by
  have hm : ∀ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) =
      ENNReal.ofReal (r ^ (γ ^ 2 / 2)) * ENNReal.ofReal (Real.exp (γ * H r z ω)) := fun ω =>
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)
  simp_rw [hm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, LQGMetric.DG.lintegral_exp_circleAvg hH hr z γ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv := gffCircleCov_self_le hr hr1 hz
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ γ ^ 2 := sq_nonneg γ
  nlinarith

/-- The first moment of the plateau mass on `B_2(0)`: `E ∫ plat_{0,4} dμ_k ≤ 5^{γ²} |B_2(0)|`. -/
lemma lintegral_platMass_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (k : ℕ) :
    ∫⁻ ω, platMass γ H 0 4 k ω ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 5)) * volume (ball (0 : ℂ) 2) := by
  have hP := hH.isProbabilityMeasure
  have hdr : 0 < GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have hdr1 : GMSLemma27.dyadicRadius k ≤ 1 := by
    rw [dyadicRadius_eq_radius]; exact pow_le_one₀ (by norm_num) (by norm_num)
  simp_rw [platMass_eq hH]
  have hmeas : AEMeasurable (Function.uncurry fun (ω : Ω) (z : ℂ) => ENNReal.ofReal (plat 0 4 z) *
      ENNReal.ofReal (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω))) (P.prod volume) :=
    ((measurable_platMass_uncurry hH hHm γ 0 4 k).comp measurable_swap).aemeasurable
  rw [lintegral_lintegral_swap hmeas]
  calc ∫⁻ z, ∫⁻ ω, ENNReal.ofReal (plat 0 4 z) * ENNReal.ofReal
        (GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (GMSLemma27.dyadicRadius k) z ω)) ∂P
      ≤ ∫⁻ z, (ball (0 : ℂ) 2).indicator (fun _ => ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 5))) z := by
        refine lintegral_mono fun z => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        by_cases hz : z ∈ ball (0 : ℂ) 2
        · rw [indicator_of_mem hz]
          rw [mem_ball, dist_zero_right] at hz
          calc ENNReal.ofReal (plat 0 4 z) * _ ≤ 1 * ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 5)) :=
                mul_le_mul' (ENNReal.ofReal_le_one.2 (plat_le_one _ _ _))
                  (lintegral_dens_le_five hH γ hdr hdr1 (by linarith))
            _ = _ := one_mul _
        · rw [mem_ball, dist_zero_right, not_lt] at hz
          rw [plat_eq_zero (by norm_num) (by rw [sub_zero]; linarith), ENNReal.ofReal_zero, zero_mul]
          exact zero_le
    _ = _ := by rw [lintegral_indicator_const measurableSet_ball]

/-- **Fatou along the vague convergence**: `E μ(B_ρ(x))^q ≤ liminf_k E[(∫ plat d μ_k)^q]`. -/
theorem lintegral_ball_rpow_le_liminf (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} {μ : Ω → Measure ℂ}
    (hμ : GMSLemma27.IsLQGAreaOf γ H μ P) (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω, μ ω (ball x ρ) ^ q ∂P ≤ liminf (fun k => ∫⁻ ω, platMass γ H x (4 * ρ) k ω ^ q ∂P) atTop := by
  have h4 : 0 < 4 * ρ := by positivity
  set f : ℂ → ℝ := plat x (4 * ρ)
  have hfc : Continuous f := continuous_plat _ _
  have hfs : HasCompactSupport f :=
    (isCompact_closedBall x (4 * ρ / 2)).of_isClosed_subset (isClosed_tsupport _) (tsupport_plat h4)
  set Glim : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂(μ ω)
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k => platMass γ H x (4 * ρ) k ω) atTop (𝓝 (Glim ω)) := by
    filter_upwards [hμ] with ω ⟨hlf, hc⟩
    have h1 := (ENNReal.continuous_ofReal.tendsto _).comp (hc f hfc hfs)
    have e1 : ∀ k, ENNReal.ofReal (∫ z, f z ∂(GMSLemma27.lqgApprox γ H k ω)) =
        platMass γ H x (4 * ρ) k ω := fun k => by
      have := isLocallyFiniteMeasure_lqgApprox hH γ k ω
      exact ofReal_integral_plat x h4
    have e2 : ENNReal.ofReal (∫ z, f z ∂(μ ω)) = Glim ω := ofReal_integral_plat x h4
    simp only [Function.comp_def, e1, e2] at h1
    exact h1
  have hballG : ∀ ω, μ ω (ball x ρ) ≤ Glim ω := fun ω => by
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ ball x ρ
    · rw [indicator_of_mem hz, Pi.one_apply]
      rw [mem_ball, dist_eq_norm] at hz
      rw [show f z = 1 from plat_eq_one h4 (by linarith), ENNReal.ofReal_one]
    · rw [indicator_of_notMem hz]
      exact zero_le
  calc ∫⁻ ω, μ ω (ball x ρ) ^ q ∂P ≤ ∫⁻ ω, Glim ω ^ q ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (hballG ω) hq.le
    _ = ∫⁻ ω, liminf (fun k => platMass γ H x (4 * ρ) k ω ^ q) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hconv] with ω hω
        exact (((ENNReal.continuous_rpow_const (y := q)).tendsto _).comp hω).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le fun k => (measurable_platMass hH hHm γ x _ k).pow_const q

/-! ### The unit disc -/

/-- `(∑ f)^q ≤ (#s)^q ∑ f^q` in `ℝ≥0∞`. -/
lemma sum_rpow_le_card_rpow_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {q : ℝ} (hq0 : 0 < q) :
    (∑ i ∈ s, f i) ^ q ≤ (s.card : ℝ≥0∞) ^ q * ∑ i ∈ s, f i ^ q := by
  have hq := hq0.le
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [ENNReal.zero_rpow_of_pos hq0]
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup s hne f
  calc (∑ i ∈ s, f i) ^ q ≤ ((s.card : ℝ≥0∞) * s.sup f) ^ q := by
        refine ENNReal.rpow_le_rpow ?_ hq
        calc ∑ i ∈ s, f i ≤ ∑ _i ∈ s, s.sup f := Finset.sum_le_sum fun i hi => Finset.le_sup hi
          _ = (s.card : ℝ≥0∞) * s.sup f := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ≥0∞) ^ q * f i₀ ^ q := by rw [ENNReal.mul_rpow_of_nonneg _ _ hq, hsup]
    _ ≤ (s.card : ℝ≥0∞) ^ q * ∑ i ∈ s, f i ^ q := by
        gcongr
        exact Finset.single_le_sum (f := fun i => f i ^ q) (fun _ _ => zero_le) hi₀

/-- The 16 integer corners of the unit squares tiling `[−2, 2)²`. -/
def corners16 : Finset ℂ :=
  ((Finset.range 4) ×ˢ (Finset.range 4)).image fun p => ⟨(p.1 : ℝ) - 2, (p.2 : ℝ) - 2⟩

lemma mem_corners16_bound {z₀ : ℂ} (hz₀ : z₀ ∈ corners16) : ∀ y ∈ unitSq, ‖z₀ + y‖ ≤ 4 := by
  intro y hy
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hz₀
  obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
  have ha' : (a : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  have hb' : (b : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.add_re, Complex.add_im]
  have : |(a : ℝ) - 2 + y.re| ≤ 2 := abs_le.2 ⟨by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)], by linarith⟩
  have : |(b : ℝ) - 2 + y.im| ≤ 2 := abs_le.2 ⟨by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)], by linarith⟩
  linarith

lemma ball_two_subset_corners16 : ball (0 : ℂ) 2 ⊆ ⋃ z₀ ∈ corners16, sqQ z₀ 0 := by
  intro w hw
  rw [mem_ball, dist_zero_right] at hw
  have hre : |w.re| < 2 := lt_of_le_of_lt (Complex.abs_re_le_norm w) hw
  have him : |w.im| < 2 := lt_of_le_of_lt (Complex.abs_im_le_norm w) hw
  rw [abs_lt] at hre him
  set a := ⌊w.re + 2⌋₊
  set b := ⌊w.im + 2⌋₊
  have ha : a < 4 := by rw [Nat.floor_lt (by linarith)]; push_cast; linarith
  have hb : b < 4 := by rw [Nat.floor_lt (by linarith)]; push_cast; linarith
  refine mem_iUnion₂.2 ⟨⟨(a : ℝ) - 2, (b : ℝ) - 2⟩, Finset.mem_image.2 ⟨(a, b),
    Finset.mem_product.2 ⟨Finset.mem_range.2 ha, Finset.mem_range.2 hb⟩, rfl⟩, ?_⟩
  show (QuantumZipper.radius 0)⁻¹ • (w - ⟨(a : ℝ) - 2, (b : ℝ) - 2⟩) ∈ cell0
  have hrad0 : QuantumZipper.radius 0 = 1 := by simp [QuantumZipper.radius]
  rw [hrad0, inv_one, one_smul]
  have fa1 := Nat.floor_le (show 0 ≤ w.re + 2 by linarith)
  have fa2 := Nat.lt_floor_add_one (w.re + 2)
  have fb1 := Nat.floor_le (show 0 ≤ w.im + 2 by linarith)
  have fb2 := Nat.lt_floor_add_one (w.im + 2)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Complex.sub_re, Complex.sub_im] <;> linarith

/-- **Finite moments of the LQG mass of the unit disc**, `0 < q < 4/γ²`. -/
theorem lintegral_ball_one_rpow_lt_top (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) {μ : Ω → Measure ℂ}
    (hμ : GMSLemma27.IsLQGAreaOf γ H μ P) {q : ℝ} (hq0 : 0 < q) (hq : q < 4 / γ ^ 2) :
    ∫⁻ ω, μ ω (ball 0 1) ^ q ∂P < ⊤ := by
  have hP := hH.isProbabilityMeasure
  refine (lintegral_ball_rpow_le_liminf hH hHm hμ 0 one_pos hq0).trans_lt ?_
  rw [mul_one]
  -- `platMass ≤ μ_k` on the 16 unit squares
  have hcover : ∀ k ω, platMass γ H 0 4 k ω ≤
      ∑ z₀ ∈ corners16, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) := fun k ω => by
    calc platMass γ H 0 4 k ω ≤ GMSLemma27.lqgApprox γ H k ω (⋃ z₀ ∈ corners16, sqQ z₀ 0) := by
          rw [← lintegral_indicator_one (Finset.measurableSet_biUnion _ fun z₀ _ => measurableSet_sqQ _ _)]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ ball (0 : ℂ) 2
          · rw [indicator_of_mem (ball_two_subset_corners16 hz), Pi.one_apply]
            exact ENNReal.ofReal_le_one.2 (plat_le_one _ _ _)
          · rw [mem_ball, dist_zero_right, not_lt] at hz
            rw [plat_eq_zero (by norm_num) (by rw [sub_zero]; linarith), ENNReal.ofReal_zero]
            exact zero_le
      _ ≤ _ := measure_biUnion_finset_le _ _
  rcases le_or_gt q 1 with hq1 | hq1
  · -- first moment
    have hE := lintegral_platMass_le hH hHm γ
    refine lt_of_le_of_lt (b := (ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 5)) *
        volume (ball (0 : ℂ) 2)) ^ q) (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
      (ENNReal.rpow_lt_top_of_nonneg hq0.le (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (measure_ball_lt_top (μ := volume) (x := (0 : ℂ)) (r := 2))).ne)
    calc ∫⁻ ω, platMass γ H 0 4 k ω ^ q ∂P ≤ (∫⁻ ω, platMass γ H 0 4 k ω ∂P) ^ q :=
          lintegral_rpow_le_rpow_lintegral_of_le_one (measurable_platMass hH hHm γ 0 4 k).aemeasurable
            hq0 hq1
      _ ≤ _ := ENNReal.rpow_le_rpow (hE k) hq0.le
  · obtain ⟨C, hC, hsq⟩ := exists_lintegral_unitSq_rpow_le hH hHm hγ hq1 hq
    refine lt_of_le_of_lt (b := (corners16.card : ℝ≥0∞) ^ q * ((corners16.card : ℝ≥0∞) * C))
      (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le (ENNReal.natCast_ne_top _))
        (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hC))
    calc ∫⁻ ω, platMass γ H 0 4 k ω ^ q ∂P
        ≤ ∫⁻ ω, (corners16.card : ℝ≥0∞) ^ q *
            ∑ z₀ ∈ corners16, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ^ q ∂P :=
          lintegral_mono fun ω => (ENNReal.rpow_le_rpow (hcover k ω) hq0.le).trans
            (sum_rpow_le_card_rpow_mul _ _ hq0)
      _ = (corners16.card : ℝ≥0∞) ^ q *
            ∑ z₀ ∈ corners16, ∫⁻ ω, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ^ q ∂P := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le (ENNReal.natCast_ne_top _)),
            lintegral_finsetSum _ fun z₀ _ =>
              (measurable_lqgApprox_set hH hHm γ k (measurableSet_sqQ z₀ 0)).pow_const q]
      _ ≤ (corners16.card : ℝ≥0∞) ^ q * ((corners16.card : ℝ≥0∞) * C) := by
          gcongr
          calc ∑ z₀ ∈ corners16, ∫⁻ ω, GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ^ q ∂P
              ≤ ∑ _z₀ ∈ corners16, C := Finset.sum_le_sum fun z₀ hz₀ =>
                hsq z₀ k (mem_corners16_bound hz₀)
            _ = (corners16.card : ℝ≥0∞) * C := by rw [Finset.sum_const, nsmul_eq_mul]

end MatedCRTHarmonic.GMCFacts

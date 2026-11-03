/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgAffine at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw

/-!
# Circle averages of `h(r·+z)`: `(h(r·+z))_1(0) = h_r(z)` a.s.

`affineComp r z h` paired with `circBump n 0 1` is `h` paired with
`Φ'_n = r⁻² circBump n 0 1 ((· − z)/r)`, a different mollification of the circle `∂B(z, r)`
(mollifier at scale `r 2^{-n}`). Its log potential is `−log r + logPot (circBump n 0 1) ((x−z)/r)`
(change of variables), which is within `2^{-n}` of `−g_{z,r}(x)`, as is the log potential of
`circBump n z r` (within `2^{-n}/r`). Hence the increments `h(Φ'_n) − h(Φ_n)` have variance
`≤ 2 (1 + 1/r) 2^{-n}` and tend to `0` a.s. (Borel–Cantelli), so the two limits agree
(`ae_circleAvg_affineComp`). Own elementary argument (DS, arXiv:0808.1560, §3.1 take the
circle average as the pairing with the circle measure, for which the identity is a change of
variables).

Corollary (GM, arXiv:1905.00383v3, l. 516 / (1.15) form): for a normalized whole-plane GFF,
`h(r·+z) − h_r(z)` has the law of `h` (`map_affine_sub_circleAvg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real

namespace LQGMetric
namespace CircleAvg

/-- substitution `y = r u + z` in `ℂ` -/
lemma integral_eq_affine (g : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ y, g y = r ^ 2 * ∫ u, g (r • u + z) := by
  have h1 := Measure.integral_comp_smul (volume : Measure ℂ) (fun v => g (v + z)) r
  rw [Complex.finrank_real_complex, integral_add_right_eq_self (fun v => g v) z,
    abs_of_pos (by positivity), smul_eq_mul] at h1
  rw [h1, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- `Φ' = r⁻² φ((· − z)/r)` -/
def affTest (r : ℝ) (z : ℂ) (φ : TestC) : TestC := (r ^ 2)⁻¹ • testAffinePull r z φ

lemma affTest_apply {r : ℝ} (hr : 0 < r) (z : ℂ) (φ : TestC) (y : ℂ) :
    affTest r z φ y = (r ^ 2)⁻¹ * φ ((y - z) / r) := by
  simp [affTest, testAffinePull_apply r z hr.ne']

lemma affine_div {r : ℝ} (hr : 0 < r) (z u : ℂ) : (r • u + z - z) / (r : ℂ) = u := by
  rw [add_sub_cancel_right, Complex.real_smul, mul_div_cancel_left₀]
  exact_mod_cast hr.ne'

lemma integral_affTest {r : ℝ} (hr : 0 < r) (z : ℂ) (φ : TestC) :
    ∫ y, affTest r z φ y = ∫ y, φ y := by
  rw [integral_eq_affine _ hr z]
  simp_rw [affTest_apply hr, affine_div hr]
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma logPot_affTest {r : ℝ} (hr : 0 < r) (z : ℂ) (φ : TestC) (x : ℂ) :
    logPot (affTest r z φ) x = -Real.log r * (∫ y, φ y) + logPot φ ((x - z) / r) := by
  unfold logPot
  rw [integral_eq_affine _ hr z]
  simp_rw [affTest_apply hr, affine_div hr]
  set w := (x - z) / (r : ℂ)
  have hpt : ∀ u, u ≠ w → -Real.log ‖x - (r • u + z)‖ * ((r ^ 2)⁻¹ * φ u) =
      (r ^ 2)⁻¹ * (-Real.log r * φ u + -Real.log ‖w - u‖ * φ u) := by
    intro u hu
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have e : x - (r • u + z) = (r : ℂ) * (w - u) := by
      simp only [w, Complex.real_smul]; field_simp; ring
    have hwu : ‖w - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hu.symm)
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.log_mul hr.ne' hwu]
    ring
  rw [integral_congr_ae ((Measure.ae_ne volume w).mono hpt), integral_const_mul,
    integral_add ((integrable_testC φ).const_mul _) (integrable_log_mul_test φ w),
    integral_const_mul]
  field_simp

lemma circLog_affine {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.log r + circLog 0 1 ((x - z) / r) = circLog z r x := by
  rw [circLog_eq one_ne_zero, circLog_eq hr.ne', Real.log_one, zero_add, inv_one, one_mul,
    zero_sub, norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, norm_sub_rev,
    inv_mul_eq_div]

/-- the mean-zero difference `Φ'_n − Φ_n` -/
def affDiff (n : ℕ) (r : ℝ) (z : ℂ) (hr : 0 < r) : TestC0 :=
  ⟨affTest r z (circBump n 0 1) - circBump n z r, by
    show ∫ x, (affTest r z (circBump n 0 1) x - circBump n z r x) = 0
    rw [integral_sub (integrable_testC _) (integrable_testC _), integral_affTest hr,
      integral_circBump, integral_circBump, sub_self]⟩

lemma abs_logPot_affDiff_le (n : ℕ) {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    |logPot (affDiff n r z hr).1 x| ≤ (1 + 1 / r) * (2 : ℝ)⁻¹ ^ n := by
  show |logPot (⇑(affTest r z (circBump n 0 1) - circBump n z r)) x| ≤ _
  rw [logPot_sub, logPot_affTest hr, integral_circBump, logPot_circBump, logPot_circBump]
  have h1 := abs_integral_bump_circLog_sub_le one_pos n 0 ((x - z) / r)
  have h2 := abs_integral_bump_circLog_sub_le hr n z x
  have h3 := circLog_affine hr z x
  rw [div_one] at h1
  have h4 : (1 + 1 / r) * (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ n + (2 : ℝ)⁻¹ ^ n / r := by ring
  rw [h4]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma affTest_nonneg {r : ℝ} (hr : 0 < r) (z : ℂ) (n : ℕ) (y : ℂ) :
    0 ≤ affTest r z (circBump n 0 1) y := by
  rw [affTest_apply hr]
  exact mul_nonneg (by positivity) (circBump_nonneg _ _ _ _)

theorem logCov_affDiff_le (n : ℕ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    logCov (affDiff n r z hr).1 (affDiff n r z hr).1 ≤ 2 * (1 + 1 / r) * (2 : ℝ)⁻¹ ^ n := by
  set D := affDiff n r z hr
  set c := (1 + 1 / r) * (2 : ℝ)⁻¹ ^ n
  rw [logCov_eq_integral_logPot]
  have hD : ∀ x, |D.1 x| ≤ affTest r z (circBump n 0 1) x + circBump n z r x := by
    intro x
    show |affTest r z (circBump n 0 1) x - circBump n z r x| ≤ _
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (affTest_nonneg hr _ _ _), abs_of_nonneg (circBump_nonneg _ _ _ _)]
  have hb : ∀ x, ‖D.1 x * logPot D.1 x‖ ≤
      (affTest r z (circBump n 0 1) x + circBump n z r x) * c := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hD x) (abs_logPot_affDiff_le n hr z x) (abs_nonneg _)
      (add_nonneg (affTest_nonneg hr _ _ _) (circBump_nonneg _ _ _ _))
  have hint : Integrable fun x => (affTest r z (circBump n 0 1) x + circBump n z r x) * c :=
    ((integrable_testC _).add (integrable_testC _)).mul_const c
  have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
    (norm_integral_le_of_norm_le hint (Eventually.of_forall hb)))
  refine this.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_add (integrable_testC _) (integrable_testC _),
    integral_affTest hr, integral_circBump, integral_circBump]
  simp only [c]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Geometric `L²` bound gives a.s. convergence to `0`.** -/
theorem ae_tendsto_zero_of_sq_le [IsFiniteMeasure P] {Y : ℕ → Ω → ℝ}
    (hint : ∀ n, Integrable (fun ω => Y n ω ^ 2) P) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hb : ∀ n, ∫ ω, Y n ω ^ 2 ∂P ≤ C * q ^ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 0) := by
  set p := Real.sqrt q
  have hp0 : 0 < p := Real.sqrt_pos.mpr hq0
  have hp1 : p < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hq1)
  have hpq : p ^ 2 = q := Real.sq_sqrt hq0.le
  set s : ℕ → Set Ω := fun n => {ω | p ^ n ≤ Y n ω ^ 2}
  have hs : ∀ n, P.real (s n) ≤ C * p ^ n := by
    intro n
    have h1 := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
      (hint n) (p ^ n)
    have h2 : p ^ n * P.real (s n) ≤ p ^ n * (C * p ^ n) := by
      refine h1.trans ((hb n).trans (le_of_eq ?_))
      rw [← hpq, ← pow_mul, mul_comm 2 n, pow_mul, sq]; ring
    exact le_of_mul_le_mul_left h2 (pow_pos hp0 n)
  have hC : 0 ≤ C := by
    have := (measureReal_nonneg (μ := P) (s := s 0)).trans (hs 0)
    simpa using this
  have hsum : ∑' n, P (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal (C * p ^ n)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        ((summable_geometric_of_lt_one hp0.le hp1).mul_left C)]
      exact ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun n => ?_
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hs n)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  set ρ := Real.sqrt p
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hp1)
  have hρp : ρ ^ 2 = p := Real.sq_sqrt hp0.le
  refine squeeze_zero_norm' ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
  filter_upwards [hω] with n hn
  have h1 : Y n ω ^ 2 < p ^ n := by simpa [s] using hn
  have h2 : Y n ω ^ 2 ≤ (ρ ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, hρp]; exact h1.le
  rw [Real.norm_eq_abs]
  exact abs_le_of_sq_le_sq' h2 (pow_nonneg hρ0 n) |>.elim (fun h h' => abs_le.mpr ⟨h, h'⟩)

variable {h : Ω → DistC}

lemma integral_sq_pair (hh : IsWholePlaneGFF h P) (φ : TestC0) :
    Integrable (fun ω => h ω φ.1 ^ 2) P ∧ ∫ ω, h ω φ.1 ^ 2 ∂P = logCov φ.1 φ.1 := by
  have hG := hh.gaussian.hasGaussianLaw_eval φ
  refine ⟨hG.memLp_two.integrable_sq, ?_⟩
  rw [← hh.covariance_eq φ φ, covariance_self hG.aemeasurable,
    variance_eq_integral hG.aemeasurable, hh.centered φ]
  simp

lemma mollAvg_affineComp (g : DistC) (n : ℕ) {r : ℝ} (z : ℂ) :
    mollAvg (affineComp r z g) n 0 1 = g (affTest r z (circBump n 0 1)) := by
  rw [mollAvg_eq, affTest, map_smul, smul_eq_mul]
  rfl

/-- **P2-FINV leaf (b).** `(h(r·+z))_1(0) = h_r(z)` almost surely. -/
theorem ae_circleAvg_affineComp (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, circleAvg (affineComp r z (h ω)) 1 0 = circleAvg (h ω) r z := by
  have := hh.gaussian.isProbabilityMeasure
  have hE : ∀ᵐ ω ∂P, Tendsto (fun n => h ω (affDiff n r z hr).1) atTop (𝓝 0) :=
    ae_tendsto_zero_of_sq_le (C := 2 * (1 + 1 / r)) (q := 2⁻¹)
      (fun n => (integral_sq_pair hh _).1) (by norm_num) (by norm_num)
      fun n => (integral_sq_pair hh _).2.trans_le (logCov_affDiff_le n hr z)
  filter_upwards [ae_tendsto_mollAvg hh z hr, ae_tendsto_mollAvg (hh.affineComp hr z) 0 one_pos,
    hE] with ω ⟨a, ha⟩ ⟨b, hb⟩ hω
  rw [circleAvg_eq_of_tendsto ha, circleAvg_eq_of_tendsto hb]
  have hd : Tendsto (fun n => mollAvg (affineComp r z (h ω)) n 0 1 - mollAvg (h ω) n z r)
      atTop (𝓝 0) := by
    refine hω.congr fun n => ?_
    rw [mollAvg_affineComp, mollAvg_eq]
    show h ω (affTest r z (circBump n 0 1) - circBump n z r) = _
    rw [map_sub]
  have := tendsto_nhds_unique (hb.sub ha) hd
  linarith

/-- GM's form: for a normalized whole-plane GFF, `h(r·+z) − h_r(z)` has the law of `h`. -/
theorem map_affine_sub_circleAvg (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    P.map (fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)) = P.map h := by
  rw [← map_affine_normalized hh hr z]
  refine Measure.map_congr ?_
  filter_upwards [ae_circleAvg_affineComp hh.1 hr z] with ω hω
  rw [hω]

end CircleAvg
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.LogCorrFamily at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.CircleCov
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Sq

/-!
# The recentred circle averages form a log-correlated family, uniformly in the centre and scale

For a whole-plane GFF circle-average process `H` (`IsGFFCircleAverage`), a circle `∂B_ε(z)` and a dyadic square
`Q = z₀ + 2^{-m}[0,1]²` of side `a = 2^{-m} ∈ (ε/8, ε/2]` centred at `z` (`z₀ = sqCorner z a`), the family

  `Z_n(y) = γ (h_{2^{-(m+n)}}(z₀ + 2^{-m} y) − h_ε(z))`, `y ∈ [0,1]²` (`rZ`, `y` clamped to `[0,1]²`)

is `γ²`-log-correlated on `[0,1]²` up to the **universal** constant `4γ² log 2` in the sense of LQGMetric's
`DGMC.LogCorr` (`logCorr_rZ`): `|Cov(Z_n(x), Z_n(y)) + γ² log max(2^{-n}, |x − y|)| ≤ 4γ² log 2`. This is the
quantitative content of the coordinate change (3.15)–(3.16) in the proof of [GHM15, Lemma 3.12]
: the rescaled, recentred field `h(ε · + z) − h_ε(z)` is a normalized
whole-plane GFF, so its GMC is controlled independently of `(z, ε)`. LQGMetric's
`DGMC.LogCorr.exists_uniform_neg_moment` (Berestycki–Powell, Theorem `T:negmom`) then bounds every negative moment of
the discrete chaos uniformly (`NegMoment.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset
open LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-! ### The square centred at `z` -/

/-- The centre `(1 + i)/2` of the unit square. -/
def sqCentre : ℂ := ⟨1 / 2, 1 / 2⟩

/-- The lower-left corner `z − a (1 + i)/2` of the square of side `a` centred at `z`. -/
def sqCorner (z : ℂ) (a : ℝ) : ℂ := z - a • sqCentre

lemma norm_sub_sqCentre_le {y : ℂ} (hy : y ∈ unitSq) : ‖y - sqCentre‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (y - sqCentre).re = y.re - 1 / 2 := by simp [sqCentre]
  have e2 : (y - sqCentre).im = y.im - 1 / 2 := by simp [sqCentre]
  rw [e1, e2]
  have a1 : |y.re - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have a2 : |y.im - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- Points of the square of side `a` centred at `z` lie within `a` of `z`. -/
lemma norm_sqPoint_sub_le (z : ℂ) {a : ℝ} (ha : 0 ≤ a) {y : ℂ} (hy : y ∈ unitSq) :
    ‖(sqCorner z a + a • y) - z‖ ≤ a := by
  have e : (sqCorner z a + a • y) - z = a • (y - sqCentre) := by
    simp only [sqCorner, smul_sub]; abel
  rw [e, norm_smul, Real.norm_of_nonneg ha]
  exact mul_le_of_le_one_right ha (norm_sub_sqCentre_le hy)

/-! ### Gaussianity of recentred families -/

/-- Any family of recentred circle averages `γ (h_{ρ(s)}(x(s)) − h_ε(z))` is a Gaussian process. -/
lemma isGaussianProcess_recentred (hH : LQGDimension.IsGFFCircleAverage H P) {S : Type*} (γ : ℝ)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) (ρ : S → ℝ) (hρ : ∀ s, 0 < ρ s) (x : S → ℂ) :
    IsGaussianProcess (fun s ω => γ * (H (ρ s) (x s) ω - H ε z ω)) P := by
  classical
  exact hH.isGaussianProcess.of_isGaussianProcess fun s =>
    ⟨{((⟨ρ s, hρ s⟩ : Ioi (0 : ℝ)), x s), ((⟨ε, hε⟩ : Ioi (0 : ℝ)), z)},
      { toFun := fun v => γ * (v ⟨(⟨ρ s, hρ s⟩, x s), by simp⟩ - v ⟨(⟨ε, hε⟩, z), by simp⟩)
        map_add' := fun v w => by simp only [Pi.add_apply]; ring
        map_smul' := fun c v => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
      fun ω => by simp⟩

/-- The recentred circle averages are centred. -/
lemma integral_recentred (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (z w : ℂ) :
    ∫ ω, γ * (H r w ω - H ε z ω) ∂P = 0 := by
  have := hH.isProbabilityMeasure
  rw [integral_const_mul, integral_sub ((memLp_two_coord hH hr w).integrable one_le_two)
    ((memLp_two_coord hH hε z).integrable one_le_two), hH.integral_eq_zero r hr w,
    hH.integral_eq_zero ε hε z, sub_zero, mul_zero]

/-! ### The comparison family -/

/-- The recentred family on the square of side `2^{-m}` centred at `z`:
`Z_n(y) = γ (h_{2^{-(m+n)}}(z₀ + 2^{-m} y) − h_ε(z))`, `y` clamped to `[0,1]²`. -/
def rZ (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (z : ℂ) (ε : ℝ) (m n : ℕ) (y : ℂ) (ω : Ω) : ℝ :=
  γ * (H (QuantumZipper.radius (m + n)) (sqCorner z (QuantumZipper.radius m) +
    QuantumZipper.radius m • clampC y) ω - H ε z ω)

/-- `log ε − log a ∈ [log 2, 3 log 2]` for `a ∈ (ε/8, ε/2]`. -/
lemma log_sub_log_bounds {ε a : ℝ} (ha : 0 < a) (haε : a ≤ ε / 2) (haε' : ε / 8 < a) :
    Real.log 2 ≤ Real.log ε - Real.log a ∧ Real.log ε - Real.log a ≤ 3 * Real.log 2 := by
  have hε : 0 < ε := by linarith
  constructor
  · have := Real.log_le_log (by positivity : (0 : ℝ) < 2 * a) (show 2 * a ≤ ε by linarith)
    rw [Real.log_mul two_ne_zero ha.ne'] at this
    linarith
  · have := Real.log_le_log hε (show ε ≤ 8 * a by linarith)
    rw [Real.log_mul (by norm_num) ha.ne', show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith

/-- **The recentred family is `γ²`-log-correlated**, with the universal constant `4 γ² log 2`. -/
theorem logCorr_rZ (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (γ : ℝ) (z : ℂ) {ε : ℝ} {m : ℕ} (hε : 0 < ε) (ha : QuantumZipper.radius m ≤ ε / 2)
    (ha' : ε / 8 < QuantumZipper.radius m) :
    LogCorr (rZ γ H z ε m) P (γ ^ 2) (γ ^ 2 * (4 * Real.log 2)) := by
  set a := QuantumZipper.radius m with ha_def
  have hrm : 0 < a := QuantumZipper.radius_pos m
  have hrad : ∀ n, QuantumZipper.radius (m + n) ≤ a := fun n => by
    rw [radius_add]
    exact mul_le_of_le_one_right hrm.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hpt : ∀ y, ‖(sqCorner z a + a • clampC y) - z‖ ≤ ε / 2 := fun y =>
    (norm_sqPoint_sub_le z hrm.le (clampC_mem y)).trans ha
  refine ⟨fun n => ?_, fun n x => ?_, fun n x => ?_, fun n x y hx hy => ?_⟩
  · exact isGaussianProcess_recentred hH γ hε z (fun _ => QuantumZipper.radius (m + n))
      (fun _ => QuantumZipper.radius_pos _) (fun y => sqCorner z a + a • clampC y)
  · exact (((hHm _ _).sub (hHm _ _)).const_mul γ)
  · exact integral_recentred hH γ hε (QuantumZipper.radius_pos _) z _
  · show |cov[fun ω => γ * (H (QuantumZipper.radius (m + n)) (sqCorner z a + a • clampC x) ω -
        H ε z ω), fun ω => γ * (H (QuantumZipper.radius (m + n)) (sqCorner z a + a • clampC y) ω -
        H ε z ω); P] + γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ _
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have h := abs_cov_recentred_add_log_sub_log_le (P := P) hH hε (QuantumZipper.radius_pos (m + n))
      ((hrad n).trans ha) (hpt x) (hpt y)
    have hL : Real.log (max (QuantumZipper.radius (m + n))
        ‖(sqCorner z a + a • clampC x) - (sqCorner z a + a • clampC y)‖) =
        Real.log a + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖) := by
      rw [norm_smul_sub _ hrm.le, clampC_eq hx, clampC_eq hy, radius_add,
        ← mul_max_of_nonneg _ _ hrm.le,
        Real.log_mul hrm.ne' (lt_max_of_lt_left (by positivity)).ne']
    rw [hL] at h
    obtain ⟨hb1, hb2⟩ := log_sub_log_bounds hrm ha ha'
    set C := cov[fun ω => H (QuantumZipper.radius (m + n)) (sqCorner z a + a • clampC x) ω -
      H ε z ω, fun ω => H (QuantumZipper.radius (m + n)) (sqCorner z a + a • clampC y) ω -
      H ε z ω; P]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have key : |C + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ 4 * Real.log 2 := by
      have := abs_le.1 h
      rw [abs_le]; constructor <;> linarith
    rw [show γ * (γ * C) + γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖) =
      γ ^ 2 * (C + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)) by ring, abs_mul,
      abs_of_nonneg (sq_nonneg γ)]
    exact mul_le_mul_of_nonneg_left key (sq_nonneg γ)

end MatedCRTHarmonic.GMCFacts

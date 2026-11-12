/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatMollifyLip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyPoint
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm

/-!
# Lipschitz bounds and fourth moments for the heat-kernel truncations (P2-FHEAT, part 2b)

* `abs_heatKernel_sub_le`: for `‖w‖ ≥ n+1`, `‖z‖, ‖z'‖ ≤ r`,
  `|p_s(z,w) − p_s(z',w)| ≤ L e^{-n} ‖z − z'‖` (elementary: `|e^{-a} − e^{-b}| ≤ |a−b| e^{-min}`).
* `abs_logCov_meanZeroPart_le`: the variance of the mean-zero part of a test function bounded by
  `B` and supported in `B̄_t` is `≤ mzConst · B² t⁹`.
* `IsWholePlaneGFF.lintegral_pow_four`: Gaussian fourth moments `E|⟨h,φ⟩|⁴ = 3 logCov(φ,φ)²`
  (in the form `gaussianAbsMoment 4`, reused from `QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq`).

Own elementary estimates (FOUNDATIONS §3 route; GM give no proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric

/-! ### Elementary exponential estimates -/

lemma abs_exp_neg_sub_exp_neg_le (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| * Real.exp (-min a b) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (by linarith))),
      abs_of_nonpos (by linarith)]
    have h1 := Real.add_one_le_exp (-(b - a))
    have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    have := Real.exp_pos (-a)
    nlinarith
  · rw [min_eq_right hab, abs_of_nonpos (sub_nonpos.2 (Real.exp_le_exp.2 (by linarith))),
      abs_of_nonneg (by linarith)]
    have h1 := Real.add_one_le_exp (-(a - b))
    have h2 : Real.exp (-a) = Real.exp (-b) * Real.exp (-(a - b)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    have := Real.exp_pos (-b)
    nlinarith

/-- the Lipschitz constant of the truncation differences on `B̄_r` -/
def heatLipConst (s r : ℝ) : ℝ :=
  (2 * Real.pi * s)⁻¹ * (2 * s)⁻¹ * Real.exp (2 * s) * (2 * (1 + r)) * Real.exp r

lemma heatLipConst_nonneg (s r : ℝ) (hs : 0 < s) (hr : 0 ≤ r) : 0 ≤ heatLipConst s r := by
  unfold heatLipConst; positivity

lemma abs_heatKernel_sub_le (s : ℝ) (hs : 0 < s) (r : ℝ) (hr : 0 ≤ r) (z z' : ℂ)
    (hz : ‖z‖ ≤ r) (hz' : ‖z'‖ ≤ r) (n : ℕ) (w : ℂ) (hw : (n : ℝ) + 1 ≤ ‖w‖) :
    |heatKernel s z w - heatKernel s z' w| ≤
      heatLipConst s r * Real.exp (-(n : ℝ)) * ‖z - z'‖ := by
  set t := ‖z - w‖
  set t' := ‖z' - w‖
  set u := min t t'
  have ht : ‖w‖ - r ≤ t := by
    have := norm_sub_norm_le w z; rw [norm_sub_rev] at this; simp only [t]; linarith
  have ht' : ‖w‖ - r ≤ t' := by
    have := norm_sub_norm_le w z'; rw [norm_sub_rev] at this; simp only [t']; linarith
  have hu0 : 0 ≤ u := le_min (norm_nonneg _) (norm_nonneg _)
  have hun : (n : ℝ) + 1 - r ≤ u := le_min (by linarith) (by linarith)
  have htt : |t - t'| ≤ ‖z - z'‖ := by
    have := abs_norm_sub_norm_le (z - w) (z' - w)
    simpa [t, t'] using this
  have hsum : t + t' ≤ 2 * u + ‖z - z'‖ := by
    rcases le_total t t' with h | h
    · have : u = t := min_eq_left h
      rw [this]; linarith [(abs_le.1 htt).1]
    · have : u = t' := min_eq_right h
      rw [this]; linarith [(abs_le.1 htt).2]
  have hzz : ‖z - z'‖ ≤ 2 * r := (norm_sub_le _ _).trans (by linarith)
  have hmin : u ^ 2 / (2 * s) ≤ min (t ^ 2 / (2 * s)) (t' ^ 2 / (2 * s)) := by
    apply le_min <;> gcongr
    · exact min_le_left _ _
    · exact min_le_right _ _
  -- step 1
  have h1 : |heatKernel s z w - heatKernel s z' w| ≤
      (2 * Real.pi * s)⁻¹ * ((2 * s)⁻¹ * (‖z - z'‖ * (2 * u + 2 * r)) *
        Real.exp (-(u ^ 2 / (2 * s)))) := by
    unfold heatKernel
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e := abs_exp_neg_sub_exp_neg_le (t ^ 2 / (2 * s)) (t' ^ 2 / (2 * s))
    simp only [neg_div] at e ⊢
    refine e.trans (mul_le_mul ?_ (Real.exp_le_exp.2 (neg_le_neg hmin)) (by positivity)
      (by positivity))
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * s), div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [sq_sub_sq, abs_mul]
    rw [mul_comm]
    refine mul_le_mul htt ?_ (abs_nonneg _) (norm_nonneg _)
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine h1.trans ?_
  -- step 2: `(2u + 2r) e^{-u²/2s} ≤ 2(1+r) e^{2s} e^{r} e^{-n}`
  have h2 : Real.exp (-(u ^ 2 / (2 * s))) ≤ Real.exp (2 * s - 2 * u) := by
    apply Real.exp_le_exp.2
    rw [neg_le, neg_sub, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (u - 2 * s)]
  have h3 : (2 * u + 2 * r) * Real.exp (-2 * u) ≤ 2 * (1 + r) * Real.exp (-u) := by
    have e1 := Real.add_one_le_exp u
    have e2 : Real.exp (-2 * u) = Real.exp (-u) * Real.exp (-u) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : u * Real.exp (-u) ≤ 1 := by
      have : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-u)]
    have e4 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have k : (2 * u + 2 * r) * Real.exp (-u) ≤ 2 * (1 + r) := by
      have := Real.exp_pos (-u)
      nlinarith
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right k (Real.exp_pos _).le
  have h4 : Real.exp (-u) ≤ Real.exp r * Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; linarith
  have h5 : (2 * u + 2 * r) * Real.exp (-(u ^ 2 / (2 * s))) ≤
      Real.exp (2 * s) * (2 * (1 + r)) * Real.exp r * Real.exp (-(n : ℝ)) := by
    calc (2 * u + 2 * r) * Real.exp (-(u ^ 2 / (2 * s)))
        ≤ (2 * u + 2 * r) * Real.exp (2 * s - 2 * u) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp (2 * s) * ((2 * u + 2 * r) * Real.exp (-2 * u)) := by
          rw [← mul_assoc, mul_comm (Real.exp (2 * s)), mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (2 * s) * (2 * (1 + r) * (Real.exp r * Real.exp (-(n : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left
            (h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity))) (Real.exp_pos _).le
      _ = _ := by ring
  unfold heatLipConst
  have hzz0 := norm_nonneg (z - z')
  calc (2 * Real.pi * s)⁻¹ * ((2 * s)⁻¹ * (‖z - z'‖ * (2 * u + 2 * r)) *
        Real.exp (-(u ^ 2 / (2 * s))))
      = (2 * Real.pi * s)⁻¹ * (2 * s)⁻¹ * ‖z - z'‖ *
          ((2 * u + 2 * r) * Real.exp (-(u ^ 2 / (2 * s)))) := by ring
    _ ≤ (2 * Real.pi * s)⁻¹ * (2 * s)⁻¹ * ‖z - z'‖ *
          (Real.exp (2 * s) * (2 * (1 + r)) * Real.exp r * Real.exp (-(n : ℝ))) := by
        gcongr
    _ = _ := by ring

/-- the truncation difference `D_n(z) = p(z,·)(χ_{n+1} − χ_n)` -/
def heatDiff (s : ℝ) (z : ℂ) (n : ℕ) : TestC := heatTrunc s z (n + 1) - heatTrunc s z n

lemma heatDiff_apply (s : ℝ) (z : ℂ) (n : ℕ) (w : ℂ) :
    heatDiff s z n w = (heatKernel s z w) * ((cutoff (n + 1) : ℂ → ℝ) w - cutoff n w) := by
  simp only [heatDiff]
  show heatKernel s z w * _ - heatKernel s z w * _ = _
  ring

lemma abs_heatDiff_sub_le (s : ℝ) (hs : 0 < s) (r : ℝ) (hr : 0 ≤ r) (z z' : ℂ)
    (hz : ‖z‖ ≤ r) (hz' : ‖z'‖ ≤ r) (n : ℕ) (w : ℂ) :
    |heatDiff s z n w - heatDiff s z' n w| ≤
      heatLipConst s r * Real.exp (-(n : ℝ)) * ‖z - z'‖ := by
  by_cases hw : ‖w‖ ≤ (n : ℝ) + 1
  · have h1 := heatTrunc_succ_sub_eq_zero s z n w hw
    have h2 := heatTrunc_succ_sub_eq_zero s z' n w hw
    have : heatDiff s z n w = 0 := h1
    have : heatDiff s z' n w = 0 := h2
    simp only [*, sub_zero, abs_zero]
    have := heatLipConst_nonneg s r hs hr
    positivity
  push_neg at hw
  rw [heatDiff_apply, heatDiff_apply, ← sub_mul, abs_mul]
  have hc : |(cutoff (n + 1) : ℂ → ℝ) w - (cutoff n : ℂ → ℝ) w| ≤ 1 := by
    have := (cutoff (n + 1)).nonneg (x := w); have := (cutoff (n + 1)).le_one (x := w)
    have := (cutoff n).nonneg (x := w); have := (cutoff n).le_one (x := w)
    rw [abs_le]; constructor <;> linarith
  exact (mul_le_of_le_one_right (abs_nonneg _) hc).trans
    (abs_heatKernel_sub_le s hs r hr z z' hz hz' n w hw.le)

/-! ### Variance of mean-zero parts -/

/-- a fixed bound for `|refTest|` -/
def refC : ℝ := Classical.choose exists_bound_refTest

lemma refC_nonneg : 0 ≤ refC := (Classical.choose_spec exists_bound_refTest).1

lemma abs_refTest_le (x : ℂ) : |refTest x| ≤ refC :=
  (Classical.choose_spec exists_bound_refTest).2 x

/-- the constant in `abs_logCov_meanZeroPart_le` -/
def mzConst : ℝ := (1 + Real.pi * refC) ^ 2 * Real.pi * (2 * Real.pi + logBallConst)

lemma mzConst_nonneg : 0 ≤ mzConst := by
  unfold mzConst; have := refC_nonneg; have := logBallConst_nonneg; positivity

lemma abs_logCov_meanZeroPart_le (ψ : TestC) {B t : ℝ} (hB : 0 ≤ B) (ht : 1 ≤ t)
    (hψ : ∀ w, |ψ w| ≤ B) (hs : ∀ w, t < ‖w‖ → ψ w = 0) :
    |logCov (meanZeroPart ψ).1 (meanZeroPart ψ).1| ≤ mzConst * B ^ 2 * t ^ 9 := by
  have hC := refC_nonneg
  have hIb : |∫ x, ψ x| ≤ B * (Real.pi * t ^ 2) := abs_integral_le_of_bound (by linarith) hψ hs
  set M := B * (1 + Real.pi * t ^ 2 * refC)
  have hmzb : ∀ w, |(meanZeroPart ψ).1 w| ≤ M := by
    intro w
    rw [meanZeroPart_apply]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hIb (abs_refTest_le w) (abs_nonneg _) (by positivity)
    simp only [M]
    nlinarith [hψ w]
  have hmzs : ∀ w, t < ‖w‖ → (meanZeroPart ψ).1 w = 0 := by
    intro w hw
    rw [meanZeroPart_apply, hs w hw, refTest_eq_zero w (by linarith), mul_zero, sub_zero]
  refine (abs_logCov_le (by linarith) hmzb hmzb hmzs hmzs).trans ?_
  have hC1 := logBallConst_nonneg
  have e1 : 1 + Real.pi * t ^ 2 * refC ≤ (1 + Real.pi * refC) * t ^ 2 := by
    have : 1 ≤ t ^ 2 := one_le_pow₀ ht
    nlinarith [Real.pi_pos]
  have e2 : 2 * t * (Real.pi * t ^ 2) + logBallConst ≤ (2 * Real.pi + logBallConst) * t ^ 3 := by
    have : 1 ≤ t ^ 3 := one_le_pow₀ ht
    nlinarith [Real.pi_pos]
  have e0 : 0 ≤ 1 + Real.pi * t ^ 2 * refC := by have := Real.pi_pos; positivity
  have ht0 : 0 ≤ t := by linarith
  calc M * M * (Real.pi * t ^ 2) * (2 * t * (Real.pi * t ^ 2) + logBallConst)
      = B ^ 2 * (1 + Real.pi * t ^ 2 * refC) ^ 2 * (Real.pi * t ^ 2) *
          (2 * t * (Real.pi * t ^ 2) + logBallConst) := by simp only [M]; ring
    _ ≤ B ^ 2 * ((1 + Real.pi * refC) * t ^ 2) ^ 2 * (Real.pi * t ^ 2) *
          ((2 * Real.pi + logBallConst) * t ^ 3) := by
        have := Real.pi_pos
        gcongr
    _ = mzConst * B ^ 2 * t ^ 9 := by unfold mzConst; ring

/-! ### Fourth moments -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma IsWholePlaneGFF.lintegral_pow_four (hh : IsWholePlaneGFF h P) (φ : TestC0) :
    ∫⁻ ω, ENNReal.ofReal (|h ω φ.1| ^ 4) ∂P =
      ENNReal.ofReal ((logCov φ.1 φ.1) ^ 2 * QuantumZipper.gaussianAbsMoment 4) := by
  have hX : Measurable fun ω => h ω φ.1 := (measurable_distOn_apply φ.1).comp hh.measurable
  have hlaw := (hh.gaussian.hasGaussianLaw_eval φ).map_eq_gaussianReal
  have hV : Var[fun ω => h ω φ.1; P] = logCov φ.1 φ.1 := by
    rw [← hh.covariance_eq φ φ, covariance_self (hh.gaussian.aemeasurable φ)]
  have hV0 : 0 ≤ logCov φ.1 φ.1 := hV ▸ variance_nonneg _ _
  simp only [hh.centered φ, hV] at hlaw
  have := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq hX 2 hlaw
  rw [Real.coe_toNNReal _ hV0] at this
  simpa using this

end LQGMetric

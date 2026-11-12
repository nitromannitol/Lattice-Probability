/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA1Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA1Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA1Var2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L1Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Cont

/-!
# Ding–Gwynne Lemma A.1: the increments of `h^U_{1,∞}` (task P2-DG3C)

DG (`metric-comparison-final.tex`, DG:2141–2162): `h^U_{1,∞}(z) = √π ∫_1^∞ ∫ p_U(s/2; z, w) W(dw, ds)`
"admits a continuous modification (Kolmogorov)". Kernel form: `wndKernelL2 U (Ioi 1) z`.

* `norm_sq_tailKernel_sub_le` — `‖k_{1,∞}(x) − k_{1,∞}(c)‖² ≤ 64 R⁴ E(|x − c|)` for
  `U ⊆ B(c₀, R)`, `B(x, 1/10), B(c, 1/10) ⊆ U`, by integrating `lintegral_sq_killedHeat_sub_tail_le`
  (time `s/2 = 1/4 + σ`, `σ ≥ s/4`) against `∫_1^∞ s⁻² ds = 1`.

Own argument (DEVIATIONS DG3B-2: DG only says "easily checked").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ SupTail

/-- The bracket `E(|x − c|)` of the tail increment bound (`q = 1/4`, `ρ = 1/10`). -/
def dgTailE (d : ℝ) : ℝ :=
  2 * (d ^ 2 / (8 * Real.pi * (1 / 4 : ℝ) ^ 2)) +
    2 * ((1 / (4 * Real.pi) + 34992 / (Real.pi * (1 / 10 : ℝ) ^ 6)) * d)

lemma dgTailE_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ dgTailE d := by
  unfold dgTailE; have := Real.pi_pos; positivity

lemma lintegral_Ioi_one_rpow (M : ℝ) (hM : 0 ≤ M) :
    ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (M * s ^ (-2 : ℝ)) = ENNReal.ofReal M := by
  have hi : IntegrableOn (fun s : ℝ => M * s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul M
  rw [← ofReal_integral_eq_lintegral_ofReal hi ((ae_restrict_iff' measurableSet_Ioi).2
    (ae_of_all _ fun s (hs : 1 < s) => by positivity)), integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-- **Tail increments of `h^U_{1,∞}`**. -/
theorem norm_sq_tailKernel_sub_le {U : Set ℂ} (hU : IsOpen U) {c₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hUR : U ⊆ Metric.ball c₀ R) {x c : ℂ} (hx : Metric.ball x (1 / 10) ⊆ U)
    (hc : Metric.ball c (1 / 10) ⊆ U) :
    ‖wndKernelL2 U (Ioi 1) x - wndKernelL2 U (Ioi 1) c‖ ^ 2 ≤ 64 * R ^ 4 * dgTailE ‖x - c‖ := by
  have hpi := Real.pi_pos
  have hE := dgTailE_nonneg (norm_nonneg (x - c))
  have hI : Ioi (1 : ℝ) ⊆ Ioi (1 / 2) := Ioi_subset_Ioi (by norm_num)
  have hmx := memLp_wndKernel hU hR.le hUR measurableSet_Ioi (by norm_num : (0 : ℝ) < 1 / 2) hI x
  have hmc := memLp_wndKernel hU hR.le hUR measurableSet_Ioi (by norm_num : (0 : ℝ) < 1 / 2) hI c
  have ex : wndKernelL2 U (Ioi 1) x = hmx.toLp _ := by
    rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true hmx)]
  have ec : wndKernelL2 U (Ioi 1) c = hmc.toLp _ := by
    rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true hmc)]
  have hae : ((wndKernelL2 U (Ioi 1) x - wndKernelL2 U (Ioi 1) c : WNSpace) : ℝ × ℂ → ℝ)
      =ᵐ[volume] wndKernel U (Ioi 1) x - wndKernel U (Ioi 1) c := by
    rw [ex, ec]
    filter_upwards [Lp.coeFn_sub (hmx.toLp _) (hmc.toLp _), hmx.coeFn_toLp,
      hmc.coeFn_toLp] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    rfl
  rw [norm_sq_eq_of_ae hae]
  have hM : 0 ≤ 64 * R ^ 4 * dgTailE ‖x - c‖ := by positivity
  have hB : ∫⁻ s in Ioi (1 : ℝ), ∫⁻ w, ENNReal.ofReal
      ((killedHeat U (s / 2).toNNReal x w - killedHeat U (s / 2).toNNReal c w) ^ 2) ≤
      ENNReal.ofReal (64 * R ^ 4 * dgTailE ‖x - c‖) := by
    rw [← lintegral_Ioi_one_rpow _ hM]
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_))
    have hs1 : (1 : ℝ) < s := hs
    set σ : ℝ≥0 := (s / 2 - 1 / 4).toNNReal with hσdef
    have hσr : (σ : ℝ) = s / 2 - 1 / 4 := Real.coe_toNNReal _ (by linarith)
    have hσ0 : σ ≠ 0 := by
      intro h; have := congrArg (fun t : ℝ≥0 => (t : ℝ)) h; simp only [hσr] at this
      norm_num at this; linarith
    have hsplit : (s / 2).toNNReal = (1 / 4 : ℝ≥0) + σ := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (by linarith), NNReal.coe_add, hσr]
      norm_num
    have hq : (1 / 4 : ℝ≥0) ≠ 0 := by norm_num
    have h := lintegral_sq_killedHeat_sub_tail_le hU hR hUR (by norm_num : (0 : ℝ) < 1 / 10)
      hx hc hq hσ0
    rw [← hsplit] at h
    refine h.trans ?_
    have hq' : ((1 / 4 : ℝ≥0) : ℝ) = 1 / 4 := by norm_num
    rw [hq']
    have h2 : ∀ a : ℝ, 0 ≤ a → 2 * ENNReal.ofReal a = ENNReal.ofReal (2 * a) := fun a ha => by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    have ha : 0 ≤ ‖x - c‖ ^ 2 / (8 * Real.pi * (1 / 4 : ℝ) ^ 2) := by positivity
    have hb : 0 ≤ (1 / (4 * Real.pi) + 34992 / (Real.pi * (1 / 10 : ℝ) ^ 6)) * ‖x - c‖ := by
      positivity
    rw [h2 _ ha, h2 _ hb, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hσpos : 0 < (σ : ℝ) := by rw [hσr]; linarith
    have hs0 : 0 < s := by linarith
    have hkey : (2 * R ^ 2 / σ) ^ 2 ≤ 64 * R ^ 4 * s ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hs0.le, Real.rpow_two, div_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have hσs : s ≤ 4 * (σ : ℝ) := by rw [hσr]; linarith
      have : s ^ 2 ≤ 16 * (σ : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg R, pow_nonneg (sq_nonneg R) 2]
    have hEe : 2 * (‖x - c‖ ^ 2 / (8 * Real.pi * (1 / 4 : ℝ) ^ 2)) +
        2 * ((1 / (4 * Real.pi) + 34992 / (Real.pi * (1 / 10 : ℝ) ^ 6)) * ‖x - c‖) =
        dgTailE ‖x - c‖ := rfl
    rw [hEe]
    calc (2 * R ^ 2 / σ) ^ 2 * dgTailE ‖x - c‖ ≤ 64 * R ^ 4 * s ^ (-2 : ℝ) * dgTailE ‖x - c‖ :=
          mul_le_mul_of_nonneg_right hkey hE
      _ = 64 * R ^ 4 * dgTailE ‖x - c‖ * s ^ (-2 : ℝ) := by ring
  refine (integral_sq_le_slices ((measurable_wndKernel hU measurableSet_Ioi x).sub
    (measurable_wndKernel hU measurableSet_Ioi c)) measurableSet_Ioi
    (h := fun s w => killedHeat U (s / 2).toNNReal x w - killedHeat U (s / 2).toNNReal c w)
    (fun s w => ?_) hB ENNReal.ofReal_ne_top).trans (le_of_eq (ENNReal.toReal_ofReal hM))
  by_cases hs : s ∈ Ioi (1 : ℝ) <;> simp [wndKernel, hs]

/-! ### Lemma A.1 in white-noise form -/

lemma abs_clamp_sub_le (a c u v : ℝ) :
    |max a (min c u) - max a (min c v)| ≤ |u - v| := by
  rw [max_comm a, max_comm a]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- The coordinatewise clamp of `ℂ` onto `ferniqueBox y b` (a `1`-Lipschitz retraction). -/
def boxClamp (y : ℂ) (b : ℝ) (z : ℂ) : ℂ :=
  ⟨max y.re (min (y.re + b) z.re), max y.im (min (y.im + b) z.im)⟩

lemma boxClamp_mem {y : ℂ} {b : ℝ} (hb : 0 ≤ b) (z : ℂ) : boxClamp y b z ∈ ferniqueBox y b := by
  simp only [ferniqueBox, boxClamp, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩,
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩

lemma boxClamp_of_mem {y : ℂ} {b : ℝ} {z : ℂ} (hz : z ∈ ferniqueBox y b) : boxClamp y b z = z := by
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc] at hz
  apply Complex.ext <;> simp [boxClamp, hz.1.1, hz.1.2, hz.2.1, hz.2.2]

lemma norm_boxClamp_sub_le (y : ℂ) (b : ℝ) (x x' : ℂ) :
    ‖boxClamp y b x - boxClamp y b x'‖ ≤ ‖x - x'‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have h1 := abs_clamp_sub_le y.re (y.re + b) x.re x'.re
  have h2 := abs_clamp_sub_le y.im (y.im + b) x.im x'.im
  simp only [boxClamp, Complex.sub_re, Complex.sub_im]
  have e1 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
  have e2 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
  nlinarith [e1, e2, sq_abs (x.re - x'.re), sq_abs (x.im - x'.im)]

lemma norm_sub_le_of_mem_box {y : ℂ} {b : ℝ} {x c : ℂ} (hx : x ∈ ferniqueBox y b)
    (hc : c ∈ ferniqueBox y b) : ‖x - c‖ ≤ 2 * b := by
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc] at hx hc
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have : |x.re - c.re| ≤ b := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have : |x.im - c.im| ≤ b := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  linarith

/-- The kernel of `(h^U − ĥ^tr)(z) = h^U_{1,∞}(z) + f(z)` (DG:2156), `h^U` the white-noise field
`lim_{t→0} h^U_{t,∞}` of DG:2142–2146. -/
def dgA1Kernel (U : Set ℂ) (z : ℂ) : WNSpace := wndKernelL2 U (Ioi 1) z + kernelU0 U z

/-- (A.3) for `h^U − ĥ^tr` on a box `K` with `B(z, 1/10) ⊆ U` for `z ∈ K`. -/
theorem dg_A1_var_box {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {y : ℂ} {b : ℝ}
    (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ferniqueBox y b, ∀ c ∈ ferniqueBox y b,
      ‖dgA1Kernel U x - dgA1Kernel U c‖ ^ 2 ≤ L * ‖x - c‖ := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hUb
  have hR' : U ⊆ Metric.ball 0 (max R 1) := hR.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hR1 : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨C, hC⟩ := dg_A1_var0 hU hUb
  have hpi := Real.pi_pos
  set a : ℝ := 2 * b / (8 * Real.pi * (1 / 4 : ℝ) ^ 2)
  set k : ℝ := 1 / (4 * Real.pi) + 34992 / (Real.pi * (1 / 10 : ℝ) ^ 6)
  have ha : 0 ≤ a := by positivity
  have hk : 0 ≤ k := by positivity
  set Rm := max R 1
  refine ⟨2 * (64 * Rm ^ 4 * (2 * a + 2 * k)) + 2 * (max C 0 / Real.pi), by positivity,
    fun x hx c hc => ?_⟩
  set d := ‖x - c‖
  have hd : 0 ≤ d := norm_nonneg _
  have hd2 : d ≤ 2 * b := norm_sub_le_of_mem_box hx hc
  have hT := norm_sq_tailKernel_sub_le hU hR1 hR' (hK x hx) (hK c hc)
  have hTE : dgTailE d ≤ (2 * a + 2 * k) * d := by
    have h1 : d ^ 2 / (8 * Real.pi * (1 / 4 : ℝ) ^ 2) ≤ a * d := by
      rw [show a * d = (2 * b * d) / (8 * Real.pi * (1 / 4 : ℝ) ^ 2) by simp only [a]; ring]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    rw [show dgTailE d = 2 * (d ^ 2 / (8 * Real.pi * (1 / 4 : ℝ) ^ 2)) + 2 * (k * d) from rfl]
    nlinarith
  have hV := hC x c (hK x hx) (hK c hc)
  have hV' : ‖kernelU0 U x - kernelU0 U c‖ ^ 2 ≤ max C 0 / Real.pi * d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    nlinarith [le_max_left C 0, mul_le_mul_of_nonneg_right (le_max_left C 0) hd]
  have e : dgA1Kernel U x - dgA1Kernel U c =
      (wndKernelL2 U (Ioi 1) x - wndKernelL2 U (Ioi 1) c) + (kernelU0 U x - kernelU0 U c) := by
    unfold dgA1Kernel; abel
  rw [e]
  have hsq : ∀ u v : WNSpace, ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := fun u v => by
    have := norm_add_le u v
    nlinarith [norm_nonneg (u + v), norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
  refine (hsq _ _).trans ?_
  have hR4 : 0 ≤ 64 * Rm ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left hTE hR4
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- Kolmogorov + Borell–TIS on a box (DG:2156–2164, generic form): if `F` is `½`-Hölder in
`L²` on `K = ferniqueBox y b`, then `√π W(F ·)|_K` has a continuous modification with Gaussian
tail of `max_K`. Off `K` the kernel is replaced by `F ∘ boxClamp` (a `1`-Lipschitz retraction). -/
theorem exists_box_modification_tail (hW : IsWhiteNoise P W) (F : ℂ → WNSpace) {y : ℂ} {b : ℝ}
    (hb : 0 < b) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ ferniqueBox y b, ∀ c ∈ ferniqueBox y b, ‖F x - F c‖ ^ 2 ≤ L * ‖x - c‖) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun z => Y z ω) ∧ (∀ z, Measurable (Y z)) ∧
      (∀ z ∈ ferniqueBox y b, Y z =ᵐ[P] fun ω => Real.sqrt Real.pi * W (F z) ω) ∧
      ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
        P {ω | ¬ ∀ z ∈ ferniqueBox y b, |Y z ω| ≤ A} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  have hpi := Real.pi_pos
  have := hW.isProbabilityMeasure
  set G : ℂ → WNSpace := fun z => F (boxClamp y b z) with hGdef
  have hG : ∀ x x', ‖G x - G x'‖ ^ 2 ≤ L * ‖x - x'‖ := fun x x' =>
    (hL _ (boxClamp_mem hb.le x) _ (boxClamp_mem hb.le x')).trans
      (mul_le_mul_of_nonneg_left (norm_boxClamp_sub_le y b x x') hL0)
  have hGK : ∀ z ∈ ferniqueBox y b, G z = F z := fun z hz => by
    simp only [hGdef, boxClamp_of_mem hz]
  obtain ⟨Y, hYc, hYm, hY⟩ := exists_continuous_modification_of_kernel_half hW G hL0 hG
    (Real.sqrt Real.pi)
  refine ⟨Y, hYc, hYm, fun z hz => by rw [← hGK z hz]; exact hY z, ?_⟩
  have hsq : ∀ u v, ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P = Real.pi * ‖G v - G u‖ ^ 2 := by
    intro u v
    have hae : (fun ω => (Y v ω - Y u ω) ^ 2) =ᵐ[P] fun ω =>
        (Real.sqrt Real.pi * W (G v) ω - Real.sqrt Real.pi * W (G u) ω) ^ 2 := by
      filter_upwards [hY u, hY v] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
  set V : ℝ := Real.pi * (2 * ‖G y‖ ^ 2 + 2 * (L * (2 * b))) + 1
  have hV : 0 < V := by positivity
  have hσ : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hy : y ∈ ferniqueBox y b := by
    simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc]
    exact ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩
  refine gaussian_tail_of_incr (X := Y)
    ((isGaussianProcess_sqrtPi hW G).congr fun x => (hY x).symm)
    (fun v => by rw [integral_congr_ae (hY v)]; exact integral_sqrtPi hW _)
    hb (by positivity : (0 : ℝ) < Real.pi * L + 1) hσ
    (fun ω => (hYc ω).continuousOn) (fun u _ v _ => ?_) (fun v hv => ?_) subset_rfl
  · rw [hsq]
    have h := hG v u
    rw [norm_sub_rev v u] at h
    nlinarith [norm_nonneg (u - v), mul_le_mul_of_nonneg_left h hpi.le]
  · rw [variance_congr (hY v), variance_sqrtPi hW, Real.sq_sqrt hV.le]
    have h1 : ‖G v‖ ≤ ‖G y‖ + ‖G v - G y‖ := by
      have := norm_add_le (G y) (G v - G y); simpa using this
    have h2 := hG v y
    have h3 : ‖v - y‖ ≤ 2 * b := norm_sub_le_of_mem_box hv hy
    have h4 : ‖G v‖ ^ 2 ≤ 2 * ‖G y‖ ^ 2 + 2 * (L * (2 * b)) := by
      nlinarith [norm_nonneg (G v), norm_nonneg (G y), norm_nonneg (G v - G y),
        sq_nonneg (‖G y‖ - ‖G v - G y‖), mul_le_mul_of_nonneg_left h3 hL0]
    nlinarith [mul_le_mul_of_nonneg_left h4 hpi.le]

/-- **DG Lemma A.1** (white-noise form, `K` a box): with `h^U := lim_{t→0} h^U_{t,∞}` built from
the white noise `W` of `ĥ^tr` (DG:2142–2146), `(h^U − ĥ^tr)|_K = √π W(dgA1Kernel U ·)` has a
continuous modification `Y` and `P[max_K |Y| > A] ≤ c₀ e^{−c₁ A²}` for all `A ≥ 0`. Here `K` is a
box all of whose points are at distance `≥ 1/10` from `∂U` (DG: the whole set `K`; see
DEVIATIONS DG3C-1). -/
theorem dg_lemmaA1_wn (hW : IsWhiteNoise P W) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ U) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun z => Y z ω) ∧ (∀ z, Measurable (Y z)) ∧
      (∀ z ∈ ferniqueBox y b, Y z =ᵐ[P] fun ω => Real.sqrt Real.pi * W (dgA1Kernel U z) ω) ∧
      ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
        P {ω | ¬ ∀ z ∈ ferniqueBox y b, |Y z ω| ≤ A} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  obtain ⟨L, hL0, hL⟩ := dg_A1_var_box hU hUb hb hK
  exact exists_box_modification_tail hW _ hb hL0 hL

end DG
end LQGMetric

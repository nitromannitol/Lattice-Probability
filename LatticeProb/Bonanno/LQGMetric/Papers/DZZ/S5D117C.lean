/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3VarBdry
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Perc
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# D117 packet P-SIM (c): (eq-var-compare) for two points and two dyadic scales (P2-DZZSIM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Lemma 3.8 (l. 1218–1233) needs (eq-var-compare):
`|Var ζ⁽¹⁾_{2^{-n}}(v) − Var ζ⁽²⁾_{a 2^{-n}}(θ v)| ≤ b₁`. In the setting of lem-scaling-coupling
(l. 611–624, `ζ⁽ⁱ⁾` with the law of `η`) DZZ leave this implicit. For `η` it holds because the
kernel `p_{𝕍 ∩ B(v, r(s))}(s/2; v, ·)` of `η` (DZZ (eq-def-eta)) is, for `r(s) < ξ` and `v ∈ 𝕍^ξ`,
the kernel of the ball `B(v, r(s))`, which does not depend on `v` (translation invariance of the
Brownian bridge), and the band `(a²ε², ε²)` of times contributes at most `log a⁻¹`
(`p_s(v, v) = (2πs)⁻¹`). Own elementary proof of this unstated step (DEC-117 P-SIM); for `h̃` it
then follows from `dzz_var_compare` (S3L10Var).

* `killedHeat_ball_center`: `p_{B(v,R)}(t; v, v) = p_{B(0,R)}(t; 0, 0)`;
* `norm_etaKernelL2_sq`: `‖K_I(v)‖² = ∫_I p_{𝕍 ∩ B(v,r(s))}(s; v, v) ds`;
* `etaVar_two_point_le`: `|Var η_{2^{-n}}(z) − Var η_{r 2^{-n}}(w)| ≤ B + log r⁻¹` on `𝕍^ξ`;
* `tildeVar_sub_etaVar_le`: `0 ≤ Var h̃_ε − Var η_ε ≤ b₁` at every scale (not only dyadic);
* `tildeVar_two_point_le`: the two-point bound for `Var h̃`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat SupTail

/-- translation invariance of the killed heat kernel of a ball on the diagonal -/
lemma killedHeat_ball_center (v : ℂ) (R : ℝ) (t : ℝ≥0) :
    killedHeat (Metric.ball v R) t v v = killedHeat (Metric.ball 0 R) t 0 0 := by
  unfold killedHeat bridgeStay
  congr 1
  · simp only [heatKernel, sub_self]
  · congr 2
    ext ω
    simp only [bridgeEvent, bridgePath, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, sub_self,
      mul_zero, add_zero, zero_add, add_sub_cancel_left, sub_zero]

/-- the integrand of `Var η`: `p_{𝕍 ∩ B(v, r(s))}(s; v, v)` -/
def etaDiag (v : ℂ) (s : ℝ) : ℝ := killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v

lemma norm_etaKernelL2_sq {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (v : ℂ) : ‖etaKernelL2 I v‖ ^ 2 = ∫ s in I, etaDiag v s := by
  rw [← real_inner_self_eq_norm_sq, inner_etaKernelL2 hI hc₀ hI0 v v]
  simpa [sq, etaDiag] using integral_sq_eq_of_lintegral (measurable_etaKernel hI v)
    (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time v)
    (fun s => killedHeat_nonneg _ _ _ _)
    (lintegral_etaKernel_sq hI (hI0.trans (Ioi_subset_Ioi hc₀.le)) v)

/-- the band `(a, b)` of times contributes at most `½ log(b/a)` to `Var η` -/
lemma pi_mul_integral_etaDiag_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (w : ℂ) :
    Real.pi * ∫ s in Ioo a b, etaDiag w s ≤ Real.log (b / a) / 2 := by
  have hinv : IntegrableOn (fun s : ℝ => (2 * Real.pi)⁻¹ * s⁻¹) (Ioc a b) :=
    (((continuousOn_inv₀.mono fun x hx => mem_compl_singleton_iff.mpr
      (ne_of_gt (ha.trans_le hx.1))).integrableOn_Icc).mono_set Ioc_subset_Icc_self).const_mul _
  have hfi : IntegrableOn (etaDiag w) (Ioc a b) :=
    (integrableOn_killedHeat_eta (c₀ := a / 2) (by positivity)
      (fun s hs => (half_lt_self ha).trans hs.1) w)
  have h1 : ∫ s in Ioc a b, etaDiag w s ≤ ∫ s in Ioc a b, (2 * Real.pi)⁻¹ * s⁻¹ := by
    refine setIntegral_mono_on hfi hinv measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := ha.trans hs.1
    refine (killedHeat_le_heatKernel _ _ _ _).trans ?_
    refine (heatKernel_le_inv _ (NNReal.coe_nonneg _) w w).trans (le_of_eq ?_)
    rw [Real.coe_toNNReal _ hs0.le, mul_inv]
  have h2 : ∫ s in Ioc a b, (2 * Real.pi)⁻¹ * s⁻¹ = (2 * Real.pi)⁻¹ * Real.log (b / a) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha
      (ha.trans_le hab)]
  rw [← integral_Ioc_eq_integral_Ioo]
  have hpi := Real.pi_pos
  calc Real.pi * ∫ s in Ioc a b, etaDiag w s ≤ Real.pi * ((2 * Real.pi)⁻¹ * Real.log (b / a)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) hpi.le
    _ = Real.log (b / a) / 2 := by field_simp

/-- `r(s) < ξ` for `0 < s ≤ (ξ²/16)²` -/
lemma etaRad_lt_of_small {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {s : ℝ} (hs : 0 < s)
    (hsξ : s ≤ (ξ ^ 2 / 16) ^ 2) : etaRad s < ξ := by
  set e := ξ ^ 2 / 16 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by rw [he]; nlinarith
  refine (etaRad_le_band hs he0 hsξ he1).trans_lt ?_
  have hlog : Real.log (e ^ 2)⁻¹ = 4 * Real.log (4 / ξ) := by
    rw [show (e ^ 2)⁻¹ = (4 / ξ) ^ 4 by rw [he]; field_simp; ring, Real.log_pow]; norm_num
  have hl := Real.log_le_sub_one_of_pos (show 0 < 4 / ξ by positivity)
  have hel : e * Real.log (e ^ 2)⁻¹ ≤ ξ := by
    rw [hlog]
    calc e * (4 * Real.log (4 / ξ)) ≤ e * (4 * (4 / ξ - 1)) := by gcongr
      _ ≤ e * (16 / ξ) := by
          gcongr; linarith [show 16 / ξ = 4 * (4 / ξ) by ring]
      _ = ξ := by rw [he]; field_simp
  have : e < ξ := by rw [he]; nlinarith
  linarith

lemma ball_etaRad_subset {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {s : ℝ} (hs : 0 < s)
    (hsξ : s ≤ (ξ ^ 2 / 16) ^ 2) {z : ℂ} (hz : z ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ)) :
    Metric.ball z (etaRad s) ⊆ openSquare := by
  have hr := etaRad_lt_of_small hξ hξ1 hs hsξ
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hre := (Complex.abs_re_le_norm (y - z)).trans_lt (hy.trans hr)
  have him := (Complex.abs_im_le_norm (y - z)).trans_lt (hy.trans hr)
  rw [Complex.sub_re, abs_lt] at hre
  rw [Complex.sub_im, abs_lt] at him
  simp only at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `etaDiag` does not depend on the point of `𝕍^ξ` for small times -/
lemma etaDiag_eq {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {s : ℝ} (hs : 0 < s)
    (hsξ : s ≤ (ξ ^ 2 / 16) ^ 2) {z w : ℂ} (hz : z ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ))
    (hw : w ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ)) : etaDiag z s = etaDiag w s := by
  unfold etaDiag
  rw [inter_eq_right.2 (ball_etaRad_subset hξ hξ1 hs hsξ hz),
    inter_eq_right.2 (ball_etaRad_subset hξ hξ1 hs hsξ hw), killedHeat_ball_center z,
    killedHeat_ball_center w]

/-- **(eq-var-compare) for `η` at two points and two scales**: on `𝕍^ξ`, for `0 < r ≤ 1`,
`|Var η_{2^{-n}}(z) − Var η_{r 2^{-n}}(w)| ≤ B + log r⁻¹`. -/
theorem etaVar_two_point_le {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (r : ℝ), 0 < r → r ≤ 1 → ∀ z w : ℂ,
      z ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) → w ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) →
      |etaVar ((1 / 2 : ℝ) ^ n) z - etaVar (r * (1 / 2 : ℝ) ^ n) w| ≤ B + Real.log r⁻¹ := by
  set e := ξ ^ 2 / 16 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by rw [he]; nlinarith
  have hl0 : 0 ≤ Real.log e⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨he0, he1⟩)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log e⁻¹ + 4, by linarith, fun n r hr hr1 z w hz hw => ?_⟩
  have hp : ∀ k : ℕ, (0 : ℝ) < (1 / 2) ^ k := fun k => by positivity
  have hp1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hlogp : ∀ k : ℕ, Real.log ((1 / 2 : ℝ) ^ k)⁻¹ = k * Real.log 2 := fun k => by
    rw [one_div, inv_pow, inv_inv, Real.log_pow]
  have hlr : 0 ≤ Real.log r⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hr, hr1⟩)
  have hrp : 0 < r * (1 / 2 : ℝ) ^ n := mul_pos hr (hp n)
  have hnm : r * (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ n := mul_le_of_le_one_left (hp n).le hr1
  have hVz := etaVar_le (hp n) (hp1 n) z
  have hVw := etaVar_le hrp (hnm.trans (hp1 n)) w
  have hz0 := etaVar_nonneg ((1 / 2 : ℝ) ^ n) z
  have hw0 := etaVar_nonneg (r * (1 / 2 : ℝ) ^ n) w
  rw [hlogp] at hVz
  rw [mul_inv, Real.log_mul (inv_ne_zero hr.ne') (inv_ne_zero (hp n).ne'), hlogp] at hVw
  by_cases hn : (1 / 2 : ℝ) ^ n ≤ e
  · -- small scales: the parts below `e` coincide
    have hb : ∀ v : ℂ, etaVar ((1 / 2 : ℝ) ^ n) v = etaVar e v +
        Real.pi * ∫ s in Ioo (((1 / 2 : ℝ) ^ n) ^ 2) (e ^ 2), etaDiag v s := fun v => by
      rw [etaVar_split (hp n) hn v, norm_etaKernelL2_sq measurableSet_Ioo
        (pow_pos (hp n) 2) Ioo_subset_Ioi_self]
    have hsame : ∫ s in Ioo (((1 / 2 : ℝ) ^ n) ^ 2) (e ^ 2), etaDiag z s =
        ∫ s in Ioo (((1 / 2 : ℝ) ^ n) ^ 2) (e ^ 2), etaDiag w s :=
      setIntegral_congr_fun measurableSet_Ioo fun s hs =>
        etaDiag_eq hξ hξ1 ((pow_pos (hp n) 2).trans hs.1) hs.2.le hz hw
    have hband : etaVar (r * (1 / 2 : ℝ) ^ n) w = etaVar ((1 / 2 : ℝ) ^ n) w +
        Real.pi * ∫ s in Ioo ((r * (1 / 2 : ℝ) ^ n) ^ 2) (((1 / 2 : ℝ) ^ n) ^ 2),
          etaDiag w s := by
      rw [etaVar_split hrp hnm w, norm_etaKernelL2_sq measurableSet_Ioo
        (pow_pos hrp 2) Ioo_subset_Ioi_self]
    have hbl := pi_mul_integral_etaDiag_le (pow_pos hrp 2) (pow_le_pow_left₀ hrp.le hnm 2) w
    have hratio : Real.log (((1 / 2 : ℝ) ^ n) ^ 2 / (r * (1 / 2 : ℝ) ^ n) ^ 2) / 2 =
        Real.log r⁻¹ := by
      rw [show ((1 / 2 : ℝ) ^ n) ^ 2 / (r * (1 / 2 : ℝ) ^ n) ^ 2 = r⁻¹ ^ 2 by
        field_simp, Real.log_pow]
      push_cast; ring
    rw [hratio] at hbl
    have hbn : 0 ≤ Real.pi * ∫ s in Ioo ((r * (1 / 2 : ℝ) ^ n) ^ 2) (((1 / 2 : ℝ) ^ n) ^ 2),
        etaDiag w s :=
      mul_nonneg Real.pi_pos.le (setIntegral_nonneg measurableSet_Ioo fun s _ =>
        killedHeat_nonneg _ _ _ _)
    have hez := etaVar_le he0 he1 z
    have hew := etaVar_le he0 he1 w
    have hez0 := etaVar_nonneg e z
    have hew0 := etaVar_nonneg e w
    rw [hband, hb z, hb w, hsame, abs_le]
    constructor <;> nlinarith
  · -- large scales: both variances are `O(log e⁻¹ + log r⁻¹)`
    push Not at hn
    have hnl : n * Real.log 2 ≤ Real.log e⁻¹ := by
      rw [← hlogp]
      exact Real.log_le_log (inv_pos.2 (hp n)) ((inv_le_inv₀ (hp n) he0).2 hn.le)
    rw [abs_le]
    constructor <;> nlinarith

/-- `0 ≤ Var h̃_ε(v) − Var η_ε(v) ≤ b₁` at every scale `ε ∈ (0, 1]` (the dyadic bound
`dzz_var_compare` and monotonicity of the truncation gap in the time interval). -/
theorem tildeVar_sub_etaVar_le : ∃ b₁ : ℝ, 0 ≤ b₁ ∧ ∀ (ε : ℝ), 0 < ε → ∀ v : ℂ,
    0 ≤ tildeVar ε v - etaVar ε v ∧ tildeVar ε v - etaVar ε v ≤ b₁ := by
  obtain ⟨b₁, hb₁, hv⟩ := dzz_var_compare
  refine ⟨b₁, hb₁, fun ε hε v => ?_⟩
  rw [tildeVar_sub_etaVar hε]
  refine ⟨truncGap_nonneg measurableSet_Ioi (pow_pos hε 2) subset_rfl v, ?_⟩
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hN0 : (0 : ℝ) < (1 / 2) ^ N := by positivity
  have hsq : ((1 / 2 : ℝ) ^ N) ^ 2 < ε ^ 2 := pow_lt_pow_left₀ hN hN0.le two_ne_zero
  have hsplit := truncGap_split (pow_pos hN0 2) hsq v
  have hmid := truncGap_nonneg (I := Ioo (((1 / 2 : ℝ) ^ N) ^ 2) (ε ^ 2)) measurableSet_Ioo
    (half_pos (pow_pos hN0 2)) (fun s hs => (half_lt_self (pow_pos hN0 2)).trans hs.1) v
  have hd := (abs_le.1 (hv N v)).2
  rw [tildeVar_sub_etaVar hN0] at hd
  linarith

/-- **(eq-var-compare) for `h̃` at two points and two scales** (`tildeVar_sub_etaVar_le` +
`etaVar_two_point_le`). -/
theorem tildeVar_two_point_le {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (r : ℝ), 0 < r → r ≤ 1 → ∀ z w : ℂ,
      z ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) → w ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) →
      |tildeVar ((1 / 2 : ℝ) ^ n) z - tildeVar (r * (1 / 2 : ℝ) ^ n) w| ≤
        B + Real.log r⁻¹ := by
  obtain ⟨B, hB, h⟩ := etaVar_two_point_le hξ hξ1
  obtain ⟨b₁, hb₁, hv⟩ := tildeVar_sub_etaVar_le
  refine ⟨B + b₁, by positivity, fun n r hr hr1 z w hz hw => ?_⟩
  have h1 := hv _ (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n) z
  have h2 := hv _ (mul_pos hr (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)) w
  have h3 := abs_le.1 (h n r hr hr1 z w hz hw)
  rw [abs_le]
  constructor <;> linarith

end DZZ
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127C1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatGreen
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSupp
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4a, part 1: the survival function `P^x(τ_U > t)` and its decay near an exterior
corkscrew (packet P-127C, decision D127 §3 N4(a))

`killedSurv U t x = ∫ p_U(t; x, y) dy` is the survival probability `P^x(τ_U > t)`
(`lintegral_killedHeat_eq`, DZZ l. 404–411). Here:

* `killedSurv_le_one`, `killedSurv_add` (Markov property at a fixed time, from
  Chapman–Kolmogorov `ofReal_killedHeat_add` and Tonelli), `killedSurv_anti`;
* `killedSurv_add_le_of_near` (one Markov step: survive time `t`, then survive time `s` from a
  point near `p` with probability `≤ a`, or be far from `p` at time `t`);
* `killedSurv_add_ball_le` and `lintegral_ball_heatKernel_ge` (from every point within `2R` of a
  ball of radius `R/4` outside `U`, BM is in that ball at time `R²` with probability
  `≥ γ₀ = e^{-81/32}/32`);
* `heatKernel_le_tail'`, `lintegral_far_heatKernel_le` (Gaussian tail).

The decay `killedSurv U h x → 0` as `x → Uᶜ` (`exists_killedSurv_le_of_corkscrew`, file C2) is
the classical fact that an exterior cone condition makes boundary points regular (D127 N4(a);
Mörters–Peres, *Brownian motion*, Poincaré cone condition, prove it with Blumenthal's 0-1 law,
which we do not have). We use instead a 0-1-law-free iteration of the Markov property over
scales `R_j = r₀ Λʲ` (own elementary argument, DV-P127C-1; source exact theorem numbers not
checked).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat

/-- The survival probability `P^x(τ_U > t) = ∫ p_U(t; x, y) dy`. -/
def killedSurv (U : Set ℂ) (t : ℝ≥0) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (killedHeat U t x y)

lemma lintegral_ofReal_heatKernel_eq_one {t : ℝ} (ht : 0 < t) (x : ℂ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel t x y) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel t ht x)
    (Filter.Eventually.of_forall fun y => heatKernel_nonneg t ht.le x y),
    integral_heatKernel t ht x, ENNReal.ofReal_one]

lemma killedSurv_le_one (U : Set ℂ) {t : ℝ≥0} (ht : t ≠ 0) (x : ℂ) : killedSurv U t x ≤ 1 := by
  rw [← lintegral_ofReal_heatKernel_eq_one (t := t) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)) x]
  exact lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal (killedHeat_le_heatKernel _ _ _ _)

lemma measurable_killedHeat_uncurry {U : Set ℂ} (hU : IsOpen U) (t : ℝ≥0) :
    Measurable fun q : ℂ × ℂ ↦ killedHeat U t q.1 q.2 :=
  (measurable_killedHeat hU).comp (measurable_const.prodMk measurable_id)

/-- **Markov property at a fixed time**: `P^x(τ > t + s) = ∫ p_U(t; x, w) P^w(τ > s) dw`. -/
theorem killedSurv_add {U : Set ℂ} (hU : IsOpen U) {t s : ℝ≥0} (ht : t ≠ 0) (hs : s ≠ 0)
    (x : ℂ) :
    killedSurv U (t + s) x = ∫⁻ w, ENNReal.ofReal (killedHeat U t x w) * killedSurv U s w := by
  unfold killedSurv
  simp_rw [ofReal_killedHeat_add hU ht hs]
  have hm : Measurable fun q : ℂ × ℂ ↦
      ENNReal.ofReal (killedHeat U t x q.2) * ENNReal.ofReal (killedHeat U s q.2 q.1) :=
    ((measurable_killedHeat_right hU ht x).comp measurable_snd).ennreal_ofReal.mul
      ((measurable_killedHeat_uncurry hU s).comp measurable_swap).ennreal_ofReal
  rw [lintegral_lintegral_swap hm.aemeasurable]
  refine lintegral_congr fun w ↦ ?_
  rw [lintegral_const_mul _ (measurable_killedHeat_right hU hs w).ennreal_ofReal]

theorem killedSurv_add_le {U : Set ℂ} (hU : IsOpen U) {t s : ℝ≥0} (ht : t ≠ 0) (hs : s ≠ 0)
    (x : ℂ) : killedSurv U (t + s) x ≤ killedSurv U t x := by
  rw [killedSurv_add hU ht hs]
  calc ∫⁻ w, ENNReal.ofReal (killedHeat U t x w) * killedSurv U s w
      ≤ ∫⁻ w, ENNReal.ofReal (killedHeat U t x w) * 1 :=
        lintegral_mono fun w ↦ mul_le_mul' le_rfl (killedSurv_le_one U hs w)
    _ = killedSurv U t x := by simp [killedSurv]

theorem killedSurv_anti {U : Set ℂ} (hU : IsOpen U) {t t' : ℝ≥0} (ht : t ≠ 0) (htt' : t ≤ t')
    (x : ℂ) : killedSurv U t' x ≤ killedSurv U t x := by
  rcases eq_or_lt_of_le htt' with h | h
  · rw [h]
  · have : t' = t + (t' - t) := (add_tsub_cancel_of_le htt').symm
    rw [this]
    exact killedSurv_add_le hU ht (tsub_pos_of_lt h).ne' x

/-- **One Markov step.** If `P^w(τ > s) ≤ a` for all `w` within `R` of `p`, then
`P^x(τ > t + s) ≤ a P^x(τ > t) + P^x(|B_t − p| > R)`. -/
theorem killedSurv_add_le_of_near {U : Set ℂ} (hU : IsOpen U) {t s : ℝ≥0} (ht : t ≠ 0)
    (hs : s ≠ 0) (x p : ℂ) {R : ℝ} {a : ℝ≥0∞}
    (hnear : ∀ w, dist w p ≤ R → killedSurv U s w ≤ a) :
    killedSurv U (t + s) x ≤
      a * killedSurv U t x + ∫⁻ w in {w | R < dist w p}, ENNReal.ofReal (heatKernel t x w) := by
  rw [killedSurv_add hU ht hs]
  have hF : MeasurableSet {w : ℂ | R < dist w p} :=
    measurableSet_lt measurable_const (measurable_id.dist measurable_const)
  calc ∫⁻ w, ENNReal.ofReal (killedHeat U t x w) * killedSurv U s w
      ≤ ∫⁻ w, (a * ENNReal.ofReal (killedHeat U t x w) +
          {w | R < dist w p}.indicator (fun w ↦ ENNReal.ofReal (heatKernel t x w)) w) := by
        refine lintegral_mono fun w ↦ ?_
        by_cases hw : dist w p ≤ R
        · have : w ∉ {w : ℂ | R < dist w p} := by simpa using hw
          rw [Set.indicator_of_notMem this, add_zero, mul_comm a]
          exact mul_le_mul' le_rfl (hnear w hw)
        · have : w ∈ {w : ℂ | R < dist w p} := by simpa using hw
          rw [Set.indicator_of_mem this]
          calc ENNReal.ofReal (killedHeat U t x w) * killedSurv U s w
              ≤ ENNReal.ofReal (heatKernel t x w) * 1 :=
                mul_le_mul' (ENNReal.ofReal_le_ofReal (killedHeat_le_heatKernel _ _ _ _))
                  (killedSurv_le_one U hs w)
            _ ≤ _ := by rw [mul_one]; exact le_add_self
    _ = a * killedSurv U t x +
          ∫⁻ w in {w | R < dist w p}, ENNReal.ofReal (heatKernel t x w) := by
        rw [lintegral_add_left ((measurable_killedHeat_right hU ht x).ennreal_ofReal.const_mul a),
          lintegral_const_mul _ (measurable_killedHeat_right hU ht x).ennreal_ofReal,
          lintegral_indicator hF]
        rfl

/-- Killing on a ball outside `U`: `P^x(τ > t) + P^x(B_t ∈ B(c, ρ)) ≤ 1` if `B(c, ρ) ⊆ Uᶜ`. -/
theorem killedSurv_add_ball_le {U : Set ℂ} (hU : IsOpen U) {t : ℝ≥0} (ht : t ≠ 0) (x c : ℂ)
    {ρ : ℝ} (hball : ball c ρ ⊆ Uᶜ) :
    killedSurv U t x + ∫⁻ y in ball c ρ, ENNReal.ofReal (heatKernel t x y) ≤ 1 := by
  rw [← lintegral_ofReal_heatKernel_eq_one (t := t) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)) x,
    ← lintegral_add_compl (μ := (volume : Measure ℂ)) (fun y ↦ ENNReal.ofReal (heatKernel t x y))
      (measurableSet_ball (x := c) (ε := ρ)),
    add_comm (∫⁻ y in ball c ρ, _)]
  refine add_le_add ?_ le_rfl
  unfold killedSurv
  rw [← lintegral_add_compl (μ := (volume : Measure ℂ)) (fun y ↦ ENNReal.ofReal (killedHeat U t x y))
    (measurableSet_ball (x := c) (ε := ρ))]
  have h0 : ∫⁻ y in ball c ρ, ENNReal.ofReal (killedHeat U t x y) = 0 := by
    refine le_antisymm ?_ (zero_le)
    calc ∫⁻ y in ball c ρ, ENNReal.ofReal (killedHeat U t x y) ≤ ∫⁻ _ in ball c ρ, (0 : ℝ≥0∞) :=
          setLIntegral_mono measurable_const fun y hy ↦ by
            rw [killedHeat_eq_zero_of_not_mem_right hU ht x (hball hy), ENNReal.ofReal_zero]
      _ = 0 := by simp
  rw [h0, zero_add]
  exact setLIntegral_mono (measurable_heatKernel_right _ x).ennreal_ofReal
    fun y _ ↦ ENNReal.ofReal_le_ofReal (killedHeat_le_heatKernel _ _ _ _)

/-- Gaussian lower bound on a ball: for `dist x c ≤ D`,
`P^x(B_t ∈ B(c, ρ)) ≥ (2πt)⁻¹ e^{-(D+ρ)²/(2t)} · |B(c, ρ)|`. -/
theorem lintegral_ball_heatKernel_ge {t : ℝ} (ht : 0 < t) {x c : ℂ} {D ρ : ℝ}
    (hxc : dist x c ≤ D) :
    ENNReal.ofReal ((2 * Real.pi * t)⁻¹ * Real.exp (-(D + ρ) ^ 2 / (2 * t))) * volume (ball c ρ)
      ≤ ∫⁻ y in ball c ρ, ENNReal.ofReal (heatKernel t x y) := by
  rw [← setLIntegral_const]
  refine setLIntegral_mono (measurable_heatKernel_right _ x).ennreal_ofReal fun y hy ↦ ?_
  refine ENNReal.ofReal_le_ofReal ?_
  unfold heatKernel
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have h1 : ‖x - y‖ ≤ D + ρ := by
    rw [← dist_eq_norm]
    calc dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
      _ ≤ D + ρ := add_le_add hxc (by rw [dist_comm]; exact (mem_ball.mp hy).le)
  have h2 : ‖x - y‖ ^ 2 ≤ (D + ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right h2 (by positivity)

/-- The constant `γ₀ = e^{-81/32}/32`. -/
def survGam0 : ℝ := Real.exp (-(81 / 32)) / 32

lemma survGam0_pos : 0 < survGam0 := by unfold survGam0; positivity

/-- **Corkscrew step**: if `B(c, R/4) ⊆ Uᶜ` with `dist c p ≤ R`, then for every `w` within `R`
of `p`, `P^w(τ_U > R²) ≤ 1 − γ₀`. -/
theorem killedSurv_le_of_ball {U : Set ℂ} (hU : IsOpen U) {R : ℝ≥0} (hR : R ≠ 0) {p c : ℂ}
    (hcp : dist c p ≤ R) (hball : ball c ((R : ℝ) / 4) ⊆ Uᶜ) {w : ℂ} (hw : dist w p ≤ R) :
    killedSurv U (R ^ 2) w ≤ 1 - ENNReal.ofReal survGam0 := by
  have hR' : (0 : ℝ) < R := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hR)
  have hR2 : (R ^ 2 : ℝ≥0) ≠ 0 := pow_ne_zero 2 hR
  have hwc : dist w c ≤ 2 * R := by
    calc dist w c ≤ dist w p + dist p c := dist_triangle _ _ _
      _ ≤ R + R := add_le_add hw (by rw [dist_comm]; exact hcp)
      _ = 2 * R := by ring
  have hlow := lintegral_ball_heatKernel_ge (t := ((R ^ 2 : ℝ≥0) : ℝ)) (ρ := (R : ℝ) / 4)
    (by positivity) hwc
  have hval : ENNReal.ofReal ((2 * Real.pi * ((R ^ 2 : ℝ≥0) : ℝ))⁻¹ *
      Real.exp (-(2 * R + (R : ℝ) / 4) ^ 2 / (2 * ((R ^ 2 : ℝ≥0) : ℝ)))) *
      volume (ball c ((R : ℝ) / 4)) = ENNReal.ofReal survGam0 := by
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold survGam0
    have he : -(2 * (R : ℝ) + R / 4) ^ 2 / (2 * ((R ^ 2 : ℝ≥0) : ℝ)) = -(81 / 32) := by
      push_cast
      field_simp
      ring
    rw [he, NNReal.coe_real_pi]
    push_cast
    field_simp
    ring
  rw [hval] at hlow
  have hsum := killedSurv_add_ball_le hU hR2 w c hball
  have hfin : killedSurv U (R ^ 2) w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (killedSurv_le_one U hR2 w)
  calc killedSurv U (R ^ 2) w
      = (killedSurv U (R ^ 2) w + ENNReal.ofReal survGam0) - ENNReal.ofReal survGam0 :=
        (ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top).symm
    _ ≤ 1 - ENNReal.ofReal survGam0 := tsub_le_tsub_right ((add_le_add le_rfl hlow).trans hsum) _

/-- Gaussian tail of the heat kernel (as DFGPS `heatKernel_le_tail`, recentred at `x`):
`p_s(x, w) ≤ 2 e^{-δ²/(4s)} p_{2s}(x, w)` if `δ ≤ |w − x|`. -/
theorem heatKernel_le_tail' {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) {x w : ℂ} (hu : δ ≤ ‖x - w‖) :
    heatKernel s x w ≤ 2 * Real.exp (-δ ^ 2 / (4 * s)) * heatKernel (2 * s) x w := by
  simp only [heatKernel]
  have e : 2 * Real.exp (-δ ^ 2 / (4 * s)) * ((2 * Real.pi * (2 * s))⁻¹ *
      Real.exp (-‖x - w‖ ^ 2 / (2 * (2 * s)))) =
      (2 * Real.pi * s)⁻¹ * Real.exp (-δ ^ 2 / (4 * s) + -‖x - w‖ ^ 2 / (4 * s)) := by
    rw [Real.exp_add]; field_simp; ring_nf
  rw [e]
  gcongr
  have h1 : δ ^ 2 ≤ ‖x - w‖ ^ 2 := pow_le_pow_left₀ hδ hu 2
  have e2 : -‖x - w‖ ^ 2 / (2 * s) - (-δ ^ 2 / (4 * s) + -‖x - w‖ ^ 2 / (4 * s)) =
      (δ ^ 2 - ‖x - w‖ ^ 2) / (4 * s) := by field_simp; ring
  have : (δ ^ 2 - ‖x - w‖ ^ 2) / (4 * s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- Gaussian tail: `P^x(|B_t − x| ≥ δ) ≤ 2 e^{-δ²/(4t)}`. -/
theorem lintegral_far_heatKernel_le {t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (x : ℂ) (S : Set ℂ)
    (hS : S ⊆ {w | δ ≤ dist w x}) :
    ∫⁻ w in S, ENNReal.ofReal (heatKernel t x w) ≤
      ENNReal.ofReal (2 * Real.exp (-δ ^ 2 / (4 * t))) := by
  calc ∫⁻ w in S, ENNReal.ofReal (heatKernel t x w)
      ≤ ∫⁻ w, ENNReal.ofReal (2 * Real.exp (-δ ^ 2 / (4 * t))) *
          ENNReal.ofReal (heatKernel (2 * t) x w) := by
        refine (setLIntegral_mono ((measurable_heatKernel_right _ x).ennreal_ofReal.const_mul _)
          fun w hw ↦ ?_).trans (setLIntegral_le_lintegral _ _)
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (heatKernel_le_tail' ht hδ ?_)
        rw [← dist_eq_norm, dist_comm]
        exact hS hw
    _ = _ := by
        rw [lintegral_const_mul _ (measurable_heatKernel_right _ x).ennreal_ofReal,
          lintegral_ofReal_heatKernel_eq_one (by positivity), mul_one]

end ZBM
end CONF
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53V1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UClip

/-!
# DZZ Lemma 5.3, proof: lower bound on the variance of the `η` band (P-131V, D131 §3)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 2480–2481 compare the variance of
the fine field with `log` of the scale ratio ("a straightforward computation"). D131 needs the
lower bound with an `O(1)` loss:

* `etaVar_eq_integral`: `Var η_ε(v) = π ∫_{ε²}^∞ p_{𝕍 ∩ B(v, r(t))}(t; v, v) dt` (the computation of
  `etaVar_le`, S3L1Var, isolated);
* `killedHeat_eta_ge`: for `v ∈ 𝕍^ξ` and `0 < t ≤ e^{−72}`,
  `p_{𝕍 ∩ B(v, r(t))}(t; v, v) ≥ (2πt)⁻¹ − (2π)⁻¹ · 4M`, `M = max 1 (9/(2c²))`, `c = min (1/10) ξ`:
  `B(v, r') ⊆ 𝕍 ∩ B(v, r(t))` for `r' = min (√t log t⁻¹ /4) c`, and the exit bound
  `killedHeat_sub_inter_ball_le` (S2L7Trunc, DZZ l. 557) at `A = ℂ`, with
  `t⁻¹ e^{−(log t⁻¹)²/72} ≤ 1` for `log t⁻¹ ≥ 72` and `t⁻¹ e^{−2c²/(9t)} ≤ 9/(2c²)`;
* `etaVar_band_ge` (D131 §3, exact statement): `log(s/ε) − B ≤ Var η_ε(x) − Var η_s(x)` for
  `x ∈ 𝕍^ξ`, `0 < ε ≤ s ≤ s₀`;
* `etaVar_band_ge_one`: the same for all `s ≤ 1` (with `B + 36`; uses `etaVar_anti`, S3VarBdry);
* `etaVarBand_ge`: the band form `log(s/ε) − B ≤ π ‖K^η_{(ε², s²)}‖²` (via `etaVar_split`).

DZZ give no details ("straightforward computation"); the exit-probability argument is the one of
their proof of Lemma 2.7 (l. 554–559), here used for a lower bound (own elementary step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

/-- `Var η_ε(v) = π ∫_{ε²}^∞ p_{𝕍 ∩ B(v, r(t))}(t; v, v) dt`. -/
theorem etaVar_eq_integral {ε : ℝ} (hε : 0 < ε) (v : ℂ) :
    etaVar ε v = Real.pi * ∫ t in Ioi (ε ^ 2),
      killedHeat (openSquare ∩ Metric.ball v (etaRad t)) t.toNNReal v v := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have nv : ∫ p, etaKernel (Ioi (ε ^ 2)) v p * etaKernel (Ioi (ε ^ 2)) v p =
      ∫ t in Ioi (ε ^ 2), killedHeat (openSquare ∩ Metric.ball v (etaRad t)) t.toNNReal v v := by
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel measurableSet_Ioi v)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time v)
      (fun s => killedHeat_nonneg _ _ _ _)
      (lintegral_etaKernel_sq measurableSet_Ioi (Ioi_subset_Ioi hε2.le) v)
  rw [etaVar, ← real_inner_self_eq_norm_sq,
    inner_etaKernelL2 measurableSet_Ioi hε2 subset_rfl v v, nv]

/-- `Var η_ε(v) − Var η_s(v) = π ∫_{ε²}^{s²} p_{𝕍 ∩ B(v, r(t))}(t; v, v) dt`. -/
theorem etaVar_sub_eq_integral {ε s : ℝ} (hε : 0 < ε) (hεs : ε ≤ s) (v : ℂ) :
    etaVar ε v - etaVar s v = Real.pi * ∫ t in Ioc (ε ^ 2) (s ^ 2),
      killedHeat (openSquare ∩ Metric.ball v (etaRad t)) t.toNNReal v v := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hs2 : ε ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hε.le hεs 2
  have hfi := integrableOn_killedHeat_eta hε2 subset_rfl v
  rw [etaVar_eq_integral hε, etaVar_eq_integral (hε.trans_le hεs), ← Ioc_union_Ioi_eq_Ioi hs2,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hfi.mono_set Ioc_subset_Ioi_self) (hfi.mono_set (Ioi_subset_Ioi hs2))]
  ring

/-- For `v ∈ 𝕍^ξ`, `B(v, ξ) ⊆ 𝕍°`. -/
lemma ball_subset_openSquare_of_dzzVXi {ξ : ℝ} {v : ℂ} (hv : v ∈ dzzVXi ξ) :
    Metric.ball v ξ ⊆ openSquare := by
  obtain ⟨h0, h1, h2, h3⟩ := dzzVXi_sub_dzzVIn le_rfl hv
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - v)).trans_lt hz
  have him := (Complex.abs_im_le_norm (z - v)).trans_lt hz
  rw [Complex.sub_re, abs_lt] at hre
  rw [Complex.sub_im, abs_lt] at him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `y e^{−y} ≤ 1`. -/
lemma mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  have hp := Real.exp_pos y
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ hp]
  linarith

/-- The exit term: `t⁻¹ e^{−2(r'/3)²/t} ≤ max 1 (9/(2c²))` for `r' = min (√t log t⁻¹/4) c`,
`0 < t ≤ e^{−72}`, `c > 0`. -/
lemma inv_mul_exp_exit_le {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (ht1 : t ≤ Real.exp (-72)) :
    t⁻¹ * Real.exp (-(2 * (min (Real.sqrt t * |Real.log t⁻¹| / 4) c / 3) ^ 2 / t)) ≤
      max 1 (9 / (2 * c ^ 2)) := by
  set L := Real.log t⁻¹ with hL
  have hL72 : 72 ≤ L := by
    rw [hL, Real.log_inv, le_neg]
    calc Real.log t ≤ Real.log (Real.exp (-72)) := Real.log_le_log ht ht1
      _ = -72 := Real.log_exp _
  have htL : t⁻¹ = Real.exp L := by rw [hL, Real.exp_log (inv_pos.mpr ht)]
  rcases min_choice (Real.sqrt t * |L| / 4) c with h | h <;> rw [h]
  · refine le_trans ?_ (le_max_left _ _)
    rw [abs_of_nonneg (by linarith), htL, ← Real.exp_add]
    have e : 2 * (Real.sqrt t * L / 4 / 3) ^ 2 / t = L ^ 2 / 72 := by
      rw [div_pow, div_pow, mul_pow, Real.sq_sqrt ht.le]
      field_simp
      ring
    rw [e, Real.exp_le_one_iff]
    nlinarith
  · refine le_trans ?_ (le_max_right _ _)
    set y := 2 * (c / 3) ^ 2 / t with hy
    have e : t⁻¹ = 9 / (2 * c ^ 2) * y := by
      rw [hy]; field_simp; ring
    rw [e, mul_assoc]
    have hk : 0 ≤ 9 / (2 * c ^ 2) := by positivity
    calc 9 / (2 * c ^ 2) * (y * Real.exp (-y)) ≤ 9 / (2 * c ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (mul_exp_neg_le_one y) hk
      _ = 9 / (2 * c ^ 2) := mul_one _

/-- Pointwise lower bound on the integrand: for `v ∈ 𝕍^ξ` (`ξ > 0`) and `0 < t ≤ e^{−72}`,
`p_{𝕍 ∩ B(v, r(t))}(t; v, v) ≥ (2πt)⁻¹ − (2π)⁻¹ · 4 M`. -/
theorem killedHeat_eta_ge {ξ : ℝ} (hξ : 0 < ξ) {v : ℂ} (hv : v ∈ dzzVXi ξ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ Real.exp (-72)) :
    (2 * Real.pi)⁻¹ * t⁻¹ - (2 * Real.pi)⁻¹ * (4 * max 1 (9 / (2 * min (1 / 10) ξ ^ 2))) ≤
      killedHeat (openSquare ∩ Metric.ball v (etaRad t)) t.toNNReal v v := by
  set c := min (1 / 10 : ℝ) ξ with hc
  have hc0 : 0 < c := lt_min (by norm_num) hξ
  set r' := min (Real.sqrt t * |Real.log t⁻¹| / 4) c with hr'
  have ht1' : t < 1 := ht1.trans_lt (by simp)
  have hlog : 0 < Real.log t⁻¹ := Real.log_pos ((one_lt_inv₀ ht).mpr ht1')
  have hr0 : 0 < r' := lt_min (by positivity) hc0
  have hsub : Metric.ball v r' ⊆ openSquare ∩ Metric.ball v (etaRad t) := by
    refine subset_inter ((Metric.ball_subset_ball ((min_le_right _ _).trans
      (min_le_right _ _))).trans (ball_subset_openSquare_of_dzzVXi hv))
      (Metric.ball_subset_ball ?_)
    exact min_le_min le_rfl (min_le_left _ _)
  have htn : t.toNNReal ≠ 0 := by simpa using ht
  have hex := killedHeat_sub_inter_ball_le htn univ v hr0
  rw [killedHeat_univ, univ_inter, Real.coe_toNNReal _ ht.le] at hex
  have hhk : heatKernel t v v = (2 * Real.pi * t)⁻¹ := by simp [heatKernel]
  rw [hhk] at hex
  have hM := inv_mul_exp_exit_le hc0 ht ht1
  rw [← hr'] at hM
  have hmono := killedHeat_mono hsub t.toNNReal v v
  have hpi := Real.pi_pos
  have e : (2 * Real.pi * t)⁻¹ * (4 * Real.exp (-(2 * (r' / 3) ^ 2 / t))) =
      (2 * Real.pi)⁻¹ * 4 * (t⁻¹ * Real.exp (-(2 * (r' / 3) ^ 2 / t))) := by
    rw [mul_inv]; ring
  have h2 : (2 * Real.pi)⁻¹ * 4 * (t⁻¹ * Real.exp (-(2 * (r' / 3) ^ 2 / t))) ≤
      (2 * Real.pi)⁻¹ * 4 * max 1 (9 / (2 * c ^ 2)) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have e2 : (2 * Real.pi * t)⁻¹ = (2 * Real.pi)⁻¹ * t⁻¹ := mul_inv _ _
  rw [e2] at hex
  rw [e2] at e
  linarith

/-- **DZZ l. 2480–2481, the lower bound on the `η` band variance (D131 §3, P-131V).** -/
theorem etaVar_band_ge {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1 / 2) : ∃ B : ℝ, 0 ≤ B ∧ ∃ s₀ > 0,
    ∀ x ∈ dzzVXi ξ, ∀ ε s : ℝ, 0 < ε → ε ≤ s → s ≤ s₀ →
      Real.log (s / ε) - B ≤ etaVar ε x - etaVar s x := by
  set M := max 1 (9 / (2 * min (1 / 10 : ℝ) ξ ^ 2)) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left zero_le_one
  refine ⟨2 * M, by positivity, Real.exp (-36), Real.exp_pos _, fun x hx ε s hε hεs hs => ?_⟩
  have hpi := Real.pi_pos
  have hs0 : 0 < s := hε.trans_le hεs
  have hε2 : 0 < ε ^ 2 := by positivity
  have hs2 : ε ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hε.le hεs 2
  have hss : s ^ 2 ≤ Real.exp (-72) := by
    calc s ^ 2 ≤ Real.exp (-36) ^ 2 := pow_le_pow_left₀ hs0.le hs 2
      _ = Real.exp (-72) := by rw [← Real.exp_nat_mul]; norm_num
  have hs1 : s ^ 2 ≤ 1 := hss.trans (by rw [Real.exp_le_one_iff]; norm_num)
  set K := (2 * Real.pi)⁻¹ * (4 * M) with hK
  set f : ℝ → ℝ := fun t => killedHeat (openSquare ∩ Metric.ball x (etaRad t)) t.toNNReal x x
  have hfi : IntegrableOn f (Ioc (ε ^ 2) (s ^ 2)) :=
    (integrableOn_killedHeat_eta hε2 subset_rfl x).mono_set Ioc_subset_Ioi_self
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (ε ^ 2) (s ^ 2) :=
    intervalIntegral.intervalIntegrable_inv (fun t ht => by
      rw [uIcc_of_le hs2] at ht; exact (hε2.trans_le ht.1).ne') continuousOn_id
  have hg : IntervalIntegrable (fun t : ℝ => (2 * Real.pi)⁻¹ * t⁻¹ - K) volume (ε ^ 2) (s ^ 2) :=
    (hinv.const_mul _).sub intervalIntegrable_const
  have hlow : ∫ t in Ioc (ε ^ 2) (s ^ 2), ((2 * Real.pi)⁻¹ * t⁻¹ - K) ≤
      ∫ t in Ioc (ε ^ 2) (s ^ 2), f t :=
    setIntegral_mono_on ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs2).mp hg) hfi
      measurableSet_Ioc fun t ht => killedHeat_eta_ge hξ hx (hε2.trans ht.1)
        (ht.2.trans hss)
  have hcomp : ∫ t in Ioc (ε ^ 2) (s ^ 2), ((2 * Real.pi)⁻¹ * t⁻¹ - K) =
      (2 * Real.pi)⁻¹ * (2 * Real.log (s / ε)) - K * (s ^ 2 - ε ^ 2) := by
    rw [← intervalIntegral.integral_of_le hs2, intervalIntegral.integral_sub
      (hinv.const_mul _) intervalIntegrable_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hε2 (hε2.trans_le hs2), intervalIntegral.integral_const, smul_eq_mul,
      ← div_pow, Real.log_pow]
    push_cast; ring
  rw [etaVar_sub_eq_integral hε hεs x]
  have hK0 : 0 ≤ K := by positivity
  have hKb : K * (s ^ 2 - ε ^ 2) ≤ K := by
    have : s ^ 2 - ε ^ 2 ≤ 1 := by linarith
    nlinarith
  have hπK : Real.pi * K = 2 * M := by rw [hK]; field_simp; ring
  have := mul_le_mul_of_nonneg_left (hcomp.symm.trans_le hlow) hpi.le
  have e : Real.pi * ((2 * Real.pi)⁻¹ * (2 * Real.log (s / ε))) = Real.log (s / ε) := by
    field_simp
  nlinarith

/-- `etaVar_band_ge` for all `s ≤ 1` (the loss grows by `log s₀⁻¹`). -/
theorem etaVar_band_ge_one {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1 / 2) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ x ∈ dzzVXi ξ, ∀ ε s : ℝ, 0 < ε → ε ≤ s → s ≤ 1 →
      Real.log (s / ε) - B ≤ etaVar ε x - etaVar s x := by
  obtain ⟨B, hB, s₀, hs₀, h⟩ := etaVar_band_ge hξ hξ1
  refine ⟨B + |Real.log s₀|, by positivity, fun x hx ε s hε hεs hs1 => ?_⟩
  have hs0 : 0 < s := hε.trans_le hεs
  have hab := neg_abs_le (Real.log s₀)
  have hls : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1
  rw [Real.log_div hs0.ne' hε.ne']
  rcases le_total s s₀ with h1 | h1
  · have := h x hx ε s hε hεs h1
    rw [Real.log_div hs0.ne' hε.ne'] at this
    have : 0 ≤ |Real.log s₀| := abs_nonneg _
    linarith
  rcases le_total ε s₀ with h2 | h2
  · have := h x hx ε s₀ hε h2 le_rfl
    rw [Real.log_div hs₀.ne' hε.ne'] at this
    have := etaVar_anti hs₀ h1 x
    linarith
  · have := etaVar_anti hε hεs x
    have := Real.log_le_log hs₀ h2
    linarith

/-- The band form: `log(s/ε) − B ≤ Var η^s_ε(x) = π ‖K^η_{(ε², s²), x}‖²` for `0 < ε ≤ s ≤ 1`. -/
theorem etaVarBand_ge {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1 / 2) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ x ∈ dzzVXi ξ, ∀ ε s : ℝ, 0 < ε → ε ≤ s → s ≤ 1 →
      Real.log (s / ε) - B ≤ Real.pi * ‖etaKernelL2 (Ioo (ε ^ 2) (s ^ 2)) x‖ ^ 2 := by
  obtain ⟨B, hB, h⟩ := etaVar_band_ge_one hξ hξ1
  refine ⟨B, hB, fun x hx ε s hε hεs hs1 => ?_⟩
  have := h x hx ε s hε hεs hs1
  rw [etaVar_split hε hεs x] at this
  linarith

end DZZ
end LQGMetric

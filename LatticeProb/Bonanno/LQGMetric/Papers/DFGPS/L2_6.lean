/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6Path
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyUnif
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField

/-!
# DFGPS Lemma 2.6 (`lem-lfpp-scale`): the LFPP scaling identity

Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 2.6 (T:837–856): for a
whole-plane GFF `h`, `r > 0` and `h^r := h(r·) − h_r(0)`,
`D^{ε/r}_{h^r}(z, w) = r⁻¹ e^{−ξ h_r(0)} D^ε_h(r z, r w)` for all `z, w`.

Proof (T:847–855): the heat-kernel convolutions satisfy `h^{r,*}_{ε/r}(z) = h*_ε(r z) − h_r(0)`
("a standard change of variables"), then the change of variables `P̃ = P/r` in the LFPP infimum
(`lfppInfFn_scale`, L2_6Path.lean). In this formalization `h*_ε(z)` is the limit of the truncated
pairings `⟨h, p_{ε²/2}(z,·) χ_n⟩` (FOUNDATIONS §3); after the change of variables the truncation of
`h(r·)` uses the rescaled cutoffs `χ_n(·/r)`. That both truncations have the same limit is the
a.s. statement `ae_heatMollify_affineComp_at`, proved with the Gaussian tail bound
`IsWholePlaneGFF.ae_summable_abs_of_decay` (own argument for "standard change of variables").
`h(r·)` is `affineComp r 0 h` (D10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `IsWholePlaneGFF.ae_summable_abs_of_decay` with test functions supported in `B_{a(n+3)}`
(by scaling: apply it to the whole-plane GFF `h(a·)`). -/
theorem ae_summable_abs_of_decay_scaled (hh : IsWholePlaneGFF h P) (φ : ℕ → TestC)
    {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hb : ∀ (n : ℕ) (w : ℂ), |φ n w| ≤ K * Real.exp (-(n : ℝ)))
    (hs : ∀ (n : ℕ) (w : ℂ), a * ((n : ℝ) + 3) ≤ ‖w‖ → φ n w = 0) :
    ∀ᵐ ω ∂P, Summable fun n => |h ω (φ n)| := by
  set ψ : ℕ → TestC := fun n => testAffinePull a⁻¹ 0 (φ n)
  have hψ : ∀ n w, ψ n w = φ n ((a : ℂ) * w) := fun n w => by
    simp only [ψ, testAffinePull_apply _ _ (inv_ne_zero ha.ne'), sub_zero]
    congr 1
    rw [div_eq_mul_inv]; push_cast; rw [inv_inv, mul_comm]
  have hsum := (hh.affineComp ha 0).ae_summable_abs_of_decay ψ hK
    (fun n w => by rw [hψ]; exact hb n _) (fun n w hw => by
      rw [hψ]; refine hs n _ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left hw ha.le)
  filter_upwards [hsum] with ω hω
  have e : ∀ n, h ω (φ n) = a ^ 2 * affineComp a 0 (h ω) (ψ n) := fun n => by
    rw [GFFInv.affineComp_apply]
    have : testAffinePull a 0 (ψ n) = φ n := TestFunction.ext fun x => by
      rw [testAffinePull_apply _ _ ha.ne', hψ, sub_zero]
      congr 1
      exact mul_div_cancel₀ x (Complex.ofReal_ne_zero.2 ha.ne')
    rw [this]
    field_simp
  refine (hω.mul_left (a ^ 2)).congr fun n => ?_
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg a)]

lemma cutoff_eq_one {n : ℕ} {w : ℂ} (hw : ‖w‖ ≤ (n : ℝ) + 1) : (cutoff n : ℂ → ℝ) w = 1 :=
  (cutoff n).one_of_mem_closedBall (by rwa [Metric.mem_closedBall, dist_zero_right])

lemma cutoff_eq_zero {n : ℕ} {w : ℂ} (hw : (n : ℝ) + 2 ≤ ‖w‖) : (cutoff n : ℂ → ℝ) w = 0 := by
  have : w ∉ Function.support (cutoff n : ℂ → ℝ) := by
    rw [ContDiffBump.support_eq]; simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact hw
  exact Function.notMem_support.1 this

/-- the heat kernel under the change of variables `x = r y`:
`r⁻² p_{s/r²}(z, x/r) = p_s(r z, x)` -/
lemma heatKernel_scale {s r : ℝ} (hr : 0 < r) (z x : ℂ) :
    (r ^ 2)⁻¹ * heatKernel (s / r ^ 2) z (x / r) = heatKernel s ((r : ℂ) * z) x := by
  unfold heatKernel
  have hn : ‖(r : ℂ) * z - x‖ = r * ‖z - x / r‖ := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [show (r : ℂ) * z - x = (r : ℂ) * (z - x / r) by field_simp, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  rw [hn, mul_pow]
  by_cases hs : s = 0
  · simp [hs]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  rw [← mul_assoc]
  congr 1
  · field_simp
  · congr 1; field_simp

/-- the difference of the two truncations: `p_s(r z, ·)(χ_n(·/r) − χ_n)` -/
def scaleTruncDiff (s r : ℝ) (z : ℂ) (n : ℕ) : TestC :=
  (r ^ 2)⁻¹ • testAffinePull r 0 (heatTrunc (s / r ^ 2) z n) - heatTrunc s ((r : ℂ) * z) n

lemma scaleTruncDiff_apply {s r : ℝ} (hr : 0 < r) (z : ℂ) (n : ℕ) (x : ℂ) :
    scaleTruncDiff s r z n x = heatKernel s ((r : ℂ) * z) x *
      ((cutoff n : ℂ → ℝ) (x / r) - (cutoff n : ℂ → ℝ) x) := by
  show (r ^ 2)⁻¹ * testAffinePull r 0 (heatTrunc (s / r ^ 2) z n) x -
    heatTrunc s ((r : ℂ) * z) n x = _
  rw [testAffinePull_apply _ _ hr.ne', sub_zero, heatTrunc_apply, heatTrunc_apply, ← mul_assoc,
    heatKernel_scale hr]
  ring

lemma exp_neg_sq_div_le' (s t m : ℝ) (hs : 0 < s) (hm : 0 < m) :
    Real.exp (-t ^ 2 / (2 * s)) ≤ Real.exp (s / (2 * m ^ 2) - t / m) := by
  apply Real.exp_le_exp.2
  have : 0 ≤ (t - s / m) ^ 2 / (2 * s) := by positivity
  have e : (t - s / m) ^ 2 / (2 * s) = t ^ 2 / (2 * s) - t / m + s / (2 * m ^ 2) := by
    field_simp; ring
  rw [neg_div]; linarith

lemma abs_scaleTruncDiff_le {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : ℂ) (n : ℕ) (x : ℂ) :
    |scaleTruncDiff s r z n x| ≤ (2 * Real.pi * s)⁻¹ *
      Real.exp (s / (2 * min 1 r ^ 2) + r * ‖z‖ / min 1 r) * Real.exp (-(n : ℝ)) := by
  set m := min 1 r
  have hm : 0 < m := lt_min one_pos hr
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmr : m ≤ r := min_le_right _ _
  rw [scaleTruncDiff_apply hr]
  by_cases hx : ‖x‖ ≤ m * ((n : ℝ) + 1)
  · have h1 : ‖x / r‖ ≤ (n : ℝ) + 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_le_iff₀ hr]
      nlinarith
    rw [cutoff_eq_one h1, cutoff_eq_one (by nlinarith), sub_self, mul_zero, abs_zero]
    positivity
  push Not at hx
  have hp := heatKernel_nonneg s hs.le ((r : ℂ) * z) x
  have hc : |(cutoff n : ℂ → ℝ) (x / r) - (cutoff n : ℂ → ℝ) x| ≤ 1 := by
    have := (cutoff n).nonneg (x := x / r); have := (cutoff n).le_one (x := x / r)
    have := (cutoff n).nonneg (x := x); have := (cutoff n).le_one (x := x)
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg hp]
  refine (mul_le_of_le_one_right hp hc).trans ?_
  unfold heatKernel
  rw [mul_assoc _ (Real.exp _)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (2 * Real.pi * s)⁻¹)
  refine (exp_neg_sq_div_le' s _ m hs hm).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have ht : ‖x‖ - r * ‖z‖ ≤ ‖(r : ℂ) * z - x‖ := by
    have := norm_sub_norm_le x ((r : ℂ) * z)
    rw [norm_sub_rev, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at this
    linarith
  have h2 : (m * ((n : ℝ) + 1) - r * ‖z‖) / m ≤ ‖(r : ℂ) * z - x‖ / m :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  have h3 : (m * ((n : ℝ) + 1) - r * ‖z‖) / m = (n : ℝ) + 1 - r * ‖z‖ / m := by
    field_simp
  linarith

lemma scaleTruncDiff_eq_zero {s r : ℝ} (hr : 0 < r) (z : ℂ) (n : ℕ) (x : ℂ)
    (hx : max 1 r * ((n : ℝ) + 3) ≤ ‖x‖) : scaleTruncDiff s r z n x = 0 := by
  have hA1 : 1 ≤ max 1 r := le_max_left _ _
  have hAr : r ≤ max 1 r := le_max_right _ _
  have hx1 : (n : ℝ) + 2 ≤ ‖x‖ := by nlinarith
  have hx2 : (n : ℝ) + 2 ≤ ‖x / r‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, le_div_iff₀ hr]
    nlinarith
  rw [scaleTruncDiff_apply hr, cutoff_eq_zero hx1, cutoff_eq_zero hx2, sub_self, mul_zero]

/-- **The heat-kernel change of variables** (DFGPS T:848), a.s. at a fixed point:
`(h(r·))*_{ε/r}(z) = h*_ε(r z)`. -/
theorem ae_heatMollify_affineComp_at (hh : IsWholePlaneGFF h P) {ε r : ℝ} (hε : ε ≠ 0)
    (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, heatMollify (ε / r) (affineComp r 0 (h ω)) z = heatMollify ε (h ω) ((r : ℂ) * z) := by
  set s := ε ^ 2 / 2
  have hs : 0 < s := by positivity
  have hss : (ε / r) ^ 2 / 2 = s / r ^ 2 := by simp only [s]; field_simp
  have h1 := hh.ae_tendsto_heatMollify ε hε ((r : ℂ) * z)
  have h2 := (hh.affineComp hr 0).ae_tendsto_heatMollify (ε / r) (div_ne_zero hε hr.ne') z
  have h3 := ae_summable_abs_of_decay_scaled hh (fun n => scaleTruncDiff s r z n)
    (by positivity) (lt_of_lt_of_le one_pos (le_max_left 1 r))
    (fun n w => abs_scaleTruncDiff_le hs hr z n w)
    (fun n w hw => scaleTruncDiff_eq_zero hr z n w hw)
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  rw [hss] at hω2
  have hD : Tendsto (fun n => h ω (scaleTruncDiff s r z n)) atTop (𝓝 0) :=
    hω3.of_abs.tendsto_atTop_zero
  have e : ∀ n, affineComp r 0 (h ω) (heatTrunc (s / r ^ 2) z n) =
      h ω (heatTrunc s ((r : ℂ) * z) n) + h ω (scaleTruncDiff s r z n) := fun n => by
    rw [GFFInv.affineComp_apply, scaleTruncDiff, map_sub, map_smul, smul_eq_mul]
    ring
  simp_rw [e] at hω2
  have := hω1.add hD
  rw [add_zero] at this
  exact tendsto_nhds_unique hω2 this

/-- the heat-kernel change of variables a.s. at all points simultaneously (both sides are
continuous). -/
theorem ae_heatMollify_affineComp (hh : IsWholePlaneGFF h P) {ε r : ℝ} (hε : ε ≠ 0)
    (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ z, heatMollify (ε / r) (affineComp r 0 (h ω)) z =
      heatMollify ε (h ω) ((r : ℂ) * z) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hall := (ae_ball_iff hSc).2 fun z _ => ae_heatMollify_affineComp_at hh hε hr z
  have hc1 := (hh.affineComp hr 0).ae_tendstoLocallyUniformly_heatMollify (ε / r)
    (div_ne_zero hε hr.ne')
  have hc2 := hh.ae_tendstoLocallyUniformly_heatMollify ε hε
  filter_upwards [hall, hc1, hc2] with ω hω h1 h2
  have := Continuous.ext_on hSd h1.2 (h2.2.comp (continuous_const.mul continuous_id))
    fun z hz => hω z hz
  exact fun z => congrFun this z

/-- `(g + c)*_δ = g*_δ + c` where the truncations of `g` converge. -/
theorem heatMollify_addConst_of_tendsto {δ : ℝ} (hδ : δ ≠ 0) {g : DistC} {z : ℂ}
    (hg : Tendsto (fun n : ℕ => g (heatTrunc (δ ^ 2 / 2) z n)) atTop (𝓝 (heatMollify δ g z)))
    (c : ℝ) : heatMollify δ (addConst g c) z = heatMollify δ g z + c := by
  have hM : ∀ w, |(ContinuousMap.const ℂ c) w| ≤ |c| := fun w => le_rfl
  have e := LFPP.heatMollify_add_of_tendsto hg
    (LFPP.tendsto_heatMollify_ofCont (ContinuousMap.const ℂ c) |c| hM hδ z)
  rw [show addConst g c = g + ofCont (ContinuousMap.const ℂ c) from rfl, e,
    heatMollify_ofCont _ |c| hM δ hδ z]
  simp only [ContinuousMap.const_apply]
  rw [integral_const_mul, integral_heatKernel _ (by positivity) z, mul_one]

/-- **DFGPS Lemma 2.6** (`lem-lfpp-scale`, T:837–856), the identity
`D^{ε/r}_{h(r·)+c'}(z, w) = r⁻¹ e^{ξ c'} D^ε_h(r z, r w)` for every constant `c'` (DFGPS: `c' =
−h_r(0)`), a.s. for a whole-plane GFF `h` (any additive normalization). -/
theorem lem2_6_ae_const (hh : IsWholePlaneGFF h P) (ξ : ℝ) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (z w : ℂ),
      lfppDistE ξ (ε / r) (addConst (affineComp r 0 (h ω)) (-c)) z w =
        ENNReal.ofReal (r⁻¹ * Real.exp (-ξ * c)) *
          lfppDistE ξ ε (h ω) ((r : ℂ) * z) ((r : ℂ) * w) := by
  have hεr : ε / r ≠ 0 := div_ne_zero hε.ne' hr.ne'
  filter_upwards [ae_heatMollify_affineComp hh hε.ne' hr,
    (hh.affineComp hr 0).ae_tendstoLocallyUniformly_heatMollify (ε / r) hεr] with ω hω hconv c z w
  rw [lfppDistE_eq_lfppInfFn, lfppDistE_eq_lfppInfFn]
  refine lfppInfFn_scale ξ hr (fun x => ?_) z w
  rw [heatMollify_addConst_of_tendsto hεr
    ((tendstoLocallyUniformlyOn_univ.2 hconv.1).tendsto_at (mem_univ x)), hω x]
  ring

/-- **DFGPS Lemma 2.6** (`lem-lfpp-scale`, T:837–856): for a whole-plane GFF `h`, `r > 0` and
`h^r := h(r·) − h_r(0)`, a.s. `D^{ε/r}_{h^r}(z, w) = r⁻¹ e^{−ξ h_r(0)} D^ε_h(r z, r w)` for all
`z, w`. (The normalization `h_1(0) = 0` of DFGPS is not needed for the identity.) -/
theorem lem2_6 (hh : IsWholePlaneGFF h P) (ξ : ℝ) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ,
      lfppDistE ξ (ε / r) (addConst (affineComp r 0 (h ω)) (-circleAvg (h ω) r 0)) z w =
        ENNReal.ofReal (r⁻¹ * Real.exp (-ξ * circleAvg (h ω) r 0)) *
          lfppDistE ξ ε (h ω) ((r : ℂ) * z) ((r : ℂ) * w) := by
  filter_upwards [lem2_6_ae_const hh ξ hε hr] with ω hω z w
  exact hω _ z w

end LQGMetric.DFGPS

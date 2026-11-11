import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-!
# Pairings of circle-supported mollifiers with continuous and radial functions

For a radius `r > 0` and a centre `z ∈ ℂ`, `circBump k z r` is the normalized mollified uniform measure on the circle
`∂B_r(z)` at scale `2^{-k}`. This file records the pathwise facts used to identify circle averages as limits of
pairings:

* `∫ circBump k z r · g → ⨍_{∂B_r(z)} g` as `k → ∞` for continuous `g` (`tendsto_integral_circBump_mul`), and the same
  for radial integrands `x ↦ R ‖x‖` with `R` continuous on `(0, ∞)` and `‖z‖ ≠ r`
  (`tendsto_integral_circBump_mul_radial`);
* the logarithmic potential `logPot (circBump k z r)` is `1/r`-Lipschitz and continuous, and it is within `2^{-k}/r` of
  `-circLog z r`, where `circLog z r u` is the circle average of `log ‖· - u‖` over `∂B_r(z)`
  (`abs_logPot_circBump_add_circLog_le`); in particular `log r ≤ circLog z r` (`log_le_circLog`).

The remaining lemmas (integrability of continuous functions on circles, circle averages of functions that agree on the
circle, congruence of circle averages, and a sequential criterion for convergence) concern general functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real ENNReal

open LQGMetric LQGMetric.CircleAvg

namespace LatticeProb
namespace CirclePairing

/-! ### Circle integrability and circle averages -/

/-- A continuous function is integrable on every circle. -/
lemma circleIntegrable_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (c : ℂ) (R : ℝ) : CircleIntegrable f c R :=
  (hf.comp (continuous_circleMap c R)).intervalIntegrable _ _

/-- A circle average of a function which is constant on the circle. -/
lemma circleAverage_eq_of_eqOn_sphere {f : ℂ → ℝ} {c : ℂ} {R v : ℝ} (hf : CircleIntegrable f c R)
    (h : ∀ x ∈ sphere c |R|, f x = v) : Real.circleAverage f c R = v := by
  have hc : CircleIntegrable (fun _ : ℂ => v) c R := circleIntegrable_of_continuous continuous_const c R
  refine le_antisymm ?_ ?_
  · calc Real.circleAverage f c R ≤ Real.circleAverage (fun _ => v) c R :=
          Real.circleAverage_mono hf hc fun x hx => (h x hx).le
      _ = v := Real.circleAverage_const v c R
  · calc v = Real.circleAverage (fun _ => v) c R := (Real.circleAverage_const v c R).symm
      _ ≤ Real.circleAverage f c R := Real.circleAverage_mono hc hf fun x hx => (h x hx).ge

/-- Two functions which agree off one point agree codiscretely on any set. -/
lemma eventuallyEq_codiscreteWithin_of_ne {f g : ℂ → ℝ} (S : Set ℂ) (x : ℂ) (h : ∀ y, y ≠ x → f y = g y) :
    f =ᶠ[codiscreteWithin S] g := by
  have hmem : ({x}ᶜ : Set ℂ) ∈ codiscreteWithin S := by
    rw [mem_codiscreteWithin]
    intro y _
    rw [disjoint_principal_right]
    have hx : ({x}ᶜ : Set ℂ) ∈ 𝓝[≠] y := by
      by_cases hyx : y = x
      · subst hyx
        exact self_mem_nhdsWithin
      · exact mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hyx)
    exact Filter.mem_of_superset hx fun w hw hw' => hw'.2 hw
  exact Filter.mem_of_superset hmem fun y hy => h y hy

/-! ### The logarithmic potential of a circle-supported mollifier -/

/-- The logarithmic potential of `circBump k z r` is within `2^{-k}/r` of `-circLog z r`. -/
lemma abs_logPot_circBump_add_circLog_le {r : ℝ} (hr : 0 < r) (k : ℕ) (z x : ℂ) :
    |logPot (circBump k z r) x + circLog z r x| ≤ (2 : ℝ)⁻¹ ^ k / r := by
  rw [logPot_circBump]
  have h := abs_integral_bump_circLog_sub_le hr k z x
  rw [abs_sub_comm] at h
  convert h using 2
  ring

/-- The logarithmic potential of `circBump k z r` is `1/r`-Lipschitz. -/
lemma abs_logPot_circBump_sub_le {r : ℝ} (hr : 0 < r) (k : ℕ) (z x y : ℂ) :
    |logPot (circBump k z r) x - logPot (circBump k z r) y| ≤ ‖x - y‖ / r := by
  have hi : ∀ u, Integrable fun t => bumpTest k 0 t * circLog z r (u - t) := fun u =>
    ((bumpTest k 0).continuous.mul ((continuous_circLog hr.ne' z).comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (bumpTest k 0).hasCompactSupport.mul_right
  rw [logPot_circBump, logPot_circBump, neg_sub_neg, ← integral_sub (hi y) (hi x), ← Real.norm_eq_abs]
  have hb : ∀ t, ‖bumpTest k 0 t * circLog z r (y - t) - bumpTest k 0 t * circLog z r (x - t)‖ ≤
      bumpTest k 0 t * (‖x - y‖ / r) := by
    intro t
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (bumpTest_nonneg k 0 t), Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (bumpTest_nonneg k 0 t)
    refine (abs_circLog_sub_le hr z _ _).trans (le_of_eq ?_)
    rw [sub_sub_sub_cancel_right, norm_sub_rev]
  refine (norm_integral_le_of_norm_le ((integrable_testC _).mul_const _) (Eventually.of_forall hb)).trans
    (le_of_eq ?_)
  rw [integral_mul_const, integral_bumpTest', one_mul]

/-- The logarithmic potential of `circBump k z r` is continuous. -/
lemma continuous_logPot_circBump {r : ℝ} (hr : 0 < r) (k : ℕ) (z : ℂ) :
    Continuous (logPot (circBump k z r)) := by
  refine LipschitzWith.continuous (K := Real.toNNReal r⁻¹) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.2 hr.le), ← div_eq_inv_mul]
  exact abs_logPot_circBump_sub_le hr k z x y

section Covariance

variable {k : ℕ} {z : ℂ} {r : ℝ}

/-- The product of `circBump k z r` with its logarithmic potential is integrable. -/
lemma integrable_circBump_mul_logPot (hr : 0 < r) :
    Integrable fun x => circBump k z r x * logPot (circBump k z r) x :=
  ((circBump k z r).continuous.mul (continuous_logPot_circBump hr k z)).integrable_of_hasCompactSupport
    (circBump k z r).hasCompactSupport.mul_right

end Covariance

/-- The circle-averaged logarithmic kernel dominates `log r` on the whole plane. -/
lemma log_le_circLog {z : ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) : Real.log r ≤ circLog z r x := by
  rw [circLog_eq hr.ne']
  exact le_add_of_nonneg_right Real.posLog_nonneg

/-! ### Pathwise convergence of pairings with continuous and radial functions -/

/-- Circle averages of two functions which agree on the circle agree. -/
lemma circleAverage_congr_sphere {f g : ℂ → ℝ} {c : ℂ} {R : ℝ} (h : EqOn f g (sphere c |R|)) :
    Real.circleAverage f c R = Real.circleAverage g c R := by
  simp only [Real.circleAverage_def]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => h (circleMap_mem_sphere' c R θ)

/-- A circle average is bounded by a bound for the function on the circle. -/
lemma abs_circleAverage_le {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hf : CircleIntegrable f c R)
    (h : ∀ x ∈ sphere c |R|, |f x| ≤ M) : |Real.circleAverage f c R| ≤ M := by
  have hc : ∀ v : ℝ, CircleIntegrable (fun _ : ℂ => v) c R := fun v =>
    circleIntegrable_of_continuous continuous_const c R
  rw [abs_le]
  constructor
  · calc -M = Real.circleAverage (fun _ => -M) c R := (Real.circleAverage_const _ c R).symm
      _ ≤ _ := Real.circleAverage_mono (hc _) hf fun x hx => (abs_le.1 (h x hx)).1
  · calc Real.circleAverage f c R ≤ Real.circleAverage (fun _ => M) c R :=
          Real.circleAverage_mono hf (hc _) fun x hx => (abs_le.1 (h x hx)).2
      _ = M := Real.circleAverage_const _ c R

/-- `circBump k z r` vanishes at every point at distance at least `2^{-k}` from the circle `∂B_r(z)`. -/
lemma circBump_eq_zero_of_forall_le {k : ℕ} {z x : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ c ∈ sphere z r, (2 : ℝ)⁻¹ ^ k ≤ dist x c) : circBump k z r x = 0 := by
  rw [circBump_apply]
  have hcont : Continuous fun c => bumpTest k c x := by
    have e : (fun c => bumpTest k c x) = fun c => bumpTest k 0 (x - c) := funext fun c => bumpTest_eq_sub k c x
    rw [e]
    exact (bumpTest k 0).continuous.comp (continuous_const.sub continuous_id)
  refine circleAverage_eq_of_eqOn_sphere (circleIntegrable_of_continuous hcont z r) fun c hc => ?_
  rw [abs_of_pos hr] at hc
  exact bumpTest_eq_zero_of_le k (h c hc)

/-- `∫ φ_k g → ⨍_{∂B_r(z)} g` for `g` continuous. -/
theorem tendsto_integral_circBump_mul {g : ℂ → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Tendsto (fun k => ∫ x, circBump k z r x * g x) atTop (𝓝 (Real.circleAverage g z r)) := by
  have hpair : ∀ k, ∫ x, circBump k z r x * g x =
      Real.circleAverage (fun c => ∫ y, bumpTest k c y * g y) z r := by
    intro k
    have h := circleAverage_pairing (ofCont ⟨g, hg⟩) k z r
    simp only [ofCont_apply, ContinuousMap.coe_mk] at h
    exact h.symm
  have huc := (isCompact_closedBall z (r + 1)).uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := huc (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (lt_min hδ one_pos) (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun k hk => ?_⟩
  have hkN : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hk1 : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hloc : ∀ c ∈ sphere z |r|, |(∫ y, bumpTest k c y * g y) - g c| ≤ ε / 2 := by
    intro c hc
    rw [abs_of_pos hr, mem_sphere] at hc
    have hi1 : Integrable fun y => bumpTest k c y * g y :=
      ((bumpTest k c).continuous.mul hg).integrable_of_hasCompactSupport
        (bumpTest k c).hasCompactSupport.mul_right
    have hi2 : Integrable fun y => bumpTest k c y * g c := (integrable_testC _).mul_const _
    have e : (∫ y, bumpTest k c y * g y) - g c = ∫ y, (bumpTest k c y * g y - bumpTest k c y * g c) := by
      rw [integral_sub hi1 hi2, integral_mul_const, integral_bumpTest', one_mul]
    rw [e, ← Real.norm_eq_abs]
    have hb : ∀ y, ‖bumpTest k c y * g y - bumpTest k c y * g c‖ ≤ bumpTest k c y * (ε / 2) := by
      intro y
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (bumpTest_nonneg k c y)]
      by_cases hy : dist y c < (2 : ℝ)⁻¹ ^ k
      · refine mul_le_mul_of_nonneg_left ?_ (bumpTest_nonneg k c y)
        have hyK : y ∈ closedBall z (r + 1) := by
          rw [mem_closedBall]
          linarith [dist_triangle y c z]
        have hcK : c ∈ closedBall z (r + 1) := by
          rw [mem_closedBall]
          linarith
        have := hδg y hyK c hcK (by linarith [min_le_left δ 1])
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        exact this.le
      · rw [bumpTest_eq_zero_of_le k (not_lt.1 hy), zero_mul, zero_mul]
    refine (norm_integral_le_of_norm_le ((integrable_testC _).mul_const _) (Eventually.of_forall hb)).trans
      (le_of_eq ?_)
    rw [integral_mul_const, integral_bumpTest', one_mul]
  have hci : CircleIntegrable (fun c => ∫ y, bumpTest k c y * g y) z r := by
    have := circleIntegrable_pairing (ofCont ⟨g, hg⟩) k z r
    simpa only [ofCont_apply, ContinuousMap.coe_mk] using this
  have hgi := circleIntegrable_of_continuous hg z r
  rw [hpair, Real.dist_eq, ← Real.circleAverage_sub hci hgi]
  exact (abs_circleAverage_le (hci.sub hgi) fun c hc => hloc c hc).trans_lt (half_lt_self hε)

/-- **Pathwise convergence of the radial terms**: `∫ φ_k(x) R(|x|) dx → ⨍_{∂B_r(z)} R(|·|)` for `R` continuous on
`(0, ∞)`, when the circle `∂B_r(z)` avoids `0`. -/
theorem tendsto_integral_circBump_mul_radial {R : ℝ → ℝ} (hR : ContinuousOn R (Ioi 0)) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : ‖z‖ ≠ r) :
    Tendsto (fun k => ∫ x, circBump k z r x * R ‖x‖) atTop
      (𝓝 (Real.circleAverage (fun x => R ‖x‖) z r)) := by
  set m := |‖z‖ - r| / 2 with hm_def
  have hm : 0 < m := by
    have := abs_pos.2 (sub_ne_zero.2 hz)
    positivity
  set g : ℂ → ℝ := fun x => R (max ‖x‖ m) with hg_def
  have hg : Continuous g :=
    hR.comp_continuous (continuous_norm.max continuous_const) fun x => lt_of_lt_of_le hm (le_max_right _ _)
  have hsph : ∀ c ∈ sphere z r, 2 * m ≤ ‖c‖ := by
    intro c hc
    rw [mem_sphere, dist_eq_norm] at hc
    have h1 : |‖z‖ - r| ≤ ‖c‖ := abs_le'.2
      ⟨by linarith [norm_sub_norm_le z c, norm_sub_rev z c], by linarith [norm_sub_le c z]⟩
    linarith
  have hev : ∀ᶠ k in atTop, ∫ x, circBump k z r x * g x = ∫ x, circBump k z r x * R ‖x‖ := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hm (by norm_num : (2 : ℝ)⁻¹ < 1)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hkN : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    congr 1
    funext x
    by_cases hx : m ≤ ‖x‖
    · simp only [g, max_eq_left hx]
    · rw [circBump_eq_zero_of_forall_le hr fun c hc => ?_, zero_mul, zero_mul]
      have h1 := hsph c hc
      have h2 : ‖c‖ - ‖x‖ ≤ dist x c := by
        rw [dist_comm, dist_eq_norm]
        exact norm_sub_norm_le c x
      linarith [not_le.1 hx]
  have hCA : Real.circleAverage g z r = Real.circleAverage (fun x => R ‖x‖) z r :=
    circleAverage_congr_sphere fun c hc => by
      rw [abs_of_pos hr] at hc
      simp only [g, max_eq_left (by linarith [hsph c hc] : m ≤ ‖c‖)]
  rw [← hCA]
  exact (tendsto_integral_circBump_mul hg hr z).congr' hev

/-! ### Continuity of radial functions and a sequential criterion -/

/-- Restriction of a jointly continuous family `f s z` to `z = 0` is continuous in `s > 0`. -/
lemma continuousOn_radial {f : ℝ → ℂ → ℝ} (h : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun s => f s 0) (Ioi 0) :=
  h.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs => ⟨hs, mem_univ _⟩

/-- Convergence of a real sequence, as a statement about the distances `dist (u k) a` below `(m + 1)⁻¹`. -/
lemma tendsto_iff_forall_nat {u : ℕ → ℝ} {a : ℝ} :
    Tendsto u atTop (𝓝 a) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → dist (u k) a < ((m : ℝ) + 1)⁻¹ := by
  constructor
  · intro h m
    exact Metric.tendsto_atTop.1 h _ (by positivity)
  · intro h
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := h m
    exact ⟨N, fun k hk => (hN k hk).trans (by rwa [one_div] at hm)⟩

end CirclePairing
end LatticeProb

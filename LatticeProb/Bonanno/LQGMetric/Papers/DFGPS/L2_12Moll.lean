/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_12Moll at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylBounds

/-!
# DFGPS Lemma 2.12, first step: `f^{*,n}_{ε_n} → f` locally uniformly

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1036–1037: "Let
`f_{ε_n}^{*,n} = f^n * p_{ε_n²/2}` … Then `f_{ε_n}^{*,n} → f` uniformly on compact subsets of `ℂ`."
The paper states this without proof (approximation of the identity by the heat kernel). Own
elementary proof (DEVIATIONS: DF-B7-MOLL): split `∫ (f(z) − fⁿ(z+u)) p_s(0,u) du` at `|u| = δ`;
near `0` use the uniform continuity of `f` and `fⁿ → f` on `B̄_{R+1}(0)`; far from `0` use
`|fⁿ|, |f| ≤ M` and the kernel bound `p_s(0,u) ≤ 2 e^{-δ²/(4s)} p_{2s}(0,u)` for `|u| ≥ δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

/-- Gaussian tail bound for the heat kernel: `p_s(0,u) ≤ 2 e^{-δ²/(4s)} p_{2s}(0,u)` if `δ ≤ |u|`. -/
theorem heatKernel_le_tail {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) {u : ℂ} (hu : δ ≤ ‖u‖) :
    heatKernel s 0 u ≤ 2 * Real.exp (-δ ^ 2 / (4 * s)) * heatKernel (2 * s) 0 u := by
  simp only [heatKernel, zero_sub, norm_neg]
  have e : 2 * Real.exp (-δ ^ 2 / (4 * s)) * ((2 * Real.pi * (2 * s))⁻¹ *
      Real.exp (-‖u‖ ^ 2 / (2 * (2 * s)))) =
      (2 * Real.pi * s)⁻¹ * Real.exp (-δ ^ 2 / (4 * s) + -‖u‖ ^ 2 / (4 * s)) := by
    rw [Real.exp_add]; field_simp; ring_nf
  rw [e]
  gcongr
  have h1 : δ ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ hδ hu 2
  have e2 : -‖u‖ ^ 2 / (2 * s) - (-δ ^ 2 / (4 * s) + -‖u‖ ^ 2 / (4 * s)) =
      (δ ^ 2 - ‖u‖ ^ 2) / (4 * s) := by field_simp; ring
  have : (δ ^ 2 - ‖u‖ ^ 2) / (4 * s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- **DFGPS T:1036–1037**: if `fⁿ → f` locally uniformly, `|fⁿ|, |f| ≤ M` and `ε_n → 0`, then
`fⁿ*_{ε_n} → f` uniformly on each closed ball. -/
theorem tendstoUniformlyOn_heatMollify_seq {εn : ℕ → ℝ} (hε : ∀ n, εn n ≠ 0)
    (hε0 : Tendsto εn atTop (𝓝 0)) {fn : ℕ → C(ℂ, ℝ)} {f : C(ℂ, ℝ)} {M : ℝ}
    (hfnM : ∀ n z, |fn n z| ≤ M) (hfM : ∀ z, |f z| ≤ M)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (closedBall 0 R))
    {R : ℝ} (hR : 0 < R) :
    TendstoUniformlyOn (fun n z => heatMollify (εn n) (ofCont (fn n)) z) ⇑f atTop
      (closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  set η' := η / 8 with hη'
  have hη'0 : 0 < η' := by positivity
  -- uniform continuity of `f` on `B̄_{R+1}(0)`
  have hK : IsCompact (closedBall (0 : ℂ) (R + 1)) := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous f.continuous.continuousOn) η' hη'0
  set δ₁ := min δ 1 with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ one_pos
  -- `fⁿ → f` on `B̄_{R+1}(0)`
  have hev1 := (Metric.tendstoUniformlyOn_iff.1 (hconv (R + 1) (by linarith))) η' hη'0
  -- the Gaussian tail
  have hsq : Tendsto (fun n => εn n ^ 2 / 2) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa using (hε0.pow 2).div_const 2
    · have := hε n; show 0 < εn n ^ 2 / 2; positivity
  have htail : Tendsto (fun n => Real.exp (-δ₁ ^ 2 / (4 * (εn n ^ 2 / 2)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => δ₁ ^ 2 / 4 * x⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp (h1.comp hsq)).congr fun n => ?_
    simp only [Function.comp]
    congr 1
    field_simp
  have hev2 := htail.eventually (gt_mem_nhds (show (0 : ℝ) < η' / (4 * M + 1) by positivity))
  filter_upwards [hev1, hev2] with n hn1 hn2 z hz
  set s := εn n ^ 2 / 2 with hsdef
  have hs : 0 < s := by have := hε n; positivity
  set e := Real.exp (-δ₁ ^ 2 / (4 * s)) with hedef
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hz1 : z ∈ closedBall (0 : ℂ) (R + 1) := closedBall_subset_closedBall (by linarith) hz
  -- the mollification as an integral
  have hmol : heatMollify (εn n) (ofCont (fn n)) z = ∫ u, fn n (z + u) * heatKernel s 0 u := by
    rw [heatMollify_ofCont (fn n) M (hfnM n) _ (hε n) z, integral_heatKernel_mul_eq_shift]
  have hint1 : Integrable fun u => fn n (z + u) * heatKernel s 0 u := by
    have := integrable_heatKernel_mul_of_bdd ((fn n).comp ⟨fun u => z + u, by fun_prop⟩) M
      (fun w => hfnM n _) s hs 0
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp [mul_comm]
  have hint0 : Integrable fun u => f z * heatKernel s 0 u :=
    (integrable_heatKernel s hs 0).const_mul _
  have hfz : f z = ∫ u, f z * heatKernel s 0 u := by
    rw [integral_const_mul, integral_heatKernel s hs 0, mul_one]
  have hdiff : f z - heatMollify (εn n) (ofCont (fn n)) z =
      ∫ u, (f z - fn n (z + u)) * heatKernel s 0 u := by
    rw [hmol]; nth_rewrite 1 [hfz]
    rw [← integral_sub hint0 hint1]
    congr 1; funext u; ring
  -- pointwise bound
  have hpt : ∀ u, |f z - fn n (z + u)| * heatKernel s 0 u ≤
      2 * η' * heatKernel s 0 u + 2 * M * (2 * e) * heatKernel (2 * s) 0 u := by
    intro u
    have hp0 := heatKernel_nonneg s hs.le 0 u
    have hq0 := heatKernel_nonneg (2 * s) (by positivity) 0 u
    rcases lt_or_ge ‖u‖ δ₁ with hu | hu
    · have hzu : z + u ∈ closedBall (0 : ℂ) (R + 1) := by
        rw [mem_closedBall, dist_zero_right] at hz ⊢
        have := norm_add_le z u
        linarith [min_le_right δ 1]
      have h1 : dist (f z) (f (z + u)) < η' := hδf z hz1 (z + u) hzu (by
        rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact hu.trans_le (min_le_left _ _))
      have h2 := hn1 (z + u) hzu
      rw [Real.dist_eq] at h1 h2
      have h3 : |f z - fn n (z + u)| ≤ 2 * η' := by
        calc |f z - fn n (z + u)| ≤ |f z - f (z + u)| + |f (z + u) - fn n (z + u)| := abs_sub_le _ _ _
          _ ≤ 2 * η' := by linarith
      have : 0 ≤ 2 * M * (2 * e) * heatKernel (2 * s) 0 u := by positivity
      nlinarith
    · have h3 : |f z - fn n (z + u)| ≤ 2 * M := by
        calc |f z - fn n (z + u)| ≤ |f z| + |fn n (z + u)| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hfM z, hfnM n (z + u)]
      have h4 := heatKernel_le_tail hs hδ₁0.le hu
      have : 0 ≤ 2 * η' * heatKernel s 0 u := by positivity
      calc |f z - fn n (z + u)| * heatKernel s 0 u ≤ 2 * M * heatKernel s 0 u :=
            mul_le_mul_of_nonneg_right h3 hp0
        _ ≤ 2 * M * (2 * e * heatKernel (2 * s) 0 u) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ _ := by nlinarith
  have hintB : Integrable fun u =>
      2 * η' * heatKernel s 0 u + 2 * M * (2 * e) * heatKernel (2 * s) 0 u :=
    ((integrable_heatKernel s hs 0).const_mul _).add
      ((integrable_heatKernel (2 * s) (by positivity) 0).const_mul _)
  have hB : ∫ u, (2 * η' * heatKernel s 0 u + 2 * M * (2 * e) * heatKernel (2 * s) 0 u) =
      2 * η' + 4 * M * e := by
    rw [integral_add ((integrable_heatKernel s hs 0).const_mul _)
      ((integrable_heatKernel (2 * s) (by positivity) 0).const_mul _), integral_const_mul,
      integral_const_mul, integral_heatKernel s hs 0, integral_heatKernel (2 * s) (by positivity) 0]
    ring
  have hle : |f z - heatMollify (εn n) (ofCont (fn n)) z| ≤ 2 * η' + 4 * M * e := by
    rw [hdiff, ← hB]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun u => abs_nonneg _) hintB (Eventually.of_forall fun u => ?_))
    simp only
    rw [abs_mul, abs_of_nonneg (heatKernel_nonneg s hs.le 0 u)]
    exact hpt u
  have hMe : 4 * M * e ≤ η' := by
    have : e * (4 * M + 1) < η' := (lt_div_iff₀ (by positivity)).1 hn2
    nlinarith
  rw [Real.dist_eq]
  linarith

end LQGMetric.DFGPS

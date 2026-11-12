import Mathlib
import LatticeProb.LQG.LQGMeasure

/-!
# The Liouville quantum gravity measure under a continuous perturbation of the field

If `m` is the dyadic vague limit of the approximations `ε^{γ²/2} e^{γ h_ε(z)} dz` of the field with circle
averages `h_ε`, and `F : ℂ → ℝ` is continuous and is the locally uniform limit, along the dyadic scales, of the
circle averages `F_ε` of a perturbation, then the approximations of the field with circle averages `h_ε + F_ε`
converge vaguely to `e^{γ F} m` (`IsLQGLimit.add_continuous`).

This is the elementary part of the coordinate-free change of the field `h ↦ h + F` by a continuous function:
the density `e^{γ F_ε}` converges uniformly on every compact set, while the masses of compact sets under the
approximations of `h` stay bounded because they converge vaguely.
-/

namespace LatticeProb.LQG

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Uniform convergence of `F_k` to a continuous `F` on a compact set gives uniform convergence of
`exp (γ F_k)` to `exp (γ F)` there. -/
theorem tendstoUniformlyOn_exp_mul {F : ℂ → ℝ} {Fk : ℕ → ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hF : Continuous F) (γ : ℝ) (h : TendstoUniformlyOn Fk F atTop K) :
    TendstoUniformlyOn (fun k z => Real.exp (γ * Fk k z)) (fun z => Real.exp (γ * F z)) atTop K := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro η hη
  set c : ℝ := Real.exp (|γ| * |C|) with hc
  have hcpos : 0 < c := Real.exp_pos _
  set θ : ℝ := min (1 / (|γ| + 1)) (η / (4 * (|γ| + 1) * c)) with hθ
  have hθpos : 0 < θ := lt_min (by positivity) (by positivity)
  have hθ1 : θ ≤ 1 / (|γ| + 1) := min_le_left _ _
  have hθ2 : θ ≤ η / (4 * (|γ| + 1) * c) := min_le_right _ _
  filter_upwards [h θ hθpos] with k hk z hz
  have h1 : dist (F z) (Fk k z) < θ := hk z hz
  rw [Real.dist_eq] at h1 ⊢
  have hd : |Fk k z - F z| ≤ θ := by rw [abs_sub_comm]; exact h1.le
  have hγθ : |γ| * θ ≤ 1 := by
    calc |γ| * θ ≤ |γ| * (1 / (|γ| + 1)) := by gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith [abs_nonneg γ]
  have hγd : |γ * (Fk k z - F z)| ≤ 1 := by
    rw [abs_mul]
    calc |γ| * |Fk k z - F z| ≤ |γ| * θ := by gcongr
      _ ≤ 1 := hγθ
  have hFz : Real.exp (γ * F z) ≤ c := by
    rw [hc]
    apply Real.exp_le_exp.2
    have h3 := hC z hz
    rw [Real.norm_eq_abs] at h3
    calc γ * F z ≤ |γ * F z| := le_abs_self _
      _ = |γ| * |F z| := abs_mul _ _
      _ ≤ |γ| * |C| := mul_le_mul_of_nonneg_left (h3.trans (le_abs_self C)) (abs_nonneg γ)
  have hprod : Real.exp (γ * F z) * Real.exp (γ * (Fk k z - F z)) = Real.exp (γ * Fk k z) := by
    rw [← Real.exp_add]; congr 1; ring
  have key : Real.exp (γ * F z) - Real.exp (γ * Fk k z) =
      -(Real.exp (γ * F z) * (Real.exp (γ * (Fk k z - F z)) - 1)) := by
    rw [mul_sub, hprod, mul_one]; ring
  have hbound : |Real.exp (γ * F z) - Real.exp (γ * Fk k z)| ≤ c * (2 * (|γ| * θ)) := by
    rw [key, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (γ * F z) * |Real.exp (γ * (Fk k z - F z)) - 1|
        ≤ c * (2 * |γ * (Fk k z - F z)|) := by
          gcongr
          exact Real.abs_exp_sub_one_le hγd
      _ ≤ c * (2 * (|γ| * θ)) := by
          gcongr
          rw [abs_mul]
          gcongr
  have heq : c * (2 * (|γ| * (η / (4 * (|γ| + 1) * c)))) = η / 2 * (|γ| / (|γ| + 1)) := by
    field_simp
    ring
  have hfrac : |γ| / (|γ| + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc |Real.exp (γ * F z) - Real.exp (γ * Fk k z)| ≤ c * (2 * (|γ| * θ)) := hbound
    _ ≤ c * (2 * (|γ| * (η / (4 * (|γ| + 1) * c)))) := by gcongr
    _ = η / 2 * (|γ| / (|γ| + 1)) := heq
    _ ≤ η / 2 * 1 := by gcongr
    _ < η := by linarith

/-- Adding the circle averages `F_ε` of a perturbation to those of a field multiplies the approximation at
scale `ε` by the density `e^{γ F_ε}`. -/
theorem lqgApprox_add_eq_withDensity (γ : ℝ) {hε Fε : ℝ → ℂ → ℝ} {ε : ℝ} (hε0 : 0 < ε)
    (hm : Measurable (hε ε)) (hFm : Measurable (Fε ε)) :
    lqgApprox γ (fun ε z => hε ε z + Fε ε z) ε =
      (lqgApprox γ hε ε).withDensity fun z => ENNReal.ofReal (Real.exp (γ * Fε ε z)) := by
  unfold lqgApprox
  have hd : Measurable fun z : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul hm)))
  have he : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (γ * Fε ε z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hFm))
  rw [← withDensity_mul _ hd he]
  congr 1
  funext z
  have hnn : 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z) := by positivity
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hnn]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

/-- **The LQG measure under a continuous perturbation of the field.** Let `m` be the dyadic vague limit of the
approximations of the field with continuous (in `z`) circle averages `h_ε`. Let `F` be continuous, and let the
continuous functions `F_ε`, `ε = 2^{-k}`, converge to `F` uniformly on compact sets. Then the approximations of the
field with circle averages `h_ε + F_ε` converge vaguely, along the dyadic scales, to `e^{γ F} m`. -/
theorem IsLQGLimit.add_continuous {γ : ℝ} {hε Fε : ℝ → ℂ → ℝ} {m : Measure ℂ} (h : IsLQGLimit γ hε m)
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {F : ℂ → ℝ} (hF : Continuous F)
    (hFcont : ∀ k : ℕ, Continuous (Fε (dyadicScale k)))
    (hFlim : ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun (k : ℕ) => Fε (dyadicScale k)) F atTop K) :
    IsLQGLimit γ (fun ε z => hε ε z + Fε ε z)
      (m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * F z))) := by
  have := h.isLocallyFiniteMeasure
  have hpos : ∀ k : ℕ, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hEc : Continuous fun z => Real.exp (γ * F z) :=
    Real.continuous_exp.comp (continuous_const.mul hF)
  have hEmeas : Measurable fun z => ENNReal.ofReal (Real.exp (γ * F z)) :=
    ENNReal.measurable_ofReal.comp hEc.measurable
  refine ⟨IsLocallyFiniteMeasure.withDensity_ofReal hEc, fun g hg hgc => ?_⟩
  set ν : ℕ → Measure ℂ := fun k => lqgApprox γ hε (dyadicScale k) with hν
  have hνfin : ∀ k, IsLocallyFiniteMeasure (ν k) := fun k => by
    simp only [hν, lqgApprox]
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont k))))
  have hrew : ∀ k, ∫ z, g z ∂(lqgApprox γ (fun ε z => hε ε z + Fε ε z) (dyadicScale k)) =
      ∫ z, Real.exp (γ * Fε (dyadicScale k) z) * g z ∂(ν k) := by
    intro k
    have hmk : Measurable fun z => ENNReal.ofReal (Real.exp (γ * Fε (dyadicScale k) z)) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (hFcont k))).measurable
    rw [lqgApprox_add_eq_withDensity γ (hpos k) (hcont k).measurable (hFcont k).measurable,
      integral_withDensity_eq_integral_toReal_smul hmk
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp [ENNReal.toReal_ofReal (Real.exp_pos _).le, hν]
  have hlimit : ∫ z, g z ∂(m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * F z))) =
      ∫ z, Real.exp (γ * F z) * g z ∂m := by
    rw [integral_withDensity_eq_integral_toReal_smul hEmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [hlimit]
  simp_rw [hrew]
  have hg' : Continuous fun z => Real.exp (γ * F z) * g z := hEc.mul hg
  have hg'c : HasCompactSupport fun z => Real.exp (γ * F z) * g z := hgc.mul_left
  have h1 := h.tendsto_integral _ hg' hg'c
  -- the error term tends to zero
  have habs := h.tendsto_integral (fun z => |g z|) hg.abs hgc.abs
  have h2 : Tendsto (fun k => ∫ z, (Real.exp (γ * Fε (dyadicScale k) z) - Real.exp (γ * F z)) * g z
      ∂(ν k)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set L : ℝ := ∫ z, |g z| ∂m + 1 with hL
    have hL1 : 1 ≤ L := by
      have : 0 ≤ ∫ z, |g z| ∂m := integral_nonneg fun z => abs_nonneg _
      linarith
    have hLpos : 0 < L := by linarith
    set η' : ℝ := η / L with hη'
    have hη'pos : 0 < η' := div_pos hη hLpos
    have hexp := tendstoUniformlyOn_exp_mul hgc hF γ (hFlim _ hgc)
    rw [Metric.tendstoUniformlyOn_iff] at hexp
    have hev1 : ∀ᶠ k in atTop, ∀ z ∈ tsupport g,
        dist (Real.exp (γ * F z)) (Real.exp (γ * Fε (dyadicScale k) z)) < η' / 2 :=
      hexp (η' / 2) (by positivity)
    have hev2 : ∀ᶠ k in atTop, ∫ z, |g z| ∂(ν k) < L := by
      have := habs.eventually (gt_mem_nhds (show ∫ z, |g z| ∂m < L by rw [hL]; linarith))
      exact this
    filter_upwards [hev1, hev2] with k hk1 hk2
    have hint : Integrable (fun z => (Real.exp (γ * Fε (dyadicScale k) z) - Real.exp (γ * F z)) * g z)
        (ν k) := by
      have := hνfin k
      exact (((Real.continuous_exp.comp (continuous_const.mul (hFcont k))).sub hEc).mul
        hg).integrable_of_hasCompactSupport hgc.mul_left
    have hintabs : Integrable (fun z => |g z|) (ν k) := by
      have := hνfin k
      exact hg.abs.integrable_of_hasCompactSupport hgc.abs
    have hpt : ∀ z, ‖(Real.exp (γ * Fε (dyadicScale k) z) - Real.exp (γ * F z)) * g z‖ ≤
        η' / 2 * |g z| := by
      intro z
      by_cases hz : z ∈ tsupport g
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
        have := hk1 z hz
        rw [Real.dist_eq] at this
        exact mul_le_mul_of_nonneg_right this.le (abs_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hz]
        simp
    have hbd : ‖∫ z, (Real.exp (γ * Fε (dyadicScale k) z) - Real.exp (γ * F z)) * g z ∂(ν k)‖ ≤
        ∫ z, η' / 2 * |g z| ∂(ν k) :=
      norm_integral_le_of_norm_le (hintabs.const_mul _) (ae_of_all _ hpt)
    rw [integral_const_mul] at hbd
    rw [dist_zero_right]
    calc ‖∫ z, (Real.exp (γ * Fε (dyadicScale k) z) - Real.exp (γ * F z)) * g z ∂(ν k)‖
        ≤ η' / 2 * ∫ z, |g z| ∂(ν k) := hbd
      _ ≤ η' / 2 * L := by gcongr
      _ < η := by
        rw [hη']
        field_simp
        linarith
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr fun k => ?_
  have := hνfin k
  have hi1 : Integrable (fun z => Real.exp (γ * F z) * g z) (ν k) :=
    hg'.integrable_of_hasCompactSupport hg'c
  have hi2 : Integrable (fun z => (Real.exp (γ * Fε (dyadicScale k) z) - Real.exp (γ * F z)) * g z)
      (ν k) :=
    (((Real.continuous_exp.comp (continuous_const.mul (hFcont k))).sub hEc).mul
      hg).integrable_of_hasCompactSupport hgc.mul_left
  rw [← integral_add hi1 hi2]
  congr 1
  funext z
  ring

end LatticeProb.LQG

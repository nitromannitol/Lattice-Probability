/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127G4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127G2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Cont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 (L2), part 4: Hölder continuity of the coarse kernel from the decay of the survival
probability at the boundary (packet P-127G, task P2-HEATG)

* `sq_norm_wndKernelL2_le`: `‖K^{(t,∞)}_x‖² ≤ R²/(π t)`;
* `sq_norm_wndKernelL2_sub_le_surv`: G1 + G2;
* `coarseKer_holder_of_survDecay`: if `P^y(τ_U > t/8) ≤ C ρ^β` whenever `B(y, ρ) ⊄ U`
  (`0 < β ≤ 1`), then `‖K_x − K_{x'}‖² ≤ K |x − x'|^{β/4}` for all `x, x' ∈ ℂ`
  (parameters `τ₁ = (t/8)|x − x'|^{1/2}`, `ρ = |x − x'|^{1/8}`);
* `exists_continuous_coarseField_of_survDecay`: the continuous version (via
  `exists_continuous_modification_of_kernel_holder`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat DZZ WhiteNoise

/-- `‖K^{(t,∞)}_x‖² ≤ R²/(π t)`. -/
theorem sq_norm_wndKernelL2_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {t : ℝ} (ht : 0 < t) (x : ℂ) :
    ‖wndKernelL2 U (Ioi t) x‖ ^ 2 ≤ R ^ 2 / (Real.pi * t) := by
  rw [← real_inner_self_eq_norm_sq, inner_wndKernelL2 hU hR hUR measurableSet_Ioi ht Subset.rfl]
  have hint : IntegrableOn (fun s : ℝ => R ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht).const_mul _
  refine (setIntegral_mono_on (integrableOn_killedHeat_Ioi_G hU hR hUR ht x x) hint
    measurableSet_Ioi fun s hs => killedHeat_le_rpow hR hUR (ht.trans hs) x x).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ht,
    show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- G1 + G2. -/
theorem sq_norm_wndKernelL2_sub_le_surv {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hUR : U ⊆ ball c R) {t : ℝ} (ht : 0 < t) {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0)
    (h₂ : τ₂ ≠ 0) (hτt : 4 * ((τ₁ : ℝ) + τ₂) ≤ t) {ρ ω : ℝ} (hρ : 0 < ρ) (hω0 : 0 ≤ ω)
    (hω : ∀ y, ¬ ball y ρ ⊆ U → survG U τ₂ y ≤ ω) (x x' : ℂ) :
    ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2 ≤
      4 * R ^ 2 / (Real.pi * t) * ((1 / (16 * Real.pi) + Real.pi * R ^ 2 / 2) * ‖x - x'‖ / τ₁ +
        2 * (ω + killErrG ρ τ₁)) ^ 2 := by
  have h12 : τ₁ + τ₂ ≠ 0 := by positivity
  refine (sq_norm_wndKernelL2_sub_le hU hR hUR ht h12 (by push_cast; linarith) x x').trans ?_
  have hL := integral_abs_killedHeat_sub_le hU hR hUR h₁ h₂ hρ hω0 hω x x'
  have hL0 : 0 ≤ ∫ y, |killedHeat U (τ₁ + τ₂) x y - killedHeat U (τ₁ + τ₂) x' y| :=
    integral_nonneg fun _ => abs_nonneg _
  gcongr

lemma exp_neg_le_inv_G {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ y⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hy (by linarith [Real.add_one_le_exp y])

lemma killErrG_le {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) : killErrG ρ τ ≤ 104 * τ / ρ ^ 2 := by
  unfold killErrG
  have h1 := exp_neg_le_inv_G (y := 2 * (ρ / 4) ^ 2 / τ) (by positivity)
  have h2 := exp_neg_le_inv_G (y := (ρ / 3) ^ 2 / (4 * τ)) (by positivity)
  rw [show -(ρ / 3) ^ 2 / (4 * τ) = -((ρ / 3) ^ 2 / (4 * τ)) by ring]
  have e1 : (2 * (ρ / 4) ^ 2 / τ)⁻¹ = 8 * τ / ρ ^ 2 := by field_simp; ring
  have e2 : ((ρ / 3) ^ 2 / (4 * τ))⁻¹ = 36 * τ / ρ ^ 2 := by field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have : 104 * τ / ρ ^ 2 = 4 * (8 * τ / ρ ^ 2) + 2 * (36 * τ / ρ ^ 2) := by ring
  rw [this]
  linarith

/-- **(L2) from the boundary decay of the survival probability.** -/
theorem coarseKer_holder_of_survDecay {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {t : ℝ} (ht : 0 < t) {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β)
    (hβ1 : β ≤ 1)
    (hS : ∀ y : ℂ, ∀ ρ : ℝ, 0 < ρ → ¬ ball y ρ ⊆ U → survG U (t / 8).toNNReal y ≤ C * ρ ^ β) :
    ∃ K, 0 ≤ K ∧ ∀ x x' : ℂ,
      ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2 ≤ K * ‖x - x'‖ ^ (β / 4) := by
  set A : ℝ := 1 / (16 * Real.pi) + Real.pi * R ^ 2 / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set K1 : ℝ := 8 * A / t + 2 * C + 26 * t with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set B : ℝ := 4 * R ^ 2 / (Real.pi * t) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨B * max (K1 ^ 2) 1, by positivity, fun x x' => ?_⟩
  set d := ‖x - x'‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  rcases hd0.eq_or_lt with hd0' | hdpos
  · have hxx : x = x' := by
      have : ‖x - x'‖ = 0 := hd0'.symm
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    subst hxx
    have h0 : ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x‖ ^ 2 = 0 := by simp
    rw [h0]; positivity
  by_cases hd1 : 1 < d
  · -- far points: `‖K_x − K_{x'}‖² ≤ (‖K_x‖ + ‖K_{x'}‖)² ≤ 4R²/(π t)`
    have h1 := sq_norm_wndKernelL2_le hU hR hUR ht x
    have h2 := sq_norm_wndKernelL2_le hU hR hUR ht x'
    have hn1 : ‖wndKernelL2 U (Ioi t) x‖ ≤ Real.sqrt (R ^ 2 / (Real.pi * t)) :=
      Real.le_sqrt_of_sq_le h1
    have hn2 : ‖wndKernelL2 U (Ioi t) x'‖ ≤ Real.sqrt (R ^ 2 / (Real.pi * t)) :=
      Real.le_sqrt_of_sq_le h2
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ R ^ 2 / (Real.pi * t))
    have hdp : 1 ≤ d ^ (β / 4) := Real.one_le_rpow hd1.le (by positivity)
    calc ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2
        ≤ (‖wndKernelL2 U (Ioi t) x‖ + ‖wndKernelL2 U (Ioi t) x'‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ (2 * Real.sqrt (R ^ 2 / (Real.pi * t))) ^ 2 := by
          gcongr; linarith
      _ = B := by rw [mul_pow, hsq, hB]; field_simp; ring
      _ ≤ B * max (K1 ^ 2) 1 * d ^ (β / 4) := by
          have : 1 ≤ max (K1 ^ 2) 1 * d ^ (β / 4) :=
            one_le_mul_of_one_le_of_one_le (le_max_right _ _) hdp
          nlinarith
  push_neg at hd1
  -- near points
  set τ₁ : ℝ≥0 := (t / 8 * d ^ (1 / 2 : ℝ)).toNNReal with hτ₁
  set τ₂ : ℝ≥0 := (t / 8).toNNReal with hτ₂
  have hsq2 : 0 < d ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hdpos _
  have hτ₁c : (τ₁ : ℝ) = t / 8 * d ^ (1 / 2 : ℝ) := Real.coe_toNNReal _ (by positivity)
  have hτ₂c : (τ₂ : ℝ) = t / 8 := Real.coe_toNNReal _ (by positivity)
  have hτ₁0 : (0 : ℝ) < τ₁ := by rw [hτ₁c]; positivity
  have h₁ : τ₁ ≠ 0 := fun h => by rw [h] at hτ₁0; simp at hτ₁0
  have h₂ : τ₂ ≠ 0 := by rw [hτ₂]; simpa using ht
  have hsq1 : d ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hd0 hd1 (by norm_num)
  have hτt : 4 * ((τ₁ : ℝ) + τ₂) ≤ t := by
    rw [hτ₁c, hτ₂c]; nlinarith
  set ρ : ℝ := d ^ (1 / 8 : ℝ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hdpos _
  have hω := fun y (hy : ¬ ball y ρ ⊆ U) => hS y ρ hρ0 hy
  have hmain := sq_norm_wndKernelL2_sub_le_surv hU hR hUR ht h₁ h₂ hτt hρ0
    (by positivity : 0 ≤ C * ρ ^ β) hω x x'
  -- the three terms
  have hdd : d = d ^ (1 / 2 : ℝ) * d ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hdpos]; norm_num
  have t1 : A * d / τ₁ = 8 * A / t * d ^ (1 / 2 : ℝ) := by
    rw [hτ₁c]; nth_rewrite 1 [hdd]; field_simp
  have hρ2 : ρ ^ 2 = d ^ (1 / 4 : ℝ) := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hd0]; norm_num
  have t2 : killErrG ρ τ₁ ≤ 13 * t * d ^ (1 / 4 : ℝ) := by
    refine (killErrG_le hρ0 hτ₁0).trans (le_of_eq ?_)
    rw [hρ2, hτ₁c]
    have : d ^ (1 / 2 : ℝ) = d ^ (1 / 4 : ℝ) * d ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hdpos]; norm_num
    rw [this]
    have h4 : 0 < d ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hdpos _
    field_simp
    ring
  have t3 : C * ρ ^ β = C * d ^ (β / 8) := by
    rw [hρ, ← Real.rpow_mul hd0]; ring_nf
  have hb8 : β / 8 ≤ 1 / 4 := by linarith
  have p1 : d ^ (1 / 2 : ℝ) ≤ d ^ (β / 8) :=
    Real.rpow_le_rpow_of_exponent_ge hdpos hd1 (by linarith)
  have p2 : d ^ (1 / 4 : ℝ) ≤ d ^ (β / 8) := Real.rpow_le_rpow_of_exponent_ge hdpos hd1 hb8
  have hsum : A * d / τ₁ + 2 * (C * ρ ^ β + killErrG ρ τ₁) ≤ K1 * d ^ (β / 8) := by
    rw [t1, t3, hK1]
    have hA8 : 0 ≤ 8 * A / t := by positivity
    have : 8 * A / t * d ^ (1 / 2 : ℝ) ≤ 8 * A / t * d ^ (β / 8) :=
      mul_le_mul_of_nonneg_left p1 hA8
    have : 13 * t * d ^ (1 / 4 : ℝ) ≤ 13 * t * d ^ (β / 8) :=
      mul_le_mul_of_nonneg_left p2 (by positivity)
    nlinarith
  have hs0 : 0 ≤ A * d / τ₁ + 2 * (C * ρ ^ β + killErrG ρ τ₁) := by
    have := killErrG_nonneg ρ τ₁
    positivity
  have hsq8 : (d ^ (β / 8)) ^ 2 = d ^ (β / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd0]; ring_nf
  calc ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2
      ≤ B * (A * d / τ₁ + 2 * (C * ρ ^ β + killErrG ρ τ₁)) ^ 2 := hmain
    _ ≤ B * (K1 * d ^ (β / 8)) ^ 2 := by gcongr
    _ = B * K1 ^ 2 * d ^ (β / 4) := by rw [mul_pow, hsq8]; ring
    _ ≤ B * max (K1 ^ 2) 1 * d ^ (β / 4) := by
        gcongr
        exact le_max_left _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end ZBM
end CONF
end LQGMetric

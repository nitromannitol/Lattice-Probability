/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.TwoRadiusTilt at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

/-!
# M4-B1: one-point tilt estimates for a centered real Gaussian

Blueprint node M4-B1 (`blueprint/M4_BLUEPRINT.md`).

* `integral_exp_mul_Ioi_gaussianReal`: the exact tilt identity
  `E[e^{λN}; N > c] = e^{λ²σ²/2} P(N + λσ² > c)` for `N ~ 𝒩(0,σ²)`, `σ² > 0`;
* `gaussianReal_real_Ioi_le`: the Gaussian (Chernoff) tail `P(𝒩(m,σ²) > c) ≤ e^{-(c-m)²/2σ²}`;
* `integral_goodA_sq_le`, `integral_badA_le`: the truncated exponential moments used by the
  two-radius lemma (Chernoff form, valid for every tilt parameter `θ ≥ 0` and every variance
  bounded by `2L + K`);
* `integral_tiltY`, `integral_tiltY_sq_le`, `integral_abs_tiltY_le`: moments of the normalized
  factor `Y = e^{(γ/2)Δ - γ² Var Δ / 8}`, whose mean is exactly `1`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace TwoRadius

/-- Good (truncated) part of the one-point density `e^{-(γ²/4)L + (γ/2)x}`, on `{x ≤ αL}`. -/
noncomputable def goodA (γ α L x : ℝ) : ℝ :=
  if x ≤ α * L then exp (-(γ ^ 2 / 4) * L + γ / 2 * x) else 0

/-- Bad part of the one-point density, on `{x > αL}`. -/
noncomputable def badA (γ α L x : ℝ) : ℝ :=
  if x ≤ α * L then 0 else exp (-(γ ^ 2 / 4) * L + γ / 2 * x)

/-- The centered factor `1 - Y`, with `Y = e^{(γ/2)d - γ² w / 8}`. -/
noncomputable def tiltY (γ w d : ℝ) : ℝ := 1 - exp (-(γ ^ 2 / 8 * w) + γ / 2 * d)

lemma goodA_add_badA (γ α L x : ℝ) :
    goodA γ α L x + badA γ α L x = exp (-(γ ^ 2 / 4) * L + γ / 2 * x) := by
  unfold goodA badA; split_ifs <;> simp

lemma goodA_nonneg (γ α L x : ℝ) : 0 ≤ goodA γ α L x := by
  unfold goodA; split_ifs <;> positivity

lemma badA_nonneg (γ α L x : ℝ) : 0 ≤ badA γ α L x := by
  unfold badA; split_ifs <;> positivity

/-- On the good event the density is bounded: `goodA ≤ e^{(γ/2)(α - γ/2) L}`. -/
lemma goodA_le {γ α L x : ℝ} (hγ : 0 ≤ γ) :
    goodA γ α L x ≤ exp (γ / 2 * (α - γ / 2) * L) := by
  unfold goodA; split_ifs with hx
  · apply exp_le_exp.2; nlinarith [mul_le_mul_of_nonneg_left hx hγ]
  · positivity

lemma measurable_goodA₂ (γ α : ℝ) : Measurable (fun p : ℝ × ℝ => goodA γ α p.1 p.2) := by
  unfold goodA
  exact Measurable.ite (measurableSet_le measurable_snd (measurable_const.mul measurable_fst))
    (by fun_prop) measurable_const

lemma measurable_badA₂ (γ α : ℝ) : Measurable (fun p : ℝ × ℝ => badA γ α p.1 p.2) := by
  unfold badA
  exact Measurable.ite (measurableSet_le measurable_snd (measurable_const.mul measurable_fst))
    measurable_const (by fun_prop)

lemma measurable_goodA (γ α L : ℝ) : Measurable (goodA γ α L) :=
  (measurable_goodA₂ γ α).comp (measurable_const.prodMk measurable_id)

lemma measurable_badA (γ α L : ℝ) : Measurable (badA γ α L) :=
  (measurable_badA₂ γ α).comp (measurable_const.prodMk measurable_id)

lemma continuous_tiltY₂ (γ : ℝ) : Continuous (fun p : ℝ × ℝ => tiltY γ p.1 p.2) := by
  unfold tiltY; fun_prop

lemma measurable_tiltY (γ w : ℝ) : Measurable (tiltY γ w) := by
  unfold tiltY; fun_prop

/-! ### Exponential moments -/

lemma integral_exp_mul_add_gaussianReal (v : ℝ≥0) (a b : ℝ) :
    ∫ x, exp (b + a * x) ∂(gaussianReal 0 v) = exp (b + v * a ^ 2 / 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) a
  simp only [mgf] at h
  simp_rw [exp_add]
  rw [integral_const_mul, h]
  simp

lemma integrable_exp_mul_add_gaussianReal (v : ℝ≥0) (a b : ℝ) :
    Integrable (fun x => exp (b + a * x)) (gaussianReal 0 v) := by
  simp_rw [exp_add]
  exact (integrable_exp_mul_gaussianReal a).const_mul _

/-! ### Truncated moments (Chernoff form) -/

/-- Good part: `E[A²; N ≤ αL] ≤ e^{(γ-θ)²K/2} e^{(-γ²/2 + θα + (γ-θ)²) L}` for `θ ≥ 0`. -/
lemma integral_goodA_sq_le {γ α θ L K : ℝ} {v : ℝ≥0} (hθ : 0 ≤ θ)
    (hv : (v : ℝ) ≤ 2 * L + K) :
    ∫ x, goodA γ α L x ^ 2 ∂(gaussianReal 0 v)
      ≤ exp ((γ - θ) ^ 2 * K / 2) * exp ((-(γ ^ 2 / 2) + θ * α + (γ - θ) ^ 2) * L) := by
  have hpt : ∀ x, goodA γ α L x ^ 2 ≤ exp ((-(γ ^ 2 / 2) * L + θ * α * L) + (γ - θ) * x) := by
    intro x
    unfold goodA
    split_ifs with hx
    · rw [sq, ← exp_add]
      apply exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_left hx hθ]
    · rw [zero_pow two_ne_zero]; exact (exp_pos _).le
  calc ∫ x, goodA γ α L x ^ 2 ∂(gaussianReal 0 v)
      ≤ ∫ x, exp ((-(γ ^ 2 / 2) * L + θ * α * L) + (γ - θ) * x) ∂(gaussianReal 0 v) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          (integrable_exp_mul_add_gaussianReal v _ _) (ae_of_all _ hpt)
    _ = exp ((-(γ ^ 2 / 2) * L + θ * α * L) + v * (γ - θ) ^ 2 / 2) :=
        integral_exp_mul_add_gaussianReal v _ _
    _ ≤ _ := by
        rw [← exp_add]; apply exp_le_exp.2
        nlinarith [mul_nonneg (sq_nonneg (γ - θ)) (sub_nonneg.2 hv)]

/-- Bad part: `E[A; N > αL] ≤ e^{(γ/2+θ)²K/2} e^{(-γ²/4 - θα + (γ/2+θ)²) L}` for `θ ≥ 0`. -/
lemma integral_badA_le {γ α θ L K : ℝ} {v : ℝ≥0} (hθ : 0 ≤ θ)
    (hv : (v : ℝ) ≤ 2 * L + K) :
    ∫ x, badA γ α L x ∂(gaussianReal 0 v)
      ≤ exp ((γ / 2 + θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 4) - θ * α + (γ / 2 + θ) ^ 2) * L) := by
  have hpt : ∀ x, badA γ α L x ≤ exp ((-(γ ^ 2 / 4) * L - θ * α * L) + (γ / 2 + θ) * x) := by
    intro x
    unfold badA
    split_ifs with hx
    · positivity
    · apply exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_left (not_le.1 hx).le hθ]
  calc ∫ x, badA γ α L x ∂(gaussianReal 0 v)
      ≤ ∫ x, exp ((-(γ ^ 2 / 4) * L - θ * α * L) + (γ / 2 + θ) * x) ∂(gaussianReal 0 v) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => badA_nonneg _ _ _ _)
          (integrable_exp_mul_add_gaussianReal v _ _) (ae_of_all _ hpt)
    _ = exp ((-(γ ^ 2 / 4) * L - θ * α * L) + v * (γ / 2 + θ) ^ 2 / 2) :=
        integral_exp_mul_add_gaussianReal v _ _
    _ ≤ _ := by
        rw [← exp_add]; apply exp_le_exp.2
        nlinarith [mul_nonneg (sq_nonneg (γ / 2 + θ)) (sub_nonneg.2 hv)]

lemma integrable_badA_gaussianReal (γ α L : ℝ) (v : ℝ≥0) :
    Integrable (badA γ α L) (gaussianReal 0 v) := by
  refine Integrable.mono' (integrable_exp_mul_add_gaussianReal v (γ / 2) (-(γ ^ 2 / 4) * L))
    (measurable_badA γ α L).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (badA_nonneg _ _ _ _)]
  unfold badA; split_ifs <;> [positivity; exact le_rfl]

/-! ### The normalized factor `Y` -/

lemma integral_tiltY (γ : ℝ) (w : ℝ≥0) : ∫ d, tiltY γ w d ∂(gaussianReal 0 w) = 0 := by
  unfold tiltY
  rw [integral_sub (integrable_const _) (integrable_exp_mul_add_gaussianReal w _ _),
    integral_exp_mul_add_gaussianReal,
    show -(γ ^ 2 / 8 * (w : ℝ)) + (w : ℝ) * (γ / 2) ^ 2 / 2 = 0 by ring]
  simp

lemma tiltY_sq_le (γ w d : ℝ) : tiltY γ w d ^ 2 ≤ 1 + exp (-(γ ^ 2 / 4 * w) + γ * d) := by
  unfold tiltY
  have hE : exp (-(γ ^ 2 / 8 * w) + γ / 2 * d) ^ 2 = exp (-(γ ^ 2 / 4 * w) + γ * d) := by
    rw [sq, ← exp_add]; congr 1; ring
  nlinarith [hE, exp_pos (-(γ ^ 2 / 8 * w) + γ / 2 * d)]

lemma abs_tiltY_le (γ w d : ℝ) : |tiltY γ w d| ≤ 1 + exp (-(γ ^ 2 / 8 * w) + γ / 2 * d) := by
  unfold tiltY
  have := exp_pos (-(γ ^ 2 / 8 * w) + γ / 2 * d)
  rw [abs_le]; constructor <;> linarith

lemma integrable_tiltY_sq (γ : ℝ) (w : ℝ≥0) :
    Integrable (fun d => tiltY γ w d ^ 2) (gaussianReal 0 w) := by
  refine Integrable.mono' ((integrable_const 1).add
    (integrable_exp_mul_add_gaussianReal w γ (-(γ ^ 2 / 4 * w))))
    ((measurable_tiltY γ w).pow_const 2).aestronglyMeasurable (ae_of_all _ fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact tiltY_sq_le γ w d

lemma integral_tiltY_sq_le (γ : ℝ) (w : ℝ≥0) :
    ∫ d, tiltY γ w d ^ 2 ∂(gaussianReal 0 w) ≤ 1 + exp (γ ^ 2 / 4 * w) := by
  calc ∫ d, tiltY γ w d ^ 2 ∂(gaussianReal 0 w)
      ≤ ∫ d, (1 + exp (-(γ ^ 2 / 4 * w) + γ * d)) ∂(gaussianReal 0 w) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          ((integrable_const 1).add (integrable_exp_mul_add_gaussianReal w γ _))
          (ae_of_all _ fun d => tiltY_sq_le γ w d)
    _ = 1 + exp (γ ^ 2 / 4 * w) := by
        rw [integral_add (integrable_const _) (integrable_exp_mul_add_gaussianReal w γ _),
          integral_exp_mul_add_gaussianReal,
          show -(γ ^ 2 / 4 * (w : ℝ)) + (w : ℝ) * γ ^ 2 / 2 = γ ^ 2 / 4 * w by ring]
        simp

lemma integral_abs_tiltY_le (γ : ℝ) (w : ℝ≥0) :
    ∫ d, |tiltY γ w d| ∂(gaussianReal 0 w) ≤ 2 := by
  calc ∫ d, |tiltY γ w d| ∂(gaussianReal 0 w)
      ≤ ∫ d, (1 + exp (-(γ ^ 2 / 8 * w) + γ / 2 * d)) ∂(gaussianReal 0 w) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          ((integrable_const 1).add (integrable_exp_mul_add_gaussianReal w _ _))
          (ae_of_all _ fun d => abs_tiltY_le γ w d)
    _ = 2 := by
        rw [integral_add (integrable_const _) (integrable_exp_mul_add_gaussianReal w _ _),
          integral_exp_mul_add_gaussianReal,
          show -(γ ^ 2 / 8 * (w : ℝ)) + (w : ℝ) * (γ / 2) ^ 2 / 2 = 0 by ring]
        norm_num

/-! ### The exact tilt identity and the Gaussian tail -/

end TwoRadius
end QuantumZipper

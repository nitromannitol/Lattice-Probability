/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareLip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareTheta

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Lipschitz bound with large-time decay for the image kernel (task P2-DDDFP29, WP-110)

`HeatSq.abs_intervalDirKernel_sub_sub_le`: for `s ≥ 1`,
`|q_s(u,v) − q_s(u',v)| ≤ C(L) e^{−π²s/(2L²)} |u − u'|`, from the cosine series
(`tsum_gauss1_shift_eq_cos`) and `|cos x − cos y| ≤ |x − y|`. These are the "gradient
estimates" for the killed kernel at large times used in DDDF Prop 29 (`tightness.tex:1574`,
first term for `s ≥ √|x−x'|`, and the third term `η²_t`, `tightness.tex:1590–1596`).
-/

noncomputable section

open Real

namespace LQGMetric
namespace HeatSq

/-- The constant of the Lipschitz bound (times `s ≥ s₀`). -/
def lipConst (L s₀ : ℝ) : ℝ :=
  (2 * L)⁻¹ * (2 * π / L) * (2 / (π ^ 2 / (2 * L ^ 2) * s₀)) *
    Real.exp (π ^ 2 / (2 * L ^ 2) * s₀) *
    ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀) / 2) ^ k.natAbs

lemma natAbs_mul_exp_le {l : ℝ} (hl : 0 < l) (k : ℤ) :
    (k.natAbs : ℝ) * Real.exp (-l) ^ k.natAbs ≤ (2 / l) * Real.exp (-l / 2) ^ k.natAbs := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have h1 : l * k.natAbs / 2 ≤ Real.exp (l * k.natAbs / 2) := by
    linarith [Real.add_one_le_exp (l * k.natAbs / 2)]
  have h2 : Real.exp (k.natAbs * -l) = Real.exp (k.natAbs * (-l / 2)) *
      Real.exp (-(l * k.natAbs / 2)) := by rw [← Real.exp_add]; ring_nf
  rw [h2]
  have he : Real.exp (l * k.natAbs / 2) * Real.exp (-(l * k.natAbs / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (k.natAbs * (-l / 2))
  have hpos2 := Real.exp_pos (-(l * k.natAbs / 2))
  calc (k.natAbs : ℝ) * (Real.exp (k.natAbs * (-l / 2)) * Real.exp (-(l * k.natAbs / 2)))
      = (2 / l) * Real.exp (k.natAbs * (-l / 2)) *
          ((l * k.natAbs / 2) * Real.exp (-(l * k.natAbs / 2))) := by
        have hl' : l ≠ 0 := hl.ne'
        field_simp
    _ ≤ (2 / l) * Real.exp (k.natAbs * (-l / 2)) *
          (Real.exp (l * k.natAbs / 2) * Real.exp (-(l * k.natAbs / 2))) := by
        gcongr
    _ = _ := by rw [he, mul_one]

lemma lip_term_le {l s : ℝ} (hl0 : 0 < l) (hs : 1 ≤ s) (α α' β β' c : ℝ)
    (hα : |α - α'| ≤ c) (hβ : |β - β'| ≤ c) (k : ℤ) :
    |(Real.exp (-l * s * k ^ 2) * Real.cos (k * α) - Real.exp (-l * s * k ^ 2) * Real.cos (k * β)) -
      (Real.exp (-l * s * k ^ 2) * Real.cos (k * α') -
        Real.exp (-l * s * k ^ 2) * Real.cos (k * β'))| ≤
      2 * c * Real.exp l * Real.exp (-l * s) * ((2 / l) * Real.exp (-l / 2) ^ k.natAbs) := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hα
  by_cases hk : k = 0
  · subst hk; simp only [Int.cast_zero, zero_mul, Real.cos_zero, sub_self, abs_zero]
    positivity
  have hkabs : |(k : ℝ)| = k.natAbs := by rw [Nat.cast_natAbs, Int.cast_abs]
  have e : (Real.exp (-l * s * k ^ 2) * Real.cos (k * α) -
      Real.exp (-l * s * k ^ 2) * Real.cos (k * β)) - (Real.exp (-l * s * k ^ 2) *
        Real.cos (k * α') - Real.exp (-l * s * k ^ 2) * Real.cos (k * β')) =
      Real.exp (-l * s * k ^ 2) * ((Real.cos (k * α) - Real.cos (k * α')) -
        (Real.cos (k * β) - Real.cos (k * β'))) := by ring
  rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |Real.cos (k * α) - Real.cos (k * α')| ≤ k.natAbs * c := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul, hkabs]; exact mul_le_mul_of_nonneg_left hα (by positivity)
  have h2 : |Real.cos (k * β) - Real.cos (k * β')| ≤ k.natAbs * c := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul, hkabs]; exact mul_le_mul_of_nonneg_left hβ (by positivity)
  have h3 : |(Real.cos (k * α) - Real.cos (k * α')) - (Real.cos (k * β) - Real.cos (k * β'))|
      ≤ 2 * c * k.natAbs := by
    have := abs_sub (Real.cos (k * α) - Real.cos (k * α')) (Real.cos (k * β) - Real.cos (k * β'))
    linarith
  have h4 := exp_neg_mul_sq_le hl0 hs hk
  have h5 := natAbs_mul_exp_le hl0 k
  calc Real.exp (-l * s * k ^ 2) * |(Real.cos (k * α) - Real.cos (k * α')) -
        (Real.cos (k * β) - Real.cos (k * β'))|
      ≤ (Real.exp l * Real.exp (-l * s) * Real.exp (-l) ^ k.natAbs) * (2 * c * k.natAbs) :=
        mul_le_mul h4 h3 (abs_nonneg _) (by positivity)
    _ = 2 * c * Real.exp l * Real.exp (-l * s) * (k.natAbs * Real.exp (-l) ^ k.natAbs) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)

/-- **Lipschitz bound with decay**: for `0 < s₀ ≤ s`,
`|q_s(u,v) − q_s(u',v)| ≤ C(L,s₀) e^{−π²s/(2L²)} |u − u'|`. -/
theorem abs_intervalDirKernel_sub_sub_le {a L s s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hs : s₀ ≤ s) (u u' v : ℝ) :
    |intervalDirKernel a L s u v - intervalDirKernel a L s u' v| ≤
      lipConst L s₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s) * |u - u'| := by
  have hl0 : 0 < π ^ 2 / (2 * L ^ 2) := by positivity
  have hl0' : 0 < π ^ 2 / (2 * L ^ 2) * s₀ := by positivity
  have hs1 : 1 ≤ s / s₀ := (one_le_div hs₀).mpr hs
  have hs0 : 0 < s := hs₀.trans_le hs
  have hr01 : Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀) / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hG : Summable (fun k : ℤ => Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2)) := by
    have := summable_exp_neg_mul_int_sq' (l := π ^ 2 / (2 * L ^ 2) * s) (by positivity)
    refine this.congr fun k => ?_
    ring_nf
  have hcos : ∀ α : ℝ, Summable (fun k : ℤ =>
      Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) * Real.cos (k * α)) :=
    fun α => Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) hG)
  have hcosEq : ∀ c : ℝ, ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) *
      Real.cos (π * k * c / L) = ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) *
      Real.cos (k * (π * c / L)) := fun c => by
    congr 1; funext k; congr 2; ring
  rw [intervalDirKernel_eq_sub hs0 hL, intervalDirKernel_eq_sub hs0 hL,
    tsum_gauss1_shift_eq_cos hs0 hL, tsum_gauss1_shift_eq_cos hs0 hL,
    tsum_gauss1_shift_eq_cos hs0 hL, tsum_gauss1_shift_eq_cos hs0 hL,
    hcosEq, hcosEq, hcosEq, hcosEq, ← mul_sub, ← mul_sub, ← mul_sub,
    ← (hcos _).tsum_sub (hcos _), ← (hcos _).tsum_sub (hcos _),
    ← ((hcos _).sub (hcos _)).tsum_sub ((hcos _).sub (hcos _))]
  set c := π / L * |u - u'|
  have hα : |π * (u - v) / L - π * (u' - v) / L| ≤ c := by
    rw [show π * (u - v) / L - π * (u' - v) / L = π / L * (u - u') by ring, abs_mul,
      abs_of_pos (by positivity : 0 < π / L)]
  have hβ : |π * (u + v - 2 * a) / L - π * (u' + v - 2 * a) / L| ≤ c := by
    rw [show π * (u + v - 2 * a) / L - π * (u' + v - 2 * a) / L = π / L * (u - u') by ring,
      abs_mul, abs_of_pos (by positivity : 0 < π / L)]
  have hd := ((hcos (π * (u - v) / L)).sub (hcos (π * (u + v - 2 * a) / L))).sub
    ((hcos (π * (u' - v) / L)).sub (hcos (π * (u' + v - 2 * a) / L)))
  have hh := ((summable_geom_natAbs (Real.exp_pos _).le hr01).mul_left
    (2 / (π ^ 2 / (2 * L ^ 2) * s₀))).mul_left (2 * c * Real.exp (π ^ 2 / (2 * L ^ 2) * s₀) *
      Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀) * (s / s₀)))
  have hb := (norm_tsum_le_tsum_norm hd.norm).trans (hd.norm.tsum_le_tsum
    (fun k => by
      rw [Real.norm_eq_abs, exp_rescale _ s s₀ hs₀ k]
      exact lip_term_le hl0' hs1 _ _ _ _ c hα hβ k) hh)
  rw [Real.norm_eq_abs, tsum_mul_left, tsum_mul_left] at hb
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * L)⁻¹)]
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
  have e : -(π ^ 2 / (2 * L ^ 2) * s₀) * (s / s₀) = -(π ^ 2 / (2 * L ^ 2)) * s := by
    field_simp
  rw [e]
  unfold lipConst
  simp only [c]
  ring

end HeatSq
end LQGMetric

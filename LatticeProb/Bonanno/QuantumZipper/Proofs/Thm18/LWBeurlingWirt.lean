/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingWirt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingDefs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-4, node B1: the sharp Wirtinger inequality (`WirtingerDirStmt`, `WirtingerCircleStmt`)

Plan: `handoff/LW-BEURLING.md`. Source: Garnett–Marshall, *Harmonic Measure*, App. G, (G.2),
p. 480: if `g(a) = g(b) = 0` then `∫_a^b g'² ≥ (π/(b−a))² ∫_a^b g²`; here `b − a = 2π`.
GM prove it by Fourier series; we use the equivalent Picone (ground-state) identity with
`sin((x−a)/2)` (own elementary proof, avoids Fourier series): with `c = cos(y)/(2 sin y)`,
`y = (x−a)/2`, on `(a, a+2π)`
`g'² − g²/4 = (g' − g c)² + (g² c)'`,
integrated over `[a+δ, a+2π−δ]`; the boundary terms are `O(δ)` because `|g| ≤ L·dist` to the
endpoints and `sin(δ/2) ≥ δ/π` (Jordan), and the two end strips are `O(δ)`.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The Picone weight `c(x) = cos((x−a)/2) / (2 sin((x−a)/2))`. -/
def lwbPic (a x : ℝ) : ℝ := Real.cos ((x - a) / 2) / (2 * Real.sin ((x - a) / 2))

lemma lwbPic_hasDerivAt (a x : ℝ) (hs : Real.sin ((x - a) / 2) ≠ 0) :
    HasDerivAt (lwbPic a) (-1 / (4 * Real.sin ((x - a) / 2) ^ 2)) x := by
  have hy : HasDerivAt (fun x : ℝ => (x - a) / 2) (1 / 2) x :=
    ((hasDerivAt_id x).sub_const a).div_const 2
  have hc := hy.cos
  have hsn := (hy.sin).const_mul 2
  have := hc.fun_div hsn (by simpa using hs)
  refine this.congr_deriv ?_
  have h1 := Real.sin_sq_add_cos_sq ((x - a) / 2)
  field_simp
  nlinarith [h1]

/-- The pointwise Picone inequality. -/
lemma lwbPic_pointwise (u u' s co : ℝ) (hs : s ≠ 0) (hsc : s ^ 2 + co ^ 2 = 1) :
    2 * u * u' * (co / (2 * s)) + u ^ 2 * (-1 / (4 * s ^ 2)) ≤ u' ^ 2 - u ^ 2 / 4 := by
  have key : u' ^ 2 - u ^ 2 / 4 - (2 * u * u' * (co / (2 * s)) + u ^ 2 * (-1 / (4 * s ^ 2))) =
      (u' - u * (co / (2 * s))) ^ 2 := by
    field_simp
    linear_combination (-4 * u ^ 2) * hsc
  nlinarith [sq_nonneg (u' - u * (co / (2 * s)))]

/-- **B1a** (`WirtingerDirStmt`). -/
theorem wirtingerDirStmt_holds : WirtingerDirStmt := by
  intro g g' a hd hc ha hb
  set b := a + 2 * π with hb_def
  have hab : a ≤ b := by rw [hb_def]; linarith [Real.pi_pos]
  have hgc : ContinuousOn g (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  set G : ℝ → ℝ := fun x => g' x ^ 2 - g x ^ 2 / 4 with hG
  have hGc : ContinuousOn G (Icc a b) := (hc.pow 2).sub ((hgc.pow 2).div_const 4)
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL a ⟨le_rfl, hab⟩)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK a ⟨le_rfl, hab⟩)
  -- Lipschitz bounds at the two endpoints
  have hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g y - g x| ≤ L * |y - x| := by
    intro x hx y hy
    have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := g) (f' := g') (fun z hz => (hd z hz).hasDerivWithinAt) hL hx hy
    simpa [Real.norm_eq_abs] using this
  have hGint : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable G volume x y := by
    intro x hx y hy
    exact (hGc.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  -- the main estimate for every small `δ`
  have hmain : ∀ δ : ℝ, 0 < δ → δ ≤ π / 2 →
      -((2 * K + L ^ 2 * π) * δ) ≤ ∫ x in a..b, G x := by
    intro δ hδ hδπ
    set α := a + δ with hα
    set β := b - δ with hβ
    have hαβ : α ≤ β := by rw [hα, hβ, hb_def]; linarith
    have hαI : α ∈ Icc a b := ⟨by linarith, by linarith⟩
    have hβI : β ∈ Icc a b := ⟨by linarith, by linarith⟩
    have hsub : Icc α β ⊆ Icc a b := Icc_subset_Icc hαI.1 hβI.2
    -- positivity of the sine on `[α, β]`
    have hsin : ∀ x ∈ Icc α β, 0 < Real.sin ((x - a) / 2) := by
      intro x hx
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := hx.1; rw [hα] at this; linarith
      · have := hx.2; rw [hβ, hb_def] at this; linarith
    set P : ℝ → ℝ := fun x => g x ^ 2 * lwbPic a x with hP
    set P' : ℝ → ℝ := fun x => 2 * g x * g' x * lwbPic a x +
      g x ^ 2 * (-1 / (4 * Real.sin ((x - a) / 2) ^ 2)) with hP'
    have hPd : ∀ x ∈ uIcc α β, HasDerivAt P (P' x) x := by
      intro x hx
      rw [uIcc_of_le hαβ] at hx
      have h1 := ((hd x (hsub hx)).pow 2).mul (lwbPic_hasDerivAt a x (hsin x hx).ne')
      refine h1.congr_deriv ?_
      simp only [hP', Pi.pow_apply]
      push_cast
      ring
    have hP'c : ContinuousOn P' (Icc α β) := by
      have hsc : ContinuousOn (fun x : ℝ => Real.sin ((x - a) / 2)) (Icc α β) :=
        (Real.continuous_sin.comp ((continuous_id.sub continuous_const).div_const 2)).continuousOn
      have hcc : ContinuousOn (fun x : ℝ => Real.cos ((x - a) / 2)) (Icc α β) :=
        (Real.continuous_cos.comp ((continuous_id.sub continuous_const).div_const 2)).continuousOn
      have hpic : ContinuousOn (lwbPic a) (Icc α β) :=
        hcc.div (continuousOn_const.mul hsc) fun x hx => (mul_pos two_pos (hsin x hx)).ne'
      exact (((continuousOn_const.mul (hgc.mono hsub)).mul (hc.mono hsub)).mul hpic).add
        (((hgc.mono hsub).pow 2).mul (continuousOn_const.div (continuousOn_const.mul (hsc.pow 2))
          fun x hx => (mul_pos four_pos (pow_pos (hsin x hx) 2)).ne'))
    have hFTC : ∫ x in α..β, P' x = P β - P α :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hPd
        ((hP'c.mono (by rw [uIcc_of_le hαβ])).intervalIntegrable)
    have hmid : P β - P α ≤ ∫ x in α..β, G x := by
      rw [← hFTC]
      refine intervalIntegral.integral_mono_on hαβ
        ((hP'c.mono (by rw [uIcc_of_le hαβ])).intervalIntegrable) (hGint α hαI β hβI) ?_
      intro x hx
      have hs := hsin x hx
      have := lwbPic_pointwise (g x) (g' x) (Real.sin ((x - a) / 2)) (Real.cos ((x - a) / 2))
        hs.ne' (Real.sin_sq_add_cos_sq _)
      simpa [hP', hG, lwbPic] using this
    -- boundary terms
    have hJ : 2 / π * (δ / 2) ≤ Real.sin (δ / 2) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hsδ : 0 < Real.sin (δ / 2) := lt_of_lt_of_le (by positivity) hJ
    have hbd : ∀ x ∈ ({α, β} : Set ℝ), |P x| ≤ L ^ 2 * π * δ / 2 := by
      intro x hx
      have hsx : Real.sin ((x - a) / 2) = Real.sin (δ / 2) := by
        rcases hx with rfl | rfl
        · congr 1; rw [hα]; ring
        · rw [show (β - a) / 2 = π - δ / 2 by rw [hβ, hb_def]; ring, Real.sin_pi_sub]
      have hgx : |g x| ≤ L * δ := by
        rcases hx with rfl | rfl
        · have := hLip a ⟨le_rfl, hab⟩ α hαI
          rw [ha, sub_zero, show α - a = δ by rw [hα]; ring, abs_of_pos hδ] at this
          exact this
        · have := hLip b ⟨hab, le_rfl⟩ β hβI
          rw [hb, sub_zero, show β - b = -δ by rw [hβ]; ring, abs_neg, abs_of_pos hδ] at this
          exact this
      have hcos : |Real.cos ((x - a) / 2)| ≤ 1 := Real.abs_cos_le_one _
      simp only [hP, lwbPic, hsx]
      rw [abs_mul, abs_div, abs_of_pos (mul_pos two_pos hsδ), abs_pow]
      have hg2 : |g x| ^ 2 ≤ (L * δ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hgx 2
      calc |g x| ^ 2 * (|Real.cos ((x - a) / 2)| / (2 * Real.sin (δ / 2)))
          ≤ (L * δ) ^ 2 * (1 / (2 * Real.sin (δ / 2))) := by
            apply mul_le_mul hg2 _ (by positivity) (by positivity)
            exact div_le_div_of_nonneg_right hcos (by positivity)
        _ ≤ (L * δ) ^ 2 * (1 / (2 * (2 / π * (δ / 2)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply one_div_le_one_div_of_le (by positivity)
            linarith
        _ = L ^ 2 * π * δ / 2 := by field_simp
    have hPα := hbd α (by simp)
    have hPβ := hbd β (by simp)
    -- end strips
    have hend : ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b → |x - y| ≤ δ →
        -(K * δ) ≤ ∫ z in x..y, G z := by
      intro x y hx hy hxy
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y) (C := K)
        (f := G) (fun z hz => hK z (uIcc_subset_Icc hx hy (uIoc_subset_uIcc hz)))
      rw [Real.norm_eq_abs] at h
      have : K * |y - x| ≤ K * δ := mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm]) hK0
      linarith [neg_abs_le (∫ z in x..y, G z)]
    have hs1 := hend a α ⟨le_rfl, hab⟩ hαI (by rw [hα]; simp [abs_of_pos hδ])
    have hs3 := hend β b hβI ⟨hab, le_rfl⟩ (by rw [hβ]; simp [abs_of_pos hδ])
    have hsplit : ∫ x in a..b, G x =
        (∫ x in a..α, G x) + (∫ x in α..β, G x) + ∫ x in β..b, G x := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hGint a ⟨le_rfl, hab⟩ α hαI)
          (hGint α hαI β hβI),
        intervalIntegral.integral_add_adjacent_intervals (hGint a ⟨le_rfl, hab⟩ β hβI)
          (hGint β hβI b ⟨hab, le_rfl⟩)]
    rw [hsplit]
    have := abs_le.1 hPα
    have := abs_le.1 hPβ
    nlinarith
  -- let `δ → 0`
  have hG0 : 0 ≤ ∫ x in a..b, G x := by
    by_contra hneg
    push Not at hneg
    set X := ∫ x in a..b, G x
    set A := 2 * K + L ^ 2 * π + 1 with hA
    have hA0 : 0 < A := by rw [hA]; positivity
    set δ := min (π / 2) (-X / (2 * A)) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (div_pos (by linarith) (by positivity))
    have h1 := hmain δ hδ0 (min_le_left _ _)
    have h2 : δ ≤ -X / (2 * A) := min_le_right _ _
    have h3 : (2 * K + L ^ 2 * π) * δ ≤ A * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ0.le; rw [hA]; linarith
    have h4 : A * δ ≤ -X / 2 := by
      calc A * δ ≤ A * (-X / (2 * A)) := mul_le_mul_of_nonneg_left h2 hA0.le
        _ = -X / 2 := by field_simp
    linarith
  -- conclude
  have hi1 : IntervalIntegrable (fun x => g' x ^ 2) volume a b :=
    ((hc.pow 2).mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => g x ^ 2 / 4) volume a b :=
    (((hgc.pow 2).div_const 4).mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hsplitG : ∫ x in a..b, G x = (∫ x in a..b, g' x ^ 2) - (∫ x in a..b, g x ^ 2) / 4 := by
    simp only [hG]
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_div]
  rw [hsplitG] at hG0
  linarith

/-- **B1b** (`WirtingerCircleStmt`), from B1a by periodicity. -/
theorem wirtingerCircleStmt_holds : WirtingerCircleStmt := by
  intro g g' hd hc hper hz
  obtain ⟨θ₀, hθ₀⟩ := hz
  have hper' : Function.Periodic g' (2 * π) := by
    intro x
    have h1 : HasDerivAt (fun y => g (y + 2 * π)) (g' (x + 2 * π)) x :=
      (hd (x + 2 * π)).comp_add_const x (2 * π)
    have h2 : (fun y => g (y + 2 * π)) = g := funext hper
    rw [h2] at h1
    exact h1.unique (hd x)
  have hg2 : Function.Periodic (fun x => g x ^ 2) (2 * π) := fun x => by simp [hper x]
  have hg'2 : Function.Periodic (fun x => g' x ^ 2) (2 * π) := fun x => by simp [hper' x]
  have hW := wirtingerDirStmt_holds g g' θ₀ (fun x _ => hd x) hc.continuousOn hθ₀
    (by rw [hper θ₀]; exact hθ₀)
  have e1 : ∫ x in (-π)..π, g x ^ 2 = ∫ x in θ₀..θ₀ + 2 * π, g x ^ 2 := by
    have := hg2.intervalIntegral_add_eq (-π) θ₀
    rw [show -π + 2 * π = π by ring] at this
    exact this
  have e2 : ∫ x in (-π)..π, g' x ^ 2 = ∫ x in θ₀..θ₀ + 2 * π, g' x ^ 2 := by
    have := hg'2.intervalIntegral_add_eq (-π) θ₀
    rw [show -π + 2 * π = π by ring] at this
    exact this
  rw [e1, e2]
  exact hW

end LWFar
end Thm18Asm
end QuantumZipper

/-
Integrating a differential inequality.

Step 3 of `thm:subcritical` (`parking.tex:2478-2492`) integrates the
logarithmic derivative of `φ(λ) = Ê_λ F` over `[0, λ₁]`.  Dividing by `φ` is
not needed and is not done here: if `G` is any antiderivative of `g` vanishing
at zero, the product `φ e^{-G/3}` has nonnegative derivative exactly when
`g φ ≤ 3 φ'`, so it is nondecreasing and the bound at `0` follows from the
value at `λ₁`.  This form does not assume `φ` positive, which is what makes the
case `φ(0) = 0` of the paper's proof unnecessary.

The antiderivative `G` is supplied as data because the function to be integrated
is continuous only on `[0, λ₁]`: composing it with the clamp of `ℝ` onto
`[0, λ₁]` makes it continuous everywhere, so `u ↦ ∫₀^u` of the clamped function
is differentiable at every point, agrees with the paper's integral at `λ₁`, and
is the `G` the inequality above wants.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set

noncomputable section

namespace LatticeProb

/-- **The integrated form of `3 φ' ≥ g φ`.** -/
theorem le_mul_exp_of_deriv_ge {φ dφ G g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hG : ∀ s ∈ Set.Icc 0 b, HasDerivWithinAt G (g s) (Set.Icc 0 b) s) (hG0 : G 0 = 0)
    (hφ : ∀ s ∈ Set.Icc 0 b, HasDerivWithinAt φ (dφ s) (Set.Icc 0 b) s)
    (hineq : ∀ s ∈ Set.Icc 0 b, g s * φ s ≤ 3 * dφ s) :
    φ 0 ≤ φ b * Real.exp (-(G b / 3)) := by
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) b,
      HasDerivWithinAt (fun u => φ u * Real.exp (-(G u / 3)))
        ((dφ s - g s * φ s / 3) * Real.exp (-(G s / 3))) (Set.Icc 0 b) s := by
    intro s hs
    have h2 : HasDerivWithinAt (fun u => Real.exp (-(G u / 3)))
        (Real.exp (-(G s / 3)) * -(g s / 3)) (Set.Icc 0 b) s :=
      (((hG s hs).div_const 3).neg).exp
    have h3 := (hφ s hs).mul h2
    have heq : dφ s * Real.exp (-(G s / 3)) + φ s * (Real.exp (-(G s / 3)) * -(g s / 3))
        = (dφ s - g s * φ s / 3) * Real.exp (-(G s / 3)) := by ring
    rwa [heq] at h3
  have hcont : ContinuousOn (fun u => φ u * Real.exp (-(G u / 3))) (Set.Icc 0 b) :=
    fun s hs => (hderiv s hs).continuousWithinAt
  have hsub : interior (Set.Icc (0:ℝ) b) ⊆ Set.Icc 0 b := interior_subset
  have hmono : MonotoneOn (fun u => φ u * Real.exp (-(G u / 3))) (Set.Icc 0 b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b) hcont
      (fun s hs => (hderiv s (hsub hs)).mono hsub) (fun s hs => ?_)
    have h1 := hineq s (hsub hs)
    have h2 : (0:ℝ) < Real.exp (-(G s / 3)) := Real.exp_pos _
    have h3 : 0 ≤ dφ s - g s * φ s / 3 := by linarith
    exact mul_nonneg h3 (le_of_lt h2)
  have hmain := hmono (Set.left_mem_Icc.mpr hb) (Set.right_mem_Icc.mpr hb) hb
  simpa [hG0] using hmain

/-- The clamp of `ℝ` onto `[0, b]`. -/
def clamp (b r : ℝ) : ℝ := max 0 (min r b)

theorem clamp_mem {b : ℝ} (hb : 0 ≤ b) (r : ℝ) : clamp b r ∈ Set.Icc 0 b := by
  constructor
  · exact le_max_left _ _
  · exact max_le hb (min_le_right _ _)

theorem clamp_eq_self {b r : ℝ} (hr : r ∈ Set.Icc 0 b) : clamp b r = r := by
  unfold clamp
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem continuous_clamp (b : ℝ) : Continuous (clamp b) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem continuous_comp_clamp {g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hg : ContinuousOn g (Set.Icc 0 b)) : Continuous fun r => g (clamp b r) :=
  hg.comp_continuous (continuous_clamp b) (clamp_mem hb)

theorem hasDerivWithinAt_integral_clamp {g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hg : ContinuousOn g (Set.Icc 0 b)) (s : ℝ) (hs : s ∈ Set.Icc 0 b) :
    HasDerivWithinAt (fun u => ∫ r in (0:ℝ)..u, g (clamp b r)) (g s) (Set.Icc 0 b) s := by
  have hc := continuous_comp_clamp hb hg
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).hasDerivWithinAt (s := Set.Icc 0 b)
  rwa [clamp_eq_self hs] at h

theorem integral_clamp {g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b) :
    (∫ r in (0:ℝ)..b, g (clamp b r)) = ∫ r in (0:ℝ)..b, g r := by
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le hb] at hr
  rw [clamp_eq_self hr]

/-- **Step 3 of `thm:subcritical` in the form it is used.**  A continuous `g` on
`[0, b]` and the differential inequality `g φ ≤ 3 φ'` there give
`φ(0) ≤ φ(b) e^{-(1/3)∫₀^b g}`. -/
theorem le_mul_exp_intervalIntegral {φ dφ g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hgc : ContinuousOn g (Set.Icc 0 b))
    (hφ : ∀ s ∈ Set.Icc 0 b, HasDerivWithinAt φ (dφ s) (Set.Icc 0 b) s)
    (hineq : ∀ s ∈ Set.Icc 0 b, g s * φ s ≤ 3 * dφ s) :
    φ 0 ≤ φ b * Real.exp (-((∫ s in (0:ℝ)..b, g s) / 3)) := by
  have h := le_mul_exp_of_deriv_ge (G := fun u => ∫ r in (0:ℝ)..u, g (clamp b r)) (g := g)
    hb (fun s hs => hasDerivWithinAt_integral_clamp hb hgc s hs) (by simp) hφ hineq
  rwa [integral_clamp hb] at h

end LatticeProb

end

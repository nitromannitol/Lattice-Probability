/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepMV at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Complex.HarmonicComp
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mean value property against radial test functions

For `g` harmonic on an open set containing `B̄(u, δ)` and `ψ` continuous, rotation invariant and
vanishing off `B̄(0, δ)`: `∫ g(u + x) ψ(x) dx = g(u) ∫ ψ`. This identifies the pairing of the
harmonic part `𝔥` with a radial bump at `u` with `𝔥(u)` (used to express `𝔐_z` of GM l. 979,
`literature/src/1905.00383/uniqueness-final.tex`, through countably many pairings). Standard
(e.g. Evans, *PDE*, §2.2.2, Thm 2, mean value over balls); proof: rotate (`rotation` preserves
Lebesgue measure), average over the rotation angle (Fubini), and use the circle mean value
property `InnerProductSpace.HarmonicOnNhd.circleAverage_eq` (mathlib) for `w ↦ g(u + w x)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology InnerProductSpace
open scoped Real

namespace LQGMetric.GM

/-- **Mean value property against a radial `ψ`**. -/
theorem integral_mul_radial_of_harmonic {g : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V)
    (hg : HarmonicOnNhd g V) {u : ℂ} {δ : ℝ} (hBV : closedBall u δ ⊆ V) {ψ : ℂ → ℝ}
    (hψc : Continuous ψ) (hψs : ∀ y, δ < ‖y‖ → ψ y = 0)
    (hrad : ∀ (a : Circle) (y : ℂ), ψ (a * y) = ψ y) :
    ∫ x, g (u + x) * ψ x = g u * ∫ x, ψ x := by
  set Ψ : ℝ → ℂ → ℝ := fun t x => g (u + Complex.exp (t * Complex.I) * x) * ψ x with hΨ
  have hmem : ∀ (t : ℝ) (x : ℂ), ‖x‖ ≤ δ → u + Complex.exp (t * Complex.I) * x ∈ V := by
    intro t x hx
    refine hBV ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hx
  -- continuity of `Ψ`
  have hgc : ∀ v ∈ V, ContinuousAt g v := fun v hv => (hg v hv).1.continuousAt
  have hcont : Continuous (Function.uncurry Ψ) := by
    refine continuous_iff_continuousAt.2 fun ⟨t, x⟩ => ?_
    by_cases hx : δ < ‖x‖
    · have hev : Function.uncurry Ψ =ᶠ[𝓝 (t, x)] fun _ => 0 := by
        have : {p : ℝ × ℂ | δ < ‖p.2‖} ∈ 𝓝 (t, x) :=
          (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds hx
        filter_upwards [this] with p hp
        simp [Function.uncurry, hΨ, hψs p.2 hp]
      exact (continuousAt_congr hev).2 continuousAt_const
    · push Not at hx
      have h1 : ContinuousAt (fun p : ℝ × ℂ => u + Complex.exp (p.1 * Complex.I) * p.2) (t, x) :=
        (continuous_const.add (((Complex.continuous_ofReal.comp continuous_fst).mul
          continuous_const).cexp.mul continuous_snd)).continuousAt
      have h2 : ContinuousAt (fun p : ℝ × ℂ => g (u + Complex.exp (p.1 * Complex.I) * p.2)) (t, x) :=
        ContinuousAt.comp (f := fun p : ℝ × ℂ => u + Complex.exp (p.1 * Complex.I) * p.2) (g := g)
          (hgc _ (hmem t x hx)) h1
      exact h2.mul (hψc.comp continuous_snd).continuousAt
  -- each rotated integral equals the original one
  have hrot : ∀ t : ℝ, ∫ x, Ψ t x = ∫ x, g (u + x) * ψ x := by
    intro t
    set a : Circle := Circle.exp t
    have hmp := (rotation a).measurePreserving
    have := hmp.integral_comp (rotation a).toHomeomorph.measurableEmbedding
      (fun y => g (u + y) * ψ y)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hΨ, rotation_apply]
    rw [← hrad a x]
    simp [a, Circle.coe_exp]
  -- the angular average at fixed `x`
  have hang : ∀ x : ℂ, ∫ t in (0 : ℝ)..2 * π, Ψ t x = 2 * π * (g u * ψ x) := by
    intro x
    by_cases hx : δ < ‖x‖
    · simp [hΨ, hψs x hx]
    · push Not at hx
      have hharm : HarmonicOnNhd (g ∘ fun w : ℂ => u + w * x)
          ((fun w : ℂ => u + w * x) ⁻¹' V) :=
        harmonicOnNhd_comp_holo hV (hV.preimage (by fun_prop)) hg (by fun_prop)
          (fun w hw => hw)
      have hball : closedBall (0 : ℂ) |1| ⊆ (fun w : ℂ => u + w * x) ⁻¹' V := by
        intro w hw
        rw [abs_one, mem_closedBall, dist_zero_right] at hw
        refine hBV ?_
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul]
        nlinarith [norm_nonneg x, norm_nonneg w]
      have hmv := (hharm.mono hball).circleAverage_eq
      simp only [Function.comp_apply, zero_mul, add_zero] at hmv
      rw [Real.circleAverage_def] at hmv
      have hint : ∫ t in (0 : ℝ)..2 * π, Ψ t x =
          (∫ t in (0 : ℝ)..2 * π, g (u + circleMap 0 1 t * x)) * ψ x := by
        rw [← intervalIntegral.integral_mul_const]
        congr 1; funext t
        simp only [hΨ, circleMap, Complex.ofReal_one, one_mul, zero_add]
      rw [hint]
      have h2 : ∫ t in (0 : ℝ)..2 * π, g (u + circleMap 0 1 t * x) = 2 * π * g u := by
        rw [← hmv, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
        rfl
      rw [h2]; ring
  -- Fubini
  have hInt : Integrable (Function.uncurry Ψ) ((volume.restrict (uIoc 0 (2 * π))).prod volume) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℂ)), Measure.prod_restrict,
      ← IntegrableOn]
    have hK : IsCompact (Icc (0 : ℝ) (2 * π) ×ˢ closedBall (0 : ℂ) δ) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have h1 : IntegrableOn (Function.uncurry Ψ) (Icc (0 : ℝ) (2 * π) ×ˢ closedBall (0 : ℂ) δ)
        (volume.prod volume) := hcont.continuousOn.integrableOn_compact hK
    refine h1.of_forall_sdiff_eq_zero ((measurableSet_uIoc).prod MeasurableSet.univ) ?_
    rintro ⟨t, x⟩ ⟨⟨ht, -⟩, hn⟩
    have : δ < ‖x‖ := by
      by_contra hle
      push Not at hle
      refine hn ⟨?_, by simpa [mem_closedBall, dist_zero_right] using hle⟩
      have : uIoc (0 : ℝ) (2 * π) ⊆ Icc 0 (2 * π) := uIoc_subset_uIcc.trans
        (by rw [uIcc_of_le (by positivity)])
      exact this ht
    simp [Function.uncurry, hΨ, hψs x this]
  have hswap := intervalIntegral_integral_swap hInt
  simp_rw [hrot, hang] at hswap
  rw [intervalIntegral.integral_const, integral_const_mul, integral_const_mul] at hswap
  simp only [sub_zero, smul_eq_mul] at hswap
  have hpi : (2 * π) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi hswap

end LQGMetric.GM

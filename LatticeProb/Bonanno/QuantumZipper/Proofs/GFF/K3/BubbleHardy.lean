/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.BubbleHardy at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# K3-BUB1: Hardy's inequality on an annulus

Blueprint: `blueprint/EXT_PP_BLUEPRINT.md` §B, node **BUB-1** (the gate lemma replacing C4, D8).

Main result `hardy_annulus`: for `f : ℂ → ℝ` of class `C¹` with compact support, a centre `p` and
`0 < r < R`, if every circle `{‖z - p‖ = s}` with `r < s < R` meets a zero of `f`, then
`∫_{r < ‖z-p‖ < R} f²/‖z-p‖² ≤ 4π² ∫_{r < ‖z-p‖ < R} ‖Df‖²`.

**Proof route** (own elementary argument, as prescribed by EXT_PP §B "Sketch": FTC +
Cauchy–Schwarz on circles + polar coordinates; recorded in `DEVIATIONS.md`):

* `interval_cauchy_schwarz_sq`: `(∫_a^b φ)² ≤ (b-a) ∫_a^b φ²` on an interval, via the
  nonnegativity of `∫ ((b-a)φ - ∫φ)²`.
* `interval_sq_le_of_zero_at_left`: one-dimensional Poincaré inequality on `[a,b]` when `g`
  vanishes at the left endpoint: `∫_a^b g² ≤ (b-a)² ∫_a^b (g')²` (FTC from the endpoint plus
  Cauchy–Schwarz).
* `circle_hardy_wirtinger`: if `ρ > 0` and `f` has a zero on the circle of radius `ρ` about `p`,
  then `∫_{-π}^{π} f(p + ρe^{iθ})² dθ ≤ 4π² ρ² ∫_{-π}^{π} ‖Df(p + ρe^{iθ})‖² dθ`.  The circle
  map `θ ↦ f (circleMap p ρ θ)` is `2π`-periodic and has a zero at `θ₀ = arg(z - p)` for the
  given zero `z`, so the Poincaré inequality on the period interval `[θ₀, θ₀ + 2π]` transfers
  back to `[-π, π]` by periodicity, using `|∂_θ f| ≤ ρ ‖Df‖`.
* `annulus_polar_integral`: polar coordinates around `p` on the annulus `r < ‖z - p‖ < R`
  (`Complex.integral_comp_polarCoord_symm` + Fubini), together with the integrability of the
  radial marginal `ρ ↦ ρ ∫_{-π}^{π} F (circleMap p ρ θ) dθ`, which is what the final
  monotonicity step needs.
* `hardy_annulus`: assemble. The polar form of the left side is
  `∫_r^R ρ^{-1} (∫_{-π}^{π} f(circleMap p ρ θ)² dθ) dρ`, that of the right side is
  `∫_r^R ρ (∫_{-π}^{π} ‖Df(circleMap p ρ θ)‖² dθ) dρ`, and the circle inequality is the
  pointwise (in `ρ ∈ (r,R)`) bound `ρ^{-1} ∫ f² ≤ 4π² ρ ∫ ‖Df‖²`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology

namespace QuantumZipper

namespace K3

/-! ## One-dimensional Poincaré inequalities -/

/-- **Cauchy–Schwarz on an interval.** Own elementary proof: `0 ≤ ∫_a^b ((b-a) φ - ∫_a^b φ)²`
expands to `(b-a) ((b-a) ∫_a^b φ² - (∫_a^b φ)²)`. -/
theorem interval_cauchy_schwarz_sq {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, φ t) ^ 2 ≤ (b - a) * ∫ t in a..b, φ t ^ 2 := by
  set T : ℝ := b - a with hT
  have hT0 : 0 ≤ T := by rw [hT]; exact sub_nonneg.mpr hab
  set m : ℝ := ∫ t in a..b, φ t with hm
  set S : ℝ := ∫ t in a..b, φ t ^ 2 with hS
  have e : ∀ t : ℝ, (T * φ t - m) ^ 2 = T ^ 2 * φ t ^ 2 - (2 * T * m) * φ t + m ^ 2 := by
    intro t; ring
  have h0 : 0 ≤ ∫ t in a..b, (T * φ t - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hi1 : IntervalIntegrable (fun t => φ t ^ 2) volume a b := (hφ.pow 2).intervalIntegrable a b
  have hi2 : IntervalIntegrable φ volume a b := hφ.intervalIntegrable a b
  simp_rw [e] at h0
  rw [intervalIntegral.integral_add ((hi1.const_mul _).sub (hi2.const_mul _))
      intervalIntegrable_const,
    intervalIntegral.integral_sub (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [smul_eq_mul] at h0
  have h1 : 0 ≤ T * (T * S - m ^ 2) := by nlinarith [hT]
  rcases eq_or_lt_of_le hT0 with h | h
  · have hba : b = a := by rw [hT] at h; linarith
    have hm0 : m = 0 := by rw [hm, hba]; simp
    rw [← h, hm0]
    simp
  · have h2 : 0 ≤ T * S - m ^ 2 := (mul_nonneg_iff_of_pos_left h).mp h1
    have h3 : m ^ 2 ≤ T * S := by linarith
    rw [hm, hS, hT] at h3
    exact h3

/-- **One-dimensional Poincaré inequality with a zero at the left endpoint.** Own elementary
proof: `g x = ∫_a^x g'` by FTC, then Cauchy–Schwarz gives `|g x| ≤ √(b-a) √(∫_a^b (g')²)`. -/
theorem interval_sq_le_of_zero_at_left {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Continuous g) (hg' : Continuous g')
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (ha : g a = 0) :
    ∫ x in a..b, g x ^ 2 ≤ (b - a) ^ 2 * ∫ x in a..b, g' x ^ 2 := by
  set I : ℝ := ∫ x in a..b, g' x ^ 2 with hI
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have hIint : IntervalIntegrable (fun x => g' x ^ 2) volume a b :=
    (hg'.pow 2).intervalIntegrable a b
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hbd : ∀ x ∈ Icc a b, g x ^ 2 ≤ (b - a) * I := by
    intro x hx
    have hFTC : ∫ t in a..x, g' t = g x := by
      have hder : ∀ t ∈ uIcc a x, HasDerivAt g (g' t) t := by
        intro t ht
        rw [uIcc_of_le hx.1] at ht
        exact hderiv t ⟨ht.1, ht.2.trans hx.2⟩
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hg'.intervalIntegrable a x)
      rwa [ha, sub_zero] at h
    have h1 : |g x| ≤ ∫ t in a..x, |g' t| := by
      calc |g x| = |∫ t in a..x, g' t| := by rw [hFTC]
        _ ≤ ∫ t in a..x, |g' t| := intervalIntegral.abs_integral_le_integral_abs hx.1
    have h2 : (∫ t in a..x, |g' t|) ^ 2 ≤ (x - a) * ∫ t in a..x, (g' t) ^ 2 := by
      have hcs := interval_cauchy_schwarz_sq (φ := fun t => |g' t|) hg'.abs hx.1
      simpa only [sq_abs] using hcs
    have h3 : ∫ t in a..x, (g' t) ^ 2 ≤ I := by
      rw [hI]
      exact intervalIntegral.integral_mono_interval (c := a) (d := b) le_rfl hx.1 hx.2
        (ae_of_all _ fun t => sq_nonneg _) hIint
    have h4 : |g x| ^ 2 ≤ (b - a) * I := by
      have h5 : |g x| ^ 2 ≤ (x - a) * (∫ t in a..x, (g' t) ^ 2) :=
        (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans h2
      have h6 : (x - a) * (∫ t in a..x, (g' t) ^ 2) ≤ (b - a) * I :=
        mul_le_mul (by linarith [hx.2]) h3
          (intervalIntegral.integral_nonneg hx.1 fun t _ => sq_nonneg _)
          (by linarith [hx.1])
      linarith
    calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (b - a) * Real.sqrt I) ^ 2 := by
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
          calc |g x| ≤ Real.sqrt ((b - a) * I) :=
                (Real.le_sqrt (abs_nonneg _) (mul_nonneg hba hI0)).mpr h4
            _ = Real.sqrt (b - a) * Real.sqrt I := Real.sqrt_mul hba I
      _ = (b - a) * I := by
          rw [mul_pow, Real.sq_sqrt hba, Real.sq_sqrt hI0]
  calc ∫ x in a..b, g x ^ 2
      ≤ ∫ x in a..b, (b - a) * I :=
        intervalIntegral.integral_mono_on hab ((hg.pow 2).intervalIntegrable a b)
          intervalIntegrable_const hbd
    _ = (b - a) ^ 2 * ∫ x in a..b, g' x ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul, ← hI]
        ring

/-! ## The circle inequality (Hardy–Wirtinger on a circle) -/

/-- **Hardy–Wirtinger on a circle.** If `f` has a zero on the circle of radius `ρ > 0` about `p`,
then `∫_{-π}^{π} f(p + ρe^{iθ})² dθ ≤ 4π² ρ² ∫_{-π}^{π} ‖Df(p + ρe^{iθ})‖² dθ`.

Own elementary proof: `θ ↦ f (circleMap p ρ θ)` is `2π`-periodic and has a zero at
`θ₀ = arg(z - p)`; apply `interval_sq_le_of_zero_at_left` on `[θ₀, θ₀ + 2π]` and transfer back to
`[-π, π]` by periodicity, using `|∂_θ f| ≤ ρ ‖Df‖`. -/
theorem circle_hardy_wirtinger {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hz : ∃ z, ‖z - p‖ = ρ ∧ f z = 0) :
    ∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2 ≤
      4 * π ^ 2 * ρ ^ 2 * ∫ θ in (-π)..π, ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 := by
  obtain ⟨z, hzρ, hfz⟩ := hz
  set Φ : ℝ → ℝ := fun θ => f (circleMap p ρ θ) with hΦ
  set Φ' : ℝ → ℝ := fun θ => fderiv ℝ f (circleMap p ρ θ) (circleMap 0 ρ θ * Complex.I) with hΦ'
  have hcφ : Continuous (circleMap p ρ) := continuous_circleMap p ρ
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hΦc : Continuous Φ := by rw [hΦ]; exact hf.continuous.comp hcφ
  have hΦ'c : Continuous Φ' := by
    rw [hΦ']
    exact (hdf.comp hcφ).clm_apply ((continuous_circleMap 0 ρ).mul_const Complex.I)
  have hderiv : ∀ θ ∈ Icc (Complex.arg (z - p)) (Complex.arg (z - p) + 2 * π),
      HasDerivAt Φ (Φ' θ) θ := by
    intro θ _
    have h := ((hf.differentiable one_ne_zero) (circleMap p ρ θ)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap p ρ θ)
    rw [hΦ, hΦ']
    exact h
  have hΦ0 : Φ (Complex.arg (z - p)) = 0 := by
    have h1 : circleMap p ρ (Complex.arg (z - p)) = z := by
      have h2 : (↑‖z - p‖ : ℂ) * Complex.exp (↑(Complex.arg (z - p)) * Complex.I) = z - p :=
        Complex.norm_mul_exp_arg_mul_I (z - p)
      rw [hzρ] at h2
      calc circleMap p ρ (Complex.arg (z - p))
          = p + (↑ρ : ℂ) * Complex.exp (↑(Complex.arg (z - p)) * Complex.I) := rfl
        _ = p + (z - p) := by rw [h2]
        _ = z := by ring
    rw [hΦ]
    simp only [h1, hfz]
  -- periodicity of the circle function and of its derivative along the circle
  have hper : Function.Periodic Φ (2 * π) := by
    rw [hΦ]; exact (periodic_circleMap p ρ).comp f
  have hper' : Function.Periodic Φ' (2 * π) := by
    intro θ
    show fderiv ℝ f (circleMap p ρ (θ + 2 * π)) (circleMap 0 ρ (θ + 2 * π) * Complex.I)
      = fderiv ℝ f (circleMap p ρ θ) (circleMap 0 ρ θ * Complex.I)
    rw [periodic_circleMap p ρ θ, periodic_circleMap 0 ρ θ]
  have hper2 : Function.Periodic (fun x : ℝ => Φ x ^ 2) (2 * π) := by
    intro θ
    show Φ (θ + 2 * π) ^ 2 = Φ θ ^ 2
    rw [hper θ]
  have hper3 : Function.Periodic (fun x : ℝ => Φ' x ^ 2) (2 * π) := by
    intro θ
    show Φ' (θ + 2 * π) ^ 2 = Φ' θ ^ 2
    rw [hper' θ]
  have e1 : ∫ x in Complex.arg (z - p)..(Complex.arg (z - p) + 2 * π), Φ x ^ 2
      = ∫ x in (-π)..π, Φ x ^ 2 := by
    have h := hper2.intervalIntegral_add_eq (Complex.arg (z - p)) (-π)
    rw [show -π + 2 * π = π by ring] at h
    exact h
  have e2 : ∫ x in Complex.arg (z - p)..(Complex.arg (z - p) + 2 * π), Φ' x ^ 2
      = ∫ x in (-π)..π, Φ' x ^ 2 := by
    have h := hper3.intervalIntegral_add_eq (Complex.arg (z - p)) (-π)
    rw [show -π + 2 * π = π by ring] at h
    exact h
  have hab : Complex.arg (z - p) ≤ Complex.arg (z - p) + 2 * π := by linarith [Real.pi_pos]
  have hmain := interval_sq_le_of_zero_at_left hab hΦc hΦ'c hderiv hΦ0
  rw [show Complex.arg (z - p) + 2 * π - Complex.arg (z - p) = 2 * π by ring] at hmain
  rw [e1, e2] at hmain
  have hpt : ∀ θ, Φ' θ ^ 2 ≤ ρ ^ 2 * ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 := by
    intro θ
    have h1 : ‖Φ' θ‖ ≤ ρ * ‖fderiv ℝ f (circleMap p ρ θ)‖ := by
      rw [hΦ']
      calc ‖fderiv ℝ f (circleMap p ρ θ) (circleMap 0 ρ θ * Complex.I)‖
          ≤ ‖fderiv ℝ f (circleMap p ρ θ)‖ * ‖circleMap 0 ρ θ * Complex.I‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ f (circleMap p ρ θ)‖ * ρ := by
            rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hρ]
        _ = ρ * ‖fderiv ℝ f (circleMap p ρ θ)‖ := mul_comm _ _
    calc Φ' θ ^ 2 = ‖Φ' θ‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (ρ * ‖fderiv ℝ f (circleMap p ρ θ)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ρ ^ 2 * ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 := by ring
  have hI1 : ∫ θ in (-π)..π, Φ' θ ^ 2 ≤
      ρ ^ 2 * ∫ θ in (-π)..π, ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 := by
    calc ∫ θ in (-π)..π, Φ' θ ^ 2
        ≤ ∫ θ in (-π)..π, ρ ^ 2 * ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 :=
          intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
            ((hΦ'c.pow 2).intervalIntegrable _ _)
            ((continuous_const.mul ((hdf.comp hcφ).norm.pow 2)).intervalIntegrable _ _)
            (fun θ _ => hpt θ)
      _ = ρ ^ 2 * ∫ θ in (-π)..π, ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul]
  calc ∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2
      = ∫ θ in (-π)..π, Φ θ ^ 2 := by rw [hΦ]
    _ ≤ (2 * π) ^ 2 * ∫ θ in (-π)..π, Φ' θ ^ 2 := hmain
    _ ≤ (2 * π) ^ 2 * (ρ ^ 2 * ∫ θ in (-π)..π, ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hI1 (by positivity)
    _ = 4 * π ^ 2 * ρ ^ 2 * ∫ θ in (-π)..π, ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 := by ring

/-! ## Polar coordinates on an annulus -/

/-- **Polar coordinates on an annulus.** For `F` measurable and bounded on `{r < ‖x - p‖}`, the
integral of `F` over the annulus `r < ‖x - p‖ < R` equals
`∫_r^R ρ (∫_{-π}^{π} F (circleMap p ρ θ) dθ) dρ`, and the radial marginal is interval
integrable (both come from the same Fubini computation, so they are proved together).

Own elementary proof: translate `p` to `0`, use `Complex.integral_comp_polarCoord_symm`, then
Fubini (`setIntegral_prod`) and `Integrable.integral_prod_left`. -/
theorem annulus_polar_integral {F : ℂ → ℝ} (hFm : Measurable F) (p : ℂ)
    {r R C : ℝ} (hr : 0 < r) (hrR : r < R) (hC : 0 ≤ C)
    (hFb : ∀ x, r < ‖x - p‖ → ‖F x‖ ≤ C) :
    (∫ x in {x : ℂ | r < ‖x - p‖ ∧ ‖x - p‖ < R}, F x
        = ∫ ρ in r..R, ρ * ∫ θ in (-π)..π, F (circleMap p ρ θ)) ∧
      IntervalIntegrable (fun ρ => ρ * ∫ θ in (-π)..π, F (circleMap p ρ θ)) volume r R := by
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hcont : Continuous fun x : ℂ => ‖x - p‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hA : MeasurableSet {x : ℂ | r < ‖x - p‖ ∧ ‖x - p‖ < R} :=
    (isOpen_lt continuous_const hcont).measurableSet.inter
      (isOpen_lt hcont continuous_const).measurableSet
  have hS : MeasurableSet (Set.Ioo r R ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hsymm : ∀ q : ℝ × ℝ, Complex.polarCoord.symm q + p = circleMap p q.1 q.2 := by
    intro q
    rw [polarCoord_symm_eq_circleMap]
    simp only [circleMap, zero_add]
    ring
  have hcm : ∀ (ρ θ : ℝ), Complex.polarCoord.symm (ρ, θ) + p = circleMap p ρ θ := fun ρ θ =>
    hsymm (ρ, θ)
  -- Fubini integrability on the `(ρ, θ)` rectangle
  have hHm : AEStronglyMeasurable (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p))
      volume := by
    have hg : AEMeasurable (fun q : ℝ × ℝ => Complex.polarCoord.symm q + p) volume := by
      have h1 : Continuous fun q : ℝ × ℝ => circleMap p q.1 q.2 := continuous_circleMap_uncurry p
      have h2 : (fun q : ℝ × ℝ => Complex.polarCoord.symm q + p)
          = fun q => circleMap p q.1 q.2 := funext hsymm
      rw [h2]
      exact h1.aemeasurable
    exact measurable_fst.aestronglyMeasurable.mul
      (hFm.comp_aemeasurable hg).aestronglyMeasurable
  have hint : IntegrableOn (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p))
      (Set.Ioo r R ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
    refine Measure.integrableOn_of_bounded (M := R * C) ?_ hHm ?_
    · rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · filter_upwards [self_mem_ae_restrict hS] with q hq
      have hq0 : 0 < q.1 := hr.trans hq.1.1
      have hqn : ‖Complex.polarCoord.symm q + p - p‖ = q.1 := by
        rw [add_sub_cancel_right, Complex.norm_polarCoord_symm, abs_of_pos hq0]
      calc ‖q.1 * F (Complex.polarCoord.symm q + p)‖
          = |q.1| * ‖F (Complex.polarCoord.symm q + p)‖ := norm_mul _ _
        _ ≤ R * C := mul_le_mul (by rw [abs_of_pos hq0]; exact hq.1.2.le)
            (hFb _ (by rw [hqn]; exact hq.1.1)) (norm_nonneg _) (le_of_lt (hr.trans hrR))
  -- the radial marginal is integrable
  have hmarg : IntegrableOn (fun ρ => ρ * ∫ θ in (-π)..π, F (circleMap p ρ θ))
      (Set.Ioc r R) volume := by
    have h1 : IntegrableOn (fun ρ => ∫ θ in Set.Ioo (-π) π,
        (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p)) (ρ, θ))
        (Set.Ioo r R) volume := by
      have h1' := hint
      rw [IntegrableOn, ← Measure.prod_restrict] at h1'
      exact h1'.integral_prod_left
    have h3 : (fun ρ => ∫ θ in Set.Ioo (-π) π,
          (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p)) (ρ, θ))
        =ᵐ[volume.restrict (Set.Ioo r R)]
        (fun ρ => ρ * ∫ θ in (-π)..π, F (circleMap p ρ θ)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with ρ _
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi,
        intervalIntegral.integral_const_mul]
      simp only [hcm]
    exact (h1.congr_fun_ae h3).congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := r) (b := R)).symm
  refine ⟨?_, ?_⟩
  · -- the polar formula
    rw [← integral_indicator hA, ← integral_add_right_eq_self _ p,
      ← Complex.integral_comp_polarCoord_symm]
    trans ∫ q in Complex.polarCoord.target,
        (Set.Ioo r R ×ˢ Set.Ioo (-π) π).indicator
          (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p)) q
    · refine setIntegral_congr_fun ?_ ?_
      · exact (measurableSet_Ioi.prod measurableSet_Ioo :
          MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π))
      · intro q hq
        have hq1 : 0 < q.1 := hq.1
        have hq2 : q.2 ∈ Set.Ioo (-π) π := hq.2
        have hqn : ‖Complex.polarCoord.symm q + p - p‖ = q.1 := by
          rw [add_sub_cancel_right, Complex.norm_polarCoord_symm, abs_of_pos hq1]
        show q.1 • ({x : ℂ | r < ‖x - p‖ ∧ ‖x - p‖ < R}).indicator F
              (Complex.polarCoord.symm q + p)
            = (Set.Ioo r R ×ˢ Set.Ioo (-π) π).indicator
                (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p)) q
        by_cases hmem : r < q.1 ∧ q.1 < R
        · have hmemA : Complex.polarCoord.symm q + p ∈ {x : ℂ | r < ‖x - p‖ ∧ ‖x - p‖ < R} := by
            show r < ‖Complex.polarCoord.symm q + p - p‖ ∧
              ‖Complex.polarCoord.symm q + p - p‖ < R
            rw [hqn]
            exact hmem
          have hmemS : q ∈ Set.Ioo r R ×ˢ Set.Ioo (-π) π := ⟨hmem, hq2⟩
          rw [Set.indicator_of_mem hmemA, Set.indicator_of_mem hmemS]
          exact smul_eq_mul q.1 (F (Complex.polarCoord.symm q + p))
        · rw [Set.indicator_of_notMem (fun h =>
              hmem ⟨by rw [← hqn]; exact h.1, by rw [← hqn]; exact h.2⟩),
            Set.indicator_of_notMem (fun h => hmem h.1), smul_zero]
    · show ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
          (Set.Ioo r R ×ˢ Set.Ioo (-π) π).indicator
            (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p)) q
        = ∫ ρ in r..R, ρ * ∫ θ in (-π)..π, F (circleMap p ρ θ)
      rw [setIntegral_indicator hS]
      have hset : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π) ∩ (Set.Ioo r R ×ˢ Set.Ioo (-π) π)
          = Set.Ioo r R ×ˢ Set.Ioo (-π) π := by
        ext ⟨a, b⟩
        show (0 < a ∧ (-π < b ∧ b < π)) ∧ (r < a ∧ a < R) ∧ (-π < b ∧ b < π) ↔
          (r < a ∧ a < R) ∧ (-π < b ∧ b < π)
        exact ⟨fun h => ⟨h.2.1, h.1.2⟩, fun h => ⟨⟨hr.trans h.1.1, h.2⟩, h.1, h.2⟩⟩
      rw [hset, Measure.volume_eq_prod, setIntegral_prod _ hint]
      rw [intervalIntegral.integral_of_le hrR.le, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro ρ _
      show ∫ (y : ℝ) in Set.Ioo (-π) π,
          (fun q : ℝ × ℝ => q.1 * F (Complex.polarCoord.symm q + p)) (ρ, y)
        = ρ * ∫ (θ : ℝ) in (-π)..π, F (circleMap p ρ θ)
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi]
      simp only [hcm, intervalIntegral.integral_const_mul]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hrR.le).mpr hmarg

/-! ## Hardy's inequality on an annulus -/

/-- **BUB-1, Hardy's inequality on an annulus** (EXT_PP §B). If `f : ℂ → ℝ` is `C¹` with compact
support and every circle `{‖z - p‖ = s}`, `r < s < R`, contains a zero of `f`, then
`∫_{r < ‖z-p‖ < R} f²/‖z-p‖² ≤ 4π² ∫_{r < ‖z-p‖ < R} ‖Df‖²`. -/
theorem hardy_annulus {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (p : ℂ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hZ : ∀ s ∈ Set.Ioo r R, ∃ z, ‖z - p‖ = s ∧ f z = 0) :
    ∫ x in {x | r < ‖x - p‖ ∧ ‖x - p‖ < R}, f x ^ 2 / ‖x - p‖ ^ 2 ≤
      4 * Real.pi ^ 2 * ∫ x in {x | r < ‖x - p‖ ∧ ‖x - p‖ < R}, ‖fderiv ℝ f x‖ ^ 2 := by
  set F1 : ℂ → ℝ := fun x => f x ^ 2 / ‖x - p‖ ^ 2 with hF1
  set F2 : ℂ → ℝ := fun x => ‖fderiv ℝ f x‖ ^ 2 with hF2
  change ∫ x in {x : ℂ | r < ‖x - p‖ ∧ ‖x - p‖ < R}, F1 x ≤
    4 * Real.pi ^ 2 * ∫ x in {x : ℂ | r < ‖x - p‖ ∧ ‖x - p‖ < R}, F2 x
  obtain ⟨C1, hC1⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨C2, hC2⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  have hcont : Continuous fun x : ℂ => ‖x - p‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hF1m : Measurable F1 := by
    rw [hF1]
    exact (hf.continuous.pow 2).measurable.div (hcont.pow 2).measurable
  have hF1b : ∀ x, r < ‖x - p‖ → ‖F1 x‖ ≤ C1 ^ 2 / r ^ 2 := by
    intro x hx
    have hx0 : 0 < ‖x - p‖ := hr.trans hx
    have hnum : ‖f x‖ ^ 2 ≤ C1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC1 x) 2
    have hden : r ^ 2 ≤ ‖x - p‖ ^ 2 := pow_le_pow_left₀ hr.le hx.le 2
    have hval : ‖F1 x‖ = ‖f x‖ ^ 2 / ‖x - p‖ ^ 2 := by
      rw [hF1]
      simp only [norm_div, norm_pow]
      rw [Real.norm_of_nonneg (norm_nonneg (x - p))]
    have hinv : 1 / ‖x - p‖ ^ 2 ≤ 1 / r ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hr 2) hden
    rw [hval]
    calc ‖f x‖ ^ 2 / ‖x - p‖ ^ 2 = ‖f x‖ ^ 2 * (1 / ‖x - p‖ ^ 2) := by ring
      _ ≤ C1 ^ 2 * (1 / r ^ 2) :=
          mul_le_mul hnum hinv (by positivity) (sq_nonneg _)
      _ = C1 ^ 2 / r ^ 2 := by ring
  have hF2m : Measurable F2 := by
    rw [hF2]
    exact ((hf.continuous_fderiv one_ne_zero).norm.pow 2).measurable
  have hF2b : ∀ x, r < ‖x - p‖ → ‖F2 x‖ ≤ C2 ^ 2 := by
    intro x _
    have hval : ‖F2 x‖ = ‖fderiv ℝ f x‖ ^ 2 := by
      rw [hF2]
      simp only [norm_pow]
      rw [Real.norm_of_nonneg (norm_nonneg (fderiv ℝ f x))]
    rw [hval]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC2 x) 2
  obtain ⟨hL, hLi⟩ :=
    annulus_polar_integral hF1m p hr hrR (div_nonneg (sq_nonneg _) (by positivity)) hF1b
  obtain ⟨hR, hRi⟩ := annulus_polar_integral hF2m p hr hrR (sq_nonneg _) hF2b
  rw [hL, hR]
  have hpt : ∀ ρ ∈ Set.Ioo r R, ρ * ∫ θ in (-π)..π, F1 (circleMap p ρ θ)
      ≤ 4 * π ^ 2 * (ρ * ∫ θ in (-π)..π, F2 (circleMap p ρ θ)) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hr.trans hρ.1
    have hne : ρ ≠ 0 := hρ0.ne'
    have hne2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have e1 : ∫ θ in (-π)..π, F1 (circleMap p ρ θ)
        = (∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2) / ρ ^ 2 := by
      rw [hF1]
      have hc : ∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2 / ‖circleMap p ρ θ - p‖ ^ 2
          = ∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2 / ρ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro θ _
        show f (circleMap p ρ θ) ^ 2 / ‖circleMap p ρ θ - p‖ ^ 2
          = f (circleMap p ρ θ) ^ 2 / ρ ^ 2
        rw [norm_circleMap_sub_center, abs_of_pos hρ0]
      rw [hc, intervalIntegral.integral_div]
    have e2 : ∫ θ in (-π)..π, F2 (circleMap p ρ θ)
        = ∫ θ in (-π)..π, ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2 := by
      rw [hF2]
    have hcs := circle_hardy_wirtinger hf hρ0 (hZ ρ hρ)
    rw [e1, e2]
    have h1 : ρ * ((∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2) / ρ ^ 2)
        = (∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2) / ρ := by
      field_simp
    rw [h1]
    have h3 : (∫ θ in (-π)..π, f (circleMap p ρ θ) ^ 2) / ρ
        ≤ (4 * π ^ 2 * ρ ^ 2
            * ∫ θ in (-π)..π, ‖fderiv ℝ f (circleMap p ρ θ)‖ ^ 2) / ρ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hcs (inv_nonneg.mpr hρ0.le)
    refine h3.trans_eq ?_
    field_simp
  have hgi : IntervalIntegrable
      (fun ρ => 4 * π ^ 2 * (ρ * ∫ θ in (-π)..π, F2 (circleMap p ρ θ))) volume r R := by
    apply IntervalIntegrable.const_mul
    exact hRi
  calc ∫ ρ in r..R, ρ * ∫ θ in (-π)..π, F1 (circleMap p ρ θ)
      ≤ ∫ ρ in r..R, 4 * π ^ 2 * (ρ * ∫ θ in (-π)..π, F2 (circleMap p ρ θ)) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hrR.le hLi hgi hpt
    _ = 4 * π ^ 2 * ∫ ρ in r..R, ρ * ∫ θ in (-π)..π, F2 (circleMap p ρ θ) := by
        rw [intervalIntegral.integral_const_mul]

end K3

end QuantumZipper

/- Adapted from nitromannitol/Parking-Sharpness, Apache-2.0. -/
/-
Second-moment bounds for a continuum field whose covariance is the double time
integral of a Brownian heat kernel with generator `(2d)⁻¹Δ`. The kernel is an
arbitrary function satisfying the explicit heat-kernel formula. Space increments
have exponent `1/2`; time increments have exponent `1-d/4`, hence at least `1/4`
when `d ≤ 3`. The joint estimate combines these bounds. No Gaussianity is required.
-/
import LatticeProb.HeatKernelHolder

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.ZHolder


variable {d : ℕ} (K : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (hK : ∀ u x y, K u x y =
      (4 * Real.pi * u / (2 * d)) ^ (-(d : ℝ) / 2) *
        Real.exp (-(d : ℝ) * (∑ i, (x i - y i) ^ 2) / (2 * u)))

include hK

theorem contHeatKernel_nonneg (u : ℝ) (hu : 0 ≤ u) (x y : Fin d → ℝ) :
    0 ≤ K u x y := by
  simp only [hK]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

theorem contHeatKernel_le_diag (u : ℝ) (hu : 0 ≤ u) (x y : Fin d → ℝ) :
    K u x y ≤ K u x x := by
  simp only [hK]
  have hxx0 : (∑ i, (x i - x i)^2 : ℝ) = 0 := by simp
  rw [hxx0]
  simp only [mul_zero, zero_div, Real.exp_zero, mul_one]
  conv_rhs => rw [← mul_one ((4 * Real.pi * u / (2 * d)) ^ (-(d:ℝ)/2))]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  simp only [neg_mul, Left.neg_nonpos_iff]
  positivity

/-- Pointwise bracket bound (space direction), `α ∈ [0,1]`. -/
theorem contHeatKernel_diag_sub_le (u : ℝ) (hu : 0 < u) (x x' : Fin d → ℝ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    K u x x - K u x x'
      ≤ K u x x
          * ((d:ℝ) * (∑ i, (x i - x' i)^2) / (2*u)) ^ α := by
  simp only [hK]
  have hxx0 : (∑ i, (x i - x i)^2 : ℝ) = 0 := by simp
  rw [hxx0]
  simp only [mul_zero, zero_div, Real.exp_zero, mul_one]
  set K0 : ℝ := (4 * Real.pi * u / (2 * d)) ^ (-(d:ℝ)/2) with hK0def
  have hK0nonneg : 0 ≤ K0 := Real.rpow_nonneg (by positivity) _
  have hrw : K0 * Real.exp (-(d:ℝ) * (∑ i, (x i - x' i)^2) / (2*u))
      = K0 * Real.exp (-((d:ℝ) * (∑ i, (x i - x' i)^2) / (2*u))) := by
    congr 2; ring
  rw [hrw]
  have hc0 : (0:ℝ) ≤ (d:ℝ) * (∑ i, (x i - x' i)^2) / (2*u) := by positivity
  have hstep := LatticeProb.HeatKernelHolder.one_sub_exp_neg_le_rpow
    ((d:ℝ) * (∑ i, (x i - x' i)^2) / (2*u)) α hc0 hα0 hα1
  nlinarith [mul_le_mul_of_nonneg_left hstep hK0nonneg]

/-- **`contHeatKernel` at `x=y`, with the exponent written `u ^ (-((d:ℝ)/2))`** (the form
`LatticeProb.HeatKernelHolder`'s power-integral lemmas expect), separated into a
`d`-only constant times a pure power of `u`. -/
theorem contHeatKernel_diag_eq_rpow (u : ℝ) (hu : 0 < u) (x : Fin d → ℝ) :
    K u x x
      = (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * u ^ (-((d:ℝ)/2)) := by
  simp only [hK]
  have hxx0 : (∑ i, (x i - x i)^2 : ℝ) = 0 := by simp
  rw [hxx0]
  simp only [mul_zero, zero_div, Real.exp_zero, mul_one]
  rw [show (4 * Real.pi * u / (2 * d) : ℝ) = (4 * Real.pi / (2 * d)) * u from by ring]
  rw [Real.mul_rpow (by positivity) hu.le]
  have hp : (-(d:ℝ)/2 : ℝ) = -((d:ℝ)/2) := by ring
  rw [hp]

/-- **The pointwise bracket bound, fully expanded as a pure power of `u = a+b`** (`α = 1/4`):
`K(u,x,x) - K(u,x,x') ≤ K0const·(dL/2)^{1/4}·u^{-(d/2+1/4)}`, `L := ∑ᵢ(xᵢ-x'ᵢ)²`. -/
theorem contHeatKernel_diag_sub_le' (u : ℝ) (hu : 0 < u) (x x' : Fin d → ℝ) :
    K u x x - K u x x'
      ≤ (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
          * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
          * u ^ (-((d:ℝ)/2 + (1:ℝ)/4)) := by
  have h1 := (contHeatKernel_diag_sub_le K hK) u hu x x' (1/4) (by norm_num) (by norm_num)
  have h2 := (contHeatKernel_diag_eq_rpow K hK) u hu x
  nth_rewrite 2 [h2] at h1
  set L : ℝ := ∑ i, (x i - x' i)^2 with hLdef
  have hL0 : (0:ℝ) ≤ L := by rw [hLdef]; positivity
  have hrw : ((d:ℝ) * L / (2*u)) ^ ((1:ℝ)/4) = ((d:ℝ)*L/2) ^ ((1:ℝ)/4) * u ^ (-(1:ℝ)/4) := by
    rw [show ((d:ℝ)*L/(2*u) : ℝ) = ((d:ℝ)*L/2) * u⁻¹ from by ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [Real.inv_rpow hu.le]
    rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) from by ring, Real.rpow_neg hu.le]
  rw [hrw] at h1
  have hcomb : (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * u ^ (-((d:ℝ)/2))
      * (((d:ℝ)*L/2) ^ ((1:ℝ)/4) * u ^ (-(1:ℝ)/4))
      = (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * ((d:ℝ)*L/2) ^ ((1:ℝ)/4)
        * u ^ (-((d:ℝ)/2 + (1:ℝ)/4)) := by
    have hexp : u ^ (-((d:ℝ)/2)) * u ^ (-(1:ℝ)/4) = u ^ (-((d:ℝ)/2 + (1:ℝ)/4)) := by
      rw [← Real.rpow_add hu]
      congr 1
      ring
    calc (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * u ^ (-((d:ℝ)/2))
          * (((d:ℝ)*L/2) ^ ((1:ℝ)/4) * u ^ (-(1:ℝ)/4))
        = (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * ((d:ℝ)*L/2) ^ ((1:ℝ)/4)
            * (u ^ (-((d:ℝ)/2)) * u ^ (-(1:ℝ)/4)) := by ring
      _ = (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * ((d:ℝ)*L/2) ^ ((1:ℝ)/4)
            * u ^ (-((d:ℝ)/2 + (1:ℝ)/4)) := by rw [hexp]
  rw [hcomb] at h1
  exact h1

open LatticeProb.HeatKernelHolder in
/-- **The diagonal inner-integral bound**: for `a > 0`,
`∫ b in (0,B], K(a+b,x,x) ≤ K0const · 2^{-d/2} · a^{-d/4} · (B^{1-d/4}/(1-d/4))`. -/
theorem innerIntegral_contHeatKernel_diag_le (hd3 : d ≤ 3)
    (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (x : Fin d → ℝ) :
    (∫ b in Set.Ioc (0:ℝ) B, K (a+b) x x)
      ≤ (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
          * ((2:ℝ) ^ (-((d:ℝ)/2)) * a ^ (-((d:ℝ)/2)/2)
              * (B ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))) := by
  have hd0 : (0:ℝ) ≤ (d:ℝ)/2 := by positivity
  have hd2 : (d:ℝ)/2 < 2 := by
    have : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  have heq : ∀ b : ℝ, 0 ≤ b → K (a+b) x x
      = (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * (a+b) ^ (-((d:ℝ)/2)) :=
    fun b hb => (contHeatKernel_diag_eq_rpow K hK) (a+b) (by linarith) x
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun b hb => heq b hb.1.le)]
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_Ioc_rpow_neg_add_le a B ((d:ℝ)/2) ha hB hd0 hd2)
    (Real.rpow_nonneg (by positivity) _)

/-- **`b ↦ contHeatKernel d (a+b) x y` is continuous on `[0,B]`, for `a > 0` fixed** (the
argument `a+b` is then bounded away from the kernel's singularity at `0`). -/
theorem continuousOn_contHeatKernel_add_fixed (a : ℝ) (ha : 0 < a) (x y : Fin d → ℝ) (B : ℝ) :
    ContinuousOn (fun b => K (a+b) x y) (Set.Icc 0 B) := by
  simp only [hK]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; simp; fun_prop
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
    apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const
      · fun_prop
      · intro b hb
        left
        have : (0:ℝ) < a + b := by have := hb.1; linarith
        positivity
    · apply Real.continuous_exp.comp_continuousOn
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro b hb
        have : (0:ℝ) < a + b := by have := hb.1; linarith
        positivity

theorem integrableOn_Ioc_contHeatKernel_add_fixed (a : ℝ) (ha : 0 < a) (x y : Fin d → ℝ)
    (B : ℝ) (_hB : 0 ≤ B) :
    IntegrableOn (fun b => K (a+b) x y) (Set.Ioc (0:ℝ) B) volume :=
  (((continuousOn_contHeatKernel_add_fixed K hK) a ha x y B).integrableOn_Icc).mono_set
    Set.Ioc_subset_Icc_self

theorem measurable_contHeatKernel_uncurry (x y : Fin d → ℝ) :
    Measurable (fun p : ℝ × ℝ => K (p.1+p.2) x y) := by
  simp only [hK]
  fun_prop

theorem stronglyMeasurable_innerIntegral_contHeatKernel (B : ℝ) (x y : Fin d → ℝ) :
    StronglyMeasurable (fun a : ℝ =>
      ∫ b in Set.Ioc (0:ℝ) B, K (a+b) x y) :=
  ((measurable_contHeatKernel_uncurry K hK) x y).stronglyMeasurable.integral_prod_right'

/-- **The inner integral of `contHeatKernel d (a+b) x y` over `b ∈ (0,B]`, as a function of
`a`, is integrable on `(lo,hi]` for any `0 ≤ lo ≤ hi`**, for ANY `y` with
`K(·,x,y) ≤ K(·,x,x)` pointwise (the diagonal case `y = x` and, via `contHeatKernel_le_diag`,
every off-diagonal case). -/
theorem integrableOn_innerIntegral_contHeatKernel (hd3 : d ≤ 3)
    (lo hi B : ℝ) (hlo : 0 ≤ lo) (_hlohi : lo ≤ hi) (hB : 0 ≤ B) (x y : Fin d → ℝ)
    (hle : ∀ u : ℝ, 0 < u → K u x y
      ≤ K u x x) :
    IntegrableOn (fun a => ∫ b in Set.Ioc (0:ℝ) B, K (a+b) x y)
      (Set.Ioc lo hi) volume := by
  set g : ℝ → ℝ := fun a => (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
      * ((2:ℝ) ^ (-((d:ℝ)/2)) * a ^ (-((d:ℝ)/2)/2) * (B ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2)))
    with hgdef
  have hgint : IntegrableOn g (Set.Ioc lo hi) volume := by
    have hd0 : (0:ℝ) ≤ (d:ℝ)/2 := by positivity
    have hd2 : (d:ℝ)/2 < 2 := by
      have : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
      linarith
    have hrm1 : (-1:ℝ) < -((d:ℝ)/2)/2 := by linarith
    have hbase : IntegrableOn (fun a : ℝ => a ^ (-((d:ℝ)/2)/2)) (Set.Ioc lo hi) volume :=
      (intervalIntegral.intervalIntegrable_rpow' hrm1).1
    have heqg : g = fun a => ((4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
        * ((2:ℝ) ^ (-((d:ℝ)/2)) * (B ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2)))) * a ^ (-((d:ℝ)/2)/2) := by
      funext a; rw [hgdef]; ring
    rw [heqg]
    exact hbase.const_mul _
  apply Integrable.mono' hgint ((stronglyMeasurable_innerIntegral_contHeatKernel K hK) B x y).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro a ha
  have ha0 : 0 < a := lt_of_le_of_lt hlo ha.1
  have h1 : (∫ b in Set.Ioc (0:ℝ) B, K (a+b) x y)
      ≤ ∫ b in Set.Ioc (0:ℝ) B, K (a+b) x x := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun b hb => (contHeatKernel_nonneg K hK) _ (by linarith [ha0, hb.1]) x y)
    · exact (integrableOn_Ioc_contHeatKernel_add_fixed K hK) a ha0 x x B hB
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun b hb => hle (a+b) (by linarith [ha0, hb.1]))
  have h2 := (innerIntegral_contHeatKernel_diag_le K hK) hd3 a B ha0 hB x
  have h3 : (0:ℝ) ≤ ∫ b in Set.Ioc (0:ℝ) B, K (a+b) x y := by
    apply integral_nonneg_of_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioc
      (fun b hb => (contHeatKernel_nonneg K hK) _ (by linarith [ha0, hb.1]) x y)
  rw [Real.norm_of_nonneg h3]
  calc (∫ b in Set.Ioc (0:ℝ) B, K (a+b) x y)
      ≤ ∫ b in Set.Ioc (0:ℝ) B, K (a+b) x x := h1
    _ ≤ g a := h2

open LatticeProb.HeatKernelHolder in
/-- **The inner-integral difference bound**: for `a > 0`,
`∫b K(a+b,x,x) - ∫b K(a+b,x,x') ≤ K0const·(dL/2)^{1/4}·2^{-γ}·a^{-γ/2}·(t^{1-γ/2}/(1-γ/2))`,
`γ := d/2+1/4`. -/
theorem innerIntegral_diag_sub_le (hd3 : d ≤ 3) (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t)
    (x x' : Fin d → ℝ) :
    (∫ b in Set.Ioc (0:ℝ) t, K (a+b) x x)
      - (∫ b in Set.Ioc (0:ℝ) t, K (a+b) x x')
      ≤ (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
          * ((2:ℝ) ^ (-((d:ℝ)/2 + (1:ℝ)/4)) * a ^ (-((d:ℝ)/2 + (1:ℝ)/4)/2)
              * (t ^ (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2) / (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2))) := by
  set γ : ℝ := (d:ℝ)/2 + 1/4 with hγdef
  set C : ℝ := (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
    with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  rw [← MeasureTheory.integral_sub
    ((integrableOn_Ioc_contHeatKernel_add_fixed K hK) a ha x x t ht)
    ((integrableOn_Ioc_contHeatKernel_add_fixed K hK) a ha x x' t ht)]
  have hdomint : IntegrableOn (fun b => C * (a+b) ^ (-γ)) (Set.Ioc (0:ℝ) t) volume := by
    apply Integrable.const_mul
    have hcont : ContinuousOn (fun b : ℝ => (a+b) ^ (-γ)) (Set.Icc 0 t) := by
      apply ContinuousOn.rpow_const (by fun_prop)
      intro b hb
      left
      have : (0:ℝ) < a + b := by have := hb.1; linarith
      positivity
    exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  calc (∫ b in Set.Ioc (0:ℝ) t, (K (a+b) x x
        - K (a+b) x x'))
      ≤ ∫ b in Set.Ioc (0:ℝ) t, C * (a+b) ^ (-γ) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun b hb => ?_)
          have hle := (contHeatKernel_le_diag K hK) (a+b) (by linarith [ha, hb.1]) x x'
          simpa using sub_nonneg.mpr hle
        · exact hdomint
        · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun b hb =>
            (contHeatKernel_diag_sub_le' K hK) (a+b) (by linarith [ha, hb.1]) x x')
    _ = C * ∫ b in Set.Ioc (0:ℝ) t, (a+b) ^ (-γ) := MeasureTheory.integral_const_mul _ _
    _ ≤ C * ((2:ℝ) ^ (-γ) * a ^ (-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2))) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        refine integral_Ioc_rpow_neg_add_le a t γ ha ht (by rw [hγdef]; positivity) ?_
        rw [hγdef]
        have hcast : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
        linarith

open LatticeProb.HeatKernelHolder in
/-- **The full space-direction Hölder bound on the double integral**:
`Fxx(t,t) - Fxx'(t,t) ≤ K0const·(dL/2)^{1/4}·2^{-γ}·(t^{1-γ/2}/(1-γ/2))²`, `γ := d/2+1/4`,
`L := ∑ᵢ(xᵢ-x'ᵢ)²`. -/
theorem doubleIntegral_diag_sub_le (hd3 : d ≤ 3) (t : ℝ) (ht : 0 ≤ t) (x x' : Fin d → ℝ) :
    (∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x)
      - (∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x')
      ≤ (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
          * ((2:ℝ) ^ (-((d:ℝ)/2 + (1:ℝ)/4))
              * (t ^ (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2) / (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2)) ^ 2) := by
  set γ : ℝ := (d:ℝ)/2 + 1/4 with hγdef
  set C : ℝ := (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
    with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hγ0 : (0:ℝ) ≤ γ := by rw [hγdef]; positivity
  have hγ2 : γ < 2 := by
    rw [hγdef]; have hcast : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  rw [← MeasureTheory.integral_sub
    ((integrableOn_innerIntegral_contHeatKernel K hK) hd3 0 t t (le_refl (0:ℝ)) ht ht x x
      (fun u hu => le_refl _))
    ((integrableOn_innerIntegral_contHeatKernel K hK) hd3 0 t t (le_refl (0:ℝ)) ht ht x x'
      (fun u hu => (contHeatKernel_le_diag K hK) u hu.le x x'))]
  have hdomint : IntegrableOn (fun a : ℝ => C * ((2:ℝ) ^ (-γ) * a ^ (-γ/2)
      * (t ^ (1 - γ/2) / (1 - γ/2)))) (Set.Ioc (0:ℝ) t) volume := by
    have hrm1 : (-1:ℝ) < -γ/2 := by linarith
    have hbase : IntegrableOn (fun a : ℝ => a ^ (-γ/2)) (Set.Ioc (0:ℝ) t) volume :=
      (intervalIntegral.intervalIntegrable_rpow' hrm1).1
    have heq : (fun a : ℝ => C * ((2:ℝ) ^ (-γ) * a ^ (-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2))))
        = fun a => (C * (2:ℝ) ^ (-γ) * (t ^ (1 - γ/2) / (1 - γ/2))) * a ^ (-γ/2) := by
      funext a; ring
    rw [heq]
    exact hbase.const_mul _
  calc (∫ a in Set.Ioc (0:ℝ) t, ((∫ b in Set.Ioc (0:ℝ) t,
          K (a+b) x x)
        - ∫ b in Set.Ioc (0:ℝ) t, K (a+b) x x'))
      ≤ ∫ a in Set.Ioc (0:ℝ) t, C * ((2:ℝ) ^ (-γ) * a ^ (-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2))) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun a ha => ?_)
          have hyxle : (∫ b in Set.Ioc (0:ℝ) t, K (a+b) x x')
              ≤ ∫ b in Set.Ioc (0:ℝ) t, K (a+b) x x := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact ae_restrict_of_forall_mem measurableSet_Ioc
                (fun b hb => (contHeatKernel_nonneg K hK) _ (by linarith [ha.1, hb.1]) x x')
            · exact (integrableOn_Ioc_contHeatKernel_add_fixed K hK) a ha.1 x x t ht
            · exact ae_restrict_of_forall_mem measurableSet_Ioc
                (fun b hb => (contHeatKernel_le_diag K hK) (a+b) (by linarith [ha.1, hb.1]) x x')
          simpa using sub_nonneg.mpr hyxle
        · exact hdomint
        · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun a ha => ?_)
          have := (innerIntegral_diag_sub_le K hK) hd3 a t ha.1 ht x x'
          rw [hγdef, hCdef]
          convert this using 1
    _ = C * ((2:ℝ) ^ (-γ) * (t ^ (1 - γ/2) / (1 - γ/2)) ^ 2) := by
        rw [show (fun a : ℝ => C * ((2:ℝ) ^ (-γ) * a ^ (-γ/2) * (t ^ (1 - γ/2) / (1 - γ/2))))
              = fun a : ℝ => (C * (2:ℝ) ^ (-γ) * (t ^ (1 - γ/2) / (1 - γ/2))) * a ^ (-γ/2) from by
            funext a; ring]
        rw [MeasureTheory.integral_const_mul, integral_Ioc_rpow_one_sub_half t γ ht hγ2]
        ring

theorem contHeatKernel_diag_translation_invariant (u : ℝ) (x x' : Fin d → ℝ) :
    K u x' x' = K u x x := by
  simp only [hK]
  have h1 : (∑ i, (x' i - x' i)^2 : ℝ) = 0 := by simp
  have h2 : (∑ i, (x i - x i)^2 : ℝ) = 0 := by simp
  rw [h1, h2]

/-- **The space-direction second-moment Hölder bound for `Z`.** -/
theorem space_second_moment_le {Ω' : Type} [MeasurableSpace Ω'] (Q' : Measure Ω')
    (v : ℝ) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hcov : ∀ r x s y, 0 ≤ r → 0 ≤ s →
        Integrable (fun ω' => Z ω' r x * Z ω' s y) Q' ∧
        ∫ ω', Z ω' r x * Z ω' s y ∂Q'
          = v * ∫ a in Set.Ioc (0:ℝ) r, ∫ b in Set.Ioc (0:ℝ) s,
              K (a+b) x y)
    (hv : 0 ≤ v) (hd3 : d ≤ 3) (t : ℝ) (ht : 0 ≤ t) (x x' : Fin d → ℝ) :
    ∫ ω', (Z ω' t x - Z ω' t x') ^ 2 ∂Q'
      ≤ 2 * v * ((4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
          * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
          * ((2:ℝ) ^ (-((d:ℝ)/2 + (1:ℝ)/4))
              * (t ^ (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2) / (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2)) ^ 2)) := by
  have hAA := (hcov t x t x ht ht).2
  have hAB := (hcov t x t x' ht ht).2
  have hBB := (hcov t x' t x' ht ht).2
  have hAAi := (hcov t x t x ht ht).1
  have hABi := (hcov t x t x' ht ht).1
  have hBBi := (hcov t x' t x' ht ht).1
  have hexpand : ∫ ω', (Z ω' t x - Z ω' t x') ^ 2 ∂Q'
      = (∫ ω', Z ω' t x * Z ω' t x ∂Q') - 2 * (∫ ω', Z ω' t x * Z ω' t x' ∂Q')
          + (∫ ω', Z ω' t x' * Z ω' t x' ∂Q') := by
    have hcongr : ∫ ω', (Z ω' t x - Z ω' t x') ^ 2 ∂Q'
        = ∫ ω', (Z ω' t x * Z ω' t x - 2 * (Z ω' t x * Z ω' t x')) + Z ω' t x' * Z ω' t x' ∂Q' := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω'; ring
    rw [hcongr]
    have hAB2 : Integrable (fun ω' => Z ω' t x * Z ω' t x - 2 * (Z ω' t x * Z ω' t x')) Q' :=
      hAAi.sub (hABi.const_mul 2)
    rw [MeasureTheory.integral_add hAB2 hBBi]
    have heq2 : ∫ ω', (Z ω' t x * Z ω' t x - 2 * (Z ω' t x * Z ω' t x')) ∂Q'
        = ∫ ω', Z ω' t x * Z ω' t x ∂Q' - 2 * ∫ ω', Z ω' t x * Z ω' t x' ∂Q' := by
      rw [MeasureTheory.integral_sub hAAi (hABi.const_mul 2), MeasureTheory.integral_const_mul]
    rw [heq2]
  rw [hexpand, hAA, hAB, hBB]
  have hxx' : (∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x' x')
      = ∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro a _
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro b _
    exact (contHeatKernel_diag_translation_invariant K hK) (a+b) x x'
  rw [hxx']
  have hgap := (doubleIntegral_diag_sub_le K hK) hd3 t ht x x'
  nlinarith [hgap]

/-- **The outer-integral split (time direction)**: for `0 ≤ t' ≤ t`,
`F(t,t) = F(t',t) + R'`, `F(r,s) := ∫∫_{(0,r]×(0,s]} K(a+b,x,x)`,
`R' := ∫∫_{(t',t]×(0,t]} K(a+b,x,x)`. -/
theorem doubleIntegral_diag_outer_split (hd3 : d ≤ 3) (t' t : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t)
    (x : Fin d → ℝ) :
    (∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t, K (a+b) x x)
      = (∫ a in Set.Ioc (0:ℝ) t', ∫ b in Set.Ioc (0:ℝ) t,
          K (a+b) x x)
        + (∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) t,
          K (a+b) x x) := by
  have ht : (0:ℝ) ≤ t := ht'.trans htt'
  have hunion : Set.Ioc (0:ℝ) t' ∪ Set.Ioc t' t = Set.Ioc (0:ℝ) t := Set.Ioc_union_Ioc_eq_Ioc ht' htt'
  have hdisj : Disjoint (Set.Ioc (0:ℝ) t') (Set.Ioc t' t) := Set.Ioc_disjoint_Ioc_of_le (le_refl t')
  have hi1 : IntegrableOn (fun a => ∫ b in Set.Ioc (0:ℝ) t,
      K (a+b) x x) (Set.Ioc (0:ℝ) t') volume :=
    (integrableOn_innerIntegral_contHeatKernel K hK) hd3 0 t' t (le_refl 0) ht' ht x x (fun u _ => le_refl _)
  have hi2 : IntegrableOn (fun a => ∫ b in Set.Ioc (0:ℝ) t,
      K (a+b) x x) (Set.Ioc t' t) volume :=
    (integrableOn_innerIntegral_contHeatKernel K hK) hd3 t' t t ht' htt' ht x x (fun u _ => le_refl _)
  nth_rewrite 1 [← hunion]
  exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hi1 hi2

/-- **Monotonicity in the outer range (time direction)**: for `0 ≤ t' ≤ t`,
`F(t',t') ≤ F(t,t')`. -/
theorem doubleIntegral_diag_outer_mono (hd3 : d ≤ 3) (t' t : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t)
    (x : Fin d → ℝ) :
    (∫ a in Set.Ioc (0:ℝ) t', ∫ b in Set.Ioc (0:ℝ) t', K (a+b) x x)
      ≤ ∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t',
          K (a+b) x x := by
  apply MeasureTheory.setIntegral_mono_set
    ((integrableOn_innerIntegral_contHeatKernel K hK) hd3 0 t t' (le_refl 0) (ht'.trans htt') ht' x x
      (fun u _ => le_refl _))
  · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun a ha => ?_)
    exact MeasureTheory.integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun b hb => (contHeatKernel_nonneg K hK) _ (by linarith [ha.1, hb.1]) x x))
  · filter_upwards with a ha
    exact Set.Ioc_subset_Ioc_right htt' ha

open LatticeProb.HeatKernelHolder in
/-- **The `R'` bound (time direction)**: for `0 ≤ t' ≤ t`,
`R' := ∫∫_{(t',t]×(0,t]} K(a+b,x,x) ≤ K0const·2^{-d/2}·((t-t')^{1-d/4}/(1-d/4))·(t^{1-d/4}/(1-d/4))`. -/
theorem doubleIntegral_diag_offset_le (hd3 : d ≤ 3) (t' t : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t)
    (x : Fin d → ℝ) :
    (∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) t, K (a+b) x x)
      ≤ (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
          * ((2:ℝ) ^ (-((d:ℝ)/2)) * ((t - t') ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))
              * (t ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))) := by
  have hd0 : (0:ℝ) ≤ (d:ℝ)/2 := by positivity
  have hd2 : (d:ℝ)/2 < 2 := by
    have hcast : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  have ht : (0:ℝ) ≤ t := ht'.trans htt'
  have heq : ∀ a b : ℝ, t' < a → 0 ≤ b → K (a+b) x x
      = (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * (a+b) ^ (-((d:ℝ)/2)) := fun a b ha hb =>
    (contHeatKernel_diag_eq_rpow K hK) (a+b) (by linarith) x
  have hcongr : (∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x)
      = ∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) t,
        (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * (a+b) ^ (-((d:ℝ)/2)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro a ha
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro b hb
    exact heq a b ha.1 hb.1.le
  rw [hcongr]
  have hpull : (∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) t,
        (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2)) * (a+b) ^ (-((d:ℝ)/2)))
      = (4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
          * ∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) t, (a+b) ^ (-((d:ℝ)/2)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro a _
    dsimp only
    rw [MeasureTheory.integral_const_mul]
  rw [hpull]
  exact mul_le_mul_of_nonneg_left
    (doubleIntegral_rpow_neg_add_le_offset t' t t ((d:ℝ)/2) ht' htt' ht hd0 hd2)
    (Real.rpow_nonneg (by positivity) _)

/-- **The time-direction second-moment Hölder bound for `Z`.** -/
theorem time_second_moment_le {Ω' : Type} [MeasurableSpace Ω'] (Q' : Measure Ω')
    (v : ℝ) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hcov : ∀ r x s y, 0 ≤ r → 0 ≤ s →
        Integrable (fun ω' => Z ω' r x * Z ω' s y) Q' ∧
        ∫ ω', Z ω' r x * Z ω' s y ∂Q'
          = v * ∫ a in Set.Ioc (0:ℝ) r, ∫ b in Set.Ioc (0:ℝ) s,
              K (a+b) x y)
    (hv : 0 ≤ v) (hd3 : d ≤ 3) (t' t : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t) (x : Fin d → ℝ) :
    ∫ ω', (Z ω' t x - Z ω' t' x) ^ 2 ∂Q'
      ≤ v * ((4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
          * ((2:ℝ) ^ (-((d:ℝ)/2)) * ((t - t') ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))
              * (t ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2)))) := by
  have hAA := (hcov t x t x (ht'.trans htt') (ht'.trans htt')).2
  have hAB := (hcov t x t' x (ht'.trans htt') ht').2
  have hBA := (hcov t' x t x ht' (ht'.trans htt')).2
  have hBB := (hcov t' x t' x ht' ht').2
  have hAAi := (hcov t x t x (ht'.trans htt') (ht'.trans htt')).1
  have hABi := (hcov t x t' x (ht'.trans htt') ht').1
  have hBAi := (hcov t' x t x ht' (ht'.trans htt')).1
  have hBBi := (hcov t' x t' x ht' ht').1
  have hcomm : (∫ ω', Z ω' t x * Z ω' t' x ∂Q') = ∫ ω', Z ω' t' x * Z ω' t x ∂Q' := by
    apply MeasureTheory.integral_congr_ae; filter_upwards with ω'; ring
  have hexpand : ∫ ω', (Z ω' t x - Z ω' t' x) ^ 2 ∂Q'
      = (∫ ω', Z ω' t x * Z ω' t x ∂Q') - 2 * (∫ ω', Z ω' t x * Z ω' t' x ∂Q')
          + (∫ ω', Z ω' t' x * Z ω' t' x ∂Q') := by
    have hcongr : ∫ ω', (Z ω' t x - Z ω' t' x) ^ 2 ∂Q'
        = ∫ ω', (Z ω' t x * Z ω' t x - 2 * (Z ω' t x * Z ω' t' x)) + Z ω' t' x * Z ω' t' x ∂Q' := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω'; ring
    rw [hcongr]
    have hAB2 : Integrable (fun ω' => Z ω' t x * Z ω' t x - 2 * (Z ω' t x * Z ω' t' x)) Q' :=
      hAAi.sub (hABi.const_mul 2)
    rw [MeasureTheory.integral_add hAB2 hBBi]
    have heq2 : ∫ ω', (Z ω' t x * Z ω' t x - 2 * (Z ω' t x * Z ω' t' x)) ∂Q'
        = ∫ ω', Z ω' t x * Z ω' t x ∂Q' - 2 * ∫ ω', Z ω' t x * Z ω' t' x ∂Q' := by
      rw [MeasureTheory.integral_sub hAAi (hABi.const_mul 2), MeasureTheory.integral_const_mul]
    rw [heq2]
  rw [hexpand, hAA, hAB, hBB]
  have hK1 := (doubleIntegral_diag_outer_split K hK) hd3 t' t ht' htt' x
  have hK2 := (doubleIntegral_diag_outer_mono K hK) hd3 t' t ht' htt' x
  have hK3 := (doubleIntegral_diag_offset_le K hK) hd3 t' t ht' htt' x
  -- Fact 1: v·F(t,t') = v·F(t',t), from EAB = EBA (hcomm) combined with hAB, hBA.
  have hfact1 : v * (∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t',
        K (a+b) x x)
      = v * ∫ a in Set.Ioc (0:ℝ) t', ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x := by
    rw [← hAB, ← hBA]; exact hcomm
  -- Fact 2: v·F(t,t) = v·F(t',t) + v·R', from hK1 multiplied by v.
  have hfact2 : v * (∫ a in Set.Ioc (0:ℝ) t, ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x)
      = v * (∫ a in Set.Ioc (0:ℝ) t', ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x)
        + v * (∫ a in Set.Ioc t' t, ∫ b in Set.Ioc (0:ℝ) t,
        K (a+b) x x) := by
    rw [← mul_add, ← hK1]
  -- Fact 3: v·F(t',t') ≤ v·F(t,t'), from hK2 (v ≥ 0).
  have hfact3 := mul_le_mul_of_nonneg_left hK2 hv
  -- Fact 4: v·R' ≤ v·[bound], from hK3 (v ≥ 0).
  have hfact4 := mul_le_mul_of_nonneg_left hK3 hv
  linarith [hfact1, hfact2, hfact3, hfact4]

/-- **The joint space-time second-moment bound for `Z`**, combining the spatial
power `1/2` and temporal power `1-d/4` via `(a+b)^2 ≤ 2a^2+2b^2`. -/
theorem joint_second_moment_le {Ω' : Type} [MeasurableSpace Ω'] (Q' : Measure Ω')
    (v : ℝ) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hcov : ∀ r x s y, 0 ≤ r → 0 ≤ s →
        Integrable (fun ω' => Z ω' r x * Z ω' s y) Q' ∧
        ∫ ω', Z ω' r x * Z ω' s y ∂Q'
          = v * ∫ a in Set.Ioc (0:ℝ) r, ∫ b in Set.Ioc (0:ℝ) s,
              K (a+b) x y)
    (hv : 0 ≤ v) (hd3 : d ≤ 3) (t' t : ℝ) (ht' : 0 ≤ t') (htt' : t' ≤ t) (x x' : Fin d → ℝ) :
    ∫ ω', (Z ω' t x - Z ω' t' x') ^ 2 ∂Q'
      ≤ 2 * (2 * v * ((4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
            * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
            * ((2:ℝ) ^ (-((d:ℝ)/2 + (1:ℝ)/4))
                * (t ^ (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2) / (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2)) ^ 2)))
        + 2 * (v * ((4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
            * ((2:ℝ) ^ (-((d:ℝ)/2)) * ((t - t') ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))
                * (t ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))))) := by
  have ht : (0:ℝ) ≤ t := ht'.trans htt'
  have hspace := (space_second_moment_le K hK) Q' v Z hcov hv hd3 t ht x x'
  have htime := (time_second_moment_le K hK) Q' v Z hcov hv hd3 t' t ht' htt' x'
  have hAAi := (hcov t x t x ht ht).1
  have hAA'i := (hcov t x' t x' ht ht).1
  have hA'A'ttp := (hcov t x' t' x' ht ht').1
  have hBBi := (hcov t' x' t' x' ht' ht').1
  have hABi := (hcov t x t x' ht ht).1
  have hSpaceInt : Integrable (fun ω' => (Z ω' t x - Z ω' t x') ^ 2) Q' := by
    have hcongr : (fun ω' => (Z ω' t x - Z ω' t x') ^ 2)
        = fun ω' => (Z ω' t x * Z ω' t x - 2 * (Z ω' t x * Z ω' t x')) + Z ω' t x' * Z ω' t x' := by
      funext ω'; ring
    rw [hcongr]
    exact (hAAi.sub (hABi.const_mul 2)).add hAA'i
  have hTimeInt : Integrable (fun ω' => (Z ω' t x' - Z ω' t' x') ^ 2) Q' := by
    have hcongr : (fun ω' => (Z ω' t x' - Z ω' t' x') ^ 2)
        = fun ω' => (Z ω' t x' * Z ω' t x' - 2 * (Z ω' t x' * Z ω' t' x')) + Z ω' t' x' * Z ω' t' x' := by
      funext ω'; ring
    rw [hcongr]
    exact (hAA'i.sub (hA'A'ttp.const_mul 2)).add hBBi
  have hsq : ∫ ω', (Z ω' t x - Z ω' t' x') ^ 2 ∂Q'
      ≤ 2 * (∫ ω', (Z ω' t x - Z ω' t x') ^ 2 ∂Q') + 2 * (∫ ω', (Z ω' t x' - Z ω' t' x') ^ 2 ∂Q') := by
    have hcongr : ∫ ω', (Z ω' t x - Z ω' t' x') ^ 2 ∂Q'
        ≤ ∫ ω', (2 * (Z ω' t x - Z ω' t x')^2 + 2 * (Z ω' t x' - Z ω' t' x')^2) ∂Q' := by
      apply MeasureTheory.integral_mono_of_nonneg
      · filter_upwards with ω'; positivity
      · exact (hSpaceInt.const_mul 2).add (hTimeInt.const_mul 2)
      · filter_upwards with ω'
        nlinarith [sq_nonneg (Z ω' t x - Z ω' t x' - (Z ω' t x' - Z ω' t' x'))]
    rwa [MeasureTheory.integral_add (hSpaceInt.const_mul 2) (hTimeInt.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hcongr
  calc ∫ ω', (Z ω' t x - Z ω' t' x') ^ 2 ∂Q'
      ≤ 2 * (∫ ω', (Z ω' t x - Z ω' t x') ^ 2 ∂Q') + 2 * (∫ ω', (Z ω' t x' - Z ω' t' x') ^ 2 ∂Q') := hsq
    _ ≤ 2 * (2 * v * ((4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
            * ((d:ℝ) * (∑ i, (x i - x' i)^2) / 2) ^ ((1:ℝ)/4)
            * ((2:ℝ) ^ (-((d:ℝ)/2 + (1:ℝ)/4))
                * (t ^ (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2) / (1 - ((d:ℝ)/2 + (1:ℝ)/4)/2)) ^ 2)))
        + 2 * (v * ((4 * Real.pi / (2 * d)) ^ (-((d:ℝ)/2))
            * ((2:ℝ) ^ (-((d:ℝ)/2)) * ((t - t') ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))
                * (t ^ (1 - (d:ℝ)/2/2) / (1 - (d:ℝ)/2/2))))) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hspace (by norm_num))
          (mul_le_mul_of_nonneg_left htime (by norm_num))

end LatticeProb.ZHolder

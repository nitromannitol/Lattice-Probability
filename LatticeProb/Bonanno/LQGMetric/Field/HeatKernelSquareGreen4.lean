/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareGreen4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen3
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
For `f ∈ C¹_c(ℂ)` and the square mode `φ_{jk}(z) = sin(πj(x−a)/L) sin(πk(y−a)/L)`:

  `∫ ⟪∇φ_{jk}, ∇f⟫ = λ_{jk} ∫ φ_{jk} f`,  `λ_{jk} = π²(j²+k²)/L² = 2·sqRate L (j,k)`
  (`HeatSq.integral_gradInner_sqMode`),

i.e. `−Δφ_{jk} = λ_{jk} φ_{jk}` in the weak sense. Proof: one integration by parts in each
coordinate direction (mathlib `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`,
as in QZ `K3.integral_mul_fderiv_fderiv_eq_neg`), using `sin'' = −sin`.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology QuantumZipper.K3

namespace LQGMetric
namespace HeatSq

/-- derivative of a separated product `g(Re z) h(Im z)` -/
lemma hasFDerivAt_sep {g h g' h' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hh : ∀ x, HasDerivAt h (h' x) x) (z : ℂ) :
    HasFDerivAt (fun w : ℂ => g w.re * h w.im)
      ((h z.im * g' z.re) • Complex.reCLM + (g z.re * h' z.im) • Complex.imCLM) z := by
  have h1 := (hg z.re).comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
  have h2 := (hh z.im).comp_hasFDerivAt z Complex.imCLM.hasFDerivAt
  refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun (v : ℂ) => ?_)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  ring

lemma sep_apply_one {g h g' h' : ℝ → ℝ} (z : ℂ) :
    ((h z.im * g' z.re) • Complex.reCLM + (g z.re * h' z.im) • Complex.imCLM :
      ℂ →L[ℝ] ℝ) 1 = h z.im * g' z.re := by
  simp

lemma sep_apply_I {g h g' h' : ℝ → ℝ} (z : ℂ) :
    ((h z.im * g' z.re) • Complex.reCLM + (g z.re * h' z.im) • Complex.imCLM :
      ℂ →L[ℝ] ℝ) Complex.I = g z.re * h' z.im := by
  simp

/-- one integration by parts along `v` against a `C¹_c` function -/
lemma integral_mul_fderiv_eq_neg {F F' f : ℂ → ℝ} (hF : Continuous F) (hF' : Continuous F')
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : ℂ)
    (hd : ∀ z, HasLineDerivAt ℝ F (F' z) z v) :
    ∫ z, F z * fderiv ℝ f z v = -∫ z, F' z * f z := by
  have hfv : Continuous fun z => fderiv ℝ f z v :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfvc : HasCompactSupport fun z => fderiv ℝ f z v := hc.fderiv_apply (𝕜 := ℝ) v
  have h : ∫ x, ContinuousLinearMap.mul ℝ ℝ (F x) (fderiv ℝ f x v) =
      -∫ x, ContinuousLinearMap.mul ℝ ℝ (F' x) (f x) := by
    have i1 : Integrable (fun x => F' x * f x) :=
      (hF'.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
    have i2 : Integrable (fun x => F x * fderiv ℝ f x v) :=
      (hF.mul hfv).integrable_of_hasCompactSupport hfvc.mul_left
    have i3 : Integrable (fun x => F x * f x) :=
      (hF.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
    apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    · simpa only [ContinuousLinearMap.mul_apply'] using i1
    · simpa only [ContinuousLinearMap.mul_apply'] using i2
    · simpa only [ContinuousLinearMap.mul_apply'] using i3
    · exact fun x _ => hd x
    · exact fun x _ => ((hf.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v
  simpa only [ContinuousLinearMap.mul_apply'] using h

lemma hasDerivAt_sinShift (c a x : ℝ) :
    HasDerivAt (fun u => Real.sin (c * (u - a))) (c * Real.cos (c * (x - a))) x := by
  have := ((hasDerivAt_id x).sub_const a).const_mul c
  convert (Real.hasDerivAt_sin _).comp x this using 1 <;> first | rfl | (simp only [id]; ring_nf)

lemma hasDerivAt_cosShift (c a x : ℝ) :
    HasDerivAt (fun u => c * Real.cos (c * (u - a))) (-(c ^ 2) * Real.sin (c * (x - a))) x := by
  have := ((hasDerivAt_id x).sub_const a).const_mul c
  convert ((Real.hasDerivAt_cos _).comp x this).const_mul c using 1 <;> first | rfl | (simp only [id]; ring_nf)

lemma sinMode_eq (a L : ℝ) (k : ℕ) (u : ℝ) :
    sinMode a L k u = Real.sin (π * k / L * (u - a)) := by
  unfold sinMode; congr 1; ring

/-- **Weak eigenfunction equation** `∫ ⟪∇φ_{jk}, ∇f⟫ = λ_{jk} ∫ φ_{jk} f`. -/
theorem integral_gradInner_sqMode {a L : ℝ} (p : ℕ × ℕ) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∫ z, gradInner (sqMode a L p) f z = 2 * sqRate L p * ∫ z, sqMode a L p z * f z := by
  set c₁ : ℝ := π * p.1 / L
  set c₂ : ℝ := π * p.2 / L
  set g : ℝ → ℝ := fun u => Real.sin (c₁ * (u - a))
  set h : ℝ → ℝ := fun u => Real.sin (c₂ * (u - a))
  set g' : ℝ → ℝ := fun u => c₁ * Real.cos (c₁ * (u - a))
  set h' : ℝ → ℝ := fun u => c₂ * Real.cos (c₂ * (u - a))
  have hg : ∀ x, HasDerivAt g (g' x) x := fun x => hasDerivAt_sinShift c₁ a x
  have hh : ∀ x, HasDerivAt h (h' x) x := fun x => hasDerivAt_sinShift c₂ a x
  have hg' : ∀ x, HasDerivAt g' (-(c₁ ^ 2) * g x) x := fun x => hasDerivAt_cosShift c₁ a x
  have hh' : ∀ x, HasDerivAt h' (-(c₂ ^ 2) * h x) x := fun x => hasDerivAt_cosShift c₂ a x
  have hmode : sqMode a L p = fun w : ℂ => g w.re * h w.im := by
    funext w
    show sinMode a L p.1 w.re * sinMode a L p.2 w.im =
      Real.sin (π * p.1 / L * (w.re - a)) * Real.sin (π * p.2 / L * (w.im - a))
    rw [sinMode_eq, sinMode_eq]
  have hcont : ∀ {u w : ℝ → ℝ}, Continuous u → Continuous w →
      Continuous fun z : ℂ => u z.re * w z.im := fun hu hw =>
    (hu.comp Complex.continuous_re).mul (hw.comp Complex.continuous_im)
  have cg : Continuous g := by fun_prop
  have ch : Continuous h := by fun_prop
  have cg' : Continuous g' := by fun_prop
  have ch' : Continuous h' := by fun_prop
  -- the gradient of the mode
  have hfd : ∀ z, gradInner (sqMode a L p) f z =
      h z.im * g' z.re * fderiv ℝ f z 1 + g z.re * h' z.im * fderiv ℝ f z Complex.I := by
    intro z
    rw [gradInner, hmode, (hasFDerivAt_sep hg hh z).fderiv, sep_apply_one (g := g) (h := h) (g' := g') (h' := h'),
      sep_apply_I (g := g) (h := h) (g' := g') (h' := h')]
  -- integration by parts in each direction
  have i1 : ∫ z, h z.im * g' z.re * fderiv ℝ f z 1 =
      c₁ ^ 2 * ∫ z, sqMode a L p z * f z := by
    have := integral_mul_fderiv_eq_neg (F := fun z => g' z.re * h z.im)
      (F' := fun z => h z.im * (-(c₁ ^ 2) * g z.re)) (hcont cg' ch)
      ((ch.comp Complex.continuous_im).mul (continuous_const.mul (cg.comp Complex.continuous_re)))
      hf hc 1
      (fun z => by
        have := (hasFDerivAt_sep hg' hh z).hasLineDerivAt (1 : ℂ)
        rwa [sep_apply_one (g := g') (h := h) (g' := fun x => -(c₁ ^ 2) * g x) (h' := h')]
          at this)
    rw [hmode, ← integral_const_mul]
    convert this using 1
    · congr 1; funext z; ring
    · rw [← integral_neg]; congr 1; funext z; ring
  have i2 : ∫ z, g z.re * h' z.im * fderiv ℝ f z Complex.I =
      c₂ ^ 2 * ∫ z, sqMode a L p z * f z := by
    have := integral_mul_fderiv_eq_neg (F := fun z => g z.re * h' z.im)
      (F' := fun z => g z.re * (-(c₂ ^ 2) * h z.im)) (hcont cg ch')
      (hcont cg (continuous_const.mul ch)) hf hc Complex.I
      (fun z => by
        have := (hasFDerivAt_sep hg hh' z).hasLineDerivAt Complex.I
        rwa [sep_apply_I (g := g) (h := h') (g' := g') (h' := fun x => -(c₂ ^ 2) * h x)]
          at this)
    rw [hmode, ← integral_const_mul]
    convert this using 1
    · rw [← integral_neg]; congr 1; funext z; ring
  have hint : ∀ {F : ℂ → ℝ}, Continuous F → ∀ v : ℂ,
      Integrable fun z => F z * fderiv ℝ f z v := fun hF v =>
    (hF.mul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v).mul_left
  simp_rw [hfd]
  rw [integral_add (hint (F := fun z => h z.im * g' z.re)
    ((ch.comp Complex.continuous_im).mul (cg'.comp Complex.continuous_re)) 1)
    (hint (F := fun z => g z.re * h' z.im) (hcont cg ch') Complex.I), i1, i2]
  unfold sqRate
  simp only [c₁, c₂]
  ring

end HeatSq
end LQGMetric

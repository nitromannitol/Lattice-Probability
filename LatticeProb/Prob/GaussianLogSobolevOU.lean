/-
# The Ornstein–Uhlenbeck (Mehler) semigroup for the Gaussian log-Sobolev route

`LatticeProb.GaussianLogSobolev n` (`LatticeProb/External/GaussianLogSobolev.lean`) is the cited
Gaussian log-Sobolev inequality.  This module builds the Ornstein–Uhlenbeck layer that the
entropy-dissipation proof of the `n = 1` instance runs on:

* `LatticeProb.ouSemigroup` — the Mehler semigroup
  `P_t f x = ∫ z, f (e^{-t} x + √(1 - e^{-2t}) z) ∂γ(z)`, `γ = gaussianReal 0 1`;
* `LatticeProb.ouGenerator` — the Ornstein–Uhlenbeck generator `L f = f'' - x f'`;
* `mehler_pushforward_general`, `mehler_pushforward_one` — the Mehler kernel
  `(x, z) ↦ a x + b z` pushes `γ ⊗ γ` forward to the Gaussian of variance `a² + b²`,
  and to `γ` when `a² + b² = 1`;
* `mehler_double_integral_shift` — the iterated-integral form of that pushforward;
* `ouSemigroup_zero`, `ouSemigroup_const`, `ouSemigroup_one`, `ouSemigroup_const_mul` — the
  structural identities (`P_0 = id`, `P_t 1 = 1`, homogeneity);
* `integral_ouSemigroup` — **measure preservation** `∫ P_t f dγ = ∫ f dγ` for `t ≥ 0`;
* `ouSemigroup_add` — **the semigroup law** `P_s (P_t f) = P_{s+t} f` for `s, t ≥ 0`;
* `OUHeatEquation` — **the named open input**: the generator/heat equation
  `∂_t P_t f = L P_t f`, which packages the two weighted integrations by parts and the `Γ₂`
  identity of the entropy-dissipation argument.

Nothing here is conditional on `sorry`; `OUHeatEquation` is a named `Prop`, never an axiom.
-/
import Mathlib
import LatticeProb.External.GaussianLogSobolev

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace LatticeProb

noncomputable section

/-- **The `1`-dimensional Ornstein–Uhlenbeck (Mehler) semigroup.**
`P_t f x = ∫ z, f (e^{-t} x + √(1 - e^{-2t}) z) ∂γ(z)`, where `γ = gaussianReal 0 1`. -/
def ouSemigroup (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ z, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
    ∂(gaussianReal 0 1)

/-- **The `1`-dimensional Ornstein–Uhlenbeck generator** `L f = f'' - x f'`. -/
def ouGenerator (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (deriv f) x - x * deriv f x

/-- **The Mehler kernel pushes `γ ⊗ γ` forward to the Gaussian of variance `a² + b²`.**
The kernel is `(x, z) ↦ a x + b z`; the two coordinates are independent standard Gaussians,
so the image is centred Gaussian with variance `a² + b²`. -/
theorem mehler_pushforward_general (a b : ℝ) :
    Measure.map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1))
      = gaussianReal 0 (NNReal.mk (a ^ 2 + b ^ 2) (by positivity)) := by
  have h1 : Measure.map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1))
      = Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
          (Measure.map (Prod.map (fun x : ℝ => a * x) (fun y : ℝ => b * y))
            ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h1, ← Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
    (by fun_prop) (by fun_prop)]
  rw [gaussianReal_map_const_mul a, gaussianReal_map_const_mul b]
  simp only [mul_zero, mul_one]
  rw [show Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
      ((gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a))).prod
        (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b))))
      = (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a)))
        ∗ (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b))) from rfl]
  rw [gaussianReal_conv_gaussianReal]
  simp only [add_zero]
  congr 1

/-- **The Mehler kernel with `a² + b² = 1` pushes `γ ⊗ γ` forward to `γ`.** -/
theorem mehler_pushforward_one (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    Measure.map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 := by
  rw [mehler_pushforward_general a b]
  congr 1
  rw [← NNReal.coe_inj]
  simp only [NNReal.coe_one]
  exact hab

/-- **The shifted Mehler integral.**  For `a, b, c : ℝ` with `v = a² + b²`, the iterated
integral of `f (c + (a z + b z₁))` against `γ ⊗ γ` is the integral of `f` against the
Gaussian of variance `v` and mean `c`. -/
theorem mehler_double_integral_shift (a b c : ℝ) (v : ℝ≥0) (hv : (v : ℝ) = a ^ 2 + b ^ 2)
    (f : ℝ → ℝ) (hf : Integrable f (gaussianReal c v)) :
    ∫ z, ∫ z₁, f (c + (a * z + b * z₁)) ∂(gaussianReal 0 1) ∂(gaussianReal 0 1)
      = ∫ y, f y ∂(gaussianReal c v) := by
  have hmap := mehler_pushforward_general a b
  have hphi : Measurable (fun p : ℝ × ℝ => a * p.1 + b * p.2) := by fun_prop
  have hv' : NNReal.mk (a ^ 2 + b ^ 2) (by positivity) = v := by
    rw [← NNReal.coe_inj]
    simp only [NNReal.coe_mk]
    exact hv.symm
  have hshift : Measure.map (fun p : ℝ × ℝ => c + (a * p.1 + b * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal c v := by
    rw [show (fun p : ℝ × ℝ => c + (a * p.1 + b * p.2))
        = (fun y : ℝ => c + y) ∘ (fun p : ℝ × ℝ => a * p.1 + b * p.2) from rfl,
      ← Measure.map_map (by fun_prop) hphi, hmap, gaussianReal_map_const_add, hv']
    simp only [zero_add]
  have hint : Integrable (fun p : ℝ × ℝ => f (c + (a * p.1 + b * p.2)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine Integrable.comp_measurable ?_ (by fun_prop)
    rw [hshift]
    exact hf
  rw [integral_integral hint, ← hshift]
  refine (integral_map (by fun_prop) ?_).symm
  rw [hshift]
  exact hf.aestronglyMeasurable

/-- **The affine image of the standard Gaussian.**  The pushforward of `γ` under
`z ↦ c + a z` is the Gaussian of mean `c` and variance `a²`. -/
theorem gaussianReal_affine (c a : ℝ) :
    gaussianReal c (NNReal.mk (a ^ 2) (sq_nonneg a))
      = Measure.map (fun z : ℝ => c + a * z) (gaussianReal 0 1) := by
  have hcomp : (fun z : ℝ => c + a * z)
      = (fun y : ℝ => y + c) ∘ (fun z : ℝ => a * z) := by
    funext z; simp [add_comm]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  simp only [mul_zero, zero_add]
  congr 1
  rw [← NNReal.coe_inj]
  simp only [NNReal.coe_mk, NNReal.coe_one, NNReal.coe_mul]
  rw [mul_one]

/-- **Integrability transfers along an affine image of the standard Gaussian.** -/
theorem integrable_comp_affine (c a : ℝ) (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal c (NNReal.mk (a ^ 2) (sq_nonneg a)))) :
    Integrable (fun z : ℝ => f (c + a * z)) (gaussianReal 0 1) := by
  rw [gaussianReal_affine c a] at hf
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mp hf

/-- **`P_0` is the identity.** -/
theorem ouSemigroup_zero (f : ℝ → ℝ) : ouSemigroup 0 f = f := by
  funext x
  simp only [ouSemigroup]
  rw [show (fun z => f (Real.exp (-(0 : ℝ)) * x
        + Real.sqrt (1 - Real.exp (-2 * 0)) * z)) = fun _ => f x by
      funext z; norm_num]
  simp

/-- **`P_t` preserves constants** (the Mehler kernel is a probability kernel). -/
theorem ouSemigroup_const (t : ℝ) (c : ℝ) : ouSemigroup t (fun _ => c) = fun _ => c := by
  funext x
  simp only [ouSemigroup]
  rw [show (fun z => (fun _ => c) (Real.exp (-t) * x
        + Real.sqrt (1 - Real.exp (-2 * t)) * z)) = fun _ => c by rfl]
  simp

/-- **The Mehler semigroup preserves the constant `1`** (probability-kernel normalisation). -/
theorem ouSemigroup_one (t : ℝ) : ouSemigroup t (fun _ => (1 : ℝ)) = fun _ => 1 :=
  ouSemigroup_const t 1

/-- **The Mehler semigroup is homogeneous.**  `P_t (c · f) = c · P_t f` pointwise, directly from
the linearity of the Bochner integral. -/
theorem ouSemigroup_const_mul (t c : ℝ) (f : ℝ → ℝ) :
    ouSemigroup t (fun x => c * f x) = fun x => c * ouSemigroup t f x := by
  funext x
  simp only [ouSemigroup]
  rw [← integral_const_mul]

/-- **The Mehler semigroup is an `L²` contraction.**  `(P_t f x)² ≤ P_t (f²) x`, by Jensen's
inequality applied to the probability measure `γ` and the convex function `y ↦ y²`.  This is
the positivity of the carré du champ `Γ(P_t f) = P_t (f²) - (P_t f)²` at a single point. -/
theorem ouSemigroup_sq_le (t : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hf : Integrable f (gaussianReal (Real.exp (-t) * x)
      (NNReal.mk (Real.sqrt (1 - Real.exp (-2 * t)) ^ 2) (sq_nonneg _))))
    (hf2 : Integrable (fun y => (f y) ^ 2) (gaussianReal (Real.exp (-t) * x)
      (NNReal.mk (Real.sqrt (1 - Real.exp (-2 * t)) ^ 2) (sq_nonneg _)))) :
    (ouSemigroup t f x) ^ 2 ≤ ouSemigroup t (fun y => (f y) ^ 2) x := by
  simp only [ouSemigroup]
  refine ConvexOn.map_integral_le (Even.convexOn_pow (by norm_num : Even 2))
    (by fun_prop) isClosed_univ (Filter.Eventually.of_forall fun z => Set.mem_univ _) ?_ ?_
  · exact integrable_comp_affine _ _ f hf
  · exact integrable_comp_affine _ _ _ hf2

/-- **The Mehler semigroup preserves the Gaussian measure**: `∫ P_t f dγ = ∫ f dγ` for
`t ≥ 0`.  The Mehler kernel `(x, z) ↦ e^{-t} x + √(1 - e^{-2t}) z` pushes `γ ⊗ γ`
forward to `γ` (`mehler_pushforward_one`), which gives both the integrability of the
uncurried integrand and the identity through Fubini and the change-of-variables formula. -/
theorem integral_ouSemigroup (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal 0 1)) :
    ∫ x, ouSemigroup t f x ∂(gaussianReal 0 1) = ∫ z, f z ∂(gaussianReal 0 1) := by
  have hab : Real.exp (-t) ^ 2 + Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 := by
    have h1 : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have h2 : Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 - Real.exp (-2 * t) := by
      rw [Real.sq_sqrt]
      rw [sub_nonneg, Real.exp_le_one_iff]; linarith
    rw [h1, h2]; ring
  have hmap := mehler_pushforward_one (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) hab
  have hphi : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-t) * p.1 + Real.sqrt (1 - Real.exp (-2 * t)) * p.2) := by fun_prop
  have hint : Integrable (fun p : ℝ × ℝ =>
      f (Real.exp (-t) * p.1 + Real.sqrt (1 - Real.exp (-2 * t)) * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine Integrable.comp_measurable ?_ (by fun_prop)
    rw [hmap]
    exact hf
  have haesm : AEStronglyMeasurable f
      (Measure.map (fun p : ℝ × ℝ =>
        Real.exp (-t) * p.1 + Real.sqrt (1 - Real.exp (-2 * t)) * p.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  have h2 : ∫ x, ouSemigroup t f x ∂(gaussianReal 0 1)
      = ∫ p : ℝ × ℝ,
          f (Real.exp (-t) * p.1 + Real.sqrt (1 - Real.exp (-2 * t)) * p.2)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simp only [ouSemigroup]
    rw [integral_integral hint]
  rw [h2]
  conv_rhs => rw [← hmap]
  exact (integral_map hphi.aemeasurable haesm).symm

/-- **The Mehler semigroup is a semigroup**: `P_s (P_t f) = P_{s + t} f` for `s, t ≥ 0`.
The composition of the two Mehler kernels is again a Mehler kernel, because
`e^{-2t} (1 - e^{-2s}) + (1 - e^{-2t}) = 1 - e^{-2(s+t)}`; the identity is then the
pushforward form `mehler_double_integral_shift` applied to that kernel. -/
theorem ouSemigroup_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : ℝ → ℝ)
    (hf : ∀ (c : ℝ) (v : ℝ≥0), Integrable f (gaussianReal c v)) :
    ouSemigroup s (ouSemigroup t f) = ouSemigroup (s + t) f := by
  funext x
  have hsq : (Real.exp (-t) * Real.sqrt (1 - Real.exp (-2 * s))) ^ 2
      + Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 - Real.exp (-2 * (s + t)) := by
    have h1 : Real.sqrt (1 - Real.exp (-2 * s)) ^ 2 = 1 - Real.exp (-2 * s) := by
      rw [Real.sq_sqrt]; rw [sub_nonneg, Real.exp_le_one_iff]; linarith
    have h2 : Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 - Real.exp (-2 * t) := by
      rw [Real.sq_sqrt]; rw [sub_nonneg, Real.exp_le_one_iff]; linarith
    have h3 : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by rw [sq, ← Real.exp_add]; ring_nf
    have h4 : Real.exp (-2 * (s + t)) = Real.exp (-2 * s) * Real.exp (-2 * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [mul_pow, h1, h2, h3, h4]; ring
  have hexp : Real.exp (-t) * Real.exp (-s) = Real.exp (-(s + t)) := by
    rw [← Real.exp_add]; ring_nf
  have hshift : ∀ z z₁ : ℝ, Real.exp (-t) * (Real.exp (-s) * x
        + Real.sqrt (1 - Real.exp (-2 * s)) * z)
        + Real.sqrt (1 - Real.exp (-2 * t)) * z₁
      = Real.exp (-(s + t)) * x
        + ((Real.exp (-t) * Real.sqrt (1 - Real.exp (-2 * s))) * z
          + Real.sqrt (1 - Real.exp (-2 * t)) * z₁) := by
    intro z z₁; rw [← hexp]; ring
  have hnn : (0 : ℝ) ≤ 1 - Real.exp (-2 * (s + t)) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; linarith
  have hf' : Integrable f (gaussianReal (Real.exp (-(s + t)) * x)
      (NNReal.mk (1 - Real.exp (-2 * (s + t))) hnn)) := hf _ _
  simp only [ouSemigroup]
  rw [show (∫ z, (∫ z₁, f (Real.exp (-t) * (Real.exp (-s) * x
          + Real.sqrt (1 - Real.exp (-2 * s)) * z)
          + Real.sqrt (1 - Real.exp (-2 * t)) * z₁)
        ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1))
      = ∫ z, ∫ z₁, f (Real.exp (-(s + t)) * x
          + ((Real.exp (-t) * Real.sqrt (1 - Real.exp (-2 * s))) * z
            + Real.sqrt (1 - Real.exp (-2 * t)) * z₁))
        ∂(gaussianReal 0 1) ∂(gaussianReal 0 1) from by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z₁ => ?_)
    simp only [hshift z z₁]]
  rw [mehler_double_integral_shift (Real.exp (-t) * Real.sqrt (1 - Real.exp (-2 * s)))
    (Real.sqrt (1 - Real.exp (-2 * t))) (Real.exp (-(s + t)) * x)
    (NNReal.mk (1 - Real.exp (-2 * (s + t))) hnn) hsq.symm f hf']
  have hmap2 : gaussianReal (Real.exp (-(s + t)) * x) (NNReal.mk (1 - Real.exp (-2 * (s + t))) hnn)
      = Measure.map (fun z : ℝ => Real.exp (-(s + t)) * x
          + Real.sqrt (NNReal.mk (1 - Real.exp (-2 * (s + t))) hnn : ℝ) * z)
          (gaussianReal 0 1) := by
    have hcomp : (fun z : ℝ => Real.exp (-(s + t)) * x
        + Real.sqrt (NNReal.mk (1 - Real.exp (-2 * (s + t))) hnn : ℝ) * z)
        = (fun y : ℝ => y + Real.exp (-(s + t)) * x)
          ∘ (fun z : ℝ =>
              Real.sqrt (NNReal.mk (1 - Real.exp (-2 * (s + t))) hnn : ℝ) * z) := by
      funext z; simp [add_comm]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    simp only [mul_zero, zero_add]
    congr 1
    rw [← NNReal.coe_inj]
    simp only [NNReal.coe_mk, NNReal.coe_one, NNReal.coe_mul]
    rw [Real.sq_sqrt hnn, mul_one]
  rw [hmap2]
  exact integral_map (by fun_prop) (hmap2 ▸ hf').aestronglyMeasurable

/-- **The intertwining identity** `∂_x P_t f = e^{-t} P_t (∂_x f)`.  For a Lipschitz `f` with
derivative `g` bounded by the Lipschitz constant, the derivative of `P_t f` is `e^{-t}` times
`P_t g`.  The proof differentiates under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with the dominating function `e^{-t} L`. -/
theorem hasDerivAt_ouSemigroup (t : ℝ) (f g : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : LipschitzWith ⟨L, hL⟩ f) (hderiv : ∀ y, HasDerivAt f (g y) y)
    (hg : ∀ y, |g y| ≤ L) (hgm : Measurable g) (x : ℝ) :
    HasDerivAt (ouSemigroup t f) (Real.exp (-t) * ouSemigroup t g x) x := by
  set a : ℝ := Real.exp (-t) with ha
  set b : ℝ := Real.sqrt (1 - Real.exp (-2 * t)) with hb
  have hapos : 0 < a := Real.exp_pos _
  have hb1 : |b| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one, sub_le_iff_le_add]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  have hmem : MemLp (fun z : ℝ => |z|) 2 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).norm
  have hFint : Integrable (fun z : ℝ => f (a * x + b * z)) (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_const (|f 0| + L * |a * x|)).add
      (hmem.integrable (by norm_num) |>.const_mul L))
      (hf.continuous.aestronglyMeasurable.comp_aemeasurable (by fun_prop)) ?_
    filter_upwards with z
    have h1 : |f (a * x + b * z) - f 0| ≤ L * |a * x + b * z| := by
      have h := hf.dist_le_mul (a * x + b * z) 0
      rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
      convert h using 2
      exact (NNReal.coe_mk L hL).symm
    have h2 : |a * x + b * z| ≤ |a * x| + |z| := by
      calc |a * x + b * z| ≤ |a * x| + |b * z| := abs_add_le _ _
        _ = |a * x| + |b| * |z| := by simp only [abs_mul]
        _ ≤ |a * x| + 1 * |z| :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hb1 (abs_nonneg _))
        _ = |a * x| + |z| := by ring
    have h3 : |f (a * x + b * z)| ≤ |f 0| + L * |a * x| + L * |z| := by
      have h4 : |f (a * x + b * z)| ≤ L * (|a * x| + |z|) + |f 0| := by
        calc |f (a * x + b * z)|
            = |(f (a * x + b * z) - f 0) + f 0| := by ring_nf
          _ ≤ |f (a * x + b * z) - f 0| + |f 0| := abs_add_le _ _
          _ ≤ L * (|a * x| + |z|) + |f 0| := by
              have := h1.trans (mul_le_mul_of_nonneg_left h2 hL)
              linarith
      nlinarith [h4]
    rw [Real.norm_eq_abs]
    exact h3
  have hF'meas : AEStronglyMeasurable (fun z : ℝ => g (a * x + b * z) * a) (gaussianReal 0 1) :=
    ((hgm.comp (by fun_prop)).aestronglyMeasurable).mul_const a
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := x) (μ := gaussianReal 0 1)
    (F := fun s z => f (a * s + b * z))
    (F' := fun s z => g (a * s + b * z) * a)
    (bound := fun _ : ℝ => a * L)
    Filter.univ_mem
    (by filter_upwards with s
        exact (hf.continuous.aestronglyMeasurable.comp_aemeasurable (by fun_prop)))
    hFint
    hF'meas
    (by
      filter_upwards with z s _
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hapos, mul_comm]
      exact mul_le_mul_of_nonneg_left (hg _) hapos.le)
    (integrable_const _)
    (by
      filter_upwards with z s _
      have h1 : HasDerivAt (fun s : ℝ => a * s + b * z) a s := by
        simpa using ((hasDerivAt_id s).const_mul a).add_const (b * z)
      exact (hderiv (a * s + b * z)).comp s h1)
  have hval : ∫ z, g (a * x + b * z) * a ∂(gaussianReal 0 1) = a * ouSemigroup t g x := by
    rw [integral_mul_const]
    simp only [ouSemigroup]
    ring
  rw [hval] at hmain
  exact hmain.2

/-- **The time derivative of the Mehler semigroup.**  For `t > 0`, the derivative of
`s ↦ P_s f x` at `t` is the integral of `g` against the Mehler kernel times the derivative of
the kernel's argument, where `g` is the derivative of `f`.  This is the second half of the heat
equation `∂_t P_t f = L P_t f`: combined with `hasDerivAt_ouSemigroup` and the Stein identity
`∫ g dγ = ∫ z g z dγ` it gives `∂_t P_t f = P_t (f'' - · f') = L P_t f`. -/
theorem hasDerivAt_ouSemigroup_time (t : ℝ) (ht : 0 < t) (f g : ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hf : LipschitzWith ⟨L, hL⟩ f) (hderiv : ∀ y, HasDerivAt f (g y) y)
    (hg : ∀ y, |g y| ≤ L) (hgm : Measurable g) (x : ℝ) :
    HasDerivAt (fun s => ouSemigroup s f x)
      (∫ z, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
        * (-(Real.exp (-t)) * x
          + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * z)
        ∂(gaussianReal 0 1)) t := by

  have hbpos : 0 < Real.sqrt (1 - Real.exp (-2 * t)) := by
    rw [Real.sqrt_pos, sub_pos, Real.exp_lt_one_iff]; linarith
  have hmem : MemLp (fun z : ℝ => |z|) 2 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).norm
  have hFint : Integrable (fun z : ℝ => f (Real.exp (-t) * x
      + Real.sqrt (1 - Real.exp (-2 * t)) * z)) (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_const (|f 0| + L * |Real.exp (-t) * x|)).add
      (hmem.integrable (by norm_num) |>.const_mul L))
      (hf.continuous.aestronglyMeasurable.comp_aemeasurable (by fun_prop)) ?_
    filter_upwards with z
    have h1 : |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) - f 0|
        ≤ L * |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| := by
      have h := hf.dist_le_mul (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) 0
      rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
      convert h using 2
      exact (NNReal.coe_mk L hL).symm
    have h2 : |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z|
        ≤ |Real.exp (-t) * x| + |z| := by
      calc |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z|
          ≤ |Real.exp (-t) * x| + |Real.sqrt (1 - Real.exp (-2 * t)) * z| := abs_add_le _ _
        _ = |Real.exp (-t) * x| + |Real.sqrt (1 - Real.exp (-2 * t))| * |z| := by
            simp only [abs_mul]
        _ ≤ |Real.exp (-t) * x| + 1 * |z| := by
            refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
            rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one, sub_le_iff_le_add]
            exact le_add_of_nonneg_right (Real.exp_nonneg _)
        _ = |Real.exp (-t) * x| + |z| := by ring
    have h3 : |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)|
        ≤ |f 0| + L * |Real.exp (-t) * x| + L * |z| := by
      have h4 : |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)|
          ≤ L * (|Real.exp (-t) * x| + |z|) + |f 0| := by
        calc |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)|
            = |(f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) - f 0) + f 0| := by
              ring_nf
          _ ≤ |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) - f 0| + |f 0| :=
              abs_add_le _ _
          _ ≤ L * (|Real.exp (-t) * x| + |z|) + |f 0| := by
              have := h1.trans (mul_le_mul_of_nonneg_left h2 hL)
              linarith
      nlinarith [h4]
    rw [Real.norm_eq_abs]
    exact h3
  have hderiv_sqrt : ∀ u : ℝ, 0 < u →
      HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-2 * s)))
        (Real.exp (-2 * u) / Real.sqrt (1 - Real.exp (-2 * u))) u := by
    intro u hu
    have h1 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-2 * s)) (2 * Real.exp (-2 * u)) u := by
      have h2 : HasDerivAt (fun s : ℝ => -2 * s) (-2) u := by
        simpa using (hasDerivAt_id u).const_mul (-2)
      have h3 : HasDerivAt (fun s : ℝ => Real.exp (-2 * s)) (Real.exp (-2 * u) * (-2)) u :=
        (Real.hasDerivAt_exp (-2 * u)).comp u h2
      have h4 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-2 * s))
          (0 - Real.exp (-2 * u) * (-2)) u :=
        (hasDerivAt_const u (1 : ℝ)).sub h3
      convert h4 using 1
      ring
    have hpos : 0 < 1 - Real.exp (-2 * u) := by
      rw [sub_pos, Real.exp_lt_one_iff]; linarith
    have h5 := h1.sqrt (ne_of_gt hpos)
    convert h5 using 1
    field_simp
  have hderiv_exp : ∀ u : ℝ,
      HasDerivAt (fun s : ℝ => Real.exp (-s)) (-(Real.exp (-u))) u := by
    intro u
    have h2 : HasDerivAt (fun s : ℝ => -s) (-1) u := by
      simpa using (hasDerivAt_id u).const_mul (-1)
    have h3 := (Real.hasDerivAt_exp (-u)).comp u h2
    have h4 : (Real.exp ∘ Neg.neg) = fun s : ℝ => Real.exp (-s) := rfl
    rw [h4] at h3
    have h5 : Real.exp (-u) * -1 = -(Real.exp (-u)) := by ring
    rw [h5] at h3
    exact h3
  have hcont : ContinuousAt
      (fun s : ℝ => Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) t := by
    refine ContinuousAt.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · rw [Real.sqrt_ne_zero']
      rw [sub_pos, Real.exp_lt_one_iff]; linarith
  set K : ℝ := Real.exp (-t) / Real.sqrt (1 - Real.exp (-t)) with hK
  have hK0 : 0 ≤ K := div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
  have hset : Set.Icc (t / 2) (2 * t) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hbound : ∀ᵐ z ∂(gaussianReal 0 1), ∀ s ∈ Set.Icc (t / 2) (2 * t),
      ‖g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * z)
        * (-(Real.exp (-s)) * x
          + (Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) * z)‖
        ≤ L * (|x| + 1 + K) * (1 + |z|) := by
    filter_upwards with z s hs
    have hs1 : t / 2 ≤ s := hs.1
    have hs2 : s ≤ 2 * t := hs.2
    have hs0 : 0 < s := by linarith
    have hexp_le : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hratio : Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s)) ≤ K := by
      rw [hK]
      have h1 : Real.exp (-2 * s) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
      have h3 : 0 < 1 - Real.exp (-t) := by rw [sub_pos, Real.exp_lt_one_iff]; linarith
      have h4 : 0 < 1 - Real.exp (-2 * s) := by rw [sub_pos, Real.exp_lt_one_iff]; linarith
      have h5 : Real.sqrt (1 - Real.exp (-t)) ≤ Real.sqrt (1 - Real.exp (-2 * s)) :=
        Real.sqrt_le_sqrt (by linarith)
      have h6 : 0 < Real.sqrt (1 - Real.exp (-t)) := Real.sqrt_pos.mpr h3
      calc Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))
          ≤ Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * s)) :=
            div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ ≤ Real.exp (-t) / Real.sqrt (1 - Real.exp (-t)) :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le h6 h5
    have hratio0 : 0 ≤ Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s)) :=
      div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_mul]
    have hg' : |g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * z)| ≤ L := hg _
    have hz : |-(Real.exp (-s)) * x
        + (Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) * z| ≤ |x| + K * |z| := by
      calc |-(Real.exp (-s)) * x
            + (Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) * z|
          ≤ |-(Real.exp (-s)) * x|
            + |(Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) * z| := abs_add_le _ _
        _ = Real.exp (-s) * |x|
            + |Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))| * |z| := by
            rw [abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
        _ ≤ 1 * |x| + K * |z| := by
            rw [abs_of_nonneg hratio0]
            exact add_le_add (mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hratio (abs_nonneg _))
        _ = |x| + K * |z| := by ring
    calc |g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * z)|
          * |-(Real.exp (-s)) * x
            + (Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) * z|
        ≤ L * (|x| + K * |z|) := mul_le_mul hg' hz (abs_nonneg _) hL
      _ ≤ L * (|x| + 1 + K) * (1 + |z|) := by
          have hx0 : 0 ≤ |x| := abs_nonneg x
          have hz0 : 0 ≤ |z| := abs_nonneg z
          have hkey : |x| + K * |z| ≤ (|x| + 1 + K) * (1 + |z|) := by
            nlinarith [mul_nonneg hx0 hz0, mul_nonneg hz0 hK0, mul_nonneg hx0 hK0]
          calc L * (|x| + K * |z|) ≤ L * ((|x| + 1 + K) * (1 + |z|)) :=
                mul_le_mul_of_nonneg_left hkey hL
            _ = L * (|x| + 1 + K) * (1 + |z|) := by ring
  have hboundint : Integrable (fun z : ℝ => L * (|x| + 1 + K) * (1 + |z|)) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add (hmem.integrable (by norm_num))).const_mul _
  have hF'meas : AEStronglyMeasurable (fun z : ℝ =>
      g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
        * (-(Real.exp (-t)) * x
          + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * z)) (gaussianReal 0 1) :=
    (hgm.comp (by fun_prop)).aestronglyMeasurable.mul (by fun_prop)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Icc (t / 2) (2 * t)) (x₀ := t) (μ := gaussianReal 0 1)
    (F := fun s z => f (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * z))
    (F' := fun s z => g (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * z)
        * (-(Real.exp (-s)) * x
          + (Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) * z))
    (bound := fun z : ℝ => L * (|x| + 1 + K) * (1 + |z|))
    hset
    (by filter_upwards with s
        exact (hf.continuous.aestronglyMeasurable.comp_aemeasurable (by fun_prop)))
    hFint
    hF'meas
    hbound
    hboundint
    (by
      filter_upwards with z s hs
      have hs0 : 0 < s := by linarith [hs.1, ht]
      have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s) * x
          + Real.sqrt (1 - Real.exp (-2 * s)) * z)
          (-(Real.exp (-s)) * x
            + (Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) * z) s := by
        have h2 := ((hderiv_exp s).mul_const x).add ((hderiv_sqrt s hs0).mul_const z)
        have h3 : (fun s : ℝ => Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * z)
            = (fun s : ℝ => Real.exp (-s) * x)
              + fun s : ℝ => Real.sqrt (1 - Real.exp (-2 * s)) * z := rfl
        rw [h3]
        convert h2 using 1
      exact (hderiv (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * z)).comp s h1)
  exact hmain.2

/-- **The derivative of the standard Gaussian density.**  `d/dx gaussianPDFReal 0 1 x
= -(x * gaussianPDFReal 0 1 x)`, the identity that makes the Gaussian an invariant measure of
the Ornstein–Uhlenbeck generator. -/
theorem gaussianPDFReal_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => gaussianPDFReal 0 1 y) (-(x * gaussianPDFReal 0 1 x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h3 := (h2.neg).div_const 2
    have h4 : (fun x : ℝ => (-fun y => y ^ 2) x / 2) = fun y : ℝ => -(y ^ 2) / 2 := rfl
    rw [h4] at h3
    have h5 : -(2 * x) / 2 = -x := by ring
    rw [h5] at h3
    exact h3
  have h4 := (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x h1
  have h4' : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * -x) x := by
    have h6 : (Real.exp ∘ fun y : ℝ => -(y ^ 2) / 2)
        = fun y : ℝ => Real.exp (-(y ^ 2) / 2) := rfl
    rw [h6] at h4
    exact h4
  have h5 : HasDerivAt (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹
      * Real.exp (-(y ^ 2) / 2)) ((Real.sqrt (2 * Real.pi))⁻¹
        * (Real.exp (-(x ^ 2) / 2) * -x)) x := h4'.const_mul _
  have hfun : gaussianPDFReal 0 1 = fun y : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2) := by
    funext y
    rw [gaussianPDFReal_def]
    norm_num
  rw [hfun]
  convert h5 using 1
  simp only
  ring

theorem integral_deriv_gaussianReal (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hint3 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) volume)
    (hint4 : Integrable (fun x => f x * -(x * gaussianPDFReal 0 1 x)) volume)
    (hint5 : Integrable (fun x => deriv f x * gaussianPDFReal 0 1 x) volume) :
    ∫ x, deriv f x ∂(gaussianReal 0 1) = ∫ x, x * f x ∂(gaussianReal 0 1) := by
  have hgauss : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hconv : ∀ g : ℝ → ℝ,
      ∫ x, g x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x * g x := by
    intro g
    rw [hgauss]
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun x => by
        rw [gaussianPDF]; exact ENNReal.ofReal_lt_top) g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
  have hderiv_pdf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => gaussianPDFReal 0 1 y)
      (-(x * gaussianPDFReal 0 1 x)) x := gaussianPDFReal_hasDerivAt
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => f x) (v := fun x : ℝ => gaussianPDFReal 0 1 x)
    (u' := fun x : ℝ => deriv f x) (v' := fun x : ℝ => -(x * gaussianPDFReal 0 1 x))
    (fun x _ => (hf.differentiable_one x).hasDerivAt)
    (fun x _ => hderiv_pdf x)
    hint4 hint5 hint3
  · rw [hconv (fun x => deriv f x), hconv (fun x => x * f x)]
    have h1 : ∫ x, gaussianPDFReal 0 1 x * (x * f x)
        = ∫ x, deriv f x * gaussianPDFReal 0 1 x := by
      have h3 : ∫ x, f x * -(x * gaussianPDFReal 0 1 x)
          = -∫ x, gaussianPDFReal 0 1 x * (x * f x) := by
        rw [← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
      rw [h3] at hIBP
      linarith [hIBP]
    have h2 : ∫ x, gaussianPDFReal 0 1 x * deriv f x
        = ∫ x, deriv f x * gaussianPDFReal 0 1 x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h1, h2]

/-- **The shifted Stein identity.**  For `g` a `C¹` function and `c, b : ℝ`, the weighted
integration by parts against `γ` reads `∫ y g (c + b y) dγ = b ∫ g' (c + b y) dγ`.  It is the
Stein identity applied to the composition `y ↦ g (c + b y)`, whose derivative is
`b · g' (c + b y)`. -/
theorem integral_mul_comp_gaussianReal (c b : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hint3 : Integrable (fun y => g (c + b * y) * gaussianPDFReal 0 1 y) volume)
    (hint4 : Integrable (fun y => g (c + b * y) * -(y * gaussianPDFReal 0 1 y)) volume)
    (hint5 : Integrable (fun y => deriv g (c + b * y) * gaussianPDFReal 0 1 y) volume) :
    ∫ y, y * g (c + b * y) ∂(gaussianReal 0 1)
      = b * ∫ y, deriv g (c + b * y) ∂(gaussianReal 0 1) := by
  have hF : ContDiff ℝ 1 (fun y : ℝ => g (c + b * y)) := by fun_prop
  have hderiv : ∀ y : ℝ, deriv (fun y : ℝ => g (c + b * y)) y = b * deriv g (c + b * y) := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => c + b * y) b y := by
      simpa using ((hasDerivAt_id y).const_mul b).const_add c
    have h2 := (hg.differentiable_one (c + b * y)).hasDerivAt.comp y h1
    have h3 : (g ∘ fun y : ℝ => c + b * y) = fun y : ℝ => g (c + b * y) := rfl
    rw [h3] at h2
    rw [h2.deriv]
    ring
  have h5' : Integrable (fun y => deriv (fun y : ℝ => g (c + b * y)) y
      * gaussianPDFReal 0 1 y) volume := by
    refine (hint5.const_mul b).congr (Filter.Eventually.of_forall fun y => ?_)
    show b * (deriv g (c + b * y) * gaussianPDFReal 0 1 y)
      = deriv (fun y : ℝ => g (c + b * y)) y * gaussianPDFReal 0 1 y
    rw [hderiv y]; ring
  have hstein := integral_deriv_gaussianReal (fun y : ℝ => g (c + b * y)) hF hint3 hint4 h5'
  have hfun : (fun y : ℝ => deriv (fun y : ℝ => g (c + b * y)) y)
      = fun y => b * deriv g (c + b * y) := funext hderiv
  rw [hfun, integral_const_mul] at hstein
  exact hstein.symm

/-- The carré du champ of the Ornstein–Uhlenbeck generator `L g = g'' - x g'`:
`Γ(f) = (f')²`. -/
def carreDuChamp (f : ℝ → ℝ) (x : ℝ) : ℝ := (deriv f x) ^ 2

/-- The iterated carré du champ `Γ₂(f) = (f'')² + (f')²`. -/
def carreDuChamp2 (f : ℝ → ℝ) (x : ℝ) : ℝ := (deriv (deriv f) x) ^ 2 + (deriv f x) ^ 2

/-- **Bakry–Émery `Γ₂ = 1`.**  For the Ornstein–Uhlenbeck generator `L g = g'' - x g'` and
`Γ(f) = (f')²`, the iterated carré du champ satisfies
`Γ₂(f) = (1/2) L Γ(f) - Γ(f, L f)`, and with `Γ₂(f) = (f'')² + (f')²` this says
exactly that the curvature of the standard Gaussian is `1`.  Written out with the derivative values
`a = f'(x)`, `b = f''(x)`, `c = f'''(x)`, the identity is the algebraic cancellation
`(b^2 + a^2) - (1/2) * (2 * b^2 + 2 * a * c - 2 * x * a * b) + a * (c - a - x * b) = 0`. -/
theorem carreDuChamp2_bakryEmery (a b c x : ℝ) :
    (b ^ 2 + a ^ 2) - (1 / 2) * (2 * b ^ 2 + 2 * a * c - 2 * x * a * b)
      + a * (c - a - x * b) = 0 := by
  ring

/-- **The Ornstein–Uhlenbeck heat equation.**  The time derivative of the Mehler semigroup is
the semigroup applied to the generator `L g = g'' - y g'`, here written in the divergence form
`y ↦ gg y - y * g y` with `gg = g'`.  The proof combines `hasDerivAt_ouSemigroup_time` (the
derivative of the kernel) with the shifted Stein identity `integral_mul_comp_gaussianReal`
(which converts the `y`-weight into the derivative of `g`), and the identity
`e^{-2t} / √(1 - e^{-2t}) · √(1 - e^{-2t}) = e^{-2t} = 1 - (1 - e^{-2t})`. -/
theorem hasDerivAt_ouSemigroup_heat (t : ℝ) (ht : 0 < t) (f g gg : ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hf : LipschitzWith ⟨L, hL⟩ f) (hderiv : ∀ y, HasDerivAt f (g y) y)
    (hg : ∀ y, |g y| ≤ L) (hgm : Measurable g) (hgc : ContDiff ℝ 1 g)
    (hderiv2 : ∀ y, HasDerivAt g (gg y) y)
    (x : ℝ)
    (hint3 : Integrable (fun y => g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
      * gaussianPDFReal 0 1 y) volume)
    (hint4 : Integrable (fun y => g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
      * -(y * gaussianPDFReal 0 1 y)) volume)
    (hint5 : Integrable (fun y =>
      deriv g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
      * gaussianPDFReal 0 1 y) volume)
    (hint3' : Integrable (fun y => g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y))
      (gaussianReal 0 1))
    (hint4' : Integrable (fun y =>
      y * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y))
      (gaussianReal 0 1))
    (hint5' : Integrable (fun y => gg (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y))
      (gaussianReal 0 1)) :
    HasDerivAt (fun s => ouSemigroup s f x)
      (ouSemigroup t (fun y => gg y - y * g y) x) t := by
  have hbpos : 0 < Real.sqrt (1 - Real.exp (-2 * t)) := by
    rw [Real.sqrt_pos, sub_pos, Real.exp_lt_one_iff]; linarith
  have hb2 : (Real.sqrt (1 - Real.exp (-2 * t))) ^ 2 = 1 - Real.exp (-2 * t) := by
    rw [Real.sq_sqrt]
    rw [sub_nonneg, Real.exp_le_one_iff]; linarith
  have htime := hasDerivAt_ouSemigroup_time t ht f g L hL hf hderiv hg hgm x
  have hstein := integral_mul_comp_gaussianReal (Real.exp (-t) * x)
    (Real.sqrt (1 - Real.exp (-2 * t))) g hgc hint3 hint4 hint5
  have hgg' : ∀ y, gg y = deriv g y := fun y => (hderiv2 y).deriv.symm
  have h1 : ∫ y, y * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
        ∂(gaussianReal 0 1)
      = Real.sqrt (1 - Real.exp (-2 * t))
        * ∫ y, gg (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          ∂(gaussianReal 0 1) := by
    rw [hstein]
    refine congrArg (fun z => Real.sqrt (1 - Real.exp (-2 * t)) * z) ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (hgg' (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)).symm
  have hkey : ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
        * (-(Real.exp (-t)) * x
          + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y)
        ∂(gaussianReal 0 1)
      = ∫ y, (gg (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          - (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
            * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y))
        ∂(gaussianReal 0 1) := by
    have hsplit : ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          * (-(Real.exp (-t)) * x
            + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y)
          ∂(gaussianReal 0 1)
        = -(Real.exp (-t) * x)
            * ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
              ∂(gaussianReal 0 1)
          + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t)))
            * ∫ y, y * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
              ∂(gaussianReal 0 1) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring
      · exact hint3'.const_mul _
      · exact hint4'.const_mul _
    have hsplit2 : ∫ y, (gg (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          - (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
            * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y))
          ∂(gaussianReal 0 1)
        = ∫ y, gg (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
            ∂(gaussianReal 0 1)
          - ∫ y, (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
            * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
            ∂(gaussianReal 0 1) := by
      rw [integral_sub]
      · exact hint5'
      · refine ((hint3'.const_mul (Real.exp (-t) * x)).add
          (hint4'.const_mul (Real.sqrt (1 - Real.exp (-2 * t))))).congr ?_
        filter_upwards with y
        simp only [Pi.add_apply]
        ring
    have hsplit3 : ∫ y, (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          ∂(gaussianReal 0 1)
        = (Real.exp (-t) * x)
            * ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
              ∂(gaussianReal 0 1)
          + Real.sqrt (1 - Real.exp (-2 * t))
            * ∫ y, y * g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
              ∂(gaussianReal 0 1) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring
      · exact hint3'.const_mul _
      · exact hint4'.const_mul _
    rw [hsplit, hsplit2, hsplit3, h1]
    have hbne : Real.sqrt (1 - Real.exp (-2 * t)) ≠ 0 := ne_of_gt hbpos
    set A := ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
      ∂(gaussianReal 0 1) with hA
    set B := ∫ y, gg (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
      ∂(gaussianReal 0 1) with hB
    set c := Real.sqrt (1 - Real.exp (-2 * t)) with hc
    have hc2 : c ^ 2 = 1 - Real.exp (-2 * t) := hb2
    have hcne : c ≠ 0 := hbne
    field_simp
    rw [hc2]
    ring
  rw [hkey] at htime
  exact htime

/-- **The generator/heat equation** `∂_t P_t f = L P_t f`, for smooth compactly supported `f`.
This is the named open input: it packages the heat equation together with the two weighted
integrations by parts and the `Γ₂` identity, which are the missing Mathlib layer recorded in
`scratch/pk/glogsobolev-route.md`. -/
def OUHeatEquation : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
    ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun s => ouSemigroup s f x) (ouGenerator (ouSemigroup t f) x) t

end

end LatticeProb

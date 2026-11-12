/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatSqMarkov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatDens
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
(task P2-KHSQ3, target `killedHeat_sqOpen`)

For a planar Brownian motion `B` and `s ≤ t`, the increment `B_t − B_s` is independent of the
past `(B_r)_{r ≤ s}` and has independent `N(0, t − s)` coordinates. Since
`E[cos(α N(0,v))] = e^{−α² v/2}` and `E[sin(α N(0,v))] = 0` (mathlib `charFun_gaussianReal`),
the Dirichlet sine modes `φ_p` of the square `(a, a+L)²` satisfy, for every bounded measurable
functional `G` of the past,

  `E[G · φ_p(z + B_t)] = e^{−λ_p (t−s)/2} E[G · φ_p(z + B_s)]`
  (`KilledHeatSq.integral_mul_sqMode_eq`),

i.e. `e^{λ_p s/2} φ_p(z + B_s)` is a martingale (`λ_p = π²(j²+k²)/L²`). This is the
space-time harmonic function used in the classical proof that the killed heat kernel of an
interval/rectangle is its sine (eigenfunction) series (Feller II §X.5; Karatzas–Shreve,
*Brownian Motion and Stochastic Calculus*, Problem 2.8.8 and §4.3 (optional stopping for the
heat equation)). Standard Gaussian computation; own elementary proof.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeatSq

open KilledHeat HeatSq Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-- The coordinates of `B` at the times `r i` (in use: `r i ≤ s`). -/
def pastVec {ι : Type*} (B : ℝ≥0 → Ω → ℂ) (r : ι → ℝ≥0) (ω : Ω) : Bool × ι → ℝ :=
  fun i ↦ coordProc B (i.1, r i.2) ω

/-- The coordinates of the increment `B_t − B_s`. -/
def incVec (B : ℝ≥0 → Ω → ℂ) (s t : ℝ≥0) (ω : Ω) : Bool → ℝ :=
  fun b ↦ coordProc B (b, t) ω - coordProc B (b, s) ω

lemma memLp_coordProc (hB : IsPlanarBM B P) (p : Bool × ℝ≥0) : MemLp (coordProc B p) 2 P :=
  (hB.gauss.hasGaussianLaw_eval p).memLp_two

lemma cov_coord_inc (hB : IsPlanarBM B P) {s t : ℝ≥0} (hst : s ≤ t) (p : Bool × ℝ≥0)
    (hp : p.2 ≤ s) (b : Bool) :
    cov[coordProc B p, fun ω ↦ coordProc B (b, t) ω - coordProc B (b, s) ω; P] = 0 := by
  have := hB.gauss.isProbabilityMeasure
  rw [covariance_fun_sub_right (memLp_coordProc hB _) (memLp_coordProc hB _)
    (memLp_coordProc hB _), hB.cov, hB.cov]
  split_ifs <;> simp [min_eq_left hp, min_eq_left (hp.trans hst)]

lemma isGaussianProcess_past_inc {ι : Type*} (hB : IsPlanarBM B P) (r : ι → ℝ≥0) (s t : ℝ≥0) :
    IsGaussianProcess (Sum.elim (fun (i : Bool × ι) ↦ coordProc B (i.1, r i.2))
      (fun b : Bool ↦ fun ω ↦ coordProc B (b, t) ω - coordProc B (b, s) ω)) P := by
  classical
  refine hB.gauss.of_isGaussianProcess fun i ↦ ?_
  rcases i with i | b
  · exact ⟨{(i.1, r i.2)}, ContinuousLinearMap.proj ⟨(i.1, r i.2), by simp⟩, fun ω ↦ rfl⟩
  · refine ⟨{(b, t), (b, s)}, (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ({(b, t), (b, s)} : Finset (Bool × ℝ≥0)) ↦ ℝ) ⟨(b, t), by simp⟩) -
      ContinuousLinearMap.proj ⟨(b, s), by simp⟩, fun ω ↦ ?_⟩
    simp

/-- The increment `B_t − B_s` is independent of the past `(B_r)_{r ≤ s}`. -/
lemma indepFun_past_inc {ι : Type*} (hB : IsPlanarBM B P) {r : ι → ℝ≥0} {s t : ℝ≥0}
    (hr : ∀ i, r i ≤ s) (hst : s ≤ t) :
    IndepFun (pastVec B r) (incVec B s t) P := by
  have hG := isGaussianProcess_past_inc hB r s t
  exact hG.indepFun_of_covariance_eq_zero (fun i ↦ hG.aemeasurable (Sum.inl i))
    (fun b ↦ hG.aemeasurable (Sum.inr b)) (fun i b ↦ cov_coord_inc hB hst _ (hr i.2) b)

lemma cov_inc_inc (hB : IsPlanarBM B P) {s t : ℝ≥0} (hst : s ≤ t) (b b' : Bool) :
    cov[fun ω ↦ incVec B s t ω b, fun ω ↦ incVec B s t ω b'; P] =
      if b = b' then ((t : ℝ) - s) else 0 := by
  have := hB.gauss.isProbabilityMeasure
  have h := memLp_coordProc hB
  simp only [incVec]
  show cov[coordProc B (b, t) - coordProc B (b, s), coordProc B (b', t) - coordProc B (b', s); P] = _
  rw [covariance_sub_left (h _) (h _) ((h _).sub (h _)),
    covariance_sub_right (h _) (h _) (h _), covariance_sub_right (h _) (h _) (h _),
    hB.cov, hB.cov, hB.cov, hB.cov]
  simp only [min_self, min_eq_right hst, min_eq_left hst]
  split_ifs <;> ring

/-- The two increment coordinates are independent. -/
lemma indepFun_inc_coords (hB : IsPlanarBM B P) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω ↦ incVec B s t ω false) (fun ω ↦ incVec B s t ω true) P := by
  have hG0 := isGaussianProcess_past_inc hB (fun _ : Unit ↦ s) s t
  have hG : IsGaussianProcess (Sum.elim (fun _ : Unit ↦ fun ω ↦ incVec B s t ω false)
      (fun _ : Unit ↦ fun ω ↦ incVec B s t ω true)) P := by
    have e : Sum.elim (fun _ : Unit ↦ fun ω ↦ incVec B s t ω false)
        (fun _ : Unit ↦ fun ω ↦ incVec B s t ω true) =
        Sum.elim (fun (i : Bool × Unit) ↦ coordProc B (i.1, (fun _ : Unit ↦ s) i.2))
          (fun b : Bool ↦ fun ω ↦ coordProc B (b, t) ω - coordProc B (b, s) ω) ∘
          Sum.elim (fun _ : Unit ↦ Sum.inr false) (fun _ : Unit ↦ Sum.inr true) := by
      funext i
      rcases i with _ | _ <;> rfl
    rw [e]
    exact hG0.comp_right _
  have h := hG.indepFun_of_covariance_eq_zero (fun _ ↦ hG0.aemeasurable (Sum.inr _))
    (fun _ ↦ hG0.aemeasurable (Sum.inr _)) (fun _ _ ↦ by rw [cov_inc_inc hB hst]; simp)
  exact h.comp (measurable_pi_apply ()) (measurable_pi_apply ())

/-- Each increment coordinate is `N(0, t − s)`. -/
lemma hasLaw_inc (hB : IsPlanarBM B P) {s t : ℝ≥0} (hst : s ≤ t) (b : Bool) :
    HasLaw (fun ω ↦ incVec B s t ω b) (gaussianReal 0 (t - s)) P := by
  have := hB.gauss.isProbabilityMeasure
  have hG0 := isGaussianProcess_past_inc hB (fun _ : Unit ↦ s) s t
  have hG := hG0.hasGaussianLaw_eval (Sum.inr b)
  have hm : AEMeasurable (fun ω ↦ incVec B s t ω b) P := hG0.aemeasurable (Sum.inr b)
  refine ⟨hm, ?_⟩
  have h1 : ∫ ω, coordProc B (b, t) ω - coordProc B (b, s) ω ∂P = 0 := by
    rw [integral_sub ((memLp_coordProc hB _).integrable one_le_two)
      ((memLp_coordProc hB _).integrable one_le_two), hB.mean, hB.mean, sub_zero]
  have h2 := hG.map_eq_gaussianReal
  simp only [Sum.elim_inr] at h2
  change P.map (fun ω ↦ incVec B s t ω b) = _ at h2
  have h3 := cov_inc_inc hB hst b b
  simp only [incVec, if_pos rfl] at h3 hm
  rw [h2, h1, ← covariance_self hm, h3, if_pos trivial]
  first
  | rw [Real.toNNReal_coe]
  | rw [← NNReal.coe_sub hst, Real.toNNReal_coe]

/-- `E[cos(α V)] = e^{−vα²/2}` and `E[sin(α V)] = 0` for `V ∼ N(0, v)` (real and imaginary
parts of mathlib's `charFun_gaussianReal`). -/
lemma integral_cos_sin_of_hasLaw {V : Ω → ℝ} {v : ℝ≥0} (hV : HasLaw V (gaussianReal 0 v) P)
    (α : ℝ) : ∫ ω, Real.cos (α * V ω) ∂P = Real.exp (-(v * α ^ 2 / 2)) ∧
      ∫ ω, Real.sin (α * V ω) ∂P = 0 := by
  have hc := charFun_gaussianReal (μ := 0) (v := v) α
  rw [charFun_apply_real] at hc
  have he : ∀ x : ℝ, Complex.exp (α * x * Complex.I) = Complex.exp (((α * x : ℝ) : ℂ) * Complex.I) :=
    fun x ↦ by push_cast; ring_nf
  have hint : Integrable (fun x : ℝ ↦ Complex.exp (α * x * Complex.I)) (gaussianReal 0 v) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hre := integral_re hint
  have him := integral_im hint
  rw [hc] at hre him
  have hr : (α : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - (v : ℝ) * (α : ℂ) ^ 2 / 2 =
      ((-(v * α ^ 2 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [hr] at hre him
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, he, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_re, Complex.exp_ofReal_im] at hre him
  have hcm : AEStronglyMeasurable (fun x : ℝ ↦ Real.cos (α * x)) (gaussianReal 0 v) := by fun_prop
  have hsm : AEStronglyMeasurable (fun x : ℝ ↦ Real.sin (α * x)) (gaussianReal 0 v) := by fun_prop
  refine ⟨?_, ?_⟩
  · rw [← hre]
    exact hV.integral_comp hcm
  · rw [← him]
    exact hV.integral_comp hsm

lemma aemeasurable_pastVec {ι : Type*} [Countable ι] (hB : IsPlanarBM B P) (r : ι → ℝ≥0) :
    AEMeasurable (pastVec B r) P :=
  AEMeasurable.of_eval fun _ ↦ hB.gauss.aemeasurable _

lemma aemeasurable_incVec (hB : IsPlanarBM B P) (s t : ℝ≥0) :
    AEMeasurable (incVec B s t) P :=
  AEMeasurable.of_eval fun _ ↦ (hB.gauss.aemeasurable _).sub (hB.gauss.aemeasurable _)

/-- Functions of the past and of the increment factorize. -/
lemma integral_past_mul_inc {ι : Type*} [Countable ι] (hB : IsPlanarBM B P) {r : ι → ℝ≥0}
    {s t : ℝ≥0} (hr : ∀ i, r i ≤ s) (hst : s ≤ t)
    {F : (Bool × ι → ℝ) → ℝ} {H : (Bool → ℝ) → ℝ} (hF : Measurable F)
    (hH : Measurable H) :
    ∫ ω, F (pastVec B r ω) * H (incVec B s t ω) ∂P =
      (∫ ω, F (pastVec B r ω) ∂P) * ∫ ω, H (incVec B s t ω) ∂P :=
  (indepFun_past_inc hB hr hst).integral_comp_mul_comp (aemeasurable_pastVec hB r)
    (aemeasurable_incVec hB s t) hF.aestronglyMeasurable hH.aestronglyMeasurable

/-- Functions of the two increment coordinates factorize. -/
lemma integral_inc_mul (hB : IsPlanarBM B P) {s t : ℝ≥0} (hst : s ≤ t) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    ∫ ω, f (incVec B s t ω false) * g (incVec B s t ω true) ∂P =
      (∫ ω, f (incVec B s t ω false) ∂P) * ∫ ω, g (incVec B s t ω true) ∂P :=
  (indepFun_inc_coords hB hst).integral_comp_mul_comp
    ((hB.gauss.aemeasurable _).sub (hB.gauss.aemeasurable _))
    ((hB.gauss.aemeasurable _).sub (hB.gauss.aemeasurable _))
    hf.aestronglyMeasurable hg.aestronglyMeasurable

lemma integrable_term {ι : Type*} [Countable ι] (hB : IsPlanarBM B P) (r : ι → ℝ≥0) {s t : ℝ≥0}
    {F : (Bool × ι → ℝ) → ℝ} {H : (Bool → ℝ) → ℝ} (hF : Measurable F)
    (hH : Measurable H) {C : ℝ} (hFb : ∀ y, |F y| ≤ C) (hHb : ∀ d, |H d| ≤ 1) :
    Integrable (fun ω ↦ F (pastVec B r ω) * H (incVec B s t ω)) P := by
  have := hB.gauss.isProbabilityMeasure
  refine (integrable_const C).mono'
    ((hF.comp_aemeasurable (aemeasurable_pastVec hB r)).mul
      (hH.comp_aemeasurable (aemeasurable_incVec hB s t))).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h0 : 0 ≤ C := (abs_nonneg _).trans (hFb (pastVec B r ω))
  calc |F (pastVec B r ω)| * |H (incVec B s t ω)| ≤ C * 1 :=
        mul_le_mul (hFb _) (hHb _) (abs_nonneg _) h0
    _ = C := mul_one C

lemma abs_trig_mul_le (u v : ℝ) (f g : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    |f u * g v| ≤ 1 := by
  rw [abs_mul]
  calc |f u| * |g v| ≤ 1 * 1 := mul_le_mul (hf u) (hg v) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma abs_G_trig_le {C g u v : ℝ} (hg : |g| ≤ C) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |g * (u * v)| ≤ C := by
  rw [abs_mul, abs_mul]
  have h0 : 0 ≤ C := (abs_nonneg _).trans hg
  calc |g| * (|u| * |v|) ≤ C * (1 * 1) :=
        mul_le_mul hg (mul_le_mul hu hv (abs_nonneg _) zero_le_one) (by positivity) h0
    _ = C := by ring

/-- **Markov step for the sine modes**: `E[G · φ_p(z + B_t)] = e^{−λ_p(t−s)/2} E[G · φ_p(z + B_s)]`
for every bounded measurable functional `G` of `(B_r)_{r ≤ s}`. -/
theorem integral_mul_sqMode_eq {ι : Type*} [Countable ι] (hB : IsPlanarBM B P) {r : ι → ℝ≥0}
    {s t : ℝ≥0} (hr : ∀ i, r i ≤ s) {i0 : ι} (hi0 : r i0 = s) (hst : s ≤ t) (a L : ℝ)
    (p : ℕ × ℕ) (z : ℂ) {G : (Bool × ι → ℝ) → ℝ} (hG : Measurable G)
    {C : ℝ} (hGb : ∀ y, |G y| ≤ C) :
    ∫ ω, G (pastVec B r ω) * sqMode a L p (z + B t ω) ∂P =
      sqDecay L ((t - s : ℝ≥0) : ℝ) p *
        ∫ ω, G (pastVec B r ω) * sqMode a L p (z + B s ω) ∂P := by
  have := hB.gauss.isProbabilityMeasure
  set α : ℝ := π * p.1 / L with hα
  set β : ℝ := π * p.2 / L with hβ
  let θ1 : (Bool × ι → ℝ) → ℝ := fun y ↦ π * p.1 * (z.re + y (false, i0) - a) / L
  let θ2 : (Bool × ι → ℝ) → ℝ := fun y ↦ π * p.2 * (z.im + y (true, i0) - a) / L
  have hθ1 : Measurable θ1 := by fun_prop
  have hθ2 : Measurable θ2 := by fun_prop
  have h1 : ∀ ω, π * p.1 * ((z + B t ω).re - a) / L =
      θ1 (pastVec B r ω) + α * incVec B s t ω false := by
    intro ω
    simp only [θ1, hα, pastVec, incVec, coordProc, hi0, Complex.add_re, Bool.false_eq_true,
      ite_false]
    ring
  have h2 : ∀ ω, π * p.2 * ((z + B t ω).im - a) / L =
      θ2 (pastVec B r ω) + β * incVec B s t ω true := by
    intro ω
    simp only [θ2, hβ, pastVec, incVec, coordProc, hi0, Complex.add_im, ite_true]
    ring
  have h3 : ∀ ω, sqMode a L p (z + B s ω) =
      Real.sin (θ1 (pastVec B r ω)) * Real.sin (θ2 (pastVec B r ω)) := by
    intro ω
    simp only [sqMode, sinMode, θ1, θ2, pastVec, coordProc, hi0, Complex.add_re, Complex.add_im,
      Bool.false_eq_true, ite_false, ite_true]
  have hexp : (fun ω ↦ G (pastVec B r ω) * sqMode a L p (z + B t ω)) = fun ω ↦
      ((G (pastVec B r ω) * (Real.sin (θ1 (pastVec B r ω)) * Real.sin (θ2 (pastVec B r ω)))) *
        (Real.cos (α * incVec B s t ω false) * Real.cos (β * incVec B s t ω true)) +
      (G (pastVec B r ω) * (Real.sin (θ1 (pastVec B r ω)) * Real.cos (θ2 (pastVec B r ω)))) *
        (Real.cos (α * incVec B s t ω false) * Real.sin (β * incVec B s t ω true))) +
      ((G (pastVec B r ω) * (Real.cos (θ1 (pastVec B r ω)) * Real.sin (θ2 (pastVec B r ω)))) *
        (Real.sin (α * incVec B s t ω false) * Real.cos (β * incVec B s t ω true)) +
      (G (pastVec B r ω) * (Real.cos (θ1 (pastVec B r ω)) * Real.cos (θ2 (pastVec B r ω)))) *
        (Real.sin (α * incVec B s t ω false) * Real.sin (β * incVec B s t ω true))) := by
    funext ω
    simp only [sqMode, sinMode, h1, h2, Real.sin_add]
    ring
  have hsin := Real.abs_sin_le_one
  have hcos := Real.abs_cos_le_one
  have I1 := integrable_term hB r (s := s) (t := t) (hG.mul ((hθ1.sin).mul (hθ2.sin)))
    (H := fun d ↦ Real.cos (α * d false) * Real.cos (β * d true)) (by fun_prop)
    (fun y ↦ abs_G_trig_le (hGb y) (hsin _) (hsin _)) (fun d ↦ abs_trig_mul_le _ _ _ _ hcos hcos)
  have I2 := integrable_term hB r (s := s) (t := t) (hG.mul ((hθ1.sin).mul (hθ2.cos)))
    (H := fun d ↦ Real.cos (α * d false) * Real.sin (β * d true)) (by fun_prop)
    (fun y ↦ abs_G_trig_le (hGb y) (hsin _) (hcos _)) (fun d ↦ abs_trig_mul_le _ _ _ _ hcos hsin)
  have I3 := integrable_term hB r (s := s) (t := t) (hG.mul ((hθ1.cos).mul (hθ2.sin)))
    (H := fun d ↦ Real.sin (α * d false) * Real.cos (β * d true)) (by fun_prop)
    (fun y ↦ abs_G_trig_le (hGb y) (hcos _) (hsin _)) (fun d ↦ abs_trig_mul_le _ _ _ _ hsin hcos)
  have I4 := integrable_term hB r (s := s) (t := t) (hG.mul ((hθ1.cos).mul (hθ2.cos)))
    (H := fun d ↦ Real.sin (α * d false) * Real.sin (β * d true)) (by fun_prop)
    (fun y ↦ abs_G_trig_le (hGb y) (hcos _) (hcos _)) (fun d ↦ abs_trig_mul_le _ _ _ _ hsin hsin)
  simp only [Pi.mul_apply] at I1 I2 I3 I4
  have e0 := integral_add (I1.add I2) (I3.add I4)
  have e12 := integral_add I1 I2
  have e34 := integral_add I3 I4
  simp only [Pi.add_apply] at e0 e12 e34
  rw [hexp, e0, e12, e34]
  have E1 := integral_past_mul_inc hB hr hst (hG.mul ((hθ1.sin).mul (hθ2.sin)))
    (H := fun d ↦ Real.cos (α * d false) * Real.cos (β * d true)) (by fun_prop)
  have E2 := integral_past_mul_inc hB hr hst (hG.mul ((hθ1.sin).mul (hθ2.cos)))
    (H := fun d ↦ Real.cos (α * d false) * Real.sin (β * d true)) (by fun_prop)
  have E3 := integral_past_mul_inc hB hr hst (hG.mul ((hθ1.cos).mul (hθ2.sin)))
    (H := fun d ↦ Real.sin (α * d false) * Real.cos (β * d true)) (by fun_prop)
  have E4 := integral_past_mul_inc hB hr hst (hG.mul ((hθ1.cos).mul (hθ2.cos)))
    (H := fun d ↦ Real.sin (α * d false) * Real.sin (β * d true)) (by fun_prop)
  simp only [Pi.mul_apply] at E1 E2 E3 E4
  have F1 := integral_inc_mul hB hst (f := fun x ↦ Real.cos (α * x))
    (g := fun x ↦ Real.cos (β * x)) (by fun_prop) (by fun_prop)
  have F2 := integral_inc_mul hB hst (f := fun x ↦ Real.cos (α * x))
    (g := fun x ↦ Real.sin (β * x)) (by fun_prop) (by fun_prop)
  have F3 := integral_inc_mul hB hst (f := fun x ↦ Real.sin (α * x))
    (g := fun x ↦ Real.cos (β * x)) (by fun_prop) (by fun_prop)
  have F4 := integral_inc_mul hB hst (f := fun x ↦ Real.sin (α * x))
    (g := fun x ↦ Real.sin (β * x)) (by fun_prop) (by fun_prop)
  rw [E1, E2, E3, E4, F1, F2, F3, F4]
  obtain ⟨cf, sf⟩ := integral_cos_sin_of_hasLaw (hasLaw_inc hB hst false) α
  obtain ⟨ct, st⟩ := integral_cos_sin_of_hasLaw (hasLaw_inc hB hst true) β
  rw [cf, sf, ct, st]
  have h3' : (fun ω ↦ G (pastVec B r ω) * sqMode a L p (z + B s ω)) = fun ω ↦
      G (pastVec B r ω) * (Real.sin (θ1 (pastVec B r ω)) * Real.sin (θ2 (pastVec B r ω))) := by
    funext ω
    rw [h3]
  rw [h3']
  have hd : sqDecay L ((t - s : ℝ≥0) : ℝ) p =
      Real.exp (-(((t - s : ℝ≥0) : ℝ) * α ^ 2 / 2)) * Real.exp (-(((t - s : ℝ≥0) : ℝ) * β ^ 2 / 2)) := by
    simp only [sqDecay, modeDecay, hα, hβ]
    congr 1 <;> congr 1 <;> ring
  rw [hd]
  ring

end KilledHeatSq
end LQGMetric

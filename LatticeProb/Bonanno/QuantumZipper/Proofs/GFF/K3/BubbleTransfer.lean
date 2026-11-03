/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.BubbleTransfer at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.BubbleCutoff
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.BubbleHardy
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Thickening

/-!
# K3-BUB3: transfer of test functions from `D` to `Ω` through a closing gate

Blueprint: `blueprint/EXT_PP_BLUEPRINT.md` §B, node **BUB-3** (the gate lemma that replaces the
Dirichlet stability `C4`; DECISIONS D8). Given an open `D ⊆ H`, an open `Ω ⊆ D` whose frontier
inside `D` lies in a small ball `B(p, r)`, and the sphere condition `hfat` for the unbounded
component `D` (spheres of radius in `(2r, R)` always meet `ℂ \ D`), every test function
`f ∈ zeroSpace D` transfers to `f' ∈ zeroSpace Ω` whose pairing against a fixed bounded
measurable `g` supported in `Ω` differs by at most
`M √(π R² · 2R(|Im p| + R) · 2π) √(E_D(f))`, while its Dirichlet energy grows at most by the
factor `1 + ε₁ r R`.

The construction is `f' := (χ f) · 1_Ω` with `χ` the logarithmic cutoff of BUB-2
(`BubbleCutoff.lean`, `exists_logCutoff`) around `p`. Smoothness and support of `f'` in `Ω` use
that `χ f` vanishes near `frontier Ω`: near `frontier Ω ∩ D ⊆ closedBall p r` because `χ = 0`
on `closedBall p (2r)`, and near `frontier Ω \ D` because `tsupport f` is a compact subset of
the open set `D`. The pairing error is supported in `B(p, R) ∩ Ω`, and Cauchy–Schwarz together
with the vertical Poincaré inequality `integral_sq_ball_le` (BUB-2) bounds it. For the energy we
use the product rule `∇(χf) = χ ∇f + f ∇χ` with `|χ| ≤ 1`, Young's inequality
`‖a + b‖² ≤ (1+δ)‖a‖² + (1+δ⁻¹)‖b‖²`, the gradient bound of BUB-2, and Hardy's inequality
`hardy_annulus` (BUB-1) on the annulus `2r < ‖x - p‖ < R`, which applies because `f = 0` off `D`
and `hfat` supplies a zero of `f` on every sphere of radius in `(2r, R)`.

Route: EXT_PP §B (own argument; the gate lemma replacing Dirichlet stability, DECISIONS D8).
Two technical additions are elementary and are proved here: `∇χ = 0` off the *closed* annulus
(the blueprint uses only the support of `f²‖∇χ‖²`; on the two boundary spheres we apply
Fermat's theorem to the global minimum / maximum of `χ`), and Cauchy–Schwarz on a ball
("own elementary proof").
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal

namespace QuantumZipper.K3

/-! ## The constant `ε₁` -/

/-- The energy factor `ε₁ r R` of EXT_PP §B, BUB-3:
`δ + (1 + δ⁻¹) * 4 * π² * K₀² / log (R / (2r))²` with `δ := 1 / log (R / (2r))` and
`K₀ = logCutoffConst` (the constant actually provided by BUB-2). -/
def eps1 (r R : ℝ) : ℝ :=
  1 / Real.log (R / (2 * r)) +
    (1 + (1 / Real.log (R / (2 * r)))⁻¹) * 4 * Real.pi ^ 2 * logCutoffConst ^ 2 /
      Real.log (R / (2 * r)) ^ 2

/-- `ε₁` in terms of the window length `L = log (R / (2r))`. -/
lemma eps1_eq (r R L : ℝ) (hL : Real.log (R / (2 * r)) = L) :
    eps1 r R = 1 / L + (1 + (1 / L)⁻¹) * 4 * Real.pi ^ 2 * logCutoffConst ^ 2 / L ^ 2 := by
  rw [eps1, hL]

/-! ## The gradient of the logarithmic cutoff vanishes off the open annulus -/

/-- **BUB-3, geometric input.** The logarithmic cutoff of BUB-2 has vanishing gradient off the
open annulus `2r < ‖x - p‖ < R`: it is locally `0` inside `B(p, 2r)` and locally `1` outside
`B(p, R)`, while on the two boundary spheres it is a global minimum (resp. maximum), so
Fermat's theorem gives `∇χ = 0` there as well. (Own elementary proof; EXT_PP §B uses only the
resulting support restriction for `f²‖∇χ‖²`.) -/
lemma bubbleTransfer_fderiv_logCutoff_eq_zero (p : ℂ) {r R : ℝ} (hr : 0 < r) (h2rR : 2 * r < R)
    {x : ℂ} (hx : ¬ (2 * r < ‖x - p‖ ∧ ‖x - p‖ < R)) :
    fderiv ℝ (logCutoff p r R) x = 0 := by
  rcases lt_trichotomy ‖x - p‖ (2 * r) with h | h | h
  · -- inside the ball of radius `2r`: `χ` is locally `0`
    have hev : logCutoff p r R =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds x (show (0 : ℝ) < 2 * r - ‖x - p‖ by linarith)]
        with y hy
      rw [Metric.mem_ball, Complex.dist_eq] at hy
      have h2 : ‖y - p‖ ≤ 2 * r := by
        have h3 : ‖y - p‖ ≤ ‖y - x‖ + ‖x - p‖ := by
          have h4 := norm_add_le (y - x) (x - p)
          rwa [show (y - x) + (x - p) = y - p by ring] at h4
        linarith
      exact bubbleCutoff_logCutoff_eq_zero p hr h2rR h2
    rw [hev.fderiv_eq]
    simp
  · -- on the sphere `‖x - p‖ = 2r`: global minimum of `χ`
    have hmin : IsLocalMin (logCutoff p r R) x :=
      Eventually.of_forall fun y => by
        have hx0 : logCutoff p r R x = 0 := bubbleCutoff_logCutoff_eq_zero p hr h2rR h.le
        rw [hx0]
        exact (bubbleCutoff_logCutoff_mem_Icc p r R y).1
    rw [hmin.fderiv_eq_zero]
  · rcases lt_trichotomy ‖x - p‖ R with h' | h' | h'
    · exact absurd ⟨h, h'⟩ hx
    · -- on the sphere `‖x - p‖ = R`: global maximum of `χ`
      have hmax : IsLocalMax (logCutoff p r R) x :=
        Eventually.of_forall fun y => by
          have hx1 : logCutoff p r R x = 1 :=
            bubbleCutoff_logCutoff_eq_one p hr h2rR h'.symm.le
          rw [hx1]
          exact (bubbleCutoff_logCutoff_mem_Icc p r R y).2
      rw [hmax.fderiv_eq_zero]
    · -- outside the ball of radius `R`: `χ` is locally `1`
      have hev : logCutoff p r R =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Metric.ball_mem_nhds x (show (0 : ℝ) < ‖x - p‖ - R by linarith)]
          with y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        have hRy : R ≤ ‖y - p‖ := by
          have h3 : ‖x - p‖ ≤ ‖y - p‖ + ‖y - x‖ := by
            have h4 : ‖x - p‖ ≤ ‖y - p‖ + ‖x - y‖ := by
              have h6 := norm_add_le (y - p) (x - y)
              rwa [show (y - p) + (x - y) = x - p by ring] at h6
            simpa [norm_sub_rev] using h4
          linarith
        exact bubbleCutoff_logCutoff_eq_one p hr h2rR hRy
      rw [hev.fderiv_eq]
      simp

/-! ## Two elementary inequalities -/

/-- Young's inequality in the form used for the product rule: `(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²`
for `δ > 0` (own elementary proof). -/
lemma bubbleTransfer_sq_add_le (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (a + b) ^ 2 ≤ (1 + δ) * a ^ 2 + (1 + δ⁻¹) * b ^ 2 := by
  have h2 : 0 ≤ δ ^ 2 * a ^ 2 - 2 * δ * a * b + b ^ 2 := by
    nlinarith [sq_nonneg (δ * a - b)]
  have h3 : 2 * a * b * δ ≤ δ ^ 2 * a ^ 2 + b ^ 2 := by linarith
  have h4 : 2 * a * b ≤ (δ ^ 2 * a ^ 2 + b ^ 2) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have h5 : (δ ^ 2 * a ^ 2 + b ^ 2) / δ = δ * a ^ 2 + b ^ 2 / δ := by
    field_simp
  have key : 2 * a * b ≤ δ * a ^ 2 + b ^ 2 / δ := by linarith
  rw [div_eq_mul_inv] at key
  nlinarith [key, sq_nonneg a, sq_nonneg b]

/-- **Product rule bound.** For smooth `χ, f : ℂ → ℝ` with `χ x ∈ [0,1]`,
`‖∇(χf)(x)‖² ≤ (1+δ)‖∇f(x)‖² + (1+δ⁻¹) f(x)²‖∇χ(x)‖²` (own elementary proof). -/
lemma bubbleTransfer_fderiv_mul_sq_le {χ f : ℂ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hχx : χ x ∈ Set.Icc 0 1) :
    ‖fderiv ℝ (fun y => χ y * f y) x‖ ^ 2 ≤
      (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2) := by
  have hder : fderiv ℝ (fun y => χ y * f y) x
      = χ x • fderiv ℝ f x + f x • fderiv ℝ χ x :=
    fderiv_fun_mul (hχ.differentiable smooth_ne_zero).differentiableAt
      (hf.differentiable smooth_ne_zero).differentiableAt
  have hnorm : ‖fderiv ℝ (fun y => χ y * f y) x‖
      ≤ ‖χ x‖ * ‖fderiv ℝ f x‖ + |f x| * ‖fderiv ℝ χ x‖ := by
    rw [hder]
    calc ‖χ x • fderiv ℝ f x + f x • fderiv ℝ χ x‖
        ≤ ‖χ x • fderiv ℝ f x‖ + ‖f x • fderiv ℝ χ x‖ := norm_add_le _ _
      _ = ‖χ x‖ * ‖fderiv ℝ f x‖ + |f x| * ‖fderiv ℝ χ x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hχ1 : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hχx.1], by linarith [hχx.2]⟩
  have hχ1' : ‖χ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (χ x), hχ1]
  calc ‖fderiv ℝ (fun y => χ y * f y) x‖ ^ 2
      ≤ (‖χ x‖ * ‖fderiv ℝ f x‖ + |f x| * ‖fderiv ℝ χ x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg (fderiv ℝ (fun y => χ y * f y) x)) hnorm 2
    _ ≤ (1 + δ) * (‖χ x‖ * ‖fderiv ℝ f x‖) ^ 2
          + (1 + δ⁻¹) * (|f x| * ‖fderiv ℝ χ x‖) ^ 2 := bubbleTransfer_sq_add_le _ _ hδ
    _ ≤ (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2) := by
        have h1 : ‖χ x‖ ^ 2 * ‖fderiv ℝ f x‖ ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 :=
          mul_le_of_le_one_left (sq_nonneg _) hχ1'
        have h2 : (1 + δ) * (‖χ x‖ ^ 2 * ‖fderiv ℝ f x‖ ^ 2)
            ≤ (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        have h3 : (1 + δ⁻¹) * (|f x| ^ 2 * ‖fderiv ℝ χ x‖ ^ 2)
            = (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2) := by rw [sq_abs]
        rw [mul_pow, mul_pow, h3]
        exact add_le_add h2 le_rfl

/-! ## Cauchy–Schwarz on a ball -/

/-- `B(p, R)` has finite volume (own elementary proof from `Complex.volume_ball`). -/
lemma bubbleTransfer_volume_ball_lt_top (p : ℂ) (R : ℝ) : volume (Metric.ball p R) < ∞ := by
  rw [Complex.volume_ball]
  refine ENNReal.mul_lt_top ?_ (by simp)
  rw [sq]
  exact ENNReal.mul_lt_top (by simp) (by simp)

/-- `closedBall p R` has finite volume (own elementary proof from `Complex.volume_closedBall`). -/
lemma bubbleTransfer_volume_closedBall_lt_top (p : ℂ) (R : ℝ) :
    volume (Metric.closedBall p R) < ∞ := by
  rw [Complex.volume_closedBall]
  refine ENNReal.mul_lt_top ?_ (by simp)
  rw [sq]
  exact ENNReal.mul_lt_top (by simp) (by simp)

/-- **Cauchy–Schwarz on a ball**, via Hölder's inequality in mathlib
(`integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2`): `(∫_B |f|)² ≤ vol(B) ∫_B f²`. -/
lemma bubbleTransfer_integral_abs_sq_le {f : ℂ → ℝ} (hcont : Continuous f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) {p : ℂ} {R : ℝ} (hR : 0 < R) :
    (∫ x in Metric.ball p R, |f x|) ^ 2 ≤
      (R ^ 2 * Real.pi) * ∫ x in Metric.ball p R, f x ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball p R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact bubbleTransfer_volume_ball_lt_top p R⟩
  have hvol : (volume (Metric.ball p R)).toReal = R ^ 2 * Real.pi := by
    rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hR.le]
    norm_num [NNReal.coe_real_pi]
  have hf2 : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (volume.restrict (Metric.ball p R)) :=
    MemLp.of_bound hcont.abs.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hC x)
  have hg2 : MemLp (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal 2)
      (volume.restrict (Metric.ball p R)) := memLp_const 1
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Metric.ball p R))
    (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Eventually.of_forall fun x => abs_nonneg (f x)) (Eventually.of_forall fun _ => zero_le_one)
    hf2 hg2
  have h1b : (∫ x in Metric.ball p R, (1 : ℝ) ^ 2) = R ^ 2 * Real.pi := by
    rw [one_pow, integral_const, Measure.real_def, Measure.restrict_apply_univ, hvol]
    simp
  have hCS'' : ∫ x in Metric.ball p R, |f x| ≤
      (∫ x in Metric.ball p R, |f x| ^ 2) ^ (1 / 2 : ℝ) * (R ^ 2 * Real.pi) ^ (1 / 2 : ℝ) := by
    simpa [mul_one, h1b, Measure.real_def, hvol, ENNReal.toReal_ofReal hR.le] using hCS
  have hCS' : ∫ x in Metric.ball p R, |f x| ≤
      Real.sqrt (∫ x in Metric.ball p R, f x ^ 2) * Real.sqrt (R ^ 2 * Real.pi) := by
    simpa only [sq_abs, ← Real.sqrt_eq_rpow] using hCS''
  calc (∫ x in Metric.ball p R, |f x|) ^ 2
      ≤ (Real.sqrt (∫ x in Metric.ball p R, f x ^ 2) * Real.sqrt (R ^ 2 * Real.pi)) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg fun x => abs_nonneg _) hCS' 2
    _ = (R ^ 2 * Real.pi) * ∫ x in Metric.ball p R, f x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
          Real.sq_sqrt (by positivity)]
        ring

/-! ## BUB-3: the transfer theorem -/

/-- **K3-BUB3, transfer from `D` to `Ω`.** EXT_PP §B, node BUB-3. -/
theorem exists_zeroSpace_transfer {D Ω : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) (hΩ : IsOpen Ω)
    (hΩD : Ω ⊆ D) {p : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : 2 * r < R)
    (hgate : frontier Ω ∩ D ⊆ Metric.closedBall p r)
    (hfat : ∀ s ∈ Set.Ioo (2 * r) R, ∃ z, ‖z - p‖ = s ∧ z ∉ D)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hgM : ∀ z, |g z| ≤ M) (hg0 : ∀ z ∉ Ω, g z = 0)
    {f : ℂ → ℝ} (hf : f ∈ zeroSpace D) :
    ∃ f' ∈ zeroSpace Ω,
      |(∫ x, f x * g x) - ∫ x, f' x * g x| ≤
          M * Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) *
            Real.sqrt (dirichletEnergyOn D f) ∧
      dirichletEnergyOn Ω f' ≤ (1 + eps1 r R) * dirichletEnergyOn D f := by
  classical
  have hR : 0 < R := by linarith
  have h2r : (0 : ℝ) < 2 * r := by linarith
  set L : ℝ := Real.log (R / (2 * r)) with hL
  have hLpos : 0 < L := by rw [hL]; exact bubbleCutoff_log_pos hr hrR
  set δ : ℝ := 1 / L with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  -- the logarithmic cutoff of BUB-2, in the form given by `exists_logCutoff`
  set χ : ℂ → ℝ := logCutoff p r R with hχdef
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχdef]
    exact ContDiff.comp (bubbleCutoff_contDiff_logCutoffRadial hr hrR)
      ((contDiff_norm_sq (E := ℂ) ℝ).comp (contDiff_id.sub contDiff_const))
  have hχIcc : ∀ x, χ x ∈ Set.Icc 0 1 := by
    intro x; rw [hχdef]; exact bubbleCutoff_logCutoff_mem_Icc p r R x
  have hχ0 : ∀ x, ‖x - p‖ ≤ 2 * r → χ x = 0 := by
    intro x hx; rw [hχdef]; exact bubbleCutoff_logCutoff_eq_zero p hr hrR hx
  have hχ1 : ∀ x, R ≤ ‖x - p‖ → χ x = 1 := by
    intro x hx; rw [hχdef]; exact bubbleCutoff_logCutoff_eq_one p hr hrR hx
  have hχgrad : ∀ x, ‖fderiv ℝ χ x‖ ≤ logCutoffConst / (L * ‖x - p‖) := by
    intro x
    rw [hχdef, hL]
    exact bubbleCutoff_fderiv_logCutoff_le p hr hrR x
  set F : ℂ → ℝ := fun x => χ x * f x with hF
  set f' : ℂ → ℝ := Ω.indicator F with hf'def
  set A : Set ℂ := {x : ℂ | 2 * r < ‖x - p‖ ∧ ‖x - p‖ < R} with hAdef
  have hAmeas : MeasurableSet A := by
    rw [hAdef]
    exact (measurableSet_lt measurable_const
        ((continuous_norm.comp (continuous_id.sub continuous_const)).measurable)).inter
      (measurableSet_lt ((continuous_norm.comp (continuous_id.sub continuous_const)).measurable)
        measurable_const)
  have hχzero : ∀ x, x ∉ A → fderiv ℝ χ x = 0 := by
    intro x hx
    rw [hAdef] at hx
    rw [hχdef]
    exact bubbleTransfer_fderiv_logCutoff_eq_zero p hr hrR hx
  -- `f = 0` off `D`, hence off `H` (because `D ⊆ H`)
  have hf_off : ∀ z, z ∉ D → f z = 0 := by
    intro z hz
    by_contra hne
    exact hz (hf.2.2 (subset_tsupport f hne))
  have hf_lower : ∀ z : ℂ, z.im ≤ 0 → f z = 0 := by
    intro z hz
    refine hf_off z fun hzD => ?_
    have hzH := hDH hzD
    simp only [H, Set.mem_ofPred_eq] at hzH
    linarith
  -- vanishing of `f'` near `Ωᶜ`
  have hvan : ∀ x, x ∉ Ω → ∃ U ∈ 𝓝 x, ∀ y ∈ U, f' y = 0 := by
    intro x hx
    by_cases hcl : x ∈ closure Ω
    · have hfr : x ∈ frontier Ω := by
        rw [frontier, hΩ.interior_eq]
        exact ⟨hcl, hx⟩
      by_cases hxD : x ∈ D
      · -- `x` is close to `p`, where `χ` vanishes on a neighbourhood
        have hxr : ‖x - p‖ ≤ r := by
          have h1 := hgate ⟨hfr, hxD⟩
          rwa [Metric.mem_closedBall, Complex.dist_eq] at h1
        refine ⟨Metric.ball x (2 * r - ‖x - p‖), Metric.ball_mem_nhds x (by linarith), ?_⟩
        intro y hy
        rw [Metric.mem_ball, Complex.dist_eq] at hy
        have hynp : ‖y - p‖ ≤ 2 * r := by
          have h2 : ‖y - p‖ ≤ ‖y - x‖ + ‖x - p‖ := by
            have h3 := norm_add_le (y - x) (x - p)
            rwa [show (y - x) + (x - p) = y - p by ring] at h3
          linarith
        rw [hf'def]
        by_cases hyΩ : y ∈ Ω
        · simp only [Set.indicator_of_mem hyΩ, hF, hχ0 y hynp, zero_mul]
        · simp only [Set.indicator_of_notMem hyΩ]
      · -- `x ∉ D`: `f` vanishes on a neighbourhood, `tsupport f` being compact in `D`
        obtain ⟨ε, hε, hεsub⟩ := hf.2.1.exists_cthickening_subset_open hD hf.2.2
        refine ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε, ?_⟩
        intro y hy
        have hyK : y ∉ tsupport f := by
          intro hyK
          have hxth : x ∈ Metric.thickening ε (tsupport f) := by
            rw [Metric.mem_thickening_iff]
            refine ⟨y, hyK, ?_⟩
            rw [Metric.mem_ball, Complex.dist_eq] at hy
            simpa [Complex.dist_eq, norm_sub_rev] using hy
          exact hxD (hεsub (Metric.thickening_subset_cthickening ε _ hxth))
        have hfy : f y = 0 := by
          by_contra hne
          exact hyK (subset_tsupport f hne)
        rw [hf'def]
        by_cases hyΩ : y ∈ Ω
        · simp only [Set.indicator_of_mem hyΩ, hF, hfy, mul_zero]
        · simp only [Set.indicator_of_notMem hyΩ]
    · -- a neighbourhood of `x` is disjoint from `Ω`
      refine ⟨(closure Ω)ᶜ, ?_, ?_⟩
      · exact isClosed_closure.isOpen_compl.mem_nhds hcl
      · intro y hy
        rw [hf'def, Set.indicator_of_notMem]
        exact fun hyΩ => hy (subset_closure hyΩ)
  -- `f'` is a test function on `Ω`
  have hf'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxΩ : x ∈ Ω
    · refine ((hχsm.mul hf.1).contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hxΩ] with y hy
      simp only [hf'def, Set.indicator_of_mem hy, hF]
    · obtain ⟨U, hU, hU0⟩ := hvan x hxΩ
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hU] with y hy
      exact hU0 y hy
  have hf'cs : HasCompactSupport f' := by
    have hsub : support f' ⊆ support f := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hfx
      refine hx ?_
      rw [hf'def]
      by_cases hxΩ : x ∈ Ω
      · simp only [Set.indicator_of_mem hxΩ, hF, hfx, mul_zero]
      · simp only [Set.indicator_of_notMem hxΩ]
    exact hf.2.1.of_isClosed_subset (isClosed_tsupport _) (closure_mono hsub)
  have hf'ts : tsupport f' ⊆ Ω := by
    intro x hx
    by_contra hxΩ
    obtain ⟨U, hU, hU0⟩ := hvan x hxΩ
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff_nhds.mp hx U hU
    exact (Function.mem_support.mp hyS) (hU0 y hyU)
  have hf'mem : f' ∈ zeroSpace Ω := ⟨hf'sm, hf'cs, hf'ts⟩
  have hfi : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  obtain ⟨C1, hC1⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (g 0)) (hgM 0)
  -- the pairing difference
  have hfg_int : Integrable fun x => f x * g x := by
    refine (hfi.norm.const_mul M).mono'
      ((hf.1.continuous.measurable.mul hg).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |f x| * |g x| ≤ |f x| * M := mul_le_mul_of_nonneg_left (hgM x) (abs_nonneg _)
      _ = M * |f x| := by ring
  have hk_cs : HasCompactSupport fun x => (1 - χ x) * f x := by
    have hsub : support (fun x => (1 - χ x) * f x) ⊆ support f := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hfx
      exact hx (by simp [hfx])
    exact hf.2.1.of_isClosed_subset (isClosed_tsupport _) (closure_mono hsub)
  have hk_cont : Integrable fun x => (1 - χ x) * f x :=
    ((contDiff_const.sub hχsm).continuous.mul hf.1.continuous).integrable_of_hasCompactSupport
      hk_cs
  have hk : Integrable fun x => ((1 - χ x) * f x) * g x := by
    refine (hk_cont.norm.const_mul M).mono'
      ((((contDiff_const.sub hχsm).continuous.mul hf.1.continuous).measurable.mul
        hg)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |(1 - χ x) * f x| * |g x| ≤ |(1 - χ x) * f x| * M :=
          mul_le_mul_of_nonneg_left (hgM x) (abs_nonneg _)
      _ = M * |(1 - χ x) * f x| := by ring
  have hf'g_int : Integrable fun x => f' x * g x := by
    refine ((hf'sm.continuous.integrable_of_hasCompactSupport hf'cs).norm.const_mul M).mono'
      ((hf'sm.continuous.measurable.mul hg).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |f' x| * |g x| ≤ |f' x| * M := mul_le_mul_of_nonneg_left (hgM x) (abs_nonneg _)
      _ = M * |f' x| := by ring
  have hpair_eq : (∫ x, f x * g x) - ∫ x, f' x * g x = ∫ x, ((1 - χ x) * f x) * g x := by
    have hcongr : (fun x => f x * g x - f' x * g x) = fun x => ((1 - χ x) * f x) * g x := by
      funext x
      by_cases hxΩ : x ∈ Ω
      · simp only [hf'def, Set.indicator_of_mem hxΩ, hF]
        ring
      · rw [hg0 x hxΩ]; ring
    calc (∫ x, f x * g x) - ∫ x, f' x * g x
        = ∫ x, (f x * g x - f' x * g x) := (integral_sub hfg_int hf'g_int).symm
      _ = ∫ x, ((1 - χ x) * f x) * g x := by rw [hcongr]
  have hpt_g : ∀ x, |((1 - χ x) * f x) * g x|
      ≤ (Metric.ball p R).indicator (fun x => M * |f x|) x := by
    intro x
    by_cases hxB : x ∈ Metric.ball p R
    · rw [Set.indicator_of_mem hxB]
      have hχI := hχIcc x
      have habs : |1 - χ x| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hχI.2], by linarith [hχI.1]⟩
      calc |((1 - χ x) * f x) * g x| = |1 - χ x| * (|f x| * |g x|) := by
            rw [abs_mul, abs_mul]; ring
        _ ≤ 1 * (|f x| * M) :=
            mul_le_mul habs (mul_le_mul_of_nonneg_left (hgM x) (abs_nonneg _))
              (by positivity) (by norm_num)
        _ = M * |f x| := by ring
    · rw [Set.indicator_of_notMem hxB]
      have hxR : R ≤ ‖x - p‖ := by
        rw [← not_lt]
        intro hlt
        exact hxB (by rw [Metric.mem_ball, Complex.dist_eq]; exact hlt)
      rw [hχ1 x hxR]
      simp
  have hMabs_int : Integrable fun x => (Metric.ball p R).indicator (fun x => M * |f x|) x :=
    (hfi.norm.const_mul M).indicator Metric.isOpen_ball.measurableSet
  have hpair_le : |∫ x, ((1 - χ x) * f x) * g x| ≤ M * ∫ x in Metric.ball p R, |f x| := by
    calc |∫ x, ((1 - χ x) * f x) * g x| ≤ ∫ x, |((1 - χ x) * f x) * g x| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, (Metric.ball p R).indicator (fun x => M * |f x|) x :=
          integral_mono_ae hk.abs hMabs_int (Eventually.of_forall hpt_g)
      _ = ∫ x in Metric.ball p R, M * |f x| := integral_indicator Metric.isOpen_ball.measurableSet
      _ = M * ∫ x in Metric.ball p R, |f x| := by rw [integral_const_mul]
  have hED : dirichletEnergyOn D f = (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ f x‖ ^ 2 :=
    energy_eq_of_tsupport_subset hf.2.2
  have hgrad_eq : ∫ x, ‖fderiv ℝ f x‖ ^ 2 = 2 * Real.pi * dirichletEnergyOn D f := by
    rw [hED]
    field_simp
  have hI_le : ∫ x in Metric.ball p R, |f x| ≤
      Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) *
        Real.sqrt (dirichletEnergyOn D f) := by
    have hCS := bubbleTransfer_integral_abs_sq_le hf.1.continuous C1 hC1 (p := p) (R := R) hR
    have hball := integral_sq_ball_le (hf.1.of_le one_le_smooth) hf.2.1 hf_lower p hR
    have hsq : (∫ x in Metric.ball p R, |f x|) ^ 2 ≤
        (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) * dirichletEnergyOn D f := by
      calc (∫ x in Metric.ball p R, |f x|) ^ 2
          ≤ (R ^ 2 * Real.pi) * ∫ x in Metric.ball p R, f x ^ 2 := hCS
        _ ≤ (R ^ 2 * Real.pi) * (2 * R * (|p.im| + R) * ∫ x, ‖fderiv ℝ f x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hball (by positivity)
        _ = (R ^ 2 * Real.pi) *
              (2 * R * (|p.im| + R) * (2 * Real.pi * dirichletEnergyOn D f)) := by rw [hgrad_eq]
        _ = (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) * dirichletEnergyOn D f := by
            ring
    calc ∫ x in Metric.ball p R, |f x|
        ≤ Real.sqrt ((Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) *
            dirichletEnergyOn D f) := Real.le_sqrt_of_sq_le hsq
      _ = Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) *
            Real.sqrt (dirichletEnergyOn D f) := Real.sqrt_mul (by positivity) _
  have hpair : |(∫ x, f x * g x) - ∫ x, f' x * g x| ≤
      M * Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) *
        Real.sqrt (dirichletEnergyOn D f) := by
    rw [hpair_eq]
    calc |∫ x, ((1 - χ x) * f x) * g x| ≤ M * ∫ x in Metric.ball p R, |f x| := hpair_le
      _ ≤ M * (Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) *
            Real.sqrt (dirichletEnergyOn D f)) := mul_le_mul_of_nonneg_left hI_le hMnn
      _ = M * Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) *
            Real.sqrt (dirichletEnergyOn D f) := by ring
  -- the energy bound
  have hB_int : Integrable fun x => ‖fderiv ℝ f x‖ ^ 2 := by
    have hs : HasCompactSupport fun x => ‖fderiv ℝ f x‖ ^ 2 := by
      have h := (hf.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => ‖L‖ ^ 2)
        (by simp)
      rwa [Function.comp_def] at h
    exact ((hf.1.continuous_fderiv smooth_ne_zero).norm.pow 2).integrable_of_hasCompactSupport hs
  have hA_int : Integrable fun x => ‖fderiv ℝ f' x‖ ^ 2 := by
    have hs : HasCompactSupport fun x => ‖fderiv ℝ f' x‖ ^ 2 := by
      have h := (hf'cs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => ‖L‖ ^ 2)
        (by simp)
      rwa [Function.comp_def] at h
    exact ((hf'sm.continuous_fderiv smooth_ne_zero).norm.pow 2).integrable_of_hasCompactSupport hs
  have hC_cs : HasCompactSupport fun x => f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 := by
    have hsub : support (fun x => f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2) ⊆ support f := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hfx
      exact hx (by simp [hfx])
    exact hf.2.1.of_isClosed_subset (isClosed_tsupport _) (closure_mono hsub)
  have hC_int : Integrable fun x => f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 :=
    ((hf.1.continuous.pow 2).mul ((hχsm.continuous_fderiv smooth_ne_zero).norm.pow 2))
      |>.integrable_of_hasCompactSupport hC_cs
  have hG_int : Integrable fun x =>
      (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2) :=
    (hB_int.const_mul (1 + δ)).add (hC_int.const_mul (1 + δ⁻¹))
  have hInd_int : Integrable fun x => Ω.indicator (fun x =>
      (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2)) x :=
    hG_int.indicator hΩ.measurableSet
  have hpt : ∀ x, ‖fderiv ℝ f' x‖ ^ 2 ≤ Ω.indicator (fun x =>
      (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2)) x := by
    intro x
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
      have hev : f' =ᶠ[𝓝 x] fun y => χ y * f y := by
        filter_upwards [hΩ.mem_nhds hxΩ] with y hy
        simp only [hf'def, Set.indicator_of_mem hy, hF]
      rw [hev.fderiv_eq]
      exact bubbleTransfer_fderiv_mul_sq_le hχsm hf.1 hδpos (hχIcc x)
    · rw [Set.indicator_of_notMem hxΩ]
      have hev : f' =ᶠ[𝓝 x] fun _ => 0 := by
        obtain ⟨U, hU, hU0⟩ := hvan x hxΩ
        filter_upwards [hU] with y hy
        exact hU0 y hy
      rw [hev.fderiv_eq]
      simp
  have hstep1 : ∫ x, ‖fderiv ℝ f' x‖ ^ 2 ≤ ∫ x, Ω.indicator (fun x =>
      (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2)) x :=
    integral_mono_ae hA_int hInd_int (Eventually.of_forall hpt)
  have hstep2 : ∫ x, Ω.indicator (fun x =>
      (1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2)) x
      = ∫ x in Ω, ((1 + δ) * ‖fderiv ℝ f x‖ ^ 2 + (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2)) :=
    integral_indicator hΩ.measurableSet
  have hstep3 : ∫ x in Ω, ((1 + δ) * ‖fderiv ℝ f x‖ ^ 2 +
        (1 + δ⁻¹) * (f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2))
      = (1 + δ) * (∫ x in Ω, ‖fderiv ℝ f x‖ ^ 2)
        + (1 + δ⁻¹) * (∫ x in Ω, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2) := by
    rw [integral_add ((hB_int.const_mul (1 + δ)).integrableOn)
        ((hC_int.const_mul (1 + δ⁻¹)).integrableOn),
      integral_const_mul, integral_const_mul]
  have hstep4 : ∫ x in Ω, ‖fderiv ℝ f x‖ ^ 2 ≤ ∫ x, ‖fderiv ℝ f x‖ ^ 2 :=
    setIntegral_le_integral hB_int (Eventually.of_forall fun x => sq_nonneg _)
  -- the annulus estimate
  have hgA : ∫ x in Ω, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2
      = ∫ x in Ω ∩ A, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 := by
    rw [← integral_indicator hΩ.measurableSet,
      ← integral_indicator (hΩ.measurableSet.inter hAmeas)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hxΩ : x ∈ Ω
    · by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem (Set.mem_inter hxΩ hxA), Set.indicator_of_mem hxΩ]
      · rw [Set.indicator_of_notMem (show x ∉ Ω ∩ A from fun h => hxA h.2),
          Set.indicator_of_mem hxΩ]
        simp [hχzero x hxA]
    · rw [Set.indicator_of_notMem hxΩ,
        Set.indicator_of_notMem (show x ∉ Ω ∩ A from fun h => hxΩ h.1)]
  have hmono1 : ∫ x in Ω ∩ A, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2
      ≤ ∫ x in A, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 :=
    setIntegral_mono_set hC_int.integrableOn (Eventually.of_forall fun x => by positivity)
      (Eventually.of_forall fun x hx => hx.2)
  have hVolA : volume A < ∞ := by
    refine lt_of_le_of_lt (measure_mono ?_) (bubbleTransfer_volume_closedBall_lt_top p R)
    rw [hAdef]
    intro x hx
    rw [Metric.mem_closedBall, Complex.dist_eq]
    exact hx.2.le
  have hpt_ann : ∀ x ∈ A, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2
      ≤ (logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2) := by
    intro x hx
    have hd : 0 < ‖x - p‖ := by linarith [hx.1]
    have h1 : ‖fderiv ℝ χ x‖ ^ 2 ≤ (logCutoffConst / (L * ‖x - p‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hχgrad x) 2
    have hid : f x ^ 2 * (logCutoffConst / (L * ‖x - p‖)) ^ 2
        = (logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2) := by
      have hL0 : L ≠ 0 := hLpos.ne'
      have hd0 : ‖x - p‖ ≠ 0 := hd.ne'
      field_simp
    calc f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2
        ≤ f x ^ 2 * (logCutoffConst / (L * ‖x - p‖)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2) := hid
  have hInt_h : IntegrableOn (fun x => (logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2)) A := by
    have hbdd : ∀ᵐ x ∂volume.restrict A,
        ‖(logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2)‖
          ≤ (logCutoffConst / L) ^ 2 * (C1 ^ 2 / (2 * r) ^ 2) := by
      filter_upwards [ae_restrict_mem hAmeas] with x hx
      have hd : 0 < ‖x - p‖ := by linarith [hx.1]
      have hfx : |f x| ≤ C1 := hC1 x
      have hC1nn : 0 ≤ C1 := le_trans (abs_nonneg _) hfx
      have hf2 : f x ^ 2 ≤ C1 ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hfx 2
      have hd2 : (2 * r) ^ 2 ≤ ‖x - p‖ ^ 2 := pow_le_pow_left₀ h2r.le hx.1.le 2
      have hdiv : f x ^ 2 / ‖x - p‖ ^ 2 ≤ C1 ^ 2 / (2 * r) ^ 2 :=
        div_le_div₀ (sq_nonneg _) hf2 (by positivity) hd2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (logCutoffConst / L) ^ 2)]
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    have hmeas1 : Measurable fun x : ℂ => f x ^ 2 := by
      have h : (fun x : ℂ => f x ^ 2) = fun x => f x * f x := by
        funext x; rw [pow_two]
      rw [h]
      exact hf.1.continuous.measurable.mul hf.1.continuous.measurable
    have hmeas2 : Measurable fun x : ℂ => ‖x - p‖ ^ 2 := by
      have hc : Continuous fun x : ℂ => ‖x - p‖ :=
        continuous_norm.comp (continuous_id.sub continuous_const)
      have h : (fun x : ℂ => ‖x - p‖ ^ 2) = fun x => ‖x - p‖ * ‖x - p‖ := by
        funext x; rw [pow_two]
      rw [h]
      exact (hc.mul hc).measurable
    have hmeas : AEStronglyMeasurable
        (fun x => (logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2)) (volume.restrict A) :=
      (measurable_const.mul (hmeas1.div hmeas2)).aestronglyMeasurable
    exact ⟨hmeas, HasFiniteIntegral.restrict_of_bounded _ hVolA hbdd⟩
  have hmono2 : ∫ x in A, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2
      ≤ ∫ x in A, (logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2) :=
    setIntegral_mono_on (hf := hC_int.integrableOn) (hg := hInt_h) hAmeas
      (fun x hx => hpt_ann x hx)
  have hHardy : ∫ x in A, f x ^ 2 / ‖x - p‖ ^ 2
      ≤ 4 * Real.pi ^ 2 * ∫ x in A, ‖fderiv ℝ f x‖ ^ 2 := by
    rw [hAdef]
    exact hardy_annulus (hf.1.of_le one_le_smooth) hf.2.1 p h2r hrR fun s hs => by
      obtain ⟨z, hz, hzD⟩ := hfat s hs
      exact ⟨z, hz, hf_off z hzD⟩
  have hstep5 : ∫ x in Ω, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2
      ≤ (logCutoffConst / L) ^ 2 * (4 * Real.pi ^ 2) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
    calc ∫ x in Ω, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2
        = ∫ x in Ω ∩ A, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 := hgA
      _ ≤ ∫ x in A, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 := hmono1
      _ ≤ ∫ x in A, (logCutoffConst / L) ^ 2 * (f x ^ 2 / ‖x - p‖ ^ 2) := hmono2
      _ = (logCutoffConst / L) ^ 2 * ∫ x in A, f x ^ 2 / ‖x - p‖ ^ 2 :=
          integral_const_mul _ _
      _ ≤ (logCutoffConst / L) ^ 2 * (4 * Real.pi ^ 2 * ∫ x in A, ‖fderiv ℝ f x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hHardy (by positivity)
      _ = (logCutoffConst / L) ^ 2 * (4 * Real.pi ^ 2) * ∫ x in A, ‖fderiv ℝ f x‖ ^ 2 := by ring
      _ ≤ (logCutoffConst / L) ^ 2 * (4 * Real.pi ^ 2) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (setIntegral_le_integral hB_int (Eventually.of_forall fun x => sq_nonneg _))
            (by positivity)
  have hmain : ∫ x, ‖fderiv ℝ f' x‖ ^ 2 ≤ (1 + eps1 r R) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
    have hC0 : (0 : ℝ) ≤ 1 + δ := by linarith
    have hC1' : (0 : ℝ) ≤ 1 + δ⁻¹ := by positivity
    have hcomb := hstep1.trans (le_of_eq hstep2)
    rw [hstep3] at hcomb
    have h4 := mul_le_mul_of_nonneg_left hstep4 hC0
    have h5 := mul_le_mul_of_nonneg_left hstep5 hC1'
    have hkey : (1 + δ) * (∫ x in Ω, ‖fderiv ℝ f x‖ ^ 2)
        + (1 + δ⁻¹) * (∫ x in Ω, f x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2)
        ≤ (1 + δ) * (∫ x, ‖fderiv ℝ f x‖ ^ 2)
          + (1 + δ⁻¹) * ((logCutoffConst / L) ^ 2 * (4 * Real.pi ^ 2)
              * ∫ x, ‖fderiv ℝ f x‖ ^ 2) := by linarith
    refine hcomb.trans (hkey.trans (le_of_eq ?_))
    have hε : eps1 r R = 1 / L + (1 + (1 / L)⁻¹) * 4 * Real.pi ^ 2 * logCutoffConst ^ 2 / L ^ 2 :=
      eps1_eq r R L hL.symm
    rw [hε, hδ]
    field_simp
    ring
  have hEn : dirichletEnergyOn Ω f' ≤ (1 + eps1 r R) * dirichletEnergyOn D f := by
    have hEΩ : dirichletEnergyOn Ω f' = (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ f' x‖ ^ 2 :=
      energy_eq_of_tsupport_subset hf'ts
    rw [hEΩ, hED]
    calc (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ f' x‖ ^ 2
        ≤ (2 * Real.pi)⁻¹ * ((1 + eps1 r R) * ∫ x, ‖fderiv ℝ f x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = (1 + eps1 r R) * ((2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ f x‖ ^ 2) := by ring
  exact ⟨f', hf'mem, hpair, hEn⟩

end QuantumZipper.K3

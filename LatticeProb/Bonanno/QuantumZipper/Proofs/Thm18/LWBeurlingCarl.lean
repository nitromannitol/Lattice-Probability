/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingCarl at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingWirt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Algebra.QuadraticDiscriminant

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-4, node B2b: Carleman's differential inequality (`CarlemanIneqStmt`)

Plan: `handoff/LW-BEURLING.md`. Source: Garnett–Marshall, *Harmonic Measure*, App. G,
Lemma G.2 (Carleman's differential inequality), p. 481, in logarithmic coordinates
`ζ = t + iθ` (cross sections are circles of length `2π`, so `ℓ = 2π`, `π/ℓ = 1/2`).
On the circle `Re ζ = t`, with `v = V(t + i·)`:
`∫ v v_tt = ∫ v (v_tt + v_θθ) + ∫ v_θ²` (periodic integration by parts), so
`I'' = 2∫v_t² + 2∫v_θ² + 2∫v(v_tt + v_θθ) ≥ 0`; if `v` has a zero, Wirtinger (B1b) gives
`∫v² ≤ 4∫v_θ²`, and Cauchy–Schwarz `(∫ v v_t)² ≤ ∫v² ∫v_t²` gives `I'² + I² ≤ 2 I I''`.
GM use the Dirichlet integral of the harmonic measure and Green's formula instead; here the
`C²` subharmonic `V` makes the slice computation direct (own adaptation, see the plan).
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

lemma lwb_line_hasDerivAt (t θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (t : ℂ) + (θ : ℂ) * Complex.I) Complex.I θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).const_add (t : ℂ)
  simpa using h

lemma lwb_line_continuous (t : ℝ) :
    Continuous (fun θ : ℝ => (t : ℂ) + (θ : ℂ) * Complex.I) := by fun_prop

/-- Slice derivative along the circle `Re ζ = t`. -/
lemma lwb_slice_hasDerivAt {F : ℂ → ℝ} {t θ : ℝ}
    (hF : DifferentiableAt ℝ F ((t : ℂ) + (θ : ℂ) * Complex.I)) :
    HasDerivAt (fun θ : ℝ => F ((t : ℂ) + (θ : ℂ) * Complex.I))
      (fderiv ℝ F ((t : ℂ) + (θ : ℂ) * Complex.I) Complex.I) θ :=
  hF.hasFDerivAt.comp_hasDerivAt θ (lwb_line_hasDerivAt t θ)

/-- Cauchy–Schwarz for interval integrals of continuous functions (discriminant argument). -/
lemma lwb_interval_cs {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * ∫ x in a..b, g x ^ 2 := by
  set A := ∫ x in a..b, f x ^ 2
  set B := ∫ x in a..b, g x ^ 2
  set C := ∫ x in a..b, f x * g x
  have hq : ∀ s : ℝ, 0 ≤ A * (s * s) + (2 * C) * s + B := by
    intro s
    have h1 : 0 ≤ ∫ x in a..b, (s * f x + g x) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have e : ∫ x in a..b, (s * f x + g x) ^ 2 = A * (s * s) + (2 * C) * s + B := by
      have ep : (fun x => (s * f x + g x) ^ 2) =
          fun x => (s * s) * f x ^ 2 + ((2 * s) * (f x * g x) + g x ^ 2) := by
        funext x; ring
      rw [ep, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
      · ring
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [e] at h1; exact h1
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

/-- **B2b** (`CarlemanIneqStmt`). -/
theorem carlemanIneqStmt_holds : CarlemanIneqStmt := by
  intro V T hV hper hnn hsub t ht
  set Ω : Set ℂ := {ζ : ℂ | ζ.re < T} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt Complex.continuous_re continuous_const
  set L : ℝ → ℂ := fun θ : ℝ => (t : ℂ) + (θ : ℂ) * Complex.I with hLdef
  have hmem : ∀ θ : ℝ, L θ ∈ Ω := fun θ => by simp [hΩ, hLdef, ht]
  have hLc : Continuous L := lwb_line_continuous t
  -- regularity of `V` and its partial derivatives
  have hd1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ V y) Ω := hV.fderiv_of_isOpen hΩo (by norm_num)
  have hDt : ContDiffOn ℝ 1 (lpDt V) Ω := hd1.clm_apply contDiffOn_const
  have hDθ : ContDiffOn ℝ 1 (lpDθ V) Ω := hd1.clm_apply contDiffOn_const
  have hDtt : ContinuousOn (lpDtt V) Ω :=
    (hDt.continuousOn_fderiv_of_isOpen hΩo le_rfl).clm_apply continuousOn_const
  have hDθθ : ContinuousOn (lpDθθ V) Ω :=
    (hDθ.continuousOn_fderiv_of_isOpen hΩo le_rfl).clm_apply continuousOn_const
  have hdiffV : ∀ θ : ℝ, DifferentiableAt ℝ V (L θ) := fun θ =>
    (hV.differentiableOn (by norm_num) _ (hmem θ)).differentiableAt (hΩo.mem_nhds (hmem θ))
  have hdiffθ : ∀ θ : ℝ, DifferentiableAt ℝ (lpDθ V) (L θ) := fun θ =>
    (hDθ.differentiableOn (by norm_num) _ (hmem θ)).differentiableAt (hΩo.mem_nhds (hmem θ))
  -- the slices
  set v : ℝ → ℝ := fun θ => V (L θ) with hv
  set vt : ℝ → ℝ := fun θ => lpDt V (L θ) with hvt
  set vθ : ℝ → ℝ := fun θ => lpDθ V (L θ) with hvθ
  set vtt : ℝ → ℝ := fun θ => lpDtt V (L θ) with hvtt
  set vθθ : ℝ → ℝ := fun θ => lpDθθ V (L θ) with hvθθ
  have hvc : Continuous v := hV.continuousOn.comp_continuous hLc hmem
  have hvtc : Continuous vt := hDt.continuousOn.comp_continuous hLc hmem
  have hvθc : Continuous vθ := hDθ.continuousOn.comp_continuous hLc hmem
  have hvttc : Continuous vtt := hDtt.comp_continuous hLc hmem
  have hvθθc : Continuous vθθ := hDθθ.comp_continuous hLc hmem
  have hvd : ∀ θ, HasDerivAt v (vθ θ) θ := fun θ => lwb_slice_hasDerivAt (hdiffV θ)
  have hvθd : ∀ θ, HasDerivAt vθ (vθθ θ) θ := fun θ => lwb_slice_hasDerivAt (hdiffθ θ)
  -- periodicity of the slices
  have hvper : Function.Periodic v (2 * π) := by
    intro θ
    simp only [hv, hLdef]
    rw [show ((t : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I) =
      ((t : ℂ) + (θ : ℂ) * Complex.I) + 2 * π * Complex.I by push_cast; ring]
    exact hper _
  have hvθper : Function.Periodic vθ (2 * π) := by
    intro x
    have h1 : HasDerivAt (fun y => v (y + 2 * π)) (vθ (x + 2 * π)) x :=
      (hvd (x + 2 * π)).comp_add_const x (2 * π)
    have h2 : (fun y => v (y + 2 * π)) = v := funext hvper
    rw [h2] at h1
    exact h1.unique (hvd x)
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have ii : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume (-π) π :=
    fun f hf => hf.intervalIntegrable _ _
  -- integration by parts in `θ`
  have hibp : ∫ θ in (-π)..π, v θ * vθθ θ = -∫ θ in (-π)..π, vθ θ ^ 2 := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hvc.continuousOn
      hvθc.continuousOn (fun x _ => hvd x) (fun x _ => hvθd x) (ii _ hvθc) (ii _ hvθθc)]
    have e1 : v π = v (-π) := by
      have := hvper (-π); rw [show -π + 2 * π = π by ring] at this; exact this
    have e2 : vθ π = vθ (-π) := by
      have := hvθper (-π); rw [show -π + 2 * π = π by ring] at this; exact this
    rw [e1, e2, sub_self, zero_sub]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    ring
  -- the three integrals
  set A := ∫ θ in (-π)..π, v θ ^ 2 with hA
  set B := ∫ θ in (-π)..π, vt θ ^ 2 with hB
  set Cc := ∫ θ in (-π)..π, v θ * vt θ with hCc
  set E := ∫ θ in (-π)..π, vθ θ ^ 2 with hE
  set F := ∫ θ in (-π)..π, v θ * (vtt θ + vθθ θ) with hF
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hpi fun x _ => sq_nonneg _
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg hpi fun x _ => sq_nonneg _
  have hE0 : 0 ≤ E := intervalIntegral.integral_nonneg hpi fun x _ => sq_nonneg _
  have hF0 : 0 ≤ F := intervalIntegral.integral_nonneg hpi fun x _ =>
    mul_nonneg (hnn _ (hmem x)) (hsub _ (hmem x))
  have hI : lpI V t = A := rfl
  have hI1 : lpI1 V t = 2 * Cc := by
    have e : lpI1 V t = ∫ θ in (-π)..π, 2 * (v θ * vt θ) := rfl
    rw [e, intervalIntegral.integral_const_mul]
  have hvtt_eq : ∫ θ in (-π)..π, v θ * vtt θ = F + E := by
    have : (fun θ => v θ * vtt θ) = fun θ => v θ * (vtt θ + vθθ θ) - v θ * vθθ θ := by
      funext θ; ring
    rw [this, intervalIntegral.integral_sub (ii (fun θ => v θ * (vtt θ + vθθ θ)) (by fun_prop))
      (ii (fun θ => v θ * vθθ θ) (by fun_prop)), hibp]
    ring
  have hI2 : lpI2 V t = 2 * B + 2 * F + 2 * E := by
    have e : lpI2 V t = ∫ θ in (-π)..π, 2 * (vt θ ^ 2 + v θ * vtt θ) := rfl
    rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (ii (fun θ => vt θ ^ 2) (by fun_prop)) (ii (fun θ => v θ * vtt θ) (by fun_prop))]
    change 2 * (B + ∫ θ in (-π)..π, v θ * vtt θ) = _
    rw [hvtt_eq]; ring
  refine ⟨by rw [hI2]; positivity, fun hz => ?_⟩
  obtain ⟨θ₀, hθ₀⟩ := hz
  have hW : A ≤ 4 * E := wirtingerCircleStmt_holds v vθ hvd hvθc hvper ⟨θ₀, hθ₀⟩
  have hCS : Cc ^ 2 ≤ A * B := lwb_interval_cs hvc hvtc hpi
  rw [hI, hI1, hI2]
  nlinarith [mul_nonneg hA0 hF0, mul_le_mul_of_nonneg_left hW hA0]

end LWFar
end Thm18Asm
end QuantumZipper

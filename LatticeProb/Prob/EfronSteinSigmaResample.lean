/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/EfronSteinResample.lean.
-/

import LatticeProb.Prob.EfronSteinSigma
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Efron–Stein inequality: resampling forms (abstract identities)

Let `A, U, U'` be sub-σ-algebras of the ambient σ-algebra, with `U'` independent of `A ⊔ U`, and let
`F` (resp. `F'`) be square-integrable and measurable with respect to `A ⊔ U` (resp. `A ⊔ U'`).
Think of `F` as a function of `(Z, X)` and of `F'` as the same function of `(Z, X')`, where `Z`
generates `A`, `X` generates `U`, and `X'` generates `U'`.

* `es_resample_identity`: if `F'` has the same second moment as `F` and the same integrals as `F`
  over the sets of `A`, then `E[(F - E[F | A])²] = ½ E[(F' - F)²]`.
* `es_half_sq_eq_posPart_sq`: if `(F' - F)₊` and `(F - F')₊` have the same second moment, then
  `½ E[(F' - F)²] = E[((F' - F)₊)²]`.

The file also proves `es_integral_sub_condExp_sq`, the identity
`E[(F - E[F | A])²] = E[F²] - E[E[F | A]²]` used in the first identity. Together these are the conditional-variance terms of the σ-algebra
Efron–Stein inequality `efronStein_sigma` written with a resampled copy, and its half-square and
positive-part forms.

In the product-space case with real coordinates, the resulting inequality is the variance bound
`efron_stein_var` of `LatticeProb.Prob.EfronSteinCov`. This file does not reprove it.

The inequalities are the Efron–Stein inequality in the forms of van Handel, *Probability in High
Dimension* (lecture notes, 2016), §2.1, and of Boucheron–Lugosi–Massart, *Concentration
Inequalities* (OUP 2013), Thm 3.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}

/-- `E[(F - E[F | A])²] = E[F²] - E[E[F | A]²]`. -/
lemma es_integral_sub_condExp_sq [IsProbabilityMeasure μ] {A : MeasurableSpace Ω} (hA : A ≤ m₀)
    {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    ∫ ω, (F ω - μ[F | A] ω) ^ 2 ∂μ = ∫ ω, F ω ^ 2 ∂μ - ∫ ω, (μ[F | A] ω) ^ 2 ∂μ := by
  have h := es_variance_eq_add hA hF
  rw [variance_eq_sub hF, variance_eq_sub (hF.condExp one_le_two), integral_condExp hA] at h
  have e1 : μ[F ^ 2] = ∫ ω, F ω ^ 2 ∂μ := rfl
  have e2 : μ[μ[F | A] ^ 2] = ∫ ω, (μ[F | A] ω) ^ 2 ∂μ := rfl
  linarith

/-- **Resampling identity.** Let `A, U, U'` be sub-σ-algebras with `U'` independent of `A ⊔ U`,
`F ∈ L²` measurable w.r.t. `A ⊔ U`, `F' ∈ L²` measurable w.r.t. `A ⊔ U'`, with `E F'² = E F²`
and `∫_s F' = ∫_s F` for `s ∈ A`. Then `E[(F - E[F | A])²] = ½ E[(F' - F)²]`. -/
theorem es_resample_identity [IsProbabilityMeasure μ] {A U U' : MeasurableSpace Ω}
    (hA : A ≤ m₀) (hU : U ≤ m₀) (hU' : U' ≤ m₀) (hind : Indep U' (A ⊔ U) μ) {F F' : Ω → ℝ}
    (hFm : StronglyMeasurable[A ⊔ U] F) (hF'm : StronglyMeasurable[A ⊔ U'] F')
    (hF : MemLp F 2 μ) (hF' : MemLp F' 2 μ)
    (hsq : ∫ ω, F' ω ^ 2 ∂μ = ∫ ω, F ω ^ 2 ∂μ)
    (hset : ∀ s, MeasurableSet[A] s → ∫ ω in s, F' ω ∂μ = ∫ ω in s, F ω ∂μ) :
    ∫ ω, (F ω - μ[F | A] ω) ^ 2 ∂μ = (1 / 2) * ∫ ω, (F' ω - F ω) ^ 2 ∂μ := by
  have hFi : Integrable F μ := hF.integrable one_le_two
  have hF'i : Integrable F' μ := hF'.integrable one_le_two
  have hAU : A ⊔ U ≤ m₀ := sup_le hA hU
  have hAU' : U' ⊔ A ≤ m₀ := sup_le hU' hA
  set M : Ω → ℝ := μ[F | A] with hM
  have hML : MemLp M 2 μ := hF.condExp one_le_two
  -- `E[F | U' ⊔ A] = E[F | A]`
  have c1 : μ[F | U' ⊔ A] =ᵐ[μ] M :=
    condExp_sup_indep_eq le_sup_left hAU hU' hind hFm hFi
  -- `E[F' | A] = E[F | A]`
  have c2 : μ[F' | A] =ᵐ[μ] M :=
    ae_eq_condExp_of_forall_setIntegral_eq hA hFi (fun s _ _ => integrable_condExp.integrableOn)
      (fun s hs _ => by rw [setIntegral_condExp hA hF'i hs, hset s hs])
      stronglyMeasurable_condExp.aestronglyMeasurable
  have hF'm' : StronglyMeasurable[U' ⊔ A] F' := by rwa [sup_comm]
  -- `E[F F'] = E[M²]`
  have hFF' : Integrable (F * F') μ := hF.integrable_mul hF'
  have hMF' : Integrable (M * F') μ := hML.integrable_mul hF'
  have hcross : ∫ ω, F ω * F' ω ∂μ = ∫ ω, M ω ^ 2 ∂μ := by
    have s1 : ∫ ω, (F * F') ω ∂μ = ∫ ω, (M * F') ω ∂μ := by
      rw [← integral_condExp hAU' (f := F * F')]
      refine integral_congr_ae ?_
      filter_upwards [condExp_mul_of_stronglyMeasurable_right hF'm' hFF' hFi, c1] with ω h1 h2
      rw [h1, Pi.mul_apply, h2, Pi.mul_apply]
    have s2 : ∫ ω, (M * F') ω ∂μ = ∫ ω, M ω ^ 2 ∂μ := by
      rw [← integral_condExp hA (f := M * F')]
      refine integral_congr_ae ?_
      filter_upwards [condExp_mul_of_stronglyMeasurable_left
        (stronglyMeasurable_condExp (m := A) (f := F) (μ := μ)) hMF' hF'i, c2] with ω h1 h2
      rw [h1, Pi.mul_apply, h2, sq]
    simpa only [Pi.mul_apply] using s1.trans s2
  have hexp : (fun ω => (F' ω - F ω) ^ 2) =
      fun ω => F' ω ^ 2 + F ω ^ 2 - 2 * (F ω * F' ω) := by
    funext ω; ring
  have i1 : Integrable (fun ω => F' ω ^ 2 + F ω ^ 2) μ := hF'.integrable_sq.add hF.integrable_sq
  have i2 : Integrable (fun ω => 2 * (F ω * F' ω)) μ := hFF'.const_mul 2
  rw [es_integral_sub_condExp_sq hA hF, hexp, integral_sub i1 i2,
    integral_add hF'.integrable_sq hF.integrable_sq, integral_const_mul, hcross, hsq]
  ring

/-- `½ E[x²] = E[(x₊)²]` for `x = F' - F`, when `x₊` and `(-x)₊` have the same second moment
(this holds, for example, when `x` is symmetric in law). -/
theorem es_half_sq_eq_posPart_sq [IsFiniteMeasure μ] {F F' : Ω → ℝ} (hF : MemLp F 2 μ)
    (hF' : MemLp F' 2 μ)
    (hsymm : ∫ ω, max (F' ω - F ω) 0 ^ 2 ∂μ = ∫ ω, max (F ω - F' ω) 0 ^ 2 ∂μ) :
    (1 / 2) * ∫ ω, (F' ω - F ω) ^ 2 ∂μ = ∫ ω, max (F' ω - F ω) 0 ^ 2 ∂μ := by
  have hD : MemLp (fun ω => F' ω - F ω) 2 μ := hF'.sub hF
  have hP : MemLp (fun ω => max (F' ω - F ω) 0) 2 μ := hD.sup (memLp_const 0)
  have hN : MemLp (fun ω => max (F ω - F' ω) 0) 2 μ := (hF.sub hF').sup (memLp_const 0)
  have hpt : (fun ω => (F' ω - F ω) ^ 2) =
      fun ω => max (F' ω - F ω) 0 ^ 2 + max (F ω - F' ω) 0 ^ 2 := by
    funext ω
    rcases le_total (F' ω - F ω) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  rw [hpt, integral_add hP.integrable_sq hN.integrable_sq, ← hsymm]
  ring

/-! ### Nonvacuity

With the trivial σ-algebras `A = U = U' = ⊥` and a constant `F`, the resample `F' = F` is trivial.
The hypotheses of `es_resample_identity` and `es_half_sq_eq_posPart_sq` hold for it, and both
identities reduce to `0 = 0`. -/

namespace EfronSteinSigmaResampleExample

/-- Nonvacuity of `es_resample_identity`: for a constant `F` and the trivial σ-algebras
`A = U = U' = ⊥`, with the resample `F' = F`, every hypothesis holds. -/
example [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ ω, ((fun _ : Ω => c) ω - μ[fun _ : Ω => c | (⊥ : MeasurableSpace Ω)] ω) ^ 2 ∂μ =
      (1 / 2) * ∫ ω, ((fun _ : Ω => c) ω - (fun _ : Ω => c) ω) ^ 2 ∂μ :=
  es_resample_identity bot_le bot_le bot_le (indep_bot_left _) stronglyMeasurable_const
    stronglyMeasurable_const (memLp_const c) (memLp_const c) rfl fun _ _ => rfl

/-- Nonvacuity of `es_half_sq_eq_posPart_sq`: for a constant `F` and the trivial resample
`F' = F`, the symmetry hypothesis holds. -/
example [IsFiniteMeasure μ] (c : ℝ) :
    (1 / 2) * ∫ ω, ((fun _ : Ω => c) ω - (fun _ : Ω => c) ω) ^ 2 ∂μ =
      ∫ ω, max ((fun _ : Ω => c) ω - (fun _ : Ω => c) ω) 0 ^ 2 ∂μ :=
  es_half_sq_eq_posPart_sq (memLp_const c) (memLp_const c) rfl

end EfronSteinSigmaResampleExample

end LatticeProb

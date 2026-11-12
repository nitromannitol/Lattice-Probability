/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.EfronSteinResample at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.EfronStein
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Efron–Stein inequality: resampling forms (abstract identity)

The identity behind the resampling form of Efron–Stein: if `F` is a function of `(Z, X_i)`,
`F'` the same function of `(Z, X'_i)` with `X'_i` an independent copy of `X_i`, then
`E[(F - E[F | Z])²] = ½ E[(F' - F)²]` (`es_resample_identity`), and, by the symmetry of
`(F, F')`, `½ E[(F' - F)²] = E[(F' - F)_+²]` (`es_half_sq_eq_posPart_sq`).

Source: R. van Handel, *Probability in High Dimension* (lecture notes, Princeton, 2016), §2.1
(the Efron–Stein inequality in the form `Var f ≤ ½ ∑ E[(f - f^{(i)})²]`,
via `Var_i f = ½ E_i[(f - f^{(i)})²]` for an independent copy); Boucheron–Lugosi–Massart,
*Concentration Inequalities* (OUP 2013), Thm 3.1 and the remark after it (positive-part form,
used in DDDF (5.58), arXiv:1904.08021 `tightness.tex` lines 1081–1090, and LM (5.3)–(5.4),
arXiv:1905.00379 `local-metrics-final.tex` lines 1017–1025).

Here everything is stated with σ-algebras: `A = σ(Z)`, `U = σ(X_i)`, `U' = σ(X'_i)`, and the two
consequences of "`(Z, X'_i)` has the law of `(Z, X_i)`" that the proof uses are hypotheses
(`E F'² = E F²` and `∫_s F' = ∫_s F` for `s ∈ A`); the concrete random-variable version is in
`LQGMetric.Prob.EfronSteinCopy`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace LQGMetric

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

/-- `½ x² = (x₊)²` on average, when `x = F' - F` is symmetric in law. -/
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

end LQGMetric

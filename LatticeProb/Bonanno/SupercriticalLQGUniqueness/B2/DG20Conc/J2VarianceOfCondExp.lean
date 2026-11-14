/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2VarianceOfCondExp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.ConditionalVariance
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.EfronBlocks

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j2_log_variance_le_of_condExp_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) (N : ℝ)
    (hN : Var[P[L24.logLenPsi ξ Q W P n |
      (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
        (fun ω => T20B.restrD (fun x => psiMN Q W P K n x ω))]; P] ≤ N) :
    Var[L24.logLenPsi ξ Q W P n; P] ≤
      ξ ^ 2 * (K * Real.log 2) + N := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let X : Ω → T20B.dyD → ℝ :=
    fun ω => T20B.restrD (fun x => psiMN Q W P K n x ω)
  have hK := isPsiVersion_psiMN (Q := Q) hW hKn
  have hXm : Measurable X :=
    T20B.measurable_restrD.comp (measurable_pi_iff.2 hK.meas)
  have hF : MemLp (L24.logLenPsi ξ Q W P n) 2 P :=
    ((L24.psi_memLp_variance hW Q ξ).choose_spec.2 n).1
  have hdecomp := variance_decomposition hXm.comap_le hF
  have hcv : (∫ ω, Var[L24.logLenPsi ξ Q W P n; P |
      (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap X] ω ∂P) ≤
      ξ ^ 2 * (K * Real.log 2) := by
    have hi := integral_mono_ae
      (integrable_condVar (X := L24.logLenPsi ξ Q W P n)
        (m := (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap X))
      (integrable_const (ξ ^ 2 * (K * Real.log 2)))
      (psi_condVar_le hW Q ξ hKn)
    simpa using hi
  change Var[L24.logLenPsi ξ Q W P n; P] =
    (∫ ω, Var[L24.logLenPsi ξ Q W P n; P |
      (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap X] ω ∂P) +
      Var[P[L24.logLenPsi ξ Q W P n |
        (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap X]; P] at hdecomp
  rw [hdecomp]
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc

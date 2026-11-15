/- The Fubini argument is adapted from Leonardo Bonanno’s lean-formalizations
   (https://github.com/leobon12/lean-formalizations), source module
   MatedCRTHarmonic.GMCFacts.ReplacedDefs, commit fdb5cad. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedDefs

/-! # Local integrability of a radial GFF version -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- A measurable continuous version of the centered circle-average process
has an almost surely locally integrable radial realization. -/
theorem IsWholePlaneGFF.ae_locallyIntegrable_radialW
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {ρ : Ω → C(ℝ, ℝ)} (hρm : Measurable ρ)
    (hρ : ∀ t, (fun ω => ρ ω t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0) :
    ∀ᵐ ω ∂P, LocallyIntegrable (radialW (ρ ω)) volume := by
  have := hX.gaussian.isProbabilityMeasure
  have hS : MeasurableSet {p : Ω × ℂ |
      radialW (ρ p.1) p.2 = radialFun (X p.1) p.2 - circleAvg (X p.1) 1 0} := by
    refine measurableSet_eq_fun (measurable_radialW_uncurry.comp
      ((hρm.comp measurable_fst).prodMk measurable_snd)) ?_
    exact (measurable_radialFun_uncurry.comp ((hX.measurable.comp measurable_fst).prodMk
      measurable_snd)).sub ((measurable_circleAvg_left 1 0).comp (hX.measurable.comp measurable_fst))
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  have hjoint : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ),
      radialW (ρ ω) z = radialFun (X ω) z - circleAvg (X ω) 1 0 := by
    rw [Measure.ae_ae_comm hS]
    filter_upwards [hne] with z hz
    filter_upwards [hρ (-Real.log ‖z‖)] with ω hω
    simp only [radialW, hω, neg_neg, Real.exp_log (norm_pos_iff.2 hz)]
    rfl
  filter_upwards [hjoint, ConeArea4.ae_radial_R2 hX] with ω hω hR
  obtain ⟨R, -, -, hRe, hRl⟩ := hR
  have hloc : LocallyIntegrable (radialFun (X ω)) volume := hRl.congr hRe.symm
  have hsub : LocallyIntegrable
      (fun z => radialFun (X ω) z - circleAvg (X ω) 1 0) volume :=
    hloc.sub (locallyIntegrable_const _)
  exact hsub.congr (hω.mono fun _ hz => hz.symm)

end LatticeProb.LQG

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.ConeLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.ConeCutoff
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFF

/-!
# The actual cone field on a disk away from its singularity

The radial Brownian replacement theorem identifies the frozen γ-cone with a
unit-circle-normalized whole-plane GFF plus the deterministic logarithm on
the unit disk. A smooth cutoff gives equality of distributions on every
compactly contained observation region avoiding the root.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace LQGMetric
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.MoTPort.GFFBdry
open scoped NNReal

namespace MatedCRTHarmonic.GMSCM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The frozen cone field has a measurable version. The Brownian-pair cone
process and the ported cone-field measurability theorem supply it. -/
theorem aemeasurable_coneFieldOf {γ : ℝ} {X : Ω → DistC}
    {B B' : ℝ≥0 → Ω → ℝ} (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) :
    AEMeasurable (fun ω => MatedCRT.coneField (X ω)
      (MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) P := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  have hA := LQGCone.isConeProcess_motConeRadial (γ := γ) (α := γ) hB hB' hind
  have hm := MoTPort.ConeMeas2.aemeasurable_coneField hX hA
  refine hm.congr (ae_of_all _ fun ω => ?_)
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact LQGCone.coneField_eq_motConeField γ γ (X ω)
    (fun t => B t ω) (fun t => B' t ω) |>.symm

/-- The frozen γ-cone restriction is an actual deterministic smooth shift of a
normalized whole-plane GFF on every region compactly contained in the
punctured unit disk. -/
theorem exists_cone_local_shift {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P)
    (V : Opens ℂ) (hK : IsCompact (closure (V : Set ℂ)))
    (hV : closure (V : Set ℂ) ⊆ ball (0 : ℂ) 1 \ {0}) :
    ∃ (Xt : Ω → DistC) (φ : TestC), IsNormalizedWPGFF Xt P ∧
      Real.circleAverage (testCont φ) 0 1 = 0 ∧
      (∀ᵐ ω ∂P, restrictTo V (MatedCRT.coneField (X ω)
          (MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) =
        restrictTo V (addFun (Xt ω) (testCont φ))) := by
  obtain ⟨φ, hφ, hφavg, -⟩ := exists_cone_log_cutoff γ V hK hV
  obtain ⟨Xt, hXt, hdec⟩ :=
    GMCFacts.exists_cone_decomposition hγ.1 hX hB hB' hind hγ.2
  refine ⟨Xt, φ, hXt, hφavg, ?_⟩
  have hφli : LocallyIntegrable (testCont φ : ℂ → ℝ) volume :=
    (testCont φ).continuous.locallyIntegrable
  filter_upwards [hdec] with ω ⟨g, hfield, _, hgli, _, hg⟩
  have hloc : restrictTo V (ofFunC g) = restrictTo V (ofCont (testCont φ)) := by
    rw [restrictTo_ofFunC V hgli]
    change ofFunOn V g = restrictTo V (ofFunC (testCont φ))
    rw [restrictTo_ofFunC V hφli]
    ext ψ
    rw [ofFunOn_apply (hgli.locallyIntegrableOn _),
      ofFunOn_apply (hφli.locallyIntegrableOn _)]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ (V : Set ℂ)
    · have hz1 : ‖z‖ ≤ 1 := by
        have hzO := hV (subset_closure hz)
        have hzball : z ∈ ball (0 : ℂ) 1 := hzO.1
        have := (Metric.mem_ball.mp hzball)
        simpa [dist_zero_right] using le_of_lt this
      rw [hg z hz1]
      change ψ z * (γ * (-Real.log ‖z‖)) = ψ z * φ z
      rw [hφ z hz]
    · have hψ : ψ z = 0 := by
        exact image_eq_zero_of_notMem_tsupport (fun hs => hz (ψ.tsupport_subset hs))
      simp [hψ]
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  change restrictTo V (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω)
      (fun t => B' t ω)) = _
  rw [hfield, restrictTo_add, addFun, restrictTo_add, hloc]

end MatedCRTHarmonic.GMSCM

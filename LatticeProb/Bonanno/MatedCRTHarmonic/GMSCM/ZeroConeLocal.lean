/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.ZeroConeLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.AffineNormalization
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.ZeroConeMass

/-!
# The zero-cone field inside its unit circle

The zero-cone and the normalized whole-plane GFF used in the existing
zero-cone area comparison agree as distributions on every open set contained
in the unit disk. The area theorem keeps its local field lemma private, so
the restricted-field identity is stated here for the RN comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace LQGMetric
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.MoTPort.GFFBdry
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCM

private theorem zeroCone_local_field_eq
    (γ : ℝ) (X Xt : DistC) (b b' : ℝ≥0 → ℝ) (g : ℂ → ℝ)
    (hdec : CellScaling.coneFieldOf γ X b b' = Xt + ofFunC g)
    (hg : ∀ z : ℂ, ‖z‖ ≤ 1 → g z = γ * (-Real.log ‖z‖))
    (hgli : LocallyIntegrable g volume)
    (hliγ : LocallyIntegrable
      (fun z : ℂ => CellScaling.coneRadial γ γ b b' (-Real.log ‖z‖)) volume)
    (hli0 : LocallyIntegrable
      (fun z : ℂ => CellScaling.coneRadial γ 0 b b' (-Real.log ‖z‖)) volume)
    (V : Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    restrictTo V (CellScaling.coneField X (CellScaling.coneRadial γ 0 b b')) =
      restrictTo V Xt := by
  let fγ : ℂ → ℝ := fun z => CellScaling.coneRadial γ γ b b' (-Real.log ‖z‖)
  let f0 : ℂ → ℝ := fun z => CellScaling.coneRadial γ 0 b b' (-Real.log ‖z‖)
  have hfγ : LocallyIntegrable fγ volume := hliγ
  have hf0 : LocallyIntegrable f0 volume := hli0
  have hfun : ∀ z ∈ (V : Set ℂ), fγ z = f0 z + g z := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 (hV hz)).le
    have ht : 0 ≤ -Real.log ‖z‖ :=
      neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hz1)
    simp only [fγ, f0]
    rw [GMCFacts.coneRadial_of_nonneg γ γ b b' ht,
      GMCFacts.coneRadial_of_nonneg γ 0 b b' ht, hg z hz1]
    ring
  have hsum : ofFunOn V fγ = ofFunOn V f0 + ofFunOn V g := by
    calc
      ofFunOn V fγ = ofFunOn V (fun z => f0 z + g z) := by
        ext φ
        have hfg : LocallyIntegrable (fun z => f0 z + g z) volume := hf0.add hgli
        rw [ofFunOn_apply (hfγ.locallyIntegrableOn _),
          ofFunOn_apply (hfg.locallyIntegrableOn _)]
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ (V : Set ℂ)
        · rw [← hfun z hz]
        · have hφ : φ z = 0 :=
            image_eq_zero_of_notMem_tsupport fun hs => hz (φ.tsupport_subset hs)
          simp [hφ]
      _ = ofFunOn V f0 + ofFunOn V g :=
        Distribution.ofFun_add (hf0.locallyIntegrableOn _) (hgli.locallyIntegrableOn _)
  have hdecV : restrictTo V (CellScaling.lateralPart X) + ofFunOn V fγ =
      restrictTo V Xt + ofFunOn V g := by
    have h := congrArg (restrictTo V) hdec
    change restrictTo V (CellScaling.lateralPart X + ofFunC fγ) =
      restrictTo V (Xt + ofFunC g) at h
    simpa only [restrictTo_add, restrictTo_ofFunC V hfγ,
      restrictTo_ofFunC V hgli] using h
  change restrictTo V (CellScaling.lateralPart X + CellScaling.ofFunC f0) = restrictTo V Xt
  change restrictTo V (CellScaling.lateralPart X + ofFunC f0) = _
  rw [restrictTo_add, restrictTo_ofFunC V hf0]
  rw [hsum] at hdecV
  exact add_right_cancel (by simpa only [add_assoc] using hdecV)

/-- The actual frozen zero-cone field has a normalized whole-plane GFF version
on every open region contained in the unit disk. The identity is pathwise
almost surely on the same bundle sample space. -/
theorem IsMatingOfTreesCoupling.exists_zeroCone_localField_eq
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ)
    (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    ∃ Xt : Ω → DistC, IsNormalizedWPGFF Xt P ∧
      (fun ω => restrictTo V (MatedCRT.coneField (X₀ ω)
        (MatedCRT.coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))) =ᵐ[P]
        fun ω => restrictTo V (Xt ω) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Xt, hXt, hdec⟩ := GMCFacts.exists_cone_decomposition hγ.1
    D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀ hγ.2
  let Aγ : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ γ (fun s => B₀ s ω) (fun s => B₀' s ω) t
  let A0 : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t
  have hAγ : IsConeProcess γ (QuantumZipper.Qc γ) Aγ P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hA0 : IsConeProcess 0 (QuantumZipper.Qc γ) A0 P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hliγ := MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hAγ
  have hli0 := MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA0
  refine ⟨Xt, hXt, ?_⟩
  filter_upwards [hdec, hliγ, hli0] with ω hωdec hωγ hω0
  obtain ⟨g, hfield, -, hgli, -, hg⟩ := hωdec
  have hprofγ : LocallyIntegrable
      (fun z : ℂ => CellScaling.coneRadial γ γ
        (fun s => B₀ s ω) (fun s => B₀' s ω) (-Real.log ‖z‖)) volume := by
    simpa only [LQGCone.coneRadial_eq_Q_add_motConeRadial,
      CellScaling.lqgQ, QuantumZipper.Qc] using hωγ
  have hprof0 : LocallyIntegrable
      (fun z : ℂ => CellScaling.coneRadial γ 0
        (fun s => B₀ s ω) (fun s => B₀' s ω) (-Real.log ‖z‖)) volume := by
    simpa only [LQGCone.coneRadial_eq_Q_add_motConeRadial,
      CellScaling.lqgQ, QuantumZipper.Qc] using hω0
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact zeroCone_local_field_eq γ (X₀ ω) (Xt ω)
    (fun s => B₀ s ω) (fun s => B₀' s ω) g hfield hg hgli hprofγ hprof0 V hV

end MatedCRTHarmonic.GMSCM

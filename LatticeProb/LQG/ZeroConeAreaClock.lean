import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OCurveScale
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-! # Area clocks for the zero-cone curve -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
open LQGMetric MatedCRTHarmonic Metric

namespace LatticeProb

/-- The zero-cone curve and its rescaling are the area-clock evaluations of
its Lebesgue-parametrized curve and the corresponding dilation. -/
theorem zeroCone_ae_area_clock
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {b : ℝ} (hb : 0 < b)
    (W : Ω → C(ℝ, ℝ))
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ 0
      (fun s => B₀ s ω) (fun s => B₀' s ω) t) :
    ∀ᵐ ω ∂P,
      let y := γ⁻¹ * Real.log b
      let R := Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) y (W ω))
      let h := ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω)
      let h' := ConeScaling.fieldOf (affineComp R 0 (CellScaling.lateralPart (X₀ ω)))
        (ConeScaling.radShift (CellScaling.lqgQ γ) y (W ω))
      (⇑(η₀ ω) : ℝ → ℂ) = (fun t => CellScaling.JointScalingO.parEval γ h (ηL ω) t) ∧
      (⇑(CellScaling.coneRescaleCurve R b (η₀ ω)) : ℝ → ℂ) =
        (fun t => CellScaling.JointScalingO.parEval γ h'
          (CellScaling.JointScalingO.dilCurve R (ηL ω)) t) := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  have hQ0 : 0 < CellScaling.lqgQ γ := IGLaw.lqgQ_pos' hγ.1
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by
    dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  have hQc : 0 < QuantumZipper.Qc γ := hQ ▸ hQ0
  have hXA := MesoModel.FrozenIdentities.indepFun_motConeRadial_of_indep γ 0
    hC.bm_B₀ hC.bm_B₀' hC.indep_cone₀.1
  have hvague := LQGCone.ae_isVagueLimitC_coneField hγ.1 hγ.2 hQc hC.gff₀
    hC.bm_B₀ hC.bm_B₀' hC.indep_cone₀.2 hXA
  have hpos := LQGCone.ae_lqgArea_coneField_open_pos hγ.1 hγ.2 hQc hC.gff₀
    hC.bm_B₀ hC.bm_B₀' hC.indep_cone₀.2 hXA
  have hcov := IGLaw.ae_lqgArea_coneRescaleField_alpha (α := 0) hγ.1 hγ.2 hQ0
    hC.gff₀ hC.bm_B₀ hC.bm_B₀'
  have hA : MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial hC.bm_B₀ hC.bm_B₀' hC.indep_cone₀.2
  have hli : ∀ᵐ ω ∂P, LocallyIntegrable (ConeScaling.radialOf (W ω)) volume := by
    filter_upwards [hW, MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω hl
    refine hl.congr (Eventually.of_forall fun z => ?_)
    simp only [ConeScaling.radialOf, hω, LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
  filter_upwards [hW, hli, hC.areaParam₀, hvague, hpos, hcov] with ω hWω hliω hpar hv hp hc
  dsimp only
  obtain ⟨⟨φ, hφ0, hφ⟩, hareaμ⟩ := hpar
  let f := CellScaling.coneField (X₀ ω)
    (CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω))
  let R := Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b) (W ω))
  have hv' : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ f) μ := hv
  have harea : ∀ s t : ℝ, s ≤ t →
      CellScaling.lqgArea γ f (η₀ ω '' Icc s t) = ENNReal.ofReal (t - s) :=
    hareaμ _ (CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hv')
  have hR : 0 < R := Real.exp_pos _
  have hf : f = ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω) :=
    IGLaw.coneField_eq_fieldOf_alpha γ 0 (X₀ ω) hWω
  have hf' : CellScaling.coneRescaleField γ R b f =
      ConeScaling.fieldOf (affineComp R 0 (CellScaling.lateralPart (X₀ ω)))
        (ConeScaling.radShift (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b) (W ω)) := by
    rw [hf]
    exact ConeScaling.coneRescaleField_fieldOf γ b _ hliω
  have hc' : ∀ A : Set ℂ, CellScaling.lqgArea γ (CellScaling.coneRescaleField γ R b f) A =
      ENNReal.ofReal b⁻¹ * CellScaling.lqgArea γ f ((fun z => (R : ℂ) * z) '' A) :=
    fun A => hc R hR b hb A
  have hp' : 0 < CellScaling.lqgArea γ f (Metric.ball 0 R) :=
    hp _ isOpen_ball (nonempty_ball.2 hR)
  constructor
  · rw [← hf]
    exact CellScaling.JointScalingO.coe_eq_parEval_of_areaParam hv' hφ0 hφ harea
  · rw [← hf']
    exact CellScaling.JointScalingO.coe_coneRescaleCurve_eq_parEval hR hb hφ0 hφ harea hc' hp'

end LatticeProb

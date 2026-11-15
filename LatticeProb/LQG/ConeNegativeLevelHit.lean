import LatticeProb.Prob.DriftHitConvention
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero

/-! # Negative levels of a cone radial path -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- A negative last level of a cone radial path is the first passage time of
    Brownian motion with positive drift, expressed as an extended time. -/
theorem ae_ofReal_neg_lastLevel_eq_hitDrift {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {γ α : ℝ}
    (hαQ : α < CellScaling.lqgQ γ) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t)
    {y : ℝ} (hy : y < 0) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (-lastLevel (CellScaling.lqgQ γ) y (W ω)) =
      LatticeProb.hitDrift (fun t ω => -B t ω) (CellScaling.lqgQ γ - α) (-y) ω := by
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by
    dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  let A : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t
  have hA : MoTPort.IsConeProcess α (CellScaling.lqgQ γ) A P := by
    rw [hQ]
    exact LQGCone.isConeProcess_motConeRadial hB hB' hBB'
  have hd : 0 < CellScaling.lqgQ γ - α := sub_pos.mpr hαQ
  have hlast := ae_neg_lastLevel_eq_hitTime hA hαQ hy
  have hgood := CellScaling.ae_goodDrift (γ := γ) (α := α) hB.neg hd
  filter_upwards [hW, hlast, hgood] with ω hWω hlastω hgoodω
  have hset : {s : ℝ | W ω (-s) + CellScaling.lqgQ γ * s = y} =
      {s : ℝ | A (-s) ω = y} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    rw [hWω, LQGCone.coneRadial_eq_Q_add_motConeRadial]
    dsimp [A]
    constructor <;> intro h <;> linarith
  have hhit : ∃ t : ℝ≥0, -y ≤ -B t ω + (CellScaling.lqgQ γ - α) * t := by
    obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.1 hgoodω.tendsto_atTop) (-y)
    refine ⟨(max T 0).toNNReal, ?_⟩
    have h := hT (max T 0) (le_max_left _ _)
    simpa [CellScaling.coneDrift, Real.coe_toNNReal (max T 0) (le_max_right T 0)] using h
  rw [lastLevel, hset, hlastω]
  apply QuantumZipper.WedgeTrans.ofReal_hitTime_eq_hitDrift _ _ _ _ _ hhit
  intro t ht
  dsimp [A, LQGCone.motConeRadial]
  rw [CellScaling.coneRadial, ite_eq_left ht]
  ring

end MatedCRTHarmonic.ConeScaling

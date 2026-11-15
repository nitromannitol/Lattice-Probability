import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.LastLevel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial

/-! # Last levels of a cone radial path -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- Every nonnegative level of an α-cone radial path has a greatest time. -/
theorem ae_isGreatest_lastLevel_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α : ℝ} (hαQ : α < CellScaling.lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 ≤ a →
      IsGreatest {s : ℝ | W ω (-s) + CellScaling.lqgQ γ * s = a}
        (lastLevel (CellScaling.lqgQ γ) a (W ω)) := by
  have hd : 0 < CellScaling.lqgQ γ - α := by linarith
  filter_upwards [hW, hB.eval_zero_ae_eq_zero, CellScaling.ae_goodDrift hB' hd] with ω hWω hB0 hg
  intro a ha
  let X : ℝ → ℝ := fun s => W ω (-s) + CellScaling.lqgQ γ * s
  have hX : ∀ s, 0 < s → X s = CellScaling.coneDrift γ α (fun t => B' t ω)
      (CellScaling.lastZeroR (CellScaling.coneDrift γ α (fun t => B' t ω)) + s) := by
    intro s hs
    change W ω (-s) + CellScaling.lqgQ γ * s = _
    rw [hWω]
    exact CellScaling.coneLogRadial_of_pos γ α _ _ hs
  have hb : BddAbove {s : ℝ | X s = a} := hg.bddAbove_levelSet hX a
  have hc : IsClosed {s : ℝ | X s = a} := by
    apply isClosed_eq _ continuous_const
    dsimp [X]
    fun_prop
  have hn : {s : ℝ | X s = a}.Nonempty := by
    rcases ha.eq_or_lt with rfl | ha'
    · refine ⟨0, ?_⟩
      simp only [X, hWω]
      simp [CellScaling.coneRadial, hB0]
    · obtain ⟨hp, hv⟩ := hg.lastLevel_spec hX ha'
      refine ⟨sSup {s : ℝ | X s = a}, ?_⟩
      change X (sSup {s : ℝ | X s = a}) = a
      rw [hX _ hp]
      exact hv
  exact hc.isGreatest_csSup hn hb

end MatedCRTHarmonic.ConeScaling

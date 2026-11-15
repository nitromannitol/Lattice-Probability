import LatticeProb.LQG.ConeLastLevelAttainment

/-! # All last levels of a cone radial path -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

/-- Every real level of an α-cone radial path has a greatest time. -/
theorem ae_isGreatest_lastLevel {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α : ℝ} (hαQ : α < CellScaling.lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    {W : Ω → C(ℝ, ℝ)}
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ α
      (fun s => B s ω) (fun s => B' s ω) t) :
    ∀ᵐ ω ∂P, ∀ a : ℝ,
      IsGreatest {s : ℝ | W ω (-s) + CellScaling.lqgQ γ * s = a}
        (lastLevel (CellScaling.lqgQ γ) a (W ω)) := by
  have hd : 0 < CellScaling.lqgQ γ - α := sub_pos.mpr hαQ
  filter_upwards [hW, hB.eval_zero_ae_eq_zero,
    CellScaling.ae_goodDrift (γ := γ) (α := α) hB.neg hd,
    CellScaling.ae_goodDrift (γ := γ) (α := α) hB' hd,
    ae_isGreatest_lastLevel_nonneg hαQ hB hB' hW] with ω hWω hB0 hminus hplus hnonneg
  intro a
  by_cases ha : 0 ≤ a
  · exact hnonneg a ha
  · have ha' : a < 0 := lt_of_not_ge ha
    let X : ℝ → ℝ := fun s => W ω (-s) + CellScaling.lqgQ γ * s
    have hX : ∀ s, 0 < s → X s = CellScaling.coneDrift γ α (fun t => B' t ω)
        (CellScaling.lastZeroR (CellScaling.coneDrift γ α (fun t => B' t ω)) + s) := by
      intro s hs
      change W ω (-s) + CellScaling.lqgQ γ * s = _
      rw [hWω]
      exact CellScaling.coneLogRadial_of_pos γ α _ _ hs
    have hb : BddAbove {s : ℝ | X s = a} := hplus.bddAbove_levelSet hX a
    have hc : Continuous X := by dsimp [X]; fun_prop
    have hclosed : IsClosed {s : ℝ | X s = a} := isClosed_eq hc continuous_const
    have hzero : X 0 = 0 := by
      simp [X, hWω, CellScaling.coneRadial, hB0]
    obtain ⟨T, hT⟩ := (tendsto_atTop_atTop.1 hminus.tendsto_atTop) (-a)
    let t : ℝ := max T 0
    have ht : 0 ≤ t := le_max_right _ _
    have hbound := hT t (le_max_left _ _)
    have hXt : X (-t) ≤ a := by
      dsimp [X]
      rw [hWω, CellScaling.coneRadial, ite_eq_left (by linarith : 0 ≤ -(-t))]
      simp only [neg_neg]
      dsimp [CellScaling.coneDrift] at hbound
      linarith
    have hn : {s : ℝ | X s = a}.Nonempty := by
      obtain ⟨s, hs, hval⟩ := intermediate_value_Icc (show -t ≤ 0 by linarith)
        hc.continuousOn (show a ∈ Set.Icc (X (-t)) (X 0) from ⟨hXt, by linarith⟩)
      exact ⟨s, hval⟩
    exact hclosed.isGreatest_csSup hn hb

end MatedCRTHarmonic.ConeScaling

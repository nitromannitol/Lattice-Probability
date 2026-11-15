import LatticeProb.Prob.CompletedStoppedHistory
import LatticeProb.Prob.AELeSigma
import LatticeProb.Prob.ConditionalTrialHistory

/-! # Conditional bounds for almost surely included histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- Conditioning on a larger sigma algebra agrees with conditioning on a smaller one
when each event of the larger algebra has an almost surely equal representative in
the smaller one. -/
theorem condExp_ae_eq_of_aeLeSigma
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {F G : MeasurableSpace Ω} (hFG : F ≤ G) (hG : G ≤ m)
    (hGF : AELeSigma G F μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | F] =ᵐ[μ] μ[f | G] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hG hf
    (fun _ _ _ => integrable_condExp.integrableOn) ?_
    (stronglyMeasurable_condExp.mono hFG).aestronglyMeasurable
  intro A hA _
  obtain ⟨B, hB, hAB⟩ := hGF A hA
  calc
    ∫ ω in A, μ[f | F] ω ∂μ = ∫ ω in B, μ[f | F] ω ∂μ := setIntegral_congr_set hAB
    _ = ∫ ω in B, f ω ∂μ := setIntegral_condExp (hFG.trans hG) hf hB
    _ = ∫ ω in A, f ω ∂μ := (setIntegral_congr_set hAB).symm

/-- A conditional lower bound passes to a history included almost surely in the
conditioning sigma algebra. -/
theorem condExp_const_le_of_aeLeSigma
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {H G : MeasurableSpace Ω} (hH : H ≤ m) (hG : G ≤ m)
    (hHG : AELeSigma H G μ) {f : Ω → ℝ} (hf : Integrable f μ) {p : ℝ}
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[f | G] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[f | H] ω := by
  have hjoin : AELeSigma (G ⊔ H) G μ :=
    AELeSigma.sup (AELeSigma.of_le le_rfl) hHG
  have heq := condExp_ae_eq_of_aeLeSigma (μ := μ) (f := f)
    (le_sup_left : G ≤ G ⊔ H) (sup_le hG hH) hjoin hf
  have hp' : ∀ᵐ ω ∂μ, p ≤ μ[f | G ⊔ H] ω := by
    filter_upwards [hp, heq] with ω hpω heqω
    exact heqω ▸ hpω
  have hmono := condExp_mono (m := H) (integrable_const p)
    (integrable_condExp (f := f)) hp'
  have htower := condExp_condExp_of_le (μ := μ) (f := f)
    (le_sup_right : H ≤ G ⊔ H) (sup_le hG hH)
  filter_upwards [hmono, htower] with ω hω heqω
  simpa only [condExp_const hH, heqω] using hω

/-- Under strict separation, a conditional bound given a later clock and stopped
path passes to any ambient-measurable subhistory of the completed stopping history. -/
theorem completed_stopped_history_condExp_const_le_of_lt
    {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (S T : Ω → ℝ≥0∞) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hS : IsStoppingTime (completedFiltration (natFiltration X hm) μ) S)
    (hST : ∀ᵐ ω ∂μ, S ω < T ω)
    {H : MeasurableSpace Ω} (hH : H ≤ m)
    (hHS : H ≤ hS.measurableSpace)
    (hG : MeasurableSpace.comap
      (fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))) inferInstance ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) {p : ℝ}
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[f | MeasurableSpace.comap
      (fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))) inferInstance] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[f | H] ω := by
  apply condExp_const_le_of_aeLeSigma (m := m)
    (μ := μ) (f := f) (p := p) hH hG ?_ hf hp
  intro A hA
  obtain ⟨B, hB, hAB⟩ :=
    @completed_stopped_history_representative_of_lt Ω m d X hm hc S T μ hS hST A (hHS A hA)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hAB] with ω hω
  exact propext hω

end LatticeProb

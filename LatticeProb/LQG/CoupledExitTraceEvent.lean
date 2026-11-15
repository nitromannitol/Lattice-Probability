import LatticeProb.LQG.CoupledExitTraceObservation

/-! # Events of observed exit traces -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- A Borel predicate of the real exit trace has a representative measurable
in the stopped-path and clock observation. -/
theorem aeEventIn_coupled_real_prefix_trace
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (r : ℝ) (F : Set ℂ → Prop)
    (hF : MeasurableSet {K : NonemptyCompacts ℂ | F (K : Set ℂ)}) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
    let v := fun ω => stoppedPath (T ω) (w ω)
    AEEventIn P (MeasurableSpace.comap (fun ω => (v ω, T ω)) inferInstance)
      {ω | F (ηL ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ ¬ ηL ω '' Icc 0 t ⊆ ball 0 r}))} := by
  dsimp only
  refine ⟨{ω | F (compactPathPrefix
    (stoppedPath (openExitTime (fun t (_ : Unit) => ηL ω t) (ball 0 r) ())
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩)
    (openExitTime (fun t (_ : Unit) => ηL ω t) (ball 0 r) ()).toNNReal : Set ℂ)}, ?_, ?_⟩
  · exact measurable_compact_prefix_from_observation _ _ hF
  · filter_upwards [ae_coupled_exit_trace_from_observation D r] with ω hω
    exact congrArg F hω.symm

/-- If the observation is ambient measurable, the real trace event belongs to
the ambient measure completion. -/
theorem nullMeasurableSet_coupled_real_prefix_trace
    {γ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (r : ℝ) (F : Set ℂ → Prop)
    (hF : MeasurableSet {K : NonemptyCompacts ℂ | F (K : Set ℂ)})
    (hobs : let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
        ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
      let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
      MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ≤ mΩ) :
    NullMeasurableSet
      {ω | F (ηL ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ ¬ ηL ω '' Icc 0 t ⊆ ball 0 r}))} P := by
  obtain ⟨S, hS, hEq⟩ := aeEventIn_coupled_real_prefix_trace D r F hF
  exact (hobs _ hS).nullMeasurableSet.congr hEq.symm

end LatticeProb.LQG

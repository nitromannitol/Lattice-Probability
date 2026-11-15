import LatticeProb.LQG.CoupledExitTraceEvent
import LatticeProb.Prob.BrownianOpenExitStopping

/-! # Ambient measurability of exit-trace observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- The stopped path and its extended exit clock are measurable functions of
an ambient-measurable continuous complex path. -/
theorem measurable_complex_exit_observation
    {Ω : Type*} [MeasurableSpace Ω]
    {w : Ω → C(ℝ≥0, ℂ)} (hw : Measurable w) (U : Set ℂ) (hU : IsOpen U) :
    Measurable (fun ω =>
      (stoppedPath (openExitTime (fun t (_ : Unit) => w ω t) U ()) (w ω),
        openExitTime (fun t (_ : Unit) => w ω t) U ())) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm)
  have hT : Measurable (fun ω => openExitTime (fun t (_ : Unit) => w ω t) U ()) := by
    have h := measurable_openExitTime
      (B := fun t ω => e.symm (w ω t))
      (fun t => (e.symm.continuous.measurable.comp
        ((ContinuousMap.measurable_eval t).comp hw)).stronglyMeasurable)
      (fun ω => e.symm.continuous.comp (w ω).continuous)
      (hU.preimage e.continuous)
    have heq (ω : Ω) :
        openExitTime (fun t (_ : Unit) => e.symm (w ω t)) (e ⁻¹' U) () =
          openExitTime (fun t (_ : Unit) => w ω t) U () := by
      unfold openExitTime
      apply le_antisymm
      · apply le_iInf
        rintro ⟨t, ht⟩
        exact iInf_le_of_le ⟨t, by simpa only [mem_preimage, e.apply_symm_apply] using ht⟩ le_rfl
      · apply le_iInf
        rintro ⟨t, ht⟩
        exact iInf_le_of_le ⟨t, by simpa only [mem_preimage, e.apply_symm_apply] using ht⟩ le_rfl
    have heqfun : (openExitTime (fun t ω => e.symm (w ω t)) (e ⁻¹' U)) =
        (fun ω => openExitTime (fun t (_ : Unit) => w ω t) U ()) := funext heq
    rw [heqfun] at h
    exact h
  exact (continuous_stoppedPath.measurable.comp (hT.prodMk hw)).prodMk hT

/-- The exit observation of the coupled Lebesgue-time curve is ambient measurable. -/
theorem coupled_exit_observation_le
    {γ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (r : ℝ) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
    MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ≤ mΩ := by
  dsimp only
  apply Measurable.comap_le
  apply measurable_complex_exit_observation _ _ isOpen_ball
  exact (ContinuousMap.continuous_precomp
    (⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩ : C(ℝ≥0, ℝ))).measurable.comp
      D.measurable_curves.1

/-- A Borel predicate of the coupled real prefix-exit trace belongs to the
ambient measure completion. -/
theorem nullMeasurableSet_coupled_real_prefix_trace_of_measurable_curve
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (r : ℝ) (F : Set ℂ → Prop)
    (hF : MeasurableSet {K : NonemptyCompacts ℂ | F (K : Set ℂ)}) :
    NullMeasurableSet
      {ω | F (ηL ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ ¬ ηL ω '' Icc 0 t ⊆ ball 0 r}))} P :=
  nullMeasurableSet_coupled_real_prefix_trace D r F hF (coupled_exit_observation_le D r)

end LatticeProb.LQG

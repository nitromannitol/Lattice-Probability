import LatticeProb.LQG.StoppedPrefixFieldGerm
import LatticeProb.LQG.CoupledExitTraceAmbient

/-! # Field observations on a coupled exit prefix -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- On a measurable full-measure carrier, the coupled curve is rooted and its
ball-exit clock is finite; the stopped hull and collar field germs agree after
adjoining the stopped path and clock. -/
theorem exists_coupled_exit_field_germ_eq
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h : Ω → DistC) (r : ℝ) {p : ℝ} (hp : 0 < p) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
    let A : Set Ω := {ω | w ω 0 = 0 ∧ T ω ≠ ∞}
    MeasurableSet A ∧ (∀ᵐ ω ∂P, ω ∈ A) ∧
      ∃ a ψ : ℕ → TestC,
        (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
        let K := fun ω : A => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
        (∀ ω : A, (K ω : Set ℂ) = w ω '' Icc 0 (T ω).toNNReal) ∧
        (MeasurableSpace.comap (fun ω : A => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
          (⨅ n, localHullFieldSigma (fun ω : A => h ω) (fun ω => (K ω : Set ℂ)) n (a n) hp)) =
        (MeasurableSpace.comap (fun ω : A => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
          (⨅ k, MeasurableSpace.comap (collarFieldCode (fun ω : A => h ω) K localDenseTest ψ hp k) inferInstance)) := by
  dsimp only
  let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
    ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
  let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
  let A : Set Ω := {ω | w ω 0 = 0 ∧ T ω ≠ ∞}
  change MeasurableSet A ∧ (∀ᵐ ω ∂P, ω ∈ A) ∧ _
  have hw : Measurable w :=
    (ContinuousMap.continuous_precomp
      (⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩ : C(ℝ≥0, ℝ))).measurable.comp
        D.measurable_curves.1
  have hT : Measurable T := (measurable_complex_exit_observation hw _ isOpen_ball).snd
  have hA : MeasurableSet A :=
    ((measurableSet_singleton (0 : ℂ)).preimage
      ((ContinuousMap.measurable_eval 0).comp hw)).inter
      ((measurableSet_singleton (∞ : ℝ≥0∞)).preimage hT).compl
  refine ⟨hA, ?_, ?_⟩
  · filter_upwards [D.spaceFilling, ae_coupled_real_prefix_exit D] with ω hroot hexit
    exact ⟨hroot.2.2.1, (hexit r).1⟩
  · exact exists_stoppedPrefix_field_germ_eq (fun ω : A => h ω) (fun ω : A => w ω)
      (fun ω : A => T ω) 0 (fun ω => ω.property.1) (fun ω => ω.property.2) hp

end LatticeProb.LQG

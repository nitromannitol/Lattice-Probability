import LatticeProb.LQG.AmbientFieldHistory
import LatticeProb.LQG.CoupledExitTraceAmbient

/-! # Measurable stopped-curve field histories -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open LQGMetric.CONF MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- The two stopped-curve field histories have the same conditional
expectations when the field, clock and common history are ambient measurable. -/
theorem exists_condExp_coupled_stoppedPrefix_of_measurable
    {γ : ℝ} {Ω : Type} {m : MeasurableSpace Ω} {P : Measure[m] Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h : Ω → DistC) (hh : Measurable h) (T : Ω → ℝ≥0∞) (hT : Measurable T)
    {p : ℝ} (hp : 0 < p) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    ∃ a ψ : ℕ → TestC,
      (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
      let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
      ∀ (H : MeasurableSpace Ω), H ≤ m → ∀ (f : Ω → ℝ), Integrable f P →
        P[f | H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp] =ᵐ[P]
        P[f | H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance] := by
  let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
    ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
  have hw : Measurable w :=
    (ContinuousMap.continuous_precomp
      (⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩ : C(ℝ≥0, ℝ))).measurable.comp
        D.measurable_curves.1
  have hs : Measurable (fun ω => stoppedPath (T ω) (w ω)) :=
    continuous_stoppedPath.measurable.comp (hT.prodMk hw)
  have hK : Measurable (fun ω => compactPathPrefix (stoppedPath (T ω) (w ω))
      (T ω).toNNReal) := measurable_compactPathPrefix_toNNReal hs hT
  obtain ⟨a, ψ, ha, hψ, hcond⟩ :=
    exists_condExp_coupled_stoppedPrefix_hull_eq_collar D h T hp
  refine ⟨a, ψ, ha, hψ, ?_⟩
  dsimp only
  intro H hH f hf
  let : MeasurableSpace Ω := m
  obtain ⟨hHull, hCollar⟩ := joined_field_histories_le_ambient hh hK H hH a ψ hp
  exact hcond H hHull hCollar f hf

/-- For a fixed ball, the common stopped-path and exit-clock observation is
ambient measurable and the two field-history conditional expectations agree. -/
theorem exists_condExp_coupled_ballExit_of_measurable
    {γ : ℝ} {Ω : Type} {m : MeasurableSpace Ω} {P : Measure[m] Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h : Ω → DistC) (hh : Measurable h) (r : ℝ) {p : ℝ} (hp : 0 < p) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
    let H := MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance
    let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
    ∃ a ψ : ℕ → TestC,
      (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
      ∀ (f : Ω → ℝ), Integrable f P →
        P[f | H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp] =ᵐ[P]
        P[f | H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance] := by
  let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
    ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
  let T : Ω → ℝ≥0∞ := fun ω => openExitTime (fun t (_ : Unit) => w ω t) (ball 0 r) ()
  let H := MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance
  let : MeasurableSpace Ω := m
  have hH : H ≤ m := coupled_exit_observation_le D r
  have hT : Measurable T := measurable_snd.comp (measurable_iff_comap_le.mpr hH)
  obtain ⟨a, ψ, ha, hψ, hcond⟩ :=
    exists_condExp_coupled_stoppedPrefix_of_measurable D h hh T hT hp
  exact ⟨a, ψ, ha, hψ, hcond H hH⟩

end LatticeProb.LQG

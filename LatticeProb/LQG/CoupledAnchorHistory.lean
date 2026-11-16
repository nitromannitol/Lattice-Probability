import LatticeProb.LQG.AnchorCarrierHistory
import LatticeProb.LQG.StoppedPrefixAnchors
import LatticeProb.LQG.ReciprocalCollarAnchors
import LatticeProb.LQG.CoupledCurveExitAnchors

/-! # Field histories on stopped rooted curves -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open LQGMetric.CONF MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- The totalized stopped prefix contains the initial point for every clock. -/
theorem initial_mem_compact_stoppedPrefix (w : C(ℝ≥0, ℂ)) (T : ℝ≥0∞) :
    w 0 ∈ (compactPathPrefix (stoppedPath T w) T.toNNReal : Set ℂ) := by
  rw [coe_compactPathPrefix_eq_image_Icc]
  have h := Set.mem_image_of_mem (stoppedPath T w) (show (0 : ℝ≥0) ∈ Icc 0 T.toNNReal from ⟨le_rfl, zero_le⟩)
  simpa only [stoppedPath_apply, ENNReal.coe_zero, zero_min, ENNReal.toNNReal_zero] using h

/-- Fixed normalized anchors compare the field histories of a rooted stopped
prefix, provided both joined histories are ambient measurable. -/
theorem exists_condExp_stoppedPrefix_hull_eq_collar {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω} [IsFiniteMeasure μ]
    (h : Ω → DistC) (w : Ω → C(ℝ≥0, ℂ)) (T : Ω → ℝ≥0∞)
    (z : ℂ) (hw : ∀ᵐ ω ∂μ, w ω 0 = z) {p : ℝ} (hp : 0 < p) :
    ∃ a ψ : ℕ → TestC,
      (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
      let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
      ∀ (H : MeasurableSpace Ω)
        (_hHull : H ⊔ (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) ≤ m)
        (_hCollar : H ⊔ (⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance) ≤ m)
        (f : Ω → ℝ), Integrable f μ →
        μ[f | H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp] =ᵐ[μ]
        μ[f | H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance] := by
  obtain ⟨a, ha⟩ := exists_dyadicHull_anchors z
  obtain ⟨ψ, hψ⟩ := exists_reciprocal_collar_anchors z
  refine ⟨a, ψ, (fun n => (ha n).1), (fun k => (hψ k).1), ?_⟩
  dsimp only
  intro H hHull hCollar f hf
  apply condExp_hull_history_ae_eq_collar_history H h _ z a ψ
    (fun n => (ha n).1) (fun n ω hω => (ha n).2 _ hω)
    (fun k => (hψ k).1) (fun k ω hω => (hψ k).2 _ hω) hp
    ?_ hHull hCollar hf
  filter_upwards [hw] with ω hω
  rw [← hω]
  exact initial_mem_compact_stoppedPrefix (w ω) (T ω)

/-- The coupled Lebesgue-parametrized curve gives a full anchor carrier at
zero for every extended clock. -/
theorem ae_coupled_stoppedPrefix_contains_zero
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (T : Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, let w : C(ℝ≥0, ℂ) :=
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
      0 ∈ (compactPathPrefix (stoppedPath (T ω) w) (T ω).toNNReal : Set ℂ) := by
  filter_upwards [D.spaceFilling] with ω hω
  dsimp only
  have hv := initial_mem_compact_stoppedPrefix
    ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩ (T ω)
  change ηL ω 0 ∈ _ at hv
  simpa only [hω.2.2.1] using hv

/-- Conditional field histories agree for the rooted curve in the coupling,
with ambient measurability retained for each joined history. -/
theorem exists_condExp_coupled_stoppedPrefix_hull_eq_collar
    {γ : ℝ} {Ω : Type} {m : MeasurableSpace Ω} {P : Measure[m] Ω}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (h : Ω → DistC) (T : Ω → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    let w : Ω → C(ℝ≥0, ℂ) := fun ω =>
      ⟨fun t => ηL ω t, (ηL ω).continuous.comp NNReal.continuous_coe⟩
    ∃ a ψ : ℕ → TestC,
      (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
      let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
      ∀ (H : MeasurableSpace Ω)
        (_hHull : H ⊔ (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) ≤ m)
        (_hCollar : H ⊔ (⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance) ≤ m)
        (f : Ω → ℝ), Integrable f P →
        P[f | H ⊔ ⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp] =ᵐ[P]
        P[f | H ⊔ ⨅ k, MeasurableSpace.comap
          (collarFieldCode h K localDenseTest ψ hp k) inferInstance] := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  apply exists_condExp_stoppedPrefix_hull_eq_collar h _ T 0 ?_ hp
  filter_upwards [D.spaceFilling] with ω hω
  exact hω.2.2.1

end LatticeProb.LQG

import LatticeProb.LQG.CollarFixedOpenConverse
import LatticeProb.LQG.CoupledAnchorHistory

/-! # Fixed-open observations of stopped-prefix collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric
open SupercriticalConformalCovariance.TV MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- For a rooted stopped curve, fixed-open gated field observations and the
stopped curve and clock determine the dense collar observation at one scale.
The local path and phase measurability assumptions refer to the same field and
the actual open-containment gates of the stopped prefix. -/
theorem exists_measurable_stoppedPrefix_collarFieldCode_of_fixedOpenObservations
    {Ω : Type} [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (w : Ω → C(ℝ≥0, ℂ)) (T : Ω → ℝ≥0∞)
    (z : ℂ) (hz : ∀ ω, w ω 0 = z) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
    ∃ (ψ : ℕ → TestC) (hψ1 : ∫ x, ψ k x = 1)
      (V : ℕ → Opens ℂ) (hψV : ∀ n, tsupport (ψ k : ℂ → ℝ) ⊆ V n),
      (∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) ∧
      ∀ (m : MeasurableSpace Ω),
        letI : MeasurableSpace Ω := m
        Measurable (fun ω => stoppedPath (T ω) (w ω)) → Measurable T →
        (∀ n j, Measurable (({ω | (V n : Set ℂ) ⊆
          thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} : Set Ω).indicator
            (fun ω => localCountablePath (V n) (ψ k) (hψV n) hψ1 (h ω) j))) →
        (∀ n, Measurable (({ω | (V n : Set ℂ) ⊆
          thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} : Set Ω).indicator
            (fun ω => toIcoMod hp 0 (h ω (ψ k))))) →
        Measurable (collarFieldCode h K localDenseTest ψ hp k) := by
  dsimp only
  let K : Ω → NonemptyCompacts ℂ := fun ω =>
    compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
  have hzK : ∀ ω, z ∈ (K ω : Set ℂ) := by
    intro ω
    rw [← hz ω]
    exact initial_mem_compact_stoppedPrefix (w ω) (T ω)
  obtain ⟨ψ, hψ⟩ := exists_reciprocal_collar_anchors z
  have hψ1 := (hψ k).1
  have hψK : ∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ) :=
    fun ω => (hψ k).2 _ (hzK ω)
  obtain ⟨V, hψV, heq⟩ :=
    exists_collarFieldCode_comap_eq_fixedOpenCode h K ψ hp k hψ1 hψK
  refine ⟨ψ, hψ1, V, hψV, hψK, ?_⟩
  intro m
  let : MeasurableSpace Ω := m
  intro hstop hT hpath hphase
  have hK : Measurable K := measurable_compactPathPrefix_toNNReal hstop hT
  let E : ℕ → Set Ω := fun n => {ω | (V n : Set ℂ) ⊆
    thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_sigmaCompact_subset_thickening hK (isSigmaCompact_of_isOpen (V n).isOpen) _
  have hfixed : Measurable (collarFixedOpenCode h K (ψ k) hψ1 hp k V hψV) := by
    apply hK.prodMk
    apply measurable_pi_iff.mpr
    intro n
    exact (measurable_const.indicator (hE n)).prodMk
      ((measurable_pi_iff.mpr (hpath n)).prodMk (hphase n))
  exact (measurable_iff_comap_le.mpr (heq.le.trans hfixed.comap_le))

end LatticeProb.LQG

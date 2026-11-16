import LatticeProb.LQG.CollarRandomSupportReadout

/-! # Support-gated collar phases -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- The phase of a unit-integral test is observable when its support lies in
    the collar, and is set to zero otherwise. -/
theorem measurable_support_indicator_phase_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (ρ : TestC) (hρ1 : ∫ z, ρ z = 1) :
    let E := {ω | tsupport (ρ : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (E.indicator (fun ω => toIcoMod hp 0 (h ω ρ))) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  let E : Set Ω := {ω | tsupport (ρ : ℂ → ℝ) ⊆
    thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
  have hK : Measurable K :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).fst
  have hE : MeasurableSet E :=
    measurableSet_compact_subset_thickening hK ρ.hasCompactSupport.isCompact _
  have hC : Measurable (E.indicator (fun ω => h ω ρ - h ω (ψ k))) := by
    simpa only [hρ1, one_mul] using
      measurable_support_indicator_centered_pairing_of_collarFieldCode h K ψ hp k ρ
  have hphase : Measurable (fun ω => toIcoMod hp 0 (h ω (ψ k))) :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).snd.snd
  have hm := ((LatticeProb.measurable_toIcoMod_zero hp).comp (hphase.add hC)).indicator hE
  have heq : E.indicator (fun ω => toIcoMod hp 0 (h ω ρ)) =
      E.indicator (fun ω => toIcoMod hp 0 (toIcoMod hp 0 (h ω (ψ k)) +
        E.indicator (fun x => h x ρ - h x (ψ k)) ω)) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω]
      apply (toIcoMod_eq_toIcoMod hp).mpr
      refine ⟨-toIcoDiv hp 0 (h ω (ψ k)), ?_⟩
      rw [neg_zsmul]
      have hx := toIcoMod_add_toIcoDiv_zsmul hp 0 (h ω (ψ k))
      linarith
    · simp only [indicator_of_notMem hω]
  change Measurable (E.indicator (fun ω => toIcoMod hp 0 (h ω ρ)))
  rw [heq]
  exact hm

end LatticeProb.LQG

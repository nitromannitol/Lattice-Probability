import LatticeProb.LQG.CollarIndexedCode
import LatticeProb.LQG.CollarRandomSupportPhase

/-! # Change of anchor for collar observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- At a fixed scale, changing to a unit-integral anchor supported in every
collar preserves measurability of all indexed collar observations. -/
theorem measurable_collarFieldCode_of_anchor_supported {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ χ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ)
    (hχ : ∫ z, χ k z = 1)
    (hsupp : ∀ ω, tsupport (χ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (collarFieldCode h K φ χ hp k) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hK : Measurable K :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).fst
  have hEχ : {ω | tsupport (χ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact hsupp ω
  have hdiff : Measurable (fun ω => h ω (χ k) - h ω (ψ k)) := by
    have hm := measurable_support_indicator_centered_pairing_of_collarFieldCode
      h K ψ hp k (χ k)
    simpa only [hEχ, indicator_univ, hχ, one_mul] using hm
  have hphase : Measurable (fun ω => toIcoMod hp 0 (h ω (χ k))) := by
    have hm := measurable_support_indicator_phase_of_collarFieldCode h K ψ hp k (χ k) hχ
    simpa only [hEχ, indicator_univ] using hm
  have hcoordinates : Measurable (fun ω i =>
      let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
      (E.indicator (fun _ => (1 : ℝ)) ω,
        E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (χ k)) ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    have hE : MeasurableSet E :=
      measurableSet_compact_subset_thickening hK (φ i).hasCompactSupport.isCompact _
    have hold := measurable_support_indicator_centered_pairing_of_collarFieldCode
      h K ψ hp k (φ i)
    have hnew : Measurable (E.indicator (fun ω =>
        h ω (φ i) - (∫ z, φ i z) * h ω (χ k))) := by
      have heq : E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (χ k)) =
          E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ k)) -
          E.indicator (fun ω => (∫ z, φ i z) * (h ω (χ k) - h ω (ψ k))) := by
        funext ω
        by_cases hω : ω ∈ E
        · simp only [indicator_of_mem hω, Pi.sub_apply]
          ring
        · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_self]
      rw [heq]
      exact hold.sub ((measurable_const.mul hdiff).indicator hE)
    exact (measurable_const.indicator hE).prodMk hnew
  exact hK.prodMk (hcoordinates.prodMk hphase)

/-- The induced σ-algebra comparison for a supported new anchor. -/
theorem comap_collarFieldCode_le_of_anchor_supported {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ χ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ)
    (hχ : ∫ z, χ k z = 1)
    (hsupp : ∀ ω, tsupport (χ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    MeasurableSpace.comap (collarFieldCode h K φ χ hp k) inferInstance ≤
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance :=
  (measurable_collarFieldCode_of_anchor_supported h K φ ψ χ hp k hχ hsupp).comap_le

/-- Supported unit-integral anchors give the same dense collar σ-algebra. -/
theorem comap_collarFieldCode_eq_of_anchors_supported {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ χ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ)
    (hψ : ∫ z, ψ k z = 1) (hχ : ∫ z, χ k z = 1)
    (hsψ : ∀ ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (hsχ : ∀ ω, tsupport (χ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) :
    MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance =
      MeasurableSpace.comap (collarFieldCode h K localDenseTest χ hp k) inferInstance :=
  le_antisymm
    (comap_collarFieldCode_le_of_anchor_supported h K localDenseTest χ ψ hp k hψ hsψ)
    (comap_collarFieldCode_le_of_anchor_supported h K localDenseTest ψ χ hp k hχ hsχ)

end LatticeProb.LQG

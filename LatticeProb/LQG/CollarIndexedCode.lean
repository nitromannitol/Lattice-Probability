import LatticeProb.LQG.CollarRandomSupportReadout

/-! # Indexed collar observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- Every indexed collar code is measurable from the dense-test code at the
same scale, with the same anchor. -/
theorem measurable_collarFieldCode_of_localDenseTest {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (collarFieldCode h K φ ψ hp k) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hK : Measurable K :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).fst
  have hphase : Measurable (fun ω => toIcoMod hp 0 (h ω (ψ k))) :=
    (comap_measurable (collarFieldCode h K localDenseTest ψ hp k)).snd.snd
  have hcoordinates : Measurable (fun ω i =>
      let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
      (E.indicator (fun _ => (1 : ℝ)) ω,
        E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ k)) ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hE : MeasurableSet {ω | tsupport (φ i : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} :=
      measurableSet_compact_subset_thickening hK (φ i).hasCompactSupport.isCompact _
    exact (measurable_const.indicator hE).prodMk
      (measurable_support_indicator_centered_pairing_of_collarFieldCode h K ψ hp k (φ i))
  exact hK.prodMk (hcoordinates.prodMk hphase)

/-- The σ-algebra of any indexed collar code is contained in the σ-algebra
of the dense-test collar code at the same scale and anchor. -/
theorem comap_collarFieldCode_le_localDenseTest {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (φ : I → TestC)
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    MeasurableSpace.comap (collarFieldCode h K φ ψ hp k) inferInstance ≤
      MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance :=
  (measurable_collarFieldCode_of_localDenseTest h K φ ψ hp k).comap_le

end LatticeProb.LQG

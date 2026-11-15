import LatticeProb.LQG.HullGatedRestriction
import LatticeProb.Topology.CompactThickeningEvent

/-! # Selected collars and gated field restrictions -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Compact containment in a collar selected by a measurable natural index is
measurable whenever the compact set itself is measurable. -/
theorem measurableSet_compact_subset_selected_thickening {Ω X : Type*}
    [MetricSpace X] [MeasurableSpace Ω] [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)] {K : Ω → NonemptyCompacts X} (hK : Measurable K)
    {f : Ω → ℕ} (hf : Measurable f) {S : Set X} (hS : IsCompact S) :
    MeasurableSet {ω | S ⊆ thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set X)} := by
  have heq : {ω | S ⊆ thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set X)} =
      ⋃ k : ℕ, {ω | f ω = k} ∩
        {ω | S ⊆ thickening (1 / ((k : ℝ) + 1)) (K ω : Set X)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨f ω, rfl, h⟩
    · rintro ⟨k, hk, h⟩
      simpa only [hk] using h
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    (measurableSet_singleton k |>.preimage hf).inter
      (measurableSet_compact_subset_thickening hK hS _)

/-- Gated centered field observations on a selected collar are measurable from
an enclosing hull and a supported unit-integral anchor. -/
theorem measurable_selected_collar_restriction_of_localHullFieldSigma
    {Ω : Type} {I : Type*} [MeasurableSpace (NonemptyCompacts ℂ)]
    [BorelSpace (NonemptyCompacts ℂ)] (h : Ω → DistC) (A : Ω → Set ℂ)
    (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (K : Ω → NonemptyCompacts ℂ) (hK : Measurable[setSigma A] K)
    (f : Ω → ℕ) (hf : Measurable[setSigma A] f)
    (hcollar : ∀ ω, thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ) ⊆
      interior (dyadicHull n (A ω)))
    (φ : I → TestC) (ψ : TestC) (hψ : ∫ z, ψ z = 1)
    (hsupp : ∀ ω, tsupport (ψ : ℂ → ℝ) ⊆
      thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    Measurable[localHullFieldSigma h A n ψ hp] (fun (ω : Ω) =>
      ((fun i =>
        let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
          thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
        (E.indicator (fun _ => (1 : ℝ)) ω,
          E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω ψ) ω)),
       toIcoMod hp 0 (h ω ψ))) := by
  let : MeasurableSpace Ω := setSigma A
  let E : I → Set Ω := fun i => {ω | tsupport (φ i : ℂ → ℝ) ⊆
    thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
  apply measurable_gated_restriction_of_localHullFieldSigma h A hA n φ ψ hψ E
  · intro i
    exact measurableSet_compact_subset_selected_thickening hK hf (φ i).hasCompactSupport.isCompact
  · intro i ω hω
    exact hω.trans (hcollar ω)
  · intro ω
    exact (hsupp ω).trans (hcollar ω)

end LatticeProb.LQG

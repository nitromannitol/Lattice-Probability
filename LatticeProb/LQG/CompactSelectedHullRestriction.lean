import LatticeProb.LQG.EffrosCompactEncoding
import LatticeProb.LQG.MeasurableHullCollar
import LatticeProb.LQG.SelectedCollarGates

/-! # Measurable restrictions to selected compact-set collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A compact random set has a measurable collar inside each dyadic hull.
Support-gated centered field observations on that collar are measurable from
the hull observation whenever the anchor is uniformly supported in the hull. -/
theorem exists_measurable_collar_hull_restriction {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (n : ℕ)
    (φ : I → TestC) (ψ : TestC) (hψ : ∫ z, ψ z = 1)
    (hsupp : ∀ ω, tsupport (ψ : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ f : Ω → ℕ, Measurable[setSigma (fun ω => (K ω : Set ℂ))] f ∧
      (∀ ω, thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ) ⊆
        interior (dyadicHull n (K ω : Set ℂ))) ∧
      Measurable[localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n ψ hp]
        (fun (ω : Ω) =>
          ((fun i =>
            let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
              thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
            (E.indicator (fun _ => (1 : ℝ)) ω,
              E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω ψ) ω)),
           toIcoMod hp 0 (h ω ψ))) := by
  let A : Ω → Set ℂ := fun ω => K ω
  have hcompact : ∀ ω, IsCompact (A ω) := fun ω => (K ω).isCompact
  have hK : Measurable[setSigma A] K :=
    measurable_compactEncoding_of_setSigma A K (fun _ => rfl)
  obtain ⟨f, hf, hcollar⟩ :=
    exists_measurable_thickening_subset_interior_dyadicHull A hcompact n
  refine ⟨f, hf, hcollar, ?_⟩
  let E : I → Set Ω := fun i => {ω | tsupport (φ i : ℂ → ℝ) ⊆
    thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
  apply measurable_gated_restriction_of_localHullFieldSigma h A
    (fun ω => (hcompact ω).isBounded) n φ ψ hψ E
  · intro i
    let : MeasurableSpace Ω := setSigma A
    exact measurableSet_compact_subset_selected_thickening hK hf
      (φ i).hasCompactSupport.isCompact
  · intro i ω hω
    exact hω.trans (hcollar ω)
  · exact hsupp

end LatticeProb.LQG

import LatticeProb.LQG.SelectedAnchorCollarRestriction
import LatticeProb.LQG.DyadicHullAnchors
import LatticeProb.LQG.MeasurableHullCollar
import LatticeProb.LQG.HullAnchorFamilyReduction
import LatticeProb.LQG.EffrosCompactEncoding
import LatticeProb.MeasureTheory.SelectedScaleGerm

/-! # Germs of compact-collar field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A collar observation consists of the compact set, the support gates,
centered field pairings, and the phase of a unit-integral anchor. -/
def collarFieldCode {Ω : Type} {I : Type*}
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (k : ℕ) (ω : Ω) : NonemptyCompacts ℂ × (I → ℝ × ℝ) × ℝ :=
  (K ω, (fun i =>
    let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    (E.indicator (fun _ => (1 : ℝ)) ω,
      E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ k)) ω)),
    toIcoMod hp 0 (h ω (ψ k)))

/-- The germ of fixed-scale collar codes is observed at each enclosing hull,
when each scale has a deterministic anchor supported in that collar. -/
theorem iInf_collarFieldCode_le_localHullFieldSigma {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (n : ℕ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ)) (φ : I → TestC)
    (ψ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hsupp : ∀ k ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    ∃ a : TestC, (∫ x, a x) = 1 ∧
      (∀ ω, tsupport (a : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ))) ∧
      (⨅ k, MeasurableSpace.comap (collarFieldCode h K φ ψ hp k) inferInstance) ≤
        localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n a hp := by
  let A : Ω → Set ℂ := fun ω => K ω
  have hcompact : ∀ ω, IsCompact (A ω) := fun ω => (K ω).isCompact
  have hbounded : ∀ ω, Bornology.IsBounded (A ω) := fun ω => (hcompact ω).isBounded
  obtain ⟨a, ha⟩ := exists_dyadicHull_anchors z
  have hasupp : ∀ ω, tsupport (a n : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) :=
    fun ω => (ha n).2 _ (hz ω)
  obtain ⟨f, hf, hcollar⟩ := exists_measurable_thickening_subset_interior_dyadicHull A hcompact n
  have hK : Measurable[setSigma A] K :=
    measurable_compactEncoding_of_setSigma A K (fun _ => rfl)
  have hm := measurable_selected_anchor_collar_restriction h A hbounded n K hK
    f hf hcollar φ ψ hψ f hf (fun ω => hsupp (f ω) ω) hp
  have hle : (⨆ k, localHullFieldSigma h A n (ψ k) hp) ≤
      localHullFieldSigma h A n (a n) hp :=
    iSup_le fun k => localHullFieldSigma_le_of_anchor_supported h A hbounded n
      (a n) (ψ k) (ha n).1 (hψ k) hasupp hp
  have hset : setSigma A ≤ localHullFieldSigma h A n (a n) hp :=
    (le_sup_left : setSigma A ≤ hullSigma0 h A n).trans le_sup_left
  have hselected : Measurable[localHullFieldSigma h A n (a n) hp]
      (fun ω => collarFieldCode h K φ ψ hp (f ω) ω) := by
    exact (hK.mono hset le_rfl).prodMk (hm.mono hle le_rfl)
  exact ⟨a n, (ha n).1, hasupp,
    LatticeProb.iInf_comap_le_of_measurable_selected _ _ f (hf.mono hset le_rfl) hselected⟩

end LatticeProb.LQG

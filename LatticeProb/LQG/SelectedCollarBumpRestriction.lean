import LatticeProb.LQG.SelectedAnchorCollarRestriction
import LatticeProb.LQG.MeasurableCollarAnchor
import LatticeProb.LQG.HullAnchorFamilyReduction
import LatticeProb.LQG.EffrosCompactEncoding

/-! # Selected bump observations on compact-set collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A common point gives a fixed hull anchor and a measurable collar-supported
bump whose centered observations and phase are measurable from that anchor. -/
theorem exists_selected_collar_bump_restriction {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (n : ℕ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ)) (φ : I → TestC)
    {p : ℝ} (hp : 0 < p) :
    ∃ a : TestC, (∫ x, a x) = 1 ∧
      (∀ ω, tsupport (a : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ))) ∧
      ∃ f g : Ω → ℕ,
        Measurable[setSigma (fun ω => (K ω : Set ℂ))] f ∧
        Measurable[setSigma (fun ω => (K ω : Set ℂ))] g ∧
        (∀ ω, thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ) ⊆
          interior (dyadicHull n (K ω : Set ℂ))) ∧
        (∀ ω, tsupport (bumpTest (g ω) z : ℂ → ℝ) ⊆
          thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)) ∧
        Measurable[localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n a hp]
          (fun (ω : Ω) =>
            ((fun i =>
              let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
                thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
              (E.indicator (fun _ => (1 : ℝ)) ω,
                E.indicator (fun ω => h ω (φ i) -
                  (∫ x, φ i x) * h ω (bumpTest (g ω) z)) ω)),
             toIcoMod hp 0 (h ω (bumpTest (g ω) z)))) := by
  let A : Ω → Set ℂ := fun ω => K ω
  have hcompact : ∀ ω, IsCompact (A ω) := fun ω => (K ω).isCompact
  have hbounded : ∀ ω, Bornology.IsBounded (A ω) := fun ω => (hcompact ω).isBounded
  obtain ⟨a, ha⟩ := exists_dyadicHull_anchors z
  have hasupp : ∀ ω, tsupport (a n : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) :=
    fun ω => (ha n).2 _ (hz ω)
  obtain ⟨f, g, hf, hg, hfg⟩ := exists_measurable_collar_bump A hcompact n z hz
  have hK : Measurable[setSigma A] K :=
    measurable_compactEncoding_of_setSigma A K (fun _ => rfl)
  have hbump : ∀ k, ∫ x, bumpTest k z x = 1 := fun k => GFFLaw.integral_bumpTest k z
  have hm := measurable_selected_anchor_collar_restriction h A hbounded n K hK
    f hf (fun ω => (hfg ω).1) φ (fun k => bumpTest k z) hbump g hg
    (fun ω => (hfg ω).2.2) hp
  have hle : (⨆ k, localHullFieldSigma h A n (bumpTest k z) hp) ≤
      localHullFieldSigma h A n (a n) hp :=
    iSup_le fun k => localHullFieldSigma_le_of_anchor_supported h A hbounded n
      (a n) (bumpTest k z) (ha n).1 (hbump k) hasupp hp
  exact ⟨a n, (ha n).1, hasupp, f, g, hf, hg, fun ω => (hfg ω).1,
    fun ω => (hfg ω).2.2, hm.mono hle le_rfl⟩

end LatticeProb.LQG

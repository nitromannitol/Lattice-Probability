import LatticeProb.LQG.SelectedHullCenteredPairing

/-! # Measurable selection of jointly gated field coordinates -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A selected phase, gated by containment of both supports, is observable in
    the join of the local phase sigma algebras. -/
theorem measurable_selected_hull_joint_gated_phase {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ : TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (f : Ω → ℕ) (hf : Measurable[setSigma A] f) :
    Measurable[⨆ k, localHullFieldSigma h A n (ψ k) hp] (fun ω =>
      ({ω' | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ (f ω) : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω'))} : Set Ω).indicator
        (fun ω' => toIcoMod hp 0 (h ω' (ψ (f ω)))) ω) := by
  let m : MeasurableSpace Ω := ⨆ k, localHullFieldSigma h A n (ψ k) hp
  let : MeasurableSpace Ω := m
  have hset : setSigma A ≤ m :=
    (le_sup_left : setSigma A ≤ hullSigma0 h A n).trans
      ((le_sup_left : hullSigma0 h A n ≤ localHullFieldSigma h A n (ψ 0) hp).trans
        (le_iSup (fun k => localHullFieldSigma h A n (ψ k) hp) 0))
  have hfm : Measurable f := hf.mono hset le_rfl
  let X : ℕ → Ω → ℝ := fun k ω =>
    ({ω' | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ k : ℂ → ℝ) ⊆
      interior (dyadicHull n (A ω'))} : Set Ω).indicator
      (fun ω' => toIcoMod hp 0 (h ω' (ψ k))) ω
  have hX (k : ℕ) : Measurable (X k) :=
    (measurable_hull_joint_gated_phase h A hA n φ (ψ k) hp).mono
      (le_iSup (fun j => localHullFieldSigma h A n (ψ j) hp) k) le_rfl
  change Measurable (fun ω => X (f ω) ω)
  intro s hs
  have heq : (fun ω => X (f ω) ω) ⁻¹' s =
      ⋃ k : ℕ, ({ω | f ω = k} ∩ (X k ⁻¹' s)) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨f ω, rfl, hω⟩
    · rintro ⟨k, hk, hω⟩
      simpa only [hk] using hω
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    ((measurableSet_singleton k).preimage hfm).inter (hX k hs)

/-- The selected centered coordinate and selected phase are jointly measurable
    with the same support gate. -/
theorem measurable_selected_hull_joint_gated_coordinates {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ : TestC) (ψ : ℕ → TestC) (hψ : ∀ k, ∫ z, ψ k z = 1)
    {p : ℝ} (hp : 0 < p) (f : Ω → ℕ) (hf : Measurable[setSigma A] f) :
    Measurable[⨆ k, localHullFieldSigma h A n (ψ k) hp] (fun ω =>
      (({ω' | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ (f ω) : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω'))} : Set Ω).indicator
        (fun ω' => h ω' φ - (∫ z, φ z) * h ω' (ψ (f ω))) ω,
       ({ω' | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ (f ω) : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω'))} : Set Ω).indicator
        (fun ω' => toIcoMod hp 0 (h ω' (ψ (f ω)))) ω)) :=
  (measurable_selected_hull_joint_gated_centered h A hA n φ ψ hψ hp f hf).prodMk
    (measurable_selected_hull_joint_gated_phase h A hA n φ ψ hp f hf)

end LatticeProb.LQG

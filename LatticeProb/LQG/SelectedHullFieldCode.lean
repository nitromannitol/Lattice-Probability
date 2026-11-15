import LatticeProb.LQG.SelectedHullJointPhase

/-! # Selected discrete-period field observations on dyadic hulls -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- The indicator of the joint support gate is observable under measurable
selection of the anchor. -/
theorem measurable_selected_hull_joint_gate {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ : TestC) (ψ : ℕ → TestC) (f : Ω → ℕ) (hf : Measurable[setSigma A] f) :
    Measurable[hullSigma0 h A n] (fun ω =>
      ({ω' | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ (f ω) : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω'))} : Set Ω).indicator (fun _ => (1 : ℝ)) ω) := by
  let : MeasurableSpace Ω := hullSigma0 h A n
  have hfm : Measurable f := hf.mono le_sup_left le_rfl
  let E : ℕ → Set Ω := fun k => {ω | tsupport (φ : ℂ → ℝ) ∪
    tsupport (ψ k : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))}
  have hE (k : ℕ) : MeasurableSet (E k) :=
    measurableSet_subset_interior_dyadicHull h A hA n _
  let F : Set Ω := {ω | ω ∈ E (f ω)}
  have hF : MeasurableSet F := by
    have heq : F = ⋃ k : ℕ, ({ω | f ω = k} ∩ E k) := by
      ext ω
      simp only [F, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · intro hω
        exact ⟨f ω, rfl, hω⟩
      · rintro ⟨k, hk, hω⟩
        simpa only [hk] using hω
    rw [heq]
    exact MeasurableSet.iUnion fun k =>
      ((measurableSet_singleton k).preimage hfm).inter (hE k)
  exact measurable_const.indicator hF

/-- Jointly gated support indicators, centered pairings and anchor phases. -/
def selectedHullFieldCode {Ω : Type} {I : Type*} (h : Ω → DistC)
    (A : Ω → Set ℂ) (n : ℕ) (φ : I → TestC) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (f : Ω → ℕ) : Ω → (I → ℝ × (ℝ × ℝ)) :=
  fun ω i =>
    let E : Set Ω := {ω' | tsupport (φ i : ℂ → ℝ) ∪
      tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω'))}
    (E.indicator (fun _ => 1) ω,
     E.indicator (fun ω' => h ω' (φ i) - (∫ z, φ i z) * h ω' (ψ (f ω))) ω,
     E.indicator (fun ω' => toIcoMod hp 0 (h ω' (ψ (f ω)))) ω)

/-- The selected field code is measurable in the join of local phase
observation sigma algebras. -/
theorem measurable_selectedHullFieldCode {Ω : Type} {I : Type*} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ : I → TestC) (ψ : ℕ → TestC) (hψ : ∀ k, ∫ z, ψ k z = 1)
    {p : ℝ} (hp : 0 < p) (f : Ω → ℕ) (hf : Measurable[setSigma A] f) :
    Measurable[⨆ k, localHullFieldSigma h A n (ψ k) hp]
      (selectedHullFieldCode h A n φ ψ hp f) := by
  let : MeasurableSpace Ω := ⨆ k, localHullFieldSigma h A n (ψ k) hp
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_selected_hull_joint_gate h A hA n (φ i) ψ f hf).mono
    ((le_sup_left : hullSigma0 h A n ≤ localHullFieldSigma h A n (ψ 0) hp).trans
      (le_iSup (fun k => localHullFieldSigma h A n (ψ k) hp) 0)) le_rfl).prodMk
    (measurable_selected_hull_joint_gated_coordinates h A hA n (φ i) ψ hψ hp f hf)

end LatticeProb.LQG

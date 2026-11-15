import LatticeProb.LQG.SelectedCollarGates
import LatticeProb.LQG.SelectedHullJointPhase

/-! # Collar restrictions with a selected anchor -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A measurable choice from a countable family of supported anchors gives a
measurable phase in the join of the local anchor observation sigma algebras. -/
theorem measurable_selected_anchor_phase {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (n : ℕ) (ψ : ℕ → TestC)
    (g : Ω → ℕ) (hg : Measurable[setSigma A] g)
    (hsupp : ∀ ω, tsupport (ψ (g ω) : ℂ → ℝ) ⊆
      interior (dyadicHull n (A ω))) {p : ℝ} (hp : 0 < p) :
    Measurable[⨆ k, localHullFieldSigma h A n (ψ k) hp]
      (fun ω => toIcoMod hp 0 (h ω (ψ (g ω)))) := by
  let m : MeasurableSpace Ω := ⨆ k, localHullFieldSigma h A n (ψ k) hp
  let : MeasurableSpace Ω := m
  have hset : setSigma A ≤ m :=
    (le_sup_left : setSigma A ≤ hullSigma0 h A n).trans
      ((le_sup_left : hullSigma0 h A n ≤ localHullFieldSigma h A n (ψ 0) hp).trans
        (le_iSup (fun k => localHullFieldSigma h A n (ψ k) hp) 0))
  have hgm : Measurable g := hg.mono hset le_rfl
  let X : ℕ → Ω → ℝ := fun k => localHullFieldPhase h A n (ψ k) hp
  have hX (k : ℕ) : Measurable (X k) :=
    (show Measurable[localHullFieldSigma h A n (ψ k) hp] (X k) from
      (comap_measurable _).mono le_sup_right le_rfl).mono
        (le_iSup (fun j => localHullFieldSigma h A n (ψ j) hp) k) le_rfl
  have hsel : Measurable (fun ω => X (g ω) ω) := by
    intro s hs
    have heq : (fun ω => X (g ω) ω) ⁻¹' s =
        ⋃ k : ℕ, ({ω | g ω = k} ∩ X k ⁻¹' s) := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro hω
        exact ⟨g ω, rfl, hω⟩
      · rintro ⟨k, hk, hω⟩
        simpa only [hk] using hω
    rw [heq]
    exact MeasurableSet.iUnion fun k =>
      ((measurableSet_singleton k).preimage hgm).inter (hX k hs)
  have heq : (fun ω => X (g ω) ω) =
      (fun ω => toIcoMod hp 0 (h ω (ψ (g ω)))) := by
    funext ω
    exact Set.indicator_of_mem (hsupp ω) _
  rwa [heq] at hsel

/-- Collar-gated centered observations and the selected anchor phase are
measurable in the join of the local anchor observation sigma algebras. -/
theorem measurable_selected_anchor_collar_restriction {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (A : Ω → Set ℂ)
    (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (K : Ω → NonemptyCompacts ℂ) (hK : Measurable[setSigma A] K)
    (f : Ω → ℕ) (hf : Measurable[setSigma A] f)
    (hcollar : ∀ ω, thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ) ⊆
      interior (dyadicHull n (A ω)))
    (φ : I → TestC) (ψ : ℕ → TestC) (hψ : ∀ k, ∫ z, ψ k z = 1)
    (g : Ω → ℕ) (hg : Measurable[setSigma A] g)
    (hsupp : ∀ ω, tsupport (ψ (g ω) : ℂ → ℝ) ⊆
      thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    Measurable[⨆ k, localHullFieldSigma h A n (ψ k) hp] (fun (ω : Ω) =>
      ((fun i =>
        let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
          thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
        (E.indicator (fun _ => (1 : ℝ)) ω,
          E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ (g ω))) ω)),
       toIcoMod hp 0 (h ω (ψ (g ω))))) := by
  classical
  let m : MeasurableSpace Ω := ⨆ k, localHullFieldSigma h A n (ψ k) hp
  let : MeasurableSpace Ω := m
  have hset : setSigma A ≤ m :=
    (le_sup_left : setSigma A ≤ hullSigma0 h A n).trans
      ((le_sup_left : hullSigma0 h A n ≤ localHullFieldSigma h A n (ψ 0) hp).trans
        (le_iSup (fun k => localHullFieldSigma h A n (ψ k) hp) 0))
  refine Measurable.prodMk ?_ (measurable_selected_anchor_phase h A n ψ g hg
    (fun ω => (hsupp ω).trans (hcollar ω)) hp)
  apply measurable_pi_iff.mpr
  intro i
  let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
    thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
  have hE0 : MeasurableSet[setSigma A] E := by
    let : MeasurableSpace Ω := setSigma A
    exact measurableSet_compact_subset_selected_thickening hK hf (φ i).hasCompactSupport.isCompact
  have hE : MeasurableSet E := hset _ hE0
  refine (measurable_const.indicator hE).prodMk ?_
  have hm := (measurable_selected_hull_joint_gated_centered h A hA n (φ i) ψ hψ hp g hg).indicator hE
  have heq : (fun ω => E.indicator (fun ω =>
      ({ω' | tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ (g ω) : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω'))} : Set Ω).indicator
          (fun ω' => h ω' (φ i) - (∫ z, φ i z) * h ω' (ψ (g ω))) ω) ω) =
      (fun ω => E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ (g ω))) ω) := by
    funext ω
    by_cases hω : ω ∈ E
    · have hgate : ω ∈ ({ω' | tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ (g ω) : ℂ → ℝ) ⊆
          interior (dyadicHull n (A ω'))} : Set Ω) :=
        union_subset (hω.trans (hcollar ω)) ((hsupp ω).trans (hcollar ω))
      simp only [Set.indicator_of_mem hω, Set.indicator_of_mem hgate]
    · simp only [Set.indicator_of_notMem hω]
  change Measurable (fun ω => E.indicator (fun ω =>
      ({ω' | tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ (g ω) : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω'))} : Set Ω).indicator
          (fun ω' => h ω' (φ i) - (∫ z, φ i z) * h ω' (ψ (g ω))) ω) ω) at hm
  rwa [heq] at hm

end LatticeProb.LQG

import LatticeProb.Topology.DisjointOpenVisitIdentity
import LatticeProb.Topology.AreaCurveComponentIntervalOrder
import LatticeProb.Topology.AreaCurveIntervalContainment
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Simultaneous component visit identities -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- For one fixed segment, all nondegenerate interval witnesses for its interior
components have the same exceptional set of visit times. -/
theorem ae_component_visit_identity_of_proper_area_curve
    (η : ℝ → ℂ) (μ : Measure ℂ) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t : ℝ} (hst : s < t) :
    ∀ᵐ u ∂volume, ∀ x ∈ interior (η '' Icc s t), ∀ a b : ℝ, a < b →
      η '' Icc a b = closure (connectedComponentIn (interior (η '' Icc s t)) x) →
      (η u ∈ connectedComponentIn (interior (η '' Icc s t)) x ↔ u ∈ Ioo a b) := by
  classical
  let K := η '' Icc s t
  let C : Set (Set ℂ) := {U | ∃ x a b, x ∈ interior K ∧
    U = connectedComponentIn (interior K) x ∧ a < b ∧ η '' Icc a b = closure U}
  have hex : ∀ U : C, ∃ x a b, x ∈ interior K ∧
      U.1 = connectedComponentIn (interior K) x ∧ a < b ∧ η '' Icc a b = closure U.1 :=
    fun U => U.2
  choose x a b hx hU hab himage using hex
  let A : Set ℂ → ℝ := fun U => if h : U ∈ C then a ⟨U, h⟩ else 0
  let B : Set ℂ → ℝ := fun U => if h : U ∈ C then b ⟨U, h⟩ else 0
  have hK : IsClosed K := (isCompact_Icc.image hη).isClosed
  have hfront : μ (frontier K) = 0 :=
    measure_frontier_image_Icc_eq_zero_of_proper η μ hη hp hs harea hst
  have hdis : C.PairwiseDisjoint id := by
    intro U hUC V hVC hne
    apply disjoint_left.mpr
    intro z hzU hzV
    apply hne
    have hU' : U = connectedComponentIn (interior K) (x ⟨U, hUC⟩) := hU ⟨U, hUC⟩
    have hV' : V = connectedComponentIn (interior K) (x ⟨V, hVC⟩) := hU ⟨V, hVC⟩
    rw [hU'] at hzU
    rw [hV'] at hzV
    exact hU'.trans ((connectedComponentIn_eq hzU).trans
      ((connectedComponentIn_eq hzV).symm.trans hV'.symm))
  have hopen : ∀ U ∈ C, IsOpen U := by
    intro U hUC
    have hU' : U = connectedComponentIn (interior K) (x ⟨U, hUC⟩) := hU ⟨U, hUC⟩
    rw [hU']
    exact isOpen_interior.connectedComponentIn
  have hne : ∀ U ∈ C, U.Nonempty := by
    intro U hUC
    have hU' : U = connectedComponentIn (interior K) (x ⟨U, hUC⟩) := hU ⟨U, hUC⟩
    rw [hU']
    exact ⟨x ⟨U, hUC⟩, mem_connectedComponentIn (hx ⟨U, hUC⟩)⟩
  have hf : ∀ U ∈ C, μ (frontier U) = 0 := by
    intro U hUC
    have hU' : U = connectedComponentIn (interior K) (x ⟨U, hUC⟩) := hU ⟨U, hUC⟩
    rw [hU']
    exact measure_frontier_component_interior_eq_zero hK μ hfront _
  have hi : ∀ U ∈ C, η '' Icc (A U) (B U) = closure U := by
    intro U hUC
    simpa [A, B, hUC] using himage ⟨U, hUC⟩
  have hm : ∀ U ∈ C, μ (η '' Icc (A U) (B U)) = volume (Icc (A U) (B U)) := by
    intro U hUC
    have hlt : A U < B U := by simpa [A, B, hUC] using hab ⟨U, hUC⟩
    rw [harea _ _ hlt, Real.volume_Icc]
  have hall := ae_visit_disjoint_open_eq_intervals η μ C A B hη.measurable hmap
    hdis hopen hne hf hi hm
  filter_upwards [hall] with u hu y hy c d hcd hcdimage
  let U := connectedComponentIn (interior K) y
  have hUC : U ∈ C := ⟨y, c, d, hy, rfl, hcd, hcdimage⟩
  have hlt : A U < B U := by simpa [A, B, hUC] using hab ⟨U, hUC⟩
  have heq : A U = c ∧ B U = d :=
    endpoints_eq_of_area_curve_image_eq η μ hη harea hlt hcd ((hi U hUC).trans hcdimage.symm)
  simpa [U, K, heq.1, heq.2] using hu U hUC

end LatticeProb

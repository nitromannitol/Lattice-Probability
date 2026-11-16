import LatticeProb.LQG.CoupledContactFrontier

/-! # Components containing contact-window images -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.Topology

/-- If each compact subwindow belongs to an infinite component, all subwindows
of the same open interval belong to one infinite component. -/
theorem exists_component_containing_all_interval_images
    {X : Type*} [TopologicalSpace X] {S : Set X} {f : ℝ → X} {L U : ℝ}
    (hLU : L < U)
    (h : ∀ a b, L < a → b < U → a < b →
      ∃ C ∈ connectedComponentIn S '' S, C.Infinite ∧ f '' Icc a b ⊆ C) :
    ∃ C ∈ connectedComponentIn S '' S, C.Infinite ∧
      ∀ a b, L < a → b < U → a < b → f '' Icc a b ⊆ C := by
  obtain ⟨a₀, ha₀, ha₀U⟩ := exists_between hLU
  obtain ⟨b₀, ha₀b₀, hb₀⟩ := exists_between ha₀U
  obtain ⟨C, hC, hCinf, hCsub⟩ := h a₀ b₀ ha₀ hb₀ ha₀b₀
  refine ⟨C, hC, hCinf, ?_⟩
  intro a b ha hb hab
  have hlo : L < min a₀ a := lt_min ha₀ ha
  have hhi : max b₀ b < U := max_lt hb₀ hb
  have hlt : min a₀ a < max b₀ b :=
    lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le ha₀b₀ (le_max_left _ _))
  obtain ⟨D, hD, _, hDsub⟩ := h (min a₀ a) (max b₀ b) hlo hhi hlt
  have hpointC : f a₀ ∈ C := hCsub ⟨a₀, ⟨le_rfl, le_of_lt ha₀b₀⟩, rfl⟩
  have hpointD : f a₀ ∈ D := hDsub ⟨a₀, ⟨min_le_left _ _,
    le_trans (le_of_lt ha₀b₀) (le_max_left _ _)⟩, rfl⟩
  obtain ⟨c, hc, rfl⟩ := hC
  obtain ⟨d, hd, rfl⟩ := hD
  have heq : connectedComponentIn S c = connectedComponentIn S d :=
    (connectedComponentIn_eq hpointC).trans (connectedComponentIn_eq hpointD).symm
  rw [← heq] at hDsub
  exact (image_mono (Icc_subset_Icc (min_le_right _ _) (le_max_right _ _))).trans hDsub

end LatticeProb.Topology

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- All strict left contact windows for a cell pair lie in one component. -/
theorem ae_left_contact_windows_one_component
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      let f := fun level => η ω (ellMinus (bm ω) (ε * x) level)
      let S := frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
        frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))
      ∃ C ∈ connectedComponentIn S '' S, C.Infinite ∧
        ∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b → f '' Icc a b ⊆ C := by
  filter_upwards [ae_left_contact_frontier_component D] with ω h
  intro ε x y hε hxy hwindow
  exact LatticeProb.Topology.exists_component_containing_all_interval_images hwindow
    (fun a b ha hb hab => h ε x y a b hε hxy ha hb hab)

/-- All strict right contact windows for a cell pair lie in one component. -/
theorem ae_right_contact_windows_one_component
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      let f := fun level => η ω (rhoMinus (bm ω) (ε * x) level)
      let S := frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
        frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))
      ∃ C ∈ connectedComponentIn S '' S, C.Infinite ∧
        ∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b → f '' Icc a b ⊆ C := by
  filter_upwards [ae_right_contact_frontier_component D] with ω h
  intro ε x y hε hxy hwindow
  exact LatticeProb.Topology.exists_component_containing_all_interval_images hwindow
    (fun a b ha hb hab => h ε x y a b hε hxy ha hb hab)

end MatedCRTHarmonic.MoTInput

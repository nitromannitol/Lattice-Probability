import LatticeProb.Euclidean.ParentBlockBallBuffer

/-! # Ball buffers for selected parent blocks in isometric coordinates -/

set_option autoImplicit false

open Set

namespace LatticeProb.ParentBlock

/-- Each point of a parent block is within four side lengths of its centre. -/
theorem dist_center_le_of_mem_parentBlock {a x : ℂ} {S : ℝ} (hS : 0 ≤ S)
    (hx : x ∈ parentBlock a S) : dist x a ≤ 4 * S := by
  have ha : a ∈ closedSquare a S := by
    simp only [closedSquare, mem_ofPred_eq, sub_self, abs_zero]
    constructor <;> linarith
  simpa only [dist_eq_norm] using norm_sub_le_four_mul_of_mem_of_mem_parentBlock hS ha hx

/-- A parent block whose square has an anchor near a point is carried into the
corresponding larger ball by a real linear isometry. -/
theorem image_parentBlock_subset_ball_of_anchor
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ ≃ₗᵢ[ℝ] F) {a c x : ℂ} {r s : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ closedSquare c s) (hxa : x ∈ Metric.ball a r) :
    f '' parentBlock c s ⊆ Metric.ball (f a) (r + 4 * s) := by
  rintro y ⟨z, hz, rfl⟩
  have h := parentBlock_subset_ball_of_mem_closedSquare hs hx hxa hz
  simpa only [Metric.mem_ball, f.isometry.dist_eq] using h

/-- Initial and selected blocks lie in a common ball when their respective
anchors lie in an outer parent block and in their squares. -/
theorem initial_and_selected_parentBlock_image_subset_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X J : Type*} (f : ℂ ≃ₗᵢ[ℝ] F) (pos : X → F)
    (centres : J → ℂ) (initial : J) (select : ℕ → X → Option J)
    {a x₀ : ℂ} {S s r : ℝ} (hS : 0 ≤ S) (hs : 0 ≤ s)
    (hr : 4 * S < r) (hx₀ : x₀ ∈ parentBlock a S)
    (hinit : x₀ ∈ closedSquare (centres initial) s)
    (hselect : ∀ n x j, select n x = some j →
      f.symm (pos x) ∈ parentBlock a S ∧
      f.symm (pos x) ∈ closedSquare (centres j) s) :
    f '' parentBlock (centres initial) s ⊆ Metric.ball (f a) (r + 4 * s) ∧
    ∀ n x j, select n x = some j →
      f '' parentBlock (centres j) s ⊆ Metric.ball (f a) (r + 4 * s) := by
  constructor
  · apply image_parentBlock_subset_ball_of_anchor f hs hinit
    exact lt_of_le_of_lt (dist_center_le_of_mem_parentBlock hS hx₀) hr
  · intro n x j hj
    obtain ⟨hout, hin⟩ := hselect n x j hj
    apply image_parentBlock_subset_ball_of_anchor f hs hin
    exact lt_of_le_of_lt (dist_center_le_of_mem_parentBlock hS hout) hr

/-- A uniform closed buffer about a ball lies in a larger ball. -/
theorem closedBall_subset_ball_of_mem_ball
    {F : Type*} [PseudoMetricSpace F] {a x : F} {r ρ R : ℝ}
    (hx : x ∈ Metric.ball a r) (hmargin : r + ρ ≤ R) :
    Metric.closedBall x ρ ⊆ Metric.ball a R := by
  intro y hy
  change dist y a < R
  have hxa : dist x a < r := hx
  have hyx : dist y x ≤ ρ := hy
  linarith [dist_triangle y x a]

end LatticeProb.ParentBlock

import LatticeProb.Network.OpenLadder
import LatticeProb.Network.Basic

/-!
# Kirchhoff elimination on the open ladder

Harmonicity is imposed at every actual vertex except the two terminal leaves.
The computed graph neighbor sets give the bottom, interior, and top equations.
Subtracting the two column equations gives the backward elimination identities,
including the separate height-one case, without a resistance assumption.
-/

namespace LatticeProb.Network.OpenLadder

noncomputable section

/-- Harmonicity at every actual nonterminal, for the unit-conductance network. -/
abbrev Harmonic {n : ℤ} (u : Vertex n → ℝ) : Prop :=
  HarmonicOn (graph n) (unitCond (graph n)) u {v | v ≠ source n ∧ v ≠ target n}

/-- At the left leaf, the graph Laplacian is the single terminal-edge difference. -/
theorem laplacian_source {n : ℤ} (hn : 1 ≤ n) (u : Vertex n → ℝ) :
    LatticeProb.Graph.laplacian (graph n) u (source n) =
      u (left n 1 ⟨by omega, hn⟩) - u (source n) := by
  simp only [LatticeProb.Graph.laplacian, neighbors_source hn, Finset.sum_singleton]

/-- At the right leaf, the graph Laplacian is the single terminal-edge difference. -/
theorem laplacian_target {n : ℤ} (hn : 1 ≤ n) (u : Vertex n → ℝ) :
    LatticeProb.Graph.laplacian (graph n) u (target n) =
      u (right n 1 ⟨by omega, hn⟩) - u (target n) := by
  simp only [LatticeProb.Graph.laplacian, neighbors_target hn, Finset.sum_singleton]

/-- A harmonic function has zero graph Laplacian at every left rung vertex. -/
theorem laplacian_left {n j : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hj : 1 ≤ j ∧ j ≤ n) :
    LatticeProb.Graph.laplacian (graph n) u (left n j hj) = 0 := by
  rw [← netLaplacian_unitCond]
  apply hu
  constructor <;> norm_num [left, source, target, Subtype.ext_iff]

/-- A harmonic function has zero graph Laplacian at every right rung vertex. -/
theorem laplacian_right {n j : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hj : 1 ≤ j ∧ j ≤ n) :
    LatticeProb.Graph.laplacian (graph n) u (right n j hj) = 0 := by
  rw [← netLaplacian_unitCond]
  apply hu
  constructor <;> norm_num [right, source, target, Subtype.ext_iff]

/-- Kirchhoff's equation at the left one vertex. -/
theorem kirchhoff_left_one {u : Vertex 1 → ℝ} (hu : Harmonic u) :
    2 * u (left 1 1 ⟨by omega, by omega⟩) =
      u (source 1) + u (right 1 1 ⟨by omega, by omega⟩) := by
  have h := laplacian_left hu (j := 1) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_left_one] at h
  simp [left, right, source] at h ⊢
  linarith

/-- Kirchhoff's equation at the left bottom vertex. -/
theorem kirchhoff_left_bottom {n : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hn : 2 ≤ n) :
    3 * u (left n 1 ⟨by omega, by omega⟩) =
      u (source n) + u (right n 1 ⟨by omega, by omega⟩) +
        u (left n 2 ⟨by omega, by omega⟩) := by
  have h := laplacian_left hu (j := 1) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_left_bottom hn] at h
  simp [left, right, source] at h ⊢
  linarith

/-- Kirchhoff's equation at the left middle vertex. -/
theorem kirchhoff_left_middle {n j : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hj : 1 < j) (hjn : j < n) :
    3 * u (left n j ⟨by omega, by omega⟩) =
      u (right n j ⟨by omega, by omega⟩) + u (left n (j - 1) ⟨by omega, by omega⟩) +
        u (left n (j + 1) ⟨by omega, by omega⟩) := by
  have h := laplacian_left hu (j := j) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_left_middle hj hjn] at h
  have hrows : j - 1 ≠ j + 1 := by omega
  simp [left, right, Subtype.mk.injEq, Prod.mk.injEq, hrows] at h ⊢
  linarith

/-- Kirchhoff's equation at the left top vertex. -/
theorem kirchhoff_left_top {n : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hn : 2 ≤ n) :
    2 * u (left n n ⟨by omega, by omega⟩) =
      u (right n n ⟨by omega, by omega⟩) + u (left n (n - 1) ⟨by omega, by omega⟩) := by
  have h := laplacian_left hu (j := n) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_left_top hn] at h
  simp [left, right] at h ⊢
  linarith

/-- Kirchhoff's equation at the right one vertex. -/
theorem kirchhoff_right_one {u : Vertex 1 → ℝ} (hu : Harmonic u) :
    2 * u (right 1 1 ⟨by omega, by omega⟩) =
      u (target 1) + u (left 1 1 ⟨by omega, by omega⟩) := by
  have h := laplacian_right hu (j := 1) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_right_one] at h
  simp [right, left, target] at h ⊢
  linarith

/-- Kirchhoff's equation at the right bottom vertex. -/
theorem kirchhoff_right_bottom {n : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hn : 2 ≤ n) :
    3 * u (right n 1 ⟨by omega, by omega⟩) =
      u (target n) + u (left n 1 ⟨by omega, by omega⟩) +
        u (right n 2 ⟨by omega, by omega⟩) := by
  have h := laplacian_right hu (j := 1) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_right_bottom hn] at h
  simp [right, left, target] at h ⊢
  linarith

/-- Kirchhoff's equation at the right middle vertex. -/
theorem kirchhoff_right_middle {n j : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hj : 1 < j) (hjn : j < n) :
    3 * u (right n j ⟨by omega, by omega⟩) =
      u (left n j ⟨by omega, by omega⟩) + u (right n (j - 1) ⟨by omega, by omega⟩) +
        u (right n (j + 1) ⟨by omega, by omega⟩) := by
  have h := laplacian_right hu (j := j) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_right_middle hj hjn] at h
  have hrows : j - 1 ≠ j + 1 := by omega
  simp [right, left, Subtype.mk.injEq, Prod.mk.injEq, hrows] at h ⊢
  linarith

/-- Kirchhoff's equation at the right top vertex. -/
theorem kirchhoff_right_top {n : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hn : 2 ≤ n) :
    2 * u (right n n ⟨by omega, by omega⟩) =
      u (left n n ⟨by omega, by omega⟩) + u (right n (n - 1) ⟨by omega, by omega⟩) := by
  have h := laplacian_right hu (j := n) ⟨by omega, by omega⟩
  rw [LatticeProb.Graph.laplacian, neighbors_right_top hn] at h
  simp [right, left] at h ⊢
  linarith

/-- The signed difference across an actual rung. -/
def rungDifference {n : ℤ} (u : Vertex n → ℝ) (j : ℤ)
    (hj : 1 ≤ j ∧ j ≤ n) : ℝ := u (right n j hj) - u (left n j hj)

/-- At height one, the terminal gap is three times the sole rung difference. -/
theorem terminal_gap_one {u : Vertex 1 → ℝ} (hu : Harmonic u) :
    u (target 1) - u (source 1) = 3 * rungDifference u 1 ⟨by omega, by omega⟩ := by
  have hl := kirchhoff_left_one hu
  have hr := kirchhoff_right_one hu
  dsimp only [rungDifference]
  linarith

/-- The bottom equations eliminate the two terminal values when the height is at least two. -/
theorem difference_bottom {n : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u) (hn : 2 ≤ n) :
    u (target n) - u (source n) =
      4 * rungDifference u 1 ⟨by omega, by omega⟩ -
        rungDifference u 2 ⟨by omega, hn⟩ := by
  have hl := kirchhoff_left_bottom hu hn
  have hr := kirchhoff_right_bottom hu hn
  dsimp only [rungDifference]
  linarith

/-- Subtraction at an interior rung gives the backward elimination relation. -/
theorem difference_middle {n j : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u)
    (hj : 1 < j) (hjn : j < n) :
    rungDifference u (j - 1) ⟨by omega, by omega⟩ =
      4 * rungDifference u j ⟨by omega, by omega⟩ -
        rungDifference u (j + 1) ⟨by omega, by omega⟩ := by
  have hl := kirchhoff_left_middle hu hj hjn
  have hr := kirchhoff_right_middle hu hj hjn
  dsimp only [rungDifference]
  linarith

/-- At the top, the penultimate difference is three times the final difference. -/
theorem difference_top {n : ℤ} {u : Vertex n → ℝ} (hu : Harmonic u) (hn : 2 ≤ n) :
    rungDifference u (n - 1) ⟨by omega, by omega⟩ =
      3 * rungDifference u n ⟨by omega, by omega⟩ := by
  have hl := kirchhoff_left_top hu hn
  have hr := kirchhoff_right_top hu hn
  dsimp only [rungDifference]
  linarith

/-- At height two, the exact graph equations give terminal multiplier eleven. -/
theorem terminal_gap_two {u : Vertex 2 → ℝ} (hu : Harmonic u) :
    u (target 2) - u (source 2) =
      11 * rungDifference u 2 ⟨by omega, by omega⟩ := by
  have hb := difference_bottom hu (by omega)
  have ht := difference_top hu (by omega)
  norm_num only at ht
  linarith

/-- A nonconstant integer-valued voltage on the height-one carrier, viewed in the reals. -/
def voltageOne (v : Vertex 1) : ℝ := (v.val.1 : ℝ) - 1

/-- The explicit height-one voltage is harmonic at both actual nonterminals. -/
theorem voltageOne_harmonic : Harmonic voltageOne := by
  intro v hv
  obtain ⟨j, hj, hv⟩ := eq_left_or_right (by omega) v hv.1 hv.2
  have hj1 : j = 1 := by omega
  subst j
  rcases hv with rfl | rfl
  · rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian, neighbors_left_one]
    norm_num [voltageOne, source, left, right]
  · rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian, neighbors_right_one]
    norm_num [voltageOne, target, left, right]

/-- The height-one example has terminal gap three and top rung difference one. -/
theorem voltageOne_gap :
    voltageOne (target 1) - voltageOne (source 1) = 3 ∧
      rungDifference voltageOne 1 ⟨by omega, by omega⟩ = 1 := by
  norm_num [voltageOne, source, target, rungDifference, left, right]

/-- An integer-valued voltage on the six actual height-two vertices, viewed in the reals. -/
def voltageTwo (v : Vertex 2) : ℝ :=
  if v.val.2 = 2 then (v.val.1 : ℝ) + 3
  else if v.val.1 ≤ 2 then 4 * ((v.val.1 : ℝ) - 1) else 4 * (v.val.1 : ℝ) - 5

/-- The explicit height-two voltage satisfies all four actual nonterminal equations. -/
theorem voltageTwo_harmonic : Harmonic voltageTwo := by
  intro v hv
  obtain ⟨j, hj, hv⟩ := eq_left_or_right (by omega) v hv.1 hv.2
  have hj12 : j = 1 ∨ j = 2 := by omega
  rcases hv with rfl | rfl <;> rcases hj12 with rfl | rfl
  · rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian,
      neighbors_left_bottom (by omega)]
    norm_num [voltageTwo, source, left, right]
  · rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian,
      neighbors_left_top (by omega)]
    norm_num [voltageTwo, left, right]
  · rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian,
      neighbors_right_bottom (by omega)]
    norm_num [voltageTwo, target, left, right]
  · rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian,
      neighbors_right_top (by omega)]
    norm_num [voltageTwo, left, right]

/-- The height-two example has terminal gap eleven and top rung difference one. -/
theorem voltageTwo_gap :
    voltageTwo (target 2) - voltageTwo (source 2) = 11 ∧
      rungDifference voltageTwo 2 ⟨by omega, by omega⟩ = 1 := by
  norm_num [voltageTwo, source, target, rungDifference, left, right]

end

end LatticeProb.Network.OpenLadder

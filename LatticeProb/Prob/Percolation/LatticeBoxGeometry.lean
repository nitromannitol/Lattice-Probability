import LatticeProb.Prob.Percolation.AntalPisztoraGlue

/-!
# Integer box geometry

Coordinate clamping supplies an interior center, and nearby AP boxes share
an explicitly positioned integer cube.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ}

/-- Clamp a lattice point coordinatewise to the interval of admissible centers. -/
def boxCenterClamp (l u v : Vertex d) (h : ℤ) : Vertex d :=
  fun i => max (l i + h) (min (v i) (u i - h))

/-- The scalar clamp lies in the center interval, covers the point, and has the
stated distance to each face that can be exited inside the original interval. -/
theorem integer_clamp_bounds (l u v h : ℤ) (hh : 0 ≤ h)
    (hw : l + 2 * h ≤ u) (hl : l ≤ v) (hu : v ≤ u) :
    let k := max (l + h) (min v (u - h))
    l + h ≤ k ∧ k ≤ u - h ∧ |v - k| ≤ h ∧
      (l < k - h → h ≤ v - (k - h)) ∧
      (k + h < u → h ≤ (k + h) - v) := by
  dsimp only
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> omega

/-- A point in an integer box has an admissible clamped center, is covered by its
radius-h box, and has the required margin at every exitable face. -/
theorem boxCenterClamp_spec (l u v : Vertex d) (h : ℤ) (hh : 0 ≤ h)
    (hw : ∀ i, l i + 2 * h ≤ u i) (hv : ∀ i, l i ≤ v i ∧ v i ≤ u i) :
    (∀ i, l i + h ≤ boxCenterClamp l u v h i ∧
      boxCenterClamp l u v h i ≤ u i - h ∧ |v i - boxCenterClamp l u v h i| ≤ h ∧
      (l i < boxCenterClamp l u v h i - h →
        h ≤ v i - (boxCenterClamp l u v h i - h)) ∧
      (boxCenterClamp l u v h i + h < u i →
        h ≤ (boxCenterClamp l u v h i + h) - v i)) ∧
    {z : Vertex d | ∀ i, |z i - boxCenterClamp l u v h i| ≤ h} ⊆
      {z : Vertex d | ∀ i, l i ≤ z i ∧ z i ≤ u i} := by
  have hs (i : Fin d) := integer_clamp_bounds (l i) (u i) (v i) h hh (hw i) (hv i).1 (hv i).2
  refine ⟨?_, ?_⟩
  · intro i
    exact hs i
  · intro z hz i
    have hk₁ : l i + h ≤ boxCenterClamp l u v h i := (hs i).1
    have hk₂ : boxCenterClamp l u v h i ≤ u i - h := (hs i).2.1
    have hd := (abs_le.mp (hz i))
    constructor <;> omega

/-- The integer side-N cube at the coordinatewise maximum minus N is contained
in both AP outer boxes whenever their centers are at most N apart coordinatewise. -/
theorem apInner_common_outer (a b : Vertex d) (N : {n : ℕ // 0 < n})
    (hab : ∀ i, |a i - b i| ≤ (N.val : ℤ)) :
    let q : Vertex d := fun i => max (a i) (b i) - N.val
    apInner q N ⊆ apOuter a N ∧ apInner q N ⊆ apOuter b N := by
  dsimp only
  have hN : (0 : ℝ) < N.val := by exact_mod_cast N.property
  constructor <;> intro z hz <;> rw [mem_apInner_iff] at hz <;>
    rw [mem_apOuter_iff] <;> intro i
  all_goals
    have hcoord := hz i
    have hab' : |(a i : ℝ) - (b i : ℝ)| ≤ (N.val : ℝ) := by exact_mod_cast hab i
    have hdist := abs_le.mp hab'
    simp only [Int.cast_sub, Int.cast_max, Int.cast_natCast] at hcoord
    rw [abs_le]
    by_cases h : a i ≤ b i
    · have hr : (a i : ℝ) ≤ (b i : ℝ) := by exact_mod_cast h
      rw [max_eq_right hr] at hcoord
      constructor <;> linarith
    · have hr : (b i : ℝ) ≤ (a i : ℝ) := by exact_mod_cast (le_of_not_ge h)
      rw [max_eq_left hr] at hcoord
      constructor <;> linarith

/-- Nearest-neighbor centers have a common side-N cube at every positive scale. -/
theorem apInner_common_outer_of_adj (a b : Vertex d) (N : {n : ℕ // 0 < n})
    (hadj : (nearestNeighborGraph d).Adj a b) :
    let q : Vertex d := fun i => max (a i) (b i) - N.val
    apInner q N ⊆ apOuter a N ∧ apInner q N ⊆ apOuter b N := by
  apply apInner_common_outer
  intro i
  have hN : (1 : ℤ) ≤ N.val := by exact_mod_cast N.property
  obtain ⟨j, hj | hj⟩ := Graph.Zd.adj_iff.mp hadj
  · rw [hj]
    by_cases hij : i = j
    · subst i
      simp [LatticeProb.unit]
      omega
    · simp [LatticeProb.unit, Pi.single_eq_of_ne hij]
  · rw [hj]
    by_cases hij : i = j
    · subst i
      simp [LatticeProb.unit]
      omega
    · simp [LatticeProb.unit, Pi.single_eq_of_ne hij]

end
end LatticeProb.Percolation

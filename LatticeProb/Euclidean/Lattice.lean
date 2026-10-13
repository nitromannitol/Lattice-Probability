import Mathlib
import LatticeProb.Site

/-!
# Euclidean radius and physical scaling of the integer lattice

For a dimension `d` the integer lattice is `Site d = Fin d → ℤ`.  This module fixes the
Euclidean radius `radius v = √(∑ v_k²)` on the real carrier `Fin d → ℝ`, not the Pi
sup-norm, the physical scaling `physical ε z` of an integer point, the finite box
`cutoffBox d ε`, and the set `unitBallIndices d ε` of nonzero integer points whose scaled
image lies in the closed Euclidean unit ball.  It also records the coordinate reflections
that act on these index sets.  No hypothesis is assumed beyond those stated on each
declaration.
-/

noncomputable section

open scoped BigOperators

namespace LatticeProb.Euclidean.Lattice

/-- The physical point `ε z` of the scaled lattice, with coordinates `ε z_k`. -/
def physical {d : ℕ} (ε : ℝ) (z : Site d) : Fin d → ℝ :=
  fun k => ε * (z k : ℝ)

/-- The Euclidean radius `√(∑ v_k²)` of a real vector `v : Fin d → ℝ`; it is not the Pi sup-norm. -/
def radius {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ k, (v k) ^ 2)

/-- The finite box of integer indices with `|z_k| ≤ ⌈1/ε⌉` in every coordinate. -/
def cutoffBox (d : ℕ) (ε : ℝ) : Finset (Site d) :=
  Fintype.piFinset (fun _ => Finset.Icc (-⌈1 / ε⌉) ⌈1 / ε⌉)

/-- The nonzero integer indices of `cutoffBox d ε` whose physical point `ε z` lies in the closed Euclidean unit ball. -/
def unitBallIndices (d : ℕ) (ε : ℝ) : Finset (Site d) :=
  (cutoffBox d ε).filter (fun z => z ≠ 0 ∧ radius (physical ε z) ≤ 1)

/-- The Euclidean radius is nonnegative. -/
lemma radius_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ radius v :=
  Real.sqrt_nonneg _

/-- The square of the Euclidean radius is the sum of the squared coordinates. -/
lemma radius_sq {d : ℕ} (v : Fin d → ℝ) :
    radius v ^ 2 = ∑ k, (v k) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg (v k)))

/-- Each coordinate is bounded in absolute value by the Euclidean radius. -/
lemma abs_coord_le_radius {d : ℕ} (v : Fin d → ℝ) (k : Fin d) :
    |v k| ≤ radius v := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun l _ => sq_nonneg (v l)) (Finset.mem_univ k)

/-- For `ε > 0`, the physical point `ε z` is zero exactly when `z` is zero. -/
lemma physical_eq_zero_iff {d : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Site d) :
    physical ε z = 0 ↔ z = 0 := by
  constructor
  · intro h
    funext k
    have hk := congrFun h k
    change ε * (z k : ℝ) = 0 at hk
    have : (z k : ℝ) = 0 := (mul_eq_zero.mp hk).resolve_left hε.ne'
    exact_mod_cast this
  · intro h
    subst z
    funext k
    change ε * ((0 : ℤ) : ℝ) = 0
    rw [Int.cast_zero, mul_zero]

/-- For `ε > 0`, scaling by `ε` is injective on integer points. -/
lemma physical_injective {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (physical (d := d) ε) := by
  intro z w h
  funext k
  have hk := congrFun h k
  change ε * (z k : ℝ) = ε * (w k : ℝ) at hk
  have hc : (z k : ℝ) = (w k : ℝ) := mul_left_cancel₀ hε.ne' hk
  exact_mod_cast hc

/-- A nonzero real vector has positive Euclidean radius. -/
lemma radius_pos {d : ℕ} {v : Fin d → ℝ} (hv : v ≠ 0) :
    0 < radius v := by
  have h : ∃ k, v k ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨k, hk⟩ := h
  exact lt_of_lt_of_le (abs_pos.mpr hk) (abs_coord_le_radius v k)

/-- An integer point whose physical point has radius at most one lies in `cutoffBox d ε`. -/
lemma cutoff_mem_box {d : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Site d}
    (hz : radius (physical ε z) ≤ 1) : z ∈ cutoffBox d ε := by
  rw [cutoffBox, Fintype.mem_piFinset]
  intro k
  have hc := (abs_coord_le_radius (physical ε z) k).trans hz
  change |ε * (z k : ℝ)| ≤ 1 at hc
  rw [abs_mul, abs_of_pos hε] at hc
  have hb : |(z k : ℝ)| ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa [mul_comm] using hc)
  have hi : |z k| ≤ ⌈1 / ε⌉ := by
    have hr := hb.trans (Int.le_ceil (1 / ε))
    rw [← Int.cast_abs] at hr
    exact_mod_cast hr
  exact Finset.mem_Icc.mpr (abs_le.mp hi)

/-- Membership in `unitBallIndices d ε`: a nonzero integer point with physical radius at most one. -/
lemma mem_unitBallIndices {d : ℕ} {ε : ℝ} (hε : 0 < ε) (z : Site d) :
    z ∈ unitBallIndices d ε ↔ z ≠ 0 ∧ radius (physical ε z) ≤ 1 := by
  rw [unitBallIndices, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨cutoff_mem_box hε h.2, h⟩⟩

/-- For `ε > 0`, the set of nonzero integer points with physical radius at most one is finite. -/
lemma unitBallIndices_finite {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {z : Site d | z ≠ 0 ∧ radius (physical ε z) ≤ 1} := by
  have he : {z : Site d | z ≠ 0 ∧ radius (physical ε z) ≤ 1} =
      (unitBallIndices d ε : Set (Site d)) := by
    ext z
    exact (mem_unitBallIndices hε z).symm
  rw [he]
  exact Finset.finite_toSet _

/-- For `ε > 0`, the physical point of an index in `unitBallIndices d ε` is nonzero. -/
lemma unitBallIndices_physical_ne_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Site d}
    (hz : z ∈ unitBallIndices d ε) : physical ε z ≠ 0 := by
  exact fun h => ((mem_unitBallIndices hε z).mp hz).1 ((physical_eq_zero_iff hε z).mp h)

/-- Reflect just coordinate `i` of the integer index. -/
def reflect {d : ℕ} (i : Fin d) (z : Site d) : Site d :=
  fun k => if k = i then -z k else z k

/-- Reflecting the same coordinate twice is the identity. -/
lemma reflect_involutive {d : ℕ} (i : Fin d) (z : Site d) :
    reflect i (reflect i z) = z := by
  funext k
  by_cases hk : k = i <;> simp [reflect, hk]

/-- Reflecting the zero index gives zero. -/
lemma reflect_zero {d : ℕ} (i : Fin d) : reflect i (0 : Site d) = 0 := by
  funext k
  simp [reflect]

/-- Coordinate reflection preserves whether an integer index is zero. -/
lemma reflect_ne_zero {d : ℕ} (i : Fin d) (z : Site d) :
    reflect i z ≠ 0 ↔ z ≠ 0 := by
  constructor <;> intro h hn
  · exact h (by rw [hn, reflect_zero])
  · have := congrArg (reflect i) hn
    rw [reflect_involutive, reflect_zero] at this
    exact h this

/-- Reflecting one coordinate of an integer index preserves the physical radius. -/
lemma radius_reflect {d : ℕ} (ε : ℝ) (i : Fin d) (z : Site d) :
    radius (physical ε (reflect i z)) = radius (physical ε z) := by
  unfold radius
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = i <;> simp [physical, reflect, hk]

/-- Coordinate reflection preserves membership in `unitBallIndices d ε`. -/
lemma reflect_mem_unitBallIndices {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin d)
    (z : Site d) : reflect i z ∈ unitBallIndices d ε ↔ z ∈ unitBallIndices d ε := by
  rw [mem_unitBallIndices hε, mem_unitBallIndices hε, reflect_ne_zero, radius_reflect]

/-- The Euclidean radius is the norm of the vector in `EuclideanSpace ℝ (Fin d)`. -/
lemma radius_norm {d : ℕ} (v : Fin d → ℝ) :
    radius v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

/-- The Euclidean radius is 1-Lipschitz: `|radius x - radius y| ≤ radius (x - y)`. -/
lemma radius_difference {d : ℕ} (x y : Fin d → ℝ) :
    |radius x - radius y| ≤ radius (x-y) := by
  rw [radius_norm, radius_norm, radius_norm]
  exact abs_norm_sub_norm_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

/-- A nonzero integer point has physical radius at least one. -/
lemma lattice_radius_ge_one {d : ℕ} {w : Site d} (hw : w ≠ 0) :
    1 ≤ radius (physical 1 w) := by
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra! h
    exact hw (funext h)
  have hi : (1:ℤ) ≤ |w k| := by
    have := abs_pos.mpr hk
    omega
  have hr : (1:ℝ) ≤ |(w k : ℝ)| := by exact_mod_cast hi
  exact hr.trans (by simpa only [physical, one_mul] using abs_coord_le_radius (physical 1 w) k)

/-- The Euclidean radius is continuous on `Fin d → ℝ`. -/
lemma radius_continuous (d : ℕ) : Continuous (radius (d := d)) := by
  unfold radius
  exact Real.continuous_sqrt.comp
    (continuous_finsetSum _ (fun k _ => (continuous_apply k).pow 2))

/-- The Euclidean radius of the physical point `ε z` is `ε` times the radius of `z`. -/
lemma radius_physical_eq_mul {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (z : Site d) :
    radius (physical ε z) = ε * radius (physical 1 z) := by
  simp only [radius, physical]
  have h : ∑ k, (ε * (z k : ℝ)) ^ 2 = ε ^ 2 * ∑ k, (1 * (z k : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]

end LatticeProb.Euclidean.Lattice

/-
Rounding a point of `ℝ^d` to the nearest site of `ℤ^d`, moved from
`Exploding-Sandpiles`'s `Exploding/Support/Vocab.lean:186` and
`Exploding/Support/Gen.lean`.  There the rounding assembles the continuum
scaling-limit statements of `exploding.tex` (Theorem 5.2, Theorem 1.3); the
facts here are paper-independent: they only compare `nearestSite y` with `y`
and with `LatticeProb.box`, the sup-norm box already in `LatticeProb.Site`
(the source repo's own `cent d n = {x | ∀ i, |x i| ≤ n}` is the same set,
under a different name, as `LatticeProb.box d n`; this file uses the shared
name).
-/
import LatticeProb.Site

namespace LatticeProb

variable {d : ℕ}

/-- `[y]`, the nearest lattice point to `y ∈ ℝ^d`, ties broken by the
coordinatewise minimum. -/
noncomputable def nearestSite (y : Fin d → ℝ) : Site d := fun i => ⌈y i - 1 / 2⌉

/-- The nearest lattice point to `y` is within `1` of `y` in every
coordinate. -/
theorem nearestSite_sub_le (y : Fin d → ℝ) (i : Fin d) :
    |(nearestSite y i : ℝ) - y i| ≤ 1 := by
  simp only [nearestSite]
  rw [abs_sub_le_iff]
  constructor
  · have h := Int.ceil_lt_add_one (y i - 1 / 2)
    linarith
  · have h := Int.le_ceil (y i - 1 / 2)
    linarith

/-- If every coordinate of `y` is bounded by `m`, then every coordinate of
`nearestSite y` is bounded by `m + 1`. -/
theorem nearestSite_abs_le (y : Fin d → ℝ) (m : ℤ) (h : ∀ i, |y i| ≤ (m : ℝ))
    (i : Fin d) : |nearestSite y i| ≤ m + 1 := by
  rw [abs_le]
  constructor
  · have hy := (abs_le.mp (h i)).1
    simp only [nearestSite]
    have hlt : ((-(m + 1) - 1 : ℤ) : ℝ) < y i - 1 / 2 := by
      push_cast
      linarith
    have : (-(m + 1) - 1 : ℤ) < ⌈y i - 1 / 2⌉ := by
      rw [Int.lt_ceil]
      exact hlt
    omega
  · have hy := (abs_le.mp (h i)).2
    simp only [nearestSite]
    rw [Int.ceil_le]
    push_cast
    linarith

/-- A compact subset of `ℝ^d` is contained in a coordinate box of natural side
length. -/
theorem exists_nat_bound_of_isCompact {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    ∃ C : ℕ, ∀ y ∈ K, ∀ i, |y i| ≤ (C : ℝ) := by
  obtain ⟨R, hR⟩ := Bornology.IsBounded.exists_norm_le (IsCompact.isBounded hK)
  refine ⟨⌈max R 0⌉₊, fun y hy i => ?_⟩
  have h1 : ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm y i
  have h2 : ‖y‖ ≤ R := hR y hy
  have h3 : |y i| ≤ R := by
    rw [← Real.norm_eq_abs]
    linarith
  have h4 : R ≤ (⌈max R 0⌉₊ : ℝ) := le_trans (le_max_left _ _) (Nat.le_ceil _)
  linarith

/-- If every coordinate of `y` is bounded by `C`, then `nearestSite (n • y)`
lies in the box `LatticeProb.box d (n * (C + 1) + 1)`. -/
theorem nearestSite_smul_mem_box (y : Fin d → ℝ) (C n : ℕ)
    (h : ∀ i, |y i| ≤ (C : ℝ)) :
    nearestSite ((n : ℝ) • y) ∈ box d (n * (C + 1) + 1) := by
  simp only [box, Set.mem_setOf_eq]
  intro i
  have hm : ∀ j, |((n : ℝ) • y) j| ≤ (((n : ℤ) * (C + 1) : ℤ) : ℝ) := by
    intro j
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have hC1 : |y j| ≤ ((C : ℝ) + 1) := by linarith [h j]
    have := mul_le_mul_of_nonneg_left hC1 (Nat.cast_nonneg n)
    push_cast at this ⊢
    linarith
  have hb := nearestSite_abs_le ((n : ℝ) • y) ((n : ℤ) * (C + 1)) hm i
  have hcast : (((n * (C + 1) + 1 : ℕ)) : ℤ) = (n : ℤ) * (C + 1) + 1 := by push_cast; ring
  rw [hcast]
  exact hb

end LatticeProb

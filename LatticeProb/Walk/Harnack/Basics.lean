import LatticeProb.Site
import LatticeProb.Network.KilledGreen
import LatticeProb.Graph.Zd
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Walk.SRW
import LatticeProb.Walk.GreenTwoSided


/-!
# Boxes, the Laplacian, and the killed Green function

The box `harnackBox d r = [-r,r]^d`, the killed Green function `harnackGreen` (with pole in its
first argument), the Dirichlet-extension operator `harnackExt`, and the outer shell
`harnackShell`; box-containment and neighbour-stepping facts; the discrete Poisson equation
`nbrSum (harnackGreen B · y) x = 2d harnackGreen B x y - 1{x=y}`; and linearity of the
neighbour-sum operator `nbrSum`.
-/

open Finset
open scoped Classical

namespace LatticeProb

variable {d : ℕ}

/-! ### Auxiliary definitions -/

/-- The box `[-r, r]^d` as a `Finset`. -/
noncomputable def harnackBox (d r : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)

/-- The killed Green function of the finite set `B`, as a function of its FIRST argument `x`
with pole `y`: `harnackGreen B x y = g_B(y, x)` in the library's normalization, so that
`nbrSum (· ↦ harnackGreen B · y) x - 2d · harnackGreen B x y = -1{x = y}` for `x ∈ B`. -/
noncomputable def harnackGreen (B : Finset (Site d)) (x y : Site d) : ℝ :=
  Graph.killedGreenReal (lattice d) (B : Set (Site d)) y x

/-- The solution of the Dirichlet problem on `B \ K` with data `u` on `K` and `0` off `B`. -/
noncomputable def harnackExt (B K : Finset (Site d)) (u : Site d → ℝ) (x : Site d) : ℝ :=
  (if x ∈ K then u x else 0) +
    ∑ y ∈ B \ K, harnackGreen (B \ K) x y * nbrSum (fun z => if z ∈ K then u z else 0) y

/-- The outer shell of the box of radius `R + R/2`. -/
noncomputable def harnackShell (d R : ℕ) : Finset (Site d) :=
  harnackBox d (R + R / 2) \ harnackBox d (R + R / 2 - 1)

/-! ### Boxes -/

-- simp [harnackBox, box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
/-- `x ∈ harnackBox d r ↔ x ∈ box d r`: the two box definitions agree. -/
theorem mem_harnackBox_iff_mem_box (r : ℕ) (x : Site d) : x ∈ harnackBox d r ↔ x ∈ box d r
    := by
  simp [harnackBox, box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]


-- intro j; by_cases j = i; simp [unit, Pi.single_apply, box] at *; abs_le; push_cast; omega
/-- Both unit-neighbours of a point in `box d r` lie in `box d (r+1)`. -/
theorem unit_add_sub_mem_box_succ (r : ℕ) (x : Site d) (i : Fin d) (hx : x ∈ box d r) :
    x + unit i ∈ box d (r + 1) ∧ x - unit i ∈ box d (r + 1) := by
  constructor <;> intro j <;> rw [abs_le]
  · rcases eq_or_ne j i with hji | hji
    · rw [hji]
      have hi := (abs_le.mp (hx i) : -(r:ℤ) ≤ x i ∧ x i ≤ (r:ℤ))
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      push_cast
      omega
    · have hj := (abs_le.mp (hx j) : -(r:ℤ) ≤ x j ∧ x j ≤ (r:ℤ))
      simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hji, add_zero]
      push_cast
      omega
  · rcases eq_or_ne j i with hji | hji
    · rw [hji]
      have hi := (abs_le.mp (hx i) : -(r:ℤ) ≤ x i ∧ x i ≤ (r:ℤ))
      simp only [Pi.sub_apply, unit, Pi.single_eq_same]
      push_cast
      omega
    · have hj := (abs_le.mp (hx j) : -(r:ℤ) ≤ x j ∧ x j ≤ (r:ℤ))
      simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
      push_cast
      omega


-- intro j; exact le_trans (hx j) (by exact_mod_cast h)   [box is `{x | ∀ i, |x i| ≤ r}`]
/-- Box monotonicity: `x ∈ box d r` and `r ≤ s` give `x ∈ box d s`. -/
theorem mem_box_of_le {r s : ℕ} (h : r ≤ s) {x : Site d} (hx : x ∈ box d r) : x ∈ box d s :=
    by
  intro i
  exact le_trans (hx i) (by exact_mod_cast h)


/-! ### The lattice Laplacian and the killed Green function -/

-- The neighbour sum over `(lattice d).neighborFinset x` is `nbrSum`: Graph.Zd.walkOp_eq gives
-- (∑ nbrs)/deg = nbrSum/(2d); unfold Graph.walkOp, LatticeProb.walkOp, rewrite the degree with
-- Graph.Zd.degree_eq (push_cast) and cancel the common nonzero denominator (div_left_inj').
/-- The sum of `f` over the graph-theoretic neighbour finset of `x` equals `nbrSum f x`. -/
private theorem sum_neighborFinset_eq_nbrSum (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    ∑ y ∈ (lattice d).neighborFinset x, f y = nbrSum f x := by
  have hw := Graph.Zd.walkOp_eq f x
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  rw [Graph.walkOp, LatticeProb.walkOp, Graph.Zd.degree_eq] at hw
  push_cast at hw
  exact (div_left_inj' hd0).mp hw

-- Graph.Zd.degree_eq, push_cast.
/-- The lattice graph has degree `2d` at every vertex, as a real number. -/
private theorem cast_degree_eq_two_mul (x : Site d) : ((lattice d).degree x : ℝ) = 2 * (d : ℝ) := by
  rw [Graph.Zd.degree_eq]; push_cast; ring

-- unfold Graph.laplacian; Finset.sum_sub_distrib, Finset.sum_const,
-- SimpleGraph.card_neighborFinset_eq_degree,
-- Graph.Zd.degree_eq; the neighbour sum: Graph.Zd.walkOp_eq unfolded (Graph.walkOp,
-- LatticeProb.walkOp)
-- gives (∑ nbrs)/(2d) = nbrSum/(2d), cancel with field_simp using 0 < d.
/-- The graph Laplacian unfolds to `nbrSum f x - 2d f x`. -/
theorem laplacian_eq_nbrSum_sub (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    Graph.laplacian (lattice d) f x = nbrSum f x - 2 * (d : ℝ) * f x := by
  have hs := sum_neighborFinset_eq_nbrSum hd f x
  have hdeg := cast_degree_eq_two_mul (d := d) x
  unfold Graph.laplacian
  rw [Finset.sum_sub_distrib, hs, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul, hdeg]

-- haveI : NeZero d := ⟨by omega⟩; haveI := Graph.Zd.latticeInfinite d; exact
-- Infinite.exists_notMem_finset B
/-- Every finite set `B` misses some lattice point, since the lattice is infinite. -/
theorem exists_not_mem_finset (hd : 1 ≤ d) (B : Finset (Site d)) : ∃ q : Site d, q ∉ B := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Infinite (Site d) := Graph.Zd.latticeInfinite d
  exact Infinite.exists_notMem_finset B


-- NeZero d; exists_not_mem_finset for q; Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected
-- d) B hq y x
/-- `harnackGreen B x y ≥ 0`. -/
private theorem harnackGreen_nonneg (hd : 1 ≤ d) (B : Finset (Site d)) (x y : Site d) :
    0 ≤ harnackGreen B x y := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  unfold harnackGreen
  exact Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected d) B hq y x


-- NeZero d; exists_not_mem_finset; Network.killedGreenReal_eq_zero_of_not_mem
-- (Graph.Zd.latticeConnected d) B hq hx y
/-- `harnackGreen B x y = 0` when `x ∉ B`. -/
theorem harnackGreen_eq_zero_of_not_mem (hd : 1 ≤ d) (B : Finset (Site d)) {x : Site d}
    (hx : x ∉ B) (y : Site d) :
    harnackGreen B x y = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := exists_not_mem_finset hd B
  unfold harnackGreen
  exact Network.killedGreenReal_eq_zero_of_not_mem (Graph.Zd.latticeConnected d) B hq hx y


-- Network.laplacian_killedGreenReal (Graph.Zd.latticeConnected d) B hy hq (hv := hx) rewritten by
-- laplacian_eq_nbrSum_sub (with f := harnackGreen B · y, unfold harnackGreen); then linarith.
/-- For `x, y ∈ B`, `nbrSum (harnackGreen B · y) x = 2d * harnackGreen B x y - indicator (x =
y)`, the discrete Poisson equation for the Green function. -/
theorem nbrSum_harnackGreen_eq (hd : 1 ≤ d) (B : Finset (Site d)) {x y : Site d}
    (hx : x ∈ B)
    (hy : y ∈ B) :
    nbrSum (fun w => harnackGreen B w y) x
      = 2 * (d : ℝ) * harnackGreen B x y - (if x = y then 1 else 0) := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset hd B
  haveI : NeZero d := ⟨by omega⟩
  have hG : (lattice d).Connected := Graph.Zd.latticeConnected d
  have hk := Network.laplacian_killedGreenReal hG B (o := y) (q := q) hy hq (v := x) hx
  have h4 := laplacian_eq_nbrSum_sub hd (fun w => harnackGreen B w y) x
  simp only [harnackGreen] at hk h4 ⊢
  rw [hk] at h4
  by_cases hxy : x = y
  · rw [if_pos hxy] at h4 ⊢
    linarith only [h4]
  · rw [if_neg hxy] at h4 ⊢
    linarith only [h4]


/-! ### Neighbour sums -/

-- unfold nbrSum; Finset.sum_congr rfl; rw [(h i).1, (h i).2]
/-- `nbrSum f x = nbrSum g x` whenever `f` and `g` agree at every neighbour of `x`. -/
theorem nbrSum_congr {f g : Site d → ℝ} {x : Site d}
    (h : ∀ i, f (x + unit i) = g (x + unit i) ∧ f (x - unit i) = g (x - unit i)) :
    nbrSum f x = nbrSum g x := by
  unfold nbrSum
  exact Finset.sum_congr rfl fun i _ => by rw [(h i).1, (h i).2]


-- unfold nbrSum; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]; Finset.sum_congr rfl; ring
/-- `nbrSum` is linear: `nbrSum (a•f + b•g) x = a * nbrSum f x + b * nbrSum g x`. -/
theorem nbrSum_add_const_mul (a b : ℝ) (f g : Site d → ℝ) (x : Site d) :
    nbrSum (fun z => a * f z + b * g z) x = a * nbrSum f x + b * nbrSum g x := by
  unfold nbrSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


-- unfold nbrSum; simp only [Finset.sum_mul, ← Finset.sum_add_distrib]; exact Finset.sum_comm
/-- `nbrSum` commutes with a finite weighted sum: `nbrSum (∑_y F y * c y) x = ∑_y nbrSum (F y) x
* c y`. -/
theorem nbrSum_sum_mul {ι : Type*} (s : Finset ι) (F : ι → Site d → ℝ) (c : ι → ℝ)
    (x : Site d) :
    nbrSum (fun z => ∑ y ∈ s, F y z * c y) x = ∑ y ∈ s, nbrSum (F y) x * c y := by
  unfold nbrSum
  have h1 : ∑ i : Fin d, ∑ y ∈ s, F y (x + unit i) * c y
      = ∑ y ∈ s, ∑ i : Fin d, F y (x + unit i) * c y := Finset.sum_comm
  have h2 : ∑ i : Fin d, ∑ y ∈ s, F y (x - unit i) * c y
      = ∑ y ∈ s, ∑ i : Fin d, F y (x - unit i) * c y := Finset.sum_comm
  rw [Finset.sum_add_distrib, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y hy => ?_
  simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib]

end LatticeProb

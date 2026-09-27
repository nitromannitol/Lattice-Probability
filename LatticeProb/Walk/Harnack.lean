/-
The Harnack inequality for nonnegative harmonic functions on a box of `ℤ^d`.

`harnack` states: for `d ≥ 1` there is `C > 0` such that for every `R ≥ 1` and every
`u : Site d → ℝ` that is nonnegative on `box d (2R)` and harmonic on `box d (2R-1)`
(`nbrSum u x = 2d u x`), one has `u x ≤ C u y` for all `x, y ∈ box d R`.

Route (balayage / Riesz decomposition, Barlow, *Random Walks and Heat Kernels on Graphs*, §7).
Write `B = box (2R-1)`, `K = box (R + R/2)`, and let `v` be the Dirichlet extension of `u|K`
that is harmonic on `B \ K` and `0` off `B`.  The minimum principle gives `v ≤ u`, so the charge
`ν = 2d·v − nbrSum v ≥ 0` lives on the shell `∂_in K`, and `u(x) = ∑_{y ∈ shell} g_B(x,y) ν(y)`
on `box R` (Riesz representation).  The Harnack inequality then follows from the two-sided
bound `g_B(x,y) ≍ R^{2-d}` uniformly for `x ∈ box R`, `y ∈ shell`, which is
`LatticeProb.GreenTwoSided.killedGreenReal_{le,ge}_box`.  For small `R < 4` the neighbour chain
`u(x ± e_i) ≤ 2d·u(x)` gives `u x ≤ (2d)^{2Rd} u y`.

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import LatticeProb.Site
import LatticeProb.Network.KilledGreen
import LatticeProb.Graph.Zd
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Walk.SRW
import LatticeProb.Walk.GreenTwoSided

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
private theorem mem_harnackBox_iff_mem_box (r : ℕ) (x : Site d) : x ∈ harnackBox d r ↔ x ∈ box d r
    := by
  simp [harnackBox, box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]


-- intro j; by_cases j = i; simp [unit, Pi.single_apply, box] at *; abs_le; push_cast; omega
/-- Both unit-neighbours of a point in `box d r` lie in `box d (r+1)`. -/
private theorem unit_add_sub_mem_box_succ (r : ℕ) (x : Site d) (i : Fin d) (hx : x ∈ box d r) :
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
private theorem mem_box_of_le {r s : ℕ} (h : r ≤ s) {x : Site d} (hx : x ∈ box d r) : x ∈ box d s :=
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
private theorem laplacian_eq_nbrSum_sub (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    Graph.laplacian (lattice d) f x = nbrSum f x - 2 * (d : ℝ) * f x := by
  have hs := sum_neighborFinset_eq_nbrSum hd f x
  have hdeg := cast_degree_eq_two_mul (d := d) x
  unfold Graph.laplacian
  rw [Finset.sum_sub_distrib, hs, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul, hdeg]

-- haveI : NeZero d := ⟨by omega⟩; haveI := Graph.Zd.latticeInfinite d; exact
-- Infinite.exists_notMem_finset B
/-- Every finite set `B` misses some lattice point, since the lattice is infinite. -/
private theorem exists_not_mem_finset (hd : 1 ≤ d) (B : Finset (Site d)) : ∃ q : Site d, q ∉ B := by
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
private theorem harnackGreen_eq_zero_of_not_mem (hd : 1 ≤ d) (B : Finset (Site d)) {x : Site d}
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
private theorem nbrSum_harnackGreen_eq (hd : 1 ≤ d) (B : Finset (Site d)) {x y : Site d}
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
private theorem nbrSum_congr {f g : Site d → ℝ} {x : Site d}
    (h : ∀ i, f (x + unit i) = g (x + unit i) ∧ f (x - unit i) = g (x - unit i)) :
    nbrSum f x = nbrSum g x := by
  unfold nbrSum
  exact Finset.sum_congr rfl fun i _ => by rw [(h i).1, (h i).2]


-- unfold nbrSum; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]; Finset.sum_congr rfl; ring
/-- `nbrSum` is linear: `nbrSum (a•f + b•g) x = a * nbrSum f x + b * nbrSum g x`. -/
private theorem nbrSum_add_const_mul (a b : ℝ) (f g : Site d → ℝ) (x : Site d) :
    nbrSum (fun z => a * f z + b * g z) x = a * nbrSum f x + b * nbrSum g x := by
  unfold nbrSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


-- unfold nbrSum; simp only [Finset.sum_mul, ← Finset.sum_add_distrib]; exact Finset.sum_comm
/-- `nbrSum` commutes with a finite weighted sum: `nbrSum (∑_y F y * c y) x = ∑_y nbrSum (F y) x
* c y`. -/
private theorem nbrSum_sum_mul {ι : Type*} (s : Finset ι) (F : ι → Site d → ℝ) (c : ι → ℝ)
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


/-! ### Maximum principle and Riesz decomposition -/

-- Network.le_of_harmonicOn (Graph.Zd.latticeConnected d) Network.isCond_unitCond A ∅ (-w) 0 hq
-- (q from exists_not_mem_finset); harmonicity via Network.netLaplacian_unitCond,
-- laplacian_eq_nbrSum_sub applied
-- to -w (nbrSum (-w) = -nbrSum w: simp [nbrSum]); conclude with neg_nonpos.
/-- The minimum principle: a function harmonic on `A` and nonnegative off `A` is nonnegative
everywhere. -/
private theorem nonneg_of_harmonicOn (hd : 1 ≤ d) (A : Finset (Site d)) (w : Site d → ℝ)
    (hharm : ∀ x ∈ A, nbrSum w x = 2 * (d : ℝ) * w x) (hout : ∀ z, z ∉ A → 0 ≤ w z) :
    ∀ z, 0 ≤ w z := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := exists_not_mem_finset hd A
  have key : ∀ z, (-1 : ℝ) * w z ≤ 0 :=
    Network.le_of_harmonicOn (Graph.Zd.latticeConnected d) Network.isCond_unitCond
      A ∅ (fun z => (-1 : ℝ) * w z) 0 hq
      (by
        intro x hx _
        rw [Network.netLaplacian_smul, Network.netLaplacian_unitCond, laplacian_eq_nbrSum_sub hd,
          hharm x hx]
        ring)
      (by
        intro x hx
        have := hout x hx
        linarith)
      (by
        intro x hx
        exact absurd hx (Set.notMem_empty x))
  intro z
  have := key z
  linarith


-- unfold nbrSum; ← Finset.sum_neg_distrib; Finset.sum_congr rfl (ring).
/-- `nbrSum (-w) x = -nbrSum w x`. -/
private theorem nbrSum_neg (w : Site d → ℝ) (x : Site d) :
    nbrSum (fun z => -w z) x = -nbrSum w x := by
  unfold nbrSum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

-- nonneg_of_harmonicOn for w and for -w (nbrSum of -w via nbrSum_add_const_mul with a=-1,b=0 or
-- simp [nbrSum]);
-- le_antisymm.
/-- A function harmonic on `A` and vanishing off `A` vanishes everywhere, by applying the minimum
principle to `w` and `-w`. -/
private theorem eq_zero_of_harmonicOn (hd : 1 ≤ d) (A : Finset (Site d)) (w : Site d → ℝ)
    (hharm : ∀ x ∈ A, nbrSum w x = 2 * (d : ℝ) * w x) (hout : ∀ z, z ∉ A → w z = 0) :
    ∀ z, w z = 0 := by
  intro z
  have h1 := nonneg_of_harmonicOn hd A w hharm (fun z hz => (hout z hz).ge) z
  have h2 := nonneg_of_harmonicOn hd A (fun z => -w z)
    (fun x hx => by rw [nbrSum_neg, hharm x hx]; ring)
    (fun z hz => by simp [hout z hz]) z
  linarith

-- Riesz: apply eq_zero_of_harmonicOn to h := w - RHS on A := B.  Off B: w = 0 and
-- harnackGreen_eq_zero_of_not_mem.
-- On B: nbrSum of RHS by nbrSum_sum_mul + nbrSum_harnackGreen_eq, Finset.sum_sub_distrib,
-- Finset.mul_sum, Finset.sum_ite_eq' (gives ρ x since x ∈ B); nbrSum h via nbrSum_add_const_mul;
-- ring.
-- SPLIT?
/-- `nbrSum (f - g) x = nbrSum f x - nbrSum g x`. -/
private theorem nbrSum_sub (f g : Site d → ℝ) (x : Site d) :
    nbrSum (fun z => f z - g z) x = nbrSum f x - nbrSum g x := by
  have h := nbrSum_add_const_mul (1 : ℝ) (-1) f g x
  simpa only [one_mul, neg_mul, sub_eq_add_neg] using h

/-- Implementation lemma for `eq_sum_harnackGreen_mul_laplacian`. -/
private theorem eq_sum_harnackGreen_mul_laplacian' (hd : 1 ≤ d) (B : Finset (Site d))
    (w : Site d → ℝ)
    (hw : ∀ x, x ∉ B → w x = 0) (x : Site d) :
    w x = ∑ y ∈ B, harnackGreen B x y * (2 * (d : ℝ) * w y - nbrSum w y) := by
  let c : Site d → ℝ := fun y => 2 * (d : ℝ) * w y - nbrSum w y
  let R : Site d → ℝ := fun z => ∑ y ∈ B, harnackGreen B z y * c y
  have hoff : ∀ z, z ∉ B → (w - R) z = 0 := by
    intro z hz
    have hRz : R z = 0 := by
      change (∑ y ∈ B, harnackGreen B z y * c y) = 0
      apply Finset.sum_eq_zero
      intro y hy
      rw [harnackGreen_eq_zero_of_not_mem hd B hz y, zero_mul]
    rw [Pi.sub_apply, hw z hz, hRz, sub_zero]
  have hharm : ∀ x ∈ B, nbrSum (w - R) x = 2 * (d : ℝ) * (w - R) x := by
    intro x hx
    have hR : nbrSum R x
        = ∑ y ∈ B, (2 * (d : ℝ) * harnackGreen B x y - (if x = y then 1 else 0)) * c y := by
      change nbrSum (fun z => ∑ y ∈ B, harnackGreen B z y * c y) x = _
      rw [nbrSum_sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      rw [nbrSum_harnackGreen_eq hd B hx hy]
    have hsplit : (∑ y ∈ B, (2 * (d : ℝ) * harnackGreen B x y - (if x = y then 1 else 0)) * c y)
        = (∑ y ∈ B, (2 * (d : ℝ) * harnackGreen B x y) * c y)
          - (∑ y ∈ B, (if x = y then (1 : ℝ) else 0) * c y) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    have hfirst : (∑ y ∈ B, (2 * (d : ℝ) * harnackGreen B x y) * c y) = 2 * (d : ℝ) * R x := by
      change _ = 2 * (d : ℝ) * (∑ y ∈ B, harnackGreen B x y * c y)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    have hsecond : (∑ y ∈ B, (if x = y then (1 : ℝ) else 0) * c y) = c x := by
      have h1 : (∑ y ∈ B, (if x = y then (1 : ℝ) else 0) * c y)
          = ∑ y ∈ B, (if x = y then c y else 0) :=
        Finset.sum_congr rfl (fun y _ => by rw [ite_mul, one_mul, zero_mul])
      rw [h1, Finset.sum_ite_eq, if_pos hx]
    change nbrSum (fun z => w z - R z) x = 2 * (d : ℝ) * (w x - R x)
    rw [nbrSum_sub w R x, hR, hsplit, hfirst, hsecond]
    have hcx : c x = 2 * (d : ℝ) * w x - nbrSum w x := rfl
    rw [hcx]
    ring
  have hx0 : w x - R x = 0 := by
    have h := eq_zero_of_harmonicOn hd B (w - R) hharm hoff x
    simpa only [Pi.sub_apply] using h
  have hwx : w x = R x := sub_eq_zero.mp hx0
  calc w x = R x := hwx
    _ = ∑ y ∈ B, harnackGreen B x y * (2 * (d : ℝ) * w y - nbrSum w y) := rfl

/-- The Riesz representation formula: a function `w` vanishing off `B` satisfies `w x = ∑_{y ∈ B}
harnackGreen B x y * (2d w y - nbrSum w y)`. -/
private theorem eq_sum_harnackGreen_mul_laplacian (hd : 1 ≤ d) (B : Finset (Site d))
    (w : Site d → ℝ)
    (hw : ∀ x, x ∉ B → w x = 0) (x : Site d) :
    w x = ∑ y ∈ B, harnackGreen B x y * (2 * (d : ℝ) * w y - nbrSum w y) := by
  exact eq_sum_harnackGreen_mul_laplacian' hd B w hw x


/-! ### The Dirichlet problem on `B \ K` -/

-- unfold harnackExt; if_pos hx; each summand has harnackGreen (B \ K) x y = 0 by
-- harnackGreen_eq_zero_of_not_mem
-- (x ∉ B \ K since x ∈ K: Finset.mem_sdiff); Finset.sum_eq_zero; add_zero.
/-- `harnackExt B K u x = u x` for `x ∈ K`: the extension agrees with `u` on `K`. -/
private theorem harnackExt_eq_of_mem (hd : 1 ≤ d) (B K : Finset (Site d)) (u : Site d → ℝ)
    {x : Site d}
    (hx : x ∈ K) : harnackExt B K u x = u x := by
  unfold harnackExt
  rw [if_pos hx]
  have hzero : ∀ y ∈ B \ K, harnackGreen (B \ K) x y * nbrSum (fun z => if z ∈ K then u z else 0) y
      = 0 :=
    fun y hy => by
      have hx' : x ∉ B \ K := fun h => (Finset.mem_sdiff.mp h).2 hx
      rw [harnackGreen_eq_zero_of_not_mem hd (B \ K) hx' y, zero_mul]
  rw [Finset.sum_eq_zero hzero, add_zero]


-- unfold harnackExt; x ∉ K (hK : K ⊆ B); x ∉ B \ K; harnackGreen_eq_zero_of_not_mem kills the sum.
/-- `harnackExt B K u x = 0` for `x ∉ B`. -/
private theorem harnackExt_eq_zero_of_not_mem (hd : 1 ≤ d) (B K : Finset (Site d)) (hK : K ⊆ B)
    (u : Site d → ℝ)
    {x : Site d} (hx : x ∉ B) : harnackExt B K u x = 0 := by
  simp only [harnackExt, if_neg (show x ∉ K from fun h => hx (hK h)), zero_add]
  apply Finset.sum_eq_zero
  intro y hy
  rw
      [harnackGreen_eq_zero_of_not_mem hd (B \ K) (show x ∉ B \ K from fun h => hx
          (Finset.mem_sdiff.mp h).1) y,
    zero_mul]


-- A := B \ K, f := indicator of K times u.  nbrSum (harnackExt) x = nbrSum f x
-- + ∑_{y∈A} nbrSum (harnackGreen A · y) x * nbrSum f y  (nbrSum_add_const_mul/11 after `show` the
-- function as a sum), = nbrSum f x + ∑ (2d g(x,y) - 1{x=y}) nbrSum f y  (nbrSum_harnackGreen_eq,
-- x,y ∈ A)
-- = 2d ∑ g(x,y) nbrSum f y  (Finset.sum_ite_eq'), and f x = 0 since x ∉ K.  SPLIT?
/-- `harnackExt B K u` is harmonic on `B \ K`: `nbrSum (harnackExt B K u) x = 2d * harnackExt B K
u x` there. -/
private theorem nbrSum_harnackExt_eq_of_mem_sdiff (hd : 1 ≤ d) (B K : Finset (Site d))
    (u : Site d → ℝ) {x : Site d}
    (hxB : x ∈ B) (hxK : x ∉ K) :
    nbrSum (harnackExt B K u) x = 2 * (d : ℝ) * harnackExt B K u x := by
  have hxA : x ∈ B \ K := Finset.mem_sdiff.mpr ⟨hxB, hxK⟩
  have h1 : ∀ y ∈ (B \ K), nbrSum (fun z => harnackGreen (B \ K) z y) x = 2 * (d : ℝ) * harnackGreen
      (B \ K) x y - (if x = y then 1 else 0) := fun y hy => nbrSum_harnackGreen_eq hd (B \ K) hxA hy
  have hstep : nbrSum (harnackExt B K u) x = nbrSum (fun z => if z ∈ K then u z else 0) x + ∑ y ∈ B
      \ K, nbrSum (fun z => harnackGreen (B \ K) z y) x * nbrSum (fun z => if z ∈ K then u z else 0)
          y := (by
    have hfun : harnackExt B K u = fun z => (1 : ℝ) * (if z ∈ K then u z else 0) + 1 *
        (∑ y ∈ B \ K, harnackGreen (B \ K) z y * nbrSum (fun z => if z ∈ K then u z else 0) y) :=
            (by
      funext z
      simp [harnackExt])
    rw [hfun]
    rw
        [nbrSum_add_const_mul (1 : ℝ) 1 (fun z => if z ∈ K then u z else 0) (fun z => ∑ y ∈ B \ K,
            harnackGreen (B \ K) z y * nbrSum (fun z => if z ∈ K then u z else 0) y) x]
    rw
        [nbrSum_sum_mul (B \ K) (fun y z => harnackGreen (B \ K) z y) (fun y => nbrSum (fun z => if
            z ∈ K then u z else 0) y) x]
    ring)
  have hsum2 : ∑ y ∈ B \ K, nbrSum (fun z => harnackGreen (B \ K) z y) x * nbrSum
      (fun z => if z ∈ K then u z else 0) y = 2 * (d : ℝ) *
          (∑ y ∈ B \ K, harnackGreen (B \ K) x y * nbrSum (fun z => if z ∈ K then u z else 0) y) -
              nbrSum (fun z => if z ∈ K then u z else 0) x := (by
    have hpt : ∀ y ∈ (B \ K), nbrSum (fun z => harnackGreen (B \ K) z y) x * nbrSum
        (fun z => if z ∈ K then u z else 0) y = 2 * (d : ℝ) * harnackGreen (B \ K) x y * nbrSum
            (fun z => if z ∈ K then u z else 0) y - (if x = y then 1 else 0) * nbrSum
                (fun z => if z ∈ K then u z else 0) y := fun y hy => by
      rw [h1 y hy, sub_mul]
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y hy => by ring)
    · simp only [ite_mul, one_mul, zero_mul]
      rw
          [Finset.sum_ite_eq (B \ K) x (fun y => nbrSum (fun z => if z ∈ K then u z else 0) y),
              if_pos hxA])
  have hExt : harnackExt B K u x = ∑ y ∈ B \ K, harnackGreen (B \ K) x y * nbrSum
      (fun z => if z ∈ K then u z else 0) y := (by
    simp only [harnackExt]
    rw [if_neg hxK, zero_add])
  rw [hstep, hsum2, hExt]
  ring


-- Comparison v ≤ u.  Apply nonneg_of_harmonicOn on A := B \ K to w := fun z => if z ∈ D then u z -
-- v z else 0
-- (v := harnackExt B K u).  Harmonic on A: nbrSum_congr (neighbours in D by hnb, w = u - v there),
-- nbrSum_add_const_mul, hharm, nbrSum_harnackExt_eq_of_mem_sdiff.  Outside A: z ∈ K gives 0
-- (harnackExt_eq_of_mem);
-- z ∉ B, z ∈ D gives u z - 0 ≥ 0 (harnackExt_eq_zero_of_not_mem, hpos); z ∉ D gives 0.  SPLIT?
/-- The comparison principle: if `u` is nonnegative and harmonic on a set `D ⊇ B` closed under
the relevant neighbour steps, then `harnackExt B K u ≤ u` on `B`. -/
private theorem harnackExt_le_of_harmonicOn (hd : 1 ≤ d) (B K : Finset (Site d)) (hK : K ⊆ B)
    (D : Set (Site d))
    (u : Site d → ℝ) (hBD : ∀ x ∈ B, x ∈ D)
    (hnb : ∀ x ∈ B, ∀ i : Fin d, x + unit i ∈ D ∧ x - unit i ∈ D)
    (hpos : ∀ x ∈ D, 0 ≤ u x) (hharm : ∀ x ∈ B, nbrSum u x = 2 * (d : ℝ) * u x)
    {x : Site d} (hx : x ∈ B) : harnackExt B K u x ≤ u x := by
  have h1 : ∀ y ∈ B \ K, nbrSum (fun z => if z ∈ D then u z - harnackExt B K u z else 0) y
      = 2 * (d : ℝ) * (fun z => if z ∈ D then u z - harnackExt B K u z else 0) y := (by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨hyB, hyK⟩ := hy
    have hne : ∀ i : Fin d,
        (fun z => if z ∈ D then u z - harnackExt B K u z else 0) (y + unit i)
            = (fun z => u z - harnackExt B K u z) (y + unit i) ∧
        (fun z => if z ∈ D then u z - harnackExt B K u z else 0) (y - unit i)
            = (fun z => u z - harnackExt B K u z) (y - unit i) := (by
      intro i
      obtain ⟨e1, e2⟩ := hnb y hyB i
      exact ⟨by simp only [if_pos e1], by simp only [if_pos e2]⟩)
    have h9 : nbrSum (fun z => if z ∈ D then u z - harnackExt B K u z else 0) y
        = nbrSum (fun z => u z - harnackExt B K u z) y :=
      nbrSum_congr (f := fun z => if z ∈ D then u z - harnackExt B K u z else 0)
        (g := fun z => u z - harnackExt B K u z) (x := y) hne
    have h10 : nbrSum (fun z => u z - harnackExt B K u z) y
        = nbrSum u y - nbrSum (harnackExt B K u) y := (by
      have h := nbrSum_add_const_mul (1 : ℝ) (-1) u (harnackExt B K u) y
      simpa [sub_eq_add_neg, neg_mul, one_mul] using h)
    have hu : nbrSum u y = 2 * (d : ℝ) * u y := hharm y hyB
    have hv : nbrSum (harnackExt B K u) y = 2 * (d : ℝ) * harnackExt B K u y :=
      nbrSum_harnackExt_eq_of_mem_sdiff hd B K u hyB hyK
    rw [h9, h10, hu, hv]
    simp only [if_pos (hBD y hyB)]
    ring)
  have h2 : ∀ z, z ∉ B \ K → 0 ≤ (fun z => if z ∈ D then u z - harnackExt B K u z else 0) z := (by
    intro y hy
    change 0 ≤ (if y ∈ D then u y - harnackExt B K u y else 0)
    by_cases hyD : y ∈ D
    · rw [if_pos hyD]
      by_cases hyK : y ∈ K
      · rw [harnackExt_eq_of_mem hd B K u hyK]; simp
      · have hyB : y ∉ B := fun h => hy (Finset.mem_sdiff.mpr ⟨h, hyK⟩)
        rw [harnackExt_eq_zero_of_not_mem hd B K hK u hyB]
        simpa using hpos y hyD
    · rw [if_neg hyD])
  have h3 := nonneg_of_harmonicOn hd (B \ K)
    (fun z => if z ∈ D then u z - harnackExt B K u z else 0) h1 h2 x
  simp only [if_pos (hBD x hx)] at h3
  linarith


-- v y = u y (harnackExt_eq_of_mem) and nbrSum v y ≤ nbrSum u y termwise (unfold nbrSum;
-- Finset.sum_le_sum; add_le_add): a neighbour z in B uses harnackExt_le_of_harmonicOn, a neighbour
-- z ∉ B has
-- v z = 0 (harnackExt_eq_zero_of_not_mem) ≤ u z (hpos, hnb).  Then hharm y (hK hy); linarith.
/-- For `y ∈ K`, `nbrSum (harnackExt B K u) y ≤ nbrSum u y`, comparing the extension's neighbour
sum with that of `u`. -/
private theorem nbrSum_harnackExt_le_nbrSum {d : ℕ} (hd : 1 ≤ d) (B K : Finset (Site d))
    (hK : K ⊆ B) (D : Set (Site d))
    (u : Site d → ℝ) (hBD : ∀ x ∈ B, x ∈ D)
    (hnb : ∀ x ∈ B, ∀ i : Fin d, x + unit i ∈ D ∧ x - unit i ∈ D)
    (hpos : ∀ x ∈ D, 0 ≤ u x) (hharm : ∀ x ∈ B, nbrSum u x = 2 * (d : ℝ) * u x)
    {y : Site d} (hy : y ∈ K) :
    nbrSum (harnackExt B K u) y ≤ nbrSum u y := by
  have hyB : y ∈ B := hK hy
  have hstep : ∀ i : Fin d,
      harnackExt B K u (y + unit i) + harnackExt B K u (y - unit i)
        ≤ u (y + unit i) + u (y - unit i) := by
    intro i
    have h1 : harnackExt B K u (y + unit i) ≤ u (y + unit i) := by
      by_cases hz : y + unit i ∈ B
      · exact harnackExt_le_of_harmonicOn hd B K hK D u hBD hnb hpos hharm hz
      · rw [harnackExt_eq_zero_of_not_mem hd B K hK u hz]
        exact hpos _ (hnb y hyB i).1
    have h2 : harnackExt B K u (y - unit i) ≤ u (y - unit i) := by
      by_cases hz : y - unit i ∈ B
      · exact harnackExt_le_of_harmonicOn hd B K hK D u hBD hnb hpos hharm hz
      · rw [harnackExt_eq_zero_of_not_mem hd B K hK u hz]
        exact hpos _ (hnb y hyB i).2
    linarith
  simp only [nbrSum]
  exact Finset.sum_le_sum (fun i _ => hstep i)

/-- The balayage charge `2d * harnackExt B K u y - nbrSum (harnackExt B K u) y` is nonnegative on
`K`. -/
private theorem zero_le_two_mul_harnackExt_sub_nbrSum (hd : 1 ≤ d) (B K : Finset (Site d))
    (hK : K ⊆ B) (D : Set (Site d))
    (u : Site d → ℝ) (hBD : ∀ x ∈ B, x ∈ D)
    (hnb : ∀ x ∈ B, ∀ i : Fin d, x + unit i ∈ D ∧ x - unit i ∈ D)
    (hpos : ∀ x ∈ D, 0 ≤ u x) (hharm : ∀ x ∈ B, nbrSum u x = 2 * (d : ℝ) * u x)
    {y : Site d} (hy : y ∈ K) :
    0 ≤ 2 * (d : ℝ) * harnackExt B K u y - nbrSum (harnackExt B K u) y := by
  have hle := nbrSum_harnackExt_le_nbrSum hd B K hK D u hBD hnb hpos hharm hy
  have hvy := harnackExt_eq_of_mem hd B K u hy
  have hh := hharm y (hK hy)
  rw [hvy]
  linarith


-- nbrSum_congr with harnackExt_eq_of_mem on y and all its neighbours (hnbK), then
-- harnackExt_eq_of_mem at y
-- and hharm; sub_self.
/-- The balayage charge vanishes at points of `K` all of whose neighbours are also in `K`, since
there `u` is harmonic and `harnackExt` agrees with `u`. -/
private theorem two_mul_harnackExt_sub_nbrSum_eq_zero (hd : 1 ≤ d) (B K : Finset (Site d))
    (u : Site d → ℝ) {y : Site d}
    (hy : y ∈ K) (hnbK : ∀ i : Fin d, y + unit i ∈ K ∧ y - unit i ∈ K)
    (hharm : nbrSum u y = 2 * (d : ℝ) * u y) :
    2 * (d : ℝ) * harnackExt B K u y - nbrSum (harnackExt B K u) y = 0 := by
  have h1 : harnackExt B K u y = u y := harnackExt_eq_of_mem hd B K u hy; have h2 : nbrSum
      (harnackExt B K u) y = nbrSum u y := nbrSum_congr
          (fun i => ⟨harnackExt_eq_of_mem hd B K u (hnbK i).1, harnackExt_eq_of_mem hd B K u (hnbK
              i).2⟩); rw [h1, h2, hharm]; ring


/-! ### Geometry of the three boxes (R ≥ 4) -/

-- intro x; rw [mem_harnackBox_iff_mem_box, mem_harnackBox_iff_mem_box]; mem_box_of_le with R + R/2
-- ≤ 2R - 1 (omega)
/-- `harnackBox d (R + R/2) ⊆ harnackBox d (2R-1)` for `R ≥ 4`. -/
private theorem harnackBox_add_div_two_subset {R : ℕ} (hR : 4 ≤ R) :
    harnackBox d (R + R / 2) ⊆ harnackBox d (2 * R - 1) := by
  intro x hx
  rw [mem_harnackBox_iff_mem_box] at hx ⊢
  exact mem_box_of_le (by omega) hx


-- (mem_harnackBox_iff_mem_box).2 (mem_box_of_le (by omega) hx)
/-- `x ∈ box d R` implies `x ∈ harnackBox d (R + R/2)`. -/
private theorem mem_harnackBox_add_div_two_of_mem_box {R : ℕ} {x : Site d} (hx : x ∈ box d R) : x ∈
    harnackBox d (R + R / 2) := by
  rw [mem_harnackBox_iff_mem_box]
  exact mem_box_of_le (by omega) hx


-- y ∉ shell and y ∈ harnackBox (R+R/2) ⇒ y ∈ harnackBox (R+R/2-1) (harnackShell, Finset.mem_sdiff);
-- then mem_harnackBox_iff_mem_box, unit_add_sub_mem_box_succ, and R + R/2 - 1 + 1 = R + R/2 (omega,
-- R ≥ 4).
/-- The unit-neighbours of a point in `harnackBox d (R+R/2)` outside the shell stay in
`harnackBox d (R+R/2)`. -/
private theorem unit_add_sub_mem_harnackBox_of_not_mem_shell {R : ℕ} (hR : 4 ≤ R) {y : Site d}
    (hy : y ∈ harnackBox d (R + R / 2))
    (hyS : y ∉ harnackShell d R) (i : Fin d) :
    y + unit i ∈ harnackBox d (R + R / 2) ∧ y - unit i ∈ harnackBox d (R + R / 2) := by
  have hy1 : y ∈ harnackBox d (R + R / 2 - 1) := (by
    by_contra hh
    exact hyS (by rw [harnackShell]; exact Finset.mem_sdiff.mpr ⟨hy, hh⟩))
  have hybox : y ∈ box d (R + R / 2 - 1) := (mem_harnackBox_iff_mem_box (R + R / 2 - 1) y).mp hy1
  obtain ⟨h1, h2⟩ := unit_add_sub_mem_box_succ (R + R / 2 - 1) y i hybox
  have heq : R + R / 2 - 1 + 1 = R + R / 2 := (by omega)
  rw [heq] at h1 h2
  exact ⟨(mem_harnackBox_iff_mem_box (R + R / 2) (y + unit i)).mpr h1,
    (mem_harnackBox_iff_mem_box (R + R / 2) (y - unit i)).mpr h2⟩


-- Finset.sdiff_subset.trans (harnackBox_add_div_two_subset hR)
/-- `harnackShell d R ⊆ harnackBox d (2R-1)` for `R ≥ 4`. -/
private theorem harnackShell_subset_harnackBox {R : ℕ} (hR : 4 ≤ R) :
    harnackShell d R ⊆ harnackBox d (2 * R - 1) := by
  intro x hx
  rw [harnackShell, Finset.mem_sdiff] at hx
  exact harnackBox_add_div_two_subset hR hx.1


/-! ### The shell representation -/

-- Riesz eq_sum_harnackGreen_mul_laplacian for v := harnackExt B K u (vanishes off B by
-- harnackExt_eq_zero_of_not_mem + harnackBox_add_div_two_subset),
-- then Finset.sum_subset (harnackShell_subset_harnackBox): for y ∈ B \ shell either y ∉ K, where
-- the charge is 0 by
-- nbrSum_harnackExt_eq_of_mem_sdiff, or y ∈ K \ shell, where it is 0 by
-- two_mul_harnackExt_sub_nbrSum_eq_zero + unit_add_sub_mem_harnackBox_of_not_mem_shell (harmonic at
-- y
-- from hharm, mem_harnackBox_iff_mem_box, harnackBox_add_div_two_subset).  SPLIT?
/-- The Riesz representation `eq_sum_harnackGreen_mul_laplacian` specialized to `v = harnackExt
(harnackBox (2R-1)) (harnackBox (R+R/2)) u`: the sum localizes to the shell, since the charge
vanishes off it. -/
private theorem harnackExt_eq_sum_shell_mul_charge (hd : 1 ≤ d) {R : ℕ} (hR : 4 ≤ R)
    (u : Site d → ℝ)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) (x : Site d) :
    harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u x
      = ∑ y ∈ harnackShell d R, harnackGreen (harnackBox d (2 * R - 1)) x y *
          (2 * (d : ℝ) * harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u y
            - nbrSum (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u) y) := by
  have hKB : harnackBox d (R + R / 2) ⊆ harnackBox d (2 * R - 1) := harnackBox_add_div_two_subset hR
  rw [eq_sum_harnackGreen_mul_laplacian hd (harnackBox d (2 * R - 1))
      (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u)
      (fun z hz => harnackExt_eq_zero_of_not_mem hd _ _ hKB u hz) x]
  symm
  refine Finset.sum_subset (s₁ := harnackShell d R) (s₂ := harnackBox d (2 * R - 1))
    (f := fun y => harnackGreen (harnackBox d (2 * R - 1)) x y *
      (2 * (d : ℝ) * harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u y
        - nbrSum (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u) y))
    (harnackShell_subset_harnackBox hR) ?_
  intro y hyB hyS
  apply mul_eq_zero.mpr
  right
  by_cases hyK : y ∈ harnackBox d (R + R / 2)
  · exact two_mul_harnackExt_sub_nbrSum_eq_zero hd _ _ u hyK
      (unit_add_sub_mem_harnackBox_of_not_mem_shell hR hyK hyS)
      (hharm y ((mem_harnackBox_iff_mem_box (2 * R - 1) y).1 hyB))
  · have h17 := nbrSum_harnackExt_eq_of_mem_sdiff hd (harnackBox d (2 * R - 1))
        (harnackBox d (R + R / 2)) u hyB hyK
    linarith


-- hBD: mem_harnackBox_iff_mem_box then mem_box_of_le (2R-1 ≤ 2R).  hnb: unit_add_sub_mem_box_succ
-- at radius 2R-1, and
-- 2R-1+1 = 2R (omega, 1 ≤ R).
/-- `harnackBox d (2R-1) ⊆ box d (2R)`, and its unit-neighbours also lie in `box d (2R)`. -/
private theorem harnackBox_subset_box_and_unit_mem {R : ℕ} (hR : 1 ≤ R) :
    (∀ x ∈ harnackBox d (2 * R - 1), x ∈ box d (2 * R)) ∧
    (∀ x ∈ harnackBox d (2 * R - 1), ∀ i : Fin d,
      x + unit i ∈ box d (2 * R) ∧ x - unit i ∈ box d (2 * R)) := by
  have hR2 : 2 * R - 1 + 1 = 2 * R := by omega
  refine ⟨fun x hx => mem_box_of_le (by
    omega) ((mem_harnackBox_iff_mem_box _ x).1 hx), fun x hx i => ?_⟩
  have h := unit_add_sub_mem_box_succ (2 * R - 1) x i ((mem_harnackBox_iff_mem_box _ x).1 hx)
  rw [hR2] at h
  exact h

-- unfold harnackShell; Finset.mem_sdiff.
/-- `harnackShell d R ⊆ harnackBox d (R + R/2)`. -/
private theorem harnackShell_subset_harnackBox_add_div_two {R : ℕ} {y : Site d}
    (hy : y ∈ harnackShell d R) :
    y ∈ harnackBox d (R + R / 2) := by
  unfold harnackShell at hy
  exact (Finset.mem_sdiff.mp hy).1

-- ν y := 2d v y - nbrSum v y on the shell, 0 elsewhere (v := harnackExt ...).  Nonneg by
-- zero_le_two_mul_harnackExt_sub_nbrSum with D := box d (2R) (hBD, hnb from
-- mem_harnackBox_iff_mem_box/2/3, omega on 2R-1+1 = 2R).
-- u x = v x by harnackExt_eq_of_mem + mem_harnackBox_add_div_two_of_mem_box, then
-- harnackExt_eq_sum_shell_mul_charge and Finset.sum_congr (if_pos).
/-- For `u` nonnegative on `box d (2R)` and harmonic on `box d (2R-1)`, there is a nonnegative
charge `ν` supported on the shell with `u x = ∑_{y ∈ shell} harnackGreen (harnackBox (2R-1))
x y * ν y` on `box d R`. -/
private theorem exists_nonneg_eq_sum_shell_mul (hd : 1 ≤ d) {R : ℕ} (hR : 4 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) :
    ∃ ν : Site d → ℝ, (∀ y, 0 ≤ ν y) ∧ ∀ x ∈ box d R,
      u x = ∑ y ∈ harnackShell d R, harnackGreen (harnackBox d (2 * R - 1)) x y * ν y := by
  have hKB : harnackBox d (R + R / 2) ⊆ harnackBox d (2 * R - 1) := harnackBox_add_div_two_subset hR
  obtain ⟨hBD, hnb⟩ := harnackBox_subset_box_and_unit_mem (d := d) (R := R) (by omega)
  have hharmB : ∀ x ∈ harnackBox d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x :=
    fun x hx => hharm x ((mem_harnackBox_iff_mem_box _ x).1 hx)
  refine ⟨fun y => if y ∈ harnackShell d R then
      2 * (d : ℝ) * harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u y
        - nbrSum (harnackExt (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u) y
    else 0, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ harnackShell d R
    · simp only [if_pos hy]
      exact zero_le_two_mul_harnackExt_sub_nbrSum hd _ _ hKB (box d (2 * R)) u hBD hnb hpos hharmB
          (harnackShell_subset_harnackBox_add_div_two hy)
    · simp only [if_neg hy, le_refl]
  · intro x hx
    rw [← harnackExt_eq_of_mem hd (harnackBox d (2 * R - 1)) (harnackBox d (R + R / 2)) u
      (mem_harnackBox_add_div_two_of_mem_box hx), harnackExt_eq_sum_shell_mul_charge hd hR u hharm
          x]
    exact Finset.sum_congr rfl fun y hy => by simp only [if_pos hy]

/-! ### Green function estimates at scale `R` (the analytic input) -/

-- This is `LatticeProb.GreenTwoSided.killedGreenReal_le_box`, whose statement (`box`,
-- `graphNorm`, `Graph.killedGreenReal` are all shared top-level library definitions, not local
-- to the `GreenTwoSided` namespace) is byte-identical to this one, and which already has a
-- complete proof in scratch/decomp/green-two-sided/node.lean (line 658): head
-- `∑_{k<N} killedHeat ≤ N·C/r^d` from `srwHeat_gaussian`, tail via the killed Chapman–Kolmogorov
-- identity and `Network.sum_range_survival_le`.  Wire this file to that module (or a shared
-- `Network.KilledGreen`-adjacent module) instead of reproving it here.
/-- Implementation lemma for `killedGreenReal_le_box_of_mem`, obtained directly from
`LatticeProb.GreenTwoSided.killedGreenReal_le_box`. -/
private theorem killedGreenReal_le_box_of_mem' (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) →
      ∀ x y : Site d, x ≠ y →
        Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
          ≤ C * ((L : ℝ) + 1) ^ 2 * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) :=
  LatticeProb.GreenTwoSided.killedGreenReal_le_box hd

/-- The two-sided Green function upper bound `LatticeProb.GreenTwoSided.killedGreenReal_le_box`,
restated for use in the Harnack argument. -/
private theorem killedGreenReal_le_box_of_mem (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (B : Finset (Site d)), (∀ z ∈ B, z ∈ box d L) →
      ∀ x y : Site d, x ≠ y →
        Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y
          ≤ C * ((L : ℝ) + 1) ^ 2 * (1 / (graphNorm (x - y) : ℝ) ^ d + 1 / ((L : ℝ) + 1) ^ d) := by
  exact killedGreenReal_le_box_of_mem' hd

-- y ∈ shell: y ∈ harnackBox (R+R/2) \ harnackBox (R+R/2-1) (unfold harnackShell,
-- Finset.mem_sdiff, mem_harnackBox_iff_mem_box), so some coordinate has R + R/2 - 1 < |y i| (not ∀,
-- box);
-- |x i| ≤ R, hence |y i - x i| ≥ R/2 ≥ 2 (abs_le, omega).  (y - x) i ≠ 0 gives y ≠ x;
-- |y i - x i|.natAbs ≤ graphNorm (y - x) (Finset.single_le_sum, unfold graphNorm), and
-- (R:ℝ)/4 ≤ R/2 (Nat.cast_div_le-type bound, R ≥ 4; or push_cast after omega on 4*(R/2) ≥ R).
/-- A shell point `y` is distinct from any `x ∈ box d R` and satisfies `graphNorm (y-x) ≥ R/4`. -/
private theorem ne_and_div_le_graphNorm_sub_of_mem_shell {R : ℕ} (hR : 4 ≤ R) {x y : Site d}
    (hx : x ∈ box d R)
    (hy : y ∈ harnackShell d R) : y ≠ x ∧ (R : ℝ) / 4 ≤ (graphNorm (y - x) : ℝ) := by
  rw [harnackShell] at hy
  obtain ⟨hybox, hynotmem⟩ := Finset.mem_sdiff.mp hy
  have hyboxed : y ∈ box d (R + R / 2) := (mem_harnackBox_iff_mem_box (R + R / 2) y).mp hybox
  have hne : ∃ i : Fin d, ((R + R / 2 - 1 : ℕ) : ℤ) < |y i|
  · obtain ⟨i, hi⟩ := not_forall.mp
      (fun hc => hynotmem ((mem_harnackBox_iff_mem_box (R + R / 2 - 1) y).mpr hc))
    exact ⟨i, not_le.mp hi⟩
  obtain ⟨i, _⟩ := hne
  have hxi : |x i| ≤ (R : ℤ) := hx i
  have hcast : ((R + R / 2 : ℕ) : ℤ) = ((R + R / 2 - 1 : ℕ) : ℤ) + 1
  · have h2 : R + R / 2 - 1 + 1 = R + R / 2
    · omega
    rw [← h2, Nat.cast_add]
    push_cast
    ring
  have hnatsub : ((R + R / 2 : ℕ) : ℤ) - (R : ℤ) = ((R / 2 : ℕ) : ℤ)
  · rw [Nat.cast_add]
    ring
  have hylow : ((R + R / 2 : ℕ) : ℤ) ≤ |y i|
  · rw [hcast]
    omega
  have hgeo : ((R / 2 : ℕ) : ℤ) ≤ |y i - x i|
  · have h1 : ((R / 2 : ℕ) : ℤ) ≤ |y i| - |x i|
    · linarith [hylow, hxi, hnatsub]
    have h2 : |y i| - |x i| ≤ |y i - x i|
    · have h := abs_add_le (y i - x i) (x i)
      have he : (y i - x i) + x i = y i
      · ring
      rw [he] at h
      linarith
    linarith
  have hnat : (R / 2 : ℕ) ≤ (y i - x i).natAbs
  · apply Int.ofNat_le.mp
    have hcast2 : (((y i - x i).natAbs : ℕ) : ℤ) = |y i - x i|
    · rw [← Int.natAbs_abs (y i - x i), Int.natAbs_of_nonneg (abs_nonneg (y i - x i))]
    rw [hcast2]
    exact hgeo
  have hgraph : (R / 2 : ℕ) ≤ graphNorm (y - x)
  · have h5 : (R / 2 : ℕ) ≤ ((y - x) i).natAbs
    · simpa only [Pi.sub_apply] using hnat
    rw [graphNorm]
    exact le_trans h5
        (Finset.single_le_sum (f := fun j => ((y - x) j).natAbs) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i))
  have h1R : ((R / 2 : ℕ) : ℝ) ≤ (graphNorm (y - x) : ℝ)
  · exact_mod_cast hgraph
  have h2R : (R : ℝ) / 4 ≤ ((R / 2 : ℕ) : ℝ)
  · have ha : R ≤ 2 * (R / 2) + 2
    · omega
    have hb : (2 : ℝ) ≤ ((R / 2 : ℕ) : ℝ)
    · have hbb : 2 ≤ R / 2
      · omega
      exact_mod_cast hbb
    have hc : (R : ℝ) ≤ 2 * ((R / 2 : ℕ) : ℝ) + 2
    · exact_mod_cast ha
    linarith
  refine ⟨?_, ?_⟩
  · intro hxy
    have hz : |y i - x i| = 0
    · rw [hxy]
      simp
    have h6 : ((R / 2 : ℕ) : ℤ) ≤ 0
    · rw [← hz]
      exact hgeo
    have h7 : (R / 2 : ℕ) ≤ 0
    · exact Int.ofNat_le.mp h6
    omega
  · linarith [h1R, h2R]


-- ((2R-1 : ℕ) : ℝ) + 1 = 2R (Nat.cast_sub, R ≥ 1); 1/r^d ≤ 4^d/R^d (one_div_le_one_div_of_le,
-- pow_le_pow_left₀, (R/4)^d = R^d/4^d); 1/(2R)^d ≤ 1/R^d; (2R)^2 = 4R^2; R^2/R^d = R^(2-d)
-- (zpow_sub₀, zpow_natCast).  SPLIT?
/-- Arithmetic bound converting the two-sided box estimate at radius `2R-1` and distance `≥ R/4`
into `C * 4 * (4^d+1) * R^{2-d}`. -/
private theorem mul_add_one_sq_mul_le_mul_rpow_two_sub (C : ℝ) (hC : 0 < C) {R : ℕ} (hR : 4 ≤ R)
    (r : ℝ) (hr : (R : ℝ) / 4 ≤ r) :
    C * (((2 * R - 1 : ℕ) : ℝ) + 1) ^ 2 * (1 / r ^ d + 1 / (((2 * R - 1 : ℕ) : ℝ) + 1) ^ d)
      ≤ C * 4 * (4 ^ d + 1) * (R : ℝ) ^ ((2 : ℤ) - d) := by
  have hRpos : (0:ℝ) < (R:ℝ) := (by
    have h4 : (4:ℝ) ≤ (R:ℝ) := (by exact_mod_cast hR)
    linarith)
  have hcast : ((2 * R - 1 : ℕ) : ℝ) + 1 = 2 * (R : ℝ) := (by
    have hle : 1 ≤ 2 * R := (by omega)
    rw [Nat.cast_sub hle]
    push_cast
    ring)
  have hz : (R:ℝ) ^ ((2:ℤ) - d) = (R:ℝ)^2 / (R:ℝ)^d := (by
    rw [zpow_sub₀ hRpos.ne' 2 (d:ℤ), zpow_ofNat, zpow_natCast])
  have hq : (0:ℝ) < (R:ℝ)/4 := (by linarith)
  have hvpos : (0:ℝ) < (2:ℝ) * (R:ℝ) := (by linarith)
  have hA1 : ((R:ℝ)/4) ^ d ≤ r ^ d := pow_le_pow_left₀ hq.le hr d
  have hA : (1:ℝ)/r^d ≤ (4:ℝ)^d/(R:ℝ)^d := (by
    have h := one_div_le_one_div_of_le (pow_pos hq d) hA1
    have h2 : (1:ℝ)/((R:ℝ)/4)^d = (4:ℝ)^d/(R:ℝ)^d := (by rw [div_pow, one_div_div])
    rwa [h2] at h)
  have hB1 : (R:ℝ)^d ≤ (2*(R:ℝ))^d := pow_le_pow_left₀ hRpos.le (by linarith) d
  have hB : (1:ℝ)/(2*(R:ℝ))^d ≤ (1:ℝ)/(R:ℝ)^d :=
    one_div_le_one_div_of_le (pow_pos hRpos d) hB1
  have hsum : (1:ℝ)/r^d + 1/(2*(R:ℝ))^d ≤ (4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d :=
    add_le_add hA hB
  have hmain : (2*(R:ℝ))^2 * ((4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d)
      = 4 * (4^d + 1) * ((R:ℝ)^2/(R:ℝ)^d) := (by
    rw [← add_div]
    field_simp
    ring)
  calc C * (((2*R-1:ℕ):ℝ) + 1)^2 * (1/r^d + 1/(((2*R-1:ℕ):ℝ)+1)^d)
      = C * (2*(R:ℝ))^2 * (1/r^d + 1/(2*(R:ℝ))^d) := (by rw [hcast])
    _ ≤ C * (2*(R:ℝ))^2 * ((4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hC.le (pow_nonneg hvpos.le 2))
    _ = C * ((2*(R:ℝ))^2 * ((4:ℝ)^d/(R:ℝ)^d + 1/(R:ℝ)^d)) := (by ring)
    _ = C * (4 * (4^d + 1) * ((R:ℝ)^2/(R:ℝ)^d)) := (by rw [hmain])
    _ = C * 4 * (4^d + 1) * (R:ℝ)^((2:ℤ) - d) := (by rw [hz]; ring)


-- C' := C * 4 * (4^d + 1) from killedGreenReal_le_box_of_mem.  harnackGreen B x y = killedGreenReal
-- B y x
-- (unfold harnackGreen); apply killedGreenReal_le_box_of_mem with L := 2R-1, B := harnackBox d
-- (2R-1)
-- (members in box via mem_harnackBox_iff_mem_box), the pair (y, x)
-- (ne_and_div_le_graphNorm_sub_of_mem_shell); then mul_add_one_sq_mul_le_mul_rpow_two_sub
-- with r := graphNorm (y - x), and ((2R-1:ℕ):ℝ) is the L of killedGreenReal_le_box_of_mem
-- (Nat.cast).
/-- The Green function upper bound on the shell: `harnackGreen (harnackBox (2R-1)) x y ≤ C
R^{2-d}` for `x ∈ box d R`, `y ∈ harnackShell d R`. -/
private theorem harnackGreen_le_mul_rpow_two_sub (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 4 ≤ R → ∀ x ∈ box d R, ∀ y ∈ harnackShell d R,
      harnackGreen (harnackBox d (2 * R - 1)) x y ≤ C * (R : ℝ) ^ ((2 : ℤ) - d) := by
  obtain ⟨C, hC, hup⟩ := killedGreenReal_le_box_of_mem hd
  refine ⟨C * 4 * (4 ^ d + 1), by positivity, fun R hR x hx y hy => ?_⟩
  obtain ⟨hyx, hr⟩ := ne_and_div_le_graphNorm_sub_of_mem_shell hR hx hy
  unfold harnackGreen
  refine le_trans (hup (2 * R - 1) (harnackBox d (2 * R - 1))
    (fun z hz => (mem_harnackBox_iff_mem_box _ z).1 hz) y x hyx) ?_
  exact mul_add_one_sq_mul_le_mul_rpow_two_sub C hC hR _ hr

-- This is `LatticeProb.GreenTwoSided.killedGreenReal_ge_box` (same shared top-level definitions
-- as `killedGreenReal_le_box_of_mem'`), which is itself still an open lemma in
-- scratch/decomp/green-two-sided/node.lean (line 1966); once that file's carving of it lands,
-- wire this file to it instead of reproving it here.  Route (there): lazy killed walk (binomial
-- mixture of `killedHeat`), free lazy near-diagonal lower bound from `iterate_delta0_eq` and the
-- 1D local CLT `exists_srwHeat_one_sub_gauss_le_int`, killing correction from the off-diagonal
-- bound, chaining over `O_K(1)` cubes of side `≍ ρ` at `s²` different times; small `ρ` by a
-- lattice path.
/-- Implementation lemma for `killedGreenReal_ge_box_of_mem`, obtained directly from
`LatticeProb.GreenTwoSided.killedGreenReal_ge_box`. -/
private theorem killedGreenReal_ge_box_of_mem' (hd : 1 ≤ d) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ρ : ℕ), 1 ≤ ρ → m ≤ K * ρ → ∀ B : Finset (Site d),
      (∀ z ∈ box d (m + ρ), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
        c * (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y :=
  LatticeProb.GreenTwoSided.killedGreenReal_ge_box hd K

/-- The two-sided Green function lower bound `LatticeProb.GreenTwoSided.killedGreenReal_ge_box`,
restated for use in the Harnack argument. -/
private theorem killedGreenReal_ge_box_of_mem (hd : 1 ≤ d) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ρ : ℕ), 1 ≤ ρ → m ≤ K * ρ → ∀ B : Finset (Site d),
      (∀ z ∈ box d (m + ρ), z ∈ B) → ∀ x ∈ box d m, ∀ y ∈ box d m,
        c * (ρ : ℝ) ^ ((2 : ℤ) - d) ≤ Graph.killedGreenReal (lattice d) (B : Set (Site d)) x y := by
  exact killedGreenReal_ge_box_of_mem' hd K

-- omega.
/-- Arithmetic facts about the gap `2R-1-(R+R/2)` between the two nested boxes, needed to apply
the Green-function lower bound at that scale. -/
private theorem harnackBox_gap_bounds {R : ℕ} (hR : 4 ≤ R) :
    1 ≤ 2 * R - 1 - (R + R / 2) ∧ R + R / 2 ≤ 6 * (2 * R - 1 - (R + R / 2)) ∧
      R + R / 2 + (2 * R - 1 - (R + R / 2)) = 2 * R - 1 ∧
      R ≤ 4 * (2 * R - 1 - (R + R / 2)) ∧ 2 * R - 1 - (R + R / 2) ≤ R := by
  omega

-- d = 1: zpow_one, R ≤ 4ρ.  d ≥ 2: exponent 2 - d ≤ 0 and ρ ≤ R give R^(2-d) ≤ ρ^(2-d)
-- (zpow_le_zpow_left₀ on inverses / one_div_le_one_div_of_le after zpow_neg), then R^(2-d)/4 ≤
-- R^(2-d).
/-- For `ρ ≤ R ≤ 4ρ`, `(1/4) R^{2-d} ≤ ρ^{2-d}`. -/
private theorem rpow_two_sub_div_four_le_rpow_two_sub {R ρ : ℕ} (hρ : 1 ≤ ρ) (hρR : ρ ≤ R)
    (hRρ : R ≤ 4 * ρ) (hd : 1 ≤ d) :
    (1 / 4 : ℝ) * (R : ℝ) ^ ((2 : ℤ) - d) ≤ (ρ : ℝ) ^ ((2 : ℤ) - d) := by
  have hρ1 : (1 : ℝ) ≤ (ρ : ℝ) := Nat.one_le_cast.mpr hρ
  have hρR' : (ρ : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr hρR
  have hR4 : (R : ℝ) ≤ 4 * (ρ : ℝ) := (Nat.cast_le.mpr hRρ).trans (le_of_eq (Nat.cast_mul 4 ρ))
  have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hρ1.trans hρR')
  have hρpos : (0 : ℝ) < (ρ : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hρ1
  rcases eq_or_lt_of_le hd with h1 | h1
  · subst h1
    norm_num
    linarith
  · have hd2 : 2 ≤ d := Nat.succ_le_of_lt h1
    have he : (2 : ℤ) - (d : ℤ) = -(((d - 2 : ℕ) : ℤ)) :=
      (neg_sub (d : ℤ) 2).symm.trans (congrArg Neg.neg (Nat.cast_sub hd2)).symm
    rw [he, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    have hk : (ρ : ℝ) ^ (d - 2) ≤ (R : ℝ) ^ (d - 2) := pow_le_pow_left₀ hρpos.le hρR' (d - 2)
    have hp : 0 < (ρ : ℝ) ^ (d - 2) := pow_pos hρpos (d - 2)
    have hq : 0 < (R : ℝ) ^ (d - 2) := pow_pos hRpos (d - 2)
    have hinv : ((R : ℝ) ^ (d - 2))⁻¹ ≤ ((ρ : ℝ) ^ (d - 2))⁻¹ := (inv_le_inv₀ hq hp).mpr hk
    have h4 : (1 / 4 : ℝ) * ((R : ℝ) ^ (d - 2))⁻¹ ≤ ((R : ℝ) ^ (d - 2))⁻¹ :=
      mul_le_of_le_one_left (inv_nonneg.mpr hq.le) (by norm_num)
    linarith


-- c' := c/4 from killedGreenReal_ge_box_of_mem with K := 6, m := R + R/2, ρ := 2R-1-(R+R/2)
-- (harnackBox_gap_bounds);
-- B := harnackBox d (2R-1) contains box (m + ρ) = box (2R-1) (mem_harnackBox_iff_mem_box);
-- x' ∈ box m by mem_box_of_le, y ∈ box m by harnackShell_subset_harnackBox_add_div_two +
-- mem_harnackBox_iff_mem_box;
-- harnackGreen B x' y = killedGreenReal B y x' (unfold); rpow_two_sub_div_four_le_rpow_two_sub,
-- mul_le_mul_of_nonneg_left.
/-- The Green function lower bound on the shell: `c R^{2-d} ≤ harnackGreen (harnackBox (2R-1)) x
y` for `x ∈ box d R`, `y ∈ harnackShell d R`. -/
private theorem mul_rpow_two_sub_le_harnackGreen (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℕ, 4 ≤ R → ∀ x ∈ box d R, ∀ y ∈ harnackShell d R,
      c * (R : ℝ) ^ ((2 : ℤ) - d) ≤ harnackGreen (harnackBox d (2 * R - 1)) x y := by
  obtain ⟨c, hc, hlow⟩ := killedGreenReal_ge_box_of_mem hd 6
  refine ⟨c / 4, by positivity, fun R hR x hx y hy => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := harnackBox_gap_bounds hR
  have hB : ∀ z ∈ box d (R + R / 2 + (2 * R - 1 - (R + R / 2))), z ∈ harnackBox d (2 * R - 1) := by
    intro z hz
    rw [h3] at hz
    exact (mem_harnackBox_iff_mem_box _ z).2 hz
  have hyK : y ∈ box d (R + R / 2) := (mem_harnackBox_iff_mem_box _ y).1
      (harnackShell_subset_harnackBox_add_div_two hy)
  have hxK : x ∈ box d (R + R / 2) := mem_box_of_le (by omega) hx
  have key := hlow (R + R / 2) (2 * R - 1 - (R + R / 2)) h1 h2 (harnackBox d (2 * R - 1)) hB
    y hyK x hxK
  have hconv := rpow_two_sub_div_four_le_rpow_two_sub h1 h5 h4 hd
  unfold harnackGreen
  calc c / 4 * (R : ℝ) ^ ((2 : ℤ) - d)
      = c * ((1 / 4 : ℝ) * (R : ℝ) ^ ((2 : ℤ) - d)) := by ring
    _ ≤ c * ((2 * R - 1 - (R + R / 2) : ℕ) : ℝ) ^ ((2 : ℤ) - d) :=
        mul_le_mul_of_nonneg_left hconv hc.le
    _ ≤ _ := key

-- C := C₁ / c₀ from harnackGreen_le_mul_rpow_two_sub / mul_rpow_two_sub_le_harnackGreen; R^(2-d) >
-- 0 by zpow_pos;
-- g(x,y) ≤ C₁ R^(2-d) = (C₁/c₀) (c₀ R^(2-d)) ≤ (C₁/c₀) g(x',y)  (div_mul_cancel₀,
-- mul_le_mul_of_nonneg_left).
/-- A Harnack comparison for the Green function itself: `harnackGreen (harnackBox (2R-1)) x y ≤ C
* harnackGreen (harnackBox (2R-1)) x' y` for `x, x' ∈ box d R`, `y` on the shell, combining
the upper and lower bounds. -/
private theorem harnackGreen_le_mul_harnackGreen (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 4 ≤ R → ∀ x ∈ box d R, ∀ x' ∈ box d R,
      ∀ y ∈ harnackShell d R,
        harnackGreen (harnackBox d (2 * R - 1)) x y
          ≤ C * harnackGreen (harnackBox d (2 * R - 1)) x' y := by
  obtain ⟨C1, hC1pos, hC1⟩ := harnackGreen_le_mul_rpow_two_sub hd
  obtain ⟨c0, hc0pos, hc0⟩ := mul_rpow_two_sub_le_harnackGreen hd
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0pos
  have hCpos : (0 : ℝ) < C1 / c0 := div_pos hC1pos hc0pos
  refine ⟨C1 / c0, hCpos, fun R hR x hx x' hx' y hy => ?_⟩
  have h1 : harnackGreen (harnackBox d (2 * R - 1)) x y ≤ C1 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)) :=
    hC1 R hR x hx y hy
  have h2 : c0 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)) ≤ harnackGreen (harnackBox d (2 * R - 1)) x' y :=
    hc0 R hR x' hx' y hy
  have hA : (C1 / c0) * (c0 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)))
      = C1 * (R : ℝ) ^ ((2 : ℤ) - (d : ℤ)) :=
    (mul_assoc _ _ _).symm.trans
      (congrArg (· * ((R : ℝ) ^ ((2 : ℤ) - (d : ℤ)))) (div_mul_cancel₀ C1 hc0ne))
  exact le_trans h1 (le_trans (le_of_eq hA.symm) (mul_le_mul_of_nonneg_left h2 (le_of_lt hCpos)))


-- exists_nonneg_eq_sum_shell_mul gives ν; u x = ∑ g(x,y)ν y ≤ ∑ C g(x',y) ν y = C u x'
-- (Finset.sum_le_sum, mul_le_mul_of_nonneg_right with ν ≥ 0, Finset.mul_sum, mul_assoc); C from
-- harnackGreen_le_mul_harnackGreen.
/-- The Harnack inequality for `R ≥ 4`: `u x ≤ C u y` for `x, y ∈ box d R`, from the Riesz
representation `exists_nonneg_eq_sum_shell_mul` and the Green-function comparison
`harnackGreen_le_mul_harnackGreen`. -/
private theorem le_mul_of_nonneg_harmonicOn (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (u : Site d → ℝ), 4 ≤ R →
      (∀ x ∈ box d (2 * R), 0 ≤ u x) →
      (∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) →
      ∀ x ∈ box d R, ∀ y ∈ box d R, u x ≤ C * u y := by
  obtain ⟨C, hCpos, hC⟩ := harnackGreen_le_mul_harnackGreen hd
  refine ⟨C, hCpos, ?_⟩
  intro R u hR hpos hharm x hx y hy
  obtain ⟨ν, hν, hu⟩ := exists_nonneg_eq_sum_shell_mul hd hR u hpos hharm
  rw [hu x hx, hu y hy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have h1 : harnackGreen (harnackBox d (2 * R - 1)) x z ≤
      C * harnackGreen (harnackBox d (2 * R - 1)) y z := hC R hR x hx y hy z hz
  have h2 : 0 ≤ ν z := hν z
  nlinarith [h1, h2]


/-! ### Small `R`: chaining the one-step bound -/

-- 2d u x = nbrSum u x = ∑_j (u(x+e_j) + u(x-e_j)); every term ≥ 0 (neighbours lie in box (2R-1+1)
-- = box (2R) by unit_add_sub_mem_box_succ, omega using 1 ≤ R); Finset.single_le_sum at j = i, then
-- le_add_of_nonneg_right / le_add_of_nonneg_left.
/-- Each unit-neighbour value `u (x ± unit i)` is at most `2d * u x`, since `2d * u x` is a sum
of nonnegative neighbour values including that term. -/
private theorem le_two_mul_mul_of_add_unit {R : ℕ} (hR : 1 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x)
    {x : Site d} (hx : x ∈ box d (2 * R - 1)) (i : Fin d) :
    u (x + unit i) ≤ 2 * (d : ℝ) * u x ∧ u (x - unit i) ≤ 2 * (d : ℝ) * u x := by
  have hR2 : 2 * R - 1 + 1 = 2 * R := Nat.sub_add_cancel (by omega)
  have key : u (x + unit i) + u (x - unit i) ≤ 2 * (d : ℝ) * u x := by
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i' : Fin d => u (x + unit i') + u (x - unit i'))
      (fun i' _ => by
        obtain ⟨h1, h2⟩ := unit_add_sub_mem_box_succ (2 * R - 1) x i' hx
        rw [hR2] at h1 h2
        exact add_nonneg (hpos _ h1) (hpos _ h2))
      (Finset.mem_univ i)
    have hle' : u (x + unit i) + u (x - unit i) ≤ nbrSum u x := by
      simpa [nbrSum] using hle
    simpa [hharm x hx] using hle'
  obtain ⟨h1, h2⟩ := unit_add_sub_mem_box_succ (2 * R - 1) x i hx
  rw [hR2] at h1 h2
  exact ⟨by linarith [key, hpos _ h2], by linarith [key, hpos _ h1]⟩


-- Finset.add_sum_erase at i on both sums; off i the summands agree (Finset.sum_congr,
-- Finset.ne_of_mem_erase); at i use hi; omega.
/-- If `x'` agrees with `x` off coordinate `i` and its `i`-th distance to `y` is one less, then
`∑_j |x'_j - y_j| + 1 = ∑_j |x_j - y_j|`. -/
private theorem sum_natAbs_succ_eq_of_ne {x' x y : Site d} (i : Fin d)
    (hoff : ∀ j, j ≠ i → x' j = x j)
    (hi : (x' i - y i).natAbs + 1 = (x i - y i).natAbs) :
    (∑ j, (x' j - y j).natAbs) + 1 = ∑ j, (x j - y j).natAbs := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h : ∑ j ∈ Finset.univ.erase i, (x' j - y j).natAbs
      = ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs :=
    Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)]
  rw [h]
  omega

-- Stepping coordinate i toward y i keeps x in box R: coordinates j ≠ i unchanged
-- (Pi.single_eq_of_ne), coordinate i moves strictly between x i and y i (abs_le, omega).
/-- Stepping coordinate `i` of `x` up toward `y` keeps the result in `box d R`, when `x_i < y_i`. -/
private theorem add_unit_mem_box_of_lt {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R)
    {i : Fin d}
    (h : x i < y i) : x + unit i ∈ box d R := by
  intro j
  rcases eq_or_ne j i with rfl | hji
  · have h1 := abs_le.mp (hx j)
    have h2 := abs_le.mp (hy j)
    simp only [Pi.add_apply, unit, Pi.single_eq_same]
    rw [abs_le]
    constructor <;> omega
  · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hji, add_zero]
    exact hx j

-- Same as add_unit_mem_box_of_lt with x - unit i.
/-- Stepping coordinate `i` of `x` down toward `y` keeps the result in `box d R`, when `y_i <
x_i`. -/
private theorem sub_unit_mem_box_of_lt {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R)
    {i : Fin d}
    (h : y i < x i) : x - unit i ∈ box d R := by
  intro j
  rcases eq_or_ne j i with rfl | hji
  · have h1 := abs_le.mp (hx j)
    have h2 := abs_le.mp (hy j)
    simp only [Pi.sub_apply, unit, Pi.single_eq_same]
    rw [abs_le]
    constructor <;> omega
  · simp only [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
    exact hx j

-- Pick i with x i ≠ y i (Function.funext_iff).  If y i < x i take x' := x - unit i (x = x' + unit
-- i),
-- else x' := x + unit i (x = x' - unit i).  x' ∈ box R coordinatewise (unit, Pi.single_apply,
-- abs_le,
-- omega).  Distance: Finset.add_sum_erase at i on both sums; off i the summands agree
-- (Pi.single_eq_of_ne), at i natAbs drops by one (omega).  SPLIT?
/-- For `x ≠ y` in `box d R`, there is a neighbour `x'` of `x` in `box d R`, reached by a single
step toward `y`, whose `L¹` distance to `y` is one less than that of `x`. -/
private theorem exists_step_sum_natAbs_add_one_eq {R : ℕ} {x y : Site d} (hx : x ∈ box d R)
    (hy : y ∈ box d R)
    (hxy : x ≠ y) :
    ∃ x' ∈ box d R, ∃ i : Fin d, (x = x' + unit i ∨ x = x' - unit i) ∧
      (∑ j, (x' j - y j).natAbs) + 1 = ∑ j, (x j - y j).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    exact hxy (funext fun j => by by_contra hj; exact h ⟨j, hj⟩)
  rcases lt_or_gt_of_ne hi with h | h
  · refine ⟨x + unit i, add_unit_mem_box_of_lt hx hy h, i,
      Or.inr (add_sub_cancel_right x (unit i)).symm, sum_natAbs_succ_eq_of_ne i ?_ ?_⟩
    · intro j hji
      simp [unit, Pi.single_eq_of_ne hji]
    · simp only [Pi.add_apply, unit, Pi.single_eq_same]
      omega
  · refine ⟨x - unit i, sub_unit_mem_box_of_lt hx hy h, i,
      Or.inl (sub_add_cancel x (unit i)).symm, sum_natAbs_succ_eq_of_ne i ?_ ?_⟩
    · intro j hji
      simp [unit, Pi.single_eq_of_ne hji]
    · simp only [Pi.sub_apply, unit, Pi.single_eq_same]
      omega

-- Induction on n generalizing x.  n = 0: all natAbs are 0 (Finset.sum_eq_zero_iff), so x = y
-- (funext, Int.natAbs_eq_zero, sub_eq_zero); pow_zero, one_mul.  n + 1: x ≠ y (else sum 0);
-- exists_step_sum_natAbs_add_one_eq gives x'; u x ≤ 2d u x' by le_two_mul_mul_of_add_unit at x' (x'
-- ∈ box (2R-1) via
-- mem_box_of_le, omega); IH at x'; pow_succ, mul_le_mul_of_nonneg_left (0 ≤ 2d).
/-- If the `L¹` distance from `x` to `y` is `n+1`, then `x ≠ y`. -/
private theorem ne_of_sum_natAbs_eq_succ {d : ℕ} {n : ℕ} {x y : Site d}
    (h : ∑ j, (x j - y j).natAbs = n + 1) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  simp at h

/-- `a * (a^n * t) = a^{n+1} * t`. -/
private theorem mul_pow_mul_eq_pow_succ_mul (a t : ℝ) (n : ℕ) : a * (a ^ n * t) = a ^ (n + 1) * t :=
    by
  rw [pow_succ]; ring

/-- The neighbour chain bound: `u x ≤ (2d)^n * u y` whenever `x, y ∈ box d R` are at `L¹`
distance `n`, by induction along `exists_step_sum_natAbs_add_one_eq`. -/
private theorem le_two_mul_pow_mul_of_sum_natAbs_eq {R : ℕ} (hR : 1 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) :
    ∀ (n : ℕ) (x y : Site d), x ∈ box d R → y ∈ box d R →
      ∑ j, (x j - y j).natAbs = n → u x ≤ (2 * (d : ℝ)) ^ n * u y := by
  intro n x y hx hy hsum
  revert x y
  induction n with
  | zero =>
    intro x y hx hy hsum
    have hxy : x = y := funext fun j => by
      have hle : (x j - y j).natAbs ≤ ∑ i : Fin d, (x i - y i).natAbs :=
        Finset.single_le_sum (f := fun i : Fin d => (x i - y i).natAbs)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [hsum] at hle
      have h0 : (x j - y j).natAbs = 0 := Nat.le_zero.mp hle
      exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp h0)
    rw [hxy, pow_zero, one_mul]
  | succ n ih =>
    intro x y hx hy hsum
    have hne : x ≠ y := ne_of_sum_natAbs_eq_succ hsum
    obtain ⟨x', hx', i, hstep, hsum'⟩ := exists_step_sum_natAbs_add_one_eq hx hy hne
    have hx'B : x' ∈ box d (2 * R - 1) := mem_box_of_le (by omega) hx'
    have hih : u x' ≤ (2 * (d : ℝ)) ^ n * u y := ih x' y hx' hy (by omega)
    rcases hstep with h | h
    · rw [h]
      calc u (x' + unit i) ≤ 2 * (d : ℝ) * u x' :=
          (le_two_mul_mul_of_add_unit hR u hpos hharm hx'B i).1
        _ ≤ 2 * (d : ℝ) * ((2 * (d : ℝ)) ^ n * u y) := mul_le_mul_of_nonneg_left hih (by positivity)
        _ = (2 * (d : ℝ)) ^ (n + 1) * u y := mul_pow_mul_eq_pow_succ_mul (2 * (d : ℝ)) (u y) n
    · rw [h]
      calc u (x' - unit i) ≤ 2 * (d : ℝ) * u x' :=
          (le_two_mul_mul_of_add_unit hR u hpos hharm hx'B i).2
        _ ≤ 2 * (d : ℝ) * ((2 * (d : ℝ)) ^ n * u y) := mul_le_mul_of_nonneg_left hih (by positivity)
        _ = (2 * (d : ℝ)) ^ (n + 1) * u y := mul_pow_mul_eq_pow_succ_mul (2 * (d : ℝ)) (u y) n


-- Finset.sum_le_card_nsmul with bound 2R per coordinate (|x j - y j| ≤ |x j| + |y j| ≤ 2R:
-- abs_le, omega on natAbs via Int.natAbs_le / Int.ofNat_le); Finset.card_univ, Fintype.card_fin,
-- smul_eq_mul; nlinarith/ring_nf for d * (2R) = 2 * R * d.
/-- The `L¹` distance between two points of `box d R` is at most `2Rd`. -/
private theorem sum_natAbs_le_two_mul_mul {R : ℕ} {x y : Site d} (hx : x ∈ box d R)
    (hy : y ∈ box d R) :
    ∑ j, (x j - y j).natAbs ≤ 2 * R * d := by
  have hx' : ∀ j : Fin d, (x j).natAbs ≤ R := fun j =>
    Int.ofNat_le.mp (Int.abs_eq_natAbs (x j) ▸ hx j)
  have hy' : ∀ j : Fin d, (y j).natAbs ≤ R := fun j =>
    Int.ofNat_le.mp (Int.abs_eq_natAbs (y j) ▸ hy j)
  have hterm : ∀ j : Fin d, (x j - y j).natAbs ≤ 2 * R := fun j =>
    le_trans (Int.natAbs_sub_le (x j) (y j))
      (le_trans (Nat.add_le_add (hx' j) (hy' j)) (le_of_eq (Nat.two_mul R).symm))
  have hsum : ∑ j : Fin d, (x j - y j).natAbs ≤ ∑ j : Fin d, (2 * R) :=
    Finset.sum_le_sum (fun j _ => hterm j)
  have hconst : ∑ j : Fin d, (2 * R) = 2 * R * d := (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact Nat.mul_comm d (2 * R))
  omega


-- le_two_mul_pow_mul_of_sum_natAbs_eq with n := ∑ natAbs, then pow_le_pow_right₀ (1 ≤ 2d since 1 ≤
-- d) with sum_natAbs_le_two_mul_mul
-- and mul_le_mul_of_nonneg_right (0 ≤ u y by hpos, mem_box_of_le R ≤ 2R).
/-- The small-`R` Harnack bound `u x ≤ (2d)^{2Rd} * u y` for `x, y ∈ box d R`, combining the
neighbour chain bound with the `L¹` diameter of the box. -/
private theorem le_two_mul_pow_mul_of_mem_box (hd : 1 ≤ d) {R : ℕ} (hR : 1 ≤ R) (u : Site d → ℝ)
    (hpos : ∀ x ∈ box d (2 * R), 0 ≤ u x)
    (hharm : ∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x)
    {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R) :
    u x ≤ (2 * (d : ℝ)) ^ (2 * R * d) * u y := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := (by exact_mod_cast hd)
  have h1d : (1 : ℝ) ≤ 2 * (d : ℝ) := (by linarith)
  have h34 : ∑ j, (x j - y j).natAbs ≤ 2 * R * d := sum_natAbs_le_two_mul_mul hx hy
  have h33 : u x ≤ (2 * (d : ℝ)) ^ (∑ j, (x j - y j).natAbs) * u y :=
      le_two_mul_pow_mul_of_sum_natAbs_eq hR u hpos hharm (∑ j, (x j - y j).natAbs) x y hx hy rfl
  have hpow : (2 * (d : ℝ)) ^ (∑ j, (x j - y j).natAbs) ≤ (2 * (d : ℝ)) ^ (2 * R * d) :=
      pow_le_pow_right₀ h1d h34
  have hybox : y ∈ box d (2 * R) := mem_box_of_le (by omega) hy
  exact le_trans h33 (mul_le_mul_of_nonneg_right hpow (hpos y hybox))


/-! ### The Harnack inequality -/

/-- The Harnack inequality: for `d ≥ 1` there is `C > 0` such that every `u` nonnegative on `box
d (2R)` and harmonic on `box d (2R-1)` satisfies `u x ≤ C * u y` for all `x, y ∈ box d R`,
uniformly in `R ≥ 1`. -/
theorem harnack (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (u : Site d → ℝ), 1 ≤ R →
      (∀ x ∈ box d (2 * R), 0 ≤ u x) →
      (∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) →
      ∀ x ∈ box d R, ∀ y ∈ box d R, u x ≤ C * u y := by
  obtain ⟨C₂, hC₂, hbig⟩ := le_mul_of_nonneg_harmonicOn hd
  have h2d : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨(2 * (d : ℝ)) ^ (8 * d) + C₂, by positivity, ?_⟩
  intro R u hR hpos hharm x hx y hy
  have huy : 0 ≤ u y := hpos y (mem_box_of_le (by omega) hy)
  have hpow0 : 0 ≤ (2 * (d : ℝ)) ^ (8 * d) := by positivity
  by_cases hR4 : 4 ≤ R
  · have h := hbig R u hR4 hpos hharm x hx y hy
    nlinarith
  · have h := le_two_mul_pow_mul_of_mem_box hd hR u hpos hharm hx hy
    have hle : (2 * (d : ℝ)) ^ (2 * R * d) ≤ (2 * (d : ℝ)) ^ (8 * d) :=
      pow_le_pow_right₀ h2d (by nlinarith)
    nlinarith

end LatticeProb

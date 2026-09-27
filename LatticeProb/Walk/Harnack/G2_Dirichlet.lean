import LatticeProb.Site
import LatticeProb.Network.KilledGreen
import LatticeProb.Graph.Zd
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Walk.SRW
import LatticeProb.Walk.GreenTwoSided
import LatticeProb.Walk.Harnack.G1_Basics

/-!
# The minimum principle and the Dirichlet extension

The discrete minimum principle: a function harmonic on a finite set `A` and nonnegative
(respectively zero) off `A` is nonnegative (respectively zero) everywhere. The Dirichlet extension
`harnackExt B K u` of data `u` on `K` is harmonic on `B \ K`, agrees with `u` on `K`, vanishes off
`B`, and satisfies the comparison principle `harnackExt B K u ≤ u` when `u` is harmonic and
nonnegative.
-/

open Finset
open scoped Classical

namespace LatticeProb

variable {d : ℕ}

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
theorem eq_sum_harnackGreen_mul_laplacian (hd : 1 ≤ d) (B : Finset (Site d))
    (w : Site d → ℝ)
    (hw : ∀ x, x ∉ B → w x = 0) (x : Site d) :
    w x = ∑ y ∈ B, harnackGreen B x y * (2 * (d : ℝ) * w y - nbrSum w y) := by
  exact eq_sum_harnackGreen_mul_laplacian' hd B w hw x


/-! ### The Dirichlet problem on `B \ K` -/

-- unfold harnackExt; if_pos hx; each summand has harnackGreen (B \ K) x y = 0 by
-- harnackGreen_eq_zero_of_not_mem
-- (x ∉ B \ K since x ∈ K: Finset.mem_sdiff); Finset.sum_eq_zero; add_zero.
/-- `harnackExt B K u x = u x` for `x ∈ K`: the extension agrees with `u` on `K`. -/
theorem harnackExt_eq_of_mem (hd : 1 ≤ d) (B K : Finset (Site d)) (u : Site d → ℝ)
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
theorem harnackExt_eq_zero_of_not_mem (hd : 1 ≤ d) (B K : Finset (Site d)) (hK : K ⊆ B)
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
theorem nbrSum_harnackExt_eq_of_mem_sdiff (hd : 1 ≤ d) (B K : Finset (Site d))
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
theorem zero_le_two_mul_harnackExt_sub_nbrSum (hd : 1 ≤ d) (B K : Finset (Site d))
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
theorem two_mul_harnackExt_sub_nbrSum_eq_zero (hd : 1 ≤ d) (B K : Finset (Site d))
    (u : Site d → ℝ) {y : Site d}
    (hy : y ∈ K) (hnbK : ∀ i : Fin d, y + unit i ∈ K ∧ y - unit i ∈ K)
    (hharm : nbrSum u y = 2 * (d : ℝ) * u y) :
    2 * (d : ℝ) * harnackExt B K u y - nbrSum (harnackExt B K u) y = 0 := by
  have h1 : harnackExt B K u y = u y := harnackExt_eq_of_mem hd B K u hy; have h2 : nbrSum
      (harnackExt B K u) y = nbrSum u y := nbrSum_congr
          (fun i => ⟨harnackExt_eq_of_mem hd B K u (hnbK i).1, harnackExt_eq_of_mem hd B K u (hnbK
              i).2⟩); rw [h1, h2, hharm]; ring

end LatticeProb

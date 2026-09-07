/-
The exterior Dirichlet problem on `ℤ^d ∖ {0}` in dimension three and above.

A bounded function harmonic off the origin, vanishing at the origin and tending
to one at infinity is `1 - G(x,0)/G(0,0)` and nothing else.  The proof is the
maximum principle on a large box: the difference of two solutions is harmonic
off the origin, vanishes there, and is uniformly small outside a box, so the
maximum principle bounds it by that small number everywhere.

The one analytic input is that the Green function tends to zero at infinity,
which follows from the on-diagonal sup bound `p_j(x) ≤ C j^{-d/2}` and the fact
that the walk cannot reach `x` before time `|x|_1`: the Green function at `x` is
a tail of the convergent series `∑_j j^{-d/2}`.
-/
import LatticeProb.Walk.HitProb
import LatticeProb.Walk.SRWSup
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Graph.Zd
import LatticeProb.ParticleHoleLemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter Topology

namespace LatticeProb

variable {d : ℕ}

/-! ### The lattice Laplacian in network vocabulary -/

theorem netLaplacian_lattice (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f x
      = 2 * (d : ℝ) * (walkOp f x - f x) := by
  have hdne : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hw := Graph.Zd.walkOp_eq f x
  rw [Graph.walkOp, Graph.Zd.degree_eq] at hw
  have hsum : (∑ y ∈ (lattice d).neighborFinset x, f y)
      = 2 * (d : ℝ) * walkOp f x := by
    rw [← hw]
    push_cast
    field_simp
  rw [Network.netLaplacian_unitCond, Graph.laplacian,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    SimpleGraph.card_neighborFinset_eq_degree, Graph.Zd.degree_eq, hsum]
  push_cast
  ring

theorem netLaplacian_lattice_eq_zero (hd : 1 ≤ d) {f : Site d → ℝ} {x : Site d}
    (h : walkOp f x = f x) :
    Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f x = 0 := by
  rw [netLaplacian_lattice hd, h, sub_self, mul_zero]

/-! ### The maximum principle on the lattice -/

/-- **The maximum principle.**  A function harmonic on a finite set `C` away
from `S`, and at most `M` off `C` and on `S`, is at most `M` everywhere. -/
theorem le_of_harmonic_on_box (hd : 1 ≤ d) [NeZero d] (C : Finset (Site d)) (S : Set (Site d))
    (f : Site d → ℝ) (M : ℝ) {q : Site d} (hq : q ∉ C)
    (hharm : ∀ x ∈ C, x ∉ S → walkOp f x = f x)
    (hout : ∀ x, x ∉ C → f x ≤ M) (hS : ∀ x ∈ S, f x ≤ M) :
    ∀ x, f x ≤ M :=
  Network.le_of_harmonicOn (Graph.Zd.latticeConnected d) Network.isCond_unitCond C S f M hq
    (fun x hx hxS => netLaplacian_lattice_eq_zero hd (hharm x hx hxS)) hout hS

/-! ### Elementary algebra of the walk operator -/

theorem walkOp_const (hd : 1 ≤ d) (c : ℝ) (x : Site d) :
    walkOp (fun _ : Site d => c) x = c := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  rw [walkOp, nbrSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem walkOp_sub (u v : Site d → ℝ) (x : Site d) :
    walkOp (fun y => u y - v y) x = walkOp u x - walkOp v x := by
  simp only [walkOp, nbrSum, ← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem walkOp_div_const (u : Site d → ℝ) (c : ℝ) (x : Site d) :
    walkOp (fun y => u y / c) x = walkOp u x / c := by
  simp only [div_eq_mul_inv]
  exact walkOp_mul_const u c⁻¹ x

theorem walkOp_neg (u : Site d → ℝ) (x : Site d) :
    walkOp (fun y => -u y) x = -walkOp u x := by
  have h := walkOp_mul_const u (-1 : ℝ) x
  simpa using h

/-! ### The walk operator and an infinite sum -/

theorem walkOp_tsum {F : ℕ → Site d → ℝ}
    (hsum : ∀ y : Site d, Summable fun j => F j y) (x : Site d) :
    walkOp (fun y => ∑' j : ℕ, F j y) x = ∑' j : ℕ, walkOp (F j) x := by
  have hpair : ∀ i : Fin d,
      Summable fun j => F j (x + unit i) + F j (x - unit i) :=
    fun i => (hsum (x + unit i)).add (hsum (x - unit i))
  have hstep : ∀ i : Fin d,
      (∑' j : ℕ, F j (x + unit i)) + ∑' j : ℕ, F j (x - unit i)
        = ∑' j : ℕ, (F j (x + unit i) + F j (x - unit i)) :=
    fun i => (Summable.tsum_add (hsum (x + unit i)) (hsum (x - unit i))).symm
  rw [walkOp, nbrSum, Finset.sum_congr rfl fun i _ => hstep i,
    (Summable.tsum_finsetSum (fun i _ => hpair i)).symm, ← tsum_div_const]
  exact tsum_congr fun j => rfl

/-! ### The Green function is harmonic off the origin and vanishes at infinity -/

theorem walkOp_srwGreenInf (hd : 3 ≤ d) (x : Site d) :
    walkOp (srwGreenInf d) x = srwGreenInf d x - (if x = 0 then 1 else 0) := by
  have hfun : srwGreenInf d = fun y => ∑' j : ℕ, srwHeat d j y := rfl
  have h1 : walkOp (srwGreenInf d) x = ∑' j : ℕ, srwHeat d (j + 1) x := by
    rw [hfun, walkOp_tsum (fun y => summable_srwHeat hd y) x]
    exact tsum_congr fun j => (srwHeat_succ j x).symm
  have hshift := ((summable_nat_add_iff 1).mpr
    (summable_srwHeat hd x)).sum_add_tsum_nat_add' (f := fun j => srwHeat d j x)
  rw [Finset.sum_range_one, srwHeat_zero] at hshift
  rw [h1, srwGreenInf]
  linarith

/-- The Green function is harmonic away from the origin. -/
theorem walkOp_srwGreenInf_of_ne (hd : 3 ≤ d) {x : Site d} (hx : x ≠ 0) :
    walkOp (srwGreenInf d) x = srwGreenInf d x := by
  rw [walkOp_srwGreenInf hd x, if_neg hx, sub_zero]

theorem srwGreenInf_nonneg (x : Site d) : 0 ≤ srwGreenInf d x :=
  tsum_nonneg fun j => srwHeat_nonneg j x

/-- The tail of a convergent series tends to zero. -/
theorem tendsto_tsum_nat_add_zero {a : ℕ → ℝ} (hsa : Summable a) :
    Tendsto (fun n : ℕ => ∑' i : ℕ, a (i + n)) atTop (nhds 0) := by
  have hsplit : ∀ n : ℕ, ∑' i : ℕ, a (i + n) = (∑' j : ℕ, a j) - ∑ i ∈ Finset.range n, a i := by
    intro n
    have := ((summable_nat_add_iff n).mpr hsa).sum_add_tsum_nat_add' (f := a)
    linarith
  simp only [hsplit]
  have h : Tendsto (fun n : ℕ => (∑' j : ℕ, a j) - ∑ i ∈ Finset.range n, a i)
      atTop (nhds ((∑' j : ℕ, a j) - ∑' j : ℕ, a j)) :=
    Filter.Tendsto.const_sub _ hsa.hasSum.tendsto_sum_nat
  simpa using h

/-- The Green function is its own tail past any horizon. -/
theorem srwGreen_add_tsum_shift (hd : 3 ≤ d) (x : Site d) (n : ℕ) :
    (∑ j ∈ Finset.range n, srwHeat d j x) + ∑' i : ℕ, srwHeat d (i + n) x
      = srwGreenInf d x :=
  ((summable_nat_add_iff n).mpr (summable_srwHeat hd x)).sum_add_tsum_nat_add'

/-- A termwise comparison of the two tails. -/
theorem tsum_shift_srwHeat_le (hd : 3 ≤ d) {a : ℕ → ℝ} (hsa : Summable a) (x : Site d) (n : ℕ)
    (hterm : ∀ i : ℕ, srwHeat d (i + n) x ≤ a (i + n)) :
    ∑' i : ℕ, srwHeat d (i + n) x ≤ ∑' i : ℕ, a (i + n) :=
  ((summable_nat_add_iff n).mpr (summable_srwHeat hd x)).tsum_le_tsum hterm
    ((summable_nat_add_iff n).mpr hsa)

/-- **The Green function vanishes at infinity.**  The walk cannot reach `x`
before time `|x|_1`, and after that time the on-diagonal sup bound makes the
Green function a tail of the convergent series `∑_j j^{-d/2}`. -/
theorem tendsto_srwGreenInf_zero (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ x : Site d, R ≤ graphNorm x → srwGreenInf d x ≤ ε := by
  set K : ℝ := Real.sqrt 2 ^ d * greenConst d with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (by positivity) (greenConst_nonneg d)
  set a : ℕ → ℝ := fun j => K * (((j : ℝ)) ^ ((d : ℝ) / 2))⁻¹ with ha
  have hp : (1 : ℝ) < (d : ℝ) / 2 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hsa : Summable a := (Real.summable_nat_rpow_inv.mpr hp).mul_left K
  have hann : ∀ j : ℕ, 0 ≤ a j := fun j => by
    rw [ha]
    exact mul_nonneg hKnn (by positivity)
  have hbnd : ∀ (j : ℕ) (x : Site d), 1 ≤ j → srwHeat d j x ≤ a j := by
    intro j x hj
    have h := srwHeat_sup_bound (d := d) (by omega) hj x
    rw [ha]
    refine le_trans h (le_of_eq ?_)
    rw [hK]
    congr 1
    rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring,
      Real.rpow_neg (Nat.cast_nonneg j)]
  have htail := tendsto_tsum_nat_add_zero hsa
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.Tendsto.eventually_lt_const hε htail)
  refine ⟨max N 1, le_max_right _ _, fun x hx => ?_⟩
  have hxN : N ≤ graphNorm x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ graphNorm x := le_trans (le_max_right _ _) hx
  have hzero : ∀ j ∈ Finset.range (graphNorm x), srwHeat d j x = 0 := fun j hj =>
    srwHeat_eq_zero_of_lt (Finset.mem_range.mp hj)
  have hsplit := srwGreen_add_tsum_shift hd x (graphNorm x)
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add] at hsplit
  have hterm : ∀ i : ℕ, srwHeat d (i + graphNorm x) x ≤ a (i + graphNorm x) := fun i =>
    hbnd (i + graphNorm x) x (le_trans hx1 (Nat.le_add_left _ _))
  have hle := tsum_shift_srwHeat_le hd hsa x (graphNorm x) hterm
  have hlt := hN (graphNorm x) hxN
  rw [← hsplit]
  linarith

/-! ### The return probability -/

theorem srwHitProb_le_one (hd : 0 < d) (x : Site d) : srwHitProb d x ≤ 1 := by
  have hs := (summable_srwFirstHit hd x).hasSum.tendsto_sum_nat
  refine le_of_tendsto hs (Filter.Eventually.of_forall fun n => ?_)
  cases n with
  | zero => simp
  | succ m => exact srwHitBy_le_one hd m x

theorem srwHitProb_origin : srwHitProb d (0 : Site d) = 1 := by
  have hzero : ∀ k : ℕ, srwFirstHit d k (0 : Site d) = if k = 0 then 1 else 0 := by
    intro k
    cases k with
    | zero => rw [srwFirstHit_zero, if_pos rfl, if_pos rfl]
    | succ m => rw [srwFirstHit_succ_origin, if_neg (by omega)]
  rw [srwHitProb, tsum_congr hzero, tsum_ite_eq]

/-- **The return probability of the origin.**  The average of the hitting
probability over the neighbours of the origin is `1 - 1/G(0,0)`; that is the
chance that the walk started at the origin ever comes back. -/
theorem walkOp_srwHitProb_origin (hd : 3 ≤ d) :
    walkOp (srwHitProb d) (0 : Site d) = 1 - 1 / srwGreenInf d 0 := by
  have hG0pos : (0 : ℝ) < srwGreenInf d 0 :=
    lt_of_lt_of_le zero_lt_one (one_le_srwGreenInf_origin hd)
  have hfun : srwHitProb d = fun z => srwGreenInf d z / srwGreenInf d 0 :=
    funext fun z => srwHitProb_eq_green_ratio hd z
  rw [hfun, walkOp_div_const, walkOp_srwGreenInf hd, if_pos rfl]
  field_simp

/-- `sup_{z ≠ 0} G(0,z)/G(0,0)`, the supremum of the hitting probability away
from the origin. -/
noncomputable def greenRatioSup (d : ℕ) : ℝ := ⨆ z : {z : Site d // z ≠ 0}, srwHitProb d (z : Site d)

theorem bddAbove_srwHitProb (hd : 0 < d) :
    BddAbove (Set.range fun z : {z : Site d // z ≠ 0} => srwHitProb d (z : Site d)) :=
  ⟨1, by rintro _ ⟨z, rfl⟩; exact srwHitProb_le_one hd _⟩

theorem nonempty_nonzero_site (hd : 0 < d) : Nonempty {z : Site d // z ≠ 0} :=
  ⟨⟨unit ⟨0, hd⟩, unit_ne_zero _⟩⟩

theorem greenRatioSup_le_one (hd : 0 < d) : greenRatioSup d ≤ 1 := by
  haveI := nonempty_nonzero_site hd
  exact ciSup_le fun z => srwHitProb_le_one hd _

theorem le_greenRatioSup (hd : 0 < d) {z : Site d} (hz : z ≠ 0) :
    srwHitProb d z ≤ greenRatioSup d :=
  le_ciSup (f := fun z : {z : Site d // z ≠ 0} => srwHitProb d (z : Site d))
    (bddAbove_srwHitProb hd) ⟨z, hz⟩

/-- **The return probability is at most the supremum of the hitting probability
away from the origin**: it is the average of that hitting probability over the
`2d` neighbours, each of which is a nonzero site.  Equality is the statement
that the supremum is attained at the neighbours. -/
theorem one_sub_inv_le_greenRatioSup (hd : 3 ≤ d) :
    1 - 1 / srwGreenInf d 0 ≤ greenRatioSup (d := d) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    linarith
  have hbnd : ∀ i : Fin d,
      srwHitProb d (unit i) + srwHitProb d (-unit i)
        ≤ greenRatioSup (d := d) + greenRatioSup (d := d) :=
    fun i => add_le_add (le_greenRatioSup hd0 (unit_ne_zero i))
      (le_greenRatioSup hd0 (by simpa using unit_ne_zero i))
  have hsum : ∑ i : Fin d, (srwHitProb d ((0 : Site d) + unit i)
        + srwHitProb d ((0 : Site d) - unit i))
      ≤ ∑ _i : Fin d, (greenRatioSup (d := d) + greenRatioSup (d := d)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (0 : Site d) + unit i = unit i := by rw [zero_add]
    have h2 : (0 : Site d) - unit i = -unit i := by rw [zero_sub]
    rw [h1, h2]
    exact hbnd i
  rw [← walkOp_srwHitProb_origin hd, walkOp, nbrSum]
  rw [div_le_iff₀ hdR]
  refine le_trans hsum ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  rfl

/-! ### Uniqueness for the exterior Dirichlet problem -/

theorem le_graphNorm_of_notMem_boxFinset {R : ℕ} {x : Site d}
    (hx : x ∉ boxFinset (0 : Site d) R) : R ≤ graphNorm x := by
  classical
  rw [mem_boxFinset_iff] at hx
  simp only [not_forall, not_le] at hx
  obtain ⟨i, hi⟩ := hx
  have hi' : (R : ℤ) < |x i| := by simpa using hi
  have hnat : R < (x i).natAbs := by
    have : ((R : ℤ)) < ((x i).natAbs : ℤ) := by rwa [Int.abs_eq_natAbs] at hi'
    exact_mod_cast this
  have hle : (x i).natAbs ≤ graphNorm x :=
    Finset.single_le_sum (f := fun j => (x j).natAbs) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  omega

/-- **Uniqueness for the exterior Dirichlet problem on `ℤ^d ∖ {0}`.**  A
function harmonic off the origin, vanishing at the origin and tending to one at
infinity is `1 - G(x,0)/G(0,0)`.  No boundedness hypothesis is needed: the
convergence at infinity is what the maximum principle on a large box uses. -/
theorem exterior_dirichlet_unique (hd : 3 ≤ d) [NeZero d] {f : Site d → ℝ}
    (hharm : ∀ x : Site d, x ≠ 0 → walkOp f x = f x)
    (hzero : f 0 = 0)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ x : Site d, R ≤ graphNorm x → |f x - 1| ≤ ε) :
    ∀ x : Site d, f x = 1 - srwGreenInf d x / srwGreenInf d 0 := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hG0pos : (0 : ℝ) < srwGreenInf d 0 :=
    lt_of_lt_of_le zero_lt_one (one_le_srwGreenInf_origin hd)
  have hG0ne : srwGreenInf d (0 : Site d) ≠ 0 := ne_of_gt hG0pos
  -- the candidate solution
  have hg0 : (1 : ℝ) - srwGreenInf d (0 : Site d) / srwGreenInf d 0 = 0 := by
    rw [div_self hG0ne, sub_self]
  have hgharm : ∀ x : Site d, x ≠ 0 →
      walkOp (fun y => 1 - srwGreenInf d y / srwGreenInf d 0) x
        = 1 - srwGreenInf d x / srwGreenInf d 0 := by
    intro x hx
    rw [walkOp_sub (fun _ => (1 : ℝ)) (fun y => srwGreenInf d y / srwGreenInf d 0) x,
      walkOp_const hd1, walkOp_div_const, walkOp_srwGreenInf_of_ne hd hx]
  -- the difference is smaller than every positive number
  have key : ∀ ε : ℝ, 0 < ε → ∀ y : Site d,
      |f y - (1 - srwGreenInf d y / srwGreenInf d 0)| ≤ ε := by
    intro ε hε y
    obtain ⟨R₁, hR₁⟩ := hlim (ε / 2) (by linarith)
    obtain ⟨R₂, -, hR₂⟩ := tendsto_srwGreenInf_zero (d := d) hd
      (show (0 : ℝ) < ε / 2 * srwGreenInf d 0 by positivity)
    set h : Site d → ℝ := fun z => f z - (1 - srwGreenInf d z / srwGreenInf d 0) with hh
    have hharm' : ∀ z : Site d, z ≠ 0 → walkOp h z = h z := by
      intro z hz
      rw [hh, walkOp_sub f (fun y => 1 - srwGreenInf d y / srwGreenInf d 0) z,
        hharm z hz, hgharm z hz]
    have hout : ∀ z : Site d, z ∉ boxFinset (0 : Site d) (max R₁ R₂) → |h z| ≤ ε := by
      intro z hz
      have hn := le_graphNorm_of_notMem_boxFinset hz
      have h1 : |f z - 1| ≤ ε / 2 := hR₁ z (le_trans (le_max_left _ _) hn)
      have h2 : srwGreenInf d z ≤ ε / 2 * srwGreenInf d 0 :=
        hR₂ z (le_trans (le_max_right _ _) hn)
      have h3 : srwGreenInf d z / srwGreenInf d 0 ≤ ε / 2 := by
        rw [div_le_iff₀ hG0pos]; exact h2
      have h4 : 0 ≤ srwGreenInf d z / srwGreenInf d 0 :=
        div_nonneg (srwGreenInf_nonneg z) (le_of_lt hG0pos)
      have hrw : h z = (f z - 1) + srwGreenInf d z / srwGreenInf d 0 := by rw [hh]; ring
      rw [hrw]
      have := abs_add_le (f z - 1) (srwGreenInf d z / srwGreenInf d 0)
      have h5 : |srwGreenInf d z / srwGreenInf d 0| = srwGreenInf d z / srwGreenInf d 0 :=
        abs_of_nonneg h4
      linarith [this, h5]
    have hq : (fun _ : Fin d => ((max R₁ R₂ : ℕ) : ℤ) + 1) ∉ boxFinset (0 : Site d) (max R₁ R₂) := by
      rw [mem_boxFinset_iff]
      simp only [not_forall, not_le]
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp only [Pi.zero_apply, sub_zero]
      rw [abs_of_nonneg (by positivity)]
      omega
    have hzero' : h 0 = 0 := by rw [hh]; simp only; rw [hzero, hg0]; ring
    have hup : ∀ z : Site d, h z ≤ ε :=
      le_of_harmonic_on_box hd1 (boxFinset (0 : Site d) (max R₁ R₂)) {(0 : Site d)} h ε hq
        (fun z _ hzS => hharm' z (by simpa using hzS))
        (fun z hz => le_trans (le_abs_self _) (hout z hz))
        (fun z hz => by rw [show z = (0 : Site d) from hz, hzero']; linarith)
    have hdown : ∀ z : Site d, -h z ≤ ε := by
      refine le_of_harmonic_on_box hd1 (boxFinset (0 : Site d) (max R₁ R₂)) {(0 : Site d)}
        (fun z => -h z) ε hq (fun z _ hzS => ?_) (fun z hz => ?_) (fun z hz => ?_)
      · rw [walkOp_neg h z, hharm' z (by simpa using hzS)]
      · exact le_trans (neg_le_abs _) (hout z hz)
      · rw [show z = (0 : Site d) from hz, hzero']
        simpa using le_of_lt hε
    exact abs_le.mpr ⟨by linarith [hdown y], hup y⟩
  intro x
  have habs : |f x - (1 - srwGreenInf d x / srwGreenInf d 0)| ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using key ε hε x
  have := abs_nonpos_iff.mp habs
  linarith [sub_eq_zero.mp this]

end LatticeProb

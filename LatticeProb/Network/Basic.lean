/-
Electrical networks on a locally finite graph.

A network is a locally finite `SimpleGraph V` together with a conductance
`c : V → V → ℝ`, symmetric, positive on the edges and zero off them
(`IsCond`).  The conductance `unitCond G` that gives every edge conductance one
has vertex weight `weight G (unitCond G) x = G.degree x`, so the simple random
walk of `LatticeProb.Graph` is the walk of the unit network.

Conventions.  Every sum here runs over ORDERED pairs `(x,y)` with `y ∼ x`, so
an edge with both endpoints in the index set is counted twice, once in each
orientation.  Thus

* `netLaplacian G c f x = ∑_{y ∼ x} c(x,y) (f y - f x)` is the network
  Laplacian, and `netLaplacian G (unitCond G) = LatticeProb.Graph.laplacian`;
* `formOn G c S f g = ∑_{x ∈ S} ∑_{y ∼ x} c(x,y) (f x - f y) (g x - g y)` is
  twice the Dirichlet form of `f` and `g` restricted to the edges met by `S`;
* `energyOn G c S f = formOn G c S f f` is twice the Dirichlet energy.

The factor two is carried explicitly rather than divided out, so that no
statement below has to divide by two.

An infinite graph has no finite index set containing every edge, so the index
set `S` is an argument.  The identities are stated for a function supported in
a finite set `B` and an index set `S` containing `B` and all of its neighbours;
that is the only shape the applications need, and it is what makes the
summation by parts a finite manipulation.
-/
import LatticeProb.Graph.Basic

namespace LatticeProb.Network

open Finset

variable {V : Type*} {G : SimpleGraph V}

/-! ### Conductances -/

/-- `c` is a conductance on `G`: symmetric, positive on the edges of `G`, and
zero on every pair that is not an edge. -/
structure IsCond (G : SimpleGraph V) (c : V → V → ℝ) : Prop where
  symm : ∀ x y, c x y = c y x
  pos : ∀ ⦃x y⦄, G.Adj x y → 0 < c x y
  zero_of_not_adj : ∀ ⦃x y⦄, ¬ G.Adj x y → c x y = 0

theorem IsCond.nonneg {c : V → V → ℝ} (hc : IsCond G c) (x y : V) : 0 ≤ c x y := by
  by_cases h : G.Adj x y
  · exact (hc.pos h).le
  · exact (hc.zero_of_not_adj h).ge

open scoped Classical in
/-- The unit conductance: every edge of `G` has conductance one. -/
noncomputable def unitCond (G : SimpleGraph V) : V → V → ℝ :=
  fun x y => if G.Adj x y then 1 else 0

theorem isCond_unitCond : IsCond G (unitCond G) := by
  classical
  refine ⟨fun x y => ?_, fun x y h => ?_, fun x y h => ?_⟩
  · by_cases h : G.Adj x y
    · simp [unitCond, h, h.symm]
    · rw [unitCond, unitCond, if_neg h, if_neg fun hc : G.Adj y x => h hc.symm]
  · simp [unitCond, h]
  · simp [unitCond, h]

/-- The total conductance at `x`, `π(x) = ∑_{y ∼ x} c(x,y)`. -/
noncomputable def weight (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, c x y

theorem weight_unitCond [G.LocallyFinite] (x : V) :
    weight G (unitCond G) x = G.degree x := by
  classical
  rw [weight]
  rw [Finset.sum_congr rfl (fun y hy => ?_)]
  · rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
  · rw [unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)]

/-! ### The Laplacian -/

/-- The network Laplacian `Δ_c f(x) = ∑_{y ∼ x} c(x,y) (f y - f x)`. -/
noncomputable def netLaplacian (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (f : V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, c x y * (f y - f x)

theorem netLaplacian_unitCond [G.LocallyFinite] (f : V → ℝ) (x : V) :
    netLaplacian G (unitCond G) f x = LatticeProb.Graph.laplacian G f x := by
  classical
  rw [netLaplacian, LatticeProb.Graph.laplacian]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy), one_mul]

theorem netLaplacian_add [G.LocallyFinite] (c : V → V → ℝ) (f g : V → ℝ) (x : V) :
    netLaplacian G c (f + g) x = netLaplacian G c f x + netLaplacian G c g x := by
  simp only [netLaplacian, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem netLaplacian_smul [G.LocallyFinite] (c : V → V → ℝ) (a : ℝ) (f : V → ℝ) (x : V) :
    netLaplacian G c (fun v => a * f v) x = a * netLaplacian G c f x := by
  simp only [netLaplacian, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem netLaplacian_const [G.LocallyFinite] (c : V → V → ℝ) (a : ℝ) (x : V) :
    netLaplacian G c (fun _ => a) x = 0 := by
  simp [netLaplacian]

/-- `f` is `c`-harmonic on `S`. -/
def HarmonicOn (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (f : V → ℝ)
    (S : Set V) : Prop :=
  ∀ x ∈ S, netLaplacian G c f x = 0

/-- The mean value property: at a vertex of positive total conductance,
harmonicity says that `f x` is the `c`-weighted average of its neighbours. -/
theorem harmonic_iff_mean [G.LocallyFinite] {c : V → V → ℝ} (f : V → ℝ) {x : V}
    (hx : weight G c x ≠ 0) :
    netLaplacian G c f x = 0 ↔
      f x = (∑ y ∈ G.neighborFinset x, c x y * f y) / weight G c x := by
  have h : netLaplacian G c f x
      = (∑ y ∈ G.neighborFinset x, c x y * f y) - weight G c x * f x := by
    rw [netLaplacian, weight, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [h, sub_eq_zero, eq_div_iff hx]
  constructor <;> intro h' <;> linarith

/-! ### The Dirichlet form -/

/-- Twice the Dirichlet form of `f` and `g` over the index set `S`,
`∑_{x ∈ S} ∑_{y ∼ x} c(x,y) (f x - f y)(g x - g y)`. -/
noncomputable def formOn (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (S : Finset V) (f g : V → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * (g x - g y)

/-- Twice the Dirichlet energy of `f` over the index set `S`. -/
noncomputable def energyOn (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (S : Finset V) (f : V → ℝ) : ℝ :=
  formOn G c S f f

theorem energyOn_eq_sum [G.LocallyFinite] (c : V → V → ℝ) (S : Finset V) (f : V → ℝ) :
    energyOn G c S f = ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) ^ 2 := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem energyOn_nonneg [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c) (S : Finset V)
    (f : V → ℝ) : 0 ≤ energyOn G c S f := by
  rw [energyOn_eq_sum]
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hc.nonneg x y) (sq_nonneg _)

theorem formOn_comm [G.LocallyFinite] (c : V → V → ℝ) (S : Finset V) (f g : V → ℝ) :
    formOn G c S f g = formOn G c S g f :=
  Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem formOn_add_left [G.LocallyFinite] (c : V → V → ℝ) (S : Finset V) (f g h : V → ℝ) :
    formOn G c S (f + g) h = formOn G c S f h + formOn G c S g h := by
  simp only [formOn, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem energyOn_mono_set [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c) {S T : Finset V}
    (hST : S ⊆ T) (f : V → ℝ) : energyOn G c S f ≤ energyOn G c T f := by
  rw [energyOn_eq_sum, energyOn_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg hST fun x _ _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (hc.nonneg x y) (sq_nonneg _)

/-! ### Summation by parts -/

/-- Replacing the neighbour sum by a sum over any finite set that contains
every neighbour carrying a nonzero term. -/
theorem sum_neighborFinset_eq_sum [G.LocallyFinite] (x : V) (S : Finset V) (F : V → ℝ)
    (hzero : ∀ y, ¬ G.Adj x y → F y = 0) (hmem : ∀ y ∈ G.neighborFinset x, F y ≠ 0 → y ∈ S) :
    ∑ y ∈ G.neighborFinset x, F y = ∑ y ∈ S, F y := by
  classical
  have h1 : ∑ y ∈ G.neighborFinset x, F y = ∑ y ∈ G.neighborFinset x ∩ S, F y := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro y hy hy'
    by_contra hne
    exact hy' (Finset.mem_inter.mpr ⟨hy, hmem y hy hne⟩)
  have h2 : ∑ y ∈ S, F y = ∑ y ∈ G.neighborFinset x ∩ S, F y := by
    refine (Finset.sum_subset Finset.inter_subset_right ?_).symm
    intro y hy hy'
    by_contra hne
    refine hy' (Finset.mem_inter.mpr ⟨?_, hy⟩)
    by_contra hadj
    exact hne (hzero y fun h => hadj ((SimpleGraph.mem_neighborFinset _ _ _).mpr h))
  rw [h1, h2]

/-- Summation by parts.  If `g` vanishes off the finite set `B`, and the index
set `S` contains `B` together with all of its neighbours, then
`formOn G c S f g = -2 ∑_{x ∈ B} g(x) Δ_c f(x)`. -/
theorem formOn_eq_neg_two_mul [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c)
    (S B : Finset V) (f g : V → ℝ) (hg : ∀ x, x ∉ B → g x = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    formOn G c S f g = -2 * ∑ x ∈ B, g x * netLaplacian G c f x := by
  classical
  have hsplit : formOn G c S f g
      = (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * g x)
        - ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * g y := by
    rw [formOn, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  -- the first piece
  have hA : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * g x)
      = - ∑ x ∈ B, g x * netLaplacian G c f x := by
    have hstep : ∀ x : V, (∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * g x)
        = - (g x * netLaplacian G c f x) := by
      intro x
      refine eq_neg_of_add_eq_zero_left ?_
      rw [netLaplacian, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun y _ => by ring
    rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_neg_distrib]
    congr 1
    refine (Finset.sum_subset hBS ?_).symm
    intro x _ hx
    rw [hg x hx]
    ring
  -- the second piece, after exchanging the two summations
  have hB : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * g y)
      = ∑ x ∈ B, g x * netLaplacian G c f x := by
    have hinner : ∀ x : V, (∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * g y)
        = ∑ y ∈ S, c x y * (f x - f y) * g y := by
      intro x
      refine sum_neighborFinset_eq_sum x S _ ?_ ?_
      · intro y hy
        rw [hc.zero_of_not_adj hy]
        ring
      · intro y _ hne
        by_contra hyS
        exact hne (by rw [hg y fun hyB => hyS (hBS hyB)]; ring)
    rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_comm]
    have houter : ∀ y ∈ S, (∑ x ∈ S, c x y * (f x - f y) * g y)
        = if y ∈ B then g y * netLaplacian G c f y else 0 := by
      intro y _
      by_cases hyB : y ∈ B
      · rw [if_pos hyB]
        have : (∑ x ∈ S, c x y * (f x - f y) * g y)
            = ∑ x ∈ G.neighborFinset y, c x y * (f x - f y) * g y := by
          refine (sum_neighborFinset_eq_sum y S _ ?_ ?_).symm
          · intro x hx
            rw [hc.zero_of_not_adj fun h => hx h.symm]
            ring
          · intro x hx _
            exact hnb y hyB x ((SimpleGraph.mem_neighborFinset _ _ _).mp hx)
        rw [this, netLaplacian, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by rw [hc.symm x y]; ring
      · rw [if_neg hyB, hg y hyB]
        exact Finset.sum_eq_zero fun x _ => by ring
    rw [Finset.sum_congr rfl houter, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hBS]
  rw [hsplit, hA, hB]
  ring

/-- The energy of a function supported in `B` in terms of its Laplacian. -/
theorem energyOn_eq_neg_two_mul [G.LocallyFinite] {c : V → V → ℝ} (hc : IsCond G c)
    (S B : Finset V) (f : V → ℝ) (hf : ∀ x, x ∉ B → f x = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    energyOn G c S f = -2 * ∑ x ∈ B, f x * netLaplacian G c f x :=
  formOn_eq_neg_two_mul hc S B f f hf hBS hnb

end LatticeProb.Network

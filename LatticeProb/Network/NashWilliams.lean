/-
The Nash-Williams cutset bound.

The energy of a flow is a sum over the ordered pairs `(x,y)` with `x` in the
index set and `y ∼ x`; `sum_nbr_eq_sum_pairs` writes it that way.  A cutset is a
set of such pairs across which the flow carries at least a unit, and
`one_div_sum_le_sum_sq_div` bounds the energy the flow spends on one cutset from
below by the reciprocal of its total conductance.  Summing over pairwise
disjoint cutsets gives `nashWilliams`, and with Thomson's principle a lower
bound on the effective resistance.
-/
import LatticeProb.Network.Flow

open Finset

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [DecidableEq V]

/-- The ordered pairs `(x,y)` with `x` in `S` and `y` a neighbour of `x`, the
index set of every energy sum. -/
noncomputable def pairs (G : SimpleGraph V) [G.LocallyFinite] (S : Finset V) :
    Finset (V × V) :=
  S.biUnion fun x => (G.neighborFinset x).image fun y => (x, y)

theorem pairwiseDisjoint_pairs (S : Finset V) :
    (S : Set V).PairwiseDisjoint
      fun x : V => (G.neighborFinset x).image fun y => (x, y) := by
  intro a _ b _ hab
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr fun p hp hq => ?_
  rw [Finset.mem_image] at hp hq
  obtain ⟨y, _, hy⟩ := hp
  obtain ⟨z, _, hz⟩ := hq
  exact hab ((congrArg Prod.fst hy).trans (congrArg Prod.fst hz).symm)

/-- A double sum over a vertex set and its neighbours is a sum over ordered
pairs. -/
theorem sum_nbr_eq_sum_pairs (S : Finset V) (F : V → V → ℝ) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, F x y = ∑ p ∈ pairs G S, F p.1 p.2 := by
  rw [pairs, Finset.sum_biUnion (pairwiseDisjoint_pairs S)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (fun y _ z _ h => congrArg Prod.snd h)]

theorem flowEnergyOn_eq_sum_pairs (c : V → V → ℝ) (S : Finset V) (θ : V → V → ℝ) :
    flowEnergyOn G c S θ = ∑ p ∈ pairs G S, θ p.1 p.2 ^ 2 / c p.1 p.2 :=
  sum_nbr_eq_sum_pairs S (fun x y => θ x y ^ 2 / c x y)

/-- The Nash-Williams bound: the energy of a flow is at least the sum, over any
family of pairwise disjoint cutsets it carries a unit across, of the reciprocals
of their total conductances. -/
theorem nashWilliams {ι : Type*} [DecidableEq ι] {c : V → V → ℝ} (hc : IsCond G c)
    (S : Finset V) (θ : V → V → ℝ) (K : Finset ι) (Cut : ι → Finset (V × V))
    (hsub : ∀ k ∈ K, Cut k ⊆ pairs G S)
    (hdisj : (K : Set ι).PairwiseDisjoint Cut)
    (hpos : ∀ k ∈ K, ∀ p ∈ Cut k, 0 < c p.1 p.2)
    (hcut : ∀ k ∈ K, 1 ≤ ∑ p ∈ Cut k, θ p.1 p.2) :
    ∑ k ∈ K, 1 / (∑ p ∈ Cut k, c p.1 p.2) ≤ flowEnergyOn G c S θ := by
  classical
  have hstep : ∀ k ∈ K, 1 / (∑ p ∈ Cut k, c p.1 p.2)
      ≤ ∑ p ∈ Cut k, θ p.1 p.2 ^ 2 / c p.1 p.2 := fun k hk =>
    one_div_sum_le_sum_sq_div (Cut k) (fun p => θ p.1 p.2) (fun p => c p.1 p.2)
      (hpos k hk) (hcut k hk)
  calc ∑ k ∈ K, 1 / (∑ p ∈ Cut k, c p.1 p.2)
      ≤ ∑ k ∈ K, ∑ p ∈ Cut k, θ p.1 p.2 ^ 2 / c p.1 p.2 := Finset.sum_le_sum hstep
    _ = ∑ p ∈ K.biUnion Cut, θ p.1 p.2 ^ 2 / c p.1 p.2 :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ p ∈ pairs G S, θ p.1 p.2 ^ 2 / c p.1 p.2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hp
          exact hsub k hk hpk
        · exact fun p _ _ => div_nonneg (sq_nonneg _) (hc.nonneg p.1 p.2)
    _ = flowEnergyOn G c S θ := (flowEnergyOn_eq_sum_pairs c S θ).symm

/-- With Thomson's principle: a family of pairwise disjoint cutsets bounds the
effective resistance from below. -/
theorem nashWilliams_le_effRes {ι : Type*} [DecidableEq ι] (hG : G.Connected) (C : Finset V)
    {o q : V} (ho : o ∈ C) (hq : q ∉ C) (K : Finset ι) (Cut : ι → Finset (V × V))
    (hsub : ∀ k ∈ K, Cut k ⊆ pairs G (nbhd G C))
    (hdisj : (K : Set ι).PairwiseDisjoint Cut)
    (hpos : ∀ k ∈ K, ∀ p ∈ Cut k, 0 < unitCond G p.1 p.2)
    (hcut : ∀ k ∈ K,
      1 ≤ ∑ p ∈ Cut k, current G (unitCond G) (killedGreenReal G (C : Set V) o) p.1 p.2) :
    ∑ k ∈ K, 1 / (∑ p ∈ Cut k, unitCond G p.1 p.2) ≤ 2 * effRes G C o := by
  rw [← energyOn_killedGreenReal hG C ho hq]
  have hflow : flowEnergyOn G (unitCond G) (nbhd G C)
      (current G (unitCond G) (killedGreenReal G (C : Set V) o))
      = energyOn G (unitCond G) (nbhd G C) (killedGreenReal G (C : Set V) o) := by
    rw [flowEnergyOn, energyOn_eq_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y hy => ?_
    have hcpos : 0 < unitCond G x y :=
      isCond_unitCond.pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
    rw [current]
    field_simp
  rw [← hflow]
  exact nashWilliams isCond_unitCond (nbhd G C) _ K Cut hsub hdisj hpos hcut

end LatticeProb.Network

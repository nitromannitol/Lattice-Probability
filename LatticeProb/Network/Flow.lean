/-
Flows and Thomson's principle.

A flow `θ` is an antisymmetric function on the ordered pairs of vertices,
vanishing off the edges; its divergence at `x` is the total outflow
`∑_{y ∼ x} θ(x,y)` and its energy is `∑ θ(x,y)^2 / c(x,y)`, again over ordered
pairs, so it is twice the physical energy.  The current carried by a voltage `f`
is the flow `c(x,y)(f x - f y)`, whose divergence is `-Δ_c f`.

`thomson_principle` says that among the flows with the divergence prescribed by
a voltage, the current of that voltage has the least energy.  The proof is the
summation by parts `sum_sub_mul_flow`: the difference of two such flows has
divergence zero where the voltage lives, so the cross term vanishes and the two
energies differ by the energy of the difference.

Applied to the killed Green function this bounds the effective resistance by the
energy of any unit flow out of `C`, which is the form used to decide transience.
-/
import LatticeProb.Network.Variational

open Finset
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- A flow on `G`: antisymmetric, and carried by the edges. -/
structure IsFlow (G : SimpleGraph V) (θ : V → V → ℝ) : Prop where
  antisymm : ∀ x y, θ y x = -θ x y
  zero_of_not_adj : ∀ ⦃x y⦄, ¬ G.Adj x y → θ x y = 0

/-- The divergence of a flow: the total outflow at a vertex. -/
noncomputable def divergence (G : SimpleGraph V) [G.LocallyFinite] (θ : V → V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, θ x y

/-- The energy of a flow over an index set, over ordered pairs. -/
noncomputable def flowEnergyOn (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (S : Finset V) (θ : V → V → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, θ x y ^ 2 / c x y

theorem flowEnergyOn_nonneg {c : V → V → ℝ} (hc : IsCond G c) (S : Finset V) (θ : V → V → ℝ) :
    0 ≤ flowEnergyOn G c S θ :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    div_nonneg (sq_nonneg _) (hc.nonneg x y)

/-- The current carried by a voltage is a flow. -/
theorem isFlow_current {c : V → V → ℝ} (hc : IsCond G c) (f : V → ℝ) :
    IsFlow G (current G c f) := by
  refine ⟨fun x y => ?_, fun x y hxy => ?_⟩
  · rw [current, current, hc.symm y x]; ring
  · rw [current, hc.zero_of_not_adj hxy, zero_mul]

theorem divergence_current {c : V → V → ℝ} (f : V → ℝ) (x : V) :
    divergence G (current G c f) x = -netLaplacian G c f x := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [divergence, netLaplacian, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun y _ => by rw [current]; ring

omit [G.LocallyFinite] in
theorem isFlow_sub {θ η : V → V → ℝ} (hθ : IsFlow G θ) (hη : IsFlow G η) :
    IsFlow G (fun x y => θ x y - η x y) := by
  refine ⟨fun x y => ?_, fun x y hxy => ?_⟩
  · rw [hθ.antisymm x y, hη.antisymm x y]; ring
  · rw [hθ.zero_of_not_adj hxy, hη.zero_of_not_adj hxy, sub_zero]

theorem divergence_sub {θ η : V → V → ℝ} (x : V) :
    divergence G (fun a b => θ a b - η a b) x = divergence G θ x - divergence G η x := by
  rw [divergence, divergence, divergence, ← Finset.sum_sub_distrib]

/-- Summation by parts for a flow. -/
theorem sum_sub_mul_flow {w : V → V → ℝ} (hw : IsFlow G w) (S B : Finset V) (f : V → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, (f x - f y) * w x y
      = 2 * ∑ x ∈ B, f x * divergence G w x := by
  classical
  have hsplit : ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, (f x - f y) * w x y
      = (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, f x * w x y)
        - ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, f y * w x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hA : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, f x * w x y)
      = ∑ x ∈ B, f x * divergence G w x := by
    have hstep : ∀ x : V, (∑ y ∈ G.neighborFinset x, f x * w x y)
        = f x * divergence G w x := by
      intro x
      rw [divergence, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun x _ => hstep x)]
    refine (Finset.sum_subset hBS ?_).symm
    intro x _ hx
    rw [hf x hx, zero_mul]
  have hB : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, f y * w x y)
      = -∑ x ∈ B, f x * divergence G w x := by
    have hinner : ∀ x : V, (∑ y ∈ G.neighborFinset x, f y * w x y)
        = ∑ y ∈ S, f y * w x y := by
      intro x
      refine sum_neighborFinset_eq_sum x S _ ?_ ?_
      · intro y hy
        rw [hw.zero_of_not_adj hy, mul_zero]
      · intro y _ hne
        by_contra hyS
        exact hne (by rw [hf y fun hyB => hyS (hBS hyB), zero_mul])
    rw [Finset.sum_congr rfl (fun x _ => hinner x), Finset.sum_comm]
    have houter : ∀ y ∈ S, (∑ x ∈ S, f y * w x y)
        = if y ∈ B then -(f y * divergence G w y) else 0 := by
      intro y _
      by_cases hyB : y ∈ B
      · rw [if_pos hyB]
        have hres : (∑ x ∈ S, f y * w x y) = ∑ x ∈ G.neighborFinset y, f y * w x y := by
          refine (sum_neighborFinset_eq_sum y S _ ?_ ?_).symm
          · intro x hx
            rw [hw.zero_of_not_adj (fun h => hx h.symm), mul_zero]
          · intro x hx _
            exact hnb y hyB x ((SimpleGraph.mem_neighborFinset _ _ _).mp hx)
        rw [hres]
        refine eq_neg_of_add_eq_zero_left ?_
        rw [divergence, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun x _ => by rw [hw.antisymm y x]; ring
      · rw [if_neg hyB, hf y hyB]
        exact Finset.sum_eq_zero fun x _ => by rw [zero_mul]
    rw [Finset.sum_congr rfl houter]
    rw [show (∑ y ∈ S, if y ∈ B then -(f y * divergence G w y) else 0)
        = ∑ y ∈ B, -(f y * divergence G w y) by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hBS]]
    rw [Finset.sum_neg_distrib]
  rw [hsplit, hA, hB]
  ring

/-- Thomson's principle: among the flows whose divergence is the one prescribed
by the voltage `f`, the current of `f` has the least energy. -/
theorem thomson_principle {c : V → V → ℝ} (hc : IsCond G c) (S B : Finset V) (f : V → ℝ)
    (θ : V → V → ℝ) (hθ : IsFlow G θ)
    (hf : ∀ x, x ∉ B → f x = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S)
    (hdiv : ∀ x ∈ B, divergence G θ x = -netLaplacian G c f x) :
    energyOn G c S f ≤ flowEnergyOn G c S θ := by
  classical
  set w : V → V → ℝ := fun x y => θ x y - current G c f x y with hw
  have hwflow : IsFlow G w := isFlow_sub hθ (isFlow_current hc f)
  have hwdiv : ∀ x ∈ B, divergence G w x = 0 := by
    intro x hx
    rw [hw, divergence_sub, divergence_current, hdiv x hx, sub_self]
  have hcross : ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, (f x - f y) * w x y = 0 := by
    rw [sum_sub_mul_flow hwflow S B f hf hBS hnb,
      Finset.sum_congr rfl (fun x hx => by rw [hwdiv x hx, mul_zero])]
    simp
  have hpt : ∀ x : V, ∀ y ∈ G.neighborFinset x,
      θ x y ^ 2 / c x y
        = c x y * (f x - f y) ^ 2 + 2 * ((f x - f y) * w x y) + w x y ^ 2 / c x y := by
    intro x y hy
    have hcpos : 0 < c x y := hc.pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
    have hθw : θ x y = c x y * (f x - f y) + w x y := by
      simp only [hw, current]; ring
    rw [hθw]
    field_simp
    ring
  have hexp : flowEnergyOn G c S θ
      = energyOn G c S f
        + 2 * (∑ x ∈ S, ∑ y ∈ G.neighborFinset x, (f x - f y) * w x y)
        + flowEnergyOn G c S w := by
    rw [flowEnergyOn, energyOn_eq_sum, flowEnergyOn, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y hy => hpt x y hy
  rw [hexp, hcross]
  have := flowEnergyOn_nonneg hc S w
  linarith

/-- The effective resistance is at most half the energy of any unit flow out of
`C`.  This is the bound that a finite-energy flow gives. -/
theorem effRes_le_flowEnergy (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) (θ : V → V → ℝ) (hθ : IsFlow G θ)
    (hdiv : ∀ x ∈ C, divergence G θ x = if x = o then (1 : ℝ) else 0) :
    2 * effRes G C o ≤ flowEnergyOn G (unitCond G) (nbhd G C) θ := by
  classical
  have hvan : ∀ x, x ∉ C → killedGreenReal G (C : Set V) o x = 0 := fun x hx =>
    killedGreenReal_eq_zero_of_not_mem hG C hq hx o
  have hlap : ∀ x ∈ C,
      divergence G θ x = -netLaplacian G (unitCond G) (killedGreenReal G (C : Set V) o) x := by
    intro x hx
    rw [netLaplacian_unitCond,
      laplacian_killedGreenReal hG C ho hq (by exact_mod_cast hx), neg_neg, hdiv x hx]
  rw [← energyOn_killedGreenReal hG C ho hq]
  exact thomson_principle isCond_unitCond (nbhd G C) C _ θ hθ hvan (subset_nbhd C)
    (fun x hx y hxy => mem_nbhd_of_adj hx hxy) hlap

end LatticeProb.Network

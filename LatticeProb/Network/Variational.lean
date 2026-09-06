/-
The variational principles of an electrical network, and the effective
resistance.

* `energyOn_add` expands the energy of a sum, so the Dirichlet principle
  (`dirichlet_principle`) is one line of summation by parts: a function
  harmonic where the competitor is free to move has the smallest energy among
  all competitors with the same boundary data, the difference of the two
  energies being the energy of the difference.
* `rayleigh_monotone` is Rayleigh monotonicity in that form: raising the
  conductances raises the minimal energy, hence lowers the resistance.
* `effRes G C o` is the effective resistance from `o` to the complement of the
  finite set `C`, defined as the killed Green function at the source; the
  energy identity `energyOn_killedGreenReal` says that it is exactly half of
  the energy of the equilibrium voltage, and `flux_eq_one` is Kirchhoff's node
  law, that the current out of any set containing the source and no boundary
  vertex is one.
* `one_div_sum_le_sum_sq_div` is the Cauchy--Schwarz step of the
  Nash-Williams cutset bound: a flow that carries at least a unit across a
  cutset has energy at least the reciprocal of the total conductance of that
  cutset.

Sums run over ordered pairs, so every energy here is twice the Dirichlet
energy; see `LatticeProb/Network/Basic.lean`.
-/
import LatticeProb.Network.KilledGreen

open Finset
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The index set of a finite vertex set -/

/-- A finite set together with all of its neighbours. -/
noncomputable def nbhd (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) : Finset V :=
  C ∪ C.biUnion fun x => G.neighborFinset x

theorem subset_nbhd (C : Finset V) : C ⊆ nbhd G C := Finset.subset_union_left

theorem mem_nbhd_of_adj {C : Finset V} {x : V} (hx : x ∈ C) {y : V} (hxy : G.Adj x y) :
    y ∈ nbhd G C :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨x, hx, (SimpleGraph.mem_neighborFinset _ _ _).mpr hxy⟩)

/-! ### The Dirichlet principle -/

theorem formOn_add_right (c : V → V → ℝ) (S : Finset V) (f g h : V → ℝ) :
    formOn G c S f (g + h) = formOn G c S f g + formOn G c S f h := by
  rw [formOn_comm, formOn_add_left, formOn_comm c S g f, formOn_comm c S h f]

theorem energyOn_add (c : V → V → ℝ) (S : Finset V) (f h : V → ℝ) :
    energyOn G c S (f + h)
      = energyOn G c S f + 2 * formOn G c S f h + energyOn G c S h := by
  rw [energyOn, formOn_add_left, formOn_add_right, formOn_add_right,
    formOn_comm c S h f, energyOn, energyOn]
  ring

/-- The Dirichlet principle: among the functions with the same values off a
finite set `B`, the one harmonic on `B` has the least energy. -/
theorem dirichlet_principle {c : V → V → ℝ} (hc : IsCond G c) (S B : Finset V) (f g : V → ℝ)
    (hsupp : ∀ x, x ∉ B → g x = f x) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S)
    (hharm : ∀ x ∈ B, netLaplacian G c f x = 0) :
    energyOn G c S f ≤ energyOn G c S g := by
  set h : V → ℝ := fun x => g x - f x with hh
  have hg : g = f + h := by
    funext x; simp [hh]
  have hzero : ∀ x, x ∉ B → h x = 0 := by
    intro x hx; simp [hh, hsupp x hx]
  have hform : formOn G c S f h = 0 := by
    rw [formOn_eq_neg_two_mul hc S B f h hzero hBS hnb]
    rw [Finset.sum_congr rfl (fun x hx => by rw [hharm x hx, mul_zero])]
    simp
  rw [hg, energyOn_add, hform]
  have := energyOn_nonneg hc S h
  linarith

/-- Rayleigh monotonicity in the energy form: raising the conductances raises
the energy of every function. -/
theorem energyOn_mono_cond {c c' : V → V → ℝ}
    (hcc : ∀ x y, c x y ≤ c' x y) (S : Finset V) (f : V → ℝ) :
    energyOn G c S f ≤ energyOn G c' S f := by
  rw [energyOn_eq_sum, energyOn_eq_sum]
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_right (hcc x y) (sq_nonneg _)

/-- Rayleigh monotonicity: the minimal energy for the larger conductance is at
least the minimal energy for the smaller one, so the effective resistance
decreases when a conductance is raised. -/
theorem rayleigh_monotone {c c' : V → V → ℝ} (hc : IsCond G c)
    (hcc : ∀ x y, c x y ≤ c' x y) (S B : Finset V) (f f' : V → ℝ)
    (hsupp : ∀ x, x ∉ B → f' x = f x) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S)
    (hharm : ∀ x ∈ B, netLaplacian G c f x = 0) :
    energyOn G c S f ≤ energyOn G c' S f' :=
  le_trans (dirichlet_principle hc S B f f' hsupp hBS hnb hharm)
    (energyOn_mono_cond hcc S f')

/-! ### Kirchhoff's node law -/

/-- The current along the edge `(x,y)` carried by the voltage `f`. -/
noncomputable def current (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (f : V → ℝ)
    (x y : V) : ℝ :=
  c x y * (f x - f y)

/-- The total current out of the finite set `U`. -/
noncomputable def flux (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (f : V → ℝ)
    (U : Finset V) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∉ U), current G c f x y

/-- Kirchhoff's node law across a cut: the current out of a set containing the
source and no vertex where the voltage is not harmonic is one. -/
theorem flux_eq_one {c : V → V → ℝ} (hc : IsCond G c) (f : V → ℝ) (U : Finset V) {o : V}
    (ho : o ∈ U)
    (hlap : ∀ x ∈ U, netLaplacian G c f x = -(if x = o then (1 : ℝ) else 0)) :
    flux G c f U = 1 := by
  classical
  have hanti : ∀ x y : V, current G c f y x = -current G c f x y := by
    intro x y
    rw [current, current, hc.symm y x]
    ring
  have hint : ∑ x ∈ U, ∑ y ∈ U, current G c f x y = 0 := by
    have h1 : ∑ x ∈ U, ∑ y ∈ U, current G c f x y
        = ∑ x ∈ U, ∑ y ∈ U, current G c f y x := Finset.sum_comm
    have h2 : (∑ x ∈ U, ∑ y ∈ U, current G c f y x)
        + ∑ x ∈ U, ∑ y ∈ U, current G c f x y = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hanti x y]
      ring
    linarith [h1, h2]
  have hsplit : ∀ x : V, ∑ y ∈ G.neighborFinset x, current G c f x y
      = (∑ y ∈ U, current G c f x y)
        + ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∉ U), current G c f x y := by
    intro x
    have hin : ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ U), current G c f x y
        = ∑ y ∈ U, current G c f x y := by
      refine Finset.sum_subset (fun y hy => (Finset.mem_filter.mp hy).2) ?_
      intro y hyU hy
      have hny : ¬ G.Adj x y := by
        intro h
        exact hy (Finset.mem_filter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr h, hyU⟩)
      rw [current, hc.zero_of_not_adj hny, zero_mul]
    rw [← hin]
    exact (Finset.sum_filter_add_sum_filter_not (G.neighborFinset x) (fun y => y ∈ U)
      (current G c f x)).symm
  have hlapsum : ∀ x : V, ∑ y ∈ G.neighborFinset x, current G c f x y
      = -netLaplacian G c f x := by
    intro x
    refine eq_neg_of_add_eq_zero_left ?_
    rw [netLaplacian, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun y _ => by rw [current]; ring
  have hmain : ∑ x ∈ U, (-netLaplacian G c f x)
      = (∑ x ∈ U, ∑ y ∈ U, current G c f x y) + flux G c f U := by
    rw [flux, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [← hlapsum x, hsplit x]
  rw [hint, zero_add] at hmain
  rw [← hmain, Finset.sum_congr rfl (fun x hx => by rw [hlap x hx, neg_neg]),
    Finset.sum_ite_eq' U o (fun _ => (1 : ℝ)), if_pos ho]

/-! ### The effective resistance -/

/-- The effective resistance from `o` to the complement of the finite set `C`,
which is the killed Green function at the source. -/
noncomputable def effRes (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) (o : V) : ℝ :=
  killedGreenReal G (C : Set V) o o

/-- The energy of the equilibrium voltage is twice the effective resistance.
The factor two is the ordered-pair convention. -/
theorem energyOn_killedGreenReal (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) :
    energyOn G (unitCond G) (nbhd G C) (killedGreenReal G (C : Set V) o)
      = 2 * effRes G C o := by
  classical
  have hvan : ∀ x, x ∉ C → killedGreenReal G (C : Set V) o x = 0 := fun x hx =>
    killedGreenReal_eq_zero_of_not_mem hG C hq hx o
  have hlap : ∀ x ∈ C, netLaplacian G (unitCond G) (killedGreenReal G (C : Set V) o) x
      = -(if x = o then (1 : ℝ) else 0) := by
    intro x hx
    rw [netLaplacian_unitCond]
    exact laplacian_killedGreenReal hG C ho hq (by exact_mod_cast hx)
  rw [energyOn_eq_neg_two_mul isCond_unitCond (nbhd G C) C _ hvan (subset_nbhd C)
    (fun x hx y hxy => mem_nbhd_of_adj hx hxy)]
  rw [Finset.sum_congr rfl (fun x hx => by rw [hlap x hx])]
  rw [Finset.sum_congr rfl (fun x _ => show
      killedGreenReal G (C : Set V) o x * -(if x = o then (1 : ℝ) else 0)
        = -(if x = o then killedGreenReal G (C : Set V) o x else 0) by
    by_cases h : x = o <;> simp [h])]
  rw [Finset.sum_neg_distrib, Finset.sum_ite_eq' C o (killedGreenReal G (C : Set V) o),
    if_pos ho, effRes]
  ring

/-! ### The Nash-Williams cutset bound -/

/-- The Cauchy--Schwarz step of the Nash-Williams bound: a flow carrying at
least a unit across a cutset has at least the reciprocal of the cutset's total
conductance as its energy there. -/
theorem one_div_sum_le_sum_sq_div {ι : Type*} (s : Finset ι) (θ w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hθ : 1 ≤ ∑ i ∈ s, θ i) :
    1 / (∑ i ∈ s, w i) ≤ ∑ i ∈ s, θ i ^ 2 / w i := by
  have hwpos : 0 < ∑ i ∈ s, w i := by
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · exact absurd hθ (by norm_num)
    · exact Finset.sum_pos hw hs
  refine le_trans ?_ (Finset.sq_sum_div_le_sum_sq_div s θ hw)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by nlinarith [hθ]) (by positivity)

end LatticeProb.Network

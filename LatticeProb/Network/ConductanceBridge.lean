/-
Built on modules adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
-/
import LatticeProb.Network.ConductanceHarmonic
import LatticeProb.Network.DirichletForm
import LatticeProb.Network.Basic

/-!
# Bridge from conductance graphs to LP's locally finite networks

For a `ConductanceGraph` `G`, the underlying simple graph `G.toSimpleGraph` with conductance `G.c`
is an LP network: `IsCond G.toSimpleGraph G.c` holds for every instance (`isCond_toSimpleGraph`).
This file relates the notions of `ConductanceGraph` to LP's `netLaplacian`, `HarmonicOn`,
`energyOn` and `formOn`, which live in `LatticeProb.Network` and assume local finiteness.

* `isHarmonicAt_iff_netLaplacian` and `isHarmonicOn_iff_harmonicOn`: under local finiteness,
  `G.IsHarmonicAt h x` is `netLaplacian G.toSimpleGraph G.c h x = 0`, and `G.IsHarmonicOn h S` is
  LP's `HarmonicOn G.toSimpleGraph G.c h S`. Absolute summability of the Laplacian sum holds
  automatically, because only finitely many terms are nonzero.
* `energy_eq_energyOn_half` and `dirichletForm_eq_formOn_half`: on a finite vertex type,
  `G.Energy f = energyOn G.toSimpleGraph G.c univ f / 2` and
  `G.dirichletForm f g = formOn G.toSimpleGraph G.c univ f g / 2`. The factor is `2` because
  `Energy` and `dirichletForm` carry the factor `½` over ordered pairs, while LP's `energyOn` and
  `formOn` sum over ordered pairs without it.

`ConductanceGraph` allows vertices of infinite degree, and LP's network API does not. The
harmonicity bridge therefore needs `[G.toSimpleGraph.LocallyFinite]`, and the energy bridge needs
a finite vertex type (where `toSimpleGraphLocallyFinite` supplies local finiteness), so neither
bridge applies to an infinite-degree instance. Results about such instances are stated for
`ConductanceGraph` directly.

The examples at the end check the bridges on `ConductanceGraph.Example.path3`, the path `0 – 1 – 2`,
which is finite and therefore locally finite (`toSimpleGraphLocallyFinite`, as a local instance).
-/

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- On a finite vertex type every vertex has finitely many neighbours, so `G.toSimpleGraph` is
locally finite. This is a definition, not a global instance; use it as a local instance. -/
@[reducible] noncomputable def toSimpleGraphLocallyFinite [Finite V] :
    G.toSimpleGraph.LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- The underlying simple graph of a conductance graph, with conductance `G.c`, is a network in
LP's sense: the conductance is symmetric, positive on edges, and zero on non-edges. -/
theorem isCond_toSimpleGraph : IsCond G.toSimpleGraph G.c where
  symm := G.c_symm
  pos := fun _ _ h => h
  zero_of_not_adj := fun _ _ h => le_antisymm (not_lt.mp h) (G.c_nonneg _ _)

/-- Under local finiteness, `h` is harmonic at `x` in the sense of `ConductanceGraph` exactly when
LP's network Laplacian of `h` vanishes at `x`. Absolute summability of the Laplacian sum is
automatic, since all but finitely many terms are zero. -/
theorem isHarmonicAt_iff_netLaplacian [G.toSimpleGraph.LocallyFinite] (h : V → ℝ) (x : V) :
    G.IsHarmonicAt h x ↔ netLaplacian G.toSimpleGraph G.c h x = 0 := by
  have hnb : ∀ y, y ∉ G.toSimpleGraph.neighborFinset x → G.c x y = 0 := fun y hy =>
    (isCond_toSimpleGraph G).zero_of_not_adj (by rwa [SimpleGraph.mem_neighborFinset] at hy)
  have habs : G.AbsSummableAt h x :=
    summable_of_ne_finset_zero (s := G.toSimpleGraph.neighborFinset x) fun y hy => by
      simp [hnb y hy]
  have hsum : ∑' y, G.lapTerm h x y = netLaplacian G.toSimpleGraph G.c h x :=
    (tsum_eq_sum (s := G.toSimpleGraph.neighborFinset x) fun y hy => by
      simp [lapTerm, hnb y hy]).trans rfl
  unfold IsHarmonicAt
  constructor
  · rintro ⟨-, hs⟩
    rw [← hsum]
    exact hs
  · intro hn
    refine ⟨habs, ?_⟩
    rw [hsum]
    exact hn

/-- Under local finiteness, `h` is harmonic on `S` in the sense of `ConductanceGraph` exactly when
it is `HarmonicOn` in LP's sense for the conductance `G.c` on `G.toSimpleGraph`. -/
theorem isHarmonicOn_iff_harmonicOn [G.toSimpleGraph.LocallyFinite] (h : V → ℝ) (S : Set V) :
    G.IsHarmonicOn h S ↔ HarmonicOn G.toSimpleGraph G.c h S :=
  ⟨fun H x hx => (G.isHarmonicAt_iff_netLaplacian h x).1 (H x hx),
    fun H x hx => (G.isHarmonicAt_iff_netLaplacian h x).2 (H x hx)⟩

/-- On a finite vertex type, the Dirichlet form of `f` and `g` is half of LP's `formOn` over the
whole vertex set. -/
theorem dirichletForm_eq_formOn_half [Fintype V] [G.toSimpleGraph.LocallyFinite] (f g : V → ℝ) :
    G.dirichletForm f g = formOn G.toSimpleGraph G.c Finset.univ f g / 2 := by
  have hsum : ∑' p : V × V, G.gradProd f g p = formOn G.toSimpleGraph G.c Finset.univ f g := by
    rw [tsum_fintype, formOn, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sum_neighborFinset_eq_sum (G := G.toSimpleGraph) x Finset.univ]
    · exact Finset.sum_congr rfl fun y _ => by simp only [gradProd]; ring
    · intro y hy
      simp [(isCond_toSimpleGraph G).zero_of_not_adj hy]
    · intro y _ _
      exact Finset.mem_univ y
  rw [dirichletForm, hsum]

/-- On a finite vertex type, the Dirichlet energy is half of LP's `energyOn` over the whole vertex
set. The factor is `2`: `energyOn` sums over ordered pairs without the factor `½`. -/
theorem energy_eq_energyOn_half [Fintype V] [G.toSimpleGraph.LocallyFinite] (f : V → ℝ) :
    G.Energy f = energyOn G.toSimpleGraph G.c Finset.univ f / 2 := by
  rw [← G.dirichletForm_self, G.dirichletForm_eq_formOn_half]
  rfl

end ConductanceGraph

/-! ## Examples

These check the bridges on `ConductanceGraph.Example.path3`, the path `0 – 1 – 2` with unit
conductances. It is finite, so it is locally finite and the bridges apply. -/

namespace ConductanceGraph.Example

attribute [local instance] ConductanceGraph.toSimpleGraphLocallyFinite

/-- The energy identity holds for the concrete function `x ↦ x` on `path3`. -/
example : path3.Energy (fun x : Fin 3 => ((x : ℕ) : ℝ)) =
    energyOn path3.toSimpleGraph path3.c Finset.univ (fun x : Fin 3 => ((x : ℕ) : ℝ)) / 2 :=
  energy_eq_energyOn_half path3 _

/-- On `path3`, the energy of `x ↦ x` is `2`: the two unit edges each contribute `1`. -/
theorem path3_energy_id : path3.Energy (fun x : Fin 3 => ((x : ℕ) : ℝ)) = 2 := by
  unfold ConductanceGraph.Energy ConductanceGraph.gradSq
  rw [tsum_fintype, Fintype.sum_prod_type]
  norm_num [path3, Fin.sum_univ_three]

/-- Through the bridge, LP's `energyOn` of `x ↦ x` over the whole of `path3` is `4`, twice the
energy `2`. -/
example :
    energyOn path3.toSimpleGraph path3.c Finset.univ (fun x : Fin 3 => ((x : ℕ) : ℝ)) = 4 := by
  have hE := energy_eq_energyOn_half path3 (fun x : Fin 3 => ((x : ℕ) : ℝ))
  linarith [path3_energy_id]

/-- On `path3`, the identity `x ↦ x` is harmonic at the middle vertex `1`, checked through the
bridge: its network Laplacian at `1` vanishes. -/
example : path3.IsHarmonicAt (fun x : Fin 3 => ((x : ℕ) : ℝ)) 1 := by
  refine (isHarmonicAt_iff_netLaplacian path3 _ 1).2 ?_
  rw [netLaplacian, sum_neighborFinset_eq_sum (G := path3.toSimpleGraph) 1 Finset.univ]
  · norm_num [path3, Fin.sum_univ_three]
  · intro y hy
    simp [(isCond_toSimpleGraph path3).zero_of_not_adj hy]
  · intro y _ _
    exact Finset.mem_univ y

end ConductanceGraph.Example

end LatticeProb.Network

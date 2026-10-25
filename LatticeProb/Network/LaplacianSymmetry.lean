module

/-
Symmetry of the graph Laplacian against finitely supported functions.

For a locally finite simple graph `G`, a finite set `D` of vertices, and functions `f` and `g`
vanishing off `D`, the two pairings with the Laplacian `Δ = LatticeProb.Graph.laplacian G` agree:
  `∑_{v∈D} f v Δg v = ∑_{v∈D} g v Δf v`.

The proof is the unit-conductance case of the summation by parts
`LatticeProb.Network.formOn_eq_neg_two_mul` for the network Laplacian, together with the
symmetry `formOn_comm` of the Dirichlet form.  The finite index set is `D` together with the
neighbours of `D`, and `netLaplacian_unitCond` identifies the network Laplacian with
`Graph.laplacian`.  Only the statement in the vocabulary of `Graph.laplacian` is new here.
-/
public import LatticeProb.Network.Basic

@[expose] public section

namespace LatticeProb.Network

/-- **Symmetry of the graph Laplacian.**  If `f` and `g` vanish off a finite set `D`, then
`∑_{v∈D} f(v) Δg(v) = ∑_{v∈D} g(v) Δf(v)`, where `Δ = LatticeProb.Graph.laplacian G` is the
unnormalized discrete Laplacian `Δh(x) = ∑_{y∼x} (h(y) - h(x))` of a locally finite graph. -/
theorem sum_mul_laplacian_comm {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (D : Finset V) (f g : V → ℝ) (hf : ∀ v, v ∉ D → f v = 0) (hg : ∀ v, v ∉ D → g v = 0) :
    ∑ v ∈ D, f v * LatticeProb.Graph.laplacian G g v
      = ∑ v ∈ D, g v * LatticeProb.Graph.laplacian G f v := by
  classical
  -- a finite index set containing `D` and every neighbour of a point of `D`
  obtain ⟨S, hBS, hnb⟩ : ∃ S : Finset V, D ⊆ S ∧ ∀ x ∈ D, ∀ y, G.Adj x y → y ∈ S :=
    ⟨D ∪ D.biUnion (fun x => G.neighborFinset x),
      fun x hx => Finset.mem_union_left _ hx,
      fun x hx y hxy => Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨x, hx, (G.mem_neighborFinset x y).mpr hxy⟩)⟩
  have h1 : formOn G (unitCond G) S f g
      = -2 * ∑ x ∈ D, g x * LatticeProb.Graph.laplacian G f x := by
    rw [formOn_eq_neg_two_mul (isCond_unitCond (G := G)) S D f g hg hBS hnb]
    simp only [netLaplacian_unitCond]
  have h2 : formOn G (unitCond G) S g f
      = -2 * ∑ x ∈ D, f x * LatticeProb.Graph.laplacian G g x := by
    rw [formOn_eq_neg_two_mul (isCond_unitCond (G := G)) S D g f hf hBS hnb]
    simp only [netLaplacian_unitCond]
  have h3 : formOn G (unitCond G) S f g = formOn G (unitCond G) S g f :=
    formOn_comm (unitCond G) S f g
  exact (mul_left_cancel₀ (by norm_num : (-2 : ℝ) ≠ 0) (h1.symm.trans (h3.trans h2))).symm

end LatticeProb.Network

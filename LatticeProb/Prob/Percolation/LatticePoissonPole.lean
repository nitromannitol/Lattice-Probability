import LatticeProb.Prob.Percolation.LatticeBondGraph
import LatticeProb.Lattice.SubtypeCofinite
import LatticeProb.Network.IntegerLaplacianSupport

/-!
# Integer Poisson poles on actual open components

A real function decaying in the coordinate ℓ¹ norm on an actual open component has a finite
integer pole whenever its negative component Laplacian is integer-valued. Integer casts
characterize the pole uniquely. Its standard zero extension has finite ambient support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open Filter Topology

variable {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)

/-- Integer casts uniquely determine a component pole from its real Poisson equation. -/
theorem component_pole_unique (u : C → ℝ) (f g : C → ℤ)
    (hf : ∀ x, -componentLaplacian C u x = (f x : ℝ))
    (hg : ∀ x, -componentLaplacian C u x = (g x : ℝ)) : f = g := by
  funext x
  exact Int.cast_injective ((hf x).symm.trans (hg x))

/-- A given integer pole of an ℓ¹-decaying real potential has finite component support. -/
theorem finite_support_component_pole_of_natAbs_decay (u : C → ℝ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : C, R < ∑ j, Int.natAbs (x.val j) → |u x| < ε)
    (f : C → ℤ) (hf : ∀ x, -componentLaplacian C u x = (f x : ℝ)) :
    Function.HasFiniteSupport f := by
  have ht := (Lattice.SubtypeCofinite.tendsto_zero_iff_natAbs_decay u).mpr hdecay
  apply Network.finite_support_pole_of_tendsto_zero (2 * d)
    (componentGraph_degree_le C) u ht f
  intro x
  rw [← componentLaplacian_eq_netLaplacian]
  exact hf x

/-- Integer-valued negative Laplacian yields the unique finitely supported component pole.
The potential is real-valued, and no exterior harmonicity is assumed. -/
theorem exists_unique_component_pole_of_natAbs_decay (u : C → ℝ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : C, R < ∑ j, Int.natAbs (x.val j) → |u x| < ε)
    (hinteger : ∀ x, ∃ z : ℤ, -componentLaplacian C u x = (z : ℝ)) :
    ∃! f : C → ℤ, Function.HasFiniteSupport f ∧
      ∀ x, -componentLaplacian C u x = (f x : ℝ) := by
  classical
  choose f hf using hinteger
  refine ⟨f, ⟨finite_support_component_pole_of_natAbs_decay C u hdecay f hf, hf⟩, ?_⟩
  intro g hg
  exact component_pole_unique C u g f hg.2 hf

/-- Inside Poisson equations and exterior zeros uniquely characterize the ambient pole. -/
theorem lattice_pole_unique (u : C → ℝ) (f g : Vertex d → ℤ)
    (hf : ∀ x : C, -componentLaplacian C u x = (f x.val : ℝ))
    (hg : ∀ x : C, -componentLaplacian C u x = (g x.val : ℝ))
    (hfzero : ∀ x ∉ C.supp, f x = 0) (hgzero : ∀ x ∉ C.supp, g x = 0) :
    f = g := by
  funext x
  by_cases hx : x ∈ C.supp
  · exact Int.cast_injective ((hf ⟨x, hx⟩).symm.trans (hg ⟨x, hx⟩))
  · exact (hfzero x hx).trans (hgzero x hx).symm

/-- Construct a finite integer pole and its finite zero extension from actual ℓ¹ decay.
The inside equation holds at every vertex of the genuine component subtype. -/
theorem exists_lattice_pole_of_natAbs_decay (u : C → ℝ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : C, R < ∑ j, Int.natAbs (x.val j) → |u x| < ε)
    (hinteger : ∀ x, ∃ z : ℤ, -componentLaplacian C u x = (z : ℝ)) :
    ∃ (f : C → ℤ) (g : Vertex d → ℤ),
      Function.HasFiniteSupport f ∧ Function.HasFiniteSupport g ∧
      (∀ x, -componentLaplacian C u x = (f x : ℝ)) ∧
      (∀ x : C, g x.val = f x) ∧
      (∀ x : C, -componentLaplacian C u x = (g x.val : ℝ)) ∧
      (∀ x ∉ C.supp, g x = 0) := by
  classical
  obtain ⟨f, ⟨hfinite, hf⟩, _⟩ := exists_unique_component_pole_of_natAbs_decay
    C u hdecay hinteger
  let g : Vertex d → ℤ := fun x => if hx : x ∈ C.supp then f ⟨x, hx⟩ else 0
  have hinside (x : C) : g x.val = f x := by
    dsimp only [g]
    rw [dif_pos (show x.val ∈ C.supp from x.property)]
  have houtside (x : Vertex d) (hx : x ∉ C.supp) : g x = 0 := by
    simp only [g, dif_neg hx]
  have hgfinite : Function.HasFiniteSupport g := by
    refine (hfinite.image (fun x : C => x.val)).subset ?_
    intro x hx
    by_cases hmem : x ∈ C.supp
    · refine ⟨⟨x, hmem⟩, ?_, rfl⟩
      simpa only [Function.mem_support, g, dif_pos hmem] using hx
    · exact False.elim (hx (houtside x hmem))
  refine ⟨f, g, hfinite, hgfinite, hf, hinside, ?_, houtside⟩
  intro x
  rw [hinside]
  exact hf x

/-- The ambient pole producer also accepts the literal real coordinate ℓ¹ norm. -/
theorem exists_lattice_pole_of_real_abs_decay (u : C → ℝ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ,
      ∀ x : C, (R : ℝ) < ∑ j, |(x.val j : ℝ)| → |u x| < ε)
    (hinteger : ∀ x, ∃ z : ℤ, -componentLaplacian C u x = (z : ℝ)) :
    ∃ (f : C → ℤ) (g : Vertex d → ℤ),
      Function.HasFiniteSupport f ∧ Function.HasFiniteSupport g ∧
      (∀ x, -componentLaplacian C u x = (f x : ℝ)) ∧
      (∀ x : C, g x.val = f x) ∧
      (∀ x : C, -componentLaplacian C u x = (g x.val : ℝ)) ∧
      (∀ x ∉ C.supp, g x = 0) := by
  have ht := (Lattice.SubtypeCofinite.tendsto_zero_iff_real_abs_decay u).mpr hdecay
  exact exists_lattice_pole_of_natAbs_decay C u
    ((Lattice.SubtypeCofinite.tendsto_zero_iff_natAbs_decay u).mp ht) hinteger

end LatticeProb.Percolation

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedGMS/Forms/AnchoredTraceMinimizer.lean.
-/
import LatticeProb.Network.AnchoredTraceMinimizer
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Energy minimizers with a prescribed anchor trace

Let `G` be a conductance graph on a vertex type `V`, let `A : Set V`, and let `u : V → ℝ` have
finite energy. The competition class is the set of finite-energy functions `h` with `h = u` on
`A`, and the energy `G.Energy` is minimized over it.

Assume `G.BoundaryAnchored A`, which says that every vertex is joined to a vertex of `A` by a walk.
The file proves:

* `exists_anchored_trace_minimizer`: the competition class contains a minimizer `f`. The
  function `f` also has zero Dirichlet form against every finite-energy function vanishing on `A`.
* `existsUnique_anchored_trace_minimizer`: the minimizer is unique. Any two finite-energy
  functions with trace `u` on `A` that minimize the energy over this class are equal.

The proofs project the normalized gradient of `u` onto the closed subspace of gradients of
finite-energy functions vanishing on `A`, which is `zeroTraceGradient` in
`Network/AnchoredTraceMinimizer.lean`. The graph may be disconnected, `A` may be infinite, and the
functions need not have finite support.

Two limits apply. `G.BoundaryAnchored A` fails when `A = ∅` and `V` is nonempty, so the results say
nothing in that case. The reference function `u` must have finite energy (`hu`), so infinite-energy
boundary data is not covered. The example section checks the path `0 – 1 – 2` with `A = {0}`.
-/

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-! ### Minimizers with a supplied boundary trace -/

/-- **Existence of the anchored trace minimizer.** Let `G.BoundaryAnchored A` hold, which fails when
`A = ∅` and `V` is nonempty, and let `u` have finite energy. Then there is a finite-energy function
`f` with `f = u` on `A` such that
`G.Energy f ≤ G.Energy h` for every finite-energy `h` with `h = u` on `A`. The same `f` has zero
Dirichlet form against every finite-energy function vanishing on `A`. Infinite-energy `u` is not
covered. -/
theorem exists_anchored_trace_minimizer {A : Set V} (hA : G.BoundaryAnchored A)
    {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    ∃ f : V → ℝ, G.HasFiniteEnergy f ∧ (∀ a ∈ A, f a = u a) ∧
      (∀ φ ∈ zeroTraceSubmodule G A, G.dirichletForm f φ = 0) ∧
      (∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
        G.Energy f ≤ G.Energy h) := by
  obtain ⟨w, hwK, hwmin⟩ :=
    (zeroTraceGradient G A).exists_norm_eq_iInf_of_complete_subspace
      (isComplete_zeroTraceGradient G hA) (weightedGradient G u hu)
  have horth : ∀ k ∈ zeroTraceGradient G A,
      inner ℝ (weightedGradient G u hu - w) k = 0 :=
    (Submodule.norm_eq_iInf_iff_real_inner_eq_zero _ hwK).1 hwmin
  obtain ⟨φ₀, hφ₀mem, hφ₀coord⟩ := hwK
  have hfE : G.HasFiniteEnergy (u - φ₀) := hu.sub hφ₀mem.1
  have hgrad : weightedGradient G (u - φ₀) hfE = weightedGradient G u hu - w := by
    refine (weightedGradient_eq_of_coord G hfE _ ?_).symm
    intro p
    rw [weightedGradientCoord_sub, ← hφ₀coord p, lp.coeFn_sub]
    rfl
  have hperp : ∀ φ ∈ zeroTraceSubmodule G A, G.dirichletForm (u - φ₀) φ = 0 := by
    intro φ hφ
    have h := horth _ (weightedGradient_mem_zeroTraceGradient G hφ)
    rwa [← hgrad, inner_weightedGradient] at h
  refine ⟨u - φ₀, hfE, ?_, hperp, ?_⟩
  · intro a ha
    simp only [Pi.sub_apply, hφ₀mem.2 a ha, sub_zero]
  · intro h hh htrace
    have hdiff : h - (u - φ₀) ∈ zeroTraceSubmodule G A := by
      refine ⟨hh.sub hfE, fun a ha => ?_⟩
      simp only [Pi.sub_apply, htrace a ha, hφ₀mem.2 a ha, sub_zero, sub_self]
    have hkey := energy_add_of_dirichletForm_zero G hfE hdiff.1 (hperp _ hdiff)
    have heq : (u - φ₀) + (h - (u - φ₀)) = h := by abel
    rw [heq] at hkey
    have hnn : 0 ≤ G.Energy (h - (u - φ₀)) := G.Energy_nonneg _
    linarith

/-- **Uniqueness of the anchored trace minimizer.** Let `G.BoundaryAnchored A` hold, which fails when
`A = ∅` and `V` is nonempty, and let `u` have finite energy. Then there is exactly one
finite-energy function `f` with `f = u` on `A` whose energy is at most the energy of every
finite-energy `h` with `h = u` on `A`. Infinite-energy `u` is not covered. -/
theorem existsUnique_anchored_trace_minimizer {A : Set V} (hA : G.BoundaryAnchored A)
    {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    ∃! f : V → ℝ, G.HasFiniteEnergy f ∧ (∀ a ∈ A, f a = u a) ∧
      ∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
        G.Energy f ≤ G.Energy h := by
  obtain ⟨f, hfE, hftrace, hforth, hfmin⟩ := exists_anchored_trace_minimizer G hA hu
  refine ⟨f, ⟨hfE, hftrace, hfmin⟩, ?_⟩
  rintro f' ⟨hf'E, hf'trace, hf'min⟩
  have hEeq : G.Energy f' = G.Energy f :=
    le_antisymm (hf'min f hfE hftrace) (hfmin f' hf'E hf'trace)
  have hdiff : f' - f ∈ zeroTraceSubmodule G A := by
    refine ⟨hf'E.sub hfE, fun a ha => ?_⟩
    simp only [Pi.sub_apply, hf'trace a ha, hftrace a ha, sub_self]
  have hkey := energy_add_of_dirichletForm_zero G hfE hdiff.1 (hforth _ hdiff)
  have heq : f + (f' - f) = f' := by abel
  rw [heq] at hkey
  have hE0 : G.Energy (f' - f) = 0 := by linarith
  exact eq_of_eqOn_energy_sub_zero G hA hf'E hfE
    (fun a ha => by rw [hf'trace a ha, hftrace a ha]) hE0

/-! ## Example

The path `0 – 1 – 2` with unit conductances, from `Network/Conductance.lean`, with anchor set
`{0}`. The reference function `x ↦ x` has finite energy, because the path has finitely many
ordered pairs of vertices. -/

namespace AnchoredMinimizer.Example

/-- The reference function `x ↦ x` on the path `0 – 1 – 2` has finite energy. -/
example : ConductanceGraph.Example.path3.HasFiniteEnergy (fun x : Fin 3 => ((x : ℕ) : ℝ)) :=
  Summable.of_finite

/-- On the path `0 – 1 – 2` with anchor set `{0}` and reference function `x ↦ x`, the anchored
trace minimizer exists. -/
example :=
  exists_anchored_trace_minimizer ConductanceGraph.Example.path3
    ConductanceGraph.Example.boundaryAnchored_path3 (u := fun x : Fin 3 => ((x : ℕ) : ℝ))
      Summable.of_finite

/-- On the path `0 – 1 – 2` with anchor set `{0}` and reference function `x ↦ x`, the anchored
trace minimizer is unique. -/
example :=
  existsUnique_anchored_trace_minimizer ConductanceGraph.Example.path3
    ConductanceGraph.Example.boundaryAnchored_path3 (u := fun x : Fin 3 => ((x : ℕ) : ℝ))
      Summable.of_finite

end AnchoredMinimizer.Example

end ConductanceGraph

end LatticeProb.Network

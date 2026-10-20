/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedGMS/Analysis/AnchoredEnergy.lean.
-/
import LatticeProb.Network.DirichletForm

/-!
# Finite-energy functions vanishing on an anchor set

Let `G` be a conductance graph on a vertex type `V`, and let `A : Set V`. The predicate
`G.BoundaryAnchored A` says that every vertex is joined to some vertex of `A` by a walk in
`G.toSimpleGraph`. It is not LP's `BoundaryAccessible` in `Network/Dirichlet.lean`, which says that
every vertex of `A` reaches the complement of `A`. The two properties differ, and the name
`BoundaryAnchored` is used only for the first one.

`G.BoundaryAnchored A` is false when `A = ∅` and `V` is nonempty. So the results below that assume
it say nothing in that case.

The file defines `G.zeroTraceSubmodule A`, the finite-energy functions vanishing on `A`, and
proves:

* `abs_apply_le_explicit_anchor_walk`: along a walk from a point of `A` where `f` vanishes on `A`,
  the increment of `f` is at most the walk constant times `√(2 · Energy f)`;
* `exists_vertex_energy_bound`: under `BoundaryAnchored`, each vertex evaluation is bounded on
  `zeroTraceSubmodule` by a constant times `√(2 · Energy f)`;
* `eq_zero_of_zeroTrace_energy_zero`: a zero-trace function of finite energy with zero energy is
  zero;
* `eq_of_eqOn_energy_sub_zero`: two finite-energy functions with the same trace on `A` and zero
  energy difference are equal.

The example section checks that the path `0 – 1 – 2` with `A = {0}` satisfies `BoundaryAnchored`,
and applies `eq_zero_of_zeroTrace_energy_zero` to it.
-/

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- Every vertex is joined to some vertex of `A` by a walk in `G.toSimpleGraph`. This is not the
property `BoundaryAccessible` of `Network/Dirichlet.lean`, which asks that every vertex of `A`
reach the complement of `A`. -/
def BoundaryAnchored (A : Set V) : Prop :=
  ∀ v, ∃ a ∈ A, G.toSimpleGraph.Reachable v a

/-- The finite-energy functions vanishing on the whole set `A`, as a submodule of `V → ℝ`. -/
def zeroTraceSubmodule (A : Set V) : Submodule ℝ (V → ℝ) where
  carrier := {f | G.HasFiniteEnergy f ∧ ∀ a ∈ A, f a = 0}
  zero_mem' := ⟨G.hasFiniteEnergy_zero, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    refine ⟨hf.add hg, ?_⟩
    intro a ha
    simp only [Pi.add_apply, hfA a ha, hgA a ha, add_zero]
  smul_mem' := by
    rintro r f ⟨hf, hfA⟩
    refine ⟨hf.smul r, ?_⟩
    intro a ha
    simp only [Pi.smul_apply, smul_eq_mul, hfA a ha, mul_zero]

/-- Membership in `zeroTraceSubmodule`: finite energy and vanishing on `A`. -/
@[simp] theorem mem_zeroTraceSubmodule {A : Set V} {f : V → ℝ} :
    f ∈ G.zeroTraceSubmodule A ↔ G.HasFiniteEnergy f ∧ ∀ a ∈ A, f a = 0 := Iff.rfl

/-- If `f` has finite energy and vanishes on `A`, then along any walk from a point `a ∈ A` to `x`,
`|f x|` is at most the walk constant times `√(2 · Energy f)`. -/
theorem abs_apply_le_explicit_anchor_walk {A : Set V} {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) {a x : V} (ha : a ∈ A)
    (hzero : ∀ b ∈ A, f b = 0) (w : G.toSimpleGraph.Walk a x) :
    |f x| ≤ G.walkConst w * Real.sqrt (2 * G.Energy f) := by
  have hb := G.abs_sub_le_walkConst_mul hf w
  simpa only [hzero a ha, sub_zero] using hb

/-- Under `BoundaryAnchored G A`, each vertex evaluation is bounded on the zero-trace
finite-energy functions by a constant times `√(2 · Energy f)`. The constant may depend on the
vertex. -/
theorem exists_vertex_energy_bound {A : Set V} (hA : G.BoundaryAnchored A) (x : V) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : V → ℝ, f ∈ G.zeroTraceSubmodule A →
        |f x| ≤ C * Real.sqrt (2 * G.Energy f) := by
  obtain ⟨a, ha, hxa⟩ := hA x
  obtain ⟨w⟩ := hxa.symm
  refine ⟨G.walkConst w, G.walkConst_nonneg w, ?_⟩
  intro f hf
  exact abs_apply_le_explicit_anchor_walk G hf.1 ha hf.2 w

/-- Under `BoundaryAnchored G A`, a finite-energy function vanishing on `A` with zero energy is
identically zero. -/
theorem eq_zero_of_zeroTrace_energy_zero {A : Set V}
    (hA : G.BoundaryAnchored A) {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hzero : ∀ a ∈ A, f a = 0) (hE : G.Energy f = 0) : f = 0 := by
  funext x
  obtain ⟨C, _, hC⟩ := exists_vertex_energy_bound G hA x
  have hb := hC f ⟨hf, hzero⟩
  have hfx : |f x| ≤ 0 := by
    simpa only [hE, mul_zero, Real.sqrt_zero] using hb
  exact abs_nonpos_iff.mp hfx

/-- Under `BoundaryAnchored G A`, two finite-energy functions that agree on `A` and have zero
energy difference are equal. -/
theorem eq_of_eqOn_energy_sub_zero {A : Set V}
    (hA : G.BoundaryAnchored A) {f g : V → ℝ}
    (hf : G.HasFiniteEnergy f) (hg : G.HasFiniteEnergy g)
    (htrace : Set.EqOn f g A) (hE : G.Energy (f - g) = 0) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_zeroTrace_energy_zero G hA (hf.sub hg) _ hE
  intro a ha
  simp only [Pi.sub_apply, htrace ha, sub_self]

/-! ## Examples

The path `0 – 1 – 2` with unit conductances, from `Network/Conductance.lean`, with anchor set
`{0}`. -/

namespace Example

/-- In the path `0 – 1 – 2`, every vertex is joined to `0` by a walk, so `{0}` anchors it. -/
theorem boundaryAnchored_path3 : ConductanceGraph.Example.path3.BoundaryAnchored {0} := by
  intro v
  refine ⟨0, rfl, ?_⟩
  have h10 : ConductanceGraph.Example.path3.toSimpleGraph.Adj 1 0 := by
    norm_num [ConductanceGraph.toSimpleGraph_adj, ConductanceGraph.Example.path3]
  have h21 : ConductanceGraph.Example.path3.toSimpleGraph.Adj 2 1 := by
    norm_num [ConductanceGraph.toSimpleGraph_adj, ConductanceGraph.Example.path3]
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact h10.reachable
  · exact h21.reachable.trans h10.reachable

/-- On the path `0 – 1 – 2` with anchor set `{0}`, the hypotheses of
`eq_zero_of_zeroTrace_energy_zero` hold for the zero function, which gives an instance of its
conclusion. -/
example : (fun _ : Fin 3 => (0 : ℝ)) = 0 :=
  eq_zero_of_zeroTrace_energy_zero ConductanceGraph.Example.path3 boundaryAnchored_path3
    (ConductanceGraph.Example.path3.hasFiniteEnergy_const 0) (fun _ _ => rfl)
    (ConductanceGraph.Example.path3.Energy_const 0)

end Example

end ConductanceGraph

end LatticeProb.Network

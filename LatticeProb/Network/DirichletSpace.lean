/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedWalk/DirichletSpace.lean.
-/
import LatticeProb.Network.DirichletForm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FinCases

/-!
# The Dirichlet space of a connected conductance graph

Let `G` be a conductance graph on `V` whose underlying simple graph is connected, and let `a₀ : V`.
The Dirichlet space `D₀` is the set of finite-energy functions `f : V → ℝ` with `f a₀ = 0`, with the
Dirichlet form `G.dirichletForm` as its inner product. This file proves that `D₀` is a real inner
product space whose norm is the square root of the Dirichlet energy, and it gives a nonzero element
of `D₀` on the path `0 – 1 – 2`.

* `ConductanceGraph.DirichletSpace` is the space, as a subtype of `V → ℝ`, with its additive group,
  module and function-like structures.
* `ConductanceGraph.DirichletSpace.instInnerProductSpaceCore` is the inner product. It is definite
  because the graph is connected: a finite-energy function vanishing at `a₀` with zero energy is
  zero.
* `norm_eq_sqrt_energy` and `norm_sq_eq_energy` express the norm through the energy.
* `ConductanceGraph.DirichletSpace.Example` shows that the connectedness and base-point hypotheses
  are satisfiable with a nonzero element.
-/

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- The Dirichlet space `D₀ = {f : V → ℝ | HasFiniteEnergy f ∧ f a₀ = 0}` of a conductance graph
`G` whose underlying simple graph is connected, based at `a₀`. Its inner product is the Dirichlet
form `G.dirichletForm` (`instInnerProductSpaceCore`), which is definite because the graph is
connected.

This is a `def`, not an `abbrev`, so that `D₀` does not inherit the product topology of `V → ℝ`;
its topology is the one induced by the energy norm defined below. The connectedness hypothesis is
part of the type: it is not needed for the carrier, but it is what makes the inner product
definite. -/
def DirichletSpace (_hG : G.toSimpleGraph.Connected) (a₀ : V) := ↥(G.dirichletSubmodule a₀)

namespace DirichletSpace

variable {G} {hG : G.toSimpleGraph.Connected} {a₀ : V}

/-- The additive group structure of `D₀`, inherited from `dirichletSubmodule`. -/
instance : AddCommGroup (G.DirichletSpace hG a₀) :=
  inferInstanceAs (AddCommGroup (G.dirichletSubmodule a₀))

/-- The real vector space structure of `D₀`, inherited from `dirichletSubmodule`. -/
instance : Module ℝ (G.DirichletSpace hG a₀) :=
  inferInstanceAs (Module ℝ (G.dirichletSubmodule a₀))

/-- An element of `D₀` is evaluated as the function it wraps. -/
instance : FunLike (G.DirichletSpace hG a₀) V ℝ where
  coe f := Subtype.val f
  coe_injective := Subtype.val_injective

/-- The element of `D₀` given by a finite-energy function `f` with `f a₀ = 0`. -/
def mk (f : V → ℝ) (hf : G.HasFiniteEnergy f) (h0 : f a₀ = 0) : G.DirichletSpace hG a₀ :=
  ⟨f, hf, h0⟩

/-- The function underlying `mk f hf h0` is `f`. -/
@[simp] lemma coe_mk (f : V → ℝ) (hf : G.HasFiniteEnergy f) (h0 : f a₀ = 0) :
    ⇑(mk f hf h0 : G.DirichletSpace hG a₀) = f := rfl

/-- Two elements of `D₀` are equal when they agree at every vertex. -/
@[ext] lemma ext {f g : G.DirichletSpace hG a₀} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Every element of `D₀` has finite energy. -/
lemma hasFiniteEnergy (f : G.DirichletSpace hG a₀) : G.HasFiniteEnergy f :=
  (Subtype.prop f).1

/-- Every element of `D₀` vanishes at `a₀`. -/
lemma apply_base (f : G.DirichletSpace hG a₀) : f a₀ = 0 := (Subtype.prop f).2

/-- Addition in `D₀` is pointwise. -/
@[simp] lemma coe_add (f g : G.DirichletSpace hG a₀) : ⇑(f + g) = ⇑f + ⇑g := rfl

/-- Subtraction in `D₀` is pointwise. -/
@[simp] lemma coe_sub (f g : G.DirichletSpace hG a₀) : ⇑(f - g) = ⇑f - ⇑g := rfl

/-- Negation in `D₀` is pointwise. -/
@[simp] lemma coe_neg (f : G.DirichletSpace hG a₀) : ⇑(-f) = -⇑f := rfl

/-- Scalar multiplication in `D₀` is pointwise. -/
@[simp] lemma coe_smul (a : ℝ) (f : G.DirichletSpace hG a₀) : ⇑(a • f) = a • ⇑f := rfl

/-- The zero element of `D₀` is the zero function. -/
@[simp] lemma coe_zero : ⇑(0 : G.DirichletSpace hG a₀) = 0 := rfl

/-- The value of a sum in `D₀` at a vertex is the sum of the values. -/
lemma add_apply (f g : G.DirichletSpace hG a₀) (x : V) : (f + g) x = f x + g x := rfl

/-- The value of a difference in `D₀` at a vertex is the difference of the values. -/
lemma sub_apply (f g : G.DirichletSpace hG a₀) (x : V) : (f - g) x = f x - g x := rfl

/-- The value of a negation in `D₀` at a vertex is the negated value. -/
lemma neg_apply (f : G.DirichletSpace hG a₀) (x : V) : (-f) x = -f x := rfl

/-- The value of a scalar multiple in `D₀` at a vertex is the scalar times the value. -/
lemma smul_apply (a : ℝ) (f : G.DirichletSpace hG a₀) (x : V) : (a • f) x = a * f x := rfl

/-- The value of the zero element of `D₀` at a vertex is `0`. -/
lemma zero_apply (x : V) : (0 : G.DirichletSpace hG a₀) x = 0 := rfl

/-- The Dirichlet form is a genuine inner product on `D₀`. Symmetry, additivity, homogeneity and
nonnegativity come from the corresponding properties of `dirichletForm`. Definiteness uses
connectedness: a walk from `a₀` to `x` controls `|f x - f a₀|` by a constant times the square root
of the energy, so zero energy forces `f x = f a₀ = 0`. -/
noncomputable instance instInnerProductSpaceCore :
    InnerProductSpace.Core ℝ (G.DirichletSpace hG a₀) where
  inner f g := G.dirichletForm f g
  conj_inner_symm f g := by
    simp only [RCLike.conj_to_real]
    exact G.dirichletForm_comm g f
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    rw [G.dirichletForm_self]
    exact G.Energy_nonneg _
  add_left f g k :=
    G.dirichletForm_add_left f.hasFiniteEnergy g.hasFiniteEnergy k.hasFiniteEnergy
  smul_left f g r := by
    simp only [RCLike.conj_to_real]
    exact G.dirichletForm_smul_left r f g
  definite f h := by
    have hE : G.Energy f = 0 := by rw [← G.dirichletForm_self]; exact h
    ext x
    have hb := G.abs_sub_le_walkConst_mul f.hasFiniteEnergy (hG.preconnected a₀ x).some
    rw [hE, mul_zero, Real.sqrt_zero, mul_zero, f.apply_base, sub_zero] at hb
    rw [zero_apply]
    exact abs_nonpos_iff.mp hb

/-- The norm on `D₀` is induced by the inner product `G.dirichletForm`. -/
noncomputable instance : NormedAddCommGroup (G.DirichletSpace hG a₀) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

/-- `D₀` is a real inner product space for the Dirichlet form. -/
noncomputable instance : InnerProductSpace ℝ (G.DirichletSpace hG a₀) :=
  InnerProductSpace.ofCore _

/-- The inner product of two elements of `D₀` is the Dirichlet form of the underlying functions. -/
lemma inner_def (f g : G.DirichletSpace hG a₀) : inner ℝ f g = G.dirichletForm f g := rfl

/-- The norm of `D₀` is the square root of the Dirichlet energy. -/
lemma norm_eq_sqrt_energy (f : G.DirichletSpace hG a₀) : ‖f‖ = Real.sqrt (G.Energy f) := by
  rw [norm_eq_sqrt_real_inner, inner_def, G.dirichletForm_self]

/-- The squared norm of an element of `D₀` is its Dirichlet energy. -/
lemma norm_sq_eq_energy (f : G.DirichletSpace hG a₀) : ‖f‖ ^ 2 = G.Energy f := by
  rw [norm_eq_sqrt_energy, Real.sq_sqrt (G.Energy_nonneg _)]

end DirichletSpace

end ConductanceGraph

/-! ## Nonvacuity: the path `0 – 1 – 2`

On the path `0 – 1 – 2` (`ConductanceGraph.Example.path3`) the graph is connected, and the function
`x ↦ x` is a nonzero element of the Dirichlet space based at `0`. -/

namespace ConductanceGraph.DirichletSpace.Example

/-- The path `0 – 1 – 2` is connected: every vertex is reachable from `1`. -/
lemma path3_connected : ConductanceGraph.Example.path3.toSimpleGraph.Connected := by
  have h1 : ∀ v : Fin 3, ConductanceGraph.Example.path3.toSimpleGraph.Reachable 1 v := by
    intro v
    fin_cases v
    · exact (show ConductanceGraph.Example.path3.toSimpleGraph.Adj 1 0 by
        norm_num [ConductanceGraph.toSimpleGraph_adj, ConductanceGraph.Example.path3]).reachable
    · exact SimpleGraph.Reachable.refl _
    · exact (show ConductanceGraph.Example.path3.toSimpleGraph.Adj 1 2 by
        norm_num [ConductanceGraph.toSimpleGraph_adj, ConductanceGraph.Example.path3]).reachable
  exact ⟨fun u v => (h1 u).symm.trans (h1 v)⟩

/-- The function `x ↦ x` on `path3`, as an element of the Dirichlet space based at `0`. Its
energy is finite because the vertex set is finite. -/
noncomputable def ramp :
    ConductanceGraph.Example.path3.DirichletSpace path3_connected 0 :=
  ConductanceGraph.DirichletSpace.mk (fun x => ((x : ℕ) : ℝ)) Summable.of_finite (by simp)

/-- `ramp` is nonzero: its value at the vertex `1` is `1`. -/
example : ramp ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : ConductanceGraph.Example.path3.DirichletSpace path3_connected 0 =>
    f 1) h
  simp [ramp] at h1

end ConductanceGraph.DirichletSpace.Example

end LatticeProb.Network

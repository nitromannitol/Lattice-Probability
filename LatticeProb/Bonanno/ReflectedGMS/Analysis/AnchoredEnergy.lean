/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Analysis.AnchoredEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.DirichletSpace

/-!
# Finite-energy variations anchored on an arbitrary boundary

The graph may be disconnected and the boundary may be infinite. Every vertex must be
joined to some boundary vertex by a finite graph walk. The variation space contains all
finite-energy zero-boundary functions; no finite-support closure is taken.

This module supplies the algebraic variation space, finite-path evaluation control, and
the definiteness argument needed by the subsequent global Hilbert-space construction.
-/

set_option autoImplicit false

namespace ReflectedGMS

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- Every vertex reaches a prescribed boundary vertex by a finite graph walk. -/
def BoundaryAnchored (A : Set V) : Prop :=
  ∀ v, ∃ a ∈ A, G.toSimpleGraph.Reachable v a

/-- All finite-energy functions vanishing on the entire prescribed boundary. -/
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

@[simp] theorem mem_zeroTraceSubmodule {A : Set V} {f : V → ℝ} :
    f ∈ zeroTraceSubmodule G A ↔
      G.HasFiniteEnergy f ∧ ∀ a ∈ A, f a = 0 := Iff.rfl

/-- The inherited explicit-walk bound applies at any boundary anchor. -/
theorem abs_apply_le_explicit_anchor_walk {A : Set V} {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) {a x : V} (ha : a ∈ A)
    (hzero : ∀ b ∈ A, f b = 0) (w : G.toSimpleGraph.Walk a x) :
    |f x| ≤ G.walkConst w * Real.sqrt (2 * G.Energy f) := by
  have hb := G.abs_sub_le_walkConst_mul hf w
  simpa only [hzero a ha, sub_zero] using hb

/-- Each vertex evaluation admits a finite energy bound, with a constant that may depend
on the vertex. This quantifies over the full zero-trace finite-energy space. -/
theorem exists_vertex_energy_bound {A : Set V} (hA : BoundaryAnchored G A) (x : V) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : V → ℝ, f ∈ zeroTraceSubmodule G A →
        |f x| ≤ C * Real.sqrt (2 * G.Energy f) := by
  obtain ⟨a, ha, hxa⟩ := hA x
  obtain ⟨w⟩ := hxa.symm
  refine ⟨G.walkConst w, G.walkConst_nonneg w, ?_⟩
  intro f hf
  exact abs_apply_le_explicit_anchor_walk G hf.1 ha hf.2 w

/-- Zero total energy has no nonzero zero-trace representative on an anchored graph. -/
theorem eq_zero_of_zeroTrace_energy_zero {A : Set V}
    (hA : BoundaryAnchored G A) {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hzero : ∀ a ∈ A, f a = 0) (hE : G.Energy f = 0) : f = 0 := by
  funext x
  obtain ⟨C, _, hC⟩ := exists_vertex_energy_bound G hA x
  have hb := hC f ⟨hf, hzero⟩
  have hfx : |f x| ≤ 0 := by
    simpa only [hE, mul_zero, Real.sqrt_zero] using hb
  exact abs_nonpos_iff.mp hfx

/-- Equality follows from equal boundary trace and zero energy of the difference. -/
theorem eq_of_eqOn_energy_sub_zero {A : Set V}
    (hA : BoundaryAnchored G A) {f g : V → ℝ}
    (hf : G.HasFiniteEnergy f) (hg : G.HasFiniteEnergy g)
    (htrace : Set.EqOn f g A) (hE : G.Energy (f - g) = 0) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_zeroTrace_energy_zero G hA (hf.sub hg) _ hE
  intro a ha
  simp only [Pi.sub_apply, htrace ha, sub_self]

end ReflectedGMS

import LatticeProb.Prob.Percolation.MeasurableRootedPlane
import LatticeProb.Prob.Percolation.CorrectedPlaneLinearMap
import Mathlib.LinearAlgebra.Pi

/-!
# Algebra and basepoint changes for the actual encoded plane

The full rooted graph characterization makes the ambient encoding linear in its slope.
On the actual root component it agrees with every source plane after subtracting its
root value. The difference identity is asserted only on that component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- Every fully characterized rooted encoded family is a real linear map, including its
outside-zero coordinates. Existence and uniqueness come from the actual validity event. -/
theorem rooted_encoded_plane_linearMap
    (hvalid : ω ∈ correctorValidEvent d) (o : Vertex d)
    (ho : ω ∈ infiniteComponentEvent o) (F : (Fin d → ℝ) → Vertex d → ℝ)
    (hF : ∀ q, F q o = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => F q x.val) ∧
      ∀ x, ¬ (openGraph ω).Reachable o x → F q x = 0) :
    ∃ L : (Fin d → ℝ) →ₗ[ℝ] (Vertex d → ℝ), ∀ q, L q = F q := by
  have huniq := fun q =>
    existsUnique_rooted_encoded_correctedPlane ω o q
      (existsUnique_rooted_plane_of_valid hvalid o ho q)
  have heq : ∀ q U, (U o = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => U x.val) ∧
      ∀ x, ¬ (openGraph ω).Reachable o x → U x = 0) → U = F q := by
    intro q U hU
    exact (huniq q).unique hU (hF q)
  refine ⟨{ toFun := F, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro p q
    apply (heq (p + q) (F p + F q) ?_).symm
    refine ⟨?_, isCorrectedPlane_add _ (hF p).2.1 (hF q).2.1, ?_⟩
    · simp only [Pi.add_apply, (hF p).1, (hF q).1, add_zero]
    · intro x hx
      simp only [Pi.add_apply, (hF p).2.2 x hx, (hF q).2.2 x hx, add_zero]
  · intro r q
    apply (heq (r • q) (r • F q) ?_).symm
    refine ⟨?_, isCorrectedPlane_smul _ (hF q).2.1 r, ?_⟩
    · simp only [Pi.smul_apply, (hF q).1, smul_zero]
    · intro x hx
      simp only [Pi.smul_apply, (hF q).2.2 x hx, smul_zero]

/-- Every ambient coordinate of a fully characterized family has its exact finite basis
expansion, with coefficient given by the normalized coordinate plane. -/
theorem rooted_encoded_plane_basis_expansion
    (hvalid : ω ∈ correctorValidEvent d) (o : Vertex d)
    (ho : ω ∈ infiniteComponentEvent o) (F : (Fin d → ℝ) → Vertex d → ℝ)
    (hF : ∀ q, F q o = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => F q x.val) ∧
      ∀ x, ¬ (openGraph ω).Reachable o x → F q x = 0)
    (q : Fin d → ℝ) (y : Vertex d) :
    F q y = ∑ j, q j * F (Pi.single j 1) y := by
  classical
  obtain ⟨L, hL⟩ := rooted_encoded_plane_linearMap hvalid o ho F hF
  have hsum : q = ∑ j, q j • Pi.single j (1 : ℝ) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc
    F q y = L q y := congrFun (hL q).symm y
    _ = L (∑ j, q j • Pi.single j (1 : ℝ)) y := congrArg (fun v => L v y) hsum
    _ = ∑ j, q j * F (Pi.single j 1) y := by
      rw [map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [hL]

/-- Normalizing any actual source plane at the root gives the characterized encoded
plane on component vertices; no difference formula is asserted outside the component. -/
theorem rooted_encoded_plane_eq_sub
    (hvalid : ω ∈ correctorValidEvent d) (o : Vertex d)
    (ho : ω ∈ infiniteComponentEvent o) (q : Fin d → ℝ) (U : Vertex d → ℝ)
    (hU : U o = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => U x.val))
    (u : (openGraph ω).connectedComponentMk o → ℝ)
    (hu : IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q u)
    (y : (openGraph ω).connectedComponentMk o) :
    U y.val = u y - u ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ := by
  let C := (openGraph ω).connectedComponentMk o
  let x : C := ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hsub : IsCorrectedPlane C q (u - fun _ => u x) := by
    simpa only [sub_zero] using isCorrectedPlane_sub C hu (isCorrectedPlane_const C (u x))
  have hnorm : (u - (fun _ : C => u x)) x = 0 := sub_self _
  have heq := (existsUnique_rooted_plane_of_valid hvalid o ho q).unique ⟨hU.2, hU.1⟩ ⟨hsub, hnorm⟩
  exact congrFun heq y

/-- On the unique infinite component, each rooted encoding agrees with every source
plane after subtracting its value at that component root. -/
theorem rooted_encoded_plane_uniqueComponent_eq_sub
    (hvalid : ω ∈ correctorValidEvent d)
    (x y : uniqueInfiniteComponent hvalid.1) (q : Fin d → ℝ) (U : Vertex d → ℝ)
    (hU : U x.val = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk x.val) q
        (fun z => U z.val))
    (u : uniqueInfiniteComponent hvalid.1 → ℝ)
    (hu : IsCorrectedPlane (uniqueInfiniteComponent hvalid.1) q u) :
    U y.val = u y - u x := by
  let C := uniqueInfiniteComponent hvalid.1
  have hinf := (mem_uniqueInfiniteComponent_iff hvalid.1 x.val).mp x.property
  have hC := (eq_uniqueInfiniteComponent_iff hvalid.1
    ((openGraph ω).connectedComponentMk x.val)).mpr hinf
  have hplane : IsCorrectedPlane C q (fun z => U z.val) := by
    have h := hU.2
    rwa [hC] at h
  have hsub : IsCorrectedPlane C q (u - fun _ => u x) := by
    simpa only [sub_zero] using isCorrectedPlane_sub C hu (isCorrectedPlane_const C (u x))
  have heq := ((hvalid.2 hvalid.1).1 q x).unique ⟨hplane, hU.1⟩
    ⟨hsub, show (u - (fun _ : C => u x)) x = 0 from sub_self _⟩
  exact congrFun heq y

/-- Full graph characterization determines the family pointwise, independently of any
measurable selection used to construct it. -/
theorem rooted_encoded_plane_family_unique
    (hvalid : ω ∈ correctorValidEvent d) (o : Vertex d)
    (ho : ω ∈ infiniteComponentEvent o) (F H : (Fin d → ℝ) → Vertex d → ℝ)
    (hF : ∀ q, F q o = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => F q x.val) ∧
      ∀ x, ¬ (openGraph ω).Reachable o x → F q x = 0)
    (hH : ∀ q, H q o = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => H q x.val) ∧
      ∀ x, ¬ (openGraph ω).Reachable o x → H q x = 0) : F = H := by
  funext q
  exact (existsUnique_rooted_encoded_correctedPlane ω o q
    (existsUnique_rooted_plane_of_valid hvalid o ho q)).unique (hF q) (hH q)

end

end LatticeProb.Percolation

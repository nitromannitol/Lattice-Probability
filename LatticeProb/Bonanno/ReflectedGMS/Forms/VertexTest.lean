/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexTest at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullNetworkForm
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients
import LatticeProb.Bonanno.ReflectedWalk.Harmonic
import LatticeProb.Bonanno.ReflectedWalk.HarmonicMeasure

/-!
# Vertex tests for the full network form

We reuse ReflectedWalk's `ConductanceGraph.indic` as the delta function at a
vertex.  It belongs to both parts of the full form domain, and testing the
half-ordered-edge Dirichlet form against it gives the negative conductance
Laplacian with the exact existing sign and factor convention.

This is a form--generator identity at ordinary vertices.  It does not identify
the generator of a reflected process at spatial infinity or exclude an
additional boundary drift or bracket term.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace ReflectedGMS.VertexTest

variable {V : Type*}

/-- A vertex indicator has finite full network energy. -/
theorem indic_hasFiniteEnergy (G : ReflectedWalk.ConductanceGraph V) (v : V) :
    G.HasFiniteEnergy (G.indic v) := by
  apply G.hasFiniteEnergy_of_support_subset {v}
  intro u hu
  simp only [Finset.mem_singleton] at hu
  simp [ReflectedWalk.ConductanceGraph.indic, hu]

/-- A vertex indicator is square summable for every real atomic speed. -/
theorem indic_hasSpeedL2 (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (v : V) :
    FullNetworkForm.HasSpeedL2 m (G.indic v) := by
  unfold FullNetworkForm.HasSpeedL2
  apply (memℓp_zero ?_).of_exponent_ge (by norm_num)
  refine Set.Finite.subset (Set.finite_singleton v) ?_
  intro u hu
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hu ⊢
  by_contra huv
  apply hu
  simp [ReflectedWalk.ConductanceGraph.indic, huv]

/-- Integration by parts against a vertex delta.  The factor `1 / 2` in
`dirichletForm` cancels the two orientations of every incident edge. -/
theorem dirichletForm_indic_eq_neg_laplacian
    (G : ReflectedWalk.ConductanceGraph V) (f : V → ℝ)
    (hf : G.HasFiniteEnergy f) (v : V) :
    G.dirichletForm f (G.indic v) = -∑' w : V, G.lapTerm f v w := by
  classical
  have hlap : Summable (G.lapTerm f v) :=
    Summable.of_abs ((G.absSummableAt_iff f v).1
      (G.absSummableAt_of_hasFiniteEnergy hf v))
  have hneg : HasSum (fun w : V ↦ -G.lapTerm f v w)
      (-(∑' w : V, G.lapTerm f v w)) := hlap.hasSum.neg
  have hfirst : HasSum
      (fun p : V × V ↦ if p.1 = v then -G.lapTerm f v p.2 else 0)
      (-(∑' w : V, G.lapTerm f v w)) := by
    refine ((Prod.mk_right_injective v).hasSum_iff ?_).1 ?_
    · rintro ⟨x, y⟩ hp
      simp only [Set.mem_range, Prod.mk.injEq, not_exists] at hp
      exact ite_eq_right fun hxv ↦ hp y ⟨hxv.symm, rfl⟩
    · simpa [Function.comp_def] using hneg
  have hsecond : HasSum
      (fun p : V × V ↦ if p.2 = v then -G.lapTerm f v p.1 else 0)
      (-(∑' w : V, G.lapTerm f v w)) := by
    refine ((Prod.mk_left_injective v).hasSum_iff ?_).1 ?_
    · rintro ⟨x, y⟩ hp
      simp only [Set.mem_range, Prod.mk.injEq, not_exists] at hp
      exact ite_eq_right fun hyv ↦ hp x ⟨rfl, hyv.symm⟩
    · simpa [Function.comp_def] using hneg
  have hpoint : ∀ p : V × V,
      G.gradProd f (G.indic v) p =
        (if p.1 = v then -G.lapTerm f v p.2 else 0) +
        (if p.2 = v then -G.lapTerm f v p.1 else 0) := by
    rintro ⟨x, y⟩
    simp only [ReflectedWalk.ConductanceGraph.gradProd,
      ReflectedWalk.ConductanceGraph.lapTerm,
      ReflectedWalk.ConductanceGraph.indic]
    by_cases hx : x = v <;> by_cases hy : y = v
    · simp [hx, hy, G.c_self]
    · simp [hx, hy]
      ring
    · simp [hx, hy, G.c_symm]
      ring
    · simp [hx, hy]
  have htotal : HasSum (G.gradProd f (G.indic v))
      (-(∑' w : V, G.lapTerm f v w) +
        -(∑' w : V, G.lapTerm f v w)) := by
    rw [funext hpoint]
    exact hfirst.add hsecond
  unfold ReflectedWalk.ConductanceGraph.dirichletForm
  rw [htotal.tsum_eq]
  ring

end ReflectedGMS.VertexTest

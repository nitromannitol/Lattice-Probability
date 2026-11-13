/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyCarreDuChamp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexCarreDuChamp
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedEnergyAlgebra

/-!
# The full-energy carré du champ product identity

This file proves the weak square/product identity on the bounded full
finite-energy domain.  The factor is fixed by the existing convention that
`dirichletForm` is half the ordered-edge sum, whereas the speed-weighted
vertex carré du champ is an ordered row sum.

This is an analytic identity only.  It makes no stochastic bracket or
compactification-boundary assertion.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ReflectedGMS

variable {V : Type*}

private theorem summable_gradSq_mul_endpoint
    (G : ReflectedWalk.ConductanceGraph V) {u v : V → ℝ} {B : ℝ}
    (hu : G.HasFiniteEnergy u) (hv : ∀ x, |v x| ≤ B) (i : V × V → V) :
    Summable (fun p : V × V ↦ G.gradSq u p * v (i p)) := by
  apply Summable.of_norm_bounded (hu.mul_left B)
  intro p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (G.gradSq_nonneg u p)]
  calc
    G.gradSq u p * |v (i p)| ≤ G.gradSq u p * B :=
      mul_le_mul_of_nonneg_left (hv (i p)) (G.gradSq_nonneg u p)
    _ = B * G.gradSq u p := mul_comm _ _

private theorem tsum_gradSq_mul_snd_eq_fst
    (G : ReflectedWalk.ConductanceGraph V) (u v : V → ℝ) :
    (∑' p : V × V, G.gradSq u p * v p.2) =
      ∑' p : V × V, G.gradSq u p * v p.1 := by
  rw [← (Equiv.prodComm V V).tsum_eq
    (fun p : V × V ↦ G.gradSq u p * v p.1)]
  apply tsum_congr
  rintro ⟨x, y⟩
  simp only [Equiv.prodComm_apply, Prod.swap]
  unfold ReflectedWalk.ConductanceGraph.gradSq
  rw [G.c_symm]
  ring

/-- Ordered-edge form of the full-energy weak square/product identity. -/
theorem fullEnergy_carreDuChamp_edge_identity
    (G : ReflectedWalk.ConductanceGraph V) {u v : V → ℝ} {A B : ℝ}
    (huBound : ∀ x, |u x| ≤ A) (hvBound : ∀ x, |v x| ≤ B)
    (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    G.dirichletForm (u ^ 2) v =
      2 * G.dirichletForm u (u * v) -
        ∑' p : V × V, G.gradSq u p * v p.1 := by
  have huu : G.HasFiniteEnergy (u ^ 2) := by
    simpa only [pow_two] using
      FullNetworkForm.hasFiniteEnergy_mul_of_bounded G huBound huBound hu hu
  have huv : G.HasFiniteEnergy (u * v) :=
    FullNetworkForm.hasFiniteEnergy_mul_of_bounded G huBound hvBound hu hv
  have hprod := G.summable_gradProd hu huv
  have hfst : Summable (fun p : V × V ↦ G.gradSq u p * v p.1) :=
    summable_gradSq_mul_endpoint G hu hvBound Prod.fst
  have hsnd : Summable (fun p : V × V ↦ G.gradSq u p * v p.2) :=
    summable_gradSq_mul_endpoint G hu hvBound Prod.snd
  unfold ReflectedWalk.ConductanceGraph.dirichletForm
  rw [show (∑' p : V × V, G.gradProd (u ^ 2) v p) =
      ∑' p : V × V, (2 * G.gradProd u (u * v) p -
        G.gradSq u p * v p.1 - G.gradSq u p * v p.2) by
        apply tsum_congr
        intro p
        simp only [ReflectedWalk.ConductanceGraph.gradProd,
          ReflectedWalk.ConductanceGraph.gradSq, Pi.pow_apply, Pi.mul_apply]
        ring]
  rw [((hprod.mul_left 2).sub hfst).tsum_sub hsnd,
    (hprod.mul_left 2).tsum_sub hfst, hprod.tsum_mul_left,
    tsum_gradSq_mul_snd_eq_fst G u v]
  ring

/-- The speed-measure pairing of the vertex carré du champ is the ordered
edge pairing used in `fullEnergy_carreDuChamp_edge_identity`. -/
theorem tsum_speed_mul_vertexCarreDuChamp_mul
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) {u v : V → ℝ} {B : ℝ}
    (hvBound : ∀ x, |v x| ≤ B) (hu : G.HasFiniteEnergy u) :
    (∑' x : V, m x * vertexCarreDuChamp G m u x * v x) =
      ∑' p : V × V, G.gradSq u p * v p.1 := by
  have hedge : Summable (fun p : V × V ↦ G.gradSq u p * v p.1) :=
    summable_gradSq_mul_endpoint G hu hvBound Prod.fst
  calc
    (∑' x : V, m x * vertexCarreDuChamp G m u x * v x) =
        ∑' x : V, (∑' y : V, G.gradSq u (x, y)) * v x := by
      apply tsum_congr
      intro x
      rw [speed_mul_vertexCarreDuChamp G m hm hu x]
    _ = ∑' x : V, ∑' y : V, G.gradSq u (x, y) * v x := by
      apply tsum_congr
      intro x
      rw [tsum_mul_right]
    _ = ∑' p : V × V, G.gradSq u p * v p.1 := hedge.tsum_prod.symm

/-- Full-energy carré-du-champ identity with the existing vertex rate and
speed measure.  Both functions remain in the full finite-energy domain; the
boundedness assumptions are used only for products and absolute summability. -/
theorem fullEnergy_carreDuChamp_identity
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) {u v : V → ℝ} {A B : ℝ}
    (huBound : ∀ x, |u x| ≤ A) (hvBound : ∀ x, |v x| ≤ B)
    (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    G.dirichletForm (u ^ 2) v =
      2 * G.dirichletForm u (u * v) -
        ∑' x : V, m x * vertexCarreDuChamp G m u x * v x := by
  rw [tsum_speed_mul_vertexCarreDuChamp_mul G m hm hvBound hu]
  exact fullEnergy_carreDuChamp_edge_identity G huBound hvBound hu hv

end ReflectedGMS

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyTraceBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VectorTraceMinimizer
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The componentwise maximum principle for the full-energy Dirichlet minimizer

This module proves the remaining clause of the paper's full-energy Dirichlet lemma:

> On each component, every coordinate bound on its boundary trace also bounds that
> coordinate of `h`. In particular a common bound on all of `A` bounds `h` on all vertices.

The route is the one indicated in the manuscript: *clipping plus uniqueness*. A one-sided
clip `max m ·` (resp. `min · M`) is applied **only on the graph component of the vertex
under consideration** and leaves the minimizer untouched on every other component. Since
every conductance edge joins two vertices of the same component, the modified function
still dominates no edge density, so its energy cannot increase; and since the assumed
bound holds at every boundary vertex of that component, the prescribed trace is preserved.
Minimality plus the existing uniqueness of `existsUnique_anchored_trace_minimizer` (scalar)
and `existsUnique_vector_trace_minimizer` (plane-valued) therefore force the clip to be the
identity on that component, which is exactly the asserted bound.

Everything is stated for the full energy domain and the full variation class of the two
existing minimizer theorems: an arbitrary countable vertex type, an arbitrary anchored
boundary set `A` (possibly infinite), arbitrarily many components, and competitors ranging
over *all* functions with the prescribed trace. No finite cell count, no connected patch,
no finite-support closure, and no extra integrability is assumed anywhere.

The energy comparison uses only edgewise domination of `gradSq`, which generalizes the
global `FullNetworkForm.gradSq_contraction_le` to a contraction that acts on one component
only. The plane-valued statements reuse the coordinate splitting of `vectorEnergy` from
`VectorTraceMinimizer`.
-/

set_option autoImplicit false

namespace ReflectedGMS.FullEnergyTraceBounds

open scoped ENNReal
open StatementIngredients

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### Energy domination from edgewise domination

The two existing contraction lemmas of `Forms/NormalContraction.lean` are stated for a
globally applied `1`-Lipschitz map. Only the underlying edgewise comparison is needed here,
because the modification below is not of the form `φ ∘ f`. -/

/-- Edgewise domination of the energy densities transfers the finite-energy domain. -/
theorem hasFiniteEnergy_of_gradSq_le {f g : V → ℝ} (hg : G.HasFiniteEnergy g)
    (hle : ∀ p : V × V, G.gradSq f p ≤ G.gradSq g p) : G.HasFiniteEnergy f :=
  Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg f p) hle hg

/-- Edgewise domination of the energy densities dominates the total energy. -/
theorem energy_le_of_gradSq_le {f g : V → ℝ} (hg : G.HasFiniteEnergy g)
    (hle : ∀ p : V × V, G.gradSq f p ≤ G.gradSq g p) : G.Energy f ≤ G.Energy g :=
  div_le_div_of_nonneg_right
    ((hasFiniteEnergy_of_gradSq_le G hg hle).tsum_le_tsum hle hg) (by norm_num)

/-- Edgewise domination in the extended-real energy of `Analysis/ExtendedEnergy.lean`. -/
theorem energyENN_le_of_gradSq_le {f g : V → ℝ} (hg : G.HasFiniteEnergy g)
    (hle : ∀ p : V × V, G.gradSq f p ≤ G.gradSq g p) : energyENN G f ≤ energyENN G g := by
  rw [energyENN_eq_ofReal_Energy G (hasFiniteEnergy_of_gradSq_le G hg hle),
    energyENN_eq_ofReal_Energy G hg]
  exact ENNReal.ofReal_le_ofReal (energy_le_of_gradSq_le G hg hle)

/-! ### Modifying a function on a single graph component -/

open Classical in
/-- Apply `φ` on the graph component of `x` and leave the function unchanged elsewhere.
The component is described by graph reachability, so no component index set, local
finiteness or connectedness of the whole graph is used. -/
noncomputable def componentModify (x : V) (φ : ℝ → ℝ) (h : V → ℝ) : V → ℝ := fun v =>
  if G.toSimpleGraph.Reachable x v then φ (h v) else h v

theorem componentModify_apply_of_reachable (x : V) (φ : ℝ → ℝ) (h : V → ℝ) {v : V}
    (hv : G.toSimpleGraph.Reachable x v) : componentModify G x φ h v = φ (h v) :=
  if_pos hv

theorem componentModify_apply_of_not_reachable (x : V) (φ : ℝ → ℝ) (h : V → ℝ) {v : V}
    (hv : ¬ G.toSimpleGraph.Reachable x v) : componentModify G x φ h v = h v :=
  if_neg hv

/-- **A one-component contraction decreases every edge density.** An edge of positive
conductance joins two vertices of one component, so its two endpoints are modified in the
same way: either both by the `1`-Lipschitz map `φ`, or neither. -/
theorem gradSq_componentModify_le (x : V) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (h : V → ℝ)
    (p : V × V) : G.gradSq (componentModify G x φ h) p ≤ G.gradSq h p := by
  rcases eq_or_lt_of_le (G.c_nonneg p.1 p.2) with hc | hc
  · simp only [ReflectedWalk.ConductanceGraph.gradSq, ← hc, zero_mul, le_refl]
  · have hadj : G.toSimpleGraph.Adj p.1 p.2 := G.toSimpleGraph_adj.2 hc
    have hd : |componentModify G x φ h p.2 - componentModify G x φ h p.1| ≤
        |h p.2 - h p.1| := by
      by_cases h1 : G.toSimpleGraph.Reachable x p.1
      · have h2 : G.toSimpleGraph.Reachable x p.2 := h1.trans hadj.reachable
        rw [componentModify_apply_of_reachable G x φ h h1,
          componentModify_apply_of_reachable G x φ h h2]
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
          hφ.dist_le_mul (h p.2) (h p.1)
      · have h2 : ¬ G.toSimpleGraph.Reachable x p.2 := fun hr => h1 (hr.trans hadj.symm.reachable)
        rw [componentModify_apply_of_not_reachable G x φ h h1,
          componentModify_apply_of_not_reachable G x φ h h2]
    exact mul_le_mul_of_nonneg_left (sq_le_sq.2 hd) (G.c_nonneg p.1 p.2)

theorem energyENN_componentModify_le (x : V) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    {h : V → ℝ} (hh : G.HasFiniteEnergy h) :
    energyENN G (componentModify G x φ h) ≤ energyENN G h :=
  energyENN_le_of_gradSq_le G hh (gradSq_componentModify_le G x hφ h)

/-- The prescribed trace survives a component modification that fixes the boundary values
of that component. -/
theorem componentModify_trace (x : V) (φ : ℝ → ℝ) (h : V → ℝ) {A : Set V}
    (hfix : ∀ a ∈ A, G.toSimpleGraph.Reachable x a → φ (h a) = h a) :
    ∀ a ∈ A, componentModify G x φ h a = h a := by
  intro a ha
  by_cases hr : G.toSimpleGraph.Reachable x a
  · rw [componentModify_apply_of_reachable G x φ h hr]
    exact hfix a ha hr
  · exact componentModify_apply_of_not_reachable G x φ h hr

/-! ### The scalar componentwise maximum principle -/

/-! ### Replacing one coordinate of a plane-valued function -/

/-- Replace the `i`-th coordinate of a plane-valued function by a scalar function. -/
noncomputable def coordUpdate (f : V → Plane) (i : Fin 2) (k : V → ℝ) : V → Plane := fun v =>
  (WithLp.toLp 2 (fun j => if j = i then k v else f v j) : Plane)

theorem coordUpdate_apply (f : V → Plane) (i : Fin 2) (k : V → ℝ) (v : V) (j : Fin 2) :
    coordUpdate f i k v j = if j = i then k v else f v j := rfl

/-- The replacement does not change the value where the new coordinate already agrees. -/
theorem coordUpdate_eq_of_coord_eq {f : V → Plane} {i : Fin 2} {k : V → ℝ} {a : V}
    (h : k a = f a i) : coordUpdate f i k a = f a := by
  refine PiLp.ext fun j => ?_
  rw [coordUpdate_apply]
  rcases eq_or_ne j i with hj | hj
  · rw [if_pos hj, h, hj]
  · rw [if_neg hj]

/-- Replacing one coordinate by one of no larger energy does not increase the vector
energy: the coordinate sum of `vectorEnergy` is compared term by term. -/
theorem vectorEnergy_coordUpdate_le {f : V → Plane} {i : Fin 2} {k : V → ℝ}
    (hle : energyENN G k ≤ energyENN G (fun v => f v i)) :
    vectorEnergy G (coordUpdate f i k) ≤ vectorEnergy G f := by
  rw [vectorEnergy_eq_sum, vectorEnergy_eq_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases eq_or_ne j i with hj | hj
  · have hk : (fun v => coordUpdate f i k v j) = k := by
      funext v
      rw [coordUpdate_apply, if_pos hj]
    rw [hk, hj]
    exact hle
  · have hk : (fun v => coordUpdate f i k v j) = fun v => f v j := by
      funext v
      rw [coordUpdate_apply, if_neg hj]
    rw [hk]

/-! ### The componentwise maximum principle for the plane-valued minimizer -/

/-- **Coordinate clipping on one component is the identity for the vector minimizer.**
The clipped coordinate is reassembled into a plane-valued competitor with the same trace
and no larger vector energy, so the existing uniqueness statement identifies it with the
minimizer. The competition class is the full one: *every* plane-valued function with the
prescribed trace, of finite or infinite energy. -/
theorem coord_componentModify_eq_of_vector_trace_minimizer {A : Set V}
    (hA : BoundaryAnchored G A) {u f : V → Plane} (hf : vectorEnergy G f < ∞)
    (htrace : ∀ a ∈ A, f a = u a)
    (hmin : ∀ g : V → Plane, (∀ a ∈ A, g a = u a) → vectorEnergy G f ≤ vectorEnergy G g)
    (i : Fin 2) (x : V) {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hfix : ∀ a ∈ A, G.toSimpleGraph.Reachable x a → φ (u a i) = u a i) :
    ∀ v, componentModify G x φ (fun w => f w i) v = f v i := by
  have hcoord : G.HasFiniteEnergy (fun w => f w i) := hasFiniteEnergy_coord G hf i
  have hfix' : ∀ a ∈ A, G.toSimpleGraph.Reachable x a →
      φ ((fun w => f w i) a) = (fun w => f w i) a := by
    intro a ha hr
    simp only [htrace a ha]
    exact hfix a ha hr
  have hmin' : ∀ g : V → Plane, (∀ a ∈ A, g a = f a) →
      vectorEnergy G f ≤ vectorEnergy G g := fun g hg =>
    hmin g fun a ha => (hg a ha).trans (htrace a ha)
  have hvle : vectorEnergy G (coordUpdate f i (componentModify G x φ (fun w => f w i))) ≤
      vectorEnergy G f :=
    vectorEnergy_coordUpdate_le G (energyENN_componentModify_le G x hφ hcoord)
  have hvtrace : ∀ a ∈ A,
      coordUpdate f i (componentModify G x φ (fun w => f w i)) a = f a := fun a ha =>
    coordUpdate_eq_of_coord_eq (componentModify_trace G x φ (fun w => f w i) hfix' a ha)
  have hveq : coordUpdate f i (componentModify G x φ (fun w => f w i)) = f :=
    (existsUnique_vector_trace_minimizer G hA hf).unique
      ⟨lt_of_le_of_lt hvle hf, hvtrace, fun g hg => le_trans hvle (hmin' g hg)⟩
      ⟨hf, fun _ _ => rfl, hmin'⟩
  intro v
  have hv : coordUpdate f i (componentModify G x φ (fun w => f w i)) v i = f v i :=
    congrArg (fun z : Plane => z i) (congrFun hveq v)
  rwa [coordUpdate_apply, if_pos rfl] at hv

/-- **Lower bound on one coordinate over one component.** -/
theorem le_coord_of_vector_trace_minimizer_on_component {A : Set V}
    (hA : BoundaryAnchored G A) {u f : V → Plane} (hf : vectorEnergy G f < ∞)
    (htrace : ∀ a ∈ A, f a = u a)
    (hmin : ∀ g : V → Plane, (∀ a ∈ A, g a = u a) → vectorEnergy G f ≤ vectorEnergy G g)
    (i : Fin 2) {m : ℝ} {x : V}
    (hb : ∀ a ∈ A, G.toSimpleGraph.Reachable x a → m ≤ u a i) :
    m ≤ f x i := by
  have hclip := coord_componentModify_eq_of_vector_trace_minimizer G hA hf htrace hmin i x
    (φ := fun t => max m t) (LipschitzWith.id.const_max m)
    (fun a ha hr => max_eq_right (hb a ha hr)) x
  rw [componentModify_apply_of_reachable G x _ (fun w => f w i)
    (SimpleGraph.Reachable.refl x)] at hclip
  rw [← hclip]
  exact le_max_left m (f x i)

/-- **Upper bound on one coordinate over one component.** -/
theorem coord_le_of_vector_trace_minimizer_on_component {A : Set V}
    (hA : BoundaryAnchored G A) {u f : V → Plane} (hf : vectorEnergy G f < ∞)
    (htrace : ∀ a ∈ A, f a = u a)
    (hmin : ∀ g : V → Plane, (∀ a ∈ A, g a = u a) → vectorEnergy G f ≤ vectorEnergy G g)
    (i : Fin 2) {M : ℝ} {x : V}
    (hb : ∀ a ∈ A, G.toSimpleGraph.Reachable x a → u a i ≤ M) :
    f x i ≤ M := by
  have hclip := coord_componentModify_eq_of_vector_trace_minimizer G hA hf htrace hmin i x
    (φ := fun t => min t M) (LipschitzWith.id.min_const M)
    (fun a ha hr => min_eq_left (hb a ha hr)) x
  rw [componentModify_apply_of_reachable G x _ (fun w => f w i)
    (SimpleGraph.Reachable.refl x)] at hclip
  rw [← hclip]
  exact min_le_right (f x i) M

/-- **The componentwise maximum principle of the full-energy Dirichlet lemma.** On the
graph component of `x`, every bound satisfied by the prescribed boundary trace in the
coordinate `i` is also satisfied by that coordinate of the minimizer. The boundary set,
the number of components and the vertex type are all arbitrary, and the minimality
hypothesis is the full one against every plane-valued function with the given trace. -/
theorem coord_mem_Icc_of_vector_trace_minimizer_on_component {A : Set V}
    (hA : BoundaryAnchored G A) {u f : V → Plane} (hf : vectorEnergy G f < ∞)
    (htrace : ∀ a ∈ A, f a = u a)
    (hmin : ∀ g : V → Plane, (∀ a ∈ A, g a = u a) → vectorEnergy G f ≤ vectorEnergy G g)
    (i : Fin 2) {m M : ℝ} {x : V}
    (hb : ∀ a ∈ A, G.toSimpleGraph.Reachable x a → u a i ∈ Set.Icc m M) :
    f x i ∈ Set.Icc m M :=
  ⟨le_coord_of_vector_trace_minimizer_on_component G hA hf htrace hmin i
      fun a ha hr => (hb a ha hr).1,
    coord_le_of_vector_trace_minimizer_on_component G hA hf htrace hmin i
      fun a ha hr => (hb a ha hr).2⟩

end ReflectedGMS.FullEnergyTraceBounds

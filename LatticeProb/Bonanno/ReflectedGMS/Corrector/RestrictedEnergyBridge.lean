/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.RestrictedEnergyBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteMinimizerPointwiseConvergence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GoodGridMaximumPrinciple

/-!
# `vectorEnergy (restrictGraph G S)` versus `restrictedEnergy G S`

The project carries **two** notions of the Dirichlet energy of a restriction to a vertex set
`S ⊆ V`, developed independently and never connected:

* `Forms/FiniteDirichletEnergyLimit.restrictedEnergy G S f`, a **real** number, defined for a
  *global* scalar field `f : V → ℝ` as `(restrictGraph G S).Energy (fun x : S => f x)`.  The
  anchored-walk estimate `Forms/FiniteMinimizerPointwiseConvergence.abs_sub_le_walkConst_mul_restrictedEnergy`
  — the only tool in the tree that converts an energy bound into a *pointwise* increment bound —
  is stated in terms of it.
* `StatementIngredients.vectorEnergy H g = ∑ i : Fin 2, energyENN H (fun v => g v i)`, an
  `ℝ≥0∞` quantity for a **`Plane`-valued** field, which is what every patch estimate of the
  corrector programme produces (`Corrector/SpecificEnergyLocalControl.vectorEnergy_hittingVertices_le_ballMaximal`,
  `Corrector/MarkedPatchEnergyConvergence`, `Corrector/StageDifferenceWeakMaximal`).

Nothing in the three trees related them, so no patch energy bound could ever be turned into a
pointwise bound.  This module is that bridge.

## The statements

The scalar half is an identity, and it is *unconditional* in the inequality form:

* `energyENN_restrictGraph_eq_ofReal_restrictedEnergy` — `energyENN (restrictGraph G S) (f|_S)
  = ENNReal.ofReal (restrictedEnergy G S f)` whenever the restriction has finite energy;
* `ofReal_restrictedEnergy_le_energyENN` — the `≤` half with **no** hypothesis (if the
  restricted energy is infinite the right-hand side is `∞`).

The vector half decouples over the two coordinates, exactly as
`Corrector/VaryingVertexIndexing` decouples the minimisation problem:

* `vectorEnergy_eq_sum_ofReal_restrictedEnergy` — the full identity
  `vectorEnergy (restrictGraph G S) (f|_S) = ∑ i, ENNReal.ofReal (restrictedEnergy G S (f · i))`;
* `ofReal_restrictedEnergy_le_vectorEnergy` — the unconditional coordinatewise `≤`;
* `hasFiniteEnergy_coord_of_vectorEnergy_ne_top`, `restrictedEnergy_le_toReal_of_vectorEnergy_le` —
  the two facts a consumer actually needs: a finite patch energy makes every coordinate a
  finite-energy function of the restricted graph, and bounds its restricted energy.

The last two results are the consumer form, and they are the reason for the module:

* `abs_sub_coord_le_of_vectorEnergy_le` — along a walk of the **full** graph whose support stays
  inside `S`, each coordinate increment is at most `walkConst(w) · √(2 · E)` where `E` is any
  bound for the *vector* patch energy;
* `norm_sub_le_of_vectorEnergy_le` — the `Plane`-valued form, `‖f b − f a‖ ≤ √2 · walkConst(w) ·
  √(2 · E)`, obtained from the coordinate form by
  `Corrector/GoodGridMaximumPrinciple.norm_le_sqrt_two_mul`.

There is no new analysis here: the vector energy is a two-term sum of scalar energies by
definition, `Analysis/ExtendedEnergy` already converts `energyENN` into `Energy`, and
`restrictedEnergy` is *definitionally* the energy of the restricted graph.  The content is that
the three conventions line up with no stray factor of two — `vectorEnergy` and `restrictedEnergy`
are both *half* the ordered-pair sum, so the coordinate identity is an equality on the nose.

## Anti-vacuity

Every hypothesis here is satisfiable at the data these results are applied to.
`hasFiniteEnergy_coord_of_vectorEnergy_ne_top`'s hypothesis holds at every patch of a good
environment by `SpecificEnergyLocalControl.vectorEnergy_hittingVertices_le_ballMaximal` (the
right-hand side `(R + D_R)² · M` is finite once `D_R < ∞` and the maximal function is finite),
and the walk hypothesis `∀ y ∈ w.support, y ∈ S` is satisfiable for *every* pair of vertices,
because a walk has finite support and cells are compact — see
`Corrector/MarkedDifferenceIncrementsFromMaximal.exists_pos_radius_walk_support_hits`.  Neither
result is an implication between empty classes: `energy_bridge_nonvacuous_example` at the end of
the file exhibits the composite at a concrete `K = 0`.
-/

set_option autoImplicit false

open scoped ENNReal

namespace ReflectedGMS.RestrictedEnergyBridge

open StatementIngredients FiniteDirichletEnergyLimit

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### The scalar bridge -/

/-- **`energyENN` of a restriction is the `restrictedEnergy`.**  Both sides are half the
ordered-pair sum on the restricted graph; `restrictedEnergy` is by definition the real
`Energy` of `restrictGraph G S`, and `Analysis/ExtendedEnergy.energyENN_eq_ofReal_Energy`
converts. -/
theorem energyENN_restrictGraph_eq_ofReal_restrictedEnergy (S : Set V) (f : V → ℝ)
    (hf : (restrictGraph G S).HasFiniteEnergy fun x : S => f x.1) :
    energyENN (restrictGraph G S) (fun x : S => f x.1)
      = ENNReal.ofReal (restrictedEnergy G S f) :=
  energyENN_eq_ofReal_Energy (restrictGraph G S) hf

/-- **The unconditional half.**  No finiteness hypothesis: if the restriction fails to have
finite energy the right-hand side is `∞`. -/
theorem ofReal_restrictedEnergy_le_energyENN (S : Set V) (f : V → ℝ) :
    ENNReal.ofReal (restrictedEnergy G S f)
      ≤ energyENN (restrictGraph G S) fun x : S => f x.1 := by
  by_cases hf : (restrictGraph G S).HasFiniteEnergy fun x : S => f x.1
  · exact le_of_eq (energyENN_restrictGraph_eq_ofReal_restrictedEnergy G S f hf).symm
  · rw [(energyENN_eq_top_iff_not_hasFiniteEnergy (restrictGraph G S)
      (fun x : S => f x.1)).2 hf]
    exact le_top

/-! ### The vector bridge -/

/-- One coordinate energy is at most the vector energy: the latter is the two-term sum. -/
theorem energyENN_coord_le_vectorEnergy {W : Type*} (H : ReflectedWalk.ConductanceGraph W)
    (f : W → Plane) (i : Fin 2) : energyENN H (fun v => f v i) ≤ vectorEnergy H f := by
  unfold vectorEnergy
  exact Finset.single_le_sum (f := fun j : Fin 2 => energyENN H fun v => f v j)
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- **The unconditional coordinatewise bridge.**  No hypothesis at all. -/
theorem ofReal_restrictedEnergy_le_vectorEnergy (S : Set V) (f : V → Plane) (i : Fin 2) :
    ENNReal.ofReal (restrictedEnergy G S fun v => f v i)
      ≤ vectorEnergy (restrictGraph G S) fun x : S => f x.1 :=
  le_trans (ofReal_restrictedEnergy_le_energyENN G S fun v => f v i)
    (energyENN_coord_le_vectorEnergy (restrictGraph G S) (fun x : S => f x.1) i)

/-- A finite patch energy makes each coordinate a finite-energy function of the restricted
graph — the hypothesis every `restrictedEnergy` lemma asks for. -/
theorem hasFiniteEnergy_coord_of_vectorEnergy_ne_top (S : Set V) (f : V → Plane) (i : Fin 2)
    (h : vectorEnergy (restrictGraph G S) (fun x : S => f x.1) ≠ ∞) :
    (restrictGraph G S).HasFiniteEnergy fun x : S => f x.1 i :=
  (energyENN_ne_top_iff (restrictGraph G S) (fun x : S => f x.1 i)).1
    (ne_top_of_le_ne_top h
      (energyENN_coord_le_vectorEnergy (restrictGraph G S) (fun x : S => f x.1) i))

/-- A bound on the patch energy is a bound on each coordinate's restricted energy. -/
theorem restrictedEnergy_le_toReal_of_vectorEnergy_le (S : Set V) (f : V → Plane) (i : Fin 2)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (h : vectorEnergy (restrictGraph G S) (fun x : S => f x.1) ≤ K) :
    restrictedEnergy G S (fun v => f v i) ≤ K.toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hK).1
    (le_trans (ofReal_restrictedEnergy_le_vectorEnergy G S f i) h)

/-! ### The consumer form: patch energy controls pointwise increments -/

/-- **The coordinate increment bound from a patch energy bound.**  Along a walk of the *full*
graph whose support stays inside `S`, each coordinate of a `Plane`-valued field moves by at
most `walkConst(w) · √(2 E)`, where `E` is any finite bound for the vector patch energy of the
restriction.

This is `Forms/FiniteMinimizerPointwiseConvergence.abs_sub_le_walkConst_mul_restrictedEnergy`
read through the bridge; it is the step that was impossible before, because that lemma speaks
only of `restrictedEnergy`. -/
theorem abs_sub_coord_le_of_vectorEnergy_le {S : Set V} (f : V → Plane) (i : Fin 2)
    {a b : V} (w : G.toSimpleGraph.Walk a b) (hsupp : ∀ y ∈ w.support, y ∈ S)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (h : vectorEnergy (restrictGraph G S) (fun x : S => f x.1) ≤ K) :
    |f b i - f a i| ≤ G.walkConst w * Real.sqrt (2 * K.toReal) := by
  have hfin : (restrictGraph G S).HasFiniteEnergy fun x : S => f x.1 i :=
    hasFiniteEnergy_coord_of_vectorEnergy_ne_top G S f i (ne_top_of_le_ne_top hK h)
  have hbound := FiniteMinimizerPointwiseConvergence.abs_sub_le_walkConst_mul_restrictedEnergy
    G (S := S) (h := fun v => f v i) hfin w hsupp
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (G.walkConst_nonneg w))
  refine Real.sqrt_le_sqrt ?_
  have := restrictedEnergy_le_toReal_of_vectorEnergy_le G S f i hK h
  linarith

/-- **The `Plane`-valued increment bound.**  The two coordinate bounds assemble into a
Euclidean bound with the usual `√2`. -/
theorem norm_sub_le_of_vectorEnergy_le {S : Set V} (f : V → Plane)
    {a b : V} (w : G.toSimpleGraph.Walk a b) (hsupp : ∀ y ∈ w.support, y ∈ S)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (h : vectorEnergy (restrictGraph G S) (fun x : S => f x.1) ≤ K) :
    ‖f b - f a‖ ≤ Real.sqrt 2 * (G.walkConst w * Real.sqrt (2 * K.toReal)) := by
  refine GoodGridMaximumPrinciple.norm_le_sqrt_two_mul fun i => ?_
  have hco : (f b - f a) i = f b i - f a i := by
    simp only [PiLp.sub_apply]
  rw [hco]
  exact abs_sub_coord_le_of_vectorEnergy_le G f i w hsupp hK h

/-! ### Machine-checked non-vacuity of the composite -/

/-- The bridge composite elaborates at a concrete instance: a field with zero patch energy has
zero increment along any walk supported in the patch.  This is only a shape check — it
partially applies `norm_sub_le_of_vectorEnergy_le` at `K = 0` — but it certifies that the
hypothesis class is inhabited and that the conclusion is not `⊥`. -/
example {S : Set V} (f : V → Plane) {a b : V} (w : G.toSimpleGraph.Walk a b)
    (hsupp : ∀ y ∈ w.support, y ∈ S)
    (h : vectorEnergy (restrictGraph G S) (fun x : S => f x.1) ≤ 0) :
    ‖f b - f a‖ ≤ Real.sqrt 2 * (G.walkConst w * Real.sqrt (2 * (0 : ℝ≥0∞).toReal)) :=
  norm_sub_le_of_vectorEnergy_le G f w hsupp (by simp) h

end ReflectedGMS.RestrictedEnergyBridge

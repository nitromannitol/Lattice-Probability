/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AreaTransitionReversibility at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.AreaCylinderShiftIdentity
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIdentification
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea

/-! # Detailed balance of the reflected transition function for a non-summable speed

`ReflectedGMS.Temporal.AreaCylinderShiftIdentity` reduced σ-finite shift
invariance of the area-weighted two-sided law of the **area-speed** reflected
process to one two-point identity,

`ProcessTransitionReversible PF (cellArea F) δ`, i.e.
`area x · p_δ(x,y) = area y · p_δ(y,x)`,

and recorded that the existing proof of that identity
(`reflected_transition_detailedBalance`) is unusable here because it routes
through `reflected_vertexProbability_eq_semigroupKernel ←
reflected_occupationResolvent`, which carries `Summable m`.  This file proves the
identity for **every** pointwise positive speed, in particular for the total cell
area, which is not summable.

## Where `Summable m` was actually used, and why it is avoidable

`Summable m` is *essential* to the existing route and cannot be weakened inside
it.  The route identifies the process transition function with the analytic
full-form semigroup kernel, and that identification compares the finite-trace
resolvent with the full resolvent in the **global** `L²(m)` norm:
`finiteTraceResolventExtension_error_le_tail` bounds the error by the tail mass
`∑' v ∉ A, m v`, and `finiteTraceResolventExtension_hasSpeedL2` needs
`hasSpeedL2_of_abs_le hm hmsum` — a function bounded by `1` lies in `L²(m)` only
when `m` is summable.  For a non-summable speed the finite-trace resolvent of a
vertex indicator is simply not in `L²(m)`, so no reweighting or local
integrability repairs that comparison.

The observation of this file is that **detailed balance does not need the
identification at all**.  Reversibility is inherited by any limit:

* each finite-trace object is a genuine finite-graph resolvent, and the
  symmetric Dirichlet form of the finite target graph makes it exactly
  `m`-symmetric — `parameterizedResolventFunction_indic_detailedBalance`, proved
  from the already checked weak resolvent equation
  `parameterizedResolventFunction_weak` and `dirichletForm_comm`, with no
  summability, no finiteness of the total mass and no operator-algebra input;
* the actual occupation resolvent of the process is the limit of those
  finite-trace resolvents along any exhaustion — this is exactly the convergence
  half of `reflected_occupationResolvent_of_trace_approximation`
  (`tendsto_integral_exp_neg_mul_measureReal_of_ae_approximated` together with
  `targetTraceProcess_laplace_eq_resolvent`), and that half carries **no**
  `Summable` hypothesis; only the identification of the limit with the full
  resolvent does.  Sigma-finite exhaustion therefore transports the two-point
  identity even though it does not transport the resolvent itself;
* a symmetric family of Laplace transforms forces the transition functions
  themselves to be symmetric, by the already checked right-continuity/uniqueness
  lemma `eqOn_nonneg_of_integral_exp_neg_mul_eq`, applied to the two transition
  functions rescaled into `[0,1]` by `max (m x) (m y)`.

So the pointwise `L²` input that replaces `Summable m` is exactly the
**point-supported** one: only weighted vertex indicators — which lie in `L²(m)`
for every positive `m` — and the *finite* graphs of an exhaustion are ever
tested, never a globally bounded function against the infinite total mass.

## Hypotheses

The process is unchanged: `IsReflectedWalk G (fun v => G.pi v / m v) hmin PF`,
its own rate function, and the reversing measure is the same `m`.  The only
hypotheses are `hG : G.toSimpleGraph.Connected` (needed by the exhaustion and by
`G.pi_pos_of_connected`, and already required by every existing identification
result) and `hm : ∀ v, 0 < m v`.  For the area instance `hm` is
`StatementIngredients.cellArea_pos F hF`, so the area statements need only the
geometry hypothesis `hF` that the rest of the project already carries.  No
summability, no finite total area, no `IsFiniteMeasure`, no reweighting of a
fast-speed process.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace BigOperators

namespace ReflectedGMS.AreaReversibility

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open TargetTraceTransition TraceLaplaceConvergence

/-! ## Symmetry of the parameterized resolvent, from the weak form equation -/

section Form

variable {V : Type*}

/-- Testing the parameterized resolvent against a weighted vertex indicator
returns the mass-weighted resolvent value.  This is the resolvent analogue of
`inner_semigroup_indic_eq_mass_mul_kernel`. -/
theorem inner_parameterizedResolvent_indic_eq_mass_mul [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v) (h : ℝ)
    (f : ValueSpace V) (x : V) :
    ⟪parameterizedResolvent G m h f,
        weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)⟫_ℝ =
      m x * parameterizedResolventFunction G m h f x := by
  rw [weightedValue_indic_eq_single G m x, lp.inner_single_right]
  simp only [Real.inner_apply, parameterizedResolventFunction, unweight]
  have hs : Real.sqrt (m x) ≠ 0 := (Real.sqrt_pos.2 (hm x)).ne'
  field_simp [hs]
  rw [Real.sq_sqrt (hm x).le]

/-- **The parameterized resolvent is symmetric on `L²(m)`.**  Only the checked
weak resolvent equation on the full energy domain and symmetry of the Dirichlet
form are used; there is no summability, no finiteness of the total mass and no
spectral-calculus input. -/
theorem inner_parameterizedResolvent_comm
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v) {h : ℝ} (hh : 0 < h)
    (f g : ValueSpace V) :
    ⟪f, parameterizedResolvent G m h g⟫_ℝ =
      ⟪g, parameterizedResolvent G m h f⟫_ℝ := by
  have h1 := parameterizedResolventFunction_weak G m hm hh g
    (unweight m (parameterizedResolvent G m h f))
    (hasSpeedL2_unweight m hm (parameterizedResolvent G m h f))
    (parameterizedResolventFunction_hasFiniteEnergy G m h f)
  have h2 := parameterizedResolventFunction_weak G m hm hh f
    (unweight m (parameterizedResolvent G m h g))
    (hasSpeedL2_unweight m hm (parameterizedResolvent G m h g))
    (parameterizedResolventFunction_hasFiniteEnergy G m h g)
  rw [weightedValue_unweight m hm (parameterizedResolvent G m h f)] at h1
  rw [weightedValue_unweight m hm (parameterizedResolvent G m h g)] at h2
  have hD : G.dirichletForm (parameterizedResolventFunction G m h g)
        (unweight m (parameterizedResolvent G m h f)) =
      G.dirichletForm (parameterizedResolventFunction G m h f)
        (unweight m (parameterizedResolvent G m h g)) := by
    simp only [parameterizedResolventFunction]
    exact G.dirichletForm_comm _ _
  rw [hD] at h1
  have hcomm : ⟪parameterizedResolvent G m h g, parameterizedResolvent G m h f⟫_ℝ =
      ⟪parameterizedResolvent G m h f, parameterizedResolvent G m h g⟫_ℝ :=
    real_inner_comm _ _
  linarith [h1, h2, hcomm]

/-- **Detailed balance of the parameterized resolvent kernel.**  For every
pointwise positive speed `m`, without any summability. -/
theorem parameterizedResolventFunction_indic_detailedBalance [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v) {h : ℝ} (hh : 0 < h)
    (x y : V) :
    m x * parameterizedResolventFunction G m h
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x =
      m y * parameterizedResolventFunction G m h
        (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)) y := by
  rw [← inner_parameterizedResolvent_indic_eq_mass_mul G m hm h
      (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x,
    ← inner_parameterizedResolvent_indic_eq_mass_mul G m hm h
      (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)) y]
  have hkey := inner_parameterizedResolvent_comm G m hm hh
    (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x))
    (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))
  have c1 : ⟪parameterizedResolvent G m h
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)),
      weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)⟫_ℝ =
      ⟪weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x),
        parameterizedResolvent G m h
          (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))⟫_ℝ :=
    real_inner_comm _ _
  have c2 : ⟪parameterizedResolvent G m h
        (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)),
      weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)⟫_ℝ =
      ⟪weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y),
        parameterizedResolvent G m h
          (weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x))⟫_ℝ :=
    real_inner_comm _ _
  linarith [hkey, c1, c2]

end Form

/-! ## Detailed balance of the actual reflected process -/

section Process

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The occupation-normalized finite-trace resolvent of a finite target graph is
`m`-symmetric.  The finite target graph carries the same speed atoms, so this is
the previous symmetry specialized to `finiteTargetGraph`. -/
theorem finiteTraceOccupationResolvent_indic_detailedBalance
    (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {alpha : ℝ} (ha : 0 < alpha) (x y : {v // v ∈ A}) :
    m x.1 * finiteTraceOccupationResolvent G hG A hA m alpha
        (weightedValue (fun z : {v // v ∈ A} => m z.1)
          ((finiteTargetGraph G hG A hA).indic y)
          (VertexTest.indic_hasSpeedL2 (finiteTargetGraph G hG A hA)
            (fun z : {v // v ∈ A} => m z.1) y)) x =
      m y.1 * finiteTraceOccupationResolvent G hG A hA m alpha
        (weightedValue (fun z : {v // v ∈ A} => m z.1)
          ((finiteTargetGraph G hG A hA).indic x)
          (VertexTest.indic_hasSpeedL2 (finiteTargetGraph G hG A hA)
            (fun z : {v // v ∈ A} => m z.1) x)) y := by
  have hbal := parameterizedResolventFunction_indic_detailedBalance
    (finiteTargetGraph G hG A hA) (fun z : {v // v ∈ A} => m z.1)
    (fun z => hm z.1) (one_div_pos.mpr ha) x y
  simp only [finiteTraceOccupationResolvent]
  linear_combination (1 / alpha) * hbal

/-- The actual process occupation resolvent is the limit of the finite-trace
occupation resolvents along any exhaustion.  This is the convergence half of
`reflected_occupationResolvent_of_trace_approximation`; unlike the identification
of the limit with the full-network resolvent it uses **no** summability of the
speed. -/
theorem tendsto_finiteTraceOccupationResolvent_reflected
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (E : G.Exhaustion) (x y : V) (hx : ∀ n, x ∈ E.Gsub n) (hy : ∀ n, y ∈ E.Gsub n)
    {alpha : ℝ} (ha : 0 < alpha) :
    Tendsto
      (fun n => finiteTraceOccupationResolvent G hG (E.Gsub n) (E.nonempty n) m alpha
        (weightedValue (fun z : {v // v ∈ E.Gsub n} => m z.1)
          ((finiteTargetGraph G hG (E.Gsub n) (E.nonempty n)).indic ⟨y, hy n⟩)
          (VertexTest.indic_hasSpeedL2
            (finiteTargetGraph G hG (E.Gsub n) (E.nonempty n))
            (fun z : {v // v ∈ E.Gsub n} => m z.1) ⟨y, hy n⟩)) ⟨x, hx n⟩)
      atTop
      (𝓝 (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
        (PF.P x {ω | PF.X (Real.toNNReal t) ω = some y}).toReal)) := by
  have hw : ∀ v, 0 < G.pi v / m v := fun v =>
    div_pos (G.pi_pos_of_connected hG v) (hm v)
  have hprob := tendsto_integral_exp_neg_mul_measureReal_of_ae_approximated
    (fun n t => aemeasurable_targetTraceProcess h hG (E.nonempty n) (hx n) t)
    PF.measurable_X (reflected_targetTrace_approximated h hG hw E x hx) y
    (fun n => measurable_targetTraceProcess_transitionReal h hG hw
      (E.nonempty n) (hx n) y)
    (measurable_reflected_vertexProbability h x y) ha
  exact hprob.congr fun n => targetTraceProcess_laplace_eq_resolvent hG (E.Gsub n)
    (E.nonempty n) m hm h ha ⟨x, hx n⟩ ⟨y, hy n⟩

/-- **Detailed balance of the actual occupation resolvent of the reflected
process, for a non-summable speed.**  Each finite-trace approximation is exactly
`m`-symmetric, and symmetry passes to the exhaustion limit even though the limit
is not identified with the full-network resolvent. -/
theorem reflected_occupationResolvent_detailedBalance
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    m x * (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
        (PF.P x {ω | PF.X (Real.toNNReal t) ω = some y}).toReal) =
      m y * (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
        (PF.P y {ω | PF.X (Real.toNNReal t) ω = some x}).toReal) := by
  classical
  obtain ⟨E⟩ := Existence.exists_exhaustion hG
  obtain ⟨N, hN⟩ := E.exists_subset {x, y}
  have hx : ∀ n, x ∈ (E.shift N).Gsub n := fun n => hN (n + N) (by omega) (by simp)
  have hy : ∀ n, y ∈ (E.shift N).Gsub n := fun n => hN (n + N) (by omega) (by simp)
  have hxy := (tendsto_finiteTraceOccupationResolvent_reflected h hG hm
    (E.shift N) x y hx hy ha).const_mul (m x)
  have hyx := (tendsto_finiteTraceOccupationResolvent_reflected h hG hm
    (E.shift N) y x hy hx ha).const_mul (m y)
  refine tendsto_nhds_unique hxy (hyx.congr fun n => ?_)
  exact (finiteTraceOccupationResolvent_indic_detailedBalance G hG
    ((E.shift N).Gsub n) ((E.shift N).nonempty n) m hm ha ⟨x, hx n⟩ ⟨y, hy n⟩).symm

/-- **Detailed balance of the actual reflected transition function for a
non-summable speed.**  This is `reflected_transition_detailedBalance` with
`Summable m` removed: the two-point identity `m x · p_t(x,y) = m y · p_t(y,x)`
holds at every fixed time for every pointwise positive speed.  The passage from
the symmetric Laplace transforms to the transition functions is the already
checked right-continuity uniqueness `eqOn_nonneg_of_integral_exp_neg_mul_eq`,
applied after rescaling both transition functions into `[0,1]`. -/
theorem reflected_transition_detailedBalance_of_positive_speed
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v) (t : ℝ≥0) (x y : V) :
    m x * (PF.P x {ω | PF.X t ω = some y}).toReal =
      m y * (PF.P y {ω | PF.X t ω = some x}).toReal := by
  classical
  have hMpos : 0 < max (m x) (m y) := lt_max_of_lt_left (hm x)
  have hcx0 : 0 ≤ m x / max (m x) (m y) := div_nonneg (hm x).le hMpos.le
  have hcy0 : 0 ≤ m y / max (m x) (m y) := div_nonneg (hm y).le hMpos.le
  have hcx1 : m x / max (m x) (m y) ≤ 1 := (div_le_one hMpos).2 (le_max_left _ _)
  have hcy1 : m y / max (m x) (m y) ≤ 1 := (div_le_one hMpos).2 (le_max_right _ _)
  have hpull : ∀ (c a : ℝ) (φ : ℝ → ℝ),
      (∫ s : ℝ in Ioi 0, Real.exp (-a * s) * (c * φ s)) =
        c * ∫ s : ℝ in Ioi 0, Real.exp (-a * s) * φ s := by
    intro c a φ
    have hfun : (fun s : ℝ => Real.exp (-a * s) * (c * φ s)) =
        fun s : ℝ => c * (Real.exp (-a * s) * φ s) := by
      funext s; ring
    rw [hfun, integral_const_mul]
  have hkey : EqOn
      (fun s : ℝ => (m x / max (m x) (m y)) *
        (PF.P x {ω | PF.X (Real.toNNReal s) ω = some y}).toReal)
      (fun s : ℝ => (m y / max (m x) (m y)) *
        (PF.P y {ω | PF.X (Real.toNNReal s) ω = some x}).toReal) (Ici 0) := by
    refine eqOn_nonneg_of_integral_exp_neg_mul_eq _ _
      ((measurable_reflected_vertexProbability h x y).const_mul _)
      ((measurable_reflected_vertexProbability h y x).const_mul _)
      (fun s _ => ⟨mul_nonneg hcx0 (reflected_vertexProbability_mem_Icc PF x y s).1,
        mul_le_one₀ hcx1 (reflected_vertexProbability_mem_Icc PF x y s).1
          (reflected_vertexProbability_mem_Icc PF x y s).2⟩)
      (fun s _ => ⟨mul_nonneg hcy0 (reflected_vertexProbability_mem_Icc PF y x s).1,
        mul_le_one₀ hcy1 (reflected_vertexProbability_mem_Icc PF y x s).1
          (reflected_vertexProbability_mem_Icc PF y x s).2⟩)
      (fun s _ => continuousWithinAt_const.mul
        (reflected_vertexProbability_rightContinuous h x y s))
      (fun s _ => continuousWithinAt_const.mul
        (reflected_vertexProbability_rightContinuous h y x s))
      (fun alpha halpha => ?_)
    rw [hpull, hpull, div_mul_eq_mul_div, div_mul_eq_mul_div,
      reflected_occupationResolvent_detailedBalance h hG hm halpha x y]
  have ht := hkey (Set.mem_Ici.2 t.coe_nonneg)
  simp only [Real.toNNReal_coe] at ht
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff hMpos.ne' hMpos.ne'] at ht
  exact mul_right_cancel₀ hMpos.ne' ht

/-- **The producer hypothesis of `AreaCylinderShiftIdentity`, for every
pointwise positive speed.**  `ProcessTransitionReversible PF m δ` with no
summability of `m`. -/
theorem processTransitionReversible_of_positive_speed
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v) (t : ℝ≥0) :
    TwoSided.ProcessTransitionReversible PF m t := by
  intro x y
  simp only [TwoSided.processTransition]
  exact reflected_transition_detailedBalance_of_positive_speed h hG hm t x y

/-! ## The area instance, and the unconditional area-clock conclusions -/

/-- **Reversibility of the area-speed reflected process with respect to the cell
area.**  The process is the reflected walk with rate `π(x) / area(x)` and the
reversing measure is the same cell area; positivity of the area is
`StatementIngredients.cellArea_pos`, and the total area is never assumed
finite. -/
theorem processTransitionReversible_cellArea
    {G : ConductanceGraph V} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}
    (F : IndexedCells V) (hF : Geometry F)
    (h : IsReflectedWalk G
      (fun v => G.pi v / StatementIngredients.cellArea F v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (δ : ℝ≥0) :
    TwoSided.ProcessTransitionReversible PF (StatementIngredients.cellArea F) δ :=
  processTransitionReversible_of_positive_speed h hG
    (StatementIngredients.cellArea_pos F hF) δ

end Process

end ReflectedGMS.AreaReversibility

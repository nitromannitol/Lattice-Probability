/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TraceOccupationResolventLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceResolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceRenewal

/-! The occupation-normalized finite-trace resolvent of a vertex indicator
converges pointwise to the corresponding full-network resolvent. -/

-- Merged from `ReflectedGMS/Forms/TracePotentialLimit.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_TracePotentialLimit

/-! Pointwise convergence of the actual finite-trace potentials follows from
the checked full-form error bound and positivity of each speed atom. This is
the deterministic limit needed to identify process occupation resolvents. -/

set_option autoImplicit false

open scoped ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

theorem weightedValue_vertex_sq_le_norm_sq (m : V → ℝ) (hm : ∀ x, 0 < m x)
    (f : V → ℝ) (hf : HasSpeedL2 m f) (x : V) :
    m x * (f x) ^ 2 ≤ ‖weightedValue m f hf‖ ^ 2 := by
  have hn := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (weightedValue m f hf) x
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
  simpa only [weightedValue_apply, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (hm x).le] using hs

theorem finiteTraceResolventExtension_pointwise_error_sq_le
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) (x : V) :
    (finiteTraceResolventExtension G hG A hA m h f x -
      parameterizedResolventFunction G m h f x) ^ 2 ≤
        (∑' v : {v // v ∉ A}, m v.1) / m x := by
  let e := finiteTraceResolventExtension G hG A hA m h f -
    parameterizedResolventFunction G m h f
  have he := finiteTraceResolventExtension_sub_resolvent_hasSpeedL2
    G hG A hA m hm hmsum hh f hf
  have hvertex := weightedValue_vertex_sq_le_norm_sq m hm e he x
  have htotal := finiteTraceResolventExtension_error_le_tail
    G hG A hA m hm hmsum hh f hf
  have henergy : 0 ≤ h * G.Energy e := mul_nonneg hh.le (G.Energy_nonneg e)
  apply (le_div_iff₀ (hm x)).2
  have hb : m x * (e x) ^ 2 ≤ ∑' v : {v // v ∉ A}, m v.1 :=
    hvertex.trans ((le_add_of_nonneg_right henergy).trans htotal)
  simpa only [e, Pi.sub_apply, mul_comm] using hb

/-- Every vertex has pointwise convergence, along every finite exhaustion. -/
theorem finiteTraceResolventExtension_pointwise_tendsto
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (E : G.Exhaustion) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) (x : V) :
    Filter.Tendsto
      (fun n => finiteTraceResolventExtension G hG (E.Gsub n) (E.nonempty n) m h f x)
      Filter.atTop (nhds (parameterizedResolventFunction G m h f x)) := by
  have hEG : Filter.Tendsto E.Gsub Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro A
    obtain ⟨N, hN⟩ := E.exists_subset A
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  have htail : Filter.Tendsto
      (fun n => (∑' v : {v // v ∉ E.Gsub n}, m v.1) / m x)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, zero_div] using
      ((tendsto_tsum_compl_atTop_zero m).comp hEG).div_const (m x)
  have hs : Filter.Tendsto
      (fun n => (finiteTraceResolventExtension G hG (E.Gsub n) (E.nonempty n) m h f x -
        parameterizedResolventFunction G m h f x) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => sq_nonneg _) (fun n =>
        finiteTraceResolventExtension_pointwise_error_sq_le
          G hG (E.Gsub n) (E.nonempty n) m hm hmsum hh f hf x)
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Function.comp_def, Real.dist_eq, Real.sqrt_sq_eq_abs, Real.sqrt_zero]
    using Real.continuous_sqrt.continuousAt.tendsto.comp hs

end ReflectedGMS.FullNetworkForm

end Merged_TracePotentialLimit

set_option autoImplicit false

open Classical

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- The weighted indicator on a finite target is the restriction of the
full-network weighted indicator. -/
theorem finiteTrace_weightedIndicator_eq_restriction
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) {y : V} (hy : y ∈ A) :
    weightedValue (fun z : {v // v ∈ A} => m z.1)
        ((finiteTargetGraph G hG A hA).indic ⟨y, hy⟩)
        (VertexTest.indic_hasSpeedL2 (finiteTargetGraph G hG A hA)
          (fun z : {v // v ∈ A} => m z.1) ⟨y, hy⟩) =
      weightedValue (fun z : {v // v ∈ A} => m z.1)
        (fun z => G.indic y z.1) (Memℓp.all _) := by
  apply lp.ext
  funext z
  by_cases hz : z = ⟨y, hy⟩
  · simp [weightedValue_apply, ReflectedWalk.ConductanceGraph.indic, hz]
  · have hzval : z.1 ≠ y := by
      intro h
      apply hz
      exact Subtype.ext h
    simp [weightedValue_apply, ReflectedWalk.ConductanceGraph.indic, hz, hzval]

/-- Along every finite exhaustion, the occupation-normalized finite-trace
resolvent of a vertex indicator converges to the full resolvent. -/
theorem finiteTraceOccupationResolvent_indicator_tendsto
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (E : G.Exhaustion) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (halpha : 0 < alpha) (x y : V) :
    Filter.Tendsto
      (fun n => if hx : x ∈ E.Gsub n then
        finiteTraceOccupationResolvent G hG (E.Gsub n) (E.nonempty n) m alpha
          (weightedValue (fun z : {v // v ∈ E.Gsub n} => m z.1)
            (fun z => G.indic y z.1) (Memℓp.all _)) ⟨x, hx⟩
        else 0)
      Filter.atTop
      (nhds ((1 / alpha) *
        parameterizedResolventFunction G m (1 / alpha)
          (weightedValue m (G.indic y)
            (VertexTest.indic_hasSpeedL2 G m y)) x)) := by
  let f : ValueSpace V :=
    weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)
  have hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1 := by
    intro v
    rw [show unweight m f = G.indic y from
      unweight_weightedValue m hm (G.indic y)
        (VertexTest.indic_hasSpeedL2 G m y)]
    by_cases hv : v = y <;>
      simp [ReflectedWalk.ConductanceGraph.indic, hv]
  have hlimit := finiteTraceResolventExtension_pointwise_tendsto
    G hG E m hm hmsum (one_div_pos.mpr halpha) f hf x
  have hscaled : Filter.Tendsto
      (fun n => (1 / alpha) *
        finiteTraceResolventExtension G hG (E.Gsub n) (E.nonempty n)
          m (1 / alpha) f x)
      Filter.atTop
      (nhds ((1 / alpha) * parameterizedResolventFunction G m (1 / alpha) f x)) :=
    hlimit.const_mul (1 / alpha)
  obtain ⟨N, hN⟩ := E.exists_subset {x}
  apply hscaled.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn
  have hx : x ∈ E.Gsub n := hn (Finset.mem_singleton_self x)
  have hforcing :
      weightedValue (fun z : {v // v ∈ E.Gsub n} => m z.1)
          (fun z => G.indic y z.1) (Memℓp.all _) =
        finiteTraceForcing (E.Gsub n) f := by
    rfl
  simp only [hx, ↓reduceDIte]
  rw [finiteTraceOccupationResolvent, hforcing]
  exact congrArg (fun z : ℝ => (1 / alpha) * z)
    (finiteTraceResolventExtension_eqOn G hG (E.Gsub n) (E.nonempty n)
      m (1 / alpha) f hx)

end ReflectedGMS.FullNetworkForm

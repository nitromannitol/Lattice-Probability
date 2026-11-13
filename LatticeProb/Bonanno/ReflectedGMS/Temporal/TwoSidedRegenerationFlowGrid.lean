/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TwoSidedRegenerationFlowGrid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationFlow
import LatticeProb.Bonanno.ReflectedGMS.Temporal.GridAveragedInvariantVersion

/-!
# The regeneration flow on the marked carrier, in the consumer's `hθ` / `hS` shape

The directional bracket-LLN weld (`Limit/DirectionalBracketLLNWeld`,
`Limit/DirectionalBracketLLNGatesCoding`) takes the marked flow and scaling on `(Env × X) × Grid`
through the binders

* `hθ : ∀ t y d, θ t (y, d) = (θΩ t y, translate (timeVec t) d)`,
* `hS : ∀ C y d, S C (y, d) = (SΩ C y, gridScale C d)`.

Here `X = FlowCoding`, `θΩ = reRootFlow`, `SΩ = reScale` (`Temporal/TwoSidedRegenerationFlow`),
and `gridFlow` / `gridScaleFlow` are the marked maps: `hθ` and `hS` hold by `rfl`
(`gridFlow_apply`, `gridScaleFlow_apply`), and the three pointwise flow fields of
`ConditionalTemporalAveraging.TemporalBlockSystem` (`flow_zero`, `flow_add`, `measurable_flow`) and
the field `flowScale` of `ScaledRootChain.ScaledRootChainSystem` hold (`gridFlow_zero`,
`gridFlow_add`, `measurable_gridFlow`, `flowScaleIntertwine_gridFlow`).  The block fields and
the transport are not addressed here.
-/

set_option autoImplicit false

open MeasureTheory

namespace ReflectedGMS.TwoSidedRegenerationFlowGrid

open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance ReflectedGMS.MarkedSimilarityActionLaws
open ReflectedGMS.ScaledConditionalTemporalAveraging

/-! ### The time vector -/

theorem timeVec_eq_smul (t : ℝ) : timeVec t = t • timeVec 1 := by
  ext i
  fin_cases i <;> simp [timeVec]

theorem timeVec_add (a b : ℝ) : timeVec (a + b) = timeVec a + timeVec b := by
  rw [timeVec_eq_smul (a + b), timeVec_eq_smul a, timeVec_eq_smul b, add_smul]

theorem timeVec_mul (c t : ℝ) : timeVec (c * t) = c • timeVec t := by
  rw [timeVec_eq_smul (c * t), timeVec_eq_smul t, smul_smul]

theorem timeVec_zero' : timeVec 0 = 0 := by
  rw [timeVec_eq_smul, zero_smul]

theorem measurable_timeVec : Measurable timeVec := by
  have h : timeVec = fun t : ℝ => t • timeVec 1 := funext timeVec_eq_smul
  rw [h]
  exact (continuous_id.smul continuous_const).measurable

/-! ### The marked flow and scaling -/

/-- The marked flow: re-root the configuration, re-root the time grid. -/
noncomputable def gridFlow (t : ℝ) (p : FlowSpace × Grid) : FlowSpace × Grid :=
  (reRootFlow t p.1, translate (timeVec t) p.2)

/-- The marked scaling: scale the configuration, scale the time grid. -/
noncomputable def gridScaleFlow (C : ℝ) (p : FlowSpace × Grid) : FlowSpace × Grid :=
  (reScale C p.1, gridScale C p.2)

/-- **The consumer's `hθ`**, by definition. -/
theorem gridFlow_apply (t : ℝ) (y : FlowSpace) (d : Grid) :
    gridFlow t (y, d) = (reRootFlow t y, translate (timeVec t) d) := rfl

/-- **The consumer's `hS`**, by definition. -/
theorem gridScaleFlow_apply (C : ℝ) (y : FlowSpace) (d : Grid) :
    gridScaleFlow C (y, d) = (reScale C y, gridScale C d) := rfl

/-- `TemporalBlockSystem.flow_zero`. -/
theorem gridFlow_zero (p : FlowSpace × Grid) : gridFlow 0 p = p := by
  obtain ⟨y, d⟩ := p
  rw [gridFlow_apply, reRootFlow_zero, timeVec_zero', translate_zero]

/-- `TemporalBlockSystem.flow_add`. -/
theorem gridFlow_add (a b : ℝ) (p : FlowSpace × Grid) :
    gridFlow a (gridFlow b p) = gridFlow (a + b) p := by
  obtain ⟨y, d⟩ := p
  rw [gridFlow_apply, gridFlow_apply, gridFlow_apply, reRootFlow_add, translate_translate,
    timeVec_add, add_comm (timeVec b)]

/-- `TemporalBlockSystem.measurable_flow`. -/
theorem measurable_gridFlow :
    Measurable fun q : (FlowSpace × Grid) × ℝ => gridFlow q.2 q.1 := by
  have h1c : Measurable ((fun p : FlowSpace × ℝ => reRootFlow p.2 p.1)
      ∘ fun q : (FlowSpace × Grid) × ℝ => (q.1.1, q.2)) :=
    measurable_reRootFlow.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h1 : Measurable fun q : (FlowSpace × Grid) × ℝ => reRootFlow q.2 q.1.1 := by
    simpa only [Function.comp_def] using h1c
  have h2c : Measurable ((fun p : Grid × Plane => translate p.2 p.1)
      ∘ fun q : (FlowSpace × Grid) × ℝ => (q.1.2, timeVec q.2)) :=
    measurable_translate.comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_timeVec.comp measurable_snd))
  have h2 : Measurable fun q : (FlowSpace × Grid) × ℝ => translate (timeVec q.2) q.1.2 := by
    simpa only [Function.comp_def] using h2c
  exact h1.prodMk h2

/-- `ScaledRootChainSystem.flowScale`: `θ (C² t) ∘ S C = S C ∘ θ t` on the marked carrier. -/
theorem flowScaleIntertwine_gridFlow : FlowScaleIntertwine gridFlow gridScaleFlow := by
  intro C hC t p
  obtain ⟨y, d⟩ := p
  rw [gridScaleFlow_apply, gridFlow_apply, gridFlow_apply, gridScaleFlow_apply,
    flowScaleIntertwine_reRootFlow C hC t y, gridScale_of_pos hC, gridScale_of_pos hC,
    dilate_translate, timeVec_mul]

end ReflectedGMS.TwoSidedRegenerationFlowGrid

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ReflectedIdentification at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetTraceTransition
import LatticeProb.Bonanno.ReflectedGMS.Forms.TraceOccupationResolventLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.TraceLaplaceConvergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.LaplaceFunctionUniqueness
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRightNhds
import LatticeProb.Bonanno.ReflectedGMS.Forms.TransitionRightContinuity
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupKernelLaplace
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnClockCompatibility
import LatticeProb.Bonanno.ReflectedGMS.Forms.ClockTraceApproximation
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceHoldingDivergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupProbabilityKernel
import LatticeProb.Bonanno.ReflectedWalk.Existence

/-! Identify the actual reflected-process occupation resolvent with the full
network resolvent by the finite-target trace limit. The true occupation-clock representation discharges the approximation
premise; the resulting vertex semigroup and transition-law equalities have no
separate form-association hypothesis. -/

-- Merged from `ReflectedGMS/Forms/OccupationResolventComparison.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_OccupationResolventComparison

/-! The precise final comparison step for form/process association.

This file does not prove the original process occupation-resolvent identity.
It proves that this explicitly displayed identity suffices to identify every
vertex transition probability with the actual full-form semigroup kernel.
The outstanding premise is the target of the finite-trace occupation argument.
-/

-- Merged from `ReflectedGMS/Forms/RightContinuousUniqueness.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_RightContinuousUniqueness

/-! Almost-everywhere equality on positive times determines right-continuous
transition functions, including their value at time zero. This is the final
topological adapter after uniqueness of weighted Laplace measures. -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace ReflectedGMS

/-- Lebesgue-a.e. equality on positive times determines any common right limit
at a nonnegative time. No measurability of representatives is needed. -/
theorem eq_of_ae_eq_of_rightContinuousAt {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E} (hfg : f =ᵐ[volume.restrict (Ioi 0)] g)
    {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousWithinAt f (Ici t) t)
    (hg : ContinuousWithinAt g (Ici t) t) : f t = g t := by
  apply tendsto_nhds_unique_of_frequently_eq hf hg
  change ¬ ∀ᶠ u in 𝓝[≥] t, f u ≠ g u
  intro hne
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hne
  have hpos : (volume : Measure ℝ) (Ioo t b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hb)
  obtain ⟨u, hu, heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae (ae_imp_of_ae_restrict hfg))
  exact hsub ⟨hu.1.le, hu.2⟩ (heq (lt_of_le_of_lt ht hu.1))

/-- Right-continuous functions agreeing at almost every positive time agree at
all nonnegative times. -/
theorem eqOn_nonneg_of_ae_eq_of_rightContinuous {E : Type*}
    [TopologicalSpace E] [T2Space E] {f g : ℝ → E}
    (hfg : f =ᵐ[volume.restrict (Ioi 0)] g)
    (hf : ∀ t, 0 ≤ t → ContinuousWithinAt f (Ici t) t)
    (hg : ∀ t, 0 ≤ t → ContinuousWithinAt g (Ici t) t) :
    EqOn f g (Ici 0) :=
  fun t ht => eq_of_ae_eq_of_rightContinuousAt hfg ht (hf t ht) (hg t ht)

end ReflectedGMS

end Merged_RightContinuousUniqueness

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace ReflectedGMS

/-- Positive-parameter Laplace transforms determine bounded nonnegative
right-continuous functions at every nonnegative time. -/
theorem eqOn_nonneg_of_integral_exp_neg_mul_eq
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ t, 0 < t → f t ∈ Icc (0 : ℝ) 1)
    (hgb : ∀ t, 0 < t → g t ∈ Icc (0 : ℝ) 1)
    (hfc : ∀ t, 0 ≤ t → ContinuousWithinAt f (Ici t) t)
    (hgc : ∀ t, 0 ≤ t → ContinuousWithinAt g (Ici t) t)
    (hlap : ∀ alpha : ℝ, 0 < alpha →
      (∫ t in Ioi (0 : ℝ), Real.exp (-alpha * t) * f t) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-alpha * t) * g t) :
    EqOn f g (Ici 0) :=
  eqOn_nonneg_of_ae_eq_of_rightContinuous
    (ae_eq_of_integral_exp_neg_mul_eq f g hf hg
      (fun t ht => (hfb t ht).1) (fun t ht => (hgb t ht).1)
      (fun t ht => (hfb t ht).2) (fun t ht => (hgb t ht).2) hlap) hfc hgc

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u}

/-- Once the actual process occupation integral is identified with the full
resolvent, its vertex transitions equal the analytic semigroup at all times.
The occupation identity is an explicit intermediate premise, not an added
hypothesis of either main theorem. -/
theorem reflected_vertexProbability_eq_semigroupKernel_of_occupationResolvent
    {G : ConductanceGraph V} {w m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (hm : ∀ x, 0 < m x) (x y : V)
    (hoccupation : ∀ alpha : ℝ, 0 < alpha →
      (∫ t in Ioi (0 : ℝ), Real.exp (-alpha * t) *
        (PF.P x {ω | PF.X (Real.toNNReal t) ω = some y}).toReal) =
      (1 / alpha) * unweight m
        (parameterizedResolvent G m (1 / alpha)
          (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))) x)
    (t : ℝ≥0) :
    (PF.P x {ω | PF.X t ω = some y}).toReal = semigroupKernel G m t x y := by
  classical
  let f : ℝ → ℝ := fun s => (PF.P x {ω | PF.X (Real.toNNReal s) ω = some y}).toReal
  let g : ℝ → ℝ := fun s => semigroupKernel G m (Real.toNNReal s) x y
  have hgc : Continuous g :=
    (continuous_semigroupKernel G m hm x y).comp continuous_real_toNNReal
  have hgb (s : ℝ) (_hs : 0 < s) : g s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨semigroupKernel_nonneg G m hm _ x y, ?_⟩
    simpa only [Finset.sum_singleton] using
      semigroupKernel_finset_sum_le_one G m hm (Real.toNNReal s) x {y}
  have heq : EqOn f g (Ici 0) := eqOn_nonneg_of_integral_exp_neg_mul_eq f g
    (measurable_reflected_vertexProbability h x y) hgc.measurable
    (fun s _ => reflected_vertexProbability_mem_Icc PF x y s) hgb
    (fun s _ => reflected_vertexProbability_rightContinuous h x y s)
    (fun _ _ => hgc.continuousWithinAt)
    (fun alpha ha => (hoccupation alpha ha).trans
      (integral_exp_neg_alpha_mul_semigroupKernel G m ha x y).symm)
  simpa only [f, g, Real.toNNReal_coe] using heq (x := (t : ℝ)) t.2

end ReflectedGMS

end Merged_OccupationResolventComparison

-- Merged from `ReflectedGMS/Forms/TraceLaplaceConvergenceAE.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_TraceLaplaceConvergenceAE

/-! Completed stopping times produce a.e.-measurable trace paths. Reuse the
checked measurable-path Laplace convergence theorem through measurable
representatives at each time. The countable approximation index permits one
full-probability agreement event for each fixed time. -/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.TraceLaplaceConvergence

open ReflectedWalk ReflectedWalk.Theorem16

universe u
variable {V Ω : Type u} [MeasurableSpace V] [Countable V]
  [MeasurableSingletonClass V] [MeasurableSpace Ω]

/-- The approximation-to-Laplace step also applies to traces extracted at
completed stopping times, without strengthening a.e. measurability. -/
theorem tendsto_integral_exp_neg_mul_measureReal_of_ae_approximated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → Option V} {Q : ℕ → ℝ≥0 → Ω → Option V}
    (hQm : ∀ n t, AEMeasurable (Q n t) P) (hXm : ∀ t, Measurable (X t))
    (happ : ApproximatedAtFixedTimes P X Q) (y : V)
    (hQt : ∀ n, Measurable fun t : ℝ =>
      (P {ω | Q n (Real.toNNReal t) ω = some y}).toReal)
    (hXt : Measurable fun t : ℝ =>
      (P {ω | X (Real.toNNReal t) ω = some y}).toReal)
    {alpha : ℝ} (ha : 0 < alpha) :
    Tendsto (fun n => ∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      (P {ω | Q n (Real.toNNReal t) ω = some y}).toReal) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
        (P {ω | X (Real.toNNReal t) ω = some y}).toReal)) := by
  let Q' : ℕ → ℝ≥0 → Ω → Option V := fun n t => (hQm n t).mk (Q n t)
  have hrep (n : ℕ) (t : ℝ≥0) : Q n t =ᵐ[P] Q' n t := (hQm n t).ae_eq_mk
  have hprob (n : ℕ) (t : ℝ≥0) :
      P {ω | Q' n t ω = some y} = P {ω | Q n t ω = some y} := by
    apply measure_congr
    filter_upwards [hrep n t] with ω hω
    simp only [hω]
  have happ' : ApproximatedAtFixedTimes P X Q' := by
    intro t
    filter_upwards [happ t, ae_all_iff.mpr (fun n => hrep n t)] with ω hω heq
    filter_upwards [hω] with n hn
    exact (heq n).symm.trans hn
  have hQt' (n : ℕ) : Measurable fun t : ℝ =>
      (P {ω | Q' n (Real.toNNReal t) ω = some y}).toReal := by
    simpa only [hprob] using hQt n
  have hlim := tendsto_integral_exp_neg_mul_measureReal_of_approximated
    (Q := Q') (fun n t => (hQm n t).measurable_mk) hXm happ' y hQt' hXt ha
  simpa only [hprob] using hlim

end ReflectedGMS.TraceLaplaceConvergence

end Merged_TraceLaplaceConvergenceAE

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open TargetTraceTransition TraceLaplaceConvergence

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The original process occupation resolvent follows from actual trace
approximation and the already proved finite occupation-resolvent identity. -/
theorem reflected_occupationResolvent_of_trace_approximation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (E : G.Exhaustion) (x y : V)
    (hx : ∀ n, x ∈ E.Gsub n) (hy : ∀ n, y ∈ E.Gsub n)
    (happ : ApproximatedAtFixedTimes (PF.P x) PF.X
      (fun n => targetTraceProcess PF.X (E.Gsub n) x))
    {alpha : ℝ} (ha : 0 < alpha) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      (PF.P x {ω | PF.X (Real.toNNReal t) ω = some y}).toReal) =
      (1 / alpha) * parameterizedResolventFunction G m (1 / alpha)
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x := by
  classical
  have hw : ∀ v, 0 < G.pi v / m v := fun v =>
    div_pos (G.pi_pos_of_connected hG v) (hm v)
  have hprob := tendsto_integral_exp_neg_mul_measureReal_of_ae_approximated
    (fun n t => aemeasurable_targetTraceProcess h hG (E.nonempty n) (hx n) t)
    PF.measurable_X happ y
    (fun n => measurable_targetTraceProcess_transitionReal h hG hw
      (E.nonempty n) (hx n) y)
    (measurable_reflected_vertexProbability h x y) ha
  have hform := finiteTraceOccupationResolvent_indicator_tendsto
    G hG E m hm hmsum ha x y
  have heq (n : ℕ) :
      (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
        (PF.P x {ω | targetTraceProcess PF.X (E.Gsub n) x
          (Real.toNNReal t) ω = some y}).toReal) =
      (if hx' : x ∈ E.Gsub n then
        finiteTraceOccupationResolvent G hG (E.Gsub n) (E.nonempty n) m alpha
          (weightedValue (fun z : {v // v ∈ E.Gsub n} => m z.1)
            (fun z => G.indic y z.1) (Memℓp.all _)) ⟨x, hx'⟩ else 0) := by
    rw [dite_eq_left (hx n)]
    have hn := targetTraceProcess_laplace_eq_resolvent
      hG (E.Gsub n) (E.nonempty n) m hm h ha ⟨x, hx n⟩ ⟨y, hy n⟩
    rw [finiteTrace_weightedIndicator_eq_restriction G hG (E.Gsub n)
      (E.nonempty n) m (hy n)] at hn
    exact hn
  exact tendsto_nhds_unique hprob (hform.congr' (Eventually.of_forall fun n => (heq n).symm))

/-- The actual reflected path is approximated at each fixed time by its true
finite-target traces. Finiteness and clock divergence are proved from its law. -/
theorem reflected_targetTrace_approximated
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v)
    (E : G.Exhaustion) (x : V) (hx : ∀ n, x ∈ E.Gsub n) :
    ApproximatedAtFixedTimes (PF.P x) PF.X
      (fun n => targetTraceProcess PF.X (E.Gsub n) x) := by
  have hcompat : ∀ᵐ ω ∂PF.P x,
      ClockTraceApproximation.ClockCompatible (fun n => (E.Gsub n : Set V)) PF.X
        (fun n => targetTraceProcess PF.X (E.Gsub n) x) ω := by
    filter_upwards [ae_all_iff.mpr (fun n =>
      TargetReturnRecursion.ae_forall_targetReturnTime_finite_mem
        h hG (E.nonempty n) (hx n)),
      ae_all_iff.mpr (fun n => targetReturnHolding_ae_tsum_eq_top
        h hG hw (E.nonempty n) (hx n))] with ω hreturn hdiv
    intro n u hu
    exact TargetReturnClockCompatibility.targetTrace_at_occupationClock
      (fun j => (hreturn n j).1) (fun j => (hreturn n j).2) (hdiv n) u hu
  exact ClockTraceApproximation.IsReflectedWalk.approximatedAtFixedTimes_of_clockCompatible
    h (fun n k hnk => E.mono hnk) (fun v => E.exists_mem v)
    (fun n => targetTraceProcess PF.X (E.Gsub n) x) x hcompat

/-- The actual reflected-process occupation resolvent is the resolvent of the
full finite-energy form. No process/form identification is assumed. -/
theorem reflected_occupationResolvent
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      (PF.P x {ω | PF.X (Real.toNNReal t) ω = some y}).toReal) =
      (1 / alpha) * parameterizedResolventFunction G m (1 / alpha)
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x := by
  classical
  obtain ⟨E⟩ := Existence.exists_exhaustion hG
  obtain ⟨N, hN⟩ := E.exists_subset {x, y}
  let E' := E.shift N
  have hx (n : ℕ) : x ∈ E'.Gsub n := hN (n + N) (by omega) (by simp)
  have hy (n : ℕ) : y ∈ E'.Gsub n := hN (n + N) (by omega) (by simp)
  have hw : ∀ v, 0 < G.pi v / m v := fun v =>
    div_pos (G.pi_pos_of_connected hG v) (hm v)
  exact reflected_occupationResolvent_of_trace_approximation h hG hm hmsum E' x y
    hx hy (reflected_targetTrace_approximated h hG hw E' x hx) ha

/-- Actual reflected-walk transitions equal the full-form semigroup at every
vertex and every nonnegative time, including time zero. -/
theorem reflected_vertexProbability_eq_semigroupKernel
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x y : V) :
    (PF.P x {ω | PF.X t ω = some y}).toReal = semigroupKernel G m t x y := by
  exact reflected_vertexProbability_eq_semigroupKernel_of_occupationResolvent h hm x y
    (fun alpha ha => reflected_occupationResolvent h hG hm hmsum ha x y) t

/-- Reversibility of the actual reflected transition probabilities with
respect to the summable fast speed. -/
theorem reflected_transition_detailedBalance
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x y : V) :
    m x * (PF.P x {ω | PF.X t ω = some y}).toReal =
      m y * (PF.P y {ω | PF.X t ω = some x}).toReal := by
  classical
  rw [reflected_vertexProbability_eq_semigroupKernel h hG hm hmsum,
    reflected_vertexProbability_eq_semigroupKernel h hG hm hmsum]
  exact semigroupKernel_detailedBalance G m hm t x y

open Classical in
/-- Equality of the full one-time transition laws, including the null mass of
`none`, with the probability kernel constructed from the full form. -/
theorem reflected_transitionLaw_eq_semigroupProbabilityKernel
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x : V) :
    (PF.P x).map (PF.X t) =
      (semigroupProbabilityKernel G m hm hmsum t x).map (some : V → Option V) := by
  have hsome : Measurable (some : V → Option V) := measurable_of_countable _
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (PF.measurable_X t) (measurableSet_singleton z),
    Measure.map_apply hsome (measurableSet_singleton z)]
  cases z with
  | none =>
      have hz : PF.P x {ω | PF.X t ω = none} = 0 := by
        calc
          _ = PF.P x ∅ := by
            apply measure_congr
            filter_upwards [(h x).2.1 t] with ω hω
            obtain ⟨y, hy⟩ := hω.1
            simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
            rw [hy]
            simp
          _ = 0 := measure_empty
      simpa only [Set.preimage, Set.mem_singleton_iff, Option.some_ne_none,
        Set.setOf_false, measure_empty] using hz
  | some y =>
      have heq : PF.P x {ω | PF.X t ω = some y} =
          semigroupProbabilityKernel G m hm hmsum t x {y} := by
        rw [semigroupProbabilityKernel_apply_singleton,
          ← reflected_vertexProbability_eq_semigroupKernel h hG hm hmsum t x y,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
      simpa only [Set.preimage, Set.mem_singleton_iff, Option.some.injEq,
        Set.setOf_eq_eq_singleton] using heq

end ReflectedGMS

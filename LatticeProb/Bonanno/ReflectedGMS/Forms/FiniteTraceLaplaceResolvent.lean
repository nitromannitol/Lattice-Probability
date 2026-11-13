/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceLaplaceResolvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.JumpPathOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.TraceLaplaceConvergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceOccupationPotential

/-!
# Laplace transform of the canonical finite induced chain

Tonelli identifies the scalar transition-probability transform of the
canonical jump path with its expected literal occupation.  The checked
pathwise holding-series identity and finite-trace occupation identification
then give the analytic finite-trace resolvent.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.ContinuousTimeChain FullNetworkForm

universe u

variable {V : Type u} [MeasurableSpace V] [Countable V]
  [MeasurableSingletonClass V] [Nontrivial V]

private theorem lintegral_discountedVertexOccupation_jumpPath
    (P : Measure ((ℕ → V) × (ℕ → ℝ))) [SFinite P]
    (alpha : ℝ) (y : V) :
    (∫⁻ p, discountedVertexOccupation (fun t p => jumpPath p t) alpha y p ∂P) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-alpha * t)) *
        P {p | jumpPath p (Real.toNNReal t) = some y} := by
  let H : ((ℕ → V) × (ℕ → ℝ)) → ℝ → ℝ≥0∞ := fun p t =>
    {s : ℝ | jumpPath p (Real.toNNReal s) = some y}.indicator
      (fun s => ENNReal.ofReal (Real.exp (-alpha * s))) t
  have hset : MeasurableSet
      {q : ((ℕ → V) × (ℕ → ℝ)) × ℝ |
        jumpPath q.1 (Real.toNNReal q.2) = some y} := by
    exact (TraceLaplaceConvergence.measurableSet_jumpPath_real_eq_some y).preimage
      measurable_swap
  have hH : Measurable (Function.uncurry H) := by
    change Measurable
      ({q : ((ℕ → V) × (ℕ → ℝ)) × ℝ |
          jumpPath q.1 (Real.toNNReal q.2) = some y}.indicator
        (fun q => ENNReal.ofReal (Real.exp (-alpha * q.2))))
    exact (by fun_prop : Measurable fun q : ((ℕ → V) × (ℕ → ℝ)) × ℝ =>
      ENNReal.ofReal (Real.exp (-alpha * q.2))).indicator hset
  change (∫⁻ p, ∫⁻ t : ℝ in Ioi 0, H p t ∂volume ∂P) = _
  rw [lintegral_lintegral_swap hH.aemeasurable]
  apply lintegral_congr
  intro t
  change (∫⁻ p,
    {p | jumpPath p (Real.toNNReal t) = some y}.indicator
      (fun _ => ENNReal.ofReal (Real.exp (-alpha * t))) p ∂P) = _
  exact lintegral_indicator_const
    (measurable_prodMk_left
      (TraceLaplaceConvergence.measurableSet_jumpPath_real_eq_some y)) _

private theorem expected_jumpPathOccupation_eq_expectedSeries
    (κ : Kernel V V) [IsMarkovKernel κ] (w : V → ℝ) (hw : ∀ z, 0 < w z)
    {alpha : ℝ} (halpha : 0 < alpha) (x y : V) :
    (∫⁻ p, discountedVertexOccupation (fun t p => jumpPath p t) alpha y p
      ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w)) =
      finiteTraceExpectedOccupation κ w alpha (fun z => if z = y then 1 else 0) x := by
  unfold finiteTraceExpectedOccupation
  apply lintegral_congr_ae
  have hp : MeasurableSet
      {p : (ℕ → V) × (ℕ → ℝ) | ∀ n, 0 ≤ p.2 n} := by
    rw [show {p : (ℕ → V) × (ℕ → ℝ) | ∀ n, 0 ≤ p.2 n} =
        ⋂ n : ℕ, {p : (ℕ → V) × (ℕ → ℝ) | 0 ≤ p.2 n} by
      ext p
      simp]
    exact MeasurableSet.iInter fun n => measurableSet_Ici.preimage
      ((measurable_pi_apply n).comp measurable_snd)
  have hnonneg : ∀ᵐ p ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w),
      ∀ n, 0 ≤ p.2 n := by
    apply Measure.ae_compProd_of_ae_ae hp
    exact ae_of_all _ fun path => holdingKernel_ae_nonneg hw path
  filter_upwards [hnonneg] with p hT
  exact discountedVertexOccupation_jumpPath_eq_series p halpha hT y

private theorem jumpPath_laplace_eq_expectedOccupation
    (κ : Kernel V V) [IsMarkovKernel κ] (w : V → ℝ) (hw : ∀ z, 0 < w z)
    {alpha : ℝ} (halpha : 0 < alpha) (x y : V) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      ((MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w)
        {p | jumpPath p (Real.toNNReal t) = some y}).toReal) =
      (finiteTraceExpectedOccupation κ w alpha
        (fun z => if z = y then 1 else 0) x).toReal := by
  let P := MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w
  let f : ℝ → ℝ := fun t => Real.exp (-alpha * t) *
    (P {p | jumpPath p (Real.toNNReal t) = some y}).toReal
  have hfm : Measurable f :=
    (measurable_const.mul measurable_id).exp.mul
      ((TraceLaplaceConvergence.measurable_jumpPath_vertexProbability P y).ennreal_toReal)
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos halpha) 0).mono'
      hfm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
      ENNReal.toReal_nonneg)]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) <| by
      calc
        (P {p | jumpPath p (Real.toNNReal t) = some y}).toReal ≤
            (P Set.univ).toReal :=
          ENNReal.toReal_mono (by simp) (measure_mono (subset_univ _))
        _ = 1 := by simp
  have htonelli := lintegral_discountedVertexOccupation_jumpPath P alpha y
  have hseries := expected_jumpPathOccupation_eq_expectedSeries κ w hw halpha x y
  rw [hseries] at htonelli
  have hnonneg : 0 ≤ ∫ t : ℝ in Ioi 0, f t :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun t =>
      mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg)
  rw [← ENNReal.toReal_ofReal_eq_iff.mpr hnonneg]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hfi
    (Filter.Eventually.of_forall fun t =>
      mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg)]
  calc
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (f t)) =
        ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-alpha * t)) *
          P {p | jumpPath p (Real.toNNReal t) = some y} := by
      apply lintegral_congr
      intro t
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = _ := htonelli.symm

/-- The scalar transition Laplace transform of the canonical finite induced
chain equals the occupation-normalized finite-trace resolvent applied to the
weighted indicator of the target vertex. -/
theorem finiteTrace_jumpPath_laplace_eq_resolvent
    (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {alpha : ℝ} (halpha : 0 < alpha) (x y : {v // v ∈ A}) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      ((MarkovChain.chainLaw (G.inducedKernel hG hA) x.1 ⊗ₘ
          holdingKernel (fun v => G.pi v / m v))
        {p | jumpPath p (Real.toNNReal t) = some y.1}).toReal) =
      finiteTraceOccupationResolvent G hG A hA m alpha
        (weightedValue (fun z : {v // v ∈ A} => m z.1)
          ((finiteTargetGraph G hG A hA).indic y)
          (VertexTest.indic_hasSpeedL2 (finiteTargetGraph G hG A hA)
            (fun z : {v // v ∈ A} => m z.1) y)) x := by
  let w : V → ℝ := fun v => G.pi v / m v
  have hw : ∀ z, 0 < w z := fun z =>
    div_pos (G.pi_pos_of_connected hG z) (hm z)
  rw [jumpPath_laplace_eq_expectedOccupation
    (G.inducedKernel hG hA) w hw halpha x.1 y.1]
  have hid := congrFun
    (finiteTraceExpectedOccupation_eq_resolvent G hG A hA m hm halpha
      (G.indic y.1)
      (fun z => by by_cases hzy : z = y.1 <;> simp [ConductanceGraph.indic, hzy])
      (fun z => by by_cases hzy : z = y.1 <;> simp [ConductanceGraph.indic, hzy])) x
  change
    (finiteTraceExpectedOccupation (G.inducedKernel hG hA)
      (fun v => G.pi v / m v) alpha (G.indic y.1) x.1).toReal = _
  rw [hid]
  congr 2
  funext z
  by_cases hzy : z = y
  · subst z
    simp [ConductanceGraph.indic]
  · simp [ConductanceGraph.indic, hzy]

end ReflectedGMS

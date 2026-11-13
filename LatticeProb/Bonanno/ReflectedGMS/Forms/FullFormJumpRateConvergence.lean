/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullFormJumpRateConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.JumpRateEnergyContinuity
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingaleLimit

/-!
# Full-form convergence of ordinary-edge jump rates

Convergence in the full Hilbert form norm implies `L¹(vertexSpeedMeasure m)`
convergence of the canonical real ordinary-edge square-increment rates.  We
then specialize this analytic statement to the geometric resolvent-core
approximants used by `fullEnergyMartingaleApprox`.

This file makes no process, bracket, or covariance assertion.
-/

set_option autoImplicit false

open Filter MeasureTheory Topology

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V]

private theorem decode_sub (G : ConductanceGraph V) (m : V → ℝ)
    (U W : hilbertDomain G m) :
    unweight m (valueInclusion G m (U - W)) =
      unweight m (valueInclusion G m U) -
        unweight m (valueInclusion G m W) := by
  funext x
  simp only [map_sub, unweight, lp.coeFn_sub, Pi.sub_apply]
  ring

private theorem decode_add (G : ConductanceGraph V) (m : V → ℝ)
    (U W : hilbertDomain G m) :
    unweight m (valueInclusion G m (U + W)) =
      unweight m (valueInclusion G m U) +
        unweight m (valueInclusion G m W) := by
  funext x
  simp only [map_add, unweight, lp.coeFn_add, Pi.add_apply]
  ring

private theorem sqrt_energy_decode_eq_gradient_norm
    (G : ConductanceGraph V) (m : V → ℝ) (U : hilbertDomain G m) :
    Real.sqrt (G.Energy (unweight m (valueInclusion G m U))) =
      ‖gradientInclusion G m U‖ := by
  rw [← weightedGradient_norm_sq G
    (unweight m (valueInclusion G m U))
    (hilbertDomain_hasFiniteEnergy G m U),
    ← gradientInclusion_eq G m U, Real.sqrt_sq (norm_nonneg _)]

/-- Full Hilbert form-norm convergence implies speed-`L¹` convergence of the
canonical real ordinary-edge square-increment rates. -/
theorem fullForm_jumpRate_integral_norm_tendsto
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ x, 0 < m x)
    (U : hilbertDomain G m) (Un : ℕ → hilbertDomain G m)
    (hUn : Tendsto Un atTop (nhds U)) :
    Tendsto (fun n ↦
      ∫ x : V,
        ‖(stateVertexCarreDuChamp G m
              (unweight m (valueInclusion G m (Un n))) (some x)).toReal -
          (stateVertexCarreDuChamp G m
              (unweight m (valueInclusion G m U)) (some x)).toReal‖
        ∂vertexSpeedMeasure m) atTop (nhds 0) := by
  let d : ℕ → hilbertDomain G m := fun n ↦ Un n - U
  let s : ℕ → hilbertDomain G m := fun n ↦ Un n + U
  have hd : Tendsto d atTop (nhds 0) := by
    simpa only [d, sub_self] using hUn.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ U) atTop (nhds U))
  have hs : Tendsto s atTop (nhds (U + U)) :=
    hUn.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ U) atTop (nhds U))
  have hgradD : Tendsto (fun n ↦ ‖gradientInclusion G m (d n)‖)
      atTop (nhds 0) := by
    have hmap := (gradientInclusion G m).continuous.continuousAt.tendsto.comp hd
    simpa only [Function.comp_apply, map_zero, norm_zero] using hmap.norm
  have hgradS : Tendsto (fun n ↦ ‖gradientInclusion G m (s n)‖)
      atTop (nhds ‖gradientInclusion G m (U + U)‖) := by
    exact ((gradientInclusion G m).continuous.continuousAt.tendsto.comp hs).norm
  have hbound : ∀ n,
      (∫ x : V,
        ‖(stateVertexCarreDuChamp G m
              (unweight m (valueInclusion G m (Un n))) (some x)).toReal -
          (stateVertexCarreDuChamp G m
              (unweight m (valueInclusion G m U)) (some x)).toReal‖
        ∂vertexSpeedMeasure m) ≤
        2 * ‖gradientInclusion G m (d n)‖ *
          ‖gradientInclusion G m (s n)‖ := by
    intro n
    have h := integral_norm_stateVertexCarreDuChamp_toReal_sub_le G m hm
      (hilbertDomain_hasFiniteEnergy G m (Un n))
      (hilbertDomain_hasFiniteEnergy G m U)
    rw [← decode_sub G m (Un n) U,
      sqrt_energy_decode_eq_gradient_norm G m (d n),
      ← decode_add G m (Un n) U,
      sqrt_energy_decode_eq_gradient_norm G m (s n)] at h
    exact h
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _
  · exact Eventually.of_forall hbound
  · convert (tendsto_const_nhds.mul hgradD).mul hgradS using 1 <;> simp

/-- The canonical even-index resolvent-core features used in the full-energy
martingale approximation have jump rates converging in
`L¹(vertexSpeedMeasure m)` to the rate of the decoded full-domain vector. -/
theorem fullEnergyCore_jumpRate_integral_norm_tendsto
    [Nontrivial V] (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ x, 0 < m x)
    (U : hilbertDomain G m) :
    Tendsto (fun n ↦
      ∫ x : V,
        ‖(stateVertexCarreDuChamp G m
              (countableResolventCoreFeature G m
                (fullEnergyCoreIndex G m hm U (2 * n))) (some x)).toReal -
          (stateVertexCarreDuChamp G m
              (unweight m (valueInclusion G m U)) (some x)).toReal‖
        ∂vertexSpeedMeasure m) atTop (nhds 0) := by
  let Un : ℕ → hilbertDomain G m := fun n ↦
    countableResolventCoreVector G m
      (fullEnergyCoreIndex G m hm U (2 * n))
  have hbound : ∀ n, ‖Un n - U‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    exact (fullEnergyCoreIndex_bound G m hm U (2 * n)).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_mul_of_pos_left n (by norm_num)))
  have hUn : Tendsto Un atTop (nhds U) :=
    countableResolventCoreVector_tendsto_of_geometric_bound G m U
      (fun n ↦ fullEnergyCoreIndex G m hm U (2 * n)) hbound
  have h := fullForm_jumpRate_integral_norm_tendsto G m hm U Un hUn
  have hdecode : ∀ n,
      unweight m (valueInclusion G m (Un n)) =
        countableResolventCoreFeature G m
          (fullEnergyCoreIndex G m hm U (2 * n)) := by
    intro n
    rw [show Un n = countableResolventCoreVector G m
        (fullEnergyCoreIndex G m hm U (2 * n)) from rfl,
      countableResolventCoreVector_eq_inHilbertDomain G m hm,
      valueInclusion_inHilbertDomain, unweight_weightedValue m hm]
  simpa only [hdecode] using h

end ReflectedGMS

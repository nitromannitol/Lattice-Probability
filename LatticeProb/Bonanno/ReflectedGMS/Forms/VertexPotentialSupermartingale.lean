/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexPotentialSupermartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexResolventExcessive
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIdentification
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedMarkovConditional
import Mathlib.Probability.Martingale.Basic

/-!
# Supermartingale from the vertex occupation potential

The bounded real version of the vertex-potential excessivity inequality, and
its application to the actual reflected walk.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- A vertex occupation potential is nonnegative. -/
theorem vertexOccupationPotential_nonneg
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    0 ≤ vertexOccupationPotential G m alpha x y := by
  apply integral_nonneg_of_ae
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦
    mul_nonneg (Real.exp_nonneg _)
      (semigroupKernel_nonneg G m hm (Real.toNNReal t) x y)

/-- The potential of a single vertex is bounded by the total discounted
occupation mass. -/
theorem vertexOccupationPotential_le_inv
    [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    vertexOccupationPotential G m alpha x y ≤ 1 / alpha := by
  have hk (t : ℝ) : semigroupKernel G m (Real.toNNReal t) x y ≤ 1 := by
    simpa only [Finset.sum_singleton] using
      semigroupKernel_finset_sum_le_one G m hm (Real.toNNReal t) x {y}
  have hleft := integrableOn_exp_neg_alpha_mul_semigroupKernel G m ha x y
  have hright : IntegrableOn (fun t : ℝ ↦ Real.exp (-alpha * t)) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  calc
    vertexOccupationPotential G m alpha x y
        ≤ ∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) := by
          apply setIntegral_mono_on hleft hright measurableSet_Ioi
          intro t _
          exact mul_le_of_le_one_right (Real.exp_nonneg _) (hk t)
    _ = 1 / alpha := by
      rw [show (fun t : ℝ ↦ Real.exp (-alpha * t)) =
          (fun t : ℝ ↦ Real.exp ((-alpha) * t)) by rfl,
        integral_exp_mul_Ioi (neg_lt_zero.mpr ha) 0]
      simp only [mul_zero, neg_zero, Real.exp_zero]
      ring

/-- ENNReal excessivity expressed as integration against the analytic
probability kernel. -/
theorem vertexOccupationPotentialENN_kernel_excessive
    [DecidableEq V] [Countable V] [MeasurableSpace V]
    [DiscreteMeasurableSpace V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    {alpha : ℝ} (ha : 0 < alpha) (s : ℝ≥0) (x y : V) :
    ENNReal.ofReal (Real.exp (-alpha * (s : ℝ))) *
        ∫⁻ z, vertexOccupationPotentialENN G m alpha z y
          ∂semigroupProbabilityKernel G m hm hmsum s x ≤
      vertexOccupationPotentialENN G m alpha x y := by
  rw [lintegral_countable']
  simp only [semigroupProbabilityKernel_apply_singleton]
  simpa only [mul_comm] using
    vertexOccupationPotentialENN_excessive G m hm hmsum ha s x y

/-- Real bounded excessivity of the vertex potential, in probability-kernel
integral form. -/
theorem vertexOccupationPotential_kernel_excessive
    [DecidableEq V] [Countable V] [MeasurableSpace V]
    [DiscreteMeasurableSpace V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    {alpha : ℝ} (ha : 0 < alpha) (s : ℝ≥0) (x y : V) :
    Real.exp (-alpha * (s : ℝ)) *
        ∫ z, vertexOccupationPotential G m alpha z y
          ∂semigroupProbabilityKernel G m hm hmsum s x ≤
      vertexOccupationPotential G m alpha x y := by
  let K := semigroupProbabilityKernel G m hm hmsum s x
  have hU0 (z : V) : 0 ≤ vertexOccupationPotential G m alpha z y :=
    vertexOccupationPotential_nonneg G m hm ha z y
  have hUb (z : V) : vertexOccupationPotential G m alpha z y ≤ 1 / alpha :=
    vertexOccupationPotential_le_inv G m hm ha z y
  have hUint : Integrable (fun z ↦ vertexOccupationPotential G m alpha z y) K := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (1 / alpha)
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hU0 z)]
      exact hUb z
  have hlift : ENNReal.ofReal (∫ z, vertexOccupationPotential G m alpha z y ∂K) =
      ∫⁻ z, vertexOccupationPotentialENN G m alpha z y ∂K := by
    rw [ofReal_integral_eq_lintegral_ofReal hUint (ae_of_all K hU0)]
    apply lintegral_congr
    intro z
    exact (vertexOccupationPotentialENN_eq_ofReal G m hm ha z y).symm
  have h := vertexOccupationPotentialENN_kernel_excessive G m hm hmsum ha s x y
  change ENNReal.ofReal (Real.exp (-alpha * (s : ℝ))) *
      (∫⁻ z, vertexOccupationPotentialENN G m alpha z y ∂K) ≤
    vertexOccupationPotentialENN G m alpha x y at h
  rw [← hlift, vertexOccupationPotentialENN_eq_ofReal G m hm ha x y,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (hU0 x)).mp h

end ReflectedGMS.FullNetworkForm

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The current state is measurable with respect to the actual natural
filtration at the current time. -/
private theorem measurable_X_naturalFiltration (PF : ProcessFamily V) (t : ℝ≥0) :
    Measurable[PF.naturalFiltration t] (PF.X t) := by
  change Measurable[pastSigma PF.X t] (PF.X t)
  intro A hA
  apply measurableSet_pastSigma_iff.mpr
  refine ⟨{p | p ⟨t, by simp⟩ ∈ A}, ?_, rfl⟩
  exact hA.preimage (measurable_pi_apply _)

/-- The actual one-time expectation of the bounded vertex potential equals
integration against the identified analytic transition kernel. -/
theorem integral_reflected_vertexOccupationPotential_at_time [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha)
    (t : ℝ≥0) (x y : V) :
    (∫ ω, (PF.X t ω).elim 0 (vertexOccupationPotential G m alpha · y) ∂PF.P x) =
      ∫ z, vertexOccupationPotential G m alpha z y
        ∂semigroupProbabilityKernel G m hm hmsum t x := by
  let g : Option V → ℝ := fun z ↦
    z.elim 0 (vertexOccupationPotential G m alpha · y)
  have hg : Measurable g := measurable_of_countable _
  have hsome : Measurable (some : V → Option V) := measurable_of_countable _
  calc
    (∫ ω, (PF.X t ω).elim 0 (vertexOccupationPotential G m alpha · y) ∂PF.P x) =
        ∫ z, g z ∂(PF.P x).map (PF.X t) := by
      simpa only [g, Function.comp_apply] using
        (integral_map (PF.measurable_X t).aemeasurable
          hg.aestronglyMeasurable).symm
    _ = ∫ z, g z ∂(semigroupProbabilityKernel G m hm hmsum t x).map
          (some : V → Option V) := by
      exact congrArg (fun μ : Measure (Option V) ↦ ∫ z, g z ∂μ)
        (reflected_transitionLaw_eq_semigroupProbabilityKernel
          h hG hm hmsum t x)
    _ = ∫ z, vertexOccupationPotential G m alpha z y
          ∂semigroupProbabilityKernel G m hm hmsum t x := by
      simpa only [g, Function.comp_apply, Option.elim_some] using
        integral_map hsome.aemeasurable hg.aestronglyMeasurable

/-- The discounted potential evaluated along the path is strongly adapted to
the actual natural filtration. -/
theorem stronglyAdapted_discountedVertexOccupationPotential
    (PF : ProcessFamily V)
    (G : ConductanceGraph V) (m : V → ℝ) (alpha : ℝ) (y : V) :
    StronglyAdapted PF.naturalFiltration
      (fun t ω ↦ Real.exp (-alpha * (t : ℝ)) *
        (PF.X t ω).elim 0 (vertexOccupationPotential G m alpha · y)) := by
  intro t
  let g : Option V → ℝ := fun z ↦
    z.elim 0 (vertexOccupationPotential G m alpha · y)
  have hg : Measurable g := measurable_of_countable _
  have hstate : Measurable[PF.naturalFiltration t] (fun ω ↦ g (PF.X t ω)) :=
    hg.comp (measurable_X_naturalFiltration PF t)
  have hc : Measurable[PF.naturalFiltration t]
      (fun _ : PF.Ω ↦ Real.exp (-alpha * (t : ℝ))) := measurable_const
  exact (hc.mul hstate).stronglyMeasurable

/-- For every starting vertex, the discounted potential of a fixed vertex is
a supermartingale in the actual natural filtration. -/
theorem reflected_vertexOccupationPotential_supermartingale [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V) :
    Supermartingale
      (fun (t : ℝ≥0) ω ↦ Real.exp (-alpha * (t : ℝ)) *
        (PF.X t ω).elim 0 (vertexOccupationPotential G m alpha · y))
      PF.naturalFiltration (PF.P z) := by
  let U : V → ℝ := fun x ↦ vertexOccupationPotential G m alpha x y
  have hU0 (x : V) : 0 ≤ U x := vertexOccupationPotential_nonneg G m hm ha x y
  have hUb (x : V) : U x ≤ 1 / alpha :=
    vertexOccupationPotential_le_inv G m hm ha x y
  have hstrong : StronglyAdapted PF.naturalFiltration
      (fun (t : ℝ≥0) ω ↦
        Real.exp (-alpha * (t : ℝ)) * (PF.X t ω).elim 0 U) := by
    simpa only [U] using
      stronglyAdapted_discountedVertexOccupationPotential PF G m alpha y
  refine ⟨hstrong, ?_, ?_⟩
  · intro s t hst
    let f : V → ℝ := fun x ↦ Real.exp (-alpha * (t : ℝ)) * U x
    let C : ℝ := Real.exp (-alpha * (t : ℝ)) * (1 / alpha)
    have hf (x : V) : ‖f x‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_nonneg _) (hU0 x))]
      exact mul_le_mul_of_nonneg_left (hUb x) (Real.exp_nonneg _)
    have hce := ReflectedMarkovConditional.condExp_vertex_test
      h z hst f C hf
    have heval :
        (fun ω ↦ Real.exp (-alpha * (t : ℝ)) * (PF.X t ω).elim 0 U) =ᵐ[PF.P z]
          fun ω ↦ (PF.X t ω).elim 0 f := by
      filter_upwards [] with ω
      cases PF.X t ω <;> simp [f]
    have hce' := (condExp_congr_ae heval).trans hce
    apply hce'.trans_le
    filter_upwards [] with ω
    cases hx : PF.X s ω with
    | none => simp [f, hx]
    | some x =>
        have hkernel : Real.exp (-alpha * ((t - s : ℝ≥0) : ℝ)) *
              ∫ q, U q ∂semigroupProbabilityKernel G m hm hmsum (t - s) x ≤ U x := by
          simpa only [U] using vertexOccupationPotential_kernel_excessive
            G m hm hmsum ha (t - s) x y
        have hfuture :
            (∫ ω', (PF.X (t - s) ω').elim 0 f ∂PF.P x) =
              Real.exp (-alpha * (t : ℝ)) *
                ∫ q, U q ∂semigroupProbabilityKernel G m hm hmsum (t - s) x := by
          calc
            (∫ ω', (PF.X (t - s) ω').elim 0 f ∂PF.P x) =
                ∫ ω', Real.exp (-alpha * (t : ℝ)) *
                  (PF.X (t - s) ω').elim 0 U ∂PF.P x := by
                    apply integral_congr_ae
                    filter_upwards [] with ω'
                    cases PF.X (t - s) ω' <;> simp [f]
            _ = Real.exp (-alpha * (t : ℝ)) *
                  ∫ ω', (PF.X (t - s) ω').elim 0 U ∂PF.P x :=
                by rw [integral_const_mul]
            _ = Real.exp (-alpha * (t : ℝ)) *
                  ∫ q, U q ∂semigroupProbabilityKernel G m hm hmsum (t - s) x := by
                    congr 1
                    simpa only [U] using
                      integral_reflected_vertexOccupationPotential_at_time
                        h hG hm hmsum ha (t - s) x y
        simp only [Option.elim_some]
        rw [hfuture]
        have htime : (t : ℝ) = (s : ℝ) + ((t - s : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_sub hst]
          linarith
        have hexp : Real.exp (-alpha * (t : ℝ)) =
            Real.exp (-alpha * (s : ℝ)) *
              Real.exp (-alpha * ((t - s : ℝ≥0) : ℝ)) := by
          rw [htime, ← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        calc
          (Real.exp (-alpha * (s : ℝ)) *
              Real.exp (-alpha * ((t - s : ℝ≥0) : ℝ))) *
                ∫ q, U q ∂semigroupProbabilityKernel G m hm hmsum (t - s) x =
              Real.exp (-alpha * (s : ℝ)) *
                (Real.exp (-alpha * ((t - s : ℝ≥0) : ℝ)) *
                  ∫ q, U q ∂semigroupProbabilityKernel G m hm hmsum (t - s) x) := by
                    ring
          _ ≤ Real.exp (-alpha * (s : ℝ)) * U x :=
            mul_le_mul_of_nonneg_left hkernel (Real.exp_nonneg _)
  · intro t
    let g : Option V → ℝ := fun q ↦
      Real.exp (-alpha * (t : ℝ)) * q.elim 0 U
    have hg : Measurable g := measurable_of_countable _
    apply Integrable.of_bound
      (hg.comp (PF.measurable_X t)).aestronglyMeasurable
      (Real.exp (-alpha * (t : ℝ)) * (1 / alpha))
    filter_upwards [] with ω
    cases hx : PF.X t ω with
    | none =>
        simp only [Function.comp_apply, hx, g, Option.elim_none, mul_zero, norm_zero]
        exact mul_nonneg (Real.exp_nonneg _) (by positivity : 0 ≤ 1 / alpha)
    | some x =>
        rw [show (g ∘ PF.X t) ω = Real.exp (-alpha * (t : ℝ)) * U x by
              simp [g, hx], Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (Real.exp_nonneg _) (hU0 x))]
        exact mul_le_mul_of_nonneg_left (hUb x) (Real.exp_nonneg _)

end ReflectedGMS

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryGridMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedMarkovConditional
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryPotentialVariance
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinEnergy
import Mathlib.Probability.Martingale.Centering

/-!
# The stationary discrete-grid martingale

For a bounded decoded full-form vector, this file identifies Mathlib's
`martingalePart` on a deterministic time grid with the semigroup-compensated
potential.  The terminal second-moment estimate is a separate continuation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators InnerProductSpace NNReal ENNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/- The deterministic nonnegative-time grid. -/
def stationaryGridTime (δ : ℝ≥0) (n : ℕ) : ℝ≥0 := (n : ℝ≥0) * δ

/- The actual natural filtration restricted to a deterministic grid. -/
noncomputable def stationaryGridFiltration (PF : ProcessFamily V) (δ : ℝ≥0) :
    Filtration ℕ (inferInstance : MeasurableSpace PF.Ω) where
  seq n := PF.naturalFiltration (stationaryGridTime δ n)
  mono' := fun _ _ h => PF.naturalFiltration.mono
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) δ.2)
  le' n := PF.naturalFiltration.le (stationaryGridTime δ n)

/- The raw `Option`-valued process decoded by a full weighted `L²` vector. -/
noncomputable def stationaryGridPotential
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) : ℕ → PF.Ω → ℝ :=
  fun n ω => (PF.X (stationaryGridTime δ n) ω).elim 0
    (unweight m (valueInclusion G m U))

/- One-step analytic semigroup drift, decoded at the current grid state. -/
noncomputable def stationaryGridDrift
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) : ℕ → PF.Ω → ℝ :=
  fun n ω => (PF.X (stationaryGridTime δ n) ω).elim 0
    (unweight m
      (fullFormSemigroup G m δ (valueInclusion G m U) - valueInclusion G m U))

/- The centered Doob martingale on the stationary grid.  The Doob
decomposition itself is Mathlib's `martingalePart`. -/
noncomputable def stationaryGridMartingale
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) : ℕ → PF.Ω → ℝ :=
  fun n => martingalePart (stationaryGridPotential PF G m U δ)
      (stationaryGridFiltration PF δ) (reflectedSpeedLaw PF m) n -
    stationaryGridPotential PF G m U δ 0

private theorem measurable_X_naturalFiltration
    (PF : ProcessFamily V) (t : ℝ≥0) :
    Measurable[PF.naturalFiltration t] (PF.X t) := by
  change Measurable[pastSigma PF.X t] (PF.X t)
  intro A hA
  apply measurableSet_pastSigma_iff.mpr
  refine ⟨{p | p ⟨t, by simp⟩ ∈ A}, ?_, rfl⟩
  exact hA.preimage (measurable_pi_apply _)

theorem stronglyAdapted_stationaryGridPotential
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) :
    StronglyAdapted (stationaryGridFiltration PF δ)
      (stationaryGridPotential PF G m U δ) := by
  intro n
  change StronglyMeasurable[PF.naturalFiltration (stationaryGridTime δ n)]
    (fun ω => (PF.X (stationaryGridTime δ n) ω).elim 0
      (unweight m (valueInclusion G m U)))
  exact ((measurable_of_countable
    (fun q : Option V => q.elim 0 (unweight m (valueInclusion G m U)))).comp
      (measurable_X_naturalFiltration PF (stationaryGridTime δ n))).stronglyMeasurable

theorem integrable_stationaryGridPotential
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (n : ℕ) :
    Integrable (stationaryGridPotential PF G m U δ n)
      (reflectedSpeedLaw PF m) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  exact (memLp_two_reflected_unweight_speedLaw h hG hm hmsum
    (valueInclusion G m U) (stationaryGridTime δ n)).integrable (by norm_num)

private theorem stationaryGridTime_succ_sub (δ : ℝ≥0) (n : ℕ) :
    stationaryGridTime δ (n + 1) - stationaryGridTime δ n = δ := by
  simp only [stationaryGridTime, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
    add_tsub_cancel_left]

/- Under the unnormalized stationary mixture, the next grid potential has
conditional expectation given by the actual full-form semigroup. -/
theorem condExp_stationaryGridPotential_succ
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (n : ℕ) :
    (reflectedSpeedLaw PF m)[stationaryGridPotential PF G m U δ (n + 1) |
        stationaryGridFiltration PF δ n] =ᵐ[reflectedSpeedLaw PF m]
      fun ω => (PF.X (stationaryGridTime δ n) ω).elim 0
        (unweight m (fullFormSemigroup G m δ (valueInclusion G m U))) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let lhs := stationaryGridPotential PF G m U δ (n + 1)
  let rhs : PF.Ω → ℝ := fun ω =>
    (PF.X (stationaryGridTime δ n) ω).elim 0
      (unweight m (fullFormSemigroup G m δ (valueInclusion G m U)))
  have hlhs : Integrable lhs (reflectedSpeedLaw PF m) :=
    integrable_stationaryGridPotential h hG hm hmsum U δ (n + 1)
  have hrhs : Integrable rhs (reflectedSpeedLaw PF m) := by
    exact (memLp_two_reflected_unweight_speedLaw h hG hm hmsum
      (fullFormSemigroup G m δ (valueInclusion G m U))
      (stationaryGridTime δ n)).integrable (by norm_num)
  have hrhs_meas : StronglyMeasurable[stationaryGridFiltration PF δ n] rhs :=
    by
      change StronglyMeasurable[PF.naturalFiltration (stationaryGridTime δ n)]
        (fun ω => (PF.X (stationaryGridTime δ n) ω).elim 0
          (unweight m (fullFormSemigroup G m δ (valueInclusion G m U))))
      exact ((measurable_of_countable
      (fun q : Option V => q.elim 0
        (unweight m (fullFormSemigroup G m δ (valueInclusion G m U))))).comp
      (measurable_X_naturalFiltration PF (stationaryGridTime δ n))).stronglyMeasurable
  apply (ae_eq_condExp_of_forall_setIntegral_eq
    (Filtration.le (stationaryGridFiltration PF δ) n) hlhs
    (fun _ _ _ => hrhs.integrableOn) ?_ hrhs_meas.aestronglyMeasurable).symm
  intro A hA _
  have hA0 : MeasurableSet A := (stationaryGridFiltration PF δ).le n A hA
  have hl := integral_reflectedSpeedLaw PF m hmsum (hlhs.indicator hA0)
  have hr := integral_reflectedSpeedLaw PF m hmsum (hrhs.indicator hA0)
  simp only [integral_indicator hA0] at hl hr
  rw [hl, hr]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have hc := ReflectedMarkovConditional.condExp_vertex_test h z
      (show stationaryGridTime δ n ≤ stationaryGridTime δ (n + 1) by
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ n)) δ.2)
      (unweight m (valueInclusion G m U)) C hbounded
    have hc' :
        (PF.P z)[lhs | PF.naturalFiltration (stationaryGridTime δ n)] =ᵐ[PF.P z] rhs := by
      have hY : lhs = fun ω =>
          (PF.X (stationaryGridTime δ (n + 1)) ω).elim 0
            (unweight m (valueInclusion G m U)) := rfl
      rw [hY]
      filter_upwards [hc] with ω hω
      simp only [rhs]
      rw [hω, stationaryGridTime_succ_sub]
      congr 1
      funext x
      exact integral_reflected_unweight_at_time h hG hm hmsum δ x
        (valueInclusion G m U)
    have hlhs_z : Integrable lhs (PF.P z) := by
      exact integrable_reflected_unweight_at_time h hG hm hmsum
        (stationaryGridTime δ (n + 1)) z (valueInclusion G m U)
    have hrhs_z : Integrable rhs (PF.P z) := by
      exact integrable_reflected_unweight_at_time h hG hm hmsum
        (stationaryGridTime δ n) z
        (fullFormSemigroup G m δ (valueInclusion G m U))
    symm
    calc
      ∫ ω in A, lhs ω ∂PF.P z =
          ∫ ω in A,
            (PF.P z)[lhs | PF.naturalFiltration (stationaryGridTime δ n)] ω
            ∂PF.P z :=
        (setIntegral_condExp (PF.naturalFiltration.le _) hlhs_z hA).symm
      _ = ∫ ω in A, rhs ω ∂PF.P z :=
        setIntegral_congr_ae ((PF.naturalFiltration.le _) A hA)
          (hc'.mono fun _ hx _ => hx)

/- The conditional mean of one grid increment is exactly the decoded
semigroup drift. -/
theorem condExp_stationaryGridPotential_increment
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (n : ℕ) :
    (reflectedSpeedLaw PF m)[
        stationaryGridPotential PF G m U δ (n + 1) -
          stationaryGridPotential PF G m U δ n |
        stationaryGridFiltration PF δ n] =ᵐ[reflectedSpeedLaw PF m]
      stationaryGridDrift PF G m U δ n := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hnext := condExp_stationaryGridPotential_succ
    h hG hm hmsum U δ C hbounded n
  have hYn : Integrable (stationaryGridPotential PF G m U δ n)
      (reflectedSpeedLaw PF m) :=
    integrable_stationaryGridPotential h hG hm hmsum U δ n
  have hYnext : Integrable (stationaryGridPotential PF G m U δ (n + 1))
      (reflectedSpeedLaw PF m) :=
    integrable_stationaryGridPotential h hG hm hmsum U δ (n + 1)
  have hself := condExp_of_stronglyMeasurable
    (Filtration.le (stationaryGridFiltration PF δ) n)
    (stronglyAdapted_stationaryGridPotential PF G m U δ n) hYn
  filter_upwards [condExp_sub hYnext hYn _, hnext, hself.eventuallyEq]
    with ω hsub hnextω hselfω
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hnextω, hselfω]
  dsimp only [stationaryGridPotential, stationaryGridDrift]
  cases PF.X (stationaryGridTime δ n) ω with
  | none => simp
  | some x =>
      simp only [Option.elim_some]
      unfold unweight
      simp only [lp.coeFn_sub, Pi.sub_apply]
      ring

/- Mathlib's predictable part is the finite sum of the actual semigroup
drifts. -/
theorem predictablePart_stationaryGridPotential_ae_eq
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (n : ℕ) :
    predictablePart (stationaryGridPotential PF G m U δ)
        (stationaryGridFiltration PF δ) (reflectedSpeedLaw PF m) n =ᵐ[reflectedSpeedLaw PF m]
      fun ω => ∑ i ∈ Finset.range n, stationaryGridDrift PF G m U δ i ω := by
  unfold predictablePart
  have hall : ∀ᵐ ω ∂reflectedSpeedLaw PF m, ∀ i,
      (reflectedSpeedLaw PF m)[
        stationaryGridPotential PF G m U δ (i + 1) -
          stationaryGridPotential PF G m U δ i |
        stationaryGridFiltration PF δ i] ω =
      stationaryGridDrift PF G m U δ i ω :=
    ae_all_iff.2 fun i => condExp_stationaryGridPotential_increment
      h hG hm hmsum U δ C hbounded i
  filter_upwards [hall] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hω i

/- The centered existing Doob martingale has the advertised explicit
semigroup-compensated form. -/
theorem stationaryGridMartingale_ae_eq_compensated
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (n : ℕ) :
    stationaryGridMartingale PF G m U δ n =ᵐ[reflectedSpeedLaw PF m]
      fun ω => stationaryGridPotential PF G m U δ n ω -
        stationaryGridPotential PF G m U δ 0 ω -
        ∑ i ∈ Finset.range n, stationaryGridDrift PF G m U δ i ω := by
  filter_upwards [predictablePart_stationaryGridPotential_ae_eq
    h hG hm hmsum U δ C hbounded n] with ω hpred
  simp only [stationaryGridMartingale, martingalePart, Pi.sub_apply, hpred]
  ring

/- The centered Doob part is a true martingale under the finite stationary
speed law. -/
theorem stationaryGridMartingale_isMartingale
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) :
    Martingale (stationaryGridMartingale PF G m U δ)
      (stationaryGridFiltration PF δ) (reflectedSpeedLaw PF m) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let Y := stationaryGridPotential PF G m U δ
  let F := stationaryGridFiltration PF δ
  let μ := reflectedSpeedLaw PF m
  have hYad : StronglyAdapted F Y :=
    stronglyAdapted_stationaryGridPotential PF G m U δ
  have hYint : ∀ n, Integrable (Y n) μ :=
    integrable_stationaryGridPotential h hG hm hmsum U δ
  have hpart : Martingale (martingalePart Y F μ) F μ :=
    martingale_martingalePart hYad hYint
  have hconst : Martingale (fun _ => Y 0) F μ :=
    martingale_const_fun F μ (hYad 0) (hYint 0)
  unfold stationaryGridMartingale
  exact hpart.sub hconst

end ReflectedGMS

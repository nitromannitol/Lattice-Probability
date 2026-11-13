/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedOccupationCorePairing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ActualStoppedOccupationDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreApproximation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreInput
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreSquareAlgebra
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- Merged from `ReflectedGMS/Forms/LocalVariationalStoppedMartingale.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_LocalVariationalStoppedMartingale

/-!
# The local variational estimate for the stopped-martingale problem

The full local variational identity controls the actual resolvent-core generator
against every full-domain supported test, uniformly in the test's graph norm.
This is the analytic input supplied by harmonicity to a stopped occupation
argument. It does not assert that weak generator convergence implies convergence
of stopped occupations: that process/form localization step remains necessary.
-/

set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [DecidableEq V]
  (G : ConductanceGraph V) (m : V → ℝ)

/-- Full local variational harmonicity bounds a core generator's action on
all supported full-domain tests by the core approximation error. The set may
contain infinitely many vertices, so this retains the boundary-sensitive tests. -/
theorem local_variational_resolventCore_generator_bound
    (U : hilbertDomain G m) (A : Set V)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (q : CountableResolventCoreIndex V) (v : hilbertDomain G m)
    (hv : ∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) :
    |⟪valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q, valueInclusion G m v⟫_ℝ| ≤
      ‖countableResolventCoreVector G m q - U‖ * ‖v‖ := by
  have horth : ⟪gradientInclusion G m U, gradientInclusion G m v⟫_ℝ = 0 := by
    rw [gradientInclusion_eq, gradientInclusion_eq, weightedGradient_inner]
    exact hU v hv
  have hweak := oneResolventLift_weak G m (countableResolventCoreInput G m q) v
  change ⟪valueInclusion G m (countableResolventCoreVector G m q),
      valueInclusion G m v⟫_ℝ +
    ⟪gradientInclusion G m (countableResolventCoreVector G m q),
      gradientInclusion G m v⟫_ℝ = _ at hweak
  have heq :
      ⟪valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q, valueInclusion G m v⟫_ℝ =
      -⟪gradientInclusion G m (countableResolventCoreVector G m q - U),
        gradientInclusion G m v⟫_ℝ := by
    rw [map_sub, inner_sub_left, inner_sub_left, horth]
    linarith
  rw [heq, abs_neg]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul
    (WithLp.norm_snd_le (ValueSpace V)
      ((countableResolventCoreVector G m q - U) : EnergyAmbient V))
    (WithLp.norm_snd_le (ValueSpace V) (v : EnergyAmbient V))
    (norm_nonneg _) (norm_nonneg _))

variable [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The weighted generator used in the full variational estimate decodes to
exactly the state density in the already proved core Dynkin martingale. -/
theorem resolventCore_generator_unweight_eq_drift
    (hm : ∀ x, 0 < m x) (hmsum : Summable m)
    (q : CountableResolventCoreIndex V) (x : V) :
    unweight m (valueInclusion G m (countableResolventCoreVector G m q) -
      countableResolventCoreInput G m q) x = resolventCoreDrift G m q (some x) := by
  have hinput : unweight m (countableResolventCoreInput G m q) x = (q x : ℝ) := by
    rw [countableResolventCoreInput_eq_weightedValue G m hm hmsum q,
      unweight_weightedValue m hm]
  change (valueInclusion G m (countableResolventCoreVector G m q) x -
      countableResolventCoreInput G m q x) / Real.sqrt (m x) = _
  rw [sub_div]
  change countableResolventCoreFeature G m q x -
      unweight m (countableResolventCoreInput G m q) x = _
  rw [hinput]
  rfl

end ReflectedGMS

end Merged_LocalVariationalStoppedMartingale

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- Literal event-restricted occupation of one vertex before the stopping time. -/
noncomputable def actualStoppedVertexOccupation (PF : ProcessFamily V)
    (B : Set PF.Ω) (tau : PF.Ω → WithTop ℝ≥0) (s t : ℝ≥0) (x : V)
    (ω : PF.Ω) : ℝ := by
  classical
  exact ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
    if ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω ∧
      PF.X r.toNNReal ω = some x then (1 : ℝ) else 0

theorem actualStoppedVertexOccupation_nonneg (PF : ProcessFamily V)
    (B : Set PF.Ω) (tau : PF.Ω → WithTop ℝ≥0) (s t : ℝ≥0) (x : V)
    (ω : PF.Ω) : 0 ≤ actualStoppedVertexOccupation PF B tau s t x ω := by
  classical
  unfold actualStoppedVertexOccupation
  apply integral_nonneg
  intro r
  dsimp only [Pi.zero_apply]
  by_cases hp : ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω ∧
      PF.X r.toNNReal ω = some x
  · rw [if_pos hp]
    norm_num
  · rw [if_neg hp]

/-- Joint measurability is needed only for an indistinguishable dyadic version. -/
theorem integrable_actualStoppedVertexOccupation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (z : V) {B : Set PF.Ω} (hB : MeasurableSet B)
    {tau : PF.Ω → WithTop ℝ≥0} (htau : Measurable tau)
    (s t : ℝ≥0) (x : V) :
    Integrable (actualStoppedVertexOccupation PF B tau s t x) (PF.P z) := by
  classical
  let F : PF.Ω → ℝ → ℝ := fun ω r ↦
    if ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω ∧
      Theorem16.dyadicLimit PF.X r.toNNReal ω = some x then 1 else 0
  have hset : MeasurableSet {p : PF.Ω × ℝ | p.1 ∈ B ∧
      (p.2.toNNReal : WithTop ℝ≥0) < tau p.1 ∧
      Theorem16.dyadicLimit PF.X p.2.toNNReal p.1 = some x} := by
    refine (hB.preimage measurable_fst).inter (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt (by fun_prop) (htau.comp measurable_fst)
    · exact (Theorem16.measurable_swap_toNNReal
        (Theorem16.measurable_uncurry_dyadicLimit PF.measurable_X))
        (Theorem16.measurableSet_option {some x})
  have hF : Measurable (Function.uncurry F) :=
    measurable_const.ite hset measurable_const
  have hi : Integrable (Function.uncurry F)
      ((PF.P z).prod (volume.restrict (Icc (s : ℝ) (t : ℝ)))) := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    filter_upwards [] with p
    dsimp only [Function.uncurry, F]
    by_cases hp : p.1 ∈ B ∧ (p.2.toNNReal : WithTop ℝ≥0) < tau p.1 ∧
        Theorem16.dyadicLimit PF.X p.2.toNNReal p.1 = some x
    · rw [if_pos hp]
      norm_num
    · rw [if_neg hp]
      norm_num
  apply hi.integral_prod_left.congr
  filter_upwards [Theorem16.ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  simp only [Function.uncurry, F, hω]

/-- Bounded vertex tests pair the actual density with the expected countable
sum of literal stopped vertex occupations. -/
theorem actualStoppedOccupationMass_pairing_eq_expected_tsum
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) {B : Set PF.Ω} (hB : MeasurableSet B)
    {tau : PF.Ω → WithTop ℝ≥0} (htau : Measurable tau)
    {s t : ℝ≥0} (hst : s ≤ t) (f : V → ℝ)
    (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    (∑' x, f x * actualStoppedOccupationMass PF z B tau s t x) =
      ∫ ω, (∑' x, f x * actualStoppedVertexOccupation PF B tau s t x ω) ∂PF.P z := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := (abs_nonneg (f z)).trans (hC z)
  have hmean (x : V) :
      (∫ ω, actualStoppedVertexOccupation PF B tau s t x ω ∂PF.P z) =
        actualStoppedOccupationMass PF z B tau s t x :=
    (actualStoppedOccupationMass_eq_expected_occupation h z hB htau s t x).symm
  have hint (x : V) : Integrable
      (fun ω ↦ f x * actualStoppedVertexOccupation PF B tau s t x ω) (PF.P z) :=
    (integrable_actualStoppedVertexOccupation h z hB htau s t x).const_mul _
  have hnorm (x : V) :
      (∫ ω, ‖f x * actualStoppedVertexOccupation PF B tau s t x ω‖ ∂PF.P z) =
        |f x| * actualStoppedOccupationMass PF z B tau s t x := by
    simp_rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (actualStoppedVertexOccupation_nonneg PF B tau s t x _)]
    rw [integral_const_mul, hmean]
  have hsum : Summable (fun x ↦
      ∫ ω, ‖f x * actualStoppedVertexOccupation PF B tau s t x ω‖ ∂PF.P z) := by
    simp_rw [hnorm]
    apply Summable.of_nonneg_of_le (fun x ↦ mul_nonneg (abs_nonneg _)
      (actualStoppedOccupationMass_nonneg PF z B tau s t x))
      (fun x ↦ ?_) (hmsum.mul_left (C * ((t : ℝ) - (s : ℝ)) / m z))
    calc
      |f x| * actualStoppedOccupationMass PF z B tau s t x ≤
          C * (((t : ℝ) - (s : ℝ)) * (m x / m z)) :=
        mul_le_mul (hC x) (actualStoppedOccupationMass_le h hG hm hmsum z B tau hst x)
          (actualStoppedOccupationMass_nonneg PF z B tau s t x) hC0
      _ = _ := by ring
  have hexchange := integral_tsum_of_summable_integral_norm hint hsum
  simpa only [integral_const_mul, hmean] using hexchange

/-- The weighted Hilbert pairing has the same actual stopped-path meaning. -/
theorem actualStoppedOccupationDensity_inner_eq_expected_tsum
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) {B : Set PF.Ω} (hB : MeasurableSet B)
    {tau : PF.Ω → WithTop ℝ≥0} (htau : Measurable tau)
    {s t : ℝ≥0} (hst : s ≤ t) (f : ValueSpace V)
    (hf : ∃ C : ℝ, ∀ x, |unweight m f x| ≤ C) :
    ⟪f, actualStoppedOccupationDensity h hG hm hmsum z B tau hst⟫_ℝ =
      ∫ ω, (∑' x, unweight m f x *
        actualStoppedVertexOccupation PF B tau s t x ω) ∂PF.P z := by
  rw [lp.inner_eq_tsum]
  calc
    _ = ∑' x, unweight m f x * actualStoppedOccupationMass PF z B tau s t x := by
      apply tsum_congr
      intro x
      change actualStoppedOccupationMass PF z B tau s t x / Real.sqrt (m x) *
        f x = (f x / Real.sqrt (m x)) * actualStoppedOccupationMass PF z B tau s t x
      ring
    _ = _ := actualStoppedOccupationMass_pairing_eq_expected_tsum
      h hG hm hmsum z hB htau hst (unweight m f) hf

/-- The bounded drift pairing required by the stopped Dynkin argument for
full spatial harmonicity (`p:lem:localharm`). -/
theorem resolventCore_generator_actualStoppedOccupation_pairing
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) {B : Set PF.Ω} (hB : MeasurableSet B)
    {tau : PF.Ω → WithTop ℝ≥0} (htau : Measurable tau)
    {s t : ℝ≥0} (hst : s ≤ t) (q : CountableResolventCoreIndex V) :
    ⟪valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q,
      actualStoppedOccupationDensity h hG hm hmsum z B tau hst⟫_ℝ =
      ∫ ω, (∑' x, resolventCoreDrift G m q (some x) *
        actualStoppedVertexOccupation PF B tau s t x ω) ∂PF.P z := by
  have hbound : ∃ C : ℝ, ∀ x,
      |unweight m (valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q) x| ≤ C := by
    refine ⟨2 * countableResolventCoreBound q, fun x ↦ ?_⟩
    rw [resolventCore_generator_unweight_eq_drift G m hm hmsum]
    exact norm_resolventCoreDrift_le G m hm q (some x)
  simpa only [resolventCore_generator_unweight_eq_drift G m hm hmsum] using
    actualStoppedOccupationDensity_inner_eq_expected_tsum h hG hm hmsum z hB htau hst
      (valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q) hbound

end ReflectedGMS

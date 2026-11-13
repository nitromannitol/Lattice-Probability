/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexDynkinMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedStateOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedTrajectoryConditional
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedSemigroupAction
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.Basic

/-!
# The ordinary vertex-potential Dynkin martingale

The full-form Dynkin identity is transferred to the reflected process through
the whole-future trajectory Markov property.  The compensator uses the
canonical natural-filtration version of bounded state occupation.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The bounded state observable appearing in the ordinary Dynkin formula. -/
noncomputable def vertexDynkinIntegrand [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (alpha : ℝ) (y : V) : Option V → ℝ :=
  fun q ↦ q.elim 0
    (fun x ↦ alpha * vertexOccupationPotential G m alpha x y - G.indic y x)

/-- The ordinary compensated vertex-potential process. -/
noncomputable def vertexDynkinMartingale [DecidableEq V]
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (alpha : ℝ) (y : V) : ℝ≥0 → PF.Ω → ℝ :=
  fun t ω ↦ (PF.X t ω).elim 0 (vertexOccupationPotential G m alpha · y) -
    boundedStateOccupationVersion PF (vertexDynkinIntegrand G m alpha y) t ω

/-- The canonical measurable finite-horizon integral on trajectory space. -/
noncomputable def trajectoryStateIntegral
    (f : Option V → ℝ) (t : ℝ≥0) (γ : Trajectory V) : ℝ :=
  ∫ r : ℝ in Icc 0 (t : ℝ),
    f (dyadicLimit (evalProc V) (Real.toNNReal r) γ)

theorem measurable_trajectoryStateIntegral
    (f : Option V → ℝ) (t : ℝ≥0) :
    Measurable (trajectoryStateIntegral (V := V) f t) := by
  let F : Trajectory V → ℝ → ℝ := fun γ r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator (fun r ↦
      f (dyadicLimit (evalProc V) (Real.toNNReal r) γ)) r
  have hjoint : Measurable (Function.uncurry F) := by
    dsimp only [F]
    apply Measurable.indicator
    · exact (measurable_of_countable f).comp
        (measurable_swap_toNNReal
          (measurable_uncurry_dyadicLimit (fun s ↦ measurable_pi_apply s)))
    · exact measurable_snd measurableSet_Icc
  change Measurable (fun γ : Trajectory V ↦ ∫ r : ℝ in Icc 0 (t : ℝ),
    f (dyadicLimit (evalProc V) (Real.toNNReal r) γ))
  have hsm : StronglyMeasurable (fun γ : Trajectory V ↦
      ∫ r : ℝ in Icc 0 (t : ℝ),
        f (dyadicLimit (evalProc V) (Real.toNNReal r) γ)) := by
    simpa only [F, integral_indicator measurableSet_Icc] using
      hjoint.stronglyMeasurable.integral_prod_right
  exact hsm.measurable

private theorem norm_trajectoryStateIntegral_le
    (f : Option V → ℝ) (t : ℝ≥0) {C : ℝ} (hf : ∀ q, ‖f q‖ ≤ C)
    (γ : Trajectory V) :
    ‖trajectoryStateIntegral (V := V) f t γ‖ ≤ (t : ℝ) * C := by
  unfold trajectoryStateIntegral
  calc
    ‖∫ r : ℝ in Icc 0 (t : ℝ),
        f (dyadicLimit (evalProc V) (Real.toNNReal r) γ)‖
        ≤ C * volume.real (Icc (0 : ℝ) (t : ℝ)) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top (fun r _ ↦ hf _)
    _ = (t : ℝ) * C := by simp [mul_comm]

/-- A canonical bounded-state occupation has the expected deterministic
finite-horizon bound. -/
theorem norm_boundedStateOccupationVersion_le
    (PF : ProcessFamily V) (f : Option V → ℝ) (t : ℝ≥0)
    {C : ℝ} (hf : ∀ q, ‖f q‖ ≤ C) (ω : PF.Ω) :
    ‖boundedStateOccupationVersion PF f t ω‖ ≤ (t : ℝ) * C := by
  unfold boundedStateOccupationVersion
  calc
    ‖∫ r : ℝ in Icc 0 (t : ℝ),
        f (dyadicLimit _ (Real.toNNReal r) ω)‖
        ≤ C * volume.real (Icc (0 : ℝ) (t : ℝ)) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top (fun r _ ↦ hf _)
    _ = (t : ℝ) * C := by simp [mul_comm]

theorem vertexDynkinIntegrand_bound [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {alpha : ℝ} (ha : 0 < alpha) (y : V) (q : Option V) :
    ‖vertexDynkinIntegrand G m alpha y q‖ ≤ 2 := by
  cases q with
  | none => simp [vertexDynkinIntegrand]
  | some x =>
      have hU0 := vertexOccupationPotential_nonneg G m hm ha x y
      have hUb := vertexOccupationPotential_le_inv G m hm ha x y
      have haU0 : 0 ≤ alpha * vertexOccupationPotential G m alpha x y :=
        mul_nonneg ha.le hU0
      have haUb : alpha * vertexOccupationPotential G m alpha x y ≤ 1 := by
        calc
          alpha * vertexOccupationPotential G m alpha x y ≤ alpha * (1 / alpha) :=
            mul_le_mul_of_nonneg_left hUb ha.le
          _ = 1 := by field_simp
      have hi0 := G.indic_nonneg y x
      have hi1 := G.indic_le_one y x
      rw [vertexDynkinIntegrand, Option.elim_some, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> linarith

private theorem measurable_vertexDynkinTrajectoryIncrement [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (alpha : ℝ) (y : V) (t : ℝ≥0) :
    Measurable (fun γ : Trajectory V ↦
      (γ t).elim 0 (vertexOccupationPotential G m alpha · y) -
        trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t γ) := by
  exact ((measurable_of_countable (fun q : Option V ↦
    q.elim 0 (vertexOccupationPotential G m alpha · y))).comp
      (measurable_pi_apply t)).sub
    (measurable_trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t)

private theorem norm_vertexDynkinTrajectoryIncrement_le [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {alpha : ℝ} (ha : 0 < alpha) (y : V) (t : ℝ≥0) (γ : Trajectory V) :
    ‖(γ t).elim 0 (vertexOccupationPotential G m alpha · y) -
        trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t γ‖
      ≤ 1 / alpha + (t : ℝ) * 2 := by
  calc
    ‖(γ t).elim 0 (vertexOccupationPotential G m alpha · y) -
        trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t γ‖
      ≤ ‖(γ t).elim 0 (vertexOccupationPotential G m alpha · y)‖ +
          ‖trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t γ‖ :=
        norm_sub_le _ _
    _ ≤ 1 / alpha + (t : ℝ) * 2 := by
      apply add_le_add
      · cases γ t with
        | none => simpa using one_div_nonneg.mpr ha.le
        | some x =>
            rw [Option.elim_some, Real.norm_eq_abs,
              abs_of_nonneg (vertexOccupationPotential_nonneg G m hm ha x y)]
            exact vertexOccupationPotential_le_inv G m hm ha x y
      · exact norm_trajectoryStateIntegral_le _ t
          (vertexDynkinIntegrand_bound G m hm ha y) γ

private theorem unweight_vertexDynkinGenerator [DecidableEq V]
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {alpha : ℝ} (ha : 0 < alpha) (y x : V) :
    unweight m
        (alpha • vertexOccupationPotentialValue G m alpha y -
          weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x =
      vertexDynkinIntegrand G m alpha y (some x) := by
  have hlin : unweight m
        (alpha • vertexOccupationPotentialValue G m alpha y -
          weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x =
      alpha * unweight m (vertexOccupationPotentialValue G m alpha y) x -
        unweight m
          (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) x := by
    unfold unweight
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sub, Pi.sub_apply]
    ring
  rw [hlin, unweight_vertexOccupationPotentialValue G m ha,
    congrFun (unweight_weightedValue m hm (G.indic y)
      (VertexTest.indic_hasSpeedL2 G m y)) x]
  rfl

private theorem integral_trajectoryStateIntegral_law [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha)
    (t : ℝ≥0) (x y : V) :
    (∫ γ, trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t γ
        ∂PF.law x) =
      ∫ r : ℝ in Icc 0 (t : ℝ),
        unweight m (fullFormSemigroup G m (Real.toNNReal r)
          (alpha • vertexOccupationPotentialValue G m alpha y -
            weightedValue m (G.indic y)
              (VertexTest.indic_hasSpeedL2 G m y))) x := by
  let g := vertexDynkinIntegrand G m alpha y
  let A := alpha • vertexOccupationPotentialValue G m alpha y -
    weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)
  let F : PF.Ω → ℝ → ℝ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator (fun r ↦
      g (dyadicLimit PF.X (Real.toNNReal r) ω)) r
  have hjoint : Measurable (Function.uncurry F) := by
    dsimp only [F]
    apply Measurable.indicator
    · exact (measurable_of_countable g).comp
        (measurable_swap_toNNReal
          (measurable_uncurry_dyadicLimit PF.measurable_X))
    · exact measurable_snd measurableSet_Icc
  have hdom : Integrable (fun p : PF.Ω × ℝ ↦
      (Icc (0 : ℝ) (t : ℝ)).indicator (fun _ ↦ (2 : ℝ)) p.2)
      ((PF.P x).prod volume) := by
    apply Integrable.comp_snd
    simpa only [integrable_indicator_iff measurableSet_Icc] using
      (integrableOn_const (C := (2 : ℝ)) measure_Icc_lt_top.ne)
  have hFint : Integrable (Function.uncurry F) ((PF.P x).prod volume) := by
    apply hdom.mono' hjoint.aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Function.uncurry, F]
    by_cases hp : p.2 ∈ Icc (0 : ℝ) (t : ℝ)
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      simpa only [Real.norm_eq_abs] using
        vertexDynkinIntegrand_bound G m hm ha y
          (dyadicLimit PF.X (Real.toNNReal p.2) p.1)
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
      simp
  have hver := ae_dyadicLimit_eq (h x).2.2.1 (h x).2.2.2.1
  have htraj : Measurable PF.trajectory := measurable_pi_iff.mpr PF.measurable_X
  calc
    (∫ γ, trajectoryStateIntegral g t γ ∂PF.law x) =
        ∫ ω, trajectoryStateIntegral g t (PF.trajectory ω) ∂PF.P x := by
      rw [ProcessFamily.law, integral_map htraj.aemeasurable
        (measurable_trajectoryStateIntegral g t).aestronglyMeasurable]
    _ = ∫ ω, ∫ r, F ω r ∂volume ∂PF.P x := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [trajectoryStateIntegral, F, integral_indicator measurableSet_Icc]
      rfl
    _ = ∫ r, ∫ ω, F ω r ∂PF.P x ∂volume := integral_integral_swap hFint
    _ = ∫ r : ℝ in Icc 0 (t : ℝ),
        unweight m (fullFormSemigroup G m (Real.toNNReal r) A) x := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with r
      by_cases hr : r ∈ Icc (0 : ℝ) (t : ℝ)
      · rw [Set.indicator_of_mem hr]
        simp only [F, Set.indicator_of_mem hr]
        have heq : (fun ω ↦ g (dyadicLimit PF.X (Real.toNNReal r) ω)) =ᵐ[PF.P x]
            fun ω ↦ (PF.X (Real.toNNReal r) ω).elim 0 (unweight m A) := by
          filter_upwards [hver] with ω hω
          rw [hω]
          cases PF.X (Real.toNNReal r) ω with
          | none => simp [g, vertexDynkinIntegrand]
          | some z =>
              simp only [Option.elim_some]
              exact (unweight_vertexDynkinGenerator G m hm ha y z).symm
        rw [integral_congr_ae heq]
        exact integral_reflected_unweight_at_time h hG hm hmsum
          (Real.toNNReal r) x A
      · rw [Set.indicator_of_notMem hr]
        simp only [F, Set.indicator_of_notMem hr, integral_zero]
    _ = _ := by rfl

private theorem integral_vertexDynkinTrajectoryIncrement_law [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha)
    (t : ℝ≥0) (x y : V) :
    (∫ γ, ((γ t).elim 0 (vertexOccupationPotential G m alpha · y) -
        trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t γ)
        ∂PF.law x) = vertexOccupationPotential G m alpha x y := by
  let U := vertexOccupationPotentialValue G m alpha y
  let A := alpha • U -
    weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)
  have hUint : Integrable
      (fun γ : Trajectory V ↦ (γ t).elim 0 (vertexOccupationPotential G m alpha · y))
      (PF.law x) := by
    apply Integrable.of_bound
      (((measurable_of_countable (fun q : Option V ↦
        q.elim 0 (vertexOccupationPotential G m alpha · y))).comp
          (measurable_pi_apply t)).aestronglyMeasurable) (1 / alpha)
    filter_upwards [] with γ
    change ‖(γ t).elim 0 (vertexOccupationPotential G m alpha · y)‖ ≤ 1 / alpha
    cases γ t with
    | none => simpa using one_div_nonneg.mpr ha.le
    | some z =>
        rw [Option.elim_some, Real.norm_eq_abs,
          abs_of_nonneg (vertexOccupationPotential_nonneg G m hm ha z y)]
        exact vertexOccupationPotential_le_inv G m hm ha z y
  have hOint : Integrable
      (trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) t) (PF.law x) := by
    apply Integrable.of_bound
      (measurable_trajectoryStateIntegral
        (vertexDynkinIntegrand G m alpha y) t).aestronglyMeasurable ((t : ℝ) * 2)
    filter_upwards [] with γ
    exact norm_trajectoryStateIntegral_le _ t
      (vertexDynkinIntegrand_bound G m hm ha y) γ
  rw [integral_sub hUint hOint]
  have hstate : (∫ γ, (γ t).elim 0
      (vertexOccupationPotential G m alpha · y) ∂PF.law x) =
      unweight m (fullFormSemigroup G m t U) x := by
    have htraj : Measurable PF.trajectory := measurable_pi_iff.mpr PF.measurable_X
    calc
      (∫ γ, (γ t).elim 0
          (vertexOccupationPotential G m alpha · y) ∂PF.law x) =
          ∫ ω, (PF.trajectory ω t).elim 0
            (vertexOccupationPotential G m alpha · y) ∂PF.P x := by
        rw [ProcessFamily.law]
        exact integral_map htraj.aemeasurable
          (((measurable_of_countable (fun q : Option V ↦
            q.elim 0 (vertexOccupationPotential G m alpha · y))).comp
              (measurable_pi_apply t)).aestronglyMeasurable)
      _ = ∫ ω, (PF.X t ω).elim 0 (unweight m U) ∂PF.P x := by
        apply integral_congr_ae
        filter_upwards [] with ω
        change (PF.X t ω).elim 0 (vertexOccupationPotential G m alpha · y) =
          (PF.X t ω).elim 0 (unweight m U)
        cases hq : PF.X t ω with
        | none => simp [hq]
        | some z =>
            simpa only [hq, Option.elim_some, U] using
              (unweight_vertexOccupationPotentialValue G m ha z y).symm
      _ = unweight m (fullFormSemigroup G m t U) x :=
        integral_reflected_unweight_at_time h hG hm hmsum t x U
  rw [hstate, integral_trajectoryStateIntegral_law h hG hm hmsum ha t x y]
  have hdynkin := vertexOccupationPotential_dynkin G m hm hmsum ha t x y
  rw [intervalIntegral.integral_of_le t.coe_nonneg] at hdynkin
  rw [integral_Icc_eq_integral_Ioc]
  dsimp only [U, A]
  linarith

theorem trajectoryStateIntegral_shiftedPath_eq
    (PF : ProcessFamily V) (f : Option V → ℝ) (s t : ℝ≥0) (ω : PF.Ω)
    (hω : RightRegularAt PF.X ω) :
    trajectoryStateIntegral (V := V) f t (shiftedPath PF.X s ω) =
      ∫ r : ℝ in Icc 0 (t : ℝ), f (PF.X (Real.toNNReal r + s) ω) := by
  have hshift : RightRegularAt (evalProc V) (shiftedPath PF.X s ω) :=
    rightRegularAt_shiftedPath hω s
  unfold trajectoryStateIntegral
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  change f (dyadicLimit (evalProc V) (Real.toNNReal r) (shiftedPath PF.X s ω)) =
    f (PF.X (Real.toNNReal r + s) ω)
  rw [dyadicLimit_eq_of_rightRegular hshift]
  rfl

private theorem boundedStateOccupationVersion_add_increment_ae
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (f : Option V → ℝ) {C : ℝ} (hf : ∀ q, |f q| ≤ C) (z : V)
    {s t : ℝ≥0} (hst : s ≤ t) :
    boundedStateOccupationVersion PF f t =ᵐ[PF.P z]
      fun ω ↦ boundedStateOccupationVersion PF f s ω +
        trajectoryStateIntegral f (t - s) (shiftedPath PF.X s ω) := by
  filter_upwards [boundedStateOccupationVersion_ae_eq_all_and_continuous
      h f hf z, ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hocc hreg
  rw [hocc.1 t, hocc.1 s,
    trajectoryStateIntegral_shiftedPath_eq PF f s (t - s) ω hreg]
  let H : ℝ → ℝ := fun r ↦ f (PF.X (Real.toNNReal r) ω)
  have hshiftint :
      (∫ r : ℝ in Icc 0 ((t - s : ℝ≥0) : ℝ),
          f (PF.X (Real.toNNReal r + s) ω)) =
        ∫ r : ℝ in Icc 0 ((t - s : ℝ≥0) : ℝ), H (r + (s : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    dsimp only [H]
    rw [Real.toNNReal_add hr.1 s.coe_nonneg, Real.toNNReal_coe]
  rw [hshiftint]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le t.coe_nonneg,
    ← intervalIntegral.integral_of_le s.coe_nonneg,
    ← intervalIntegral.integral_of_le (t - s).coe_nonneg]
  rw [intervalIntegral.integral_comp_add_right]
  have hts : (((t - s : ℝ≥0) : ℝ) + (s : ℝ)) = (t : ℝ) := by
    exact congrArg ((↑) : ℝ≥0 → ℝ) (tsub_add_cancel_of_le hst)
  rw [zero_add, hts]
  have hHmeas : Measurable H := by
    rw [show H = fun r : ℝ ↦
        f (dyadicLimit PF.X (Real.toNNReal r) ω) by
      funext r
      dsimp only [H]
      rw [dyadicLimit_eq_of_rightRegular hreg]]
    exact (measurable_of_countable f).comp
      (measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω)
  have hC : 0 ≤ C := by
    have := hf none
    exact (abs_nonneg (f none)).trans this
  have hHint (a b : ℝ) : IntervalIntegrable H volume a b := by
    constructor
    · apply (integrableOn_const (C := C) measure_Ioc_lt_top.ne).mono'
      · exact hHmeas.aestronglyMeasurable
      · filter_upwards [] with r
        simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hf (PF.X (Real.toNNReal r) ω)
    · apply (integrableOn_const (C := C) measure_Ioc_lt_top.ne).mono'
      · exact hHmeas.aestronglyMeasurable
      · filter_upwards [] with r
        simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hf (PF.X (Real.toNNReal r) ω)
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hHint 0 (s : ℝ)) (hHint (s : ℝ) (t : ℝ))).symm

private theorem vertexDynkinMartingale_increment_ae [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hm : ∀ v, 0 < m v) {alpha : ℝ} (ha : 0 < alpha) (y z : V)
    {s t : ℝ≥0} (hst : s ≤ t) :
    vertexDynkinMartingale PF G m alpha y t =ᵐ[PF.P z]
      fun ω ↦
        ((shiftedPath PF.X s ω (t - s)).elim 0
          (vertexOccupationPotential G m alpha · y) -
            trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) (t - s)
              (shiftedPath PF.X s ω)) -
          boundedStateOccupationVersion PF (vertexDynkinIntegrand G m alpha y) s ω := by
  have hf : ∀ q, |vertexDynkinIntegrand G m alpha y q| ≤ 2 := by
    intro q
    simpa only [Real.norm_eq_abs] using vertexDynkinIntegrand_bound G m hm ha y q
  filter_upwards [boundedStateOccupationVersion_add_increment_ae h
      (vertexDynkinIntegrand G m alpha y) hf z hst] with ω hocc
  unfold vertexDynkinMartingale
  rw [hocc]
  simp only [shiftedPath, tsub_add_cancel_of_le hst]
  ring

/-- The ordinary compensated vertex potential is a martingale in the actual
uncompleted natural filtration under every reflected starting law. -/
theorem vertexDynkinMartingale_isMartingale [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V) :
    Martingale (vertexDynkinMartingale PF G m alpha y)
      PF.naturalFiltration (PF.P z) := by
  have hUadapt : StronglyAdapted PF.naturalFiltration
      (fun t ω ↦ (PF.X t ω).elim 0
        (vertexOccupationPotential G m alpha · y)) := by
    intro t
    let U : Option V → ℝ := fun q ↦
      q.elim 0 (vertexOccupationPotential G m alpha · y)
    have hmeasX : Measurable[PF.naturalFiltration t] (PF.X t) := by
      change Measurable[pastSigma PF.X t] (PF.X t)
      intro A hA
      apply measurableSet_pastSigma_iff.mpr
      refine ⟨{p | p ⟨t, by simp⟩ ∈ A}, ?_, rfl⟩
      exact hA.preimage (measurable_pi_apply _)
    exact ((measurable_of_countable U).comp hmeasX).stronglyMeasurable
  have hstrong : StronglyAdapted PF.naturalFiltration
      (vertexDynkinMartingale PF G m alpha y) := by
    exact hUadapt.sub
      (stronglyAdapted_boundedStateOccupationVersion PF
        (vertexDynkinIntegrand G m alpha y))
  refine ⟨hstrong, ?_⟩
  intro s t hst
  let Φ : Trajectory V → ℝ := fun γ ↦
    (γ (t - s)).elim 0 (vertexOccupationPotential G m alpha · y) -
      trajectoryStateIntegral (vertexDynkinIntegrand G m alpha y) (t - s) γ
  let C : ℝ := 1 / alpha + ((t - s : ℝ≥0) : ℝ) * 2
  have hΦmeas : Measurable Φ :=
    measurable_vertexDynkinTrajectoryIncrement G m alpha y (t - s)
  have hΦbound : ∀ γ, ‖Φ γ‖ ≤ C :=
    norm_vertexDynkinTrajectoryIncrement_le G m hm ha y (t - s)
  have hce := ReflectedMarkovConditional.condExp_trajectory_test
    h z s Φ C hΦmeas hΦbound
  have hce' :
      (PF.P z)[(fun ω ↦ Φ (shiftedPath PF.X s ω)) |
        PF.naturalFiltration s] =ᵐ[PF.P z]
        fun ω ↦ (PF.X s ω).elim 0
          (vertexOccupationPotential G m alpha · y) := by
    apply hce.trans
    filter_upwards [] with ω
    cases hx : PF.X s ω with
    | none => simp [hx]
    | some x =>
        simp only [hx, Option.elim_some]
        exact integral_vertexDynkinTrajectoryIncrement_law
          h hG hm hmsum ha (t - s) x y
  have hΦint : Integrable (fun ω ↦ Φ (shiftedPath PF.X s ω)) (PF.P z) := by
    apply Integrable.of_bound
      (hΦmeas.comp (measurable_shiftedPath PF.measurable_X s)).aestronglyMeasurable C
    filter_upwards [] with ω
    exact hΦbound _
  have hAint : Integrable
      (boundedStateOccupationVersion PF (vertexDynkinIntegrand G m alpha y) s)
      (PF.P z) := by
    apply Integrable.of_bound
      ((stronglyMeasurable_boundedStateOccupationVersion PF
        (vertexDynkinIntegrand G m alpha y) s).mono
          (PF.naturalFiltration.le s)).aestronglyMeasurable ((s : ℝ) * 2)
    filter_upwards [] with ω
    exact norm_boundedStateOccupationVersion_le PF _ s
      (vertexDynkinIntegrand_bound G m hm ha y) ω
  have hincr := vertexDynkinMartingale_increment_ae h hm ha y z hst
  calc
    (PF.P z)[vertexDynkinMartingale PF G m alpha y t |
        PF.naturalFiltration s] =ᵐ[PF.P z]
      (PF.P z)[(fun ω ↦ Φ (shiftedPath PF.X s ω) -
        boundedStateOccupationVersion PF (vertexDynkinIntegrand G m alpha y) s ω) |
          PF.naturalFiltration s] := condExp_congr_ae (by simpa only [Φ] using hincr)
    _ =ᵐ[PF.P z]
      (PF.P z)[(fun ω ↦ Φ (shiftedPath PF.X s ω)) | PF.naturalFiltration s] -
        (PF.P z)[boundedStateOccupationVersion PF
          (vertexDynkinIntegrand G m alpha y) s | PF.naturalFiltration s] :=
      condExp_sub hΦint hAint _
    _ =ᵐ[PF.P z] vertexDynkinMartingale PF G m alpha y s := by
      have hAself := condExp_of_stronglyMeasurable (PF.naturalFiltration.le s)
        (stronglyMeasurable_boundedStateOccupationVersion PF
          (vertexDynkinIntegrand G m alpha y) s) hAint
      rw [hAself]
      filter_upwards [hce'] with ω hΦ
      rw [Pi.sub_apply, hΦ]
      rfl

end ReflectedGMS

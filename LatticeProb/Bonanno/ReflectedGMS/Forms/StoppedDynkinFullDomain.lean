/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedDynkinFullDomain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedOccupationCorePairing
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedOccupationFormDomain
import LatticeProb.Bonanno.ReflectedGMS.Forms.CorePotentialUniformBound
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedResolventMomentBound

/-! Actual stopped-Dynkin pairing and full-form-domain occupation for the
localization argument in `p:lem:localharm`. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace Classical

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- Countable vertex occupations reconstruct the literal stopped drift, with
zero contribution at a nonvertex state. -/
theorem actualStoppedVertexOccupation_tsum_eq_integral
    (PF : ProcessFamily V) (B : Set PF.Ω) (tau : PF.Ω → WithTop ℝ≥0)
    (s t : ℝ≥0) (f : Option V → ℝ) (hf0 : f none = 0)
    (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C) (ω : PF.Ω)
    (hω : ∀ r, Theorem16.dyadicLimit PF.X r ω = PF.X r ω) :
    (∑' x, f (some x) * actualStoppedVertexOccupation PF B tau s t x ω) =
      ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        if ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω
        then f (PF.X r.toNNReal ω) else 0 := by
  classical
  obtain ⟨C, hC⟩ := hf
  let F : V → ℝ → ℝ := fun x r ↦
    if (ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω) ∧
      PF.X r.toNNReal ω = some x then f (some x) else 0
  let g : ℝ → ℝ := fun r ↦
    if ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω
      then f (PF.X r.toNNReal ω) else 0
  have hstate : Measurable (fun r : ℝ ↦ PF.X r.toNNReal ω) := by
    have hh := Theorem16.measurable_section
      (Theorem16.measurable_uncurry_dyadicLimit PF.measurable_X) ω
    simpa only [hω] using hh
  have hgate : MeasurableSet {r : ℝ | ω ∈ B ∧
      (r.toNNReal : WithTop ℝ≥0) < tau ω} := by
    by_cases hB : ω ∈ B
    · simpa only [hB, true_and] using
        (measurableSet_lt (by fun_prop : Measurable
          (fun r : ℝ ↦ (r.toNNReal : WithTop ℝ≥0))) measurable_const)
    · simp only [hB, false_and, setOf_false, MeasurableSet.empty]
  have hFm (x : V) : Measurable (F x) :=
    measurable_const.ite
      (hgate.inter (hstate (Theorem16.measurableSet_option {some x}))) measurable_const
  have hgm : Measurable g :=
    ((measurable_of_countable f).comp hstate).ite hgate measurable_const
  have hseries (r : ℝ) : HasSum (fun x ↦ F x r) (g r) ∧
      HasSum (fun x ↦ ‖F x r‖) ‖g r‖ := by
    by_cases hg : ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω
    · cases hx : PF.X r.toNNReal ω with
      | none => simp [F, g, hg, hx, hf0]
      | some x =>
        have hsingle : ∀ y, y ≠ x → F y r = 0 := by
          intro y hy
          simp [F, hg, hx, Ne.symm hy]
        constructor
        · simpa [F, g, hg, hx] using hasSum_single x hsingle
        · have hs : HasSum (fun y ↦ ‖F y r‖) ‖F x r‖ :=
            hasSum_single x (fun y hy ↦ by rw [hsingle y hy, norm_zero])
          simpa [F, g, hg, hx] using hs
    · have hFzero (x : V) : F x r = 0 := if_neg (fun hh ↦ hg hh.1)
      have hgzero : g r = 0 := if_neg hg
      simp only [hFzero, hgzero, norm_zero, hasSum_zero, and_self]
  have hgi : Integrable (fun r ↦ ‖g r‖)
      (volume.restrict (Icc (s : ℝ) (t : ℝ))) := by
    apply Integrable.of_bound hgm.norm.aestronglyMeasurable C
    filter_upwards [] with r
    dsimp only [g]
    by_cases hg : ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω
    · simpa only [if_pos hg, norm_norm, Real.norm_eq_abs, abs_abs] using hC (PF.X r.toNNReal ω)
    · simp only [if_neg hg, norm_zero]
      exact (abs_nonneg (f none)).trans (hC none)
  have hsum := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (s : ℝ) (t : ℝ)))
    (fun x r ↦ ‖F x r‖) (fun x ↦ (hFm x).aestronglyMeasurable)
    (fun _ ↦ Eventually.of_forall fun _ ↦ le_rfl)
    (Eventually.of_forall fun r ↦ (hseries r).2.summable)
    (by simpa only [funext (fun r ↦ (hseries r).2.tsum_eq)] using hgi)
    (Eventually.of_forall fun r ↦ (hseries r).1)
  convert hsum.tsum_eq using 1
  apply tsum_congr
  intro x
  rw [actualStoppedVertexOccupation, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  dsimp only [F]
  simp only [and_assoc]
  split_ifs <;> simp

/-- Canonical bounded-state occupation stopped at `tau` is the literal dyadic
time integral strictly before `tau`; a single endpoint has zero time measure. -/
theorem stopped_boundedStateOccupationVersion_eq_integral
    (PF : ProcessFamily V) (f : Option V → ℝ)
    (tau : PF.Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : PF.Ω) :
    stoppedProcess (boundedStateOccupationVersion PF f) tau t ω =
      ∫ r : ℝ in Icc 0 (t : ℝ),
        if (r.toNNReal : WithTop ℝ≥0) < tau ω
        then f (Theorem16.dyadicLimit PF.X r.toNNReal ω) else 0 := by
  let g : ℝ → ℝ := fun r ↦ f (Theorem16.dyadicLimit PF.X r.toNNReal ω)
  change boundedStateOccupationVersion PF f
    (min (t : WithTop ℝ≥0) (tau ω)).untopA ω = _
  cases htau : tau ω with
  | top =>
      rw [min_eq_left le_top]
      change boundedStateOccupationVersion PF f t ω = _
      rw [boundedStateOccupationVersion_eq_dyadicIntegral]
      apply setIntegral_congr_fun measurableSet_Icc
      intro r _
      dsimp only
      rw [if_pos (WithTop.coe_lt_top _)]
  | coe a =>
      rw [← WithTop.coe_min]
      change boundedStateOccupationVersion PF f (min t a) ω = _
      rw [boundedStateOccupationVersion_eq_dyadicIntegral]
      change (∫ r : ℝ in Icc 0 ((min t a : ℝ≥0) : ℝ), g r) = _
      symm
      calc
        _ = ∫ r : ℝ in Icc 0 (t : ℝ), (Iio (a : ℝ)).indicator g r := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro r hr
          have hc : (r.toNNReal : WithTop ℝ≥0) < (a : WithTop ℝ≥0) ↔
              r < (a : ℝ) := by
            rw [WithTop.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal r hr.1]
          simp only [hc, indicator_apply, mem_Iio, g]
        _ = ∫ r : ℝ in Ico 0 (t : ℝ), (Iio (a : ℝ)).indicator g r :=
          integral_Icc_eq_integral_Ico
        _ = ∫ r : ℝ in Ico 0 (min (t : ℝ) (a : ℝ)), g r := by
          rw [integral_indicator measurableSet_Iio,
            Measure.restrict_restrict measurableSet_Iio]
          have hset : Iio (a : ℝ) ∩ Ico 0 (t : ℝ) =
              Ico 0 (min (t : ℝ) (a : ℝ)) := by
            ext r
            simp only [mem_inter_iff, mem_Iio, mem_Ico, lt_min_iff]
            tauto
          rw [hset]
        _ = ∫ r : ℝ in Icc 0 ((min t a : ℝ≥0) : ℝ), g r := by
          rw [NNReal.coe_min]
          exact integral_Icc_eq_integral_Ico.symm

/-- Increments of actual stopped occupation integrate exactly over the
deterministic interval, with the strict pre-stopping indicator. -/
theorem stopped_boundedStateOccupationVersion_sub_eq_integral
    (PF : ProcessFamily V) (f : Option V → ℝ)
    (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (tau : PF.Ω → WithTop ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (ω : PF.Ω) :
    stoppedProcess (boundedStateOccupationVersion PF f) tau t ω -
      stoppedProcess (boundedStateOccupationVersion PF f) tau s ω =
      ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        if (r.toNNReal : WithTop ℝ≥0) < tau ω
        then f (Theorem16.dyadicLimit PF.X r.toNNReal ω) else 0 := by
  obtain ⟨C, hC⟩ := hf
  let g : ℝ → ℝ := fun r ↦ if (r.toNNReal : WithTop ℝ≥0) < tau ω
    then f (Theorem16.dyadicLimit PF.X r.toNNReal ω) else 0
  have hgm : Measurable g :=
    ((measurable_of_countable f).comp (Theorem16.measurable_section
      (Theorem16.measurable_uncurry_dyadicLimit PF.measurable_X) ω)).ite
        (measurableSet_lt (by fun_prop) measurable_const) measurable_const
  have hint (u : ℝ≥0) : IntervalIntegrable g volume 0 (u : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le u.coe_nonneg).2
    apply Integrable.of_bound hgm.aestronglyMeasurable C
    filter_upwards [] with r
    dsimp only [g]
    split_ifs
    · exact hC _
    · simpa only [norm_zero] using (abs_nonneg (f none)).trans (hC none)
  rw [stopped_boundedStateOccupationVersion_eq_integral,
    stopped_boundedStateOccupationVersion_eq_integral]
  simp_rw [integral_Icc_eq_integral_Ioc]
  change (∫ r in Ioc 0 (t : ℝ), g r) - (∫ r in Ioc 0 (s : ℝ), g r) =
    ∫ r in Ioc (s : ℝ) (t : ℝ), g r
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg,
    intervalIntegral.integral_of_le s.coe_nonneg,
    intervalIntegral.integral_of_le (show (s : ℝ) ≤ t from hst)] using
    intervalIntegral.integral_interval_sub_left (hint t) (hint s)

/-- The generator pairing of the actual weighted occupation density is the
event-restricted increment of the actual stopped Dynkin compensator. -/
theorem resolventCore_actualStoppedOccupation_pairing_eq_stoppedDrift
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
      ∫ ω in B,
        stoppedProcess (boundedStateOccupationVersion PF (resolventCoreDrift G m q))
          tau t ω -
        stoppedProcess (boundedStateOccupationVersion PF (resolventCoreDrift G m q))
          tau s ω ∂PF.P z := by
  have hf : ∃ C : ℝ, ∀ x, |resolventCoreDrift G m q x| ≤ C :=
    ⟨2 * countableResolventCoreBound q, norm_resolventCoreDrift_le G m hm q⟩
  rw [resolventCore_generator_actualStoppedOccupation_pairing h hG hm hmsum z hB htau hst,
    ← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [Theorem16.ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
  rw [actualStoppedVertexOccupation_tsum_eq_integral PF B tau s t
    (resolventCoreDrift G m q) rfl hf ω hω]
  by_cases hb : ω ∈ B
  · rw [indicator_of_mem hb, stopped_boundedStateOccupationVersion_sub_eq_integral PF
      (resolventCoreDrift G m q) hf tau hst ω]
    simp only [hb, true_and, hω]
  · simp only [hb, false_and, ite_false, integral_zero, indicator_of_notMem hb]

/-- Bounded optional sampling turns the actual occupation pairing into
stopped compact-potential increments. No local harmonicity is assumed. -/
theorem resolventCore_actualStoppedOccupation_pairing_eq_stoppedPotential
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V) {B : Set PF.Ω}
    {tau : PF.Ω → WithTop ℝ≥0}
    (htau : IsStoppingTime PF.naturalFiltration.rightCont tau)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hB : MeasurableSet[PF.naturalFiltration.rightCont s] B)
    (q : CountableResolventCoreIndex V) :
    ⟪valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q,
      actualStoppedOccupationDensity h hG hm hmsum z B tau hst⟫_ℝ =
      ∫ ω in B,
        stoppedProcess (compactResolventCorePotential G m hm PF default q) tau t ω -
        stoppedProcess (compactResolventCorePotential G m hm PF default q) tau s ω ∂PF.P z := by
  have hBm : MeasurableSet B := PF.naturalFiltration.rightCont.le s _ hB
  have htaum : Measurable tau := by
    apply measurable_of_Iic
    intro r
    cases r with
    | top =>
        have htop : tau ⁻¹' Iic ⊤ = (univ : Set PF.Ω) := by
          ext ω
          simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
          exact le_top
        rw [htop]
        exact MeasurableSet.univ
    | coe r => exact PF.naturalFiltration.rightCont.le r _ (htau r)
  let Y := compactResolventCorePotential G m hm PF default q
  let A := boundedStateOccupationVersion PF (resolventCoreDrift G m q)
  let M := compactResolventCoreMartingale G m hm PF default q
  have hYI (r : ℝ≥0) : Integrable (stoppedProcess Y tau r) (PF.P z) :=
    integrable_stopped_compactResolventCorePotential h hG hm hmsum default z q htau r
  have hAI (r : ℝ≥0) : Integrable (stoppedProcess A tau r) (PF.P z) :=
    integrable_stopped_boundedStateOccupationVersion PF (resolventCoreDrift G m q)
      ⟨2 * countableResolventCoreBound q, norm_resolventCoreDrift_le G m hm q⟩ htau r z
  have hrep (r : ℝ≥0) : (∫ ω in B, stoppedProcess M tau r ω ∂PF.P z) =
      (∫ ω in B, stoppedProcess Y tau r ω ∂PF.P z) -
        ∫ ω in B, stoppedProcess A tau r ω ∂PF.P z := by
    rw [← integral_sub (hYI r).integrableOn (hAI r).integrableOn]
    apply setIntegral_congr_fun hBm
    intro ω _
    exact compactResolventCoreMartingale_eq_potential_sub_occupation G m hm PF default q _ ω
  have hstop := MartingaleLimit.stoppedProcess_setIntegral_eq
    (compactResolventCoreMartingale_isMartingale h hG hm hmsum default q z) htau
    ((compactResolventCoreMartingale_ae_isCadlag h hG hm hmsum default q z).mono
      fun _ hω ↦ hω.isRightContinuous) hst hB
  change (∫ ω in B, stoppedProcess M tau s ω ∂PF.P z) =
    ∫ ω in B, stoppedProcess M tau t ω ∂PF.P z at hstop
  rw [hrep s, hrep t] at hstop
  rw [resolventCore_actualStoppedOccupation_pairing_eq_stoppedDrift
    h hG hm hmsum z hBm htaum hst]
  change (∫ ω in B, stoppedProcess A tau t ω - stoppedProcess A tau s ω ∂PF.P z) =
    ∫ ω in B, stoppedProcess Y tau t ω - stoppedProcess Y tau s ω ∂PF.P z
  rw [integral_sub (hAI t).integrableOn (hAI s).integrableOn,
    integral_sub (hYI t).integrableOn (hYI s).integrableOn]
  linarith


/-- The actual stopped occupation has the required uniform graph-pairing
bound on the countable resolvent inputs. -/
theorem actualStoppedOccupation_resolventCore_pairing_bound
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) {B : Set PF.Ω}
    {tau : PF.Ω → WithTop ℝ≥0}
    (htau : IsStoppingTime PF.naturalFiltration.rightCont tau)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hB : MeasurableSet[PF.naturalFiltration.rightCont s] B)
    (q : CountableResolventCoreIndex V) :
    |⟪countableResolventCoreInput G m q,
      actualStoppedOccupationDensity h hG hm hmsum z B tau hst⟫_ℝ| ≤
      (‖actualStoppedOccupationDensity h hG hm hmsum z B tau hst‖ +
        2 * (2048 * (t : ℝ) / m z + 1)) * ‖countableResolventCoreVector G m q‖ := by
  let w := actualStoppedOccupationDensity h hG hm hmsum z B tau hst
  let U := countableResolventCoreVector G m q
  let Y := compactResolventCorePotential G m hm PF z q
  let k := 2048 * (t : ℝ) / m z + 1
  by_cases hn : 0 < ‖U‖
  · have hBm : MeasurableSet B := PF.naturalFiltration.rightCont.le s _ hB
    have hY0i : Integrable (Y 0) (PF.P z) :=
      Integrable.of_bound
        (stronglyMeasurable_compactResolventCorePotential G m hm PF z q 0).aestronglyMeasurable
        (countableResolventCoreBound q)
        (Eventually.of_forall (norm_compactResolventCorePotential_le G m hm PF z q 0))
    have hCI (r : ℝ≥0) : Integrable
        (fun ω ↦ stoppedProcess Y tau r ω - Y 0 ω) (PF.P z) :=
      (integrable_stopped_compactResolventCorePotential h hG hm hmsum z z q htau r).sub hY0i
    have hcenter : (∫ ω in B,
        stoppedProcess Y tau t ω - stoppedProcess Y tau s ω ∂PF.P z) =
        (∫ ω in B, stoppedProcess Y tau t ω - Y 0 ω ∂PF.P z) -
        ∫ ω in B, stoppedProcess Y tau s ω - Y 0 ω ∂PF.P z := by
      rw [← integral_sub (hCI t).integrableOn (hCI s).integrableOn]
      apply setIntegral_congr_fun hBm
      intro ω _
      dsimp only
      ring
    have hg : |⟪valueInclusion G m U - countableResolventCoreInput G m q, w⟫_ℝ| ≤
        2 * k * ‖U‖ := by
      change |⟪valueInclusion G m (countableResolventCoreVector G m q) -
        countableResolventCoreInput G m q,
        actualStoppedOccupationDensity h hG hm hmsum z B tau hst⟫_ℝ| ≤ _
      rw [resolventCore_actualStoppedOccupation_pairing_eq_stoppedPotential
        h hG hm hmsum z z htau hst hB]
      change |∫ ω in B, stoppedProcess Y tau t ω - stoppedProcess Y tau s ω ∂PF.P z| ≤ _
      rw [hcenter]
      calc
        _ ≤ |∫ ω in B, stoppedProcess Y tau t ω - Y 0 ω ∂PF.P z| +
            |∫ ω in B, stoppedProcess Y tau s ω - Y 0 ω ∂PF.P z| := abs_sub _ _
        _ ≤ k * ‖U‖ + k * ‖U‖ := add_le_add
          (abs_setIntegral_stoppedCorePotential_centered_le h hG hm hmsum z z q htau hBm le_rfl hn)
          (abs_setIntegral_stoppedCorePotential_centered_le h hG hm hmsum z z q htau hBm hst hn)
        _ = 2 * k * ‖U‖ := by ring
    have hlin : ⟪countableResolventCoreInput G m q, w⟫_ℝ =
        ⟪valueInclusion G m U, w⟫_ℝ -
          ⟪valueInclusion G m U - countableResolventCoreInput G m q, w⟫_ℝ := by
      rw [inner_sub_left]
      ring
    change |⟪countableResolventCoreInput G m q, w⟫_ℝ| ≤ (‖w‖ + 2 * k) * ‖U‖
    rw [hlin]
    calc
      _ ≤ |⟪valueInclusion G m U, w⟫_ℝ| +
          |⟪valueInclusion G m U - countableResolventCoreInput G m q, w⟫_ℝ| := abs_sub _ _
      _ ≤ ‖U‖ * ‖w‖ + 2 * k * ‖U‖ := add_le_add
        ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (valueInclusion_norm_le G m U) (norm_nonneg w))) hg
      _ = (‖w‖ + 2 * k) * ‖U‖ := by ring
  · have hU0 : U = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg U))
    have hinput : countableResolventCoreInput G m q = 0 := by
      apply LinearMap.ker_eq_bot.mp (oneResolventLift_ker_eq_bot G m hm)
      change U = oneResolventLift G m 0
      rw [hU0, map_zero]
    change |⟪countableResolventCoreInput G m q, w⟫_ℝ| ≤ (‖w‖ + 2 * k) * ‖U‖
    simp only [hinput, hU0, inner_zero_left, abs_zero, norm_zero, mul_zero, le_refl]

/-- Actual event-restricted stopped occupation belongs to the FULL form
domain. The stopping time may be infinite and no finite-support closure is used. -/
theorem actualStoppedOccupation_exists_fullDomain
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) {B : Set PF.Ω}
    {tau : PF.Ω → WithTop ℝ≥0}
    (htau : IsStoppingTime PF.naturalFiltration.rightCont tau)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hB : MeasurableSet[PF.naturalFiltration.rightCont s] B) :
    ∃ W : hilbertDomain G m, valueInclusion G m W =
      actualStoppedOccupationDensity h hG hm hmsum z B tau hst := by
  let w := actualStoppedOccupationDensity h hG hm hmsum z B tau hst
  let C := ‖w‖ + 2 * (2048 * (t : ℝ) / m z + 1)
  apply exists_fullDomain_of_resolvent_pairing_bound G m hm w
  refine ⟨C, fun f ↦ (denseRange_countableResolventCoreInput G m hm).induction_on f ?_ ?_⟩
  · exact isClosed_le (continuous_id.inner continuous_const).abs
      (continuous_const.mul (oneResolventLift G m).continuous.norm)
  · intro q
    exact actualStoppedOccupation_resolventCore_pairing_bound h hG hm hmsum z htau hst hB q

end ReflectedGMS

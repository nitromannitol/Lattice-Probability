/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ActualStoppedOccupationDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIdentification
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedOccupationFormDomain
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1TrajectoryOccupation

/-!
# The actual stopped occupation vector

Detailed balance and summability of the speed measure put every finite-time,
event-restricted stopped occupation density in the weighted value Hilbert space.
The construction uses the actual process, with no full-domain hypothesis.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- Expected occupation mass of a vertex, restricted to an event and to times
strictly before `tau`. -/
noncomputable def actualStoppedOccupationMass (PF : ProcessFamily V)
    (z : V) (B : Set PF.Ω) (tau : PF.Ω → WithTop ℝ≥0) (s t : ℝ≥0) (x : V) : ℝ :=
  ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
    (PF.P z {ω | ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω ∧
      PF.X r.toNNReal ω = some x}).toReal

theorem actualStoppedOccupationMass_nonneg (PF : ProcessFamily V)
    (z : V) (B : Set PF.Ω) (tau : PF.Ω → WithTop ℝ≥0) (s t : ℝ≥0) (x : V) :
    0 ≤ actualStoppedOccupationMass PF z B tau s t x :=
  integral_nonneg fun _ ↦ ENNReal.toReal_nonneg

/-- Reversibility bounds even arbitrary event-restricted transition masses. -/
theorem actualStoppedOccupation_probability_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z x : V) (r : ℝ≥0) (E : Set PF.Ω) :
    (PF.P z (E ∩ {ω | PF.X r ω = some x})).toReal ≤ m x / m z := by
  calc
    _ ≤ (PF.P z {ω | PF.X r ω = some x}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_right)
    _ ≤ m x / m z := by
      apply (le_div_iff₀ (hm z)).mpr
      rw [mul_comm, reflected_transition_detailedBalance h hG hm hmsum]
      exact (mul_le_mul_of_nonneg_left (measureReal_le_one :
        (PF.P x {ω | PF.X r ω = some z}).toReal ≤ 1) (hm x).le).trans_eq
          (mul_one _)

/-- The exact finite-interval domination of the actual occupation mass. -/
theorem actualStoppedOccupationMass_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) (B : Set PF.Ω)
    (tau : PF.Ω → WithTop ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (x : V) :
    actualStoppedOccupationMass PF z B tau s t x ≤
      ((t : ℝ) - (s : ℝ)) * (m x / m z) := by
  unfold actualStoppedOccupationMass
  calc
    _ ≤ ∫ _r : ℝ in Icc (s : ℝ) (t : ℝ), m x / m z := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
        (integrable_const _)
      filter_upwards [] with r
      simpa only [setOf_and, inter_assoc] using
        actualStoppedOccupation_probability_le h hG hm hmsum z x r.toNNReal
          {ω | ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω}
    _ = _ := by
      rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
        Real.volume_real_Icc_of_le (by exact_mod_cast hst)]

/-- The actual stopped occupation density is square summable after the
required division by the square root of the speed. -/
theorem actualStoppedOccupationDensity_memℓp
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) (B : Set PF.Ω)
    (tau : PF.Ω → WithTop ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) :
    Memℓp (fun x ↦ actualStoppedOccupationMass PF z B tau s t x /
      Real.sqrt (m x)) 2 := by
  let C : ℝ := ((t : ℝ) - (s : ℝ)) / m z
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hst)) (hm z).le
  have hmajor : Memℓp (fun x ↦ C * Real.sqrt (m x)) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs, mul_pow, Real.sq_sqrt (hm _).le] using hmsum.mul_left (C ^ 2)
  apply hmajor.mono
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (actualStoppedOccupationMass_nonneg PF z B tau s t x)
      (Real.sqrt_nonneg _))]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (hm x))).mpr
  calc
    actualStoppedOccupationMass PF z B tau s t x ≤
        ((t : ℝ) - (s : ℝ)) * (m x / m z) :=
      actualStoppedOccupationMass_le h hG hm hmsum z B tau hst x
    _ = C * Real.sqrt (m x) * Real.sqrt (m x) := by
      rw [mul_assoc, Real.mul_self_sqrt (hm x).le]
      dsimp [C]
      ring

/-- The actual vector in the full form's value space. -/
noncomputable def actualStoppedOccupationDensity
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (z : V) (B : Set PF.Ω)
    (tau : PF.Ω → WithTop ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) : ValueSpace V :=
  ⟨_, actualStoppedOccupationDensity_memℓp h hG hm hmsum z B tau hst⟩

open Classical in
/-- Each coordinate of the occupation vector is the expected actual stopped
path occupation. The jointly measurable version is used only to justify Fubini. -/
theorem actualStoppedOccupationMass_eq_expected_occupation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (z : V) {B : Set PF.Ω} (hB : MeasurableSet B)
    {tau : PF.Ω → WithTop ℝ≥0} (htau : Measurable tau)
    (s t : ℝ≥0) (x : V) :
    actualStoppedOccupationMass PF z B tau s t x =
      ∫ ω, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        if ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω ∧
          PF.X r.toNNReal ω = some x then (1 : ℝ) else 0) ∂PF.P z := by
  classical
  obtain ⟨Y, hY, _, hYX⟩ := ReflectedWalk.Theorem16.exists_jointlyMeasurable_version
    PF.measurable_X (h z).2.2.1 (h z).2.2.2.1
  let F : ℝ → PF.Ω → ℝ := fun r ω ↦
    if ω ∈ B ∧ (r.toNNReal : WithTop ℝ≥0) < tau ω ∧
      Y r.toNNReal ω = some x then 1 else 0
  have hset : MeasurableSet {p : ℝ × PF.Ω | p.2 ∈ B ∧
      (p.1.toNNReal : WithTop ℝ≥0) < tau p.2 ∧
      Y p.1.toNNReal p.2 = some x} := by
    refine (hB.preimage measurable_snd).inter (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt (by fun_prop) (htau.comp measurable_snd)
    · exact (hY.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
        measurable_snd)) (ReflectedWalk.Theorem16.measurableSet_option {some x})
  have hF : Measurable (Function.uncurry F) := by
    exact measurable_const.ite hset measurable_const
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Icc (s : ℝ) (t : ℝ))).prod (PF.P z)) := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    filter_upwards [] with p
    dsimp only [Function.uncurry, F]
    by_cases hp : p.2 ∈ B ∧ (p.1.toNNReal : WithTop ℝ≥0) < tau p.2 ∧
        Y p.1.toNNReal p.2 = some x
    · rw [if_pos hp]
      norm_num
    · rw [if_neg hp]
      norm_num
  calc
    actualStoppedOccupationMass PF z B tau s t x =
        ∫ r : ℝ in Icc (s : ℝ) (t : ℝ), (∫ ω, F r ω ∂PF.P z) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r _
      have hsection : MeasurableSet {ω | ω ∈ B ∧
          (r.toNNReal : WithTop ℝ≥0) < tau ω ∧ Y r.toNNReal ω = some x} :=
        hset.preimage (measurable_const.prodMk measurable_id)
      have hmeasure : PF.P z {ω | ω ∈ B ∧
          (r.toNNReal : WithTop ℝ≥0) < tau ω ∧ PF.X r.toNNReal ω = some x} =
          PF.P z {ω | ω ∈ B ∧
          (r.toNNReal : WithTop ℝ≥0) < tau ω ∧ Y r.toNNReal ω = some x} := by
        apply measure_congr
        filter_upwards [hYX] with ω hω
        simp only [hω]
      dsimp only
      rw [hmeasure]
      change (PF.P z).real _ = ∫ ω, F r ω ∂PF.P z
      simpa only [F, Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
        (integral_indicator_one (μ := PF.P z) hsection).symm
    _ = ∫ ω, (∫ r : ℝ in Icc (s : ℝ) (t : ℝ), F r ω) ∂PF.P z :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hYX] with ω hω
      apply setIntegral_congr_fun measurableSet_Icc
      intro r _
      simp only [F, hω]

end ReflectedGMS

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedResolventMomentBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CorePotentialUniformBound
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreApproximation

/-!
# Fixed-start moment bounds for stopped resolvent-core potentials

The stationary square-maximal envelope transfers to each fixed starting law.
Young's inequality then gives the linear graph-norm estimate needed by the
full-domain stopped-occupation argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace Classical

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- A bounded state compensator remains integrable at an arbitrary stopping
time because the actual stopped value at deterministic time `t` is bounded. -/
theorem integrable_stopped_boundedStateOccupationVersion
    (PF : ProcessFamily V) (f : Option V → ℝ)
    (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    {tau : PF.Ω → WithTop ℝ≥0}
    (htau : IsStoppingTime PF.naturalFiltration.rightCont tau) (t : ℝ≥0) (z : V) :
    Integrable (stoppedProcess (boundedStateOccupationVersion PF f) tau t) (PF.P z) := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := (abs_nonneg (f none)).trans (hC none)
  have hA : StronglyAdapted PF.naturalFiltration.rightCont
      (boundedStateOccupationVersion PF f) := fun r ↦
    (stronglyMeasurable_boundedStateOccupationVersion PF f r).mono
      (PF.naturalFiltration.le_rightCont r)
  apply Integrable.of_bound
    (hA.stronglyMeasurable_stoppedProcess
      (continuous_boundedStateOccupationVersion PF f hC) htau t).aestronglyMeasurable
    ((t : ℝ) * C)
  filter_upwards [] with omega
  let theta := min (t : WithTop ℝ≥0) (tau omega)
  have htheta : theta ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hthetat : theta.untopA ≤ t :=
    (WithTop.untopA_le_iff htheta).2 (min_le_left _ _)
  change ‖boundedStateOccupationVersion PF f theta.untopA omega‖ ≤ (t : ℝ) * C
  exact (norm_boundedStateOccupationVersion_le PF f theta.untopA hC omega).trans
    (mul_le_mul_of_nonneg_right (show (theta.untopA : ℝ) ≤ t from hthetat) hC0)

/-- Actual compact core potentials are integrable at the stopped times used
by localization, using their already constructed Dynkin martingales. -/
theorem integrable_stopped_compactResolventCorePotential
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V) (q : CountableResolventCoreIndex V)
    {tau : PF.Ω → WithTop ℝ≥0}
    (htau : IsStoppingTime PF.naturalFiltration.rightCont tau) (t : ℝ≥0) :
    Integrable (stoppedProcess (compactResolventCorePotential G m hm PF default q) tau t)
      (PF.P z) := by
  have hMI := MartingaleLimit.integrable_stoppedProcess_of_ae_rightContinuous
    (compactResolventCoreMartingale_isMartingale h hG hm hmsum default q z) htau
    ((compactResolventCoreMartingale_ae_isCadlag h hG hm hmsum default q z).mono
      fun _ homega ↦ homega.isRightContinuous) t
  have hAI := integrable_stopped_boundedStateOccupationVersion PF
    (resolventCoreDrift G m q)
    ⟨2 * countableResolventCoreBound q, norm_resolventCoreDrift_le G m hm q⟩ htau t z
  apply (hMI.add hAI).congr
  filter_upwards [] with omega
  change stoppedProcess (compactResolventCoreMartingale G m hm PF default q) tau t omega +
      stoppedProcess (boundedStateOccupationVersion PF (resolventCoreDrift G m q)) tau t omega =
    stoppedProcess (compactResolventCorePotential G m hm PF default q) tau t omega
  dsimp only [stoppedProcess]
  rw [compactResolventCoreMartingale_eq_potential_sub_occupation]
  ring

/-- The stationary maximal envelope applies under every actual starting law,
retaining its explicit speed-atom factor. -/
theorem exists_start_sq_envelope_compactResolventCorePotential
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V) (q : CountableResolventCoreIndex V)
    (T : ℝ≥0) :
    ∃ D : PF.Ω → ℝ, Measurable D ∧ Integrable D (PF.P z) ∧
      (∀ᵐ omega ∂PF.P z, 0 ≤ D omega ∧ ∀ t ≤ T,
        (compactResolventCorePotential G m hm PF default q t omega -
          compactResolventCorePotential G m hm PF default q 0 omega) ^ 2 ≤ D omega) ∧
      m z * (∫ omega, D omega ∂PF.P z) ≤
        2048 * (T : ℝ) * G.Energy (countableResolventCoreFeature G m q) := by
  obtain ⟨D, hDm, hDi, hDb, hDint⟩ :=
    exists_integrable_sq_envelope_compactResolventCorePotential
      h hG hm hmsum default q T
  have hD0 : 0 ≤ᵐ[reflectedSpeedLaw PF m] D := by
    filter_upwards [hDb] with omega homega
    simpa using homega 0 (zero_le : 0 ≤ T)
  have hDz : Integrable D (PF.P z) :=
    (integrable_smul_measure (ENNReal.ofReal_pos.mpr (hm z)).ne'
      ENNReal.ofReal_ne_top).mp
        (hDi.mono_measure (smul_start_le_reflectedSpeedLaw PF m z))
  refine ⟨D, hDm, hDz, ?_, ?_⟩
  · exact (ae_reflectedSpeedLaw_iff PF m hm _).1 (hD0.and hDb) z
  · have hb := integral_mono_measure (smul_start_le_reflectedSpeedLaw PF m z) hD0 hDi
    have hb' : m z * (∫ omega, D omega ∂PF.P z) ≤
        ∫ omega, D omega ∂reflectedSpeedLaw PF m := by
      simpa only [integral_smul_measure, ENNReal.toReal_ofReal (hm z).le,
        smul_eq_mul] using hb
    exact hb'.trans hDint

/-- A graph-norm bound on stopped core-potential increments. The elementary
quadratic inequality avoids any additional maximal theorem. -/
theorem abs_setIntegral_stoppedCorePotential_centered_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V) (q : CountableResolventCoreIndex V)
    {tau : PF.Ω → WithTop ℝ≥0}
    (htau : IsStoppingTime PF.naturalFiltration.rightCont tau)
    {B : Set PF.Ω} (hB : MeasurableSet B) {u T : ℝ≥0} (hu : u ≤ T)
    (hn : 0 < ‖countableResolventCoreVector G m q‖) :
    |∫ omega in B,
      stoppedProcess (compactResolventCorePotential G m hm PF default q) tau u omega -
        compactResolventCorePotential G m hm PF default q 0 omega ∂PF.P z| ≤
      (2048 * (T : ℝ) / m z + 1) * ‖countableResolventCoreVector G m q‖ := by
  let Y := compactResolventCorePotential G m hm PF default q
  let n := ‖countableResolventCoreVector G m q‖
  let c := 2048 * (T : ℝ) / m z
  let F : PF.Ω → ℝ := B.indicator (fun omega ↦ |stoppedProcess Y tau u omega - Y 0 omega|)
  have hY0i : Integrable (Y 0) (PF.P z) :=
    Integrable.of_bound
      (stronglyMeasurable_compactResolventCorePotential G m hm PF default q 0).aestronglyMeasurable
      (countableResolventCoreBound q)
      (Eventually.of_forall (norm_compactResolventCorePotential_le G m hm PF default q 0))
  have hCi := (integrable_stopped_compactResolventCorePotential
    h hG hm hmsum default z q htau u).sub hY0i
  have hFi : Integrable F (PF.P z) := hCi.norm.indicator hB
  obtain ⟨D, _, hDi, hDb, hDint⟩ :=
    exists_start_sq_envelope_compactResolventCorePotential h hG hm hmsum default z q T
  have hpoint : ∀ᵐ omega ∂PF.P z, n * F omega ≤ D omega + n ^ 2 := by
    filter_upwards [hDb] with omega homega
    let theta := min (u : WithTop ℝ≥0) (tau omega)
    have htheta : theta ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hthetaT : theta.untopA ≤ T :=
      ((WithTop.untopA_le_iff htheta).2 (min_le_left _ _)).trans hu
    have hs := homega.2 theta.untopA hthetaT
    change (stoppedProcess Y tau u omega - Y 0 omega) ^ 2 ≤ D omega at hs
    by_cases hb : omega ∈ B
    · change n * B.indicator (fun omega ↦ |stoppedProcess Y tau u omega - Y 0 omega|)
          omega ≤ _
      rw [indicator_of_mem hb]
      nlinarith [sq_nonneg (|stoppedProcess Y tau u omega - Y 0 omega| - n),
        sq_abs (stoppedProcess Y tau u omega - Y 0 omega),
        mul_nonneg hn.le (abs_nonneg (stoppedProcess Y tau u omega - Y 0 omega))]
    · change n * B.indicator (fun omega ↦ |stoppedProcess Y tau u omega - Y 0 omega|)
          omega ≤ _
      rw [indicator_of_notMem hb, mul_zero]
      exact add_nonneg homega.1 (sq_nonneg n)
  have hb := integral_mono_ae (hFi.const_mul n) (hDi.add (integrable_const (n ^ 2))) hpoint
  have hb' : n * (∫ omega, F omega ∂PF.P z) ≤
      (∫ omega, D omega ∂PF.P z) + n ^ 2 := by
    simpa [integral_const_mul, integral_add hDi (integrable_const (n ^ 2))] using hb
  have hzero : unweight m (valueInclusion G m (0 : hilbertDomain G m)) = 0 := by
    ext x
    simp [unweight]
  have hE : G.Energy (countableResolventCoreFeature G m q) ≤ n ^ 2 := by
    simpa only [hzero, sub_zero] using
      countableResolventCore_energy_error_le_norm_sq G m 0 q
  have hDle : (∫ omega, D omega ∂PF.P z) ≤ c * n ^ 2 := by
    have hmul : (∫ omega, D omega ∂PF.P z) * m z ≤
        2048 * (T : ℝ) * n ^ 2 := calc
      (∫ omega, D omega ∂PF.P z) * m z ≤
          2048 * (T : ℝ) * G.Energy (countableResolventCoreFeature G m q) := by
        simpa only [mul_comm] using hDint
      _ ≤ 2048 * (T : ℝ) * n ^ 2 :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    change (∫ omega, D omega ∂PF.P z) ≤
      (2048 * (T : ℝ) / m z) * n ^ 2
    calc
      (∫ omega, D omega ∂PF.P z) ≤
          (2048 * (T : ℝ) * n ^ 2) / m z := (le_div_iff₀ (hm z)).2 hmul
      _ = (2048 * (T : ℝ) / m z) * n ^ 2 := by ring
  have hmean : (∫ omega, F omega ∂PF.P z) ≤ (c + 1) * n := by
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith
  have hnorm : |∫ omega in B, stoppedProcess Y tau u omega - Y 0 omega ∂PF.P z| ≤
      ∫ omega, F omega ∂PF.P z := by
    rw [show (∫ omega, F omega ∂PF.P z) =
      ∫ omega in B, |stoppedProcess Y tau u omega - Y 0 omega| ∂PF.P z from
        integral_indicator hB]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := (PF.P z).restrict B)
        (fun omega ↦ stoppedProcess Y tau u omega - Y 0 omega))
  exact hnorm.trans hmean

end ReflectedGMS

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StateDynkinMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1SemigroupTimeIntegral
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1TrajectoryOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIntegrableTrajectoryConditional
import Mathlib.Probability.Martingale.Basic

/-!
# A bounded-state Dynkin martingale adapter

This module factors the probabilistic part of Dynkin's formula for the actual
reflected process.  The analytic semigroup evolution and an exactly adapted
version of the generator occupation are supplied as hypotheses; all required
integrability of the process, occupation, and future trajectory tests is
derived from boundedness and speed-`L¹` integrability.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

private theorem integrable_bounded_vertexSpeedMeasure
    (m : V → ℝ) (hmsum : Summable m) (u : V → ℝ) (C : ℝ)
    (hu : ∀ x, ‖u x‖ ≤ C) :
    Integrable u (vertexSpeedMeasure m) := by
  let x₀ : V := Classical.choice (inferInstance : Nonempty V)
  have hC : 0 ≤ C := (norm_nonneg (u x₀)).trans (hu x₀)
  letI : IsFiniteMeasure (vertexSpeedMeasure m) :=
    vertexSpeedMeasure_isFinite m hmsum
  exact Integrable.of_bound (measurable_of_countable u).aestronglyMeasurable C
    (ae_of_all _ fun x ↦ hu x)

private theorem integrable_stateDynkinCompensator
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {g : V → ℝ}
    (hg : Integrable g (vertexSpeedMeasure m))
    (A : ℝ≥0 → PF.Ω → ℝ)
    (hAeq : ∀ (t : ℝ≥0) (x : V), A t =ᵐ[PF.P x]
      fun ω ↦ trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t
        (PF.trajectory ω))
    (t : ℝ≥0) (z : V) : Integrable (A t) (PF.P z) := by
  have hlaw := integrable_trajectoryStateIntegral_law_of_L1
    h hG hm hmsum hg t z
  have htraj : Measurable PF.trajectory := measurable_pi_iff.mpr PF.measurable_X
  have hraw : Integrable (fun ω ↦
      trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t
        (PF.trajectory ω)) (PF.P z) := by
    rw [ProcessFamily.law] at hlaw
    have hcomp := (integrable_map_measure
      (measurable_trajectoryStateIntegral _ t).aestronglyMeasurable
      htraj.aemeasurable).mp hlaw
    convert hcomp using 1
    rfl
  exact hraw.congr (hAeq t z).symm

private theorem measurable_stateDynkinTrajectoryIncrement
    (u g : V → ℝ) (t : ℝ≥0) :
    Measurable (fun γ : Trajectory V ↦
      (γ t).elim 0 u -
        trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t γ) := by
  exact ((measurable_of_countable (fun q : Option V ↦ q.elim 0 u)).comp
    (measurable_pi_apply t)).sub (measurable_trajectoryStateIntegral _ t)

private theorem integrable_stateDynkinTrajectoryIncrement_law
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (u g : V → ℝ) (C : ℝ)
    (hu : ∀ x, ‖u x‖ ≤ C) (hg : Integrable g (vertexSpeedMeasure m))
    (t : ℝ≥0) (z : V) :
    Integrable (fun γ : Trajectory V ↦
      (γ t).elim 0 u -
        trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t γ)
      (PF.law z) := by
  apply Integrable.sub
  · apply Integrable.of_bound
      (((measurable_of_countable (fun q : Option V ↦ q.elim 0 u)).comp
        (measurable_pi_apply t)).aestronglyMeasurable) C
    filter_upwards [] with γ
    change ‖(γ t).elim 0 u‖ ≤ C
    cases γ t with
    | none =>
        let x₀ : V := Classical.choice (inferInstance : Nonempty V)
        simpa only [Option.elim_none, norm_zero] using
          (norm_nonneg (u x₀)).trans (hu x₀)
    | some x => simpa only [Option.elim_some] using hu x
  · exact integrable_trajectoryStateIntegral_law_of_L1
      h hG hm hmsum hg t z

private theorem integrable_stateDynkinTrajectoryIncrement_shifted
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (u g : V → ℝ) (C : ℝ)
    (hu : ∀ x, ‖u x‖ ≤ C) (hg : Integrable g (vertexSpeedMeasure m))
    (s t : ℝ≥0) (z : V) :
    Integrable (fun ω ↦
      ((shiftedPath PF.X s ω) t).elim 0 u -
        trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t
          (shiftedPath PF.X s ω)) (PF.P z) := by
  apply Integrable.sub
  · apply Integrable.of_bound
      ((((measurable_of_countable (fun q : Option V ↦ q.elim 0 u)).comp
        (measurable_pi_apply t)).comp
          (measurable_shiftedPath PF.measurable_X s)).aestronglyMeasurable) C
    filter_upwards [] with ω
    change ‖((shiftedPath PF.X s ω) t).elim 0 u‖ ≤ C
    cases shiftedPath PF.X s ω t with
    | none =>
        let x₀ : V := Classical.choice (inferInstance : Nonempty V)
        simpa only [Option.elim_none, norm_zero] using
          (norm_nonneg (u x₀)).trans (hu x₀)
    | some x => simpa only [Option.elim_some] using hu x
  · exact integrable_trajectoryStateIntegral_shifted_of_L1
      h hG hm hmsum hg s t z

private theorem integral_stateDynkinTrajectoryIncrement_law
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (u g : V → ℝ) (C : ℝ)
    (hu : ∀ x, ‖u x‖ ≤ C) (hg : Integrable g (vertexSpeedMeasure m))
    (hdynkin : ∀ (t : ℝ≥0) (x : V),
      weightedL1SemigroupAction G m hm hmsum t u x - u x =
        weightedL1SemigroupTimeIntegral G m hm hmsum t g x)
    (t : ℝ≥0) (x : V) :
    (∫ γ : Trajectory V,
      ((γ t).elim 0 u -
        trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t γ)
      ∂PF.law x) = u x := by
  have huL1 := integrable_bounded_vertexSpeedMeasure m hmsum u C hu
  have hstate : Integrable (fun γ : Trajectory V ↦ (γ t).elim 0 u)
      (PF.law x) := by
    apply Integrable.of_bound
      (((measurable_of_countable (fun q : Option V ↦ q.elim 0 u)).comp
        (measurable_pi_apply t)).aestronglyMeasurable) C
    filter_upwards [] with γ
    change ‖(γ t).elim 0 u‖ ≤ C
    cases γ t with
    | none =>
        let x₀ : V := Classical.choice (inferInstance : Nonempty V)
        simpa only [Option.elim_none, norm_zero] using
          (norm_nonneg (u x₀)).trans (hu x₀)
    | some y => simpa only [Option.elim_some] using hu y
  have hocc := integrable_trajectoryStateIntegral_law_of_L1
    h hG hm hmsum hg t x
  rw [integral_sub hstate hocc]
  have htraj : Measurable PF.trajectory := measurable_pi_iff.mpr PF.measurable_X
  have hstateEq : (∫ γ : Trajectory V, (γ t).elim 0 u ∂PF.law x) =
      weightedL1SemigroupAction G m hm hmsum t u x := by
    calc
      (∫ γ : Trajectory V, (γ t).elim 0 u ∂PF.law x) =
          ∫ ω, (PF.X t ω).elim 0 u ∂PF.P x := by
        rw [ProcessFamily.law]
        exact integral_map htraj.aemeasurable
          (((measurable_of_countable (fun q : Option V ↦ q.elim 0 u)).comp
            (measurable_pi_apply t)).aestronglyMeasurable)
      _ = weightedL1SemigroupAction G m hm hmsum t u x :=
        integral_reflected_at_time_eq_weightedL1SemigroupAction
          h hG hm hmsum t x u huL1
  rw [hstateEq]
  have hoccEq :
      (∫ γ : Trajectory V,
        trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t γ
        ∂PF.law x) = weightedL1SemigroupTimeIntegral G m hm hmsum t g x := by
    have hFint := integrable_dyadicStateObservable_time_start
      h hG hm hmsum hg t x
    unfold weightedL1SemigroupTimeIntegral
    rw [ProcessFamily.law, integral_map htraj.aemeasurable
      (measurable_trajectoryStateIntegral _ t).aestronglyMeasurable]
    change (∫ ω, (∫ r in Icc 0 (t : ℝ), dyadicStateObservable PF g ω r)
      ∂PF.P x) = _
    rw [integral_integral_swap hFint]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    exact (weightedL1SemigroupAction_eq_integral_dyadicStateObservable
      h hG hm hmsum hg r x).symm
  rw [hoccEq]
  linarith [hdynkin t x]

/-- A bounded state function satisfying its speed-`L¹` semigroup Dynkin
identity, minus any exactly adapted version of the corresponding trajectory
occupation, is a martingale for the actual reflected process. -/
theorem stateDynkinMartingale_isMartingale
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (u g : V → ℝ) (C : ℝ)
    (hu : ∀ x, ‖u x‖ ≤ C) (hg : Integrable g (vertexSpeedMeasure m))
    (hdynkin : ∀ (t : ℝ≥0) (x : V),
      weightedL1SemigroupAction G m hm hmsum t u x - u x =
        weightedL1SemigroupTimeIntegral G m hm hmsum t g x)
    (A : ℝ≥0 → PF.Ω → ℝ)
    (hAadapt : StronglyAdapted PF.naturalFiltration A)
    (hAeq : ∀ (t : ℝ≥0) (x : V), A t =ᵐ[PF.P x]
      fun ω ↦ trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) t
        (PF.trajectory ω))
    (z : V) :
    Martingale (fun t ω ↦ (PF.X t ω).elim 0 u - A t ω)
      PF.naturalFiltration (PF.P z) := by
  let M : ℝ≥0 → PF.Ω → ℝ := fun t ω ↦ (PF.X t ω).elim 0 u - A t ω
  change Martingale M PF.naturalFiltration (PF.P z)
  have hstateAdapt : StronglyAdapted PF.naturalFiltration
      (fun t ω ↦ (PF.X t ω).elim 0 u) := by
    intro t
    have hmeasX : Measurable[PF.naturalFiltration t] (PF.X t) := by
      change Measurable[pastSigma PF.X t] (PF.X t)
      intro B hB
      apply measurableSet_pastSigma_iff.mpr
      refine ⟨{p | p ⟨t, by simp⟩ ∈ B}, ?_, rfl⟩
      exact hB.preimage (measurable_pi_apply _)
    exact ((measurable_of_countable (fun q : Option V ↦ q.elim 0 u)).comp
      hmeasX).stronglyMeasurable
  refine ⟨hstateAdapt.sub hAadapt, ?_⟩
  intro s t hst
  let Φ : Trajectory V → ℝ := fun γ ↦
    (γ (t - s)).elim 0 u -
      trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 g) (t - s) γ
  have hΦmeas : Measurable Φ :=
    measurable_stateDynkinTrajectoryIncrement u g (t - s)
  have hΦshift : Integrable (fun ω ↦ Φ (shiftedPath PF.X s ω)) (PF.P z) :=
    integrable_stateDynkinTrajectoryIncrement_shifted
      h hG hm hmsum u g C hu hg s (t - s) z
  have hΦlaw : ∀ x, Integrable Φ (PF.law x) := by
    intro x
    exact integrable_stateDynkinTrajectoryIncrement_law
      h hG hm hmsum u g C hu hg (t - s) x
  have hce := ReflectedMarkovConditional.condExp_trajectory_test_integrable
    h z s Φ hΦmeas hΦshift hΦlaw
  have hce' :
      (PF.P z)[(fun ω ↦ Φ (shiftedPath PF.X s ω)) |
        PF.naturalFiltration s] =ᵐ[PF.P z]
      fun ω ↦ (PF.X s ω).elim 0 u := by
    apply hce.trans
    filter_upwards [] with ω
    cases hx : PF.X s ω with
    | none => simp [hx]
    | some x =>
        simp only [hx, Option.elim_some]
        exact integral_stateDynkinTrajectoryIncrement_law
          h hG hm hmsum u g C hu hg hdynkin (t - s) x
  have hAint := integrable_stateDynkinCompensator
    h hG hm hmsum hg A hAeq s z
  have hincr : M t =ᵐ[PF.P z]
      fun ω ↦ Φ (shiftedPath PF.X s ω) - A s ω := by
    filter_upwards [hAeq t z, hAeq s z,
      trajectoryStateIntegral_shifted_ae_eq_sub_of_L1
        h hG hm hmsum hg s (t - s) z] with ω hAt hAs hshift
    dsimp only [M, Φ]
    rw [hAt, hAs, hshift]
    simp only [shiftedPath, tsub_add_cancel_of_le hst]
    change (PF.X t ω).elim 0 u -
        (∫ r : ℝ in Icc 0 (t : ℝ), dyadicStateObservable PF g ω r) =
      ((PF.X t ω).elim 0 u -
        ((∫ r : ℝ in Icc 0 ((s + (t - s) : ℝ≥0) : ℝ),
          dyadicStateObservable PF g ω r) -
        ∫ r : ℝ in Icc 0 (s : ℝ), dyadicStateObservable PF g ω r)) -
      ∫ r : ℝ in Icc 0 (s : ℝ), dyadicStateObservable PF g ω r
    rw [add_tsub_cancel_of_le hst]
    ring
  calc
    (PF.P z)[M t | PF.naturalFiltration s] =ᵐ[PF.P z]
        (PF.P z)[(fun ω ↦ Φ (shiftedPath PF.X s ω) - A s ω) |
          PF.naturalFiltration s] := condExp_congr_ae hincr
    _ =ᵐ[PF.P z]
        (PF.P z)[(fun ω ↦ Φ (shiftedPath PF.X s ω)) |
          PF.naturalFiltration s] -
        (PF.P z)[A s | PF.naturalFiltration s] :=
      condExp_sub hΦshift hAint _
    _ =ᵐ[PF.P z] M s := by
      have hAself := condExp_of_stronglyMeasurable (PF.naturalFiltration.le s)
        (hAadapt s) hAint
      rw [hAself]
      filter_upwards [hce'] with ω hΦ
      rw [Pi.sub_apply, hΦ]

end ReflectedGMS

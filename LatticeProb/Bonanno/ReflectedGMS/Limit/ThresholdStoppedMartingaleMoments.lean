/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ThresholdStoppedMartingaleMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CommonSquareLocalizer
import LatticeProb.Bonanno.ReflectedGMS.Limit.UCPBracketLocalization

/-!
# Martingale and moment inputs after threshold stopping

This file supplies the martingale, compensated-square martingale, and terminal
second-moment inputs needed by the interpolation-tightness theorem after the
threshold localization of `UCPBracketLocalization`.  It retains the project's
exact indicator convention: on paths where the threshold stopping time is zero,
both stopped processes vanish.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Stopping a square-integrable martingale with the project's exact
`{τ > 0}` indicator preserves both the martingale property and deterministic-
time `L²` integrability.  The stopping time may be infinite. -/
theorem indicator_stoppedProcess_martingale_and_memLp_two
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (h2 : ∀ t, MemLp (M t) 2 P) :
    Martingale
        (stoppedProcess (fun t => {ω | ⊥ < τ ω}.indicator (M t)) τ) F P ∧
      ∀ t, MemLp
        (stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t) 2 P := by
  have hA0 : MeasurableSet[F 0] {ω | ⊥ < τ ω} := hτ.measurableSet_gt 0
  have hMstop : Martingale (stoppedProcess M τ) F P :=
    stoppedProcess_martingale_of_null_events hM hτ hnull hrM
  refine ⟨?_, fun t => ?_⟩
  · rw [stoppedProcess_indicator_comm']
    exact martingale_indicator_of_measurable_zero hMstop hA0
  · rw [stoppedProcess_indicator_comm]
    exact ((stoppedProcess_memLp_two_and_second_moment_le
      hM hτ hrM t (h2 t)).1).indicator (F.le 0 _ hA0)

/-- The compensated square remains a true martingale after threshold stopping
with the same exact indicator applied to the martingale and compensator. -/
theorem indicator_stopped_square_compensated_martingale
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω)) :
    Martingale (fun t ω =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t ω *
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t ω -
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ t ω) F P := by
  have hCstop : Martingale
      (stoppedProcess (fun t ω => M t ω * M t ω - B t ω) τ) F P :=
    stoppedProcess_martingale_of_null_events hC hτ hnull hrC
  have hA0 : MeasurableSet[F 0] {ω | ⊥ < τ ω} := hτ.measurableSet_gt 0
  have hind : Martingale (fun t => {ω | ⊥ < τ ω}.indicator
      (stoppedProcess (fun s ω => M s ω * M s ω - B s ω) τ t)) F P :=
    martingale_indicator_of_measurable_zero hCstop hA0
  have heq : (fun t ω =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t ω *
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ t ω -
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ t ω) =
      stoppedProcess (fun t => {ω | ⊥ < τ ω}.indicator
        (fun ω => M t ω * M t ω - B t ω)) τ := by
    funext t ω
    dsimp only [stoppedProcess]
    by_cases hω : ω ∈ {ω | ⊥ < τ ω}
    · simp only [Set.indicator_of_mem hω]
    · simp only [Set.indicator_of_notMem hω, zero_mul, sub_self]
  rw [heq, stoppedProcess_indicator_comm']
  exact hind

/-- A pointwise bound on the exact stopped compensator gives the terminal
second-moment bound needed for tightness.  The initial square term is retained;
the next theorem removes it under the usual zero-start normalization. -/
theorem indicator_stoppedProcess_memLp_two_and_second_moment_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2 : ∀ t, MemLp (M t) 2 P)
    (hB0 : ∀ᵐ ω ∂P, B 0 ω = 0) (T : ℝ≥0) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P,
      |stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ T ω| ≤ K) :
    let N := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ
    MemLp (N T) 2 P ∧
      (∫ ω, (N T ω) ^ 2 ∂P) ≤
        K + ∫ ω, ({ω | ⊥ < τ ω}.indicator (M 0) ω) ^ 2 ∂P := by
  let N := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ
  let A := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ
  have hN := indicator_stoppedProcess_martingale_and_memLp_two
    hM hτ hnull hrM h2
  have hcomp := indicator_stopped_square_compensated_martingale
    hC hτ hnull hrC
  change Martingale N F P ∧ (∀ t, MemLp (N t) 2 P) at hN
  change Martingale (fun t ω => N t ω * N t ω - A t ω) F P at hcomp
  have hA0 : ∀ᵐ ω ∂P, A 0 ω = 0 := by
    filter_upwards [hB0] with ω hω
    dsimp only [A]
    rw [stoppedProcess_indicator_comm]
    by_cases hωτ : ⊥ < τ ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hωτ),
        stoppedProcess_eq_of_le
          (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from bot_le), hω]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hωτ)]
  have hmom := compensated_square_second_moment_of_zero hcomp hN.2 hA0 T
  have hAint : Integrable (A T) P := by
    refine ((hN.2 T).integrable_sq.sub (hcomp.integrable T)).congr ?_
    filter_upwards [] with ω
    change N T ω ^ 2 - (N T ω * N T ω - A T ω) = A T ω
    ring
  have hAle : (∫ ω, A T ω ∂P) ≤ K := by
    calc
      (∫ ω, A T ω ∂P) ≤ ∫ _ : Ω, K ∂P :=
        integral_mono_ae hAint (integrable_const K)
          (hbound.mono fun ω hω => (le_abs_self (A T ω)).trans hω)
      _ = K := by simp
  have hN0 : (∫ ω, (N 0 ω) ^ 2 ∂P) =
      ∫ ω, ({ω | ⊥ < τ ω}.indicator (M 0) ω) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp only [N]
    rw [stoppedProcess_eq_of_le bot_le]
  refine ⟨hN.2 T, ?_⟩
  calc
    (∫ ω, (N T ω) ^ 2 ∂P) =
        (∫ ω, A T ω ∂P) + (∫ ω, (N 0 ω) ^ 2 ∂P) := hmom
    _ ≤ K + (∫ ω, (N 0 ω) ^ 2 ∂P) := add_le_add hAle le_rfl
    _ = K + ∫ ω, ({ω | ⊥ < τ ω}.indicator (M 0) ω) ^ 2 ∂P := by rw [hN0]

/-- The exact package consumed by martingale interpolation tightness: after a
threshold stop, both martingales and all deterministic-time `L²` bounds hold,
and a stopped-bracket bound by `K` gives the same terminal second-moment bound
when the martingale and bracket start at zero. -/
theorem threshold_stopped_martingale_tightness_inputs
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2 : ∀ t, MemLp (M t) 2 P)
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hB0 : ∀ᵐ ω ∂P, B 0 ω = 0)
    (T : ℝ≥0) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P,
      |stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ T ω| ≤ K) :
    let N := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ
    let A := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ
    Martingale N F P ∧
      Martingale (fun t ω => N t ω * N t ω - A t ω) F P ∧
      (∀ t, MemLp (N t) 2 P) ∧
      (∫ ω, (N T ω) ^ 2 ∂P) ≤ K := by
  let N := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (M s)) τ
  let A := stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (B s)) τ
  have hN := indicator_stoppedProcess_martingale_and_memLp_two
    hM hτ hnull hrM h2
  have hcomp := indicator_stopped_square_compensated_martingale
    hC hτ hnull hrC
  have hmom := indicator_stoppedProcess_memLp_two_and_second_moment_le
    hM hC hτ hnull hrM hrC h2 hB0 T hK hbound
  change Martingale N F P ∧ (∀ t, MemLp (N t) 2 P) at hN
  change Martingale (fun t ω => N t ω * N t ω - A t ω) F P at hcomp
  change MemLp (N T) 2 P ∧
    (∫ ω, (N T ω) ^ 2 ∂P) ≤
      K + ∫ ω, ({ω | ⊥ < τ ω}.indicator (M 0) ω) ^ 2 ∂P at hmom
  have hinit : (∫ ω, ({ω | ⊥ < τ ω}.indicator (M 0) ω) ^ 2 ∂P) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hM0] with ω hω
    simp [hω]
  refine ⟨hN.1, hcomp, hN.2, ?_⟩
  simpa only [hinit, add_zero] using hmom.2

end ReflectedGMS.MartingaleLimit

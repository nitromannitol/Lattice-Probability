/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalMartingaleCombination at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CommonSquareLocalizer
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedAdaptedness

/-!
# Linear combinations and almost-sure modifications of the project's local martingales

`Process/MartingaleIngredients.IsLocalMartingale` and
`IsLocallySquareIntegrableMartingale` are mathlib's `Locally` predicate applied to the
martingale property, i.e. they carry an explicit localizing sequence and the exact
`{τ > ⊥}`-indicator stopping of `Probability/Process/LocalProperty`.  Two facts about
them are needed by the bracket lane and exist nowhere in the tree in this form:

* **linear combinations**: the sum of two local martingales, and a scalar multiple of
  one, are local martingales, with the pointwise minimum of the two localizing
  sequences as the common localizer;
* **almost-sure modifications**: on a filtration containing every null event of the
  law, a process which agrees with a local martingale on one full-probability event,
  simultaneously at all times, is a local martingale with the *same* localizing
  sequence.

The first fact is not free in continuous time: stopping a martingale at a further
stopping time is a martingale only under path regularity, so almost-sure right
continuity is assumed throughout, exactly as in
`Limit/StoppedAdaptedness.stoppedProcess_martingale_of_null_events`.  The key
pathwise identity `indicator_stoppedProcess_min_eq` — localizing at `min σ τ` is the
same exact process as localizing at `σ`, then multiplying by the time-zero indicator
of `{τ > ⊥}` and stopping at `τ` — is the one used inside
`Limit/CommonSquareLocalizer.exists_common_square_localizer`, where it is private;
it is restated here publicly.

Nothing in this file mentions the reflected walk; it is pure martingale plumbing.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.LocalMartingaleCombination

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## The pathwise identity behind the minimum localizer -/

/-- **Localizing at the minimum of two stopping times, pathwise.**  The exact localized
process at `min σ τ` is the localized process at `σ`, then stopped at `τ` and multiplied
by the indicator of `{τ > ⊥}`. -/
theorem indicator_stoppedProcess_min_eq
    (M : ℝ≥0 → Ω → ℝ) (σ τ : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun t => {ω | ⊥ < min (σ ω) (τ ω)}.indicator (M t))
        (fun ω => min (σ ω) (τ ω)) =
      fun t => {ω | ⊥ < τ ω}.indicator
        (stoppedProcess
          (stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ) τ t) := by
  funext t ω
  rw [stoppedProcess_stoppedProcess', stoppedProcess_indicator_comm,
    stoppedProcess_indicator_comm]
  have hmin : (fun ω => min (τ ω) (σ ω)) = fun ω => min (σ ω) (τ ω) :=
    funext fun ω => min_comm _ _
  rw [hmin]
  simp only [Set.indicator, Set.mem_setOf_eq, lt_min_iff]
  split_ifs <;> simp_all

/-! ## Stopping a localized martingale at a further stopping time -/

/-- **A localized martingale, localized further at the minimum with another stopping
time, is still a martingale.**  Right continuity of the paths is needed for the second
stopping, and the filtration must contain the null events. -/
theorem martingale_indicator_stoppedProcess_of_eq_min
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    {ρ σ τ : Ω → WithTop ℝ≥0} (hρ : ∀ ω, ρ ω = min (σ ω) (τ ω))
    (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hM : Martingale (stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ) F P) :
    Martingale (stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (M t)) ρ) F P := by
  have hρ' : ρ = fun ω => min (σ ω) (τ ω) := funext hρ
  subst hρ'
  rw [indicator_stoppedProcess_min_eq]
  have hrN : ∀ᵐ ω ∂P, IsRightContinuous
      (fun t => stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ t ω) := by
    filter_upwards [hr] with ω hω
    have heq : (fun t => stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ t ω) =
        fun t => {ω | ⊥ < σ ω}.indicator (stoppedProcess M σ t) ω := by
      funext t
      rw [stoppedProcess_indicator_comm]
    rw [heq]
    by_cases hωσ : ω ∈ {ω | ⊥ < σ ω}
    · simp only [Set.indicator_of_mem hωσ]
      exact MartingaleLimit.isRightContinuous_stoppedProcess_common ω hω σ
    · simp only [Set.indicator_of_notMem hωσ]
      exact continuous_const.isRightContinuous
  exact MartingaleLimit.martingale_indicator_of_measurable_zero
    (MartingaleLimit.stoppedProcess_martingale_of_null_events hM hτ hnull hrN)
    (hτ.measurableSet_gt 0)

/-- The square-integrability companion of the previous statement: the further stopping
keeps every fixed-time value in `L²`. -/
theorem memLp_two_indicator_stoppedProcess_of_eq_min
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    {ρ σ τ : Ω → WithTop ℝ≥0} (hρ : ∀ ω, ρ ω = min (σ ω) (τ ω))
    (hτ : IsStoppingTime F τ)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hM : Martingale (stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ) F P)
    (hM2 : ∀ t, MemLp (stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ t) 2 P) :
    ∀ t, MemLp (stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (M t)) ρ t) 2 P := by
  have hρ' : ρ = fun ω => min (σ ω) (τ ω) := funext hρ
  subst hρ'
  intro t
  rw [indicator_stoppedProcess_min_eq]
  have hrN : ∀ᵐ ω ∂P, IsRightContinuous
      (fun t => stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ t ω) := by
    filter_upwards [hr] with ω hω
    have heq : (fun t => stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (M t)) σ t ω) =
        fun t => {ω | ⊥ < σ ω}.indicator (stoppedProcess M σ t) ω := by
      funext t
      rw [stoppedProcess_indicator_comm]
    rw [heq]
    by_cases hωσ : ω ∈ {ω | ⊥ < σ ω}
    · simp only [Set.indicator_of_mem hωσ]
      exact MartingaleLimit.isRightContinuous_stoppedProcess_common ω hω σ
    · simp only [Set.indicator_of_notMem hωσ]
      exact continuous_const.isRightContinuous
  exact (MartingaleLimit.stoppedProcess_memLp_two_and_second_moment_le hM hτ hrN t
    (hM2 t)).1.indicator (F.le 0 _ (hτ.measurableSet_gt 0))

/-! ## Linear combinations -/

/-- The exact localization of a pointwise sum is the sum of the exact localizations. -/
theorem stoppedProcess_indicator_add
    (M N : ℝ≥0 → Ω → ℝ) (ρ : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (fun ω => M t ω + N t ω)) ρ =
      stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (M t)) ρ +
        stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (N t)) ρ := by
  funext t ω
  simp only [stoppedProcess, Pi.add_apply, Set.indicator, Set.mem_setOf_eq]
  split_ifs <;> simp

/-- The exact localization of a scalar multiple is the scalar multiple of the exact
localization. -/
theorem stoppedProcess_indicator_const_mul
    (c : ℝ) (M : ℝ≥0 → Ω → ℝ) (ρ : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (fun ω => c * M t ω)) ρ =
      c • stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (M t)) ρ := by
  funext t ω
  simp only [stoppedProcess, Pi.smul_apply, smul_eq_mul, Set.indicator, Set.mem_setOf_eq]
  split_ifs <;> simp

/-- **The sum of two local martingales is a local martingale**, localized by the
pointwise minimum of the two localizing sequences. -/
theorem isLocalMartingale_add
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {M N : ℝ≥0 → Ω → ℝ}
    (hM : MartingaleIngredients.IsLocalMartingale P F M)
    (hN : MartingaleIngredients.IsLocalMartingale P F N)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrN : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω)) :
    MartingaleIngredients.IsLocalMartingale P F (fun t ω => M t ω + N t ω) := by
  refine ⟨fun t => (hM.1 t).add (hN.1 t), ?_⟩
  let σ := hM.2.localSeq
  let τ := hN.2.localSeq
  refine ⟨fun n ω => min (σ n ω) (τ n ω), ?_, fun n => ?_⟩
  · exact hM.2.isLocalizingSequence_localSeq.min hN.2.isLocalizingSequence_localSeq
  · beta_reduce
    rw [stoppedProcess_indicator_add]
    refine Martingale.add ?_ ?_
    · exact martingale_indicator_stoppedProcess_of_eq_min (fun ω => rfl)
        (hN.2.isLocalizingSequence_localSeq.isStoppingTime n) hnull hrM
        (hM.2.stoppedProcess_localSeq n)
    · exact martingale_indicator_stoppedProcess_of_eq_min (fun ω => min_comm _ _)
        (hM.2.isLocalizingSequence_localSeq.isStoppingTime n) hnull hrN
        (hN.2.stoppedProcess_localSeq n)

/-- **A scalar multiple of a local martingale is a local martingale**, with the same
localizing sequence. -/
theorem isLocalMartingale_const_mul
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : MartingaleIngredients.IsLocalMartingale P F M) (c : ℝ) :
    MartingaleIngredients.IsLocalMartingale P F (fun t ω => c * M t ω) := by
  refine ⟨fun t => (hM.1 t).const_mul c, ?_⟩
  refine ⟨hM.2.localSeq, hM.2.isLocalizingSequence_localSeq, fun n => ?_⟩
  beta_reduce
  rw [stoppedProcess_indicator_const_mul]
  exact (hM.2.stoppedProcess_localSeq n).smul c

/-- Differences of local martingales, as a corollary. -/
theorem isLocalMartingale_sub
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {M N : ℝ≥0 → Ω → ℝ}
    (hM : MartingaleIngredients.IsLocalMartingale P F M)
    (hN : MartingaleIngredients.IsLocalMartingale P F N)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrN : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω)) :
    MartingaleIngredients.IsLocalMartingale P F (fun t ω => M t ω - N t ω) := by
  have hrN' : ∀ᵐ ω ∂P, IsRightContinuous (fun t => -1 * N t ω) := by
    filter_upwards [hrN] with ω hω
    have h := hω.const_smul (-1 : ℝ)
    first
      | exact h
      | (convert h using 1; funext t; simp)
  have h := isLocalMartingale_add hM (isLocalMartingale_const_mul hN (-1)) hnull hrM hrN'
  have heq : (fun t ω => M t ω - N t ω) = fun t ω => M t ω + -1 * N t ω := by
    funext t ω; ring
  rw [heq]
  exact h

/-- **The sum of two locally square-integrable martingales is one**, localized by the
pointwise minimum of the two localizing sequences. -/
theorem isLocallySquareIntegrableMartingale_add
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m} {M N : ℝ≥0 → Ω → ℝ}
    (hM : MartingaleIngredients.IsLocallySquareIntegrableMartingale P F M)
    (hN : MartingaleIngredients.IsLocallySquareIntegrableMartingale P F N)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrN : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω)) :
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P F
      (fun t ω => M t ω + N t ω) := by
  refine ⟨fun t => (hM.1 t).add (hN.1 t), ?_⟩
  let σ := hM.2.localSeq
  let τ := hN.2.localSeq
  refine ⟨fun n ω => min (σ n ω) (τ n ω), ?_, fun n => ?_⟩
  · exact hM.2.isLocalizingSequence_localSeq.min hN.2.isLocalizingSequence_localSeq
  · beta_reduce
    rw [stoppedProcess_indicator_add]
    have h1 := martingale_indicator_stoppedProcess_of_eq_min
      (ρ := fun ω => min (σ n ω) (τ n ω)) (fun ω => rfl)
      (hN.2.isLocalizingSequence_localSeq.isStoppingTime n) hnull hrM
      (hM.2.stoppedProcess_localSeq n).1
    have h2 := martingale_indicator_stoppedProcess_of_eq_min
      (ρ := fun ω => min (σ n ω) (τ n ω)) (fun ω => min_comm _ _)
      (hM.2.isLocalizingSequence_localSeq.isStoppingTime n) hnull hrN
      (hN.2.stoppedProcess_localSeq n).1
    have h1' := memLp_two_indicator_stoppedProcess_of_eq_min
      (ρ := fun ω => min (σ n ω) (τ n ω)) (fun ω => rfl)
      (hN.2.isLocalizingSequence_localSeq.isStoppingTime n) hrM
      (hM.2.stoppedProcess_localSeq n).1 (hM.2.stoppedProcess_localSeq n).2
    have h2' := memLp_two_indicator_stoppedProcess_of_eq_min
      (ρ := fun ω => min (σ n ω) (τ n ω)) (fun ω => min_comm _ _)
      (hM.2.isLocalizingSequence_localSeq.isStoppingTime n) hrN
      (hN.2.stoppedProcess_localSeq n).1 (hN.2.stoppedProcess_localSeq n).2
    exact ⟨h1.add h2, fun t => (h1' t).add (h2' t)⟩

/-- A scalar multiple of a locally square-integrable martingale is one, with the same
localizing sequence. -/
theorem isLocallySquareIntegrableMartingale_const_mul
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : MartingaleIngredients.IsLocallySquareIntegrableMartingale P F M) (c : ℝ) :
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P F
      (fun t ω => c * M t ω) := by
  refine ⟨fun t => (hM.1 t).const_mul c, ?_⟩
  refine ⟨hM.2.localSeq, hM.2.isLocalizingSequence_localSeq, fun n => ?_⟩
  beta_reduce
  rw [stoppedProcess_indicator_const_mul]
  exact ⟨(hM.2.stoppedProcess_localSeq n).1.smul c,
    fun t => ((hM.2.stoppedProcess_localSeq n).2 t).const_smul c⟩

/-! ## Almost-sure modifications on a filtration containing the null events -/

/-- An almost-sure modification of a strongly measurable function is strongly
measurable for any sub-σ-algebra containing every null event. -/
theorem stronglyMeasurable_of_ae_eq_of_null_events
    {P : Measure Ω} {m' : MeasurableSpace Ω} (hm' : m' ≤ m)
    (hnull : ∀ A : Set Ω, P A = 0 → MeasurableSet[m'] A)
    {f g : Ω → ℝ} (hf : StronglyMeasurable[m'] f) (hfg : f =ᵐ[P] g) :
    StronglyMeasurable[m'] g :=
  MartingaleLimit.stronglyMeasurable_limit_of_null_events hm' hnull
    (f := fun _ => f) (fun _ => hf)
    (hfg.mono fun ω hω => by rw [hω]; exact tendsto_const_nhds)

/-- **A process agreeing with a local martingale on one full-probability event at all
times is a local martingale**, with the same localizing sequence, provided the
filtration contains every null event.  No path regularity is needed. -/
theorem isLocalMartingale_of_ae_eq
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {M N : ℝ≥0 → Ω → ℝ}
    (hM : MartingaleIngredients.IsLocalMartingale P F M)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hMN : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = N t ω) :
    MartingaleIngredients.IsLocalMartingale P F N := by
  have hadapt : StronglyAdapted F N := fun t =>
    stronglyMeasurable_of_ae_eq_of_null_events (F.le t) (hnull t) (hM.1 t)
      (hMN.mono fun ω hω => hω t)
  refine ⟨hadapt, ⟨hM.2.localSeq, hM.2.isLocalizingSequence_localSeq, fun n => ?_⟩⟩
  have hstop : ∀ t,
      stoppedProcess (fun t => {ω | ⊥ < hM.2.localSeq n ω}.indicator (M t))
          (hM.2.localSeq n) t =ᵐ[P]
        stoppedProcess (fun t => {ω | ⊥ < hM.2.localSeq n ω}.indicator (N t))
          (hM.2.localSeq n) t := by
    intro t
    filter_upwards [hMN] with ω hω
    simp only [stoppedProcess]
    simp [Set.indicator, hω]
  refine (hM.2.stoppedProcess_localSeq n).congr (fun t => ?_) hstop
  exact stronglyMeasurable_of_ae_eq_of_null_events (F.le t) (hnull t)
    ((hM.2.stoppedProcess_localSeq n).stronglyAdapted t) (hstop t)

end ReflectedGMS.LocalMartingaleCombination

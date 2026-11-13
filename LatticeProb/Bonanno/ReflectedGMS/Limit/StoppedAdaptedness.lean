/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppedAdaptedness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedMartingale
import LatticeProb.Bonanno.ReflectedGMS.Process.NaturalFiltration

/-!
Exact adaptedness of actual stopped processes on a filtration containing all
null events of the ambient law. The existing progressive stopping theorem needs
everywhere continuous paths; here finite-grid stopped values and their checked
right limits suffice. Completion removes only the measurability obstruction on
the exceptional null set, without changing the process.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A bounded finite-valued stopping time has an exactly measurable stopped
value at the deterministic upper horizon. -/
theorem stronglyMeasurable_stoppedValue_of_finite_range
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted F M) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfin : (Set.range τ).Finite)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    StronglyMeasurable[F T] (stoppedValue M τ) := by
  classical
  let s := (hfin.image WithTop.untopA).toFinset
  have hne (ω : Ω) : τ ω ≠ ⊤ :=
    (lt_of_le_of_lt (hτT ω) (WithTop.coe_lt_top T)).ne
  have hmem : ∀ ω, τ ω ∈ WithTop.some '' (s : Set ℝ≥0) := by
    intro ω
    refine ⟨(τ ω).untopA, ?_, ?_⟩
    · exact (hfin.image WithTop.untopA).mem_toFinset.mpr ⟨τ ω, ⟨ω, rfl⟩, rfl⟩
    · rw [WithTop.untopA_eq_untop (hne ω), WithTop.coe_untop]
  rw [stoppedValue_eq_of_mem_finset hmem]
  apply Finset.stronglyMeasurable_sum
  intro i hi
  have hiT : i ≤ T := by
    obtain ⟨_, ⟨ω, rfl⟩, rfl⟩ := (hfin.image WithTop.untopA).mem_toFinset.mp hi
    exact (WithTop.untopA_le_iff (hne ω)).mpr (hτT ω)
  exact ((hM i).mono (F.mono hiT)).indicator
    (F.mono hiT _ (hτ.measurableSet_eq_of_countable_range hfin.countable i))

/-- An almost-sure limit is exactly measurable in a smaller sigma algebra
when that sigma algebra already contains every null event of the ambient law. -/
theorem stronglyMeasurable_limit_of_null_events
    {P : Measure Ω} {m' : MeasurableSpace Ω} (hm' : m' ≤ m)
    (hnull : ∀ A : Set Ω, P A = 0 → MeasurableSet[m'] A)
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, StronglyMeasurable[m'] (f n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    StronglyMeasurable[m'] g := by
  let : MeasurableSpace Ω := m'
  let : (P.trim hm').IsComplete :=
    ⟨fun A hA => hnull A (measure_eq_zero_of_trim_eq_zero hm' hA)⟩
  have hlim' : ∀ᵐ ω ∂P.trim hm', Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    rw [ae_iff] at hlim ⊢
    rwa [trim_measurableSet_eq hm' (hnull _ hlim)]
  have hg := aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hf n).aestronglyMeasurable (μ := P.trim hm')) hlim'
  exact hg.aemeasurable.nullMeasurable.measurable_of_complete.stronglyMeasurable

/-- Bounded stopping preserves exact horizon measurability under almost-sure
right continuity, provided the horizon sigma algebra contains all null events.
The actual stopped value is used, including a stopping time equal to zero. -/
theorem stronglyMeasurable_stoppedValue_of_ae_rightContinuous
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted F M) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hnull : ∀ A : Set Ω, P A = 0 → MeasurableSet[F T] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) :
    StronglyMeasurable[F T] (stoppedValue M τ) := by
  apply stronglyMeasurable_limit_of_null_events (P := P) (F.le T) hnull
    (f := fun n => stoppedValue M (boundedGridApprox τ T n))
  · intro n
    exact stronglyMeasurable_stoppedValue_of_finite_range hM
      (isStoppingTime_boundedGridApprox hτ T hτT n)
      (finite_range_boundedGridApprox T hτT n) T
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2)
  · exact hr.mono fun ω hω => boundedGridApprox_stoppedValue_tendsto M T hτT ω hω

/-- Exact adaptedness of the actual stopped process. The original stopping
time is arbitrary and may equal infinity; only its value capped at each
deterministic observation horizon is approximated. -/
theorem stronglyAdapted_stoppedProcess_of_ae_rightContinuous
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted F M) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) :
    StronglyAdapted F (stoppedProcess M τ) := by
  intro t
  exact stronglyMeasurable_stoppedValue_of_ae_rightContinuous hM
    ((isStoppingTime_const F t).min hτ) t (fun _ => min_le_left _ _) (hnull t) hr

/-- Completion discharges the exact-adaptedness condition in the existing
stopped martingale theorem. -/
theorem stoppedProcess_martingale_of_null_events
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) :
    Martingale (stoppedProcess M τ) F P :=
  stoppedProcess_martingale_of_stronglyAdapted hM hτ hr
    (stronglyAdapted_stoppedProcess_of_ae_rightContinuous hM.stronglyAdapted hτ hnull hr)

end ReflectedGMS.MartingaleLimit

namespace ReflectedGMS.ProcessFiltration

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The existing completed natural filtration contains its actual null-event
sigma algebra at every time, also after right continuation. -/
theorem nullEventSigma_le_completedNaturalFiltration
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ) (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    nullEventSigma P ≤ completedNaturalFiltration P X hX t := by
  unfold completedNaturalFiltration
  dsimp only
  refine le_trans ?_ (Filtration.le_rightCont _ t)
  exact le_sup_right

/-- Every null event of the completed law is measurable at every time of the
project's completed natural filtration. -/
theorem measurableSet_completedNaturalFiltration_of_null
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ) (hX : ∀ t, Measurable (X t))
    (t : ℝ≥0) (A : Set (NullMeasurableSpace Ω P)) (hA : P.completion A = 0) :
    MeasurableSet[completedNaturalFiltration P X hX t] A :=
  nullEventSigma_le_completedNaturalFiltration P X hX t A
    (MeasurableSpace.GenerateMeasurable.basic A hA)

/-- Actual stopped processes are exactly strongly adapted to the project's
completed natural filtration under the original a.e. path assumption. -/
theorem stronglyAdapted_stoppedProcess_completedNaturalFiltration
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℕ) (hX : ∀ t, Measurable (X t))
    {M : ℝ≥0 → NullMeasurableSpace Ω P → ℝ}
    (hM : StronglyAdapted (completedNaturalFiltration P X hX) M)
    {τ : NullMeasurableSpace Ω P → WithTop ℝ≥0}
    (hτ : IsStoppingTime (completedNaturalFiltration P X hX) τ)
    (hr : ∀ᵐ ω ∂P.completion, IsRightContinuous (fun t => M t ω)) :
    StronglyAdapted (completedNaturalFiltration P X hX) (stoppedProcess M τ) :=
  MartingaleLimit.stronglyAdapted_stoppedProcess_of_ae_rightContinuous hM hτ
    (measurableSet_completedNaturalFiltration_of_null P X hX) hr

/-- The stopped process is a true martingale for the existing completed
natural filtration and completed finite law, with no residual adaptedness or
completion assumption and no bound on the stopping time. -/
theorem stoppedProcess_martingale_completedNaturalFiltration
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℝ≥0 → Ω → ℕ) (hX : ∀ t, Measurable (X t))
    {M : ℝ≥0 → NullMeasurableSpace Ω P → ℝ}
    (hM : Martingale M (completedNaturalFiltration P X hX) P.completion)
    {τ : NullMeasurableSpace Ω P → WithTop ℝ≥0}
    (hτ : IsStoppingTime (completedNaturalFiltration P X hX) τ)
    (hr : ∀ᵐ ω ∂P.completion, IsRightContinuous (fun t => M t ω)) :
    Martingale (stoppedProcess M τ) (completedNaturalFiltration P X hX) P.completion := by
  let : IsFiniteMeasure P.completion := ⟨measure_lt_top P Set.univ⟩
  exact MartingaleLimit.stoppedProcess_martingale_of_null_events hM hτ
    (measurableSet_completedNaturalFiltration_of_null P X hX) hr

end ReflectedGMS.ProcessFiltration

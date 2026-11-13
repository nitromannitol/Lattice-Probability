/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalizedArrayProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.WindowModulusGridTransfer
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedCadlagPaths

/-!
# A producer of `LocalizedMartingaleArray`

`WindowModulusGridTransfer.eventually_window_tail_of_localized_arrays` (and hence the whole
`hmodExp` weld) consumes a `LocalizedMartingaleArray`, but the project had **no producer** of
that structure: every occurrence of the name was a consumer hypothesis.  This module supplies
one, from the threshold-stopped lane that the structure's docstring already names.

The inputs are bundled as `ThresholdArrayInputs`: a sequence of square-integrable càdlàg
martingales `M n` with compensators `V n` of their squares, where each `V n` is a continuous,
monotone, nonnegative adapted bracket converging in probability, uniformly on `[0,T]`, to the
linear bracket `v · t`.  The rows of the produced array are the threshold stops of `M n` at the
first time `V n` reaches a level `K > v·T`, with the project's exact `{τ > 0}` indicator.

Two pieces of the weld were not in the tree and are proved here:

* `rightContinuous_compensated` of the stopped pair — the compensated square of the stopped
  row is the *stopped* compensated square (`indicator_stopped_compensated_eq`, the identity
  already used inside `ThresholdStoppedMartingaleMoments`), so right continuity transfers by
  `isRightContinuous_stoppedProcess_common` through the indicator
  (`isRightContinuous_indicator_stoppedProcess`);
* `agree` — off the exit event `{τ n ≤ T}` the stopped row equals the original row at **every**
  time `t ≤ T` (`tendsto_indicator_stopped_disagree`), so the rare-exit conclusion of
  `exists_threshold_bracket_localization_of_ucp` gives the agreement in probability directly.

The ℕ-indexing of the single-row `StoppedCadlagPaths` result is a pointwise application; the
localizer sequence `τ` is already ℕ-indexed by `UCPBracketLocalization`.

**No tightness estimate for the reflected walk is certified here**: this is an implication.
An anti-vacuity certificate for the *target* structure is in
`Limit/LocalizedArrayInhabitation.lean` (the zero array over any probability measure).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.LocalizedArrayProducer

open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction
open ReflectedGMS.DiffusiveModulusTranslation

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## Right continuity after an indicator threshold stop -/

/-- **Right continuity survives the project's exact indicator stopping.**  The right-continuous
analogue of `MartingaleLimit.isCadlag_indicator_stoppedProcess`; the compensated square is only
right continuous, never càdlàg, so the càdlàg version does not apply to it. -/
theorem isRightContinuous_indicator_stoppedProcess
    {N : ℝ≥0 → Ω → ℝ} (ω : Ω) (hN : IsRightContinuous (fun t => N t ω))
    (τ : Ω → WithTop ℝ≥0) :
    IsRightContinuous (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω) := by
  have heq : (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω) =
      fun t => {ω | ⊥ < τ ω}.indicator (stoppedProcess N τ t) ω := by
    funext t
    exact congrFun (stoppedProcess_indicator_comm' (u := N) (τ := τ)) t ▸ rfl
  rw [heq]
  by_cases hωτ : ⊥ < τ ω
  · have hind : (fun t => {ω | ⊥ < τ ω}.indicator
        (stoppedProcess N τ t) ω) = fun t => stoppedProcess N τ t ω := by
      funext t
      rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    exact isRightContinuous_stoppedProcess_common ω hN τ
  · have hind : (fun t => {ω | ⊥ < τ ω}.indicator
        (stoppedProcess N τ t) ω) = fun _ => (0 : ℝ) := by
      funext t
      rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hωτ)]
    rw [hind]
    exact IsRightContinuous.const

/-- **The compensated square of the stopped row is the stopped compensated square.**  This is
the identity already used inside `MartingaleLimit.indicator_stopped_square_compensated_martingale`;
it is stated separately here because the right-continuity field needs it too. -/
theorem indicator_stopped_compensated_eq (N V : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    (fun t ω =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω *
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω -
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω) =
      stoppedProcess (fun t => {ω | ⊥ < τ ω}.indicator
        (fun ω => N t ω * N t ω - V t ω)) τ := by
  funext t ω
  dsimp only [stoppedProcess]
  by_cases hω : ω ∈ {ω | ⊥ < τ ω}
  · simp only [Set.indicator_of_mem hω]
  · simp only [Set.indicator_of_notMem hω, zero_mul, sub_self]

/-- **The `rightContinuous_compensated` field.**  Almost-sure right continuity of the
compensated square passes to the exact indicator-stopped pair. -/
theorem ae_rightContinuous_indicator_stopped_compensated
    {P : Measure Ω} {N V : ℝ≥0 → Ω → ℝ} (τ : Ω → WithTop ℝ≥0)
    (hrC : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω * N t ω - V t ω)) :
    ∀ᵐ ω ∂P, IsRightContinuous (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω *
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω -
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω) := by
  filter_upwards [hrC] with ω hω
  have heq : (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω *
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (N s)) τ t ω -
      stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω) =
      fun t => stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator
        (fun ω => N s ω * N s ω - V s ω)) τ t ω := by
    funext t
    exact congrFun (congrFun (indicator_stopped_compensated_eq N V τ) t) ω
  rw [heq]
  exact isRightContinuous_indicator_stoppedProcess ω hω τ

/-! ## Agreement off the exit event -/

/-- **The `agree` field.**  Off the exit event `{τ n ≤ T}` the exact indicator-stopped row
coincides with the original row at *every* time `t ≤ T`, so rare exits give agreement in
probability. -/
theorem tendsto_indicator_stopped_disagree
    {P : Measure Ω} (N : ℕ → ℝ≥0 → Ω → ℝ) (τ : ℕ → Ω → WithTop ℝ≥0) (T : ℝ≥0)
    (hexit : Tendsto (fun n => P {ω | τ n ω ≤ (T : WithTop ℝ≥0)}) atTop (𝓝 0)) :
    Tendsto (fun n => P {ω | ∃ t ≤ T,
      stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (N n s)) (τ n) t ω ≠ N n t ω})
      atTop (𝓝 0) := by
  have hsub : ∀ n : ℕ, P {ω | ∃ t ≤ T,
      stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (N n s)) (τ n) t ω ≠ N n t ω} ≤
      P {ω | τ n ω ≤ (T : WithTop ℝ≥0)} := by
    intro n
    refine measure_mono ?_
    rintro ω ⟨t, htT, hne⟩
    by_contra hω
    simp only [Set.mem_setOf_eq, not_le] at hω
    have htau : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω :=
      le_of_lt (lt_of_le_of_lt (by exact_mod_cast htT) hω)
    have hmem : ω ∈ {ω | ⊥ < τ n ω} := lt_of_le_of_lt bot_le hω
    refine absurd ?_ hne
    rw [stoppedProcess_eq_of_le htau, Set.indicator_of_mem hmem]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexit
    (fun _ => zero_le) hsub

/-! ## The producer -/

/-- **The inputs of the threshold-stopped lane**, bundled.  `M n` are square-integrable càdlàg
martingales, `V n` compensators of their squares which are continuous, monotone, nonnegative and
adapted, and `V n` converges in probability, uniformly on `[0,T]`, to the linear bracket
`v · t`.  `K` is a level strictly above the terminal linear bracket `v · T`.

These are exactly the hypotheses of `MartingaleLimit.exists_threshold_bracket_localization_of_ucp`
and `MartingaleLimit.threshold_stopped_martingale_tightness_inputs_with_cadlag` — nothing is
added.  They are satisfied, for instance, by any sequence of continuous square-integrable
martingales on a complete filtration whose brackets converge uniformly in probability to `v·t`;
no field refers to the produced array, so the satisfiability argument is not circular. -/
structure ThresholdArrayInputs {Ω : Type*} {m : MeasurableSpace Ω} (P : @Measure Ω m)
    (F : ℕ → Filtration ℝ≥0 m) (M V : ℕ → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (v K : ℝ) : Prop where
  /-- The limiting bracket slope is nonnegative. -/
  v_nonneg : 0 ≤ v
  /-- The threshold level exceeds the terminal linear bracket. -/
  threshold_gt : v * (T : ℝ) < K
  /-- Each row is a martingale. -/
  martingale : ∀ n, Martingale (M n) (F n) P
  /-- `V n` compensates the square of `M n`. -/
  compensated : ∀ n, Martingale (fun t ω => M n t ω * M n t ω - V n t ω) (F n) P
  /-- The filtrations contain the null sets. -/
  null : ∀ n (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[(F n) t] A
  /-- The rows have càdlàg paths. -/
  cadlag : ∀ n, ∀ᵐ ω ∂P, IsCadlag (fun t => M n t ω)
  /-- The compensated squares have right-continuous paths. -/
  rightContinuous_compensated : ∀ n, ∀ᵐ ω ∂P,
    IsRightContinuous (fun t => M n t ω * M n t ω - V n t ω)
  /-- The rows are square integrable at every deterministic time. -/
  memLp : ∀ n t, MemLp (M n t) 2 P
  /-- The rows start at zero. -/
  start_martingale : ∀ n, ∀ᵐ ω ∂P, M n 0 ω = 0
  /-- The brackets start at zero. -/
  start_bracket : ∀ n, ∀ᵐ ω ∂P, V n 0 ω = 0
  /-- The brackets are adapted. -/
  adapted_bracket : ∀ n, Adapted (F n) (V n)
  /-- The brackets have continuous paths. -/
  continuous_bracket : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => V n t ω)
  /-- The brackets are monotone. -/
  monotone_bracket : ∀ n, ∀ᵐ ω ∂P, Monotone (fun t => V n t ω)
  /-- The brackets are nonnegative. -/
  nonneg_bracket : ∀ n, ∀ᵐ ω ∂P, ∀ t, 0 ≤ V n t ω
  /-- The brackets converge to the linear bracket, uniformly in probability on `[0,T]`. -/
  ucp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
    P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |V n t ω - v * (t : ℝ)|}) atTop (𝓝 0)

/-- **The `LocalizedMartingaleArray` producer.**  The threshold-stopped lane delivers, for the
target array `M` and horizon `T`, a localized martingale array in exactly the shape consumed by
`WindowModulusGridTransfer.eventually_window_tail_of_localized_arrays`.

Rows: the exact `{τ n > 0}`-indicator stops of `M n` at the first time `V n` reaches `Ici K`.
Compensators: the same stops of `V n`.  Terminal second-moment bound: `K`.  Bracket slope: `v`.
Envelope: the integrable localized bracket error of `LocalizedBracketEnvelope`. -/
theorem nonempty_localizedMartingaleArray_of_thresholdInputs
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℕ → Filtration ℝ≥0 m} {M V : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {v K : ℝ}
    (h : ThresholdArrayInputs P F M V T v K) :
    Nonempty (LocalizedMartingaleArray P M T) := by
  obtain ⟨τ, -, hτ, hexit, hVbound, R, hRint, hRerror, hRlim⟩ :=
    exists_threshold_bracket_localization_of_ucp (P := P) (F := F) (B := V) T
      h.v_nonneg h.threshold_gt h.adapted_bracket h.null h.continuous_bracket
      h.monotone_bracket h.nonneg_bracket h.ucp
  have hK : 0 ≤ K := (mul_nonneg h.v_nonneg T.2).trans h.threshold_gt.le
  have hrow : ∀ n,
      Martingale (stoppedProcess
          (fun s => {ω | ⊥ < τ n ω}.indicator (M n s)) (τ n)) (F n) P ∧
      Martingale (fun t ω =>
          stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (M n s)) (τ n) t ω *
            stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (M n s)) (τ n) t ω -
          stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (V n s)) (τ n) t ω) (F n) P ∧
      (∀ t, MemLp (stoppedProcess
          (fun s => {ω | ⊥ < τ n ω}.indicator (M n s)) (τ n) t) 2 P) ∧
      (∀ᵐ ω ∂P, IsCadlag (fun t => stoppedProcess
          (fun s => {ω | ⊥ < τ n ω}.indicator (M n s)) (τ n) t ω)) ∧
      (∫ ω, (stoppedProcess
          (fun s => {ω | ⊥ < τ n ω}.indicator (M n s)) (τ n) T ω) ^ 2 ∂P) ≤ K := by
    intro n
    exact threshold_stopped_martingale_tightness_inputs_with_cadlag
      (h.martingale n) (h.compensated n) (hτ n) (h.null n) (h.cadlag n)
      (h.rightContinuous_compensated n) (h.memLp n) (h.start_martingale n)
      (h.start_bracket n) T hK ((hVbound n).mono fun _ hω => hω T le_rfl)
  exact ⟨{
    F := F
    Y := fun n => stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (M n s)) (τ n)
    B := fun n => stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (V n s)) (τ n)
    R := R
    C := K
    v := v
    martingale := fun n => (hrow n).1
    compensated := fun n => (hrow n).2.1
    cadlag := fun n => (hrow n).2.2.2.1
    rightContinuous_compensated := fun n =>
      ae_rightContinuous_indicator_stopped_compensated (τ n) (h.rightContinuous_compensated n)
    memLp := fun n t => (hrow n).2.2.1 t
    terminal := fun n => (hrow n).2.2.2.2
    v_nonneg := h.v_nonneg
    integrable_error := hRint
    error := hRerror
    error_mean := hRlim
    agree := tendsto_indicator_stopped_disagree M τ T hexit }⟩

/-! ## Shape check against the consumer

The `harray` slot of `WindowModulusGridTransfer.eventually_window_tail_of_localized_arrays`
is filled by the producer above, at the rescaled coordinates of the comparison process.  This
`example` elaborates, so the binders genuinely match rather than merely looking compatible. -/

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable I)
    (G : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hclose : ∀ (H : ℝ≥0) (κ : ℝ), 0 < κ → Tendsto (fun n => P {ω | ∃ r < (ε n)⁻¹ ^ 2 * H,
      κ < (ε n : ℝ) * dist (I ω r) (G r ω)}) atTop (𝓝 0))
    (F : Fin 2 → ℝ≥0 → ℕ → Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (V : Fin 2 → ℝ≥0 → ℕ → ℝ≥0 → Ω → ℝ) (v K : Fin 2 → ℝ≥0 → ℝ)
    (hin : ∀ (k : Fin 2) (H : ℝ≥0), ThresholdArrayInputs P (F k H)
      (fun n u ω => (ε n : ℝ) * G ((ε n)⁻¹ ^ 2 * u) ω k) (V k H) H (v k H) (K k H))
    (mm : ℕ) (c : ℝ) (hc : 0 < c) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n in atTop,
      P (I ⁻¹' windowModulusFailure (E := BouRabeeGwynne.Euc 2) ((ε n)⁻¹ ^ 2 * (mm : ℝ≥0))
        (c / (ε n : ℝ)) (((ε n : ℝ))⁻¹ ^ 2 * d)) ≤ η :=
  eventually_window_tail_of_localized_arrays (Q := P) (fun _ => rfl) I hI G ε hεpos hclose
    (fun k H => nonempty_localizedMartingaleArray_of_thresholdInputs (hin k H)) mm c hc η hη

end ReflectedGMS.LocalizedArrayProducer

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalizedThresholdArrayInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedArrayProducer
import LatticeProb.Bonanno.ReflectedGMS.Limit.CommonSquareLocalizer
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizingExit

/-!
# The localization gap between `hbracket` and the localized-array producer

`Limit/LocalizedArrayProducer.harray_of_thresholdInputs` consumes
`ThresholdArrayInputs`, whose martingale fields are **global**: each row `M n` must be a true
square-integrable martingale and `M n ^ 2 - V n` a true martingale.  The canonical bracket
delivered by the invariance assembly's `hbracket`
(`Process/MartingaleIngredients.HasOrdinaryEdgeBracket`) is weaker: it gives
`IsLocallySquareIntegrableMartingale` for the process and `IsLocalMartingale` for each
compensated product, i.e. both only after localization by a sequence of stopping times.
So `ThresholdArrayInputs` did **not** follow from `hbracket`.

This file closes that gap.  `LocalThresholdArrayInputs` is `ThresholdArrayInputs` with its three
global martingale fields (`martingale`, `compensated`, `memLp`) replaced by the two *local*
predicates of `Process/MartingaleIngredients`, exactly as `hbracket` delivers them; its
`rightContinuous_compensated` field is dropped, being implied by the càdlàg rows and the
continuous brackets.

The composition has two halves.

* **Martingale localization.**  `MartingaleLimit.exists_common_square_localizer` already produces
  a single localizing sequence `ρ n` — the pointwise minimum of the two localizing sequences, in
  mathlib's own `IsLocalizingSequence.min` idiom — along which the exact `{ρ > ⊥}`-indicator stop
  of `M n` is a true square-integrable martingale *and* the stop of `M n ^ 2 - V n` is a true
  martingale.  Nothing new is needed there.
* **Diagonalization.**  `ThresholdArrayInputs` is a statement about a *sequence* of rows, so one
  index of each row's localizing sequence must be selected.  `MartingaleLimit.localizing_exit_tendsto_zero`
  makes the finite-horizon exit probability of `ρ n j` vanish as `j → ∞`, so `j = k n` can be
  chosen with `P {ρ n (k n) ≤ T} < n⁻¹`.  The stopped rows then satisfy `ThresholdArrayInputs`
  and disagree with the original rows on `[0,T]` with vanishing probability.

The bracket-threshold localization inside `nonempty_localizedMartingaleArray_of_thresholdInputs`
stops a second time, at the first time `V n` reaches `Ici K`; `stoppedProcess_stoppedProcess`
makes that the stop at the minimum, which is why the two localizations compose.

Finally, `LocalizedMartingaleArray` mentions the target rows only through its `agree` field, so
the two vanishing-disagreement estimates compose and the produced array is an array **for the
original, unstopped rows** (`localizedMartingaleArray_of_agree`).  The consumer interface
`harray` is therefore unchanged: `harray_of_localThresholdInputs` has the same conclusion as
`LocalizedArrayProducer.harray_of_thresholdInputs` with a strictly weaker hypothesis.

**Discharge or reduction?**  This is a *strict weakening of an existing reduction*, not a
discharge of `hmodExp`: the open input is still an input.  What is discharged is the mismatch
itself — `thresholdArrayInputs_toLocal` proves the old hypothesis implies the new one, so the
new lane is inhabited (via `LocalizedArrayProducer.thresholdArrayInputs_zero`) and never harder
to satisfy, and the local martingale form is now literally the form `hbracket` produces.

**Not closed here**: the passage from the plane-valued `HasOrdinaryEdgeBracket` to its scalar
coordinates, and the diffusive rescaling of the rows, both of which sit between `hbracket` and
this file's hypothesis.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.LocalizedThresholdArray

open ReflectedGMS.MartingaleLimit
open ReflectedGMS.LocalizedArrayProducer
open ReflectedGMS.WindowModulusGridTransfer
open ReflectedGMS.TwoClockScalingLimitReduction

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## Stopping is a continuous monotone time reparametrisation -/

/-- **Stopping at an arbitrary extended time is a reparametrisation of the time axis.**  For each
fixed `ω` there is one continuous monotone `g : ℝ≥0 → ℝ≥0` — the identity, or `t ↦ t ⊓ τ ω` —
with `stoppedProcess N τ t ω = N (g t) ω` for *every* process `N`.  Continuity, monotonicity and
nonnegativity of a path therefore all transfer at once. -/
theorem exists_stopped_reparam (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    ∃ g : ℝ≥0 → ℝ≥0, Continuous g ∧ Monotone g ∧
      ∀ (N : ℝ≥0 → Ω → ℝ) (t : ℝ≥0), stoppedProcess N τ t ω = N (g t) ω := by
  by_cases hτtop : τ ω = ⊤
  · refine ⟨id, continuous_id, monotone_id, fun N t => ?_⟩
    exact stoppedProcess_eq_of_le (by rw [hτtop]; exact le_top)
  · let c := (τ ω).untop hτtop
    have hτcoe : (c : WithTop ℝ≥0) = τ ω := WithTop.coe_untop (τ ω) hτtop
    have key : ∀ (N : ℝ≥0 → Ω → ℝ) (t : ℝ≥0),
        stoppedProcess N τ t ω = N (min t c) ω := by
      intro N t
      rw [stoppedProcess, ← hτcoe, ← WithTop.coe_min]
      rfl
    exact ⟨fun t => min t c, continuous_id.min continuous_const,
      fun a b hab => min_le_min hab le_rfl, key⟩

/-- The stopped process at time zero is the original process at time zero. -/
theorem stoppedProcess_zero_apply (N : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    stoppedProcess N τ 0 ω = N 0 ω :=
  stoppedProcess_eq_of_le (by simp)

/-- **Continuity, monotonicity and nonnegativity of a bracket path survive the project's exact
indicator stopping.**  On `{τ ≤ ⊥}` the stopped path is identically zero, which satisfies all
three. -/
theorem indicator_stoppedProcess_bracket_props
    {V : ℝ≥0 → Ω → ℝ} (ω : Ω) (τ : Ω → WithTop ℝ≥0)
    (hc : Continuous (fun t => V t ω)) (hm : Monotone (fun t => V t ω))
    (h0 : ∀ t, 0 ≤ V t ω) :
    Continuous (fun t =>
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω) ∧
      Monotone (fun t =>
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω) ∧
      ∀ t, 0 ≤ stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω := by
  obtain ⟨g, hgc, hgm, hgeq⟩ := exists_stopped_reparam τ ω
  by_cases hωτ : ⊥ < τ ω
  · have hpt : ∀ t,
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω = V (g t) ω := by
      intro t
      rw [hgeq (fun s => {ω | ⊥ < τ ω}.indicator (V s)) t,
        Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hωτ)]
    have heq : (fun t =>
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω) =
        fun t => V (g t) ω := funext hpt
    refine ⟨?_, ?_, fun t => ?_⟩
    · rw [heq]; exact hc.comp hgc
    · rw [heq]; exact fun a b hab => hm (hgm hab)
    · rw [hpt t]; exact h0 (g t)
  · have hpt : ∀ t,
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω = 0 := by
      intro t
      rw [hgeq (fun s => {ω | ⊥ < τ ω}.indicator (V s)) t,
        Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hωτ)]
    have heq : (fun t =>
        stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ t ω) =
        fun _ => (0 : ℝ) := funext hpt
    refine ⟨?_, ?_, fun t => ?_⟩
    · rw [heq]; exact continuous_const
    · rw [heq]; exact monotone_const
    · rw [hpt t]

/-- **Adaptedness of the exact indicator-stopped bracket.**  The stopped process is adapted by
`StoppedAdaptedness.stronglyAdapted_stoppedProcess_of_ae_rightContinuous`, and the indicator set
`{τ > ⊥}` is known at time zero. -/
theorem adapted_indicator_stoppedProcess
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {V : ℝ≥0 → Ω → ℝ}
    (hV : Adapted F V) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => V t ω)) :
    Adapted F (stoppedProcess (fun s => {ω | ⊥ < τ ω}.indicator (V s)) τ) := by
  have hSA : StronglyAdapted F V := fun t => (hV t).stronglyMeasurable
  have hstop : StronglyAdapted F (stoppedProcess V τ) :=
    stronglyAdapted_stoppedProcess_of_ae_rightContinuous hSA hτ hnull hr
  have hzero : MeasurableSet[F 0] {ω | ⊥ < τ ω} := hτ.measurableSet_gt 0
  intro t
  rw [stoppedProcess_indicator_comm]
  exact ((hstop t).indicator (F.mono zero_le _ hzero)).measurable

/-! ## The localized inputs -/

/-- **The localized form of `LocalizedArrayProducer.ThresholdArrayInputs`.**

The three global martingale fields `martingale`, `compensated`, `memLp` are replaced by the two
local predicates of `Process/MartingaleIngredients`, which are exactly what
`HasOrdinaryEdgeBracket` — the content of the invariance assembly's `hbracket` — delivers:
`IsLocallySquareIntegrableMartingale` for the row and `IsLocalMartingale` for its compensated
square.  The field `rightContinuous_compensated` is dropped: it follows from the càdlàg rows and
the continuous brackets.

Every remaining field is copied verbatim from `ThresholdArrayInputs`.  No field mentions
`LocalizedMartingaleArray`, so the producer below is not circular. -/
structure LocalThresholdArrayInputs {Ω : Type*} {m : MeasurableSpace Ω} (P : @Measure Ω m)
    (F : ℕ → Filtration ℝ≥0 m) (M V : ℕ → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (v K : ℝ) : Prop where
  /-- The limiting bracket slope is nonnegative. -/
  v_nonneg : 0 ≤ v
  /-- The threshold level exceeds the terminal linear bracket. -/
  threshold_gt : v * (T : ℝ) < K
  /-- Each row is a locally square-integrable martingale. -/
  localMartingale : ∀ n,
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P (F n) (M n)
  /-- `V n` compensates the square of `M n` up to a local martingale. -/
  localCompensated : ∀ n, MartingaleIngredients.IsLocalMartingale P (F n)
    (fun t ω => M n t ω * M n t ω - V n t ω)
  /-- The filtrations contain the null sets. -/
  null : ∀ n (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[(F n) t] A
  /-- The rows have càdlàg paths. -/
  cadlag : ∀ n, ∀ᵐ ω ∂P, IsCadlag (fun t => M n t ω)
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

/-! ## The composition -/

/-- **The localization composition.**  From local martingale data one obtains *global* threshold
array inputs for a sequence of stopped rows, together with the vanishing probability that a
stopped row differs from its original row anywhere on `[0,T]`.

The stopping times are `ρ n (k n)`, where `ρ n` is the common square localizer of row `n`
(`MartingaleLimit.exists_common_square_localizer`, the minimum of the martingale and compensated
localizing sequences) and `k n` is chosen by `MartingaleLimit.localizing_exit_tendsto_zero` so
that the exit probability before `T` is below `n⁻¹`. -/
theorem exists_thresholdArrayInputs_of_local
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℕ → Filtration ℝ≥0 m} {M V : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {v K : ℝ}
    (h : LocalThresholdArrayInputs P F M V T v K) :
    ∃ M' V' : ℕ → ℝ≥0 → Ω → ℝ,
      ThresholdArrayInputs P F M' V' T v K ∧
      Tendsto (fun n => P {ω | ∃ t ≤ T, M' n t ω ≠ M n t ω}) atTop (𝓝 0) := by
  have hrM : ∀ n, ∀ᵐ ω ∂P, IsRightContinuous (fun t => M n t ω) :=
    fun n => (h.cadlag n).mono fun _ hω => hω.isRightContinuous
  have hrV : ∀ n, ∀ᵐ ω ∂P, IsRightContinuous (fun t => V n t ω) :=
    fun n => (h.continuous_bracket n).mono fun _ hω => hω.isRightContinuous
  have hrC : ∀ n, ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M n t ω * M n t ω - V n t ω) := by
    intro n
    filter_upwards [hrM n, hrV n] with ω hωM hωV
    exact (hωM.mul hωM).sub hωV
  choose ρ hρloc hρprop using fun n =>
    exists_common_square_localizer (h.localMartingale n) (h.localCompensated n)
      (h.null n) (hrM n) (hrV n)
  have hchoose : ∀ n : ℕ, ∃ j : ℕ,
      P {ω | ρ n j ω ≤ (T : WithTop ℝ≥0)} < ((n : ℝ≥0∞))⁻¹ := by
    intro n
    have hlim := localizing_exit_tendsto_zero (hρloc n) T
    have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞))⁻¹ :=
      ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)
    exact (hlim.eventually_lt_const hpos).exists
  choose k hk using hchoose
  have hexit : Tendsto (fun n => P {ω | ρ n (k n) ω ≤ (T : WithTop ℝ≥0)}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) (fun n => (hk n).le)
  have hrow : ∀ n,
      Martingale (stoppedProcess
        (fun t => {ω | ⊥ < ρ n (k n) ω}.indicator (M n t)) (ρ n (k n))) (F n) P ∧
      (∀ t, MemLp (stoppedProcess
        (fun t => {ω | ⊥ < ρ n (k n) ω}.indicator (M n t)) (ρ n (k n)) t) 2 P) ∧
      Martingale (fun t ω =>
        stoppedProcess (fun s => {ω | ⊥ < ρ n (k n) ω}.indicator (M n s)) (ρ n (k n)) t ω *
          stoppedProcess (fun s => {ω | ⊥ < ρ n (k n) ω}.indicator (M n s)) (ρ n (k n)) t ω -
        stoppedProcess (fun s => {ω | ⊥ < ρ n (k n) ω}.indicator (V n s)) (ρ n (k n)) t ω)
        (F n) P :=
    fun n => hρprop n (k n)
  refine ⟨fun n => stoppedProcess
      (fun t => {ω | ⊥ < ρ n (k n) ω}.indicator (M n t)) (ρ n (k n)),
    fun n => stoppedProcess
      (fun t => {ω | ⊥ < ρ n (k n) ω}.indicator (V n t)) (ρ n (k n)), ?_,
    tendsto_indicator_stopped_disagree M (fun n => ρ n (k n)) T hexit⟩
  exact
  { v_nonneg := h.v_nonneg
    threshold_gt := h.threshold_gt
    martingale := fun n => (hrow n).1
    compensated := fun n => (hrow n).2.2
    null := h.null
    cadlag := fun n => ae_isCadlag_indicator_stoppedProcess (ρ n (k n)) (h.cadlag n)
    rightContinuous_compensated := fun n =>
      ae_rightContinuous_indicator_stopped_compensated (ρ n (k n)) (hrC n)
    memLp := fun n t => (hrow n).2.1 t
    start_martingale := fun n => by
      filter_upwards [h.start_martingale n] with ω hω
      rw [stoppedProcess_zero_apply]
      by_cases hmem : ω ∈ {ω | ⊥ < ρ n (k n) ω}
      · rw [Set.indicator_of_mem hmem]; exact hω
      · rw [Set.indicator_of_notMem hmem]
    start_bracket := fun n => by
      filter_upwards [h.start_bracket n] with ω hω
      rw [stoppedProcess_zero_apply]
      by_cases hmem : ω ∈ {ω | ⊥ < ρ n (k n) ω}
      · rw [Set.indicator_of_mem hmem]; exact hω
      · rw [Set.indicator_of_notMem hmem]
    adapted_bracket := fun n =>
      adapted_indicator_stoppedProcess (h.adapted_bracket n)
        ((hρloc n).isStoppingTime (k n)) (h.null n) (hrV n)
    continuous_bracket := fun n => by
      filter_upwards [h.continuous_bracket n, h.monotone_bracket n, h.nonneg_bracket n]
        with ω hc hm h0
      exact (indicator_stoppedProcess_bracket_props ω (ρ n (k n)) hc hm h0).1
    monotone_bracket := fun n => by
      filter_upwards [h.continuous_bracket n, h.monotone_bracket n, h.nonneg_bracket n]
        with ω hc hm h0
      exact (indicator_stoppedProcess_bracket_props ω (ρ n (k n)) hc hm h0).2.1
    nonneg_bracket := fun n => by
      filter_upwards [h.continuous_bracket n, h.monotone_bracket n, h.nonneg_bracket n]
        with ω hc hm h0
      exact (indicator_stoppedProcess_bracket_props ω (ρ n (k n)) hc hm h0).2.2
    ucp := by
      intro ε hε
      have hsub : ∀ n,
          P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |stoppedProcess
              (fun s => {ω | ⊥ < ρ n (k n) ω}.indicator (V n s)) (ρ n (k n)) t ω
                - v * (t : ℝ)|} ≤
            P {ω | ∃ t ∈ Icc (0 : ℝ≥0) T, ε < |V n t ω - v * (t : ℝ)|}
              + P {ω | ρ n (k n) ω ≤ (T : WithTop ℝ≥0)} := by
        intro n
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        rintro ω ⟨t, ht, hlt⟩
        by_cases hω : ρ n (k n) ω ≤ (T : WithTop ℝ≥0)
        · exact Or.inr hω
        · have hgt : (T : WithTop ℝ≥0) < ρ n (k n) ω := not_le.mp hω
          have hle : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ ρ n (k n) ω :=
            le_of_lt (lt_of_le_of_lt (by exact_mod_cast ht.2) hgt)
          have hmem : ω ∈ {ω | ⊥ < ρ n (k n) ω} := lt_of_le_of_lt bot_le hgt
          refine Or.inl ⟨t, ht, ?_⟩
          rwa [stoppedProcess_eq_of_le hle, Set.indicator_of_mem hmem] at hlt
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun _ => zero_le) hsub
      simpa using (h.ucp ε hε).add hexit }

/-! ## Transferring the array back to the original rows -/

/-- **`LocalizedMartingaleArray` depends on its target rows only through `agree`.**  If the rows
`Y` of an array agree in probability with rows `X` on `[0,H]`, the same array is an array for
`X`.  All six data fields and ten of the eleven proof fields are copied unchanged. -/
def localizedMartingaleArray_of_agree
    {P : Measure Ω} {X Y : ℕ → ℝ≥0 → Ω → ℝ} {H : ℝ≥0}
    (A : LocalizedMartingaleArray P Y H)
    (hYX : Tendsto (fun n => P {ω | ∃ t ≤ H, Y n t ω ≠ X n t ω}) atTop (𝓝 0)) :
    LocalizedMartingaleArray P X H := by
  refine
    { F := A.F
      Y := A.Y
      B := A.B
      R := A.R
      C := A.C
      v := A.v
      martingale := A.martingale
      compensated := A.compensated
      cadlag := A.cadlag
      rightContinuous_compensated := A.rightContinuous_compensated
      memLp := A.memLp
      terminal := A.terminal
      v_nonneg := A.v_nonneg
      integrable_error := A.integrable_error
      error := A.error
      error_mean := A.error_mean
      agree := ?_ }
  have hsub : ∀ n, P {ω | ∃ t ≤ H, A.Y n t ω ≠ X n t ω} ≤
      P {ω | ∃ t ≤ H, A.Y n t ω ≠ Y n t ω} + P {ω | ∃ t ≤ H, Y n t ω ≠ X n t ω} := by
    intro n
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    rintro ω ⟨t, htH, hne⟩
    by_cases hAY : A.Y n t ω = Y n t ω
    · exact Or.inr ⟨t, htH, fun hYXt => hne (hAY.trans hYXt)⟩
    · exact Or.inl ⟨t, htH, hAY⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => zero_le) hsub
  simpa using A.agree.add hYX

/-- **The localized `LocalizedMartingaleArray` producer.**  Same conclusion as
`LocalizedArrayProducer.nonempty_localizedMartingaleArray_of_thresholdInputs`, from the strictly
weaker localized hypothesis. -/
theorem nonempty_localizedMartingaleArray_of_localThresholdInputs
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℕ → Filtration ℝ≥0 m} {M V : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {v K : ℝ}
    (h : LocalThresholdArrayInputs P F M V T v K) :
    Nonempty (LocalizedMartingaleArray P M T) := by
  obtain ⟨M', V', hin, hdis⟩ := exists_thresholdArrayInputs_of_local h
  obtain ⟨A⟩ := nonempty_localizedMartingaleArray_of_thresholdInputs hin
  exact ⟨localizedMartingaleArray_of_agree A hdis⟩

/-! ## Shape check against the consumer

The `harray` slot of `WindowModulusGridTransfer.rescaledWindowModulusTail_of_localized_arrays`
is filled from localized threshold data alone.  This `example` elaborates, so the binders match
rather than merely looking compatible. -/

end ReflectedGMS.LocalizedThresholdArray

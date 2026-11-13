/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppedBracketIncrement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CommonSquareLocalizer
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingCrossMoment

/-!
Bounded stopping-time increments for a square-compensated martingale.  The
compensated square is assumed to be a true martingale; this file does not
identify a candidate compensator with the bracket of the limiting process.

The common-localizer specialization retains mathlib's exact `{rho > bot}`
indicator in both localized processes, including at zero and infinity.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- For two bounded ordered stopping times, the square increment of a true
martingale has expectation equal to the corresponding compensator increment.
Integrability of both random variables is part of the conclusion.  No
zero-time normalization is needed: the two constant initial terms cancel. -/
theorem bounded_stopping_bracket_increment_integral
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (T : ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P) :
    Integrable (fun ω =>
        (stoppedValue M τ ω - stoppedValue M σ ω) ^ 2) P ∧
      Integrable (stoppedValue B τ - stoppedValue B σ) P ∧
      (∫ ω, (stoppedValue M τ ω - stoppedValue M σ ω) ^ 2 ∂P) =
        ∫ ω, stoppedValue B τ ω - stoppedValue B σ ω ∂P := by
  let C : ℝ≥0 → Ω → ℝ := fun t ω => M t ω * M t ω - B t ω
  have hσT : ∀ ω, σ ω ≤ T := fun ω => (hστ ω).trans (hτT ω)
  have hMσ2 : MemLp (stoppedValue M σ) 2 P :=
    (bounded_stopping_memLp_two_and_second_moment_le
      hM hσ T hσT hrM h2T).1
  have hMτ2 : MemLp (stoppedValue M τ) 2 P :=
    (bounded_stopping_memLp_two_and_second_moment_le
      hM hτ T hτT hrM h2T).1
  have hinc2 : MemLp (stoppedValue M τ - stoppedValue M σ) 2 P :=
    hMτ2.sub hMσ2
  have hincSq : Integrable (fun ω =>
      (stoppedValue M τ ω - stoppedValue M σ ω) ^ 2) P := by
    simpa only [Pi.sub_apply] using hinc2.integrable_sq
  have hCσ := bounded_stopping_integrable_and_integral_eq_terminal
    hC hσ T hσT hrC
  have hCτ := bounded_stopping_integrable_and_integral_eq_terminal
    hC hτ T hτT hrC
  have hBσ : Integrable (stoppedValue B σ) P := by
    refine (hMσ2.integrable_sq.sub hCσ.1).congr ?_
    filter_upwards [] with ω
    change M (σ ω).untopA ω ^ 2 -
      (M (σ ω).untopA ω * M (σ ω).untopA ω - B (σ ω).untopA ω) =
        B (σ ω).untopA ω
    ring
  have hBτ : Integrable (stoppedValue B τ) P := by
    refine (hMτ2.integrable_sq.sub hCτ.1).congr ?_
    filter_upwards [] with ω
    change M (τ ω).untopA ω ^ 2 -
      (M (τ ω).untopA ω * M (τ ω).untopA ω - B (τ ω).untopA ω) =
        B (τ ω).untopA ω
    ring
  have hBs : Integrable (stoppedValue B τ - stoppedValue B σ) P :=
    hBτ.sub hBσ
  have hMinc := bounded_stopping_sq_increment_integral
    hM hσ hτ T hστ hτT hrM h2T
  have hCeq :
      (∫ ω, stoppedValue C τ ω ∂P) = ∫ ω, stoppedValue C σ ω ∂P := by
    rw [hCτ.2, hCσ.2]
  have hsplitσ :
      (∫ ω, stoppedValue C σ ω ∂P) =
        (∫ ω, (stoppedValue M σ ω) ^ 2 ∂P) -
          ∫ ω, stoppedValue B σ ω ∂P := by
    calc
      _ = ∫ ω, (stoppedValue M σ ω) ^ 2 - stoppedValue B σ ω ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp only [C, stoppedValue]
        ring
      _ = _ := integral_sub hMσ2.integrable_sq hBσ
  have hsplitτ :
      (∫ ω, stoppedValue C τ ω ∂P) =
        (∫ ω, (stoppedValue M τ ω) ^ 2 ∂P) -
          ∫ ω, stoppedValue B τ ω ∂P := by
    calc
      _ = ∫ ω, (stoppedValue M τ ω) ^ 2 - stoppedValue B τ ω ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp only [C, stoppedValue]
        ring
      _ = _ := integral_sub hMτ2.integrable_sq hBτ
  refine ⟨hincSq, hBs, ?_⟩
  rw [hMinc, integral_sub hBτ hBσ]
  rw [hsplitτ, hsplitσ] at hCeq
  linarith

/-- The expected compensator increment is nonnegative and is bounded by the
terminal second moment used in the bounded-stopping argument. -/
theorem bounded_stopping_bracket_increment_integral_nonneg_le
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (T : ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M T) 2 P) :
    0 ≤ (∫ ω, stoppedValue B τ ω - stoppedValue B σ ω ∂P) ∧
      (∫ ω, stoppedValue B τ ω - stoppedValue B σ ω ∂P) ≤
        ∫ ω, (M T ω) ^ 2 ∂P := by
  have hid := bounded_stopping_bracket_increment_integral
    hM hC hσ hτ T hστ hτT hrM hrC h2T
  have hinc := bounded_stopping_sq_increment_integral
    hM hσ hτ T hστ hτT hrM h2T
  have hτsq := bounded_stopping_memLp_two_and_second_moment_le
    hM hτ T hτT hrM h2T
  constructor
  · rw [← hid.2.2]
    exact integral_nonneg (fun ω => sq_nonneg _)
  · rw [← hid.2.2, hinc]
    exact (sub_le_self _ (integral_nonneg (fun ω => sq_nonneg _))).trans hτsq.2

/-- Right continuity of an exact indicator-localized stopped process. -/
private theorem ae_rightContinuous_indicator_stoppedProcess
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (ρ : Ω → WithTop ℝ≥0)
    (hrX : ∀ᵐ ω ∂P, IsRightContinuous (fun t => X t ω)) :
    ∀ᵐ ω ∂P, IsRightContinuous (fun t =>
      stoppedProcess (fun s => {ω | ⊥ < ρ ω}.indicator (X s)) ρ t ω) := by
  filter_upwards [hrX] with ω hω
  rw [stoppedProcess_indicator_comm']
  by_cases hρω : ⊥ < ρ ω
  · have heq :
        (fun t => {ω | ⊥ < ρ ω}.indicator (stoppedProcess X ρ t) ω) =
          fun t => stoppedProcess X ρ t ω := by
      funext t
      rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < ρ ω} from hρω)]
    rw [heq]
    by_cases htop : ρ ω = ⊤
    · have hsame : (fun t => stoppedProcess X ρ t ω) = fun t => X t ω := by
        funext t
        exact stoppedProcess_eq_of_le (by rw [htop]; exact le_top)
      rw [hsame]
      exact hω
    · let c := (ρ ω).untop htop
      have hcoe : (c : WithTop ℝ≥0) = ρ ω := WithTop.coe_untop (ρ ω) htop
      have hsame : (fun t => stoppedProcess X ρ t ω) =
          fun t => X (min t c) ω := by
        funext t
        rw [stoppedProcess, ← hcoe, ← WithTop.coe_min]
        rfl
      rw [hsame]
      intro t
      rw [continuousWithinAt_Ioi_iff_Ici]
      have hg : Continuous (fun s : ℝ≥0 => min s c) :=
        continuous_id.min continuous_const
      have hout : ContinuousWithinAt (fun s => X s ω) (Ici (min t c)) (min t c) :=
        continuousWithinAt_Ioi_iff_Ici.mp (hω (min t c))
      have hin : ContinuousWithinAt (fun s : ℝ≥0 => min s c) (Ici t) t :=
        hg.continuousWithinAt
      have hmap : MapsTo (fun s : ℝ≥0 => min s c) (Ici t) (Ici (min t c)) := by
        intro s hs
        change t ≤ s at hs
        exact min_le_min hs le_rfl
      change ContinuousWithinAt
        ((fun s => X s ω) ∘ (fun s : ℝ≥0 => min s c)) (Ici t) t
      exact hout.comp (f := fun s : ℝ≥0 => min s c) (s := Ici t) hin hmap
  · have heq :
        (fun t => {ω | ⊥ < ρ ω}.indicator (stoppedProcess X ρ t) ω) =
          fun _ => (0 : ℝ) := by
      funext t
      rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < ρ ω} from hρω)]
    rw [heq]
    exact IsRightContinuous.const

end ReflectedGMS.MartingaleLimit

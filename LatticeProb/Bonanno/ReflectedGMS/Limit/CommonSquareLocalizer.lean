/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CommonSquareLocalizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.SquareMartingaleMaximal
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedL2
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients

/-!
A common localizing sequence for a locally square-integrable martingale and
its square compensator.  The construction is the pointwise minimum of the two
existing localizing sequences.  Each further stopping is justified by the
true stopped-martingale theorem; no local martingale is promoted directly to
a true martingale.
-/

-- Merged from `ReflectedGMS/Limit/BracketSecondMoment.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_BracketSecondMoment

/-!
Second moments from a true square-compensated martingale, and bracket forms of
the localized maximal inequality. The full existing predictable covariation
predicate is retained. A local compensated martingale is never promoted to a
true martingale: the actual stopped compensated martingale is an explicit
hypothesis. Initial values and mathlib's zero-time localizer indicator remain.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The exact second-moment identity, including both initial-value terms.
Integrability of the compensator follows from L² and the true compensated
martingale; it is not assumed or replaced by the Bochner integral's default. -/
theorem compensated_square_second_moment
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {N A : ℝ≥0 → Ω → ℝ}
    (hC : Martingale (fun t ω => N t ω * N t ω - A t ω) F P)
    (h2 : ∀ t, MemLp (N t) 2 P) (T : ℝ≥0) :
    (∫ ω, (N T ω) ^ 2 ∂P) = (∫ ω, A T ω ∂P) +
      (∫ ω, (N 0 ω) ^ 2 ∂P) - (∫ ω, A 0 ω ∂P) := by
  have hA : ∀ t, Integrable (A t) P := by
    intro t
    refine ((h2 t).integrable_sq.sub (hC.integrable t)).congr ?_
    filter_upwards [] with ω
    dsimp
    ring
  have he := hC.setIntegral_eq (i := 0) (j := T) (show 0 ≤ T from zero_le)
    MeasurableSet.univ
  simp only [setIntegral_univ] at he
  have hsplit (t : ℝ≥0) :
      (∫ ω, N t ω * N t ω - A t ω ∂P) =
        (∫ ω, (N t ω) ^ 2 ∂P) - (∫ ω, A t ω ∂P) := by
    simpa only [pow_two] using integral_sub (h2 t).integrable_sq (hA t)
  rw [hsplit 0, hsplit T] at he
  linarith

/-- The zero-initial-compensator specialization used after stopping. -/
theorem compensated_square_second_moment_of_zero
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {N A : ℝ≥0 → Ω → ℝ}
    (hC : Martingale (fun t ω => N t ω * N t ω - A t ω) F P)
    (h2 : ∀ t, MemLp (N t) 2 P) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0) (T : ℝ≥0) :
    (∫ ω, (N T ω) ^ 2 ∂P) = (∫ ω, A T ω ∂P) + (∫ ω, (N 0 ω) ^ 2 ∂P) := by
  have hz : (∫ ω, A 0 ω ∂P) = 0 := by
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂P := integral_congr_ae hA0
      _ = 0 := by simp
  rw [compensated_square_second_moment hC h2 T, hz, sub_zero]

end ReflectedGMS.MartingaleLimit

end Merged_BracketSecondMoment

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Right continuity is preserved by an arbitrary extended-time stopping. -/
theorem isRightContinuous_stoppedProcess_common
    {M : ℝ≥0 → Ω → ℝ} (ω : Ω) (hM : IsRightContinuous (fun t => M t ω))
    (τ : Ω → WithTop ℝ≥0) :
    IsRightContinuous (fun t => stoppedProcess M τ t ω) := by
  by_cases hτtop : τ ω = ⊤
  · have heq : (fun t => stoppedProcess M τ t ω) = fun t => M t ω := by
      funext t
      exact stoppedProcess_eq_of_le (by rw [hτtop]; exact le_top)
    rw [heq]
    exact hM
  let c := (τ ω).untop hτtop
  have hτcoe : (c : WithTop ℝ≥0) = τ ω := WithTop.coe_untop (τ ω) hτtop
  have heq : (fun t => stoppedProcess M τ t ω) = fun t => M (min t c) ω := by
    funext t
    rw [stoppedProcess, ← hτcoe, ← WithTop.coe_min]
    rfl
  rw [heq]
  intro t
  rw [continuousWithinAt_Ioi_iff_Ici]
  have hg : Continuous (fun s : ℝ≥0 => min s c) := continuous_id.min continuous_const
  have hout : ContinuousWithinAt (fun s => M s ω) (Ici (min t c)) (min t c) :=
    continuousWithinAt_Ioi_iff_Ici.mp (hM (min t c))
  have hin : ContinuousWithinAt (fun s : ℝ≥0 => min s c) (Ici t) t :=
    hg.continuousWithinAt
  have hmap : MapsTo (fun s : ℝ≥0 => min s c) (Ici t) (Ici (min t c)) := by
    intro s hs
    change t ≤ s at hs
    exact min_le_min hs le_rfl
  change ContinuousWithinAt
    ((fun s => M s ω) ∘ (fun s : ℝ≥0 => min s c)) (Ici t) t
  exact hout.comp (f := fun s : ℝ≥0 => min s c) (s := Ici t) hin hmap

/-- Localizing at the minimum is the same exact process as first localizing at
the left stopping time and then truly stopping at the right one. -/
private theorem indicator_stopped_min_eq_left_then_right
    (M : ℝ≥0 → Ω → ℝ) (σ τ : Ω → WithTop ℝ≥0) :
    stoppedProcess
        (fun t => {ω | ⊥ < (σ ⊓ τ) ω}.indicator (M t)) (σ ⊓ τ) =
      stoppedProcess
        (fun t => {ω | ⊥ < τ ω}.indicator
          (stoppedProcess (fun s => {ω | ⊥ < σ ω}.indicator (M s)) σ t)) τ := by
  rw [stoppedProcess_indicator_comm']
  simp_rw [stoppedProcess_indicator_comm']
  rw [stoppedProcess_stoppedProcess]
  rw [inf_comm σ τ]
  ext t ω
  have hinf : ⊥ < (τ ⊓ σ) ω ↔ ⊥ < τ ω ∧ ⊥ < σ ω := by
    rw [Pi.inf_apply, lt_inf_iff]
  by_cases hσ : ⊥ < σ ω <;> by_cases hτ : ⊥ < τ ω
  · rw [Set.indicator_of_mem
        (show ω ∈ {ω | ⊥ < (τ ⊓ σ) ω} from hinf.mpr ⟨hτ, hσ⟩),
      Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hτ),
      Set.indicator_of_mem (show ω ∈ {ω | ⊥ < σ ω} from hσ)]
  · rw [Set.indicator_of_notMem
        (show ω ∉ {ω | ⊥ < (τ ⊓ σ) ω} from fun h => hτ (hinf.mp h).1),
      Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hτ)]
  · rw [Set.indicator_of_notMem
        (show ω ∉ {ω | ⊥ < (τ ⊓ σ) ω} from fun h => hσ (hinf.mp h).2),
      Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ ω} from hτ),
      Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < σ ω} from hσ)]
  · rw [Set.indicator_of_notMem
        (show ω ∉ {ω | ⊥ < (τ ⊓ σ) ω} from fun h => hτ (hinf.mp h).1),
      Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ ω} from hτ)]

/-- Multiplying a martingale by an event known at time zero preserves the
martingale property. -/
theorem martingale_indicator_of_measurable_zero
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N F P) {A : Set Ω} (hA : MeasurableSet[F 0] A) :
    Martingale (fun t => A.indicator (N t)) F P := by
  refine ⟨fun t => (hN.stronglyAdapted t).indicator (F.mono zero_le _ hA),
    fun i j hij => ?_⟩
  exact (condExp_indicator (hN.integrable j) (F.mono zero_le _ hA)).trans
    (hN.condExp_ae_eq hij).indicator

/-- The pointwise minimum of the original localizers simultaneously makes
`M` square-integrable and makes its compensated square a true martingale.
The compensator is stopped with the same `{ρ > ⊥}` indicator, including when
`ρ` is zero or infinity. -/
theorem exists_common_square_localizer
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : MartingaleIngredients.IsLocallySquareIntegrableMartingale P F M)
    (hC : MartingaleIngredients.IsLocalMartingale P F
      (fun t ω => M t ω * M t ω - B t ω))
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrB : ∀ᵐ ω ∂P, IsRightContinuous (fun t => B t ω)) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F ρ P ∧
      ∀ n,
        let Mn := stoppedProcess
          (fun t => {ω | ⊥ < ρ n ω}.indicator (M t)) (ρ n)
        let Bn := stoppedProcess
          (fun t => {ω | ⊥ < ρ n ω}.indicator (B t)) (ρ n)
        Martingale Mn F P ∧ (∀ t, MemLp (Mn t) 2 P) ∧
          Martingale (fun t ω => Mn t ω * Mn t ω - Bn t ω) F P := by
  let σ := hM.2.localSeq
  let τ := hC.2.localSeq
  let ρ : ℕ → Ω → WithTop ℝ≥0 := min σ τ
  refine ⟨ρ, hM.2.isLocalizingSequence_localSeq.min
    hC.2.isLocalizingSequence_localSeq, fun n => ?_⟩
  let NM := stoppedProcess (fun t => {ω | ⊥ < σ n ω}.indicator (M t)) (σ n)
  let C := fun t ω => M t ω * M t ω - B t ω
  let NC := stoppedProcess (fun t => {ω | ⊥ < τ n ω}.indicator (C t)) (τ n)
  have hNM : Martingale NM F P := (hM.2.stoppedProcess_localSeq n).1
  have hNM2 : ∀ t, MemLp (NM t) 2 P := (hM.2.stoppedProcess_localSeq n).2
  have hNC : Martingale NC F P := hC.2.stoppedProcess_localSeq n
  have hrNM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => NM t ω) := by
    filter_upwards [hrM] with ω hω
    have heq : (fun t => NM t ω) =
        (fun t => {ω | ⊥ < σ n ω}.indicator (stoppedProcess M (σ n) t) ω) := by
      funext t
      exact congrFun (stoppedProcess_indicator_comm' (u := M) (τ := σ n)) t ▸ rfl
    rw [heq]
    by_cases hωσ : ⊥ < σ n ω
    · have hind : (fun t => {ω | ⊥ < σ n ω}.indicator
          (stoppedProcess M (σ n) t) ω) = fun t => stoppedProcess M (σ n) t ω := by
        funext t
        rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < σ n ω} from hωσ)]
      rw [hind]
      exact isRightContinuous_stoppedProcess_common ω hω (σ n)
    · have hind : (fun t => {ω | ⊥ < σ n ω}.indicator
          (stoppedProcess M (σ n) t) ω) = fun _ => (0 : ℝ) := by
        funext t
        rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < σ n ω} from hωσ)]
      rw [hind]
      exact IsRightContinuous.const
  have hrC : ∀ᵐ ω ∂P, IsRightContinuous (fun t => C t ω) := by
    filter_upwards [hrM, hrB] with ω hωM hωB
    exact hωM.mul hωM |>.sub hωB
  have hrNC : ∀ᵐ ω ∂P, IsRightContinuous (fun t => NC t ω) := by
    filter_upwards [hrC] with ω hω
    have heq : (fun t => NC t ω) =
        (fun t => {ω | ⊥ < τ n ω}.indicator (stoppedProcess C (τ n) t) ω) := by
      funext t
      exact congrFun (stoppedProcess_indicator_comm' (u := C) (τ := τ n)) t ▸ rfl
    rw [heq]
    by_cases hωτ : ⊥ < τ n ω
    · have hind : (fun t => {ω | ⊥ < τ n ω}.indicator
          (stoppedProcess C (τ n) t) ω) = fun t => stoppedProcess C (τ n) t ω := by
        funext t
        rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ n ω} from hωτ)]
      rw [hind]
      exact isRightContinuous_stoppedProcess_common ω hω (τ n)
    · have hind : (fun t => {ω | ⊥ < τ n ω}.indicator
          (stoppedProcess C (τ n) t) ω) = fun _ => (0 : ℝ) := by
        funext t
        rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < τ n ω} from hωτ)]
      rw [hind]
      exact IsRightContinuous.const
  have hMstop : Martingale (stoppedProcess NM (τ n)) F P :=
    stoppedProcess_martingale_of_null_events hNM
      (hC.2.isLocalizingSequence_localSeq.isStoppingTime n) hnull hrNM
  have hMstop2 : ∀ t, MemLp (stoppedProcess NM (τ n) t) 2 P := fun t =>
    (stoppedProcess_memLp_two_and_second_moment_le hNM
      (hC.2.isLocalizingSequence_localSeq.isStoppingTime n) hrNM t (hNM2 t)).1
  have hCstop : Martingale (stoppedProcess NC (σ n)) F P :=
    stoppedProcess_martingale_of_null_events hNC
      (hM.2.isLocalizingSequence_localSeq.isStoppingTime n) hnull hrNC
  have hτzero : MeasurableSet[F 0] {ω | ⊥ < τ n ω} :=
    hC.2.isLocalizingSequence_localSeq.isStoppingTime n |>.measurableSet_gt 0
  have hσzero : MeasurableSet[F 0] {ω | ⊥ < σ n ω} :=
    hM.2.isLocalizingSequence_localSeq.isStoppingTime n |>.measurableSet_gt 0
  have hMρ' : Martingale
      (stoppedProcess (fun t => {ω | ⊥ < τ n ω}.indicator (NM t)) (τ n)) F P := by
    rw [stoppedProcess_indicator_comm']
    exact martingale_indicator_of_measurable_zero hMstop hτzero
  have hMρ2' : ∀ t,
      MemLp (stoppedProcess (fun s => {ω | ⊥ < τ n ω}.indicator (NM s)) (τ n) t) 2 P := by
    intro t
    rw [stoppedProcess_indicator_comm]
    exact (hMstop2 t).indicator (F.le 0 _ hτzero)
  have hCρ' : Martingale
      (stoppedProcess (fun t => {ω | ⊥ < σ n ω}.indicator (NC t)) (σ n)) F P := by
    rw [stoppedProcess_indicator_comm']
    exact martingale_indicator_of_measurable_zero hCstop hσzero
  let Mn := stoppedProcess
    (fun t => {ω | ⊥ < ρ n ω}.indicator (M t)) (ρ n)
  let Bn := stoppedProcess
    (fun t => {ω | ⊥ < ρ n ω}.indicator (B t)) (ρ n)
  have hMρeq : Mn =
      stoppedProcess (fun t => {ω | ⊥ < τ n ω}.indicator (NM t)) (τ n) := by
    simpa only [Mn, NM, ρ, Pi.inf_apply] using
      indicator_stopped_min_eq_left_then_right M (σ n) (τ n)
  have hCρeq :
      stoppedProcess (fun t => {ω | ⊥ < ρ n ω}.indicator (C t)) (ρ n) =
        stoppedProcess (fun t => {ω | ⊥ < σ n ω}.indicator (NC t)) (σ n) := by
    have hrhon : ρ n = τ n ⊓ σ n := by
      funext ω
      exact min_comm _ _
    rw [hrhon]
    simpa only [NC, Pi.inf_apply] using
      indicator_stopped_min_eq_left_then_right C (τ n) (σ n)
  have hcompEq : (fun t ω => Mn t ω * Mn t ω - Bn t ω) =
      stoppedProcess (fun t => {ω | ⊥ < ρ n ω}.indicator (C t)) (ρ n) := by
    funext t ω
    dsimp only [Mn, Bn, C, stoppedProcess]
    by_cases hω : ω ∈ {ω | ⊥ < ρ n ω}
    · simp only [Set.indicator_of_mem hω]
    · simp only [Set.indicator_of_notMem hω, zero_mul, sub_self]
  have hMρ : Martingale Mn F P := by rw [hMρeq]; exact hMρ'
  have hMρ2 : ∀ t, MemLp (Mn t) 2 P := by
    intro t
    rw [hMρeq]
    exact hMρ2' t
  refine ⟨hMρ, hMρ2, ?_⟩
  rw [hcompEq, hCρeq]
  exact hCρ'

end ReflectedGMS.MartingaleLimit

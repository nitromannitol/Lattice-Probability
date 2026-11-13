/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppedMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.BoundedStopping
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Set-integral martingale identities for the actual stopped process. The proof
partitions at whether stopping has occurred by the earlier deterministic time,
and invokes bounded conditional sampling for `min (max τ s) t` on the remaining
part. Exact StronglyAdapted is retained explicitly in the true-martingale
corollary; it is not inferred from almost-sure path properties.
-/

-- Merged from `ReflectedGMS/Limit/ConditionalStopping.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ConditionalStopping

/-!
Genuine conditional sampling after a deterministic time. The bounded finite-grid
approximants stay after that time, so mathlib's existing countable-range optional
sampling applies. Its identity passes to the actual stopped value by the checked
L¹ convergence and the existing conditional-expectation L¹ contraction.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- If `s ≤ τ ≤ T`, then the value at deterministic time `s` is the conditional
expectation of the actual bounded stopped value given `F s`. Only almost-sure
right continuity is needed. No completed/right-continuous filtration or exact
adaptedness of an arbitrary stopped process is added or claimed. -/
theorem bounded_stopping_condExp_of_const_le
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (s T : ℝ≥0)
    (hsτ : ∀ ω, (s : WithTop ℝ≥0) ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) :
    M s =ᵐ[P] P[stoppedValue M τ | F s] := by
  let Y := fun n => stoppedValue M (boundedGridApprox τ T n)
  let g := stoppedValue M τ
  obtain ⟨hFi, hg, hL1⟩ := bounded_stopping_L1 hM hτ T hτT hr
  have he (n : ℕ) : M s =ᵐ[P] P[Y n | F s] := by
    have h := hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range
      (isStoppingTime_boundedGridApprox hτ T hτT n) (isStoppingTime_const F s)
      (fun ω => (hsτ ω).trans (boundedGridApprox_bounds T hτT n ω).1)
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2)
      (finite_range_boundedGridApprox T hτT n).countable
      (Set.finite_range_const (c := (s : WithTop ℝ≥0))).countable
    simpa only [stoppedValue_const, IsStoppingTime.measurableSpace_const] using h
  let G := P[g | F s] - M s
  have hdiff (n : ℕ) : G =ᵐ[P] P[g - Y n | F s] :=
    (EventuallyEq.rfl.sub (he n)).trans (condExp_sub hg (hFi n) (F s)).symm
  have hnorm (n : ℕ) : eLpNorm G 1 P ≤ eLpNorm (Y n - g) 1 P := by
    calc
      _ = eLpNorm (P[g - Y n | F s]) 1 P := eLpNorm_congr_ae (hdiff n)
      _ ≤ eLpNorm (g - Y n) 1 P := eLpNorm_condExp_le_eLpNorm _ le_rfl
      _ = eLpNorm (Y n - g) 1 P := eLpNorm_sub_comm _ _ _ _
  have hzero : eLpNorm G 1 P = 0 :=
    le_antisymm (ge_of_tendsto hL1 (Eventually.of_forall hnorm)) zero_le
  have hG : Integrable G P := integrable_condExp.sub (hM.integrable s)
  have hae := (eLpNorm_eq_zero_iff (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)).1 hzero
  filter_upwards [hae] with ω hω
  change P[stoppedValue M τ | F s] ω - M s ω = 0 at hω
  exact (sub_eq_zero.mp hω).symm

end ReflectedGMS.MartingaleLimit

end Merged_ConditionalStopping

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Every deterministic value of the actual stopped process is integrable,
even for an unbounded or infinite stopping time, by stopping at `min t τ`. -/
theorem integrable_stoppedProcess_of_ae_rightContinuous
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) (t : ℝ≥0) :
    Integrable (stoppedProcess M τ t) P :=
  (bounded_stopping_integrable_and_integral_eq_terminal hM
    ((isStoppingTime_const F t).min hτ) t (fun _ => min_le_left _ _) hr).1

/-- The actual stopped process satisfies the full martingale set-integral
identities. The original stopping time may equal infinity. No exact stopped
adaptedness or completion hypothesis is needed for this identity. -/
theorem stoppedProcess_setIntegral_eq
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[F s] A) :
    (∫ ω in A, stoppedProcess M τ s ω ∂P) =
      ∫ ω in A, stoppedProcess M τ t ω ∂P := by
  let E : Set Ω := {ω | τ ω ≤ s}
  have hE : MeasurableSet[F s] E := hτ s
  have hEm : MeasurableSet E := F.le s _ hE
  have hB : MeasurableSet[F s] (A \ E) := hA.diff hE
  have hBm : MeasurableSet (A \ E) := F.le s _ hB
  have hNs := integrable_stoppedProcess_of_ae_rightContinuous hM hτ hr s
  have hNt := integrable_stoppedProcess_of_ae_rightContinuous hM hτ hr t
  let θ : Ω → WithTop ℝ≥0 := fun ω => min (max (τ ω) s) t
  have hθ : IsStoppingTime F θ := (hτ.max_const s).min_const t
  have hsθ : ∀ ω, (s : WithTop ℝ≥0) ≤ θ ω :=
    fun _ => le_min (le_max_right _ _) (WithTop.coe_le_coe.mpr hst)
  have hθt : ∀ ω, θ ω ≤ t := fun _ => min_le_right _ _
  have hcond := bounded_stopping_condExp_of_const_le hM hθ s t hsθ hθt hr
  have hθint := (bounded_stopping_integrable_and_integral_eq_terminal hM hθ t hθt hr).1
  have hearly : (∫ ω in A ∩ E, stoppedProcess M τ s ω ∂P) =
      ∫ ω in A ∩ E, stoppedProcess M τ t ω ∂P := by
    apply setIntegral_congr_fun (F.le s _ (hA.inter hE))
    intro ω hω
    have hωs : τ ω ≤ s := hω.2
    rw [stoppedProcess_eq_of_ge hωs,
      stoppedProcess_eq_of_ge (hωs.trans (WithTop.coe_le_coe.mpr hst))]
  have hlate : (∫ ω in A \ E, stoppedProcess M τ s ω ∂P) =
      ∫ ω in A \ E, stoppedProcess M τ t ω ∂P := by
    calc
      _ = ∫ ω in A \ E, M s ω ∂P := by
        apply setIntegral_congr_fun hBm
        intro ω hω
        exact stoppedProcess_eq_of_le (le_of_lt (lt_of_not_ge hω.2))
      _ = ∫ ω in A \ E, P[stoppedValue M θ | F s] ω ∂P := by
        apply setIntegral_congr_ae hBm
        exact hcond.mono fun _ h _ => h
      _ = ∫ ω in A \ E, stoppedValue M θ ω ∂P :=
        setIntegral_condExp (F.le s) hθint hB
      _ = ∫ ω in A \ E, stoppedProcess M τ t ω ∂P := by
        apply setIntegral_congr_fun hBm
        intro ω hω
        have hsτ : (s : WithTop ℝ≥0) ≤ τ ω := le_of_lt (lt_of_not_ge hω.2)
        dsimp only [θ, stoppedValue, stoppedProcess]
        rw [max_eq_left hsτ, min_comm]
  calc
    _ = (∫ ω in A ∩ E, stoppedProcess M τ s ω ∂P) +
        ∫ ω in A \ E, stoppedProcess M τ s ω ∂P :=
      (integral_inter_add_sdiff hEm hNs.integrableOn).symm
    _ = (∫ ω in A ∩ E, stoppedProcess M τ t ω ∂P) +
        ∫ ω in A \ E, stoppedProcess M τ t ω ∂P := by rw [hearly, hlate]
    _ = _ := integral_inter_add_sdiff hEm hNt.integrableOn

/-- The actual stopped process is a true martingale once its exact
StronglyAdapted property has been established. That property is a separate,
explicit hypothesis; a.e. right continuity is never silently promoted to it. -/
theorem stoppedProcess_martingale_of_stronglyAdapted
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hadapt : StronglyAdapted F (stoppedProcess M τ)) :
    Martingale (stoppedProcess M τ) F P := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (F.le s)
    (integrable_stoppedProcess_of_ae_rightContinuous hM hτ hr t)
    (fun _ _ _ => (integrable_stoppedProcess_of_ae_rightContinuous hM hτ hr s).integrableOn)
    (fun _ hA _ => stoppedProcess_setIntegral_eq hM hτ hr hst hA)
    (hadapt s).aestronglyMeasurable).symm

end ReflectedGMS.MartingaleLimit

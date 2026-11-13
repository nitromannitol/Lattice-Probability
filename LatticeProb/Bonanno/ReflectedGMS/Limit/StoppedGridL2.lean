/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.StoppedGridL2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.BoundedStopping
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
L² convergence of the finite stopping-grid approximations. Conditional Jensen
dominates the squares of the stopped values by conditional expectations of the
terminal square. Uniform integrability of conditional expectations, followed by
Vitali's theorem, upgrades pathwise right-continuous convergence to L².
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

private theorem unifIntegrable_two_of_sq
    {P : Measure Ω} {f : ℕ → Ω → ℝ} (hmeas : ∀ n, AEStronglyMeasurable (f n) P)
    (hsq : UnifIntegrable (fun n ω => (f n ω) ^ 2) 1 P) :
    UnifIntegrable f 2 P := by
  rw [UnifIntegrable.mk_iff] at hsq ⊢
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsq (ε ^ (2 : ℝ))
    (ENNReal.rpow_pos_of_nonneg hε zero_le_two)]
    with δ hδ
  simp only [iSup_le_iff] at hδ ⊢
  intro n s hs hPs
  rw [← ENNReal.rpow_le_rpow_iff zero_lt_two]
  calc
    eLpNorm (f n) 2 (P.restrict s) ^ (2 : ℝ) =
        eLpNorm (fun ω => (f n ω) ^ 2) 1 (P.restrict s) := by
      calc
        _ = eLpNorm (fun ω => ‖f n ω‖ ^ (2 : ℝ)) 1 (P.restrict s) := by
          simpa using (eLpNorm_norm_rpow (μ := P.restrict s) (p := 1) (f n) (hmeas n).restrict zero_lt_two).symm
        _ = _ := by
          apply eLpNorm_congr_ae
          filter_upwards with ω
          simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    _ ≤ ε ^ (2 : ℝ) := hδ n s hs hPs

/-- For a real martingale with a square-integrable terminal value, the bounded
finite-grid stopped values converge in L² to the actual bounded stopped value.
Only almost-everywhere right continuity of the paths is used. -/
theorem boundedGridApprox_stoppedValue_L2
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (h2T : MemLp (M T) 2 P) :
    Tendsto (fun n => eLpNorm
      (stoppedValue M (boundedGridApprox τ T n) - stoppedValue M τ) 2 P)
      atTop (𝓝 0) := by
  let Y : ℕ → Ω → ℝ := fun n => stoppedValue M (boundedGridApprox τ T n)
  let X2 : Ω → ℝ := fun ω => (M T ω) ^ 2
  let C : ℕ → Ω → ℝ := fun n => P[X2 | (isStoppingTime_boundedGridApprox hτ T hτT n).measurableSpace]
  have hσ (n : ℕ) : IsStoppingTime F (boundedGridApprox τ T n) :=
    isStoppingTime_boundedGridApprox hτ T hτT n
  have he (n : ℕ) : Y n =ᵐ[P] P[M T | (hσ n).measurableSpace] :=
    hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hσ n)
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2)
      (finite_range_boundedGridApprox T hτT n).countable
  have hX2int : Integrable X2 P := by
    simpa only [X2] using h2T.integrable_sq
  have hCui : UniformIntegrable C 1 P := by
    exact hX2int.uniformIntegrable_condExp (fun n => (hσ n).measurableSpace_le)
  have hsq_le (n : ℕ) : (fun ω => (Y n ω) ^ 2) ≤ᵐ[P] C n := by
    have hint : Integrable (fun ω => ‖M T ω‖ ^ (2 : ℝ)) P := by
      simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h2T.integrable_sq
    have hj := _root_.Integrable.norm_condExp_rpow_le
      (m := (hσ n).measurableSpace) (f := M T)
      (show (1 : ℝ) ≤ 2 from one_le_two) hint
    filter_upwards [he n, hj] with ω heω hjω
    rw [heω]
    simpa only [C, X2, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hjω
  have hCnonneg (n : ℕ) : 0 ≤ᵐ[P] C n := by
    exact condExp_nonneg (m := (hσ n).measurableSpace)
      (Eventually.of_forall fun ω => sq_nonneg (M T ω))
  have hdom (n : ℕ) :
      (fun ω => ‖(Y n ω) ^ 2‖ₑ) ≤ᵐ[P] (fun ω => ‖C n ω‖ₑ) := by
    filter_upwards [hsq_le n, hCnonneg n] with ω hle hnonneg
    rw [Real.enorm_of_nonneg (sq_nonneg _), Real.enorm_of_nonneg hnonneg]
    exact ENNReal.ofReal_le_ofReal hle
  have hYsqmeas (n : ℕ) : AEStronglyMeasurable (fun ω => (Y n ω) ^ 2) P :=
    ((finite_stopping_memLp_two hM (hσ n)
      (finite_range_boundedGridApprox T hτT n) T
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2) h2T).aestronglyMeasurable).pow 2
  have hYsqUI : UniformIntegrable (fun n ω => (Y n ω) ^ 2) 1 P := by
    refine ⟨hCui.1.ae_mono hYsqmeas hdom, ?_⟩
    obtain ⟨K, hK⟩ := hCui.2
    exact ⟨K, fun n => (eLpNorm_mono_enorm_ae (hYsqmeas n) (hdom n)).trans (hK n)⟩
  have hYmem (n : ℕ) : MemLp (Y n) 2 P :=
    finite_stopping_memLp_two hM (hσ n)
      (finite_range_boundedGridApprox T hτT n) T
      (fun ω => (boundedGridApprox_bounds T hτT n ω).2) h2T
  have hYunif : UnifIntegrable Y 2 P := unifIntegrable_two_of_sq
    (fun n => (hYmem n).aestronglyMeasurable) hYsqUI.1
  have hYbound : ∃ K : ℝ≥0, ∀ n, eLpNorm (Y n) 2 P ≤ K := by
    refine ⟨(eLpNorm (M T) 2 P).toNNReal, fun n => ?_⟩
    calc
      eLpNorm (Y n) 2 P = eLpNorm P[M T | (hσ n).measurableSpace] 2 P :=
        eLpNorm_congr_ae (he n)
      _ ≤ eLpNorm (M T) 2 P := eLpNorm_condExp_le_eLpNorm (M T) one_le_two
      _ = ((eLpNorm (M T) 2 P).toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal h2T.eLpNorm_ne_top).symm
  have hYUI : UniformIntegrable Y 2 P := ⟨hYunif, hYbound⟩
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop
      (𝓝 (stoppedValue M τ ω)) :=
    hr.mono fun ω hω => boundedGridApprox_stoppedValue_tendsto M T hτT ω hω
  have hstop2 : MemLp (stoppedValue M τ) 2 P :=
    (bounded_stopping_memLp_two_and_second_moment_le hM hτ T hτT hr h2T).1
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top
    (fun n => (hYmem n).aestronglyMeasurable) hstop2 hYUI.1 hconv

end ReflectedGMS.MartingaleLimit

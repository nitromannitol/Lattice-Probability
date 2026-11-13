/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.MartingaleL2Limit at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Basic

/-!
# Martingale transfer under fixed-time L2 convergence

The martingale identities pass to an exactly adapted, integrable limit under
fixed-time L1 convergence.  On a finite measure space, fixed-time L2
convergence implies the required L1 convergence.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace ReflectedGMS

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A pointwise `limUnder` of exactly strongly adapted real processes is
exactly strongly adapted. -/
theorem stronglyAdapted_limUnder_atTop
    {F : Filtration ℝ≥0 m} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, StronglyAdapted F (M n)) :
    StronglyAdapted F
      (fun t ω => limUnder atTop (fun n => M n t ω)) := by
  intro t
  let _ : MeasurableSpace Ω := F t
  exact StronglyMeasurable.limUnder (fun n => hM n t)

/-- A fixed-time L1 limit of real martingales is a martingale when the limit
is exactly strongly adapted and integrable. -/
theorem martingale_of_tendsto_eLpNorm_one
    {P : Measure Ω} {F : Filtration ℝ≥0 m}
    [SigmaFiniteFiltration P F]
    {M : ℝ≥0 → Ω → ℝ} {Mn : ℕ → ℝ≥0 → Ω → ℝ}
    (hMn : ∀ n, Martingale (Mn n) F P)
    (hadapt : StronglyAdapted F M)
    (hint : ∀ t, Integrable (M t) P)
    (hL1 : ∀ t,
      Tendsto (fun n => eLpNorm (Mn n t - M t) 1 P) atTop (𝓝 0)) :
    Martingale M F P := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq
    (F.le s) (hint t) (fun _ _ _ => (hint s).integrableOn) ?_
      (hadapt s).aestronglyMeasurable).symm
  intro A hA _
  have hs_lim : Tendsto (fun n => ∫ ω in A, Mn n s ω ∂P)
      atTop (𝓝 (∫ ω in A, M s ω ∂P)) :=
    tendsto_setIntegral_of_L1' (M s)
      (Eventually.of_forall fun n => (hMn n).integrable s) (hL1 s) A
  have ht_lim : Tendsto (fun n => ∫ ω in A, Mn n t ω ∂P)
      atTop (𝓝 (∫ ω in A, M t ω ∂P)) :=
    tendsto_setIntegral_of_L1' (M t)
      (Eventually.of_forall fun n => (hMn n).integrable t) (hL1 t) A
  have hst_lim : Tendsto (fun n => ∫ ω in A, Mn n t ω ∂P)
      atTop (𝓝 (∫ ω in A, M s ω ∂P)) :=
    hs_lim.congr' (Eventually.of_forall fun n => (hMn n).setIntegral_eq hst hA)
  exact tendsto_nhds_unique hst_lim ht_lim

/-- On a finite measure space, fixed-time L2 convergence of real martingales
transfers the martingale property to an exactly strongly adapted, integrable
limit. -/
theorem martingale_of_tendsto_eLpNorm_two
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m}
    {M : ℝ≥0 → Ω → ℝ} {Mn : ℕ → ℝ≥0 → Ω → ℝ}
    (hMn : ∀ n, Martingale (Mn n) F P)
    (hadapt : StronglyAdapted F M)
    (hint : ∀ t, Integrable (M t) P)
    (hL2 : ∀ t,
      Tendsto (fun n => eLpNorm (Mn n t - M t) 2 P) atTop (𝓝 0)) :
    Martingale M F P := by
  apply martingale_of_tendsto_eLpNorm_one hMn hadapt hint
  intro t
  let C : ℝ≥0∞ := P univ ^
    (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hC : C ≠ ∞ := by
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      IsFiniteMeasure.measure_univ_lt_top.ne).ne
  have hupper : Tendsto
      (fun n => eLpNorm (Mn n t - M t) 2 P * C) atTop (𝓝 0) := by
    simpa [C] using ENNReal.Tendsto.mul_const (hL2 t) (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) fun n => by
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (((hMn n).integrable t).1.sub (hint t).1)

end ReflectedGMS

/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianExpMartingale

/-!
# Freezing the past against a Gaussian increment

If `Y` and an event `A` are measurable for a σ-algebra `𝓕` which is independent of a centred
Gaussian variable `Z` of variance `v`, then for an interval `[a, b]`
`P (A, Y + Z ∈ [a, b]) ≤ P (A) (b - a) / √(2 π v)`.
The Brownian form takes `Y = B_r + c s`, `Z = B_s - B_r`, and `𝓕` the natural σ-algebra at `r`.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-- A centred Gaussian charges an interval of length `ℓ` by at most `ℓ / √(2 π v)`. -/
theorem gaussianReal_Icc_le {v : ℝ≥0} (hv : v ≠ 0) {c d : ℝ} (hcd : c ≤ d) :
    gaussianReal 0 v (Set.Icc c d) ≤ ENNReal.ofReal ((d - c) / √(2 * Real.pi * v)) := by
  rw [gaussianReal_apply_eq_integral 0 hv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : 0 < √(2 * Real.pi * v) := by
    have : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
    positivity
  calc ∫ x in Set.Icc c d, gaussianPDFReal 0 v x
      ≤ ∫ _ in Set.Icc c d, (√(2 * Real.pi * v))⁻¹ := by
        refine setIntegral_mono_on ((integrable_gaussianPDFReal 0 v).integrableOn)
          (integrableOn_const (by simp)) measurableSet_Icc fun x _ => ?_
        rw [gaussianPDFReal_def]
        have : Real.exp (-(x - 0) ^ 2 / (2 * v)) ≤ 1 := by
          refine Real.exp_le_one_iff.2 ?_
          have : (0 : ℝ) ≤ v := v.2
          have h2 : 0 ≤ (x - 0) ^ 2 / (2 * v) := by positivity
          rw [neg_div]
          linarith
        calc (√(2 * Real.pi * v))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * v))
            ≤ (√(2 * Real.pi * v))⁻¹ * 1 := by gcongr
          _ = _ := mul_one _
    _ = (d - c) / √(2 * Real.pi * v) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        field_simp

/-- **Gaussian freezing.**  If `A` and `Y` are measurable for a σ-algebra `𝓕` independent of a
centred Gaussian `Z` of variance `v ≠ 0`, then
`P (A ∩ {Y + Z ∈ [a, b]}) ≤ P A * (b - a) / √(2 π v)`. -/
theorem measure_inter_add_mem_Icc_le {Ω : Type*} {𝓕 mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓕 : 𝓕 ≤ mΩ) {A : Set Ω}
    (hA : MeasurableSet[𝓕] A) {Y : Ω → ℝ} (hY : Measurable[𝓕] Y) {Z : Ω → ℝ}
    (hZm : Measurable Z) {v : ℝ≥0} (hv : v ≠ 0) (hZ : P.map Z = gaussianReal 0 v)
    (hind : Indep 𝓕 (MeasurableSpace.comap Z inferInstance) P) {a b : ℝ} (hab : a ≤ b) :
    P (A ∩ {ω | Y ω + Z ω ∈ Set.Icc a b}) ≤
      P A * ENNReal.ofReal ((b - a) / √(2 * Real.pi * v)) := by
  set W : Ω → ℝ × ℝ := fun ω => (Y ω, A.indicator (fun _ => (1 : ℝ)) ω) with hW
  have hW𝓕 : Measurable[𝓕] W := hY.prodMk (measurable_const.indicator hA)
  have hWm : Measurable W := hW𝓕.mono h𝓕 le_rfl
  have hindW : IndepFun W Z P := indep_of_indep_of_le_left hind hW𝓕.comap_le
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable hZm.aemeasurable).1 hindW
  set T : Set ((ℝ × ℝ) × ℝ) := {q | q.1.2 = 1 ∧ q.1.1 + q.2 ∈ Set.Icc a b} with hT
  have hTm : MeasurableSet T := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · exact (measurableSet_Icc).preimage (by fun_prop)
  have hpre : A ∩ {ω | Y ω + Z ω ∈ Set.Icc a b} = (fun ω => (W ω, Z ω)) ⁻¹' T := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hT, hW, hω]
  have hWZm : Measurable fun ω => (W ω, Z ω) := hWm.prodMk hZm
  have h1 : P (A ∩ {ω | Y ω + Z ω ∈ Set.Icc a b}) =
      ((P.map W).prod (P.map Z)) T := by
    rw [← hlaw, hpre, Measure.map_apply hWZm hTm]
  rw [h1, hZ, Measure.prod_apply hTm]
  have hset : MeasurableSet {w : ℝ × ℝ | w.2 = 1} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have h2 : ∀ w : ℝ × ℝ, gaussianReal 0 v (Prod.mk w ⁻¹' T) ≤
      {w : ℝ × ℝ | w.2 = 1}.indicator
        (fun _ => ENNReal.ofReal ((b - a) / √(2 * Real.pi * v))) w := by
    intro w
    by_cases hw : w.2 = 1
    · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × ℝ | w.2 = 1} from hw)]
      have : Prod.mk w ⁻¹' T = Set.Icc (a - w.1) (b - w.1) := by
        ext z
        simp only [hT, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc, hw, true_and]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [this]
      have := gaussianReal_Icc_le hv (c := a - w.1) (d := b - w.1) (by linarith)
      simpa [sub_sub_sub_cancel_right] using this
    · have : Prod.mk w ⁻¹' T = ∅ := by
        ext z
        simp [hT, hw]
      simp [this]
  calc ∫⁻ w, gaussianReal 0 v (Prod.mk w ⁻¹' T) ∂P.map W
      ≤ ∫⁻ w, {w : ℝ × ℝ | w.2 = 1}.indicator
          (fun _ => ENNReal.ofReal ((b - a) / √(2 * Real.pi * v))) w ∂P.map W :=
        lintegral_mono h2
    _ = ENNReal.ofReal ((b - a) / √(2 * Real.pi * v)) * (P.map W) {w : ℝ × ℝ | w.2 = 1} :=
        lintegral_indicator_const hset _
    _ = P A * ENNReal.ofReal ((b - a) / √(2 * Real.pi * v)) := by
        have hpreA : W ⁻¹' {w : ℝ × ℝ | w.2 = 1} = A := by
          ext ω
          by_cases hω : ω ∈ A <;> simp [hW, hω]
        rw [mul_comm, Measure.map_apply hWm hset, hpreA]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Brownian freezing.**  For `r < s`, an event `A` of the natural σ-algebra at time `r` and
`a ≤ b`, `P (A, B_s + c s ∈ [a, b]) ≤ P A * (b - a) / √(2 π (s - r))`. -/
theorem measure_inter_drift_mem_Icc_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {r s : ℝ≥0} (hrs : r < s) {A : Set Ω}
    (hA : MeasurableSet[brownianFiltration B hm r] A) (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    P (A ∩ {ω | B s ω + c * s ∈ Set.Icc a b}) ≤
      P A * ENNReal.ofReal ((b - a) / √(2 * Real.pi * ((s : ℝ) - r))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlaw := hB.hasLaw_sub s r
  have hv : nndist (s : ℝ) (r : ℝ) ≠ 0 := by
    rw [Ne, nndist_eq_zero]
    exact fun h => hrs.ne' (NNReal.coe_injective h)
  have hvr : ((nndist (s : ℝ) (r : ℝ) : ℝ≥0) : ℝ) = (s : ℝ) - r := by
    rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hrs.le))]
  have hY : Measurable[brownianFiltration B hm r] (fun ω => B r ω + c * s) :=
    ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) r).measurable).add_const _
  have key := measure_inter_add_mem_Icc_le (P := P) ((brownianFiltration B hm).le r) hA hY
    ((hm s).sub (hm r)) hv hlaw.map_eq (brownian_indep_filtration_sub hB hm hrs.le) hab
  rw [hvr] at key
  have hset : {ω | B s ω + c * s ∈ Set.Icc a b} =
      {ω | B r ω + c * s + (B s - B r) ω ∈ Set.Icc a b} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.sub_apply]
    rw [show B r ω + c * s + (B s ω - B r ω) = B s ω + c * s by ring]
  rw [hset]
  exact key

end LatticeProb
